#!/usr/bin/env python3
"""Check the two companion documents' current-manuscript references.

ROOT alone executes under hi_cft_safe_run.py --limit-mib 512.  Standard
library plus pdfinfo/pdftohtml; no network, installation, TeX execution,
research-engine imports, or numerical libraries. Expected RSS <128 MiB.

`check(root)` returns a JSON-serializable report. It follows literal TeX
inputs, parses AUX groups with balanced braces, compares named PDF
destinations and pages, and reads actual GoToR annotation dictionaries
from the companions, including pdfTeX Flate-compressed object streams.
Poppler drops remote destination names in its HTML output, so HTML is
used only for a separate visible-linked-text crosscheck. That crosscheck
is global per document, not a spatial or occurrence-by-occurrence proof.

This is a bounded parser for this repository's pdfTeX output, not a
general PDF interpreter. Unsupported object-stream filters fail closed.
It never rewrites the manuscripts or PDFs.
"""

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import resource
import shutil
import subprocess
import tempfile
import unicodedata
from urllib.parse import unquote, urlsplit
import zlib


GUIDES = ('hi_cft_c8_verification_guide.tex','hi_cft_c8_lean_assessment.tex')
MAIN = 'hi_cft_c8_proof'
MAX_SOURCE = 4*1024**2
MAX_PDF = 32*1024**2
MAX_INFLATE = 16*1024**2
MAX_TOTAL_INFLATE = 64*1024**2
MAX_TOOL_OUTPUT = 32*1024**2


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(65536),b''):
            h.update(block)
    return h.hexdigest()


def bounded_text(path, limit=MAX_SOURCE):
    require(path.is_file(),f'missing file: {path}')
    require(path.stat().st_size <= limit,f'oversized input: {path}')
    return path.read_text(encoding='utf-8')


def tex_mask(text):
    """Preserve positions while blanking comments and literal-code bodies."""
    out = list(text)
    for match in re.finditer(r'\\begin\{(verbatim\*?|lstlisting|minted)\}[\s\S]*?\\end\{\1\}',text):
        for i in range(match.start(),match.end()):
            if out[i] != '\n': out[i] = ' '
    provisional = ''.join(out)
    for match in re.finditer(r'\\verb\*?([^A-Za-z\s])([^\n]*?)\1',provisional):
        for i in range(match.start(),match.end()): out[i] = ' '
    for i,char in enumerate(out):
        if char != '%': continue
        count,j = 0,i-1
        while j >= 0 and out[j] == '\\': count,j = count+1,j-1
        if count % 2: continue
        j = i
        while j < len(out) and out[j] != '\n': out[j],j = ' ',j+1
    return ''.join(out)


def group(text, pos):
    while pos < len(text) and text[pos].isspace(): pos += 1
    require(pos < len(text) and text[pos] == '{',f'expected TeX group at offset {pos}')
    begin,depth = pos+1,1
    pos += 1
    while pos < len(text):
        if text[pos] == '\\':
            # Escaped braces do not open/close a group; ordinary commands
            # still leave their following argument braces to be parsed.
            if pos+1 < len(text) and text[pos+1] in '{}%\\': pos += 2; continue
        if text[pos] == '{': depth += 1
        if text[pos] == '}':
            depth -= 1
            if depth == 0: return text[begin:pos],pos+1
        pos += 1
    raise ValueError('unbalanced TeX braces')


def group_fields(text):
    fields,pos = [],0
    while pos < len(text):
        if text[pos:].strip() == '': break
        field,pos = group(text,pos)
        fields.append(field)
    return fields


def local_path(root, parent, name, suffix):
    require(not re.search(r'[\\#{}]',name),f'nonliteral input path: {name}')
    requested = Path(name)
    if not requested.suffix: requested = requested.with_suffix(suffix)
    # This project's TeX commands run from the repository root; prefer it.
    candidates = [root/requested,parent/requested]
    chosen = next((p.resolve() for p in candidates if p.is_file()),candidates[0].resolve())
    require(chosen.is_relative_to(root),f'input escapes repository: {name}')
    require(chosen.is_file(),f'missing included file: {name}')
    return chosen


def discover_tex(root, first):
    texts, occurrences, stack = {},[],[]
    def visit(path):
        require(path not in stack,'cyclic TeX input: '+str(path))
        require(len(stack) < 24 and len(texts) < 80,'TeX discovery bounds exceeded')
        stack.append(path)
        text = bounded_text(path)
        texts[path] = text
        mask = tex_mask(text)
        for match in re.finditer(r'\\(msref|mspageref|msnameref|ref|pageref|nameref)\s*\{',mask):
            label,end = group(mask,match.end()-1)
            command = match.group(1)
            if '#' in label: continue  # The shared macro's definition.
            if command.startswith('ms'):
                kind = command[2:]
            elif label.startswith('ms-'):
                label,kind = label[3:],command
            else: continue  # An internal companion reference.
            require(bool(label.strip()),'empty manuscript label')
            occurrences.append({'source':str(path.relative_to(root)),
                                'line':text.count('\n',0,match.start())+1,
                                'command':kind,'label':label.strip()})
        for match in re.finditer(r'\\(?:input|include)\s*\{',mask):
            name,end = group(mask,match.end()-1)
            if '#' in name: continue
            visit(local_path(root,path.parent,name.strip(),'.tex'))
        stack.pop()
    visit(root/first)
    return texts,occurrences


def parse_aux(root, path):
    labels = defaultdict(list)
    visited = set()
    def visit(current):
        require(current not in visited,'duplicate/cyclic AUX input: '+str(current))
        visited.add(current)
        require(len(visited) <= 30,'AUX input count cap')
        text = tex_mask(bounded_text(current))
        for match in re.finditer(r'\\newlabel\s*\{',text):
            key,pos = group(text,match.end()-1)
            value,pos = group(text,pos)
            fields = group_fields(value)
            labels[key].append({'fields':fields,'aux':str(current.relative_to(root))})
        for match in re.finditer(r'\\@input\s*\{',text):
            name,pos = group(text,match.end()-1)
            visit(local_path(root,current.parent,name,'.aux'))
    visit(path)
    return labels,visited


def run_tool(command, cwd, temporary, stem):
    out,err = temporary/(stem+'.stdout'),temporary/(stem+'.stderr')
    with out.open('wb') as stdout,err.open('wb') as stderr:
        result = subprocess.run(command,cwd=cwd,stdout=stdout,stderr=stderr,
                                timeout=45,check=False)
    require(out.stat().st_size <= MAX_TOOL_OUTPUT and err.stat().st_size <= MAX_SOURCE,
            'Poppler output cap exceeded')
    error = err.read_text(encoding='utf-8',errors='replace')
    require(result.returncode == 0,f'Poppler command failed: {command}: {error[-2000:]}')
    return out.read_text(encoding='utf-8',errors='replace'),error


def named_destinations(text):
    dests = defaultdict(list)
    for line in text.splitlines():
        match = re.match(r'^\s*(\d+)\s+\[(.*?)\]\s+"(.*)"\s*$',line)
        if match:
            name = match.group(3).replace(r'\"','"').replace(r'\\','\\')
            dests[name].append({'page':int(match.group(1)),'view':match.group(2).strip()})
    require(bool(dests),'pdfinfo returned no parseable named destinations')
    return dests


class PDFRef(tuple):
    def __new__(cls,a,b): return tuple.__new__(cls,(a,b))


class PDFName(str):
    pass


def pdf_string(value):
    if isinstance(value,bytes):
        if value.startswith(b'\xfe\xff'): return value[2:].decode('utf-16-be')
        if value.startswith(b'\xff\xfe'): return value[2:].decode('utf-16-le')
        return value.decode('latin-1')
    return str(value)


class PDFParser:
    """Only PDF lexical objects; streams are handled outside this parser."""
    def __init__(self,data,pos=0): self.data,self.pos,self.tokens = data,pos,0

    def skip(self):
        while self.pos < len(self.data):
            if self.data[self.pos] in b'\x00\t\n\f\r ': self.pos += 1
            elif self.data[self.pos] == 37:
                end = self.data.find(b'\n',self.pos)
                self.pos = len(self.data) if end < 0 else end+1
            else: break

    def value(self,depth=0):
        self.skip(); self.tokens += 1
        require(depth <= 64 and self.tokens <= 500000,'PDF parser bound exceeded')
        p,d = self.pos,self.data
        require(p < len(d),'unexpected PDF object end')
        if d[p:p+2] == b'<<':
            self.pos += 2; result = {}
            while True:
                self.skip()
                if d[self.pos:self.pos+2] == b'>>': self.pos += 2; return result
                key = self.value(depth+1)
                require(isinstance(key,PDFName),'PDF dictionary key must be a name')
                result[str(key)] = self.value(depth+1)
        if d[p:p+1] == b'[':
            self.pos += 1; result = []
            while True:
                self.skip()
                require(self.pos < len(d),'unclosed PDF array')
                if d[self.pos] == 93: self.pos += 1; return result
                result.append(self.value(depth+1))
        if d[p:p+1] == b'/':
            self.pos += 1; begin = self.pos
            while self.pos < len(d) and d[self.pos] not in b'\x00\t\n\f\r ()<>[]{}/%': self.pos += 1
            raw = re.sub(rb'#([0-9A-Fa-f]{2})',lambda m:bytes([int(m.group(1),16)]),d[begin:self.pos])
            return PDFName(raw.decode('latin-1'))
        if d[p:p+1] == b'(':
            self.pos += 1; level,result = 1,bytearray()
            while self.pos < len(d):
                char = d[self.pos]; self.pos += 1
                if char == 92:
                    require(self.pos < len(d),'truncated PDF escape')
                    char = d[self.pos]; self.pos += 1
                    escapes = {110:10,114:13,116:9,98:8,102:12}
                    if char in escapes: result.append(escapes[char])
                    elif char in (10,13):
                        if char == 13 and d[self.pos:self.pos+1] == b'\n': self.pos += 1
                    elif 48 <= char <= 55:
                        octal = bytes([char])
                        for unused in range(2):
                            if self.pos < len(d) and 48 <= d[self.pos] <= 55:
                                octal += bytes([d[self.pos]]); self.pos += 1
                            else: break
                        result.append(int(octal,8) % 256)
                    else: result.append(char)
                elif char == 40: level += 1; result.append(char)
                elif char == 41:
                    level -= 1
                    if level == 0: return bytes(result)
                    result.append(char)
                else: result.append(char)
            raise ValueError('unclosed PDF literal string')
        if d[p:p+1] == b'<':
            end = d.find(b'>',p+1); require(end >= 0,'unclosed PDF hex string')
            raw = re.sub(rb'\s',b'',d[p+1:end])
            if len(raw) % 2: raw += b'0'
            self.pos = end+1
            return bytes.fromhex(raw.decode('ascii'))
        ref = re.match(rb'(\d+)\s+(\d+)\s+R\b',d[p:])
        if ref:
            self.pos += ref.end(); return PDFRef(int(ref.group(1)),int(ref.group(2)))
        number = re.match(rb'[+-]?(?:\d+\.\d*|\.\d+|\d+)\b',d[p:])
        if number:
            token = number.group(); self.pos += number.end()
            return float(token) if b'.' in token else int(token)
        for token,value in ((b'true',True),(b'false',False),(b'null',None)):
            if d[p:p+len(token)] == token:
                self.pos += len(token); return value
        raise ValueError('unsupported PDF token near '+repr(d[p:p+35]))


def raw_pdf_links(path):
    """Inspect actual annotation objects, not Poppler's lossy remote hrefs."""
    require(path.stat().st_size <= MAX_PDF,'PDF exceeds32MiB cap')
    data = path.read_bytes()
    require(data.startswith(b'%PDF-'),'not a PDF')
    objects,streams,parse_failures = {},{},[]
    headers = list(re.finditer(rb'(?m)(\d+)\s+(\d+)\s+obj\b',data))
    require(len(headers) <= 50000,'PDF object count cap')
    for index,match in enumerate(headers):
        key = (int(match.group(1)),int(match.group(2)))
        parser = PDFParser(data,match.end())
        try:
            value = parser.value()
        except ValueError as error:
            parse_failures.append({'object':list(key),'error':str(error)})
            continue
        objects[key] = value
        parser.skip()
        if isinstance(value,dict) and data[parser.pos:parser.pos+6] == b'stream':
            start = parser.pos+6
            if data[start:start+2] == b'\r\n': start += 2
            elif data[start:start+1] in (b'\r',b'\n'): start += 1
            else: raise ValueError('PDF stream has no EOL')
            end = data.find(b'endstream',start)
            require(end >= 0,'missing PDF endstream')
            streams[key] = (value,start,end)
    total_inflated,objstm_count = 0,0
    for key,(definition,start,end) in streams.items():
        if definition.get('Type') != 'ObjStm': continue
        length = definition.get('Length')
        if isinstance(length,PDFRef): length = objects.get(tuple(length))
        if isinstance(length,int):
            require(0 <= length <= MAX_PDF,'invalid object-stream length')
            compressed = data[start:start+length]
        else: compressed = data[start:end].rstrip(b'\r\n')
        filters = definition.get('Filter')
        if filters is None: plain = compressed
        else:
            require(filters == 'FlateDecode' or filters == [PDFName('FlateDecode')],
                    'unsupported object-stream filter')
            decompressor = zlib.decompressobj()
            plain = decompressor.decompress(compressed,MAX_INFLATE+1)
            require(len(plain) <= MAX_INFLATE and decompressor.eof,
                    'object-stream inflate cap or incomplete stream')
        total_inflated += len(plain); objstm_count += 1
        require(total_inflated <= MAX_TOTAL_INFLATE,'total object-stream inflate cap')
        first,count = definition.get('First'),definition.get('N')
        require(isinstance(first,int) and isinstance(count,int) and 0 <= first <= len(plain)
                and 0 <= count <= 50000,'invalid object-stream header')
        numbers = list(map(int,re.findall(rb'\d+',plain[:first])))
        require(len(numbers) == 2*count,'object-stream header arity mismatch')
        for i in range(count):
            number,offset = numbers[2*i:2*i+2]
            require(0 <= first+offset < len(plain),'object-stream offset out of range')
            objects[(number,0)] = PDFParser(plain,first+offset).value()
    def resolve(value):
        seen = set()
        while isinstance(value,PDFRef):
            require(value not in seen and tuple(value) in objects,'unresolved/cyclic PDF reference')
            seen.add(value); value = objects[tuple(value)]
        return value
    links = []
    for key,value in objects.items():
        if not isinstance(value,dict) or value.get('Subtype') != 'Link': continue
        action = resolve(value.get('A'))
        if not isinstance(action,dict): continue
        if action.get('S') == 'GoToR':
            file_value = resolve(action.get('F'))
            if isinstance(file_value,dict): file_value = resolve(file_value.get('UF',file_value.get('F')))
            destination = resolve(action.get('D'))
            links.append({'object':list(key),'action':'GoToR','file':pdf_string(file_value),
                          'destination':pdf_string(destination) if isinstance(destination,(bytes,str)) else None,
                          'destination_kind':'named' if isinstance(destination,(bytes,str)) else 'array',
                          'rectangle':value.get('Rect')})
        elif action.get('S') == 'URI':
            uri = pdf_string(resolve(action.get('URI')))
            split = urlsplit(uri)
            if '.pdf' in split.path.lower():
                destination = unquote(split.fragment)
                if destination.startswith('nameddest='): destination = destination[10:]
                links.append({'object':list(key),'action':'URI','file':unquote(split.path),
                              'destination':destination or None,'destination_kind':'URI',
                              'rectangle':value.get('Rect')})
    require(not parse_failures,'unsupported ordinary PDF objects: '+repr(parse_failures[:3]))
    return links,{'ordinary_objects':len(headers),'object_streams':objstm_count,
                  'objects_after_expansion':len(objects),'inflated_bytes':total_inflated}


class LinkedText(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.href,self.parts,self.links = None,[],[]
    def handle_starttag(self,tag,attrs):
        if tag == 'a':
            self.href = dict(attrs).get('href'); self.parts = []
    def handle_data(self,text):
        if self.href is not None: self.parts.append(text)
    def handle_endtag(self,tag):
        if tag == 'a' and self.href is not None:
            self.links.append({'href':self.href,'text':''.join(self.parts)})
            self.href,self.parts = None,[]


def plain_tex_title(text):
    while '\\texorpdfstring' in text:
        start = text.index('\\texorpdfstring')
        first,pos = group(text,start+len('\\texorpdfstring'))
        second,end = group(text,pos)
        text = text[:start]+second+text[end:]
    text = re.sub(r'\\[A-Za-z@]+\s*','',text)
    text = text.replace('\\','').replace('{','').replace('}','').replace('$','').replace('_','')
    return text


def canonical(text):
    text = unicodedata.normalize('NFKD',text)
    return ''.join(c.lower() for c in text if c.isalnum())


def stale_literals(root,texts):
    findings = []
    pattern = re.compile(r'\b(Sections?|Appendix|Appendices|Propositions?|Theorems?|Lemmas?|Certificates?|[Pp]ages?|pp?\.)[\s~]+([0-9]+(?:\.[0-9]+)*|[A-Z](?:\.[0-9]+)*)\b')
    for path,text in texts.items():
        mask = tex_mask(text)
        for match in pattern.finditer(mask):
            window = mask[max(0,match.start()-180):min(len(mask),match.end()+180)]
            line_start = mask.rfind('\n',0,match.start())+1
            prefix = mask[line_start:match.start()]
            if re.search(r'\\cite\w*(?:\[[^\]]*)?$',prefix):
                kind = 'external_paper_citation'
            elif re.search(r'baseline|archiv|historical|concordance|former|frozen',window,re.I):
                kind = 'historical_or_frozen_context'
            elif re.search(r'manuscript',window,re.I):
                kind = 'suspected_hard_coded_current_manuscript_reference'
            else:
                kind = 'unqualified_or_guide_internal_review_only'
            findings.append({'source':str(path.relative_to(root)),
                             'line':text.count('\n',0,match.start())+1,
                             'literal':match.group(),'classification':kind,
                             'context':' '.join(window.split())})
    return findings


def check(root):
    """Return a complete report; FAIL is explicit rather than an exception."""
    root = Path(root).resolve()
    report = {'schema':'c8-manuscript-reference-check-v1','status':'FAIL',
              'errors':[],'warnings':[],'guides':{},'main':{},
              'scope':'Literal TeX reference discovery, AUX uniqueness, actual main PDF named destinations/pages, and actual companion GoToR annotation coverage. Visible reference text is checked globally in each document linked-text pool, not spatially or occurrence by occurrence. No mathematical theorem is checked.'}
    try:
        cap = resource.getrlimit(resource.RLIMIT_AS)[0]
        require(0 < cap <= 6*1024**3,'run under the permanent resource launcher')
        for program in ('pdfinfo','pdftohtml'):
            require(shutil.which(program) is not None,f'missing Poppler binary: {program}')
        main_pdf,main_aux = root/(MAIN+'.pdf'),root/(MAIN+'.aux')
        require(main_pdf.stat().st_size <= MAX_PDF,'main PDF size cap')
        labels,aux_sources = parse_aux(root,main_aux)
        source_hashes = {str(p.relative_to(root)):digest(p) for p in aux_sources|{main_pdf}}
        shared = root/'c8_physics_20260927/manuscript_refs.tex'
        shared_text = tex_mask(bounded_text(shared))
        require(re.search(r'\\externaldocument\[ms-\]\{hi_cft_c8_proof\}\[hi_cft_c8_proof\.pdf\]',shared_text),
                'shared externaldocument does not target the current main PDF with ms- prefix')
        for wrapper,command in (('msref','ref'),('mspageref','pageref'),('msnameref','nameref')):
            require(re.search(r'\\newcommand\{\\'+wrapper+r'\}\[1\]\{\\'+command+r'\{ms-#1\}\}',shared_text),
                    f'unexpected definition of {wrapper}')
        with tempfile.TemporaryDirectory(prefix='c8-manuscript-links-') as work:
            temporary = Path(work)
            text,stderr = run_tool(['pdfinfo','-dests',str(main_pdf)],root,temporary,'main-dests')
            dests = named_destinations(text)
            info,unused = run_tool(['pdfinfo',str(main_pdf)],root,temporary,'main-info')
            pages = re.search(r'^Pages:\s+(\d+)\s*$',info,re.M)
            require(pages is not None,'main PDF page count unavailable')
            report['main'] = {'pdf':main_pdf.name,'aux':main_aux.name,'pages':int(pages.group(1)),
                              'named_destination_count':len(dests),'aux_label_count':len(labels)}
            for guide_name in GUIDES:
                texts,refs = discover_tex(root,guide_name)
                require(shared in texts,f'{guide_name} does not load the shared reference macros')
                guide_pdf = root/Path(guide_name).with_suffix('.pdf')
                require(guide_pdf.is_file(),f'missing companion PDF: {guide_pdf.name}')
                source_hashes.update({str(p.relative_to(root)):digest(p) for p in texts})
                source_hashes[guide_pdf.name] = digest(guide_pdf)
                expected = Counter()
                resolved = []
                for ref in refs:
                    records = labels.get(ref['label'],[])
                    require(len(records) == 1,f"{guide_name}: label {ref['label']} has {len(records)} AUX definitions")
                    fields = records[0]['fields']
                    require(len(fields) >= 4,f"label {ref['label']} lacks hyperref fields")
                    number,page,title,destination = fields[:4]
                    require(page.isdecimal(),f"unsupported nondecimal main page for {ref['label']}: {page}")
                    anchors = dests.get(destination,[])
                    require(len(anchors) == 1,f"destination {destination} has {len(anchors)} definitions in main PDF")
                    require(anchors[0]['page'] == int(page),
                            f"AUX/PDF page mismatch for {ref['label']}: {page} vs {anchors[0]['page']}")
                    expected[destination] += 1
                    value = {'ref':number,'pageref':page,'nameref':plain_tex_title(title)}[ref['command']]
                    resolved.append(dict(ref,number=number,page=int(page),title=title,
                                         destination=destination,expected_visible_text=value))
                require(bool(resolved),f'no manuscript references found in {guide_name}')
                links,pdf_stats = raw_pdf_links(guide_pdf)
                actual = Counter()
                manuscript_links = []
                for link in links:
                    if Path(urlsplit(link['file']).path).name != MAIN+'.pdf': continue
                    if link['destination'] is not None:
                        require(link['destination'] in dests,f"actual external link has unknown destination: {link}")
                        actual[link['destination']] += 1
                    manuscript_links.append(link)
                missing = {dest:count-actual[dest] for dest,count in expected.items() if actual[dest] < count}
                require(not missing,f'{guide_name}: insufficient actual named GoToR annotations: {missing}')
                html_path = temporary/(Path(guide_name).stem+'.html')
                stdout,stderr = run_tool(['pdftohtml','-i','-s','-noframes',str(guide_pdf),str(html_path)],
                                         root,temporary,Path(guide_name).stem+'-html')
                html_files = sorted(temporary.glob(Path(guide_name).stem+'*.html'))
                require(bool(html_files),'pdftohtml did not create companion HTML')
                extracted = []
                for html_file in html_files:
                    parser = LinkedText(); parser.feed(bounded_text(html_file,MAX_TOOL_OUTPUT))
                    extracted += parser.links
                external_text = [x['text'] for x in extracted
                                 if Path(urlsplit(x['href']).path).name == MAIN+'.pdf']
                require(bool(external_text),'no visible manuscript-linked text exposed by Poppler')
                pool = ' '.join(external_text).replace('\xa0',' ')
                normal_pool = canonical(pool)
                visible = []
                for kind,value in sorted(set((r['command'],r['expected_visible_text']) for r in resolved)):
                    if kind == 'nameref': present = canonical(value) in normal_pool
                    else: present = bool(re.search(r'(?<![A-Za-z0-9])'+re.escape(value)+r'(?![A-Za-z0-9])',pool))
                    require(present,f'{guide_name}: expected visible {kind} text absent from linked-text pool: {value}')
                    visible.append({'command':kind,'text':value,'present_in_linked_text_pool':True})
                literals = stale_literals(root,texts)
                suspects = [x for x in literals if x['classification'] == 'suspected_hard_coded_current_manuscript_reference']
                report['warnings'].extend(suspects)
                report['guides'][guide_name] = {
                    'pdf':guide_pdf.name,'active_tex_sources':[str(p.relative_to(root)) for p in sorted(texts)],
                    'reference_occurrences':len(refs),'unique_labels':len({r['label'] for r in refs}),
                    'resolved_references':resolved,'expected_destination_occurrences':dict(expected),
                    'actual_destination_annotation_counts':dict(actual),
                    'actual_manuscript_pdf_links':manuscript_links,'pdf_parser':pdf_stats,
                    'all_referenced_labels_unique':True,'all_aux_pages_agree_with_actual_pdf_destinations':True,
                    'actual_named_destination_annotation_coverage':True,
                    'visible_text_crosscheck':visible,
                    'visible_text_scope':'Global linked-text pool only; Poppler discards GoToR destination fragments and may merge adjacent anchor text. Exact targets were checked independently from actual PDF annotation dictionaries.',
                    'literal_reference_review':literals}
        for name,old in source_hashes.items():
            require(digest(root/name) == old,f'input changed during check: {name}')
        report['source_sha256'] = source_hashes
        report['checker_sha256'] = digest(Path(__file__).resolve())
        report['checked_at_UTC'] = datetime.now(timezone.utc).isoformat()
        report['status'] = 'PASS'
    except Exception as error:
        report['errors'].append(type(error).__name__+': '+str(error))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    report = check(args.root)
    output = args.output or args.root/'c8_physics_20260927/manuscript_reference_check.json'
    output = output.resolve()
    output.parent.mkdir(parents=True,exist_ok=True)
    temporary = output.with_suffix(output.suffix+'.tmp')
    with temporary.open('w',encoding='utf-8') as stream:
        json.dump(report,stream,indent=2)
        stream.write('\n')
    temporary.replace(output)
    print(json.dumps({'status':report['status'],'errors':report['errors'],
                      'warnings':len(report['warnings']),'report':str(output),
                      'guides':{k:{'reference_occurrences':v['reference_occurrences'],
                                   'unique_labels':v['unique_labels']} for k,v in report['guides'].items()}},indent=2))
    raise SystemExit(0 if report['status'] == 'PASS' else 1)


if __name__ == '__main__':
    main()
