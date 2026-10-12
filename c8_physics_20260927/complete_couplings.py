"""Complete the 96-primary three-point tensor using exact current Ward identities.

Input: directly computed highest-first slice. Projection onto the invariant
96-dimensional primary space commutes with the compact current algebra.
Only root runs this under the permanent guard: AS1GiB, timeout300s.
Expected <200MiB: at most96^3 small exact coefficients, sparse pair maps.
"""
import csv
import hashlib
import json
from pathlib import Path
import resource
import sys
from time import monotonic

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import low_weight_couplings as raw
x = raw.x


def put(v, k, c):
    value = v.get(k, x.A()) + c
    if value:
        v[k] = value
    else:
        v.pop(k, None)


def main():
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3
    start = monotonic()
    basispath = HERE/'low_weight_basis.json'
    inputpath = HERE/'low_weight_couplings.json'
    basis = json.loads(basispath.read_text())['fields']
    source = json.loads(inputpath.read_text())
    assert len(basis) == 96 and source['status'] == 'pass'
    norms = [x.A(r['norm_squared']) for r in basis]
    lookup = {(r['multiplet'], *r['lowering_powers']): r['index'] for r in basis}
    maps = {}
    for axis in (0, 1):
        f, e = {}, {}
        for i, row in enumerate(basis):
            p = row['lowering_powers'].copy()
            n = row['current_dimensions'][axis]
            if p[axis]+1 < n:
                p[axis] += 1
                f[i] = (lookup[(row['multiplet'], *p)], 1)
                p[axis] -= 1
            if p[axis]:
                coefficient = p[axis]*(n-p[axis])
                p[axis] -= 1
                e[i] = (lookup[(row['multiplet'], *p)], coefficient)
        maps[axis] = f, e
    tensor = {(i,j): {} for i in range(96) for j in range(96)}
    for r in source['normalized_couplings']:
        if any(x.A(r['numerator'])):
            tensor[r['highest'], r['second']][r['target']] = x.A(r['numerator'])/norms[r['target']]

    def act(v, matrix):
        result = {}
        for k, c in v.items():
            if k in matrix:
                target, coefficient = matrix[k]
                put(result, target, c*coefficient)
        return result

    def ward_rhs(i, j, matrix):
        result = act(tensor[i,j], matrix)
        if j in matrix:
            jj, coefficient = matrix[j]
            for k, c in tensor[i,jj].items():
                put(result, k, -coefficient*c)
        return result

    for i, row in enumerate(basis):
        p, q = row['lowering_powers']
        if not (p or q):
            continue
        axis = 1 if q else 0
        previous = [p,q]
        previous[axis] -= 1
        ii = lookup[(row['multiplet'], *previous)]
        assert ii < i and maps[axis][0][ii] == (i,1)
        for j in range(96):
            tensor[i,j] = ward_rhs(ii,j,maps[axis][0])
    for i in range(96):
        for j in range(96):
            assert tensor[i,j] == tensor[j,i], ('primary skew-symmetry',i,j)
            for axis in (0,1):
                for matrix in maps[axis]:
                    lhs = ({k: c*matrix[i][1] for k,c in tensor[matrix[i][0],j].items()}
                           if i in matrix else {})
                    assert lhs == ward_rhs(i,j,matrix), ('Ward',i,j,axis)
            for k in tensor[i,j]:
                assert all(basis[i]['Cartan_weight'][a]+basis[j]['Cartan_weight'][a]
                           == basis[k]['Cartan_weight'][a] for a in (0,1))
    print('all raising/lowering Ward identities and primary skew-symmetry passed', flush=True)
    # Separate direct lattice-mode comparisons away from the seed slice.
    fields = [
        {(tuple(t['momentum']),tuple(t['oscillators'])): x.A(t['coefficient'])
         for t in row['field']} for row in basis]
    probes = []
    for m in range(8):
        members = [r['index'] for r in basis if r['multiplet'] == m]
        for i in (members[1], members[len(members)//2], members[-1]):
            candidates = [j for j in range(96) if tensor[i,j]]
            if not candidates:
                continue
            j = candidates[(i+m) % len(candidates)]
            product = x.mode(fields[i],1,fields[j])
            charge = [basis[i]['Cartan_weight'][a]+basis[j]['Cartan_weight'][a] for a in (0,1)]
            checked = {}
            for k in range(96):
                if basis[k]['Cartan_weight'] == charge:
                    value = raw.inner(fields[k],product)/norms[k]
                    if value:
                        checked[k] = value
            assert checked == tensor[i,j], ('direct lattice probe',i,j)
            probes.append([i,j])
    output = HERE/'complete_primary_couplings.tsv'
    assert not output.exists()
    nonzero = 0
    examples = {}
    with output.open('x',newline='') as stream:
        writer = csv.writer(stream,delimiter='\t')
        writer.writerow(['i','j','k','name_i','name_j','name_k','numerator_K4',
                         'norm_product_K4','abs_C_squared_K4'])
        for (i,j), product in sorted(tensor.items()):
            for k,c in sorted(product.items()):
                numerator = c*norms[k]
                denominator = norms[i]*norms[j]*norms[k]
                square = numerator.conj(2)*numerator/denominator
                assert raw.positive_real(square)
                writer.writerow([i,j,k,basis[i]['name'],basis[j]['name'],basis[k]['name'],
                                 json.dumps(list(map(str,numerator))),
                                 json.dumps(list(map(str,denominator))),
                                 json.dumps(list(map(str,square)))])
                nonzero += 1
                multiplets = tuple(basis[t]['multiplet'] for t in (i,j,k))
                complexity = sum(len(str(v)) for v in square)
                if multiplets not in examples or complexity < examples[multiplets]['complexity']:
                    examples[multiplets] = {'indices':[i,j,k], 'names':[basis[t]['name'] for t in(i,j,k)],
                                           'multiplets':list(multiplets),'abs_C_squared':list(map(str,square)),
                                           'complexity':complexity}
    report = {'status':'PASS','basis_dimension':96,'ordered_tensor_entries':96**3,
              'nonzero_entries':nonzero,'zero_entries':96**3-nonzero,
              'encoding':'Sparse TSV: omitted triples are exactly zero within this projected96-primary tensor.',
              'coefficient_convention':source['coefficient_convention'],
              'field_basis':source['field_basis'],
              'all_current_raising_lowering_Ward_checks':4*96**2,
              'all_primary_skew_symmetry_pair_checks':96**2,
              'direct_additional_lattice_probes':probes,
              'direct_seed_nonzero_entries':source['nonzero_couplings'],
              'derivation':'P(Fi,j)=F P(i,j)-P(i,Fj); orthogonal projection commutes with current zero modes.',
              'scope':'Complete three-point tensor within the selected96-dimensional weight-two primary space; other17 weight-two primaries and nonvacuum bulk OPE coefficients are not included.',
              'source_sha256':{str(p.relative_to(raw.ROOT)):raw.sha(p) for p in [Path(__file__),inputpath,basispath]},
              'output_sha256':raw.sha(output),'selected_examples':list(examples.values()),
              'elapsed_seconds':monotonic()-start,
              'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    (HERE/'complete_primary_couplings.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['status','nonzero_entries','zero_entries','elapsed_seconds','peak_RSS_KiB']}))


if __name__ == '__main__':
    main()
