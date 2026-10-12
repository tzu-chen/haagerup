"""Bounded, deterministic layout and offline exports of result-graph data.

Layout uses SCCs and longest-path layers, with no dense matrices, force simulation,
or Graphviz crossing minimization. Memory grows with nodes, edges, and source text.
"""

from collections import Counter, defaultdict, deque
from html import escape
import json
import re

STEM = "exists_EGEquations_odd_dependencies"
W, H, DX, MAX_COLUMNS = 480, 74, 530, 24


def reachable(start, adjacency):
    seen = {start}
    pending = [start]
    while pending:
        for node in adjacency[pending.pop()]:
            if node not in seen:
                seen.add(node)
                pending.append(node)
    return seen


def layout(nodes, edges):
    """Iterative Kosaraju, then longest-path ranks of the condensation DAG."""
    succ, pred = defaultdict(list), defaultdict(list)
    for e in edges:
        succ[e[0]].append(e[1])
        pred[e[1]].append(e[0])
    seen, order = set(), []
    for root in range(len(nodes)):
        if root in seen:
            continue
        seen.add(root)
        stack = [(root, iter(succ[root]))]
        while stack:
            node, it = stack[-1]
            other = next(it, None)
            if other is None:
                order.append(node)
                stack.pop()
            elif other not in seen:
                seen.add(other)
                stack.append((other, iter(succ[other])))
    component, groups = {}, []
    for root in reversed(order):
        if root in component:
            continue
        group = []
        component[root] = len(groups)
        pending = [root]
        while pending:
            node = pending.pop()
            group.append(node)
            for other in pred[node]:
                if other not in component:
                    component[other] = len(groups)
                    pending.append(other)
        groups.append(group)
    next_groups = defaultdict(set)
    indegrees = [0] * len(groups)
    for a, b, _ in edges:
        ca, cb = component[a], component[b]
        if ca != cb and cb not in next_groups[ca]:
            next_groups[ca].add(cb)
            indegrees[cb] += 1
    ranks = [0] * len(groups)
    queue = deque(c for c in range(len(groups)) if indegrees[c] == 0)
    while queue:
        c = queue.popleft()
        for d in sorted(next_groups[c]):
            ranks[d] = max(ranks[d], ranks[c] + 1)
            indegrees[d] -= 1
            if indegrees[d] == 0:
                queue.append(d)
    layers = defaultdict(list)
    for i, node in enumerate(nodes):
        node["layer"] = ranks[component[i]]
        layers[node["layer"]].append(i)
    width = min(MAX_COLUMNS, max(map(len, layers.values()))) * DX + 100
    top = 180
    for rank, layer in sorted(layers.items()):
        layer.sort(key=lambda i: (nodes[i]["module"], nodes[i].get("line", 0), nodes[i]["name"]))
        rows = (len(layer) + MAX_COLUMNS - 1) // MAX_COLUMNS
        for row in range(rows):
            members = layer[row * MAX_COLUMNS:(row + 1) * MAX_COLUMNS]
            left = (width - len(members) * DX) / 2
            for column, i in enumerate(members):
                nodes[i]["x"] = round(left + column * DX)
                nodes[i]["y"] = top + row * (H + 45)
                nodes[i]["root"] = not pred[i]
        top += rows * (H + 45) + 130
    return width, top + 100, groups


def label(name):
    name = re.sub(r"^_private\..*?\.\d+\.", "", name)
    return name.removeprefix("HaagerupIzumi.")


def node_lines(node):
    text = label(node["name"])
    if len(text) <= 66:
        return [text]
    split = text.rfind(".", 0, 66)
    split = split + 1 if split >= 20 else 66
    return [text[:split], text[split:]]


def edge_path(a, b):
    x, y = a["x"] + W / 2, a["y"] + H
    u, v = b["x"] + W / 2, b["y"]
    if a["layer"] < b["layer"]:
        return f"M{x},{y} C{x},{y + 65} {u},{v - 65} {u},{v}"
    # Recursion/mutual recursion stays visible, with a side loop.
    return f"M{x},{y} C{x + DX},{y + 105} {u + DX},{v - 105} {u},{v}"


def render(data, target, lean_dir, docs):
    graph = data["graph"]
    all_nodes = {n["name"]: n for n in graph["nodes"]}
    if len(all_nodes) != len(graph["nodes"]) or target not in all_nodes:
        raise RuntimeError("Duplicate nodes or missing endpoint in extraction")
    pred = defaultdict(list)
    for edge in graph["edges"]:
        if edge["src"] not in all_nodes or edge["tgt"] not in all_nodes:
            raise RuntimeError(f"Dangling edge: {edge}")
        pred[edge["tgt"]].append(edge["src"])
    keep = reachable(target, pred)
    names = sorted(keep)
    index = {name: i for i, name in enumerate(names)}
    nodes = [dict(all_nodes[name]) for name in names]
    kept_edges = [e for e in graph["edges"] if e["tgt"] in keep]
    assert all(e["src"] in keep for e in kept_edges)
    assert len({(e["src"], e["tgt"]) for e in kept_edges}) == len(kept_edges)
    edges = [[index[e["src"]], index[e["tgt"]], int(e["kind"] == "statement")] for e in kept_edges]
    boundary = [e for e in data["boundary"] if e["tgt"] in keep]
    boundary_by_node = defaultdict(list)
    for e in boundary:
        boundary_by_node[e["tgt"]].append([e["src"], e["module"], e["kind"]])
    modules = sorted({n["module"] for n in nodes})
    source_files, declarations = {}, {}
    for module in modules:
        path = lean_dir.joinpath(*module.split(".")).with_suffix(".lean")
        source_files[module] = path.read_text()
        ilean = lean_dir / ".lake/build/lib/lean" / path.relative_to(lean_dir).with_suffix(".ilean")
        declarations[module] = json.loads(ilean.read_text())["decls"]
    for node in nodes:
        node["rank"] = "result" if node["name"] == target else "lemma" if node["kind"] == "thm" else "def"
        decls = declarations[node["module"]]
        name = node["name"]
        user = re.sub(r"^_private\..*?\.\d+\.", "", name)
        candidate = name if name in decls else user
        node["sourceDeclaration"] = candidate if candidate in decls else None
        # Generated helpers link to their nearest named ancestor where available.
        while candidate not in decls and "." in candidate:
            candidate = candidate.rsplit(".", 1)[0]
        if candidate in decls:
            loc = decls[candidate]
            node["line"] = loc[4] + 1
            node["sourceRange"] = [loc[0], loc[2] + 1]
            node["sourceOwner"] = candidate
        node["boundary"] = sorted(boundary_by_node[node["name"]])
        node["labelLines"] = node_lines(node)
    width, height, groups = layout(nodes, edges)
    target_id = index[target]
    bad = [n["name"] for n in nodes if n["hasSorry"] or n["sorryTainted"] or n["kind"] == "axiom"]
    if bad:
        raise RuntimeError(f"Unexpected sorry/project axiom declarations: {bad[:20]}")
    stats = {"nodes": len(nodes), "edges": len(edges), "modules": len(modules),
             "roots": sum(n["root"] for n in nodes),
             "named_declarations": sum(bool(n["sourceDeclaration"]) for n in nodes),
             "kinds": dict(sorted(Counter(n["kind"] for n in nodes).items())),
             "statement_edges": sum(e[2] for e in edges),
             "proof_edges": sum(not e[2] for e in edges),
             "external_references": len(boundary),
             "external_declarations": len({e["src"] for e in boundary}),
             "external_module_roots": sorted({e["module"].split(".")[0] for e in boundary}),
             "layers": max(n["layer"] for n in nodes) + 1,
             "mutually_recursive_components": sum(len(g) > 1 for g in groups),
             "self_edges": sum(e[0] == e[1] for e in edges),
             "svg_width": width, "svg_height": height}
    provenance = {k: data[k] for k in ["lean_version", "extractor", "axiom_audit"]}
    provenance["source_sha256"] = {m: data["source_sha256"][m] for m in modules}
    if "artifact_hashes" in data:
        provenance["artifact_hashes"] = {m: data["artifact_hashes"][m] for m in modules}
    output = {"schema_version": 1, "target": target, "stats": stats, "provenance": provenance,
              "edge_convention": "dependency -> user; statement = mentioned in type (possibly also body); proof = body only",
              "scope": "Complete backward closure of project declarations; external library references stop at the boundary. No node contraction or transitive reduction.",
              "nodes": nodes, "edges": kept_edges}
    (docs / f"{STEM}.json").write_text(json.dumps(output, ensure_ascii=False, separators=(",", ":")) + "\n")
    (docs / f"{STEM}_stats.json").write_text(json.dumps(stats, indent=2) + "\n")
    # The DOT preserves every node and direct edge. Layout is optional for consumers.
    with (docs / f"{STEM}.dot").open("w") as out:
        out.write('digraph dependencies {\n  rankdir=TB;\n  node [shape=box,fontname="DejaVu Sans Mono",fontsize=10];\n')
        for i, n in enumerate(nodes):
            attrs = {"label": n["name"], "tooltip": n["module"],
                     "color": "#b43b90" if i == target_id else "#12866a" if n["root"] else "#475569"}
            out.write(f'  n{i} [' + ",".join(f"{k}={json.dumps(v, ensure_ascii=False)}" for k, v in attrs.items()) + "];\n")
        for a, b, kind in edges:
            out.write(f'  n{a} -> n{b} [style={"dashed" if kind else "solid"}];\n')
        out.write("}\n")
    with (docs / f"{STEM}.svg").open("w") as out:
        # Keep the default raster viewport bounded while retaining the full vector
        # coordinate space; natural-size rasterization of this graph would be huge.
        display_scale = min(2400 / width, 2400 / height)
        display_width, display_height = round(width * display_scale), round(height * display_scale)
        out.write(f'<svg xmlns="http://www.w3.org/2000/svg" width="{display_width}" height="{display_height}" viewBox="0 0 {width} {height}">\n')
        out.write(f'<title>Complete dependencies of {escape(target)}</title>\n')
        out.write('<desc>Every extracted project declaration leading to the target, including private and generated helpers. Arrows point from dependencies to users. Dashed: statement; solid: proof or definition body only. External libraries stop at the boundary.</desc>\n')
        out.write('<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L10,5 L0,10 Z" fill="#667788"/></marker></defs>\n')
        out.write(f'<rect width="{width}" height="{height}" fill="#f8fafc"/>\n')
        out.write(f'<text x="40" y="55" font-size="28" font-family="sans-serif">{escape(target)} — {len(nodes):,} declarations / {len(edges):,} direct arrows</text>\n')
        out.write('<text x="40" y="95" font-size="18" font-family="sans-serif">Top → bottom. Green = no project prerequisites. Purple = endpoint. Dashed = statement; solid = body only. Mathlib / Lean boundary is not expanded.</text>\n')
        out.write('<g fill="none" stroke="#7b8a9b" stroke-width="1" stroke-opacity=".28" marker-end="url(#arrow)">\n')
        for a, b, kind in edges:
            dash = ' stroke-dasharray="6 5"' if kind else ""
            out.write(f'<path class="edge" d="{edge_path(nodes[a], nodes[b])}"{dash}/>\n')
        out.write('</g>\n<g font-family="DejaVu Sans Mono, monospace">\n')
        for i, n in enumerate(nodes):
            color = "#b43b90" if i == target_id else "#12866a" if n["root"] else "#55657b"
            fill = "#fce7f3" if i == target_id else "#e3f5ee" if n["root"] else "#fff"
            x, y = n["x"], n["y"]
            out.write(f'<g class="node" id="n{i}"><title>{escape(n["name"])}\n{escape(n["module"])}</title>')
            out.write(f'<rect x="{x}" y="{y}" width="{W}" height="{H}" rx="3" fill="{fill}" stroke="{color}" stroke-width="2"/>')
            out.write(f'<text x="{x+10}" y="{y+16}" font-size="9" fill="#64748b">{escape(n["kind"])} · {escape(n["module"].removeprefix("HaagerupIzumi."))}</text>')
            for line, text in enumerate(n["labelLines"]):
                fit = f' textLength="{W-20}" lengthAdjust="spacingAndGlyphs"' if len(text) > 66 else ""
                out.write(f'<text x="{x+10}" y="{y+37+line*17}" font-size="11" fill="#172033"{fit}>{escape(text)}</text>')
            out.write('</g>\n')
        out.write('</g></svg>\n')
    viewer_data = {"nodes": nodes, "edges": edges, "target": target_id, "stats": stats,
                   "width": width, "height": height, "nodeWidth": W, "nodeHeight": H,
                   "sources": source_files, "audit": data["axiom_audit"]}
    template = (docs / "dependency_graph_viewer.html").read_text()
    encoded = json.dumps(viewer_data, ensure_ascii=False, separators=(",", ":")).replace("<", "\\u003c")
    (docs / f"{STEM}.html").write_text(template.replace("__GRAPH_DATA__", encoded))
    print(json.dumps(stats, indent=2), flush=True)
    print(f"Wrote {docs / STEM}.{{html,svg,dot,json}}", flush=True)
