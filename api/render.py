from xml.etree import ElementTree as ET

import graphviz

# svg xml namespace needed to find <g>/<title> elements
SVG_NS = "http://www.w3.org/2000/svg"


def severity_colors(severity):
    if severity >= 2: # severity >=2 (custom, unsafe, sorry) is red
        return ("#fdecea", "#c0392b", "#c0392b")
    if severity == 1: # severity 1 (trust) is yellow
        return ("#fef9e7", "#e6b800", "#ca8a04")
    return ("#eafaf1", "#7dcea0", "#1e7a46") # severity 0 is green


# build graphviz graph
def build_graph(nodes, edges):
    g = graphviz.Digraph()
    g.attr(bgcolor="transparent", rankdir="TB", ranksep="1.8", nodesep="0.18") # TB = top to bottom, ranksep is the vertical gap between layers, nodesep the horizontal gap within one
    g.attr("node", shape="box", style="rounded,filled", fontname="Helvetica", fontsize="12", margin="0.2,0.07")
    g.attr("edge", color="#cccccc", arrowsize="0.5")

    # one box per declaration, colored by severity, labeled with just the leaf name
    for n in nodes:
        fill, line, font = severity_colors(n["severity"])
        g.node(str(n["id"]), label=n["name"].split(".")[-1], fillcolor=fill, color=line, fontcolor=font)

    # roots go to the top row (rank=min)
    targets = {e["to_id"] for e in edges}
    roots = [n for n in nodes if n["id"] not in targets]
    if roots:
        with g.subgraph() as s:
            s.attr(rank="min")
            for n in roots:
                s.node(str(n["id"]))

    # draw arrow from edge "from_id" to edge "to_id"
    for e in edges:
        g.edge(str(e["from_id"]), str(e["to_id"]))

    return g

# add data attributes so the frontend can identify nodes/edges on click
def annotate_svg(svg):
    ET.register_namespace("", SVG_NS) # write tags back as plain <g>/<path>
    root = ET.fromstring(svg[svg.find("<svg"):]) # top svg element
    ns = f"{{{SVG_NS}}}" # namespace string to find elements

    # move each node/edge id from its <title> onto data-* attributes, then remove the <title>
    # for example, <g class="node"><title>5</title>...</g> becomes <g class="node" data-id="5">...</g>
    for g in root.iter(f"{ns}g"):
        title = g.find(f"{ns}title")
        if title is None:
            continue
        text = title.text or ""
        if g.get("class") == "node":
            g.set("data-id", text)
        elif g.get("class") == "edge" and "->" in text:
            frm, to = text.split("->", 1)
            g.set("data-from", frm)
            g.set("data-to", to)
        g.remove(title)
    return ET.tostring(root, encoding="unicode")


# graph data -> graphviz svg -> annotated svg
def render_svg(nodes, edges):
    svg = build_graph(nodes, edges).pipe(format="svg", encoding="utf-8")
    return annotate_svg(svg)
