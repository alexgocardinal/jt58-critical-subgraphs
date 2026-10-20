from itertools import combinations, product
from pathlib import Path
import re

source = Path("JT58/Graph.lean").read_text()
edges = [
    (int(a), int(b))
    for a, b in re.findall(r"\((\d+),\s*(\d+)\)", source)
]
assert len(edges) == 19

clique = [0, 1, 4, 5]
triangle = [2, 3, 7]

cores = [
    sorted(clique),
    sorted(triangle + [6]),
    sorted(triangle + [8]),
]
cores += [
    sorted(list(t) + list(p) + [6, 8])
    for t in combinations(clique, 3)
    for p in combinations(triangle, 2)
]
assert len(cores) == 15

core_edges = [
    [i for i, (u, v) in enumerate(edges) if u in vs and v in vs]
    for vs in cores
]

colorings = {}
for tail in product(range(3), repeat=8):
    colors = (0,) + tail
    mask = sum(
        1 << i
        for i, (u, v) in enumerate(edges)
        if colors[u] != colors[v]
    )
    colorings.setdefault(mask, colors)

maximal = sorted(
    m for m in colorings
    if not any(m != n and (m & n) == m for n in colorings)
)
assert len(maximal) == 264

def lean_list(xs):
    return "[" + ",".join(map(str, xs)) + "]"

lines = [
    "import JT58.Selections",
    "",
    "set_option maxHeartbeats 0",
    "set_option maxRecDepth 100000",
    "",
    "namespace JT58",
    "",
    "def coreVertexLists : List (List Vertex) := [",
    ",\n".join("  " + lean_list(vs) for vs in cores),
    "]",
    "",
    "def coreEdgeLists : List (List (Fin 19)) := [",
    ",\n".join("  " + lean_list(es) for es in core_edges),
    "]",
    "",
    "def coreVertices (j : Fin 15) (v : Vertex) : Bool :=",
    "  (coreVertexLists[j.val]!).contains v",
    "",
    "def coreEdges (j : Fin 15) : List (Fin 19) :=",
    "  coreEdgeLists[j.val]!",
    "",
    "def coverCertificates : List ThreeColorCertificate := [",
]

entries = []
for mask in maximal:
    colors = colorings[mask]
    excluded = [
        i for i, (u, v) in enumerate(edges)
        if colors[u] == colors[v]
    ]
    entries.append(
        "  { colors := fun v => ("
        + lean_list(colors)
        + " : List (Fin 3))[v.val]!, excluded := "
        + lean_list(excluded)
        + " }"
    )

lines += [
    ",\n".join(entries),
    "]",
    "",
    "def certificateValid (d : ThreeColorCertificate) : Bool :=",
    "  (List.finRange 19).all (fun i =>",
    "    (d.colors (edgeU i) != d.colors (edgeV i)) ||",
    "    d.excluded.contains i)",
    "",
    "theorem certificate_data_valid :",
    "    coverCertificates.all certificateValid = true := by",
    "  decide",
    "",
    "theorem core_edges_match_vertices :",
    "    ∀ j : Fin 15, ∀ i : Fin 19,",
    "      (coreEdges j).contains i =",
    "        (coreVertices j (edgeU i) &&",
    "         coreVertices j (edgeV i)) := by",
    "  decide",
    "",
    "theorem core_vertices_have_edges :",
    "    ∀ j : Fin 15, ∀ v : Vertex,",
    "      coreVertices j v = true →",
    "      ∃ i : Fin 19, i ∈ coreEdges j ∧",
    "        (edgeU i = v ∨ edgeV i = v) := by",
    "  decide",
    "",
    "end JT58",
]

Path("JT58/CertificateData.lean").write_text("\n".join(lines) + "\n")
print("Generated 15 cores and 264 three-coloring certificates.")
