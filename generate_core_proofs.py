from itertools import combinations
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

lines = [
    "import JT58.CoreGraphs",
    "",
    "set_option maxHeartbeats 0",
    "set_option maxRecDepth 100000",
    "",
    "namespace JT58",
    "",
]

for j, vertices in enumerate(cores):
    lines += [
        f"theorem core_{j}_not_three_colorable :",
        f"    ¬ (coreGraph {j}).Colorable 3 := by",
        "  intro h",
        "  obtain ⟨c, hc⟩ := h",
    ]
    for i, (u, v) in enumerate(edges):
        if u in vertices and v in vertices:
            lines += [
                f"  have h{i} : c {u} ≠ c {v} :=",
                f"    hc {u} {v} (by unfold coreGraph; decide)",
            ]
    lines += ["  omega", ""]

cases = " ∨ ".join(f"j = {j}" for j in range(15))
patterns = " | ".join("rfl" for _ in range(15))

lines += [
    "theorem all_cores_not_three_colorable (j : Fin 15) :",
    "    ¬ (coreGraph j).Colorable 3 := by",
    f"  have hj : {cases} := by omega",
    f"  rcases hj with {patterns}",
]
for j in range(15):
    lines.append(f"  · exact core_{j}_not_three_colorable")

lines += ["", "end JT58", ""]
Path("JT58/CoreObstructions.lean").write_text("\n".join(lines))
print("Generated the 15 non-three-colorability proofs.")
