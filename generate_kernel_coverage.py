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
cores = [clique, triangle + [6], triangle + [8]]
cores += [
    list(t) + list(p) + [6, 8]
    for t in combinations(clique, 3)
    for p in combinations(triangle, 2)
]
core_indices = [
    [i for i, (u, v) in enumerate(edges) if u in vs and v in vs]
    for vs in cores
]

masks = set()
for tail in product(range(3), repeat=8):
    c = (0,) + tail
    masks.add(sum(
        1 << i for i, (u, v) in enumerate(edges) if c[u] != c[v]
    ))

maximal = sorted(
    m for m in masks
    if not any(m != n and (m & n) == m for n in masks)
)
excluded = [
    [i for i in range(19) if not (m & (1 << i))]
    for m in maximal
]
assert len(excluded) == 264

data = Path("JT58/CertificateData.lean").read_text()
stored = [
    [int(x) for x in entry.split(",") if x.strip()]
    for entry in re.findall(r"excluded := \[([0-9,\s]*)\]", data)
]
assert stored == excluded, "Certificate order mismatch."

lines = [
    "import JT58.CertificateData",
    "",
    "set_option maxHeartbeats 0",
    "set_option maxRecDepth 100000",
    "",
    "namespace JT58",
    "",
    "def corePresent (s : Selection) : Bool :=",
    "  coreEdgeLists.any (fun es => es.all s)",
    "",
    "def coverAvailable (s : Selection) : Bool :=",
    "  coverCertificates.any (fun d => d.Permitted s)",
    "",
]

cubes = []

for kind, groups in [("core", core_indices), ("color", excluded)]:
    for k, indices in enumerate(groups):
        value = "true" if kind == "core" else "false"
        assumptions = " ".join(
            f"(h{i} : s {i} = {value})" for i in indices
        )
        names = ", ".join(f"h{i}" for i in indices)
        lines += [
            f"theorem {kind}_witness_{k} (s : Selection) {assumptions} :",
            "    (corePresent s || coverAvailable s) = true := by",
        ]
        if kind == "core":
            lines += [
                "  have h : corePresent s = true := by",
                "    apply List.any_eq_true.mpr",
                f"    refine ⟨coreEdges {k}, by decide, ?_⟩",
                f"    change ({indices} : List (Fin 19)).all s = true",
                f"    simp [{names}]",
            ]
        else:
            lines += [
                "  have h : coverAvailable s = true := by",
                "    apply List.any_eq_true.mpr",
                f"    refine ⟨coverCertificates[{k}]'(by decide), ?_, ?_⟩",
                "    · exact List.getElem_mem (by decide)",
                "    · simp [ThreeColorCertificate.Permitted,",
                f"        coverCertificates, {names}]",
            ]
        lines += ["  simp [h]", ""]
        mask = sum(1 << i for i in indices)
        cubes.append({
            "kind": kind,
            "number": k,
            "indices": indices,
            "positive": mask if kind == "core" else 0,
            "negative": mask if kind == "color" else 0,
        })

lines += [
    "theorem every_selection_covered (s : Selection) :",
    "    (corePresent s || coverAvailable s) = true := by",
]

leaves = 0

def emit(candidates, positive, negative, indent):
    global leaves
    for c in candidates:
        if (c["positive"] & positive) == c["positive"] and \
           (c["negative"] & negative) == c["negative"]:
            args = " ".join(f"h{i}" for i in c["indices"])
            lines.append(
                " " * indent +
                f'exact {c["kind"]}_witness_{c["number"]} s {args}'
            )
            leaves += 1
            return

    scores = [0.0] * 19
    for c in candidates:
        remaining = (
            (c["positive"] | c["negative"]) &
            ~(positive | negative)
        )
        count = bin(remaining).count("1")
        for i in range(19):
            if remaining & (1 << i):
                scores[i] += 2.0 ** (-count)

    i = max(range(19), key=lambda i: scores[i])
    assert scores[i] > 0, "Uncovered branch."
    bit = 1 << i
    lines.append(" " * indent + f"cases h{i} : s {i} with")
    lines.append(" " * indent + "| false =>")
    emit(
        [c for c in candidates if not (c["positive"] & bit)],
        positive, negative | bit, indent + 2
    )
    lines.append(" " * indent + "| true =>")
    emit(
        [c for c in candidates if not (c["negative"] & bit)],
        positive | bit, negative, indent + 2
    )

emit(cubes, 0, 0, 2)
lines += [
    "",
    "end JT58",
    "",
    "#print axioms JT58.every_selection_covered",
    "",
]
Path("JT58/KernelCoverage.lean").write_text("\n".join(lines))
print(f"Generated a direct proof with {leaves} terminal branches.")
