import JT58.CertificateMeaning

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

def coreGraph (j : Fin 15) : Subgraph where
  vertex := fun v => coreVertices j v = true
  edge := fun u v =>
    coreVertices j u = true ∧
    coreVertices j v = true ∧
    adjacent u v = true
  edge_symm := by
    intro u v h
    exact ⟨h.2.1, h.1,
      (adjacency_symmetric v u).trans h.2.2⟩
  edge_in_host := by
    intro u v h
    exact h.2.2
  edge_endpoints := by
    intro u v h
    exact ⟨h.1, h.2.1⟩

theorem coreGraph_is_induced (j : Fin 15) :
    (coreGraph j).IsInduced := by
  intro u v hu hv huv
  exact ⟨hu, hv, huv⟩

theorem coreGraph_contains_indexed_edges :
    ∀ j : Fin 15, ∀ i : Fin 19,
      i ∈ coreEdges j →
      (coreGraph j).edge (edgeU i) (edgeV i) := by
  unfold coreGraph
  decide

end JT58
