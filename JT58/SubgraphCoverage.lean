import JT58.CoreObstructions

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

noncomputable def Subgraph.selection (H : Subgraph) : Selection := by
  classical
  exact fun i => decide (H.edge (edgeU i) (edgeV i))

theorem selection_true_iff (H : Subgraph) (i : Fin 19) :
    H.selection i = true ↔ H.edge (edgeU i) (edgeV i) := by
  classical
  simp [Subgraph.selection]

theorem selection_coloring_gives_subgraph_coloring
    (H : Subgraph) (c : Vertex → Fin 3)
    (hc : SelectionColoring H.selection c) :
    ∀ u v, H.edge u v → c u ≠ c v := by
  intro u v huv
  obtain ⟨i, hi⟩ :=
    indexed_edges_cover_host u v (H.edge_in_host u v huv)
  rcases hi with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hs : H.selection i = true :=
      (selection_true_iff H i).mpr (by
        simpa only [hu, hv] using huv)
    simpa only [hu, hv] using hc i hs
  · have hs : H.selection i = true :=
      (selection_true_iff H i).mpr (by
        simpa only [hu, hv] using H.edge_symm u v huv)
    have hback : c v ≠ c u := by
      simpa only [hu, hv] using hc i hs
    exact Ne.symm hback

theorem selected_core_contained
    (H : Subgraph) (j : Fin 15)
    (hselected : (coreEdges j).all H.selection = true) :
    (coreGraph j).ContainedIn H := by
  have hindexed :
      ∀ i : Fin 19, i ∈ coreEdges j →
        H.edge (edgeU i) (edgeV i) := by
    intro i hi
    exact (selection_true_iff H i).mp
      (List.all_eq_true.mp hselected i hi)
  constructor
  · intro v hv
    obtain ⟨i, hi, heq⟩ := core_vertices_have_edges j v hv
    have hend := H.edge_endpoints _ _ (hindexed i hi)
    rcases heq with heq | heq
    · simpa only [heq] using hend.1
    · simpa only [heq] using hend.2
  · intro u v huv
    obtain ⟨i, hi⟩ :=
      indexed_edges_cover_host u v
        ((coreGraph j).edge_in_host u v huv)
    have hpair :
        (coreGraph j).edge (edgeU i) (edgeV i) := by
      rcases hi with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · simpa only [hu, hv] using huv
      · simpa only [hu, hv] using
          (coreGraph j).edge_symm u v huv
    have hbool : (coreEdges j).contains i = true := by
      rw [core_edges_match_vertices j i]
      simp [hpair.1, hpair.2.1]
    have himem : i ∈ coreEdges j := by
      simpa using hbool
    rcases hi with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simpa only [hu, hv] using hindexed i himem
    · simpa only [hu, hv] using
        H.edge_symm _ _ (hindexed i himem)

theorem subgraph_dichotomy (H : Subgraph) :
    (∃ j : Fin 15, (coreGraph j).ContainedIn H) ∨
    H.Colorable 3 := by
  rcases selection_dichotomy H.selection with hcore | hcolor
  · obtain ⟨j, hj⟩ := hcore
    exact Or.inl ⟨j, selected_core_contained H j hj⟩
  · obtain ⟨c, hc⟩ := hcolor
    exact Or.inr
      ⟨c, selection_coloring_gives_subgraph_coloring H c hc⟩

end JT58
