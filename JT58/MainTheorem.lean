import JT58.SubgraphCoverage

namespace JT58

theorem every_four_critical_subgraph_induced :
    EveryFourCriticalSubgraphInduced := by
  classical
  intro H hcritical
  rcases subgraph_dichotomy H with hcore | hcolor
  · obtain ⟨j, hcontained⟩ := hcore
    have hvertices :
        ∀ v, H.vertex v → (coreGraph j).vertex v := by
      intro v hv
      apply Classical.byContradiction
      intro hmissing
      have hproper : (coreGraph j).ProperSubgraphOf H :=
        ⟨hcontained, Or.inl ⟨v, hv, hmissing⟩⟩
      exact all_cores_not_three_colorable j
        (hcritical.2.2 (coreGraph j) hproper)
    intro u v hu hv huv
    exact hcontained.2 u v
      (coreGraph_is_induced j u v
        (hvertices u hu) (hvertices v hv) huv)
  · exact False.elim (hcritical.2.1 hcolor)

theorem no_noninduced_four_critical_subgraph :
    ¬ ∃ H : Subgraph, H.Critical 4 ∧ ¬ H.IsInduced := by
  intro h
  obtain ⟨H, hcritical, hnoninduced⟩ := h
  exact hnoninduced
    (every_four_critical_subgraph_induced H hcritical)

theorem jt58_counterexample :
    HostCritical 5 ∧
    (∃ u v : Vertex, u ≠ v ∧ adjacent u v = false) ∧
    ¬ (∃ H : Subgraph, H.Critical 4 ∧ ¬ H.IsInduced) :=
  ⟨host_five_critical,
   ⟨0, 2, by decide, host_not_complete⟩,
   no_noninduced_four_critical_subgraph⟩

end JT58

#print axioms JT58.jt58_counterexample
