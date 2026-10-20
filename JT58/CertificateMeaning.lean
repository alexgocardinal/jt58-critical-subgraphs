import JT58.Coverage

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

theorem bool_or_true_cases :
    ∀ a b : Bool,
      (a || b) = true → a = true ∨ b = true := by
  decide

theorem permitted_certificate_colors
    (d : ThreeColorCertificate)
    (hd : d ∈ coverCertificates)
    (s : Selection)
    (hp : d.Permitted s = true) :
    SelectionColoring s d.colors := by
  have checks :
      (List.finRange 19).all (fun i =>
        (d.colors (edgeU i) != d.colors (edgeV i)) ||
        d.excluded.contains i) = true :=
    List.all_eq_true.mp certificate_data_valid d hd
  intro i hs
  have check :=
    List.all_eq_true.mp checks i (by simp)
  rcases bool_or_true_cases _ _ check with hdiff | hexcluded
  · simpa using hdiff
  · have himem : i ∈ d.excluded := by
      simpa using hexcluded
    have hn : !(s i) = true :=
      List.all_eq_true.mp hp i himem
    simp [hs] at hn

theorem core_lists_indexed :
    coreEdgeLists = (List.finRange 15).map coreEdges := by
  decide

theorem selection_dichotomy (s : Selection) :
    (∃ j : Fin 15, (coreEdges j).all s = true) ∨
    (∃ c : Vertex → Fin 3, SelectionColoring s c) := by
  rcases bool_or_true_cases _ _ (every_selection_covered s)
    with hcore | hcolor
  · obtain ⟨es, hes, hselected⟩ :=
      List.any_eq_true.mp hcore
    rw [core_lists_indexed] at hes
    obtain ⟨j, _, hje⟩ := List.mem_map.mp hes
    left
    refine ⟨j, ?_⟩
    simpa only [hje] using hselected
  · obtain ⟨d, hd, hp⟩ :=
      List.any_eq_true.mp hcolor
    right
    exact ⟨d.colors, permitted_certificate_colors d hd s hp⟩

end JT58
