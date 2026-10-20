import JT58.CoreGraphs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

theorem core_0_not_three_colorable :
    ¬ (coreGraph 0).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : c 0 ≠ c 1 :=
    hc 0 1 (by unfold coreGraph; decide)
  have h1 : c 0 ≠ c 4 :=
    hc 0 4 (by unfold coreGraph; decide)
  have h2 : c 0 ≠ c 5 :=
    hc 0 5 (by unfold coreGraph; decide)
  have h4 : c 1 ≠ c 4 :=
    hc 1 4 (by unfold coreGraph; decide)
  have h5 : c 1 ≠ c 5 :=
    hc 1 5 (by unfold coreGraph; decide)
  have h14 : c 4 ≠ c 5 :=
    hc 4 5 (by unfold coreGraph; decide)
  omega

theorem core_1_not_three_colorable :
    ¬ (coreGraph 1).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h7 : c 2 ≠ c 3 :=
    hc 2 3 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h9 : c 2 ≠ c 7 :=
    hc 2 7 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h12 : c 3 ≠ c 7 :=
    hc 3 7 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  omega

theorem core_2_not_three_colorable :
    ¬ (coreGraph 2).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h7 : c 2 ≠ c 3 :=
    hc 2 3 (by unfold coreGraph; decide)
  have h9 : c 2 ≠ c 7 :=
    hc 2 7 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h12 : c 3 ≠ c 7 :=
    hc 3 7 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_3_not_three_colorable :
    ¬ (coreGraph 3).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : c 0 ≠ c 1 :=
    hc 0 1 (by unfold coreGraph; decide)
  have h1 : c 0 ≠ c 4 :=
    hc 0 4 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h4 : c 1 ≠ c 4 :=
    hc 1 4 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h7 : c 2 ≠ c 3 :=
    hc 2 3 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  omega

theorem core_4_not_three_colorable :
    ¬ (coreGraph 4).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : c 0 ≠ c 1 :=
    hc 0 1 (by unfold coreGraph; decide)
  have h1 : c 0 ≠ c 4 :=
    hc 0 4 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h4 : c 1 ≠ c 4 :=
    hc 1 4 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h9 : c 2 ≠ c 7 :=
    hc 2 7 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_5_not_three_colorable :
    ¬ (coreGraph 5).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : c 0 ≠ c 1 :=
    hc 0 1 (by unfold coreGraph; decide)
  have h1 : c 0 ≠ c 4 :=
    hc 0 4 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h4 : c 1 ≠ c 4 :=
    hc 1 4 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h12 : c 3 ≠ c 7 :=
    hc 3 7 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_6_not_three_colorable :
    ¬ (coreGraph 6).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : c 0 ≠ c 1 :=
    hc 0 1 (by unfold coreGraph; decide)
  have h2 : c 0 ≠ c 5 :=
    hc 0 5 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h5 : c 1 ≠ c 5 :=
    hc 1 5 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h7 : c 2 ≠ c 3 :=
    hc 2 3 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  omega

theorem core_7_not_three_colorable :
    ¬ (coreGraph 7).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : c 0 ≠ c 1 :=
    hc 0 1 (by unfold coreGraph; decide)
  have h2 : c 0 ≠ c 5 :=
    hc 0 5 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h5 : c 1 ≠ c 5 :=
    hc 1 5 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h9 : c 2 ≠ c 7 :=
    hc 2 7 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_8_not_three_colorable :
    ¬ (coreGraph 8).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : c 0 ≠ c 1 :=
    hc 0 1 (by unfold coreGraph; decide)
  have h2 : c 0 ≠ c 5 :=
    hc 0 5 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h5 : c 1 ≠ c 5 :=
    hc 1 5 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h12 : c 3 ≠ c 7 :=
    hc 3 7 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_9_not_three_colorable :
    ¬ (coreGraph 9).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h1 : c 0 ≠ c 4 :=
    hc 0 4 (by unfold coreGraph; decide)
  have h2 : c 0 ≠ c 5 :=
    hc 0 5 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h7 : c 2 ≠ c 3 :=
    hc 2 3 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h14 : c 4 ≠ c 5 :=
    hc 4 5 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  omega

theorem core_10_not_three_colorable :
    ¬ (coreGraph 10).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h1 : c 0 ≠ c 4 :=
    hc 0 4 (by unfold coreGraph; decide)
  have h2 : c 0 ≠ c 5 :=
    hc 0 5 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h9 : c 2 ≠ c 7 :=
    hc 2 7 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h14 : c 4 ≠ c 5 :=
    hc 4 5 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_11_not_three_colorable :
    ¬ (coreGraph 11).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h1 : c 0 ≠ c 4 :=
    hc 0 4 (by unfold coreGraph; decide)
  have h2 : c 0 ≠ c 5 :=
    hc 0 5 (by unfold coreGraph; decide)
  have h3 : c 0 ≠ c 8 :=
    hc 0 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h12 : c 3 ≠ c 7 :=
    hc 3 7 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h14 : c 4 ≠ c 5 :=
    hc 4 5 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_12_not_three_colorable :
    ¬ (coreGraph 12).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h4 : c 1 ≠ c 4 :=
    hc 1 4 (by unfold coreGraph; decide)
  have h5 : c 1 ≠ c 5 :=
    hc 1 5 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h7 : c 2 ≠ c 3 :=
    hc 2 3 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h14 : c 4 ≠ c 5 :=
    hc 4 5 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  omega

theorem core_13_not_three_colorable :
    ¬ (coreGraph 13).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h4 : c 1 ≠ c 4 :=
    hc 1 4 (by unfold coreGraph; decide)
  have h5 : c 1 ≠ c 5 :=
    hc 1 5 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h8 : c 2 ≠ c 6 :=
    hc 2 6 (by unfold coreGraph; decide)
  have h9 : c 2 ≠ c 7 :=
    hc 2 7 (by unfold coreGraph; decide)
  have h10 : c 2 ≠ c 8 :=
    hc 2 8 (by unfold coreGraph; decide)
  have h14 : c 4 ≠ c 5 :=
    hc 4 5 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem core_14_not_three_colorable :
    ¬ (coreGraph 14).Colorable 3 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h4 : c 1 ≠ c 4 :=
    hc 1 4 (by unfold coreGraph; decide)
  have h5 : c 1 ≠ c 5 :=
    hc 1 5 (by unfold coreGraph; decide)
  have h6 : c 1 ≠ c 8 :=
    hc 1 8 (by unfold coreGraph; decide)
  have h11 : c 3 ≠ c 6 :=
    hc 3 6 (by unfold coreGraph; decide)
  have h12 : c 3 ≠ c 7 :=
    hc 3 7 (by unfold coreGraph; decide)
  have h13 : c 3 ≠ c 8 :=
    hc 3 8 (by unfold coreGraph; decide)
  have h14 : c 4 ≠ c 5 :=
    hc 4 5 (by unfold coreGraph; decide)
  have h15 : c 4 ≠ c 6 :=
    hc 4 6 (by unfold coreGraph; decide)
  have h16 : c 5 ≠ c 6 :=
    hc 5 6 (by unfold coreGraph; decide)
  have h17 : c 6 ≠ c 7 :=
    hc 6 7 (by unfold coreGraph; decide)
  have h18 : c 7 ≠ c 8 :=
    hc 7 8 (by unfold coreGraph; decide)
  omega

theorem all_cores_not_three_colorable (j : Fin 15) :
    ¬ (coreGraph j).Colorable 3 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact core_0_not_three_colorable
  · exact core_1_not_three_colorable
  · exact core_2_not_three_colorable
  · exact core_3_not_three_colorable
  · exact core_4_not_three_colorable
  · exact core_5_not_three_colorable
  · exact core_6_not_three_colorable
  · exact core_7_not_three_colorable
  · exact core_8_not_three_colorable
  · exact core_9_not_three_colorable
  · exact core_10_not_three_colorable
  · exact core_11_not_three_colorable
  · exact core_12_not_three_colorable
  · exact core_13_not_three_colorable
  · exact core_14_not_three_colorable

end JT58
