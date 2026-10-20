import JT58.Coloring

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

theorem terminals_different :
    ∀ a b c d u v : Fin 4,
      a ≠ b → a ≠ c → a ≠ d →
      b ≠ c → b ≠ d → c ≠ d →
      u ≠ c → u ≠ d →
      v ≠ a → v ≠ b →
      u ≠ v := by
  decide

theorem triangle_obstruction :
    ∀ u v x y z : Fin 4,
      u ≠ v →
      x ≠ y → x ≠ z → y ≠ z →
      u ≠ x → u ≠ y → u ≠ z →
      v ≠ x → v ≠ y → v ≠ z →
      False := by
  intro u v x y z huv hxy hxz hyz hux huy huz hvx hvy hvz
  omega

theorem host_not_four_colorable : ¬ Colorable 4 := by
  intro h
  obtain ⟨c, hc⟩ := h
  have huv : c 6 ≠ c 8 :=
    terminals_different
      (c 0) (c 1) (c 4) (c 5) (c 6) (c 8)
      (hc 0 1 (by decide))
      (hc 0 4 (by decide))
      (hc 0 5 (by decide))
      (hc 1 4 (by decide))
      (hc 1 5 (by decide))
      (hc 4 5 (by decide))
      (hc 6 4 (by decide))
      (hc 6 5 (by decide))
      (hc 8 0 (by decide))
      (hc 8 1 (by decide))
  exact triangle_obstruction
    (c 6) (c 8) (c 2) (c 3) (c 7)
    huv
    (hc 2 3 (by decide))
    (hc 2 7 (by decide))
    (hc 3 7 (by decide))
    (hc 6 2 (by decide))
    (hc 6 3 (by decide))
    (hc 6 7 (by decide))
    (hc 8 2 (by decide))
    (hc 8 3 (by decide))
    (hc 8 7 (by decide))

end JT58
