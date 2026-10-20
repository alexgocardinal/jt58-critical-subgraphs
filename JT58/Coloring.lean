import JT58.Graph

namespace JT58

def ProperColoring {k : Nat} (c : Vertex → Fin k) : Prop :=
  ∀ u v : Vertex, adjacent u v = true → c u ≠ c v

def Colorable (k : Nat) : Prop :=
  ∃ c : Vertex → Fin k, ProperColoring c

def fiveColoring (v : Vertex) : Fin 5 :=
  match v.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 2
  | _ => 3

theorem fiveColoring_proper : ProperColoring fiveColoring := by
  unfold ProperColoring
  decide

theorem host_five_colorable : Colorable 5 :=
  ⟨fiveColoring, fiveColoring_proper⟩

theorem host_not_complete :
    adjacent (0 : Vertex) (2 : Vertex) = false := by
  decide

end JT58
