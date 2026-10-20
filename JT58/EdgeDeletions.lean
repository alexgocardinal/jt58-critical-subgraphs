import JT58.NonFour

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

def edgeAt (i : Fin 19) : Nat × Nat :=
  edges[i.val]!

def ProperAfterEdgeDeletion
    (i : Fin 19) (c : Vertex → Fin 4) : Prop :=
  ∀ u v : Vertex,
    adjacent u v = true →
    (u.val, v.val) ≠ edgeAt i →
    (v.val, u.val) ≠ edgeAt i →
    c u ≠ c v

def deletionColoring (i : Fin 19) (v : Vertex) : Fin 4 :=
  match i.val with
  | 0 => ([3,3,1,2,1,2,0,3,0] : List (Fin 4))[v.val]!
  | 1 => ([3,1,1,2,3,2,0,3,0] : List (Fin 4))[v.val]!
  | 2 => ([3,1,1,2,2,3,0,3,0] : List (Fin 4))[v.val]!
  | 3 => ([0,1,1,2,2,3,0,3,0] : List (Fin 4))[v.val]!
  | 4 => ([1,3,1,2,3,2,0,3,0] : List (Fin 4))[v.val]!
  | 5 => ([1,3,1,2,2,3,0,3,0] : List (Fin 4))[v.val]!
  | 6 => ([1,0,1,2,2,3,0,3,0] : List (Fin 4))[v.val]!
  | 7 => ([0,3,3,3,1,2,0,2,1] : List (Fin 4))[v.val]!
  | 8 => ([1,2,1,2,0,3,1,3,0] : List (Fin 4))[v.val]!
  | 9 => ([0,1,2,1,2,3,0,2,3] : List (Fin 4))[v.val]!
  | 10 => ([0,1,3,1,2,3,0,2,3] : List (Fin 4))[v.val]!
  | 11 => ([1,2,2,1,0,3,1,3,0] : List (Fin 4))[v.val]!
  | 12 => ([0,1,1,2,2,3,0,2,3] : List (Fin 4))[v.val]!
  | 13 => ([0,1,1,3,2,3,0,2,3] : List (Fin 4))[v.val]!
  | 14 => ([1,2,1,2,3,3,0,3,0] : List (Fin 4))[v.val]!
  | 15 => ([1,2,1,2,0,3,0,3,0] : List (Fin 4))[v.val]!
  | 16 => ([1,2,1,2,3,0,0,3,0] : List (Fin 4))[v.val]!
  | 17 => ([1,2,2,3,0,3,1,1,0] : List (Fin 4))[v.val]!
  | 18 => ([0,1,1,2,2,3,0,3,3] : List (Fin 4))[v.val]!
  | _ => 0

theorem deletionColoring_proper :
    ∀ i : Fin 19,
      ProperAfterEdgeDeletion i (deletionColoring i) := by
  unfold ProperAfterEdgeDeletion
  decide

theorem all_edge_deletions_four_colorable :
    ∀ i : Fin 19,
      ∃ c : Vertex → Fin 4, ProperAfterEdgeDeletion i c := by
  intro i
  exact ⟨deletionColoring i, deletionColoring_proper i⟩

end JT58
