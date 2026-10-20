import Std

namespace JT58

abbrev Vertex := Fin 9

def edges : List (Nat × Nat) :=
  [(0, 1), (0, 4), (0, 5), (0, 8),
   (1, 4), (1, 5), (1, 8),
   (2, 3), (2, 6), (2, 7), (2, 8),
   (3, 6), (3, 7), (3, 8),
   (4, 5), (4, 6), (5, 6),
   (6, 7), (7, 8)]

def adjacent (u v : Vertex) : Bool :=
  edges.contains (u.val, v.val) ||
  edges.contains (v.val, u.val)

theorem nineteen_edges : edges.length = 19 := by
  decide

theorem no_duplicate_edges : edges.Nodup := by
  decide

theorem valid_endpoints :
    edges.all (fun e => e.1 < e.2 && e.2 < 9) = true := by
  decide

theorem adjacency_symmetric :
    ∀ u v : Vertex, adjacent u v = adjacent v u := by
  decide

theorem no_loops :
    ∀ v : Vertex, adjacent v v = false := by
  decide

end JT58
