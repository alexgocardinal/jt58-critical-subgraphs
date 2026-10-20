import JT58.Subgraphs

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

theorem edgeAt_bounds :
    ∀ i : Fin 19,
      (edgeAt i).1 < 9 ∧ (edgeAt i).2 < 9 := by
  decide

def edgeU (i : Fin 19) : Vertex :=
  ⟨(edgeAt i).1, (edgeAt_bounds i).1⟩

def edgeV (i : Fin 19) : Vertex :=
  ⟨(edgeAt i).2, (edgeAt_bounds i).2⟩

theorem indexed_edges_are_host_edges :
    ∀ i : Fin 19, adjacent (edgeU i) (edgeV i) = true := by
  decide

theorem indexed_edges_cover_host :
    ∀ u v : Vertex, adjacent u v = true →
      ∃ i : Fin 19,
        (edgeU i = u ∧ edgeV i = v) ∨
        (edgeU i = v ∧ edgeV i = u) := by
  decide

abbrev Selection := Fin 19 → Bool

def SelectionColoring
    (s : Selection) (c : Vertex → Fin 3) : Prop :=
  ∀ i : Fin 19,
    s i = true → c (edgeU i) ≠ c (edgeV i)

structure ThreeColorCertificate where
  colors : Vertex → Fin 3
  excluded : List (Fin 19)

def ThreeColorCertificate.Permitted
    (d : ThreeColorCertificate) (s : Selection) : Bool :=
  d.excluded.all (fun i => !(s i))

end JT58
