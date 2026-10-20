import JT58.EdgeDeletions

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

def incidentEdge (v : Vertex) : Fin 19 :=
  match v.val with
  | 0 => 0
  | 1 => 0
  | 2 => 7
  | 3 => 7
  | 4 => 1
  | 5 => 2
  | 6 => 8
  | 7 => 17
  | _ => 3

def ProperAfterVertexDeletion
    (removed : Vertex) (c : Vertex → Fin 4) : Prop :=
  ∀ u v : Vertex,
    u ≠ removed →
    v ≠ removed →
    adjacent u v = true →
    c u ≠ c v

theorem vertexDeletionColoring_proper :
    ∀ removed : Vertex,
      ProperAfterVertexDeletion removed
        (deletionColoring (incidentEdge removed)) := by
  unfold ProperAfterVertexDeletion
  decide

theorem all_vertex_deletions_four_colorable :
    ∀ removed : Vertex,
      ∃ c : Vertex → Fin 4,
        ProperAfterVertexDeletion removed c := by
  intro removed
  exact ⟨deletionColoring (incidentEdge removed),
    vertexDeletionColoring_proper removed⟩

end JT58
