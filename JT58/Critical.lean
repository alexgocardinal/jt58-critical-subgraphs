import JT58.VertexDeletions

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JT58

structure Subgraph where
  vertex : Vertex → Prop
  edge : Vertex → Vertex → Prop
  edge_symm : ∀ u v, edge u v → edge v u
  edge_in_host : ∀ u v, edge u v → adjacent u v = true
  edge_endpoints : ∀ u v, edge u v → vertex u ∧ vertex v

def Subgraph.IsProper (H : Subgraph) : Prop :=
  (∃ v, ¬ H.vertex v) ∨
  (∃ u v, adjacent u v = true ∧ ¬ H.edge u v)

def Subgraph.Colorable (H : Subgraph) (k : Nat) : Prop :=
  ∃ c : Vertex → Fin k,
    ∀ u v, H.edge u v → c u ≠ c v

theorem edge_index_covers :
    ∀ u v : Vertex, adjacent u v = true →
      ∃ i : Fin 19,
        edgeAt i = (u.val, v.val) ∨
        edgeAt i = (v.val, u.val) := by
  decide

theorem same_oriented_edge {u v a b : Vertex}
    (h : (u.val, v.val) = (a.val, b.val)) :
    u = a ∧ v = b :=
  ⟨Fin.ext (congrArg Prod.fst h),
   Fin.ext (congrArg Prod.snd h)⟩

theorem all_proper_subgraphs_four_colorable
    (H : Subgraph) (hproper : H.IsProper) :
    H.Colorable 4 := by
  rcases hproper with hvertex | hedge
  · obtain ⟨removed, hmissing⟩ := hvertex
    obtain ⟨c, hc⟩ :=
      all_vertex_deletions_four_colorable removed
    refine ⟨c, ?_⟩
    intro u v huv
    have hu : u ≠ removed := by
      intro heq
      apply hmissing
      simpa [heq] using (H.edge_endpoints u v huv).1
    have hv : v ≠ removed := by
      intro heq
      apply hmissing
      simpa [heq] using (H.edge_endpoints u v huv).2
    exact hc u v hu hv (H.edge_in_host u v huv)
  · obtain ⟨a, b, hab, hmissing⟩ := hedge
    obtain ⟨i, hi⟩ := edge_index_covers a b hab
    obtain ⟨c, hc⟩ := all_edge_deletions_four_colorable i
    have havoid (u v : Vertex) (huv : H.edge u v) :
        (u.val, v.val) ≠ edgeAt i := by
      intro heq
      rcases hi with hi | hi
      · obtain ⟨rfl, rfl⟩ :=
          same_oriented_edge (heq.trans hi)
        exact hmissing huv
      · obtain ⟨rfl, rfl⟩ :=
          same_oriented_edge (heq.trans hi)
        exact hmissing (H.edge_symm _ _ huv)
    refine ⟨c, ?_⟩
    intro u v huv
    exact hc u v
      (H.edge_in_host u v huv)
      (havoid u v huv)
      (havoid v u (H.edge_symm u v huv))

def HostCritical (k : Nat) : Prop :=
  Colorable k ∧
  ¬ Colorable (k - 1) ∧
  ∀ H : Subgraph, H.IsProper → H.Colorable (k - 1)

theorem host_five_critical : HostCritical 5 :=
  ⟨host_five_colorable,
   host_not_four_colorable,
   all_proper_subgraphs_four_colorable⟩

end JT58
