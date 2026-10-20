import JT58.Critical

namespace JT58

def Subgraph.ContainedIn (K H : Subgraph) : Prop :=
  (∀ v, K.vertex v → H.vertex v) ∧
  (∀ u v, K.edge u v → H.edge u v)

def Subgraph.ProperSubgraphOf (K H : Subgraph) : Prop :=
  K.ContainedIn H ∧
  ((∃ v, H.vertex v ∧ ¬ K.vertex v) ∨
   (∃ u v, H.edge u v ∧ ¬ K.edge u v))

def Subgraph.Critical (H : Subgraph) (k : Nat) : Prop :=
  H.Colorable k ∧
  ¬ H.Colorable (k - 1) ∧
  ∀ K : Subgraph,
    K.ProperSubgraphOf H → K.Colorable (k - 1)

def Subgraph.IsInduced (H : Subgraph) : Prop :=
  ∀ u v,
    H.vertex u →
    H.vertex v →
    adjacent u v = true →
    H.edge u v

def EveryFourCriticalSubgraphInduced : Prop :=
  ∀ H : Subgraph, H.Critical 4 → H.IsInduced

end JT58
