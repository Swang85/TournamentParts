import TournamentParts.Core

/-!
# Backedge tournaments

This file proves the coloring facts needed from Proposition 3.2 of the paper.
In particular the triangle-free factor-two bound is proved directly, without
assuming the more general clique-number inequality.
-/

namespace TournamentParts

variable {V : Type*} [LinearOrder V]

/-- A graph edge points backwards; a graph nonedge points forwards. -/
def backedge (G : SimpleGraph V) (u v : V) : Prop :=
  (u < v ∧ ¬ G.Adj u v) ∨ (v < u ∧ G.Adj u v)

theorem backedge_irrefl (G : SimpleGraph V) (u : V) : ¬ backedge G u u := by
  simp [backedge]

theorem backedge_asymm (G : SimpleGraph V) {u v : V}
    (h : backedge G u v) : ¬ backedge G v u := by
  intro h'
  rcases h with ⟨huv, hn⟩ | ⟨hvu, he⟩
  · rcases h' with ⟨hvu, _⟩ | ⟨_, he⟩
    · exact lt_asymm huv hvu
    · exact hn (G.symm he)
  · rcases h' with ⟨_, hn⟩ | ⟨huv, _⟩
    · exact hn (G.symm he)
    · exact lt_asymm hvu huv

theorem backedge_total (G : SimpleGraph V) {u v : V} (h : u ≠ v) :
    backedge G u v ∨ backedge G v u := by
  by_cases he : G.Adj u v
  · rcases lt_or_gt_of_ne h with huv | hvu
    · exact Or.inr (Or.inr ⟨huv, G.symm he⟩)
    · exact Or.inl (Or.inr ⟨hvu, he⟩)
  · rcases lt_or_gt_of_ne h with huv | hvu
    · exact Or.inl (Or.inl ⟨huv, he⟩)
    · exact Or.inr (Or.inl ⟨hvu, fun he' => he (G.symm he')⟩)

/-- The backedge orientation is a tournament. -/
theorem backedge_isTournament (G : SimpleGraph V) : IsTournament (backedge G) := by
  exact ⟨backedge_irrefl G, fun _ _ h => backedge_asymm G h,
    fun _ _ h => backedge_total G h⟩

/-- Every cyclic triangle contains an edge of the backedge graph. -/
theorem backedge_cyclic_has_edge (G : SimpleGraph V) {a b c : V}
    (h : Cyclic (backedge G) a b c) :
    G.Adj a b ∨ G.Adj b c ∨ G.Adj c a := by
  by_cases hab : G.Adj a b
  · exact Or.inl hab
  by_cases hbc : G.Adj b c
  · exact Or.inr (Or.inl hbc)
  by_cases hca : G.Adj c a
  · exact Or.inr (Or.inr hca)
  have hab' : a < b := by
    rcases h.1 with h | h
    · exact h.1
    · exact (hab h.2).elim
  have hbc' : b < c := by
    rcases h.2.1 with h | h
    · exact h.1
    · exact (hbc h.2).elim
  have hca' : c < a := by
    rcases h.2.2 with h | h
    · exact h.1
    · exact (hca h.2).elim
  exact (lt_irrefl a (lt_trans hab' (lt_trans hbc' hca'))).elim

/-- Any proper graph coloring is a tournament coloring. -/
theorem graph_coloring_backedge (G : SimpleGraph V) {C : Type*}
    (c : V → C) (hc : GProper G c) : TProper (backedge G) c := by
  intro a b z h hab hbz
  rcases backedge_cyclic_has_edge G h with he | he | he
  · exact hc he hab
  · exact hc he hbz
  · exact hc he (hab.trans hbz).symm

/-- The refinement bit records an earlier graph neighbor of the same color. -/
def hasEarlierNeighbor (G : SimpleGraph V) {C : Type*} (c : V → C) (v : V) : Prop :=
  ∃ u, u < v ∧ G.Adj u v ∧ c u = c v

/-- For an edge with equal tournament colors, precisely its later endpoint
has the refinement bit. Triangle-freeness rules out a two-edge predecessor
chain, since the missing third edge would make a monochromatic cyclic triangle. -/
theorem earlierNeighbor_separates (G : SimpleGraph V) (hG : TriangleFree G)
    {C : Type*} (c : V → C) (hc : TProper (backedge G) c)
    {u v : V} (huv : u < v) (he : G.Adj u v) (hcol : c u = c v) :
    ¬ hasEarlierNeighbor G c u ∧ hasEarlierNeighbor G c v := by
  constructor
  · rintro ⟨w, hwu, hwe, hwcol⟩
    have hn : ¬ G.Adj w v := by
      intro hwv
      exact hG w u v hwe he (G.symm hwv)
    apply hc w v u
    · exact ⟨Or.inl ⟨lt_trans hwu huv, hn⟩,
        Or.inr ⟨huv, G.symm he⟩, Or.inr ⟨hwu, G.symm hwe⟩⟩
    · exact hwcol.trans hcol
    · exact hcol.symm
  · exact ⟨u, huv, he, hcol⟩

/-- A tournament coloring of the backedge tournament of a triangle-free graph
refines to a graph coloring by doubling the palette. -/
theorem triangleFree_backedge_recolor (G : SimpleGraph V) (hG : TriangleFree G)
    {C : Type*} (c : V → C) (hc : TProper (backedge G) c) :
    ∃ d : V → C × Bool, GProper G d := by
  classical
  let d : V → C × Bool := fun v => (c v, decide (hasEarlierNeighbor G c v))
  refine ⟨d, ?_⟩
  intro u v he hd
  have hcol : c u = c v := congrArg Prod.fst hd
  have hbit : decide (hasEarlierNeighbor G c u) =
      decide (hasEarlierNeighbor G c v) := congrArg Prod.snd hd
  have huv : u ≠ v := by
    intro h
    subst v
    exact G.loopless u he
  rcases lt_or_gt_of_ne huv with huv | hvu
  · obtain ⟨hu, hv⟩ := earlierNeighbor_separates G hG c hc huv he hcol
    simp [hu, hv] at hbit
  · obtain ⟨hv, hu⟩ := earlierNeighbor_separates G hG c hc hvu (G.symm he) hcol.symm
    simp [hu, hv] at hbit

end TournamentParts

