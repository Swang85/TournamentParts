import TournamentParts.Backedge
import TournamentParts.Binary

/-!
# The two-part tournament construction

The cross edges read a Boolean function: true means X to Y.
The absence of complete pairs is unconditional: it holds for every base graph.
-/

namespace TournamentParts

variable {V : Type*} [LinearOrder V] [LinearOrder (Binary V)]

/-- The disjoint union realizes the partition into binary functions and base vertices. -/
def construction (G : SimpleGraph V) : Sum (Binary V) V → Sum (Binary V) V → Prop
  | .inl f, .inl g => backedge (binaryGraph G) f g
  | .inr u, .inr v => backedge G u v
  | .inl f, .inr v => f v = true
  | .inr v, .inl f => f v = false

theorem construction_isTournament (G : SimpleGraph V) :
    IsTournament (construction G) := by
  constructor
  · intro v
    cases v with
    | inl f => exact backedge_irrefl _ f
    | inr v => exact backedge_irrefl _ v
  constructor
  · intro u v h h'
    cases u with
    | inl f =>
      cases v with
      | inl g => exact backedge_asymm _ h h'
      | inr v => simp_all [construction]
    | inr u =>
      cases v with
      | inl g => simp_all [construction]
      | inr v => exact backedge_asymm _ h h'
  · intro u v huv
    cases u with
    | inl f =>
      cases v with
      | inl g => exact backedge_total _ (fun h => huv (congrArg Sum.inl h))
      | inr v => cases h : f v <;> simp [construction, h]
    | inr u =>
      cases v with
      | inl g => cases h : g u <;> simp [construction, h]
      | inr v => exact backedge_total _ (fun h => huv (congrArg Sum.inr h))

/-- A monochromatic common sign class of adjacent functions contains no Y triangle. -/

theorem adjacent_common_sign_no_triangle (G : SimpleGraph V)
    {f g : Binary V} (hfg : (binaryGraph G).Adj f g)
    (b : Bool) {u v w : V} (huv : Cyclic (backedge G) u v w)
    (hu : f u = b ∧ g u = b) (hv : f v = b ∧ g v = b)
    (hw : f w = b ∧ g w = b) : False := by
  rcases backedge_cyclic_has_edge G huv with he | he | he
  · exact hfg.2 he b ⟨hu.1, hu.2, hv.1, hv.2⟩
  · exact hfg.2 he b ⟨hv.1, hv.2, hw.1, hw.2⟩
  · exact hfg.2 he b ⟨hw.1, hw.2, hu.1, hu.2⟩

/-- The common in- and out-neighborhoods of an X triangle have no Y triangle. -/
theorem common_sign_no_triangle (G : SimpleGraph V)
    {f g h : Binary V} (hX : Cyclic (backedge (binaryGraph G)) f g h)
    (b : Bool) {u v w : V} (hY : Cyclic (backedge G) u v w)
    (hcross : ∀ a, a = f ∨ a = g ∨ a = h →
      ∀ z, z = u ∨ z = v ∨ z = w → a z = b) : False := by
  have hf := hcross f (Or.inl rfl)
  have hg := hcross g (Or.inr (Or.inl rfl))
  have hh := hcross h (Or.inr (Or.inr rfl))
  rcases backedge_cyclic_has_edge (binaryGraph G) hX with he | he | he
  · exact adjacent_common_sign_no_triangle G he b hY
      ⟨hf u (Or.inl rfl), hg u (Or.inl rfl)⟩
      ⟨hf v (Or.inr (Or.inl rfl)), hg v (Or.inr (Or.inl rfl))⟩
      ⟨hf w (Or.inr (Or.inr rfl)), hg w (Or.inr (Or.inr rfl))⟩
  · exact adjacent_common_sign_no_triangle G he b hY
      ⟨hg u (Or.inl rfl), hh u (Or.inl rfl)⟩
      ⟨hg v (Or.inr (Or.inl rfl)), hh v (Or.inr (Or.inl rfl))⟩
      ⟨hg w (Or.inr (Or.inr rfl)), hh w (Or.inr (Or.inr rfl))⟩
  · exact adjacent_common_sign_no_triangle G he b hY
      ⟨hh u (Or.inl rfl), hf u (Or.inl rfl)⟩
      ⟨hh v (Or.inr (Or.inl rfl)), hf v (Or.inr (Or.inl rfl))⟩
      ⟨hh w (Or.inr (Or.inr rfl)), hf w (Or.inr (Or.inr rfl))⟩

/-- Every edge from one listed triangle to the other points forward. -/
def CompleteTo {W : Type*} (T : W → W → Prop)
    (a b c u v w : W) : Prop :=
  ∀ x, x = a ∨ x = b ∨ x = c →
    ∀ y, y = u ∨ y = v ∨ y = w → T x y

/-- No two cyclic triangles in opposite prescribed parts form a complete pair. -/
theorem construction_no_complete_pair (G : SimpleGraph V)
    {f g h : Binary V} {u v w : V}
    (hX : Cyclic (construction G) (.inl f) (.inl g) (.inl h))
    (hY : Cyclic (construction G) (.inr u) (.inr v) (.inr w)) :
    ¬ CompleteTo (construction G) (.inl f) (.inl g) (.inl h)
        (.inr u) (.inr v) (.inr w) ∧
    ¬ CompleteTo (construction G) (.inr u) (.inr v) (.inr w)
        (.inl f) (.inl g) (.inl h) := by
  constructor
  · intro hc
    apply common_sign_no_triangle G hX true hY
    intro a ha z hz
    apply hc (.inl a) _ (.inr z) _
    · rcases ha with rfl | rfl | rfl <;> simp
    · rcases hz with rfl | rfl | rfl <;> simp
  · intro hc
    apply common_sign_no_triangle G hX false hY
    intro a ha z hz
    apply hc (.inr z) _ (.inl a) _
    · rcases hz with rfl | rfl | rfl <;> simp
    · rcases ha with rfl | rfl | rfl <;> simp

end TournamentParts


