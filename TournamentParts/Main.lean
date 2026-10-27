import TournamentParts.Construction
import TournamentParts.Tucker
import TournamentParts.Interpretation

/-!
# Main theorem, relative to two explicit background principles

No `axiom` or `sorry` is used. The external inputs are visible arguments of
`main`: octahedral Tucker, and the small-induced-subgraph consequence of the
Erdos high-girth/high-chromatic theorem. See README for the precise boundary.
-/
namespace TournamentParts

/-- The finite statement chi(T) >= d, expressed without a minimum convention. -/
def ChromaticAtLeast {V : Type*} (T : V → V → Prop) (d : ℕ) : Prop :=
  ∀ k, k < d → ¬ ∃ c : V → Fin k, TProper T c

/-- The exact graph-existence input used in the construction. The usual Erdos
 theorem with girth > 2D and chromatic number > 2D supplies this package.
 The reduction from that classical theorem is not formalized here. -/
def ErdosInput : Prop :=
  ∀ D : ℕ, 4 ≤ D → ∃ N : ℕ, ∃ G : SimpleGraph (Fin N),
    2 * D + 1 ≤ N ∧ TriangleFree G ∧
    (¬ ∃ c : Fin N → Fin (2 * D), GProper G c) ∧
    SmallBipartite G (2 * D + 1)

/-- Encode a doubled palette in any sufficiently large even palette. -/
def doubledPalette {k D : ℕ} (hk : k ≤ D) (p : Fin k × Bool) : Fin (2 * D) :=
  ⟨2 * p.1.val + (if p.2 then 1 else 0), by
    have := p.1.isLt
    split <;> omega⟩

theorem doubledPalette_injective {k D : ℕ} (hk : k ≤ D) :
    Function.Injective (doubledPalette hk) := by
  intro ⟨a,b⟩ ⟨a',b'⟩ he
  have hv := congrArg Fin.val he
  simp only [doubledPalette] at hv
  cases b <;> cases b' <;> simp_all only [Bool.false_eq_true, reduceIte]
  all_goals first
    | have : a.val = a'.val := by omega
      exact Prod.ext (Fin.ext this) rfl
    | omega

/-- The lower bound for a triangle-free backedge tournament. -/
theorem backedge_chromaticAtLeast {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (hG : TriangleFree G) {D d : ℕ} (hd : d ≤ D)
    (hc : ¬ ∃ c : V → Fin (2 * D), GProper G c) :
    ChromaticAtLeast (backedge G) d := by
  intro k hk ⟨c, hcol⟩
  obtain ⟨c', hc'⟩ := triangleFree_backedge_recolor G hG c hcol
  have hkD : k ≤ D := by omega
  apply hc
  refine ⟨fun v => doubledPalette hkD (c' v), ?_⟩
  intro u v huv he
  exact hc' huv (doubledPalette_injective hkD he)

/-- No pair of triangles in opposite summands is complete in either direction. -/
def NoCrossCompletePair {X Y : Type*} (T : Sum X Y → Sum X Y → Prop) : Prop :=
  ∀ f g h u v w,
    Cyclic T (.inl f) (.inl g) (.inl h) →
    Cyclic T (.inr u) (.inr v) (.inr w) →
    ¬ CompleteTo T (.inl f) (.inl g) (.inl h) (.inr u) (.inr v) (.inr w) ∧
    ¬ CompleteTo T (.inr u) (.inr v) (.inr w) (.inl f) (.inl g) (.inl h)

/-- Paper Theorem 2.1. The two finite summands are the prescribed partition.
 This theorem is conditional on the explicitly named classical inputs. -/
theorem main (erdos : ErdosInput) (tucker : OctahedralTucker) (d : ℕ) :
    ∃ N : ℕ, ∃ T : Sum (Binary (Fin N)) (Fin N) →
        Sum (Binary (Fin N)) (Fin N) → Prop,
      IsTournament T ∧
      ChromaticAtLeast (fun f g => T (.inl f) (.inl g)) d ∧
      ChromaticAtLeast (fun u v => T (.inr u) (.inr v)) d ∧
      NoCrossCompletePair T := by
  classical
  let D := max d 4
  have hD : 4 ≤ D := le_max_right _ _
  have hd : d ≤ D := le_max_left _ _
  obtain ⟨N, G, hN, htri, hchrom, hsmall⟩ := erdos D hD
  letI : LinearOrder (Binary (Fin N)) :=
    LinearOrder.lift' (Fintype.equivFin (Binary (Fin N))) (Equiv.injective _)
  have h6 : ¬ ∃ c : Fin N → Fin 6, GProper G c := by
    rintro ⟨c, hc⟩
    apply hchrom
    refine ⟨fun v => ⟨(c v).val, by have := (c v).isLt; omega⟩, ?_⟩
    intro u v huv he
    apply hc huv
    apply Fin.ext
    exact congrArg (fun z : Fin (2 * D) => z.val) he
  have hBtri : TriangleFree (binaryGraph G) := binary_triangleFree G h6
  have hBchrom : ¬ ∃ c : Binary (Fin N) → Fin (2 * D),
      GProper (binaryGraph G) c := by
    rintro ⟨c, hc⟩
    exact binary_not_colorable_of_smallBipartite tucker hsmall
      (by omega) hN (by omega) c hc
  refine ⟨N, construction G, construction_isTournament G, ?_, ?_, ?_⟩
  · exact backedge_chromaticAtLeast (binaryGraph G) hBtri hd hBchrom
  · exact backedge_chromaticAtLeast G htri hd hchrom
  · intro f g h u v w hX hY
    exact construction_no_complete_pair G hX hY

/-- The prescribed-parts conjecture in the same finite model. -/
def PrescribedPartsConjecture : Prop :=
  ∃ d : ℕ, ∀ N : ℕ, ∀ T : Sum (Binary (Fin N)) (Fin N) →
      Sum (Binary (Fin N)) (Fin N) → Prop,
    IsTournament T →
    ChromaticAtLeast (fun f g => T (.inl f) (.inl g)) d →
    ChromaticAtLeast (fun u v => T (.inr u) (.inr v)) d →
    ¬ NoCrossCompletePair T

/-- Even the conjecture restricted to these finite vertex sets is false. -/
theorem not_prescribedPartsConjecture (erdos : ErdosInput)
    (tucker : OctahedralTucker) : ¬ PrescribedPartsConjecture := by
  rintro ⟨d, hd⟩
  obtain ⟨N, T, hT, hX, hY, hno⟩ := main erdos tucker d
  exact hd N T hT hX hY hno

/-- Numeric version of the main theorem, using the minimum number of
transitive color classes, rather than a coloring-obstruction abbreviation. -/
theorem main_chromaticNumber (erdos : ErdosInput) (tucker : OctahedralTucker)
    (d : ℕ) :
    ∃ N : ℕ, ∃ T : Sum (Binary (Fin N)) (Fin N) →
        Sum (Binary (Fin N)) (Fin N) → Prop,
      ∃ hT : IsTournament T,
        d ≤ tournamentChromaticNumber (fun f g => T (.inl f) (.inl g))
          (hT.comap Sum.inl Sum.inl_injective) ∧
        d ≤ tournamentChromaticNumber (fun u v => T (.inr u) (.inr v))
          (hT.comap Sum.inr Sum.inr_injective) ∧
        NoCrossCompletePair T := by
  obtain ⟨N, T, hT, hX, hY, hno⟩ := main erdos tucker d
  refine ⟨N, T, hT, ?_, ?_, hno⟩
  · exact (le_tournamentChromaticNumber_iff _ _ d).mpr hX
  · exact (le_tournamentChromaticNumber_iff _ _ d).mpr hY

/-- The conjecture for arbitrary finite prescribed parts, modeled as a
partition into two disjoint summands. The original conjecture implies this
statement by taking the two summands as its disjoint vertex subsets. -/
def FinitePartsConjecture : Prop :=
  ∃ d : ℕ, ∀ (X Y : Type), [Fintype X] → [Fintype Y] →
    ∀ T : Sum X Y → Sum X Y → Prop,
      IsTournament T →
      ChromaticAtLeast (fun f g => T (.inl f) (.inl g)) d →
      ChromaticAtLeast (fun u v => T (.inr u) (.inr v)) d →
      ¬ NoCrossCompletePair T

theorem not_finitePartsConjecture (erdos : ErdosInput)
    (tucker : OctahedralTucker) : ¬ FinitePartsConjecture := by
  rintro ⟨d, hd⟩
  obtain ⟨N, T, hT, hX, hY, hno⟩ := main erdos tucker d
  exact hd (Binary (Fin N)) (Fin N) T hT hX hY hno

end TournamentParts


