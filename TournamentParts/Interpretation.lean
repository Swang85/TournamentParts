import TournamentParts.Core
import Mathlib.Data.Nat.Find

/-!
# Meaning of tournament coloring and chromatic lower bounds

The main development represents a tournament coloring by the absence of
monochromatic cyclic triangles. This file proves that each such color class
has a transitive arc relation, and defines its ordinary minimum chromatic
number for finite tournaments.
-/

namespace TournamentParts

variable {V C : Type*}

/-- Restricting or transporting a tournament along an injection preserves the
tournament axioms. This includes the two injections into the disjoint sum used
in the paper's construction. -/
theorem IsTournament.comap {W : Type*} {T : V → V → Prop}
    (hT : IsTournament T) (f : W → V) (hf : Function.Injective f) :
    IsTournament (fun a b => T (f a) (f b)) := by
  refine ⟨fun a => hT.1 (f a), ?_, ?_⟩
  · intro a b hab
    exact hT.2.1 (f a) (f b) hab
  · intro a b hab
    exact hT.2.2 (f a) (f b) (fun he => hab (hf he))

/-- A coloring restricts along any vertex map. -/
theorem TProper.comap {W : Type*} {T : V → V → Prop} {c : V → C}
    (hc : TProper T c) (f : W → V) :
    TProper (fun a b => T (f a) (f b)) (fun a => c (f a)) := by
  intro a b z hcyc hab hbz
  exact hc (f a) (f b) (f z) hcyc hab hbz

/-- Transitivity of the arc relation on every color class. -/
def ColorClassesTransitive (T : V → V → Prop) (c : V → C) : Prop :=
  ∀ a b z, c a = c b → c b = c z → T a b → T b z → T a z

/-- In a tournament, a color class has no cyclic triangle exactly when its
arc relation is transitive. The inherited irreflexivity and totality make this
a strict total ordering on that color class. -/
theorem tproper_iff_colorClassesTransitive (T : V → V → Prop)
    (hT : IsTournament T) (c : V → C) :
    TProper T c ↔ ColorClassesTransitive T c := by
  constructor
  · intro hc a b z hab hbz habArc hbzArc
    have haz : a ≠ z := by
      intro he
      subst z
      exact hT.2.1 a b habArc hbzArc
    rcases hT.2.2 a z haz with hazArc | hzaArc
    · exact hazArc
    · exact (hc a b z ⟨habArc, hbzArc, hzaArc⟩ hab hbz).elim
  · intro hc a b z hcyc hab hbz
    exact hT.2.1 a z (hc a b z hab hbz hcyc.1 hcyc.2.1) hcyc.2.2

/-- Every finite tournament can be colored by giving each vertex its own color. -/
theorem finite_tournament_colorable [Fintype V] (T : V → V → Prop)
    (hT : IsTournament T) : ∃ k : ℕ, ∃ c : V → Fin k, TProper T c := by
  classical
  refine ⟨Fintype.card V, Fintype.equivFin V, ?_⟩
  intro a b z hcyc hab _
  have he : a = b := (Fintype.equivFin V).injective hab
  subst b
  exact hT.1 a hcyc.1

/-- The usual tournament chromatic number: the least number of transitive
color classes. It is zero for an empty tournament. -/
noncomputable def tournamentChromaticNumber [Fintype V] (T : V → V → Prop)
    (hT : IsTournament T) : ℕ := by
  classical
  exact Nat.find (finite_tournament_colorable T hT)

/-- The coloring-obstruction formulation used in the main theorem is exactly
the numerical lower bound on the usual chromatic number. -/
theorem le_tournamentChromaticNumber_iff [Fintype V] (T : V → V → Prop)
    (hT : IsTournament T) (d : ℕ) :
    d ≤ tournamentChromaticNumber T hT ↔
      ∀ k : ℕ, k < d → ¬ ∃ c : V → Fin k, TProper T c := by
  classical
  unfold tournamentChromaticNumber
  exact Nat.le_find_iff (finite_tournament_colorable T hT) d

/-- The minimum is attained. -/
theorem tournamentChromaticNumber_colorable [Fintype V] (T : V → V → Prop)
    (hT : IsTournament T) :
    ∃ c : V → Fin (tournamentChromaticNumber T hT), TProper T c := by
  classical
  exact Nat.find_spec (finite_tournament_colorable T hT)

end TournamentParts

