import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.SplitIfs

namespace TournamentParts

abbrev Binary (V : Type*) := V → Bool

def GProper {V C : Type*} (G : SimpleGraph V) (c : V → C) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False

def Cyclic {V : Type*} (T : V → V → Prop) (a b c : V) : Prop :=
  T a b ∧ T b c ∧ T c a

def TProper {V C : Type*} (T : V → V → Prop) (c : V → C) : Prop :=
  ∀ a b z, Cyclic T a b z → c a = c b → c b = c z → False

def IsTournament {V : Type*} (T : V → V → Prop) : Prop :=
  (∀ v, ¬ T v v) ∧ (∀ u v, T u v → ¬ T v u) ∧
    (∀ u v, u ≠ v → T u v ∨ T v u)

def binaryGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (Binary V) where
  Adj f g := f ≠ g ∧ ∀ ⦃u v⦄, G.Adj u v → ∀ b : Bool,
    ¬ (f u = b ∧ g u = b ∧ f v = b ∧ g v = b)
  symm := by
    intro f g h
    refine ⟨Ne.symm h.1, ?_⟩
    intro u v huv b hb
    exact h.2 huv b ⟨hb.2.1, hb.1, hb.2.2.2, hb.2.2.1⟩
  loopless := by intro f h; exact h.1 rfl

end TournamentParts
