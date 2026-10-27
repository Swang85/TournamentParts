import TournamentParts.Core

/-!
# Binary function graphs

The paper encodes the signs -1 and +1 by `false` and `true`.
A triangle of binary functions gives six independent common-sign classes.
The explicit coloring below avoids any choice of a covering class.
-/

namespace TournamentParts

variable {V : Type*}

/-- Coordinatewise sign reversal. -/
def binaryComplement (f : Binary V) : Binary V := fun v => !(f v)

@[simp] theorem binaryComplement_involutive (f : Binary V) :
    binaryComplement (binaryComplement f) = f := by
  funext v
  simp [binaryComplement]

/-- Every binary function is adjacent to its complement, on a nonempty base. -/
theorem binary_adj_complement [Nonempty V] (G : SimpleGraph V) (f : Binary V) :
    (binaryGraph G).Adj f (binaryComplement f) := by
  constructor
  · intro h
    let v : V := Classical.choice inferInstance
    have hv := congrFun h v
    cases hf : f v <;> simp [binaryComplement, hf] at hv
  · intro u v huv b h
    rcases h with ⟨hfu, hgu, hfv, hgv⟩
    cases b <;> simp_all [binaryComplement]

/-- Simultaneously reversing both signs preserves adjacency. -/
theorem binary_adj_complement_both (G : SimpleGraph V) {f g : Binary V}
    (h : (binaryGraph G).Adj f g) :
    (binaryGraph G).Adj (binaryComplement f) (binaryComplement g) := by
  constructor
  · intro heq
    apply h.1
    have := congrArg binaryComplement heq
    simpa using this
  · intro u v huv b hb
    apply h.2 huv (!b)
    rcases hb with ⟨hfu, hgu, hfv, hgv⟩
    cases b <;> simp_all [binaryComplement]

/-- Choose the first agreeing pair of functions and its shared sign. -/
def sixColor (f g h : Binary V) (v : V) : Fin 6 :=
  if f v = g v then (if f v then 1 else 0)
  else if f v = h v then (if f v then 3 else 2)
  else (if g v then 5 else 4)

/-- A triangle in the binary graph supplies a proper six-coloring of the base. -/
theorem sixColor_proper (G : SimpleGraph V) (f g h : Binary V)
    (hfg : (binaryGraph G).Adj f g)
    (hgh : (binaryGraph G).Adj g h)
    (hhf : (binaryGraph G).Adj h f) :
    GProper G (sixColor f g h) := by
  intro u v huv hc
  have hfg0 := hfg.2 huv false
  have hfg1 := hfg.2 huv true
  have hgh0 := hgh.2 huv false
  have hgh1 := hgh.2 huv true
  have hhf0 := hhf.2 huv false
  have hhf1 := hhf.2 huv true
  cases hfu : f u <;> cases hgu : g u <;> cases hhu : h u <;>
    cases hfv : f v <;> cases hgv : g v <;> cases hhv : h v <;>
    simp_all [sixColor]

/-- Lemma 2.3: if the base has no six-coloring, its binary graph is triangle-free. -/
theorem binary_triangleFree (G : SimpleGraph V)
    (hG : ¬ ∃ c : V → Fin 6, GProper G c) :
    TriangleFree (binaryGraph G) := by
  intro f g h hfg hgh hhf
  exact hG ⟨sixColor f g h, sixColor_proper G f g h hfg hgh hhf⟩

end TournamentParts
