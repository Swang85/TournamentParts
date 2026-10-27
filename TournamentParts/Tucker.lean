import TournamentParts.Binary
import Mathlib.Data.Finset.Max

/-!
The paper's combinatorial chromatic bound. `OctahedralTucker` is an explicit
background theorem, not an axiom declared by this project. Binary signs are
encoded by Bool; partial signs by Option Bool, with none representing zero.
-/
namespace TournamentParts

abbrev PartialBinary (N : ℕ) := Fin N → Option Bool

def flipPartial {N : ℕ} (s : PartialBinary N) : PartialBinary N :=
  fun i => (s i).map Bool.not

def flipBinary {V : Type*} (f : Binary V) : Binary V := fun i => !(f i)

@[simp] theorem flipBinary_flipBinary {V : Type*} (f : Binary V) :
    flipBinary (flipBinary f) = f := by
  funext i
  simp [flipBinary]

@[simp] theorem flipPartial_flipPartial {N : ℕ} (s : PartialBinary N) :
    flipPartial (flipPartial s) = s := by
  funext i
  cases h : s i with
  | none => simp [flipPartial, h]
  | some b => simp [flipPartial, h]

noncomputable def signSupport {N : ℕ} (s : PartialBinary N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => s i ≠ none)

noncomputable def signZeros {N : ℕ} (s : PartialBinary N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => s i = none)

@[simp] theorem mem_signSupport {N : ℕ} (s : PartialBinary N) (i : Fin N) :
    i ∈ signSupport s ↔ s i ≠ none := by classical simp [signSupport]

@[simp] theorem mem_signZeros {N : ℕ} (s : PartialBinary N) (i : Fin N) :
    i ∈ signZeros s ↔ s i = none := by classical simp [signZeros]

@[simp] theorem support_flip {N : ℕ} (s : PartialBinary N) :
    signSupport (flipPartial s) = signSupport s := by
  classical
  ext i
  simp only [mem_signSupport]
  cases h : s i <;> simp [flipPartial, h]

@[simp] theorem zeros_flip {N : ℕ} (s : PartialBinary N) :
    signZeros (flipPartial s) = signZeros s := by
  classical
  ext i
  simp only [mem_signZeros]
  cases h : s i <;> simp [flipPartial, h]

theorem support_add_zeros {N : ℕ} (s : PartialBinary N) :
    (signSupport s).card + (signZeros s).card = N := by
  classical
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin N))) (p := fun i => s i ≠ none)
  simpa [signSupport, signZeros] using h

def SignExtends {N : ℕ} (s t : PartialBinary N) : Prop :=
  ∀ i b, s i = some b → t i = some b

theorem SignExtends.refl {N : ℕ} (s : PartialBinary N) : SignExtends s s :=
  fun _ _ h => h

theorem support_subset_of_extends {N : ℕ} {s t : PartialBinary N}
    (h : SignExtends s t) : signSupport s ⊆ signSupport t := by
  intro i hi
  simp only [mem_signSupport] at hi ⊢
  cases hs : s i with
  | none => exact False.elim (hi hs)
  | some b => rw [h i b hs]; simp

theorem eq_of_extends_card {N : ℕ} {s t : PartialBinary N}
    (h : SignExtends s t) (hc : (signSupport s).card = (signSupport t).card) :
    s = t := by
  have heq := Finset.eq_of_subset_of_card_le (support_subset_of_extends h) (le_of_eq hc.symm)
  funext i
  cases hs : s i with
  | some b => exact (h i b hs).symm
  | none =>
    have hi : i ∉ signSupport s := by simp [hs]
    rw [heq] at hi
    have ht : t i = none := by simpa only [mem_signSupport, not_not] using hi
    exact ht.symm

noncomputable def firstSign {N : ℕ} (s : PartialBinary N) : Bool :=
  if h : (signSupport s).Nonempty then
    (s ((signSupport s).min' h)).getD false
  else false

theorem firstSign_flip {N : ℕ} (s : PartialBinary N)
    (hs : (signSupport s).Nonempty) :
    firstSign (flipPartial s) = !(firstSign s) := by
  classical
  have hn : s ((signSupport s).min' hs) ≠ none :=
    (mem_signSupport _ _).mp (Finset.min'_mem _ _)
  simp only [firstSign, support_flip, dif_pos hs, flipPartial]
  cases h : s ((signSupport s).min' hs) with
  | none => exact False.elim (hn h)
  | some b => simp

noncomputable def canonicalSign {N : ℕ} (s : PartialBinary N) : PartialBinary N :=
  if firstSign s then s else flipPartial s

theorem canonicalSign_flip {N : ℕ} (s : PartialBinary N)
    (hs : (signSupport s).Nonempty) :
    canonicalSign (flipPartial s) = canonicalSign s := by
  simp only [canonicalSign, firstSign_flip s hs, flipPartial_flipPartial]
  cases firstSign s <;> rfl

@[simp] theorem support_canonical {N : ℕ} (s : PartialBinary N) :
    signSupport (canonicalSign s) = signSupport s := by
  simp only [canonicalSign]
  cases firstSign s <;> simp

/-- Every induced subgraph on fewer than g vertices has a proper two-coloring. -/
def SmallBipartite {N : ℕ} (G : SimpleGraph (Fin N)) (g : ℕ) : Prop :=
  ∀ Z : Finset (Fin N), Z.card < g →
    ∃ f : Binary (Fin N), ∀ ⦃u v⦄, u ∈ Z → v ∈ Z → G.Adj u v → f u ≠ f v

/-- A binary completion retaining nonzero signs and properly coloring zeros. -/
def GoodCompletion {N : ℕ} (G : SimpleGraph (Fin N))
    (s : PartialBinary N) (f : Binary (Fin N)) : Prop :=
  (∀ i b, s i = some b → f i = b) ∧
  (∀ ⦃u v⦄, s u = none → s v = none → G.Adj u v → f u ≠ f v)

theorem exists_goodCompletion {N g : ℕ} {G : SimpleGraph (Fin N)}
    (hG : SmallBipartite G g) (s : PartialBinary N)
    (h : (signZeros s).card < g) : ∃ f, GoodCompletion G s f := by
  classical
  obtain ⟨f, hf⟩ := hG (signZeros s) h
  refine ⟨fun i => (s i).getD (f i), ?_, ?_⟩
  · intro i b hi
    simp [hi]
  · intro u v hu hv huv
    simpa [hu, hv] using hf ((mem_signZeros _ _).mpr hu)
      ((mem_signZeros _ _).mpr hv) huv

theorem GoodCompletion.flip {N : ℕ} {G : SimpleGraph (Fin N)}
    {s : PartialBinary N} {f : Binary (Fin N)} (h : GoodCompletion G s f) :
    GoodCompletion G (flipPartial s) (flipBinary f) := by
  constructor
  · intro i b hi
    cases hs : s i with
    | none => simp [flipPartial, hs] at hi
    | some a =>
      have ha : (!a) = b := by simpa [flipPartial, hs] using hi
      simp [flipBinary, h.1 i a hs, ha]
  · intro u v hu hv huv heq
    have hsu : s u = none := by
      cases hsu : s u <;> simp_all [flipPartial]
    have hsv : s v = none := by
      cases hsv : s v <;> simp_all [flipPartial]
    have hne := h.2 hsu hsv huv
    exact hne (by simpa [flipBinary] using congrArg Bool.not heq)

noncomputable def chosenCompletion {N : ℕ} (G : SimpleGraph (Fin N))
    (s : PartialBinary N) : Binary (Fin N) := by
  classical
  exact if h : ∃ f, GoodCompletion G s f then Classical.choose h else fun _ => false

theorem chosenCompletion_good {N : ℕ} (G : SimpleGraph (Fin N))
    (s : PartialBinary N) (h : ∃ f, GoodCompletion G s f) :
    GoodCompletion G s (chosenCompletion G s) := by
  simp only [chosenCompletion, dif_pos h]
  exact Classical.choose_spec h

noncomputable def completion {N : ℕ} (G : SimpleGraph (Fin N))
    (s : PartialBinary N) : Binary (Fin N) :=
  if firstSign s then chosenCompletion G (canonicalSign s)
  else flipBinary (chosenCompletion G (canonicalSign s))

theorem completion_flip {N : ℕ} (G : SimpleGraph (Fin N))
    (s : PartialBinary N) (hs : (signSupport s).Nonempty) :
    completion G (flipPartial s) = flipBinary (completion G s) := by
  simp only [completion, firstSign_flip s hs, canonicalSign_flip s hs]
  cases firstSign s <;> simp

theorem completion_good {N g : ℕ} {G : SimpleGraph (Fin N)}
    (hG : SmallBipartite G g) (s : PartialBinary N)
    (h : (signZeros s).card < g) : GoodCompletion G s (completion G s) := by
  classical
  have hc : (signZeros (canonicalSign s)).card < g := by
    simp only [canonicalSign]
    cases firstSign s <;> simpa using h
  have hg := chosenCompletion_good G (canonicalSign s)
    (exists_goodCompletion hG (canonicalSign s) hc)
  unfold completion
  cases hs : firstSign s
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have hcan : canonicalSign s = flipPartial s := by simp [canonicalSign, hs]
    rw [hcan] at hg ⊢
    have hh := hg.flip
    simpa using hh
  · simp only [hs, ↓reduceIte]
    have hcan : canonicalSign s = s := by simp [canonicalSign, hs]
    simpa [hcan] using hg

/-- Comparable nonzero partial signs give adjacent opposite completions. -/
theorem completions_adjacent {N : ℕ} {G : SimpleGraph (Fin N)}
    {s t : PartialBinary N} {f h : Binary (Fin N)}
    (hs : (signSupport s).Nonempty) (hst : SignExtends s t)
    (hf : GoodCompletion G s f) (hh : GoodCompletion G t h) :
    (binaryGraph G).Adj f (flipBinary h) := by
  constructor
  · obtain ⟨i, hi⟩ := hs
    have hn := (mem_signSupport s i).mp hi
    cases hsi : s i with
    | none => exact False.elim (hn hsi)
    | some b =>
      intro heq
      have heqi := congrFun heq i
      have hfi := hf.1 i b hsi
      have hhi := hh.1 i b (hst i b hsi)
      have hnot : b = !b := by simpa [flipBinary, hfi, hhi] using heqi
      cases b <;> simp at hnot
  · intro u v huv b hvals
    have hz : ∀ i, f i = b → flipBinary h i = b → s i = none := by
      intro i hfi hhi
      cases hsi : s i with
      | none => rfl
      | some a =>
        have hfa := hf.1 i a hsi
        have hha := hh.1 i a (hst i a hsi)
        cases a <;> cases b <;> simp_all [flipBinary]
    exact hf.2 (hz u hvals.1 hvals.2.1) (hz v hvals.2.2.1 hvals.2.2.2)
      huv (hvals.1.trans hvals.2.2.1.symm)

/-- Octahedral Tucker's lemma, with signed integer labels.
The open bounds -N < label < N mean labels ±1,...,±(N-1).
The all-zero sign vector is excluded from the range and conclusion. -/
def OctahedralTucker : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ label : PartialBinary N → ℤ,
    (∀ s, label (flipPartial s) = -label s) →
    (∀ s, (signSupport s).Nonempty →
      label s ≠ 0 ∧ -(N : ℤ) < label s ∧ label s < (N : ℤ)) →
    ∃ s t, (signSupport s).Nonempty ∧ (signSupport t).Nonempty ∧
      SignExtends s t ∧ label s = -label t



/-- The large-support label uses the smaller of two distinct colors. -/
def largeLabel (q a b : ℕ) : ℤ :=
  if a < b then (q + a + 1 : ℕ) else -(q + b + 1 : ℕ)

theorem largeLabel_swap (q a b : ℕ) (h : a ≠ b) :
    largeLabel q b a = -largeLabel q a b := by
  unfold largeLabel
  split_ifs <;> omega

noncomputable def tuckerLabel {N k : ℕ} (G : SimpleGraph (Fin N))
    (c : Binary (Fin N) → Fin k) (q : ℕ) (s : PartialBinary N) : ℤ :=
  if (signSupport s).card ≤ q then
    if firstSign s then ((signSupport s).card : ℤ) else -((signSupport s).card : ℤ)
  else largeLabel q (c (completion G s)).val (c (flipBinary (completion G s))).val

theorem good_of_large {N g : ℕ} {G : SimpleGraph (Fin N)}
    (hG : SmallBipartite G g) (s : PartialBinary N)
    (hs : ¬ (signSupport s).card ≤ N - g) :
    GoodCompletion G s (completion G s) := by
  apply completion_good hG
  have hc := support_add_zeros s
  omega

theorem completion_colors_ne {N g k : ℕ} {G : SimpleGraph (Fin N)}
    (hG : SmallBipartite G g) {c : Binary (Fin N) → Fin k}
    (hc : GProper (binaryGraph G) c) (s : PartialBinary N)
    (hs : ¬ (signSupport s).card ≤ N - g) :
    (c (completion G s)).val ≠ (c (flipBinary (completion G s))).val := by
  have hn : (signSupport s).Nonempty := Finset.card_pos.mp (by omega)
  have hgood := good_of_large hG s hs
  have hadj := completions_adjacent hn (SignExtends.refl s) hgood hgood
  intro h
  exact hc hadj (Fin.ext h)

theorem tuckerLabel_flip {N g k : ℕ} {G : SimpleGraph (Fin N)}
    (hG : SmallBipartite G g) {c : Binary (Fin N) → Fin k}
    (hc : GProper (binaryGraph G) c) (s : PartialBinary N) :
    tuckerLabel G c (N - g) (flipPartial s) = -tuckerLabel G c (N - g) s := by
  classical
  by_cases hz : (signSupport s).card = 0
  · simp [tuckerLabel, hz]
  have hn : (signSupport s).Nonempty := Finset.card_pos.mp (by omega)
  simp only [tuckerLabel, support_flip]
  by_cases hs : (signSupport s).card ≤ N - g
  · simp only [if_pos hs, firstSign_flip s hn]
    cases firstSign s <;> simp
  · simp only [if_neg hs, completion_flip G s hn, flipBinary_flipBinary]
    exact largeLabel_swap _ _ _ (completion_colors_ne hG hc s hs)

theorem tuckerLabel_range {N g k : ℕ} {G : SimpleGraph (Fin N)}
    (hG : SmallBipartite G g) (hg : 2 ≤ g) (hgN : g ≤ N) (hk : k ≤ g)
    {c : Binary (Fin N) → Fin k} (hc : GProper (binaryGraph G) c)
    (s : PartialBinary N) (hs : (signSupport s).Nonempty) :
    tuckerLabel G c (N - g) s ≠ 0 ∧
      -(N : ℤ) < tuckerLabel G c (N - g) s ∧
      tuckerLabel G c (N - g) s < (N : ℤ) := by
  have hpos : 0 < (signSupport s).card := Finset.card_pos.mpr hs
  unfold tuckerLabel
  by_cases hsmall : (signSupport s).card ≤ N - g
  · simp only [if_pos hsmall]
    have hne : signSupport s ≠ ∅ := hs.ne_empty
    cases firstSign s <;> simp [hne] <;> omega
  · simp only [if_neg hsmall]
    have hne := completion_colors_ne hG hc s hsmall
    have ha := (c (completion G s)).isLt
    have hb := (c (flipBinary (completion G s))).isLt
    unfold largeLabel
    split_ifs <;> omega

/-- The paper's technical chromatic bound, in coloring form.
For a finite base graph, small induced subgraphs being bipartite forces every
proper coloring of its binary function graph to use more than g colors.
The only topological/combinatorial background input is Octahedral Tucker.
-/
theorem binary_not_colorable_of_smallBipartite
    (tucker : OctahedralTucker) {N g k : ℕ} {G : SimpleGraph (Fin N)}
    (hG : SmallBipartite G g) (hg : 2 ≤ g) (hgN : g ≤ N) (hk : k ≤ g)
    (c : Binary (Fin N) → Fin k) : ¬ GProper (binaryGraph G) c := by
  intro hc
  obtain ⟨s, t, hs, ht, hst, heq⟩ := tucker N (by omega)
    (tuckerLabel G c (N - g)) (tuckerLabel_flip hG hc)
    (tuckerLabel_range hG hg hgN hk hc)
  have hspos : 0 < (signSupport s).card := Finset.card_pos.mpr hs
  have htpos : 0 < (signSupport t).card := Finset.card_pos.mpr ht
  by_cases hsmall_s : (signSupport s).card ≤ N - g
  · by_cases hsmall_t : (signSupport t).card ≤ N - g
    · have hcard : (signSupport s).card = (signSupport t).card := by
        simp only [tuckerLabel, if_pos hsmall_s, if_pos hsmall_t] at heq
        cases firstSign s <;> cases firstSign t <;> simp_all <;> omega
      have hequal := eq_of_extends_card hst hcard
      subst t
      have hnonzero := (tuckerLabel_range hG hg hgN hk hc s hs).1
      omega
    · simp only [tuckerLabel, if_pos hsmall_s, if_neg hsmall_t, largeLabel] at heq
      split_ifs at heq <;> omega
  · by_cases hsmall_t : (signSupport t).card ≤ N - g
    · simp only [tuckerLabel, if_neg hsmall_s, if_pos hsmall_t, largeLabel] at heq
      split_ifs at heq <;> omega
    · have hgood_s := good_of_large hG s hsmall_s
      have hgood_t := good_of_large hG t hsmall_t
      have hadj := completions_adjacent hs hst hgood_s hgood_t
      have hcross₁ : (c (completion G s)).val ≠
          (c (flipBinary (completion G t))).val := by
        intro h
        exact hc hadj (Fin.ext h)
      have hadj₂ : (binaryGraph G).Adj (flipBinary (completion G s)) (completion G t) := by
        have hflip := binary_adj_complement_both G hadj
        change (binaryGraph G).Adj (flipBinary (completion G s))
          (flipBinary (flipBinary (completion G t))) at hflip
        simpa only [flipBinary_flipBinary] using hflip
      have hcross₂ : (c (flipBinary (completion G s))).val ≠
          (c (completion G t)).val := by
        intro h
        exact hc hadj₂ (Fin.ext h)
      simp only [tuckerLabel, if_neg hsmall_s, if_neg hsmall_t, largeLabel] at heq
      split_ifs at heq <;> omega

end TournamentParts






