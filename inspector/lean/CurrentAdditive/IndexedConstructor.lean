import CurrentAdditive.IndexedBounds
import CurrentAdditive.ZeroFilterNormalized
import CurrentAdditive.DeterministicIndexedMatrix

/-! The functional exact indexed Code D constructor. No physical clock or
intermediate arithmetic bound is asserted here. -/

namespace CurrentAdditive.IndexedLaw

open SequentialCode SequentialSourceCode SequentialAppendMoments
  SequentialFeatureCoverage IndependentSupport LabelTrace

/-- This total executable function uses the actual independent-support loop.
The default cannot occur, as `construct_success` proves. -/
def construct {m : Nat} (D : Nat) (μ : Fin m → ℚ) (q : Nat) :
    Array ((Fin q → Nat) × ℚ) :=
  (sequentialPreprocessed D (indexedAlphabet μ) q).getD #[]

theorem construct_success {m : Nat} (D : Nat) (μ : Fin m → ℚ) (q : Nat) :
    sequentialPreprocessed D (indexedAlphabet μ) q = some (construct D μ q) := by
  obtain ⟨out, hout, _⟩ := sequentialPreprocessed_total D (indexedAlphabet μ) q
  simp [construct, hout]

theorem construct_positive {m : Nat} (D : Nat) (μ : Fin m → ℚ) (q : Nat) :
    SourcePositive (construct D μ q) := by
  obtain ⟨out, hout, hpos⟩ := sequentialPreprocessed_total D (indexedAlphabet μ) q
  simpa [construct, hout] using hpos

theorem construct_mass {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1) (q : Nat) :
    sourceMass (construct D μ q) = 1 := by
  exact sequentialPreprocessed_mass D (indexedAlphabet μ)
    (indexedAlphabet_nonnegative μ hμ) (by simpa using hmass)
    q (construct D μ q) (construct_success D μ q)

theorem construct_size {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) (q : Nat) :
    (construct D μ q).size ≤ (1 + q * m) ^ D := by
  simpa using sequentialPreprocessed_size_polynomial D (indexedAlphabet μ)
    (by simpa using hmass) q (construct D μ q) (construct_success D μ q)

theorem construct_index_bound {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) (q : Nat)
    (j : Fin (construct D μ q).size) (i : Fin q) :
    (construct D μ q)[j].1 i < m := by
  exact sequentialPreprocessed_index_bound D μ hmass q (construct D μ q)
    (construct_success D μ q) _ (Array.getElem_mem j.isLt) i

/-- Each source label is an actual position of the returned array; its word
contains original alphabet indices. -/
def decode {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) (q : Nat)
    (j : Fin (construct D μ q).size) (i : Fin q) : Fin m :=
  ⟨(construct D μ q)[j].1 i, construct_index_bound D μ hmass q j i⟩

@[simp] theorem decode_val {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) (q : Nat)
    (j : Fin (construct D μ q).size) (i : Fin q) :
    (decode D μ hmass q j i).val = (construct D μ q)[j].1 i := rfl

def outputLaw {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1) (q : Nat) :
    Paper2.PositiveRationalLaw (Fin (construct D μ q).size) where
  weight j := (construct D μ q)[j].2
  positive j := by
    have h := (Array.all_eq_true.mp (construct_positive D μ q)) j.val j.isLt
    simpa using h
  total := by
    have hm := construct_mass D μ hμ hmass q
    rw [sourceMass_eq_weightedSum, weightedSum_eq_sum_positions] at hm
    simpa using hm

theorem construct_cylinder {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1)
    (q : Nat) (J : Finset (Fin q)) (a : Fin q → Fin m)
    (hJ : J.card ≤ D) :
    (∑ j : Fin (construct D μ q).size,
      if ∀ i ∈ J, decode D μ hmass q j i = a i
        then (construct D μ q)[j].2 else 0) =
      ∏ i ∈ J, μ (a i) := by
  classical
  have hm := sequentialPreprocessed_pattern_moment D (indexedAlphabet μ)
    (indexedAlphabet_nonnegative μ hμ) (by simpa using hmass)
    q (construct D μ q) (construct_success D μ q)
    (coordinatePattern J a) (by simpa using hJ)
  rw [weightedSum_eq_sum_positions, coordinatePattern_target] at hm
  convert hm using 1
  apply Finset.sum_congr rfl
  intro j _
  have hiff : (∀ i ∈ J, decode D μ hmass q j i = a i) ↔
      PatternMatches (coordinatePattern J a) (construct D μ q)[j.val].1 := by
    rw [coordinatePattern_matches]
    simp only [← Fin.val_inj, decode_val, Fin.getElem_fin]
  simp only [Fin.getElem_fin]
  by_cases hj : ∀ i ∈ J, decode D μ hmass q j i = a i
  · have hp := hiff.mp hj
    simp only [if_pos hj, if_pos hp, mul_one]
  · have hp : ¬ PatternMatches (coordinatePattern J a)
        (construct D μ q)[j.val].1 := fun hp => hj (hiff.mpr hp)
    simp only [if_neg hj, if_neg hp, mul_zero]

theorem mass_one_alphabet_pos {m : Nat} (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) : 0 < m := by
  by_contra h
  have hm : m = 0 := by omega
  subst m
  simp at hmass

noncomputable def inputLaw {m : Nat} (μ : Fin m → ℚ)
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1) :
    Paper2.FiniteLaw (Fin m) where
  weight i := μ i
  nonneg i := by exact_mod_cast hμ i
  total := by exact_mod_cast hmass

theorem construct_isDWise {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1) (q : Nat) :
    CurrentAdditive.IsDWise D (outputLaw D μ hμ hmass q).toFiniteLaw
      (decode D μ hmass q) (inputLaw μ hμ hmass) := by
  classical
  intro J hJ E
  apply Paper2.FiniteLaw.prob_preimage_eq_of_fibres
    (outputLaw D μ hμ hmass q).toFiniteLaw
    (Paper2.FiniteLaw.pi (fun _ : J => inputLaw μ hμ hmass))
    (fun j i => decode D μ hmass q j i)
  intro y
  let a : Fin q → Fin m := fun i =>
    if hi : i ∈ J then y ⟨i, hi⟩ else ⟨0, mass_one_alphabet_pos μ hmass⟩
  have heq (j : Fin (construct D μ q).size) :
      (fun i : J => decode D μ hmass q j i) = y ↔
        ∀ i ∈ J, decode D μ hmass q j i = a i := by
    constructor
    · intro h i hi
      have h' := congrFun h ⟨i, hi⟩
      simpa [a, hi] using h'
    · intro h
      funext i
      simpa [a, i.property] using h i i.property
  have hc := construct_cylinder D μ hμ hmass q J a hJ
  have hcr :
      (∑ j : Fin (construct D μ q).size,
        if ∀ i ∈ J, decode D μ hmass q j i = a i
          then ((construct D μ q)[j].2 : ℝ) else 0) =
        ∏ i ∈ J, (μ (a i) : ℝ) := by
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hc
    push_cast at hcast
    simpa only [apply_ite, Rat.cast_zero] using hcast
  unfold Paper2.FiniteLaw.prob Paper2.FiniteLaw.pi
    Paper2.PositiveRationalLaw.toFiniteLaw outputLaw inputLaw
  calc
    _ = ∑ j : Fin (construct D μ q).size,
        if ∀ i ∈ J, decode D μ hmass q j i = a i
          then ((construct D μ q)[j].2 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : (fun i : J => decode D μ hmass q j i) = y
      · have hp := (heq j).mp hj
        simp only [if_pos hj, if_pos hp]
      · have hp : ¬ ∀ i ∈ J, decode D μ hmass q j i = a i :=
          fun hp => hj ((heq j).mpr hp)
        simp only [if_neg hj, if_neg hp]
    _ = ∏ i ∈ J, (μ (a i) : ℝ) := hcr
    _ = ∏ i : J, (μ (y i) : ℝ) := by
      rw [Finset.prod_subtype (p := fun i => i ∈ J) J
        (fun _ => Iff.rfl) (fun i => (μ (a i) : ℝ))]
      apply Finset.prod_congr rfl
      intro i _
      simp [a, i.property]

/-- A concrete implementation of the finite source interface. Its labels,
weights and decoder all come from the same executable array. -/
def codeSource {m : Nat} (D q : Nat)
    (μ : Paper2.PositiveRationalLaw (Fin m)) :
    DeterministicIndexedMatrix.CodeSource D q (Fin m) μ where
  Label := Fin (construct D μ.weight q).size
  finite := inferInstance
  decEq := inferInstance
  law := outputLaw D μ.weight (fun i => (μ.positive i).le) μ.total q
  decode := decode D μ.weight μ.total q
  exactLaw := construct_isDWise D μ.weight (fun i => (μ.positive i).le) μ.total q

@[simp] theorem codeSource_label {m : Nat} (D q : Nat)
    (μ : Paper2.PositiveRationalLaw (Fin m)) :
    (codeSource D q μ).Label = Fin (construct D μ.weight q).size := rfl

theorem codeSource_card {m : Nat} (D q : Nat)
    (μ : Paper2.PositiveRationalLaw (Fin m)) :
    Fintype.card (codeSource D q μ).Label ≤ (1 + q * m) ^ D := by
  change Fintype.card (Fin (construct D μ.weight q).size) ≤ _
  rw [Fintype.card_fin]
  exact construct_size D μ.weight μ.total q

@[simp] theorem codeSource_weight {m : Nat} (D q : Nat)
    (μ : Paper2.PositiveRationalLaw (Fin m))
    (j : Fin (construct D μ.weight q).size) :
    (codeSource D q μ).law.weight j = (construct D μ.weight q)[j].2 := rfl

@[simp] theorem codeSource_decode_val {m : Nat} (D q : Nat)
    (μ : Paper2.PositiveRationalLaw (Fin m))
    (j : Fin (construct D μ.weight q).size) (i : Fin q) :
    ((codeSource D q μ).decode j i).val = (construct D μ.weight q)[j].1 i := rfl

theorem construct_run {m : Nat} (D : Nat) (μ : Fin m → ℚ) (q : Nat) :
    sequentialIndependent D (positiveLaw (indexedAlphabet μ)) q =
      some (construct D μ q) := construct_success D μ q

theorem construct_independent {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (q : Nat) :
    ColumnIndependent (featureRows
      (generatedFeatures (q + 1) D
        ((positiveLaw (indexedAlphabet μ)).map Prod.fst)).size
      (fun v j => generatedFeatureValue v
        (generatedFeatures (q + 1) D
          ((positiveLaw (indexedAlphabet μ)).map Prod.fst))[j])
      (construct D μ (q + 1))) :=
  sequentialIndependent_columns_independent D (positiveLaw (indexedAlphabet μ))
    q (construct D μ (q + 1)) (construct_success D μ (q + 1))

end CurrentAdditive.IndexedLaw
