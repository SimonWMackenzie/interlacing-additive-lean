import CurrentAdditive.SequentialFeatureCoverage
import CurrentAdditive.IndependentStreams

/-!
The retained source array is the actual finite carrier. Its positions remain
distinct even when their decoded words coincide. This file turns exact
rational cylinder moments into Paper2's finite-law interface.
-/

namespace CurrentAdditive.SequentialFiniteLaw

open SequentialCode SequentialSourceCode SequentialAppendMoments
  SequentialFeatureCoverage Paper2

theorem weightedSum_eq_sum_fin {α : Type*}
    (source : Array (α × ℚ)) (f : α → ℚ) :
    weightedSum source f =
      ∑ i : Fin source.size, source[i].2 * f source[i].1 := by
  calc
    weightedSum source f =
        ∑ i : Fin source.toList.length,
          source.toList[i].2 * f source.toList[i].1 := by
            exact (Fin.sum_univ_fun_getElem source.toList
              (fun x => x.2 * f x.1)).symm
    _ = ∑ i : Fin source.size, source[i].2 * f source[i].1 := by
      simp [Array.getElem_toList]

theorem sourceMass_eq_sum_fin {α : Type*}
    (source : Array (α × ℚ)) :
    sourceMass source = ∑ i : Fin source.size, source[i].2 := by
  rw [sourceMass_eq_weightedSum, weightedSum_eq_sum_fin]
  simp

/-- The literal array positions form a positive rational law when its
checked weights are positive and normalized. -/
def indexedLaw {α : Type*} (source : Array (α × ℚ))
    (hpositive : SourcePositive source) (hmass : sourceMass source = 1) :
    PositiveRationalLaw (Fin source.size) where
  weight i := source[i].2
  positive i := by
    have hi := (Array.all_eq_true.mp hpositive) i.val i.isLt
    simpa [SourcePositive] using hi
  total := by
    simpa [sourceMass_eq_sum_fin] using hmass

theorem indexedLaw_prob {α : Type*}
    (source : Array (α × ℚ))
    (hpositive : SourcePositive source) (hmass : sourceMass source = 1)
    (E : α → Prop) [DecidablePred E] :
    (indexedLaw source hpositive hmass).toFiniteLaw.prob
        (fun i => E source[i].1) =
      (weightedSum source (fun x => if E x then 1 else 0) : ℝ) := by
  classical
  have hrat : weightedSum source (fun x => if E x then 1 else 0) =
      ∑ i : Fin source.size,
        if E source[i].1 then source[i].2 else 0 := by
    rw [weightedSum_eq_sum_fin]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [hrat]
  simp [Paper2.FiniteLaw.prob, indexedLaw,
    PositiveRationalLaw.toFiniteLaw]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

def subsetPattern {Y : Type*} {q : Nat}
    (s : Finset (Fin q)) (y : s → Y) (i : Fin q) : Option Y :=
  if h : i ∈ s then some (y ⟨i, h⟩) else none

theorem subsetPattern_size {Y : Type*} {q : Nat}
    (s : Finset (Fin q)) (y : s → Y) :
    patternSize (subsetPattern s y) = s.card := by
  classical
  simp [patternSize, subsetPattern]

theorem subsetPattern_matches {Y : Type*} {q : Nat}
    (s : Finset (Fin q)) (y : s → Y) (v : Fin q → Y) :
    PatternMatches (subsetPattern s y) v ↔
      ∀ i : s, v i.val = y i := by
  classical
  constructor
  · intro h i
    have hi := h i.val
    simp [subsetPattern, i.property] at hi
    exact hi.symm
  · intro h i
    by_cases hi : i ∈ s
    · right
      simpa [subsetPattern, hi] using (h ⟨i, hi⟩).symm
    · left
      simp [subsetPattern, hi]

theorem subsetPattern_target {Y : Type*} [DecidableEq Y] {q : Nat}
    (alphabet : Array (Y × ℚ))
    (s : Finset (Fin q)) (y : s → Y) :
    patternTarget alphabet (subsetPattern s y) =
      ∏ i : s, alphabetPointMass alphabet (y i) := by
  classical
  unfold patternTarget subsetPattern
  have hprod :
      (∏ i : Fin q,
        match (if h : i ∈ s then some (y ⟨i, h⟩) else none) with
        | none => (1 : ℚ)
        | some z => alphabetPointMass alphabet z) =
      (∏ i : Fin q,
        if h : i ∈ s then alphabetPointMass alphabet (y ⟨i, h⟩)
        else 1) := by
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> rfl
  refine hprod.trans ?_
  change (∏ i : Fin q,
    if h : i ∈ s then alphabetPointMass alphabet (y ⟨i, h⟩)
    else 1) = _
  let f : Fin q → ℚ := fun i =>
    if h : i ∈ s then alphabetPointMass alphabet (y ⟨i, h⟩) else 1
  have hrestrict : (∏ i ∈ s, f i) = ∏ i : Fin q, f i := by
    apply Finset.prod_subset_one_on_sdiff (Finset.subset_univ s)
    · intro i hi
      have hinot : i ∉ s := (Finset.mem_sdiff.mp hi).2
      simp [f, hinot]
    · intro i hi
      rfl
  rw [← hrestrict]
  change (∏ i ∈ s, f i) = _
  rw [Finset.prod_subtype s (fun _ => Iff.rfl) f]
  apply Finset.prod_congr rfl
  intro i hi
  simp [f, i.property]

theorem sequential_output_positive {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : SourcePositive alphabet)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialMaterialized D alphabet q = some out) :
    SourcePositive out := by
  obtain ⟨other, hother, hpositive⟩ :=
    sequentialMaterialized_total D alphabet halphabet q
  rw [hout] at hother
  cases hother
  exact hpositive

theorem sequential_indexed_fibre {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1)
    (hcover : ∀ y : Y, y ∈ (alphabet.map Prod.fst).toList)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialMaterialized D alphabet q = some out)
    (hpositive : SourcePositive out)
    (hmass : sourceMass out = 1)
    (s : Finset (Fin q)) (hs : s.card ≤ D) (y : s → Y) :
    (indexedLaw out hpositive hmass).toFiniteLaw.prob
        (fun j => ∀ i : s, out[j].1 i.val = y i) =
      ∏ i : s, (alphabetPointMass alphabet (y i) : ℝ) := by
  classical
  let p := subsetPattern s y
  have hvalues : ∀ i z, p i = some z →
      z ∈ (alphabet.map Prod.fst).toList := by
    intro i z hz
    by_cases hi : i ∈ s
    · have heq : y ⟨i, hi⟩ = z := by
        simpa [p, subsetPattern, hi] using hz
      subst z
      exact hcover _
    · simp [p, subsetPattern, hi] at hz
  have hsize : patternSize p ≤ D := by
    simpa [p, subsetPattern_size] using hs
  have hrat := sequentialMaterialized_pattern_moment D alphabet
    halphabet q out hout p hvalues hsize
  have hevent : (fun v : Fin q → Y =>
      if (∀ i : s, v i.val = y i) then (1 : ℚ) else 0) =
      (fun v => if PatternMatches p v then 1 else 0) := by
    funext v
    by_cases h : ∀ i : s, v i.val = y i
    · have hp : PatternMatches p v :=
        (subsetPattern_matches s y v).mpr h
      simp only [if_pos h, if_pos hp]
    · have hp : ¬PatternMatches p v := by
        intro hp
        exact h ((subsetPattern_matches s y v).mp hp)
      simp only [if_neg h, if_neg hp]
  have htarget : patternTarget alphabet p =
      ∏ i : s, alphabetPointMass alphabet (y i) :=
    subsetPattern_target alphabet s y
  calc
    (indexedLaw out hpositive hmass).toFiniteLaw.prob
        (fun j => ∀ i : s, out[j].1 i.val = y i) =
      (weightedSum out (fun v =>
        if (∀ i : s, v i.val = y i) then 1 else 0) : ℝ) :=
          indexedLaw_prob out hpositive hmass
            (fun v => ∀ i : s, v i.val = y i)
    _ = ∏ i : s, (alphabetPointMass alphabet (y i) : ℝ) := by
      rw [hevent]
      rw [htarget] at hrat
      exact_mod_cast hrat

/-- The actual indexed output law has every bounded-coordinate marginal of
the specified positive rational alphabet law. Duplicate decoded words are
still separate outcomes of `Fin out.size`. -/
theorem sequential_indexed_dwise {Y : Type*}
    [Fintype Y] [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1)
    (hcover : ∀ y : Y, y ∈ (alphabet.map Prod.fst).toList)
    (μ : PositiveRationalLaw Y)
    (hpoint : ∀ y, alphabetPointMass alphabet y = μ.weight y)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialMaterialized D alphabet q = some out)
    (hpositive : SourcePositive out)
    (hmass : sourceMass out = 1) :
    IsDWise D (indexedLaw out hpositive hmass).toFiniteLaw
      (fun j => out[j].1) μ.toFiniteLaw := by
  classical
  intro s hs E
  apply Paper2.FiniteLaw.prob_preimage_eq_of_fibres
    (indexedLaw out hpositive hmass).toFiniteLaw
    (Paper2.FiniteLaw.pi (fun _ : s => μ.toFiniteLaw))
    (fun j i => out[j].1 i.val)
  intro y
  have hfibre := sequential_indexed_fibre D alphabet halphabet hcover
    q out hout hpositive hmass s hs y
  have hevent :
      (fun j : Fin out.size =>
        (fun i : s => out[j].1 i.val) = y) =
      (fun j : Fin out.size => ∀ i : s, out[j].1 i.val = y i) := by
    funext j
    apply propext
    simp [funext_iff]
  rw [hevent, hfibre]
  calc
    (∏ i : s, (alphabetPointMass alphabet (y i) : ℝ)) =
        ∏ i : s, (μ.weight (y i) : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hpoint]
    _ = (Paper2.FiniteLaw.pi (fun _ : s => μ.toFiniteLaw)).weight y := rfl

/-- Executable indexed source with a literal feature-array support bound and
exact `D`-wise marginals. The alphabet array is the algorithm's rational
input table; its point masses are required to match `μ`. -/
theorem exists_sequential_indexed_dwise_source {Y : Type*}
    [Fintype Y] [DecidableEq Y]
    (D q : Nat) (alphabet : Array (Y × ℚ))
    (hpositive : SourcePositive alphabet)
    (halphabet : sourceMass alphabet = 1)
    (hcover : ∀ y : Y, y ∈ (alphabet.map Prod.fst).toList)
    (μ : PositiveRationalLaw Y)
    (hpoint : ∀ y, alphabetPointMass alphabet y = μ.weight y) :
    ∃ (out : Array ((Fin q → Y) × ℚ))
      (houtpositive : SourcePositive out)
      (houtmass : sourceMass out = 1),
      sequentialMaterialized D alphabet q = some out ∧
      out.size ≤ (generatedFeatures q D (alphabet.map Prod.fst)).size ∧
      IsDWise D (indexedLaw out houtpositive houtmass).toFiniteLaw
        (fun j => out[j].1) μ.toFiniteLaw := by
  obtain ⟨out, hout, houtpositive, hbound⟩ :=
    sequentialMaterialized_exists_bounded D alphabet hpositive q
  have houtmass : sourceMass out = 1 :=
    sequentialMaterialized_mass D alphabet halphabet q out hout
  refine ⟨out, houtpositive, houtmass, hout, hbound, ?_⟩
  exact sequential_indexed_dwise D alphabet halphabet hcover μ hpoint
    q out hout houtpositive houtmass

#print axioms indexedLaw
#print axioms indexedLaw_prob
#print axioms sequential_indexed_fibre
#print axioms sequential_indexed_dwise
#print axioms exists_sequential_indexed_dwise_source

end CurrentAdditive.SequentialFiniteLaw
