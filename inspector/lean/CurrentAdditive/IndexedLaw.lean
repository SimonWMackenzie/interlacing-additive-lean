import CurrentAdditive.SequentialFeatureCoverage

/-! Original-position alphabet laws for the literal Code D constructor.
The Nat label `i.val` is the original alphabet position, even when several
positions decode to the same application-level value. -/

namespace CurrentAdditive.IndexedLaw

open SequentialCode SequentialAppendMoments SequentialFeatureCoverage

def indexedAlphabet {m : Nat} (μ : Fin m → ℚ) : Array (Nat × ℚ) :=
  Array.ofFn (fun i => (i.val, μ i))

@[simp] theorem indexedAlphabet_size {m : Nat} (μ : Fin m → ℚ) :
    (indexedAlphabet μ).size = m := by simp [indexedAlphabet]

@[simp] theorem indexedAlphabet_get {m : Nat} (μ : Fin m → ℚ) (i : Fin m) :
    (indexedAlphabet μ)[i.val] = (i.val, μ i) := by simp [indexedAlphabet]

theorem indexedAlphabet_nonnegative {m : Nat} (μ : Fin m → ℚ)
    (hμ : ∀ i, 0 ≤ μ i) :
    (indexedAlphabet μ).all (fun e => decide (0 ≤ e.2)) = true := by
  apply Array.all_eq_true.mpr
  intro i hi
  simpa [indexedAlphabet] using hμ ⟨i, by simpa using hi⟩

@[simp] theorem indexedAlphabet_mass {m : Nat} (μ : Fin m → ℚ) :
    sourceMass (indexedAlphabet μ) = ∑ i, μ i := by
  simp [sourceMass, indexedAlphabet, List.map_ofFn, List.sum_ofFn]

@[simp] theorem indexedAlphabet_pointMass {m : Nat} (μ : Fin m → ℚ)
    (i : Fin m) :
    alphabetPointMass (indexedAlphabet μ) i.val = μ i := by
  simp [alphabetPointMass, weightedSum, indexedAlphabet,
    List.map_ofFn, List.sum_ofFn, Fin.val_inj]

theorem indexedAlphabet_label_bound {m : Nat} (μ : Fin m → ℚ)
    (e : Nat × ℚ) (he : e ∈ indexedAlphabet μ) : e.1 < m := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp he
  have hlabel : i = e.1 := by
    simpa [indexedAlphabet] using congrArg Prod.fst hget
  simpa [hlabel] using hi

def coordinatePattern {m q : Nat} (J : Finset (Fin q))
    (a : Fin q → Fin m) : Fin q → Option Nat :=
  fun i => if i ∈ J then some (a i).val else none

@[simp] theorem coordinatePattern_size {m q : Nat}
    (J : Finset (Fin q)) (a : Fin q → Fin m) :
    patternSize (coordinatePattern J a) = J.card := by
  classical
  simp [patternSize, coordinatePattern]

theorem coordinatePattern_matches {m q : Nat}
    (J : Finset (Fin q)) (a : Fin q → Fin m) (v : Fin q → Nat) :
    PatternMatches (coordinatePattern J a) v ↔
      ∀ i ∈ J, v i = (a i).val := by
  classical
  constructor
  · intro h i hi
    simpa [coordinatePattern, hi, eq_comm] using h i
  · intro h i
    by_cases hi : i ∈ J
    · simpa [coordinatePattern, hi, h i hi]
    · simp [coordinatePattern, hi]

theorem coordinatePattern_target {m q : Nat} (μ : Fin m → ℚ)
    (J : Finset (Fin q)) (a : Fin q → Fin m) :
    patternTarget (indexedAlphabet μ) (coordinatePattern J a) =
      ∏ i ∈ J, μ (a i) := by
  classical
  calc
    _ = ∏ i : Fin q, if i ∈ J then μ (a i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ J <;> simp [patternTarget, coordinatePattern, hi]
    _ = ∏ i ∈ J, μ (a i) := by simp

/-- Sum over actual output array positions. Equal words at different array
positions continue to contribute separately. -/
theorem weightedSum_eq_sum_positions {α : Type*} (out : Array (α × ℚ))
    (f : α → ℚ) :
    weightedSum out f = ∑ j : Fin out.size, out[j].2 * f out[j].1 := by
  have hsum : weightedSum (Array.ofFn (fun j : Fin out.size => out[j.val])) f =
      ∑ j : Fin out.size, out[j].2 * f out[j].1 := by
    simp only [weightedSum, Array.toList_ofFn, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply, Fin.getElem_fin]
  have heq : (Array.ofFn (fun j : Fin out.size => out[j.val])) = out :=
    Array.ofFn_getElem
  rw [heq] at hsum
  exact hsum

end CurrentAdditive.IndexedLaw
