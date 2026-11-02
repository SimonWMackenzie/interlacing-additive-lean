import CurrentAdditive.IndexedBaseLookup

/-! Common-denominator integer masses computed from rational input arrays. -/

namespace Paper2.IndexedRationalDenominator

open scoped BigOperators
open Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open Paper2.IndexedRationalFinCode Paper2.IndexedRationalProgramBridge
open Paper2.IndexedRationalLawBridge
open Paper2.GeneratorCode Paper2.RecursiveLabelCodecScratch

/-- An executable integer mass for a position in a finite rational array. -/
def mass {n : ℕ} (q : Fin n → ℚ) (i : Fin n) : ℕ :=
  (q i).num.toNat * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
    (q j).den

theorem mass_eq_multiplicity {n : ℕ} (μ : PositiveRationalLaw (Fin n))
    (i : Fin n) : mass μ.weight i = μ.multiplicity i := by
  classical
  unfold mass PositiveRationalLaw.multiplicity
  congr 1
  apply Finset.prod_congr
  · ext j
    simp
  · intro j hj
    rfl

theorem mass_pos {n : ℕ} (μ : PositiveRationalLaw (Fin n))
    (i : Fin n) : 0 < mass μ.weight i := by
  rw [mass_eq_multiplicity]
  exact μ.multiplicity_pos i

theorem mass_sum {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    ∑ i, mass μ.weight i = μ.denominator := by
  simp_rw [mass_eq_multiplicity]
  exact μ.sum_multiplicity

theorem mass_scaled {n : ℕ} (μ : PositiveRationalLaw (Fin n))
    (i : Fin n) :
    (mass μ.weight i : ℚ) = μ.weight i * μ.denominator := by
  rw [mass_eq_multiplicity]
  exact μ.multiplicity_eq_scaled i

theorem normalized_mass_eq {n : ℕ} (μ : PositiveRationalLaw (Fin n))
    (i : Fin n) :
    (mass μ.weight i : ℚ) / (∑ j, mass μ.weight j) = μ.weight i := by
  rw [mass_sum, mass_scaled]
  have hd : (μ.denominator : ℚ) ≠ 0 := by
    exact_mod_cast μ.denominator_pos.ne'
  field_simp

/-- A first-order code computed from the rational-weight array itself. -/
def rationalCode {n : ℕ} (μ : PositiveRationalLaw (Fin n)) : Code :=
  code n (mass μ.weight)

/-- Typed finite-choice meaning of the rational code. -/
def rationalProgram {n : ℕ} (hn : 0 < n)
    (μ : PositiveRationalLaw (Fin n)) : Program (Fin n) :=
  program hn (indices n (mass μ.weight))

theorem rationalCode_exact {n : ℕ} (hn : 0 < n)
    (μ : PositiveRationalLaw (Fin n)) :
    meaning (rationalCode μ) =
      Program.map (finCodec n).encode (rationalProgram hn μ) := by
  exact code_exact hn (mass μ.weight) (mass_pos μ)

theorem rationalProgram_generates {n : ℕ} (hn : 0 < n)
    (μ : PositiveRationalLaw (Fin n)) :
    Generates (rationalProgram hn μ) μ.toFiniteLaw := by
  intro f
  have h := program_generates hn (mass μ.weight) (mass_pos μ) f
  change Program.expect (rationalProgram hn μ) f =
    ∑ i, ((law hn (mass μ.weight) (mass_pos μ)).toFiniteLaw.weight i) * f i at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (((mass μ.weight i : ℚ) /
      (∑ j, mass μ.weight j) : ℚ) : ℝ) = (μ.weight i : ℝ)
  exact_mod_cast normalized_mass_eq μ i

#print axioms mass_scaled
#print axioms rationalCode_exact
#print axioms rationalProgram_generates

end Paper2.IndexedRationalDenominator
