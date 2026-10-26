import CurrentAdditive.ExecutableSourceSpec

/-! Exact array enumeration of finite indexed rational alphabets. -/

namespace CurrentAdditive.ExecutableCodeSource

open Paper2 SequentialCode SequentialSourceCode SequentialAppendMoments
  SequentialFeatureCoverage SequentialFiniteLaw

def finEntries (n : Nat) (w : Fin n → ℚ) : Array (Fin n × ℚ) :=
  Array.ofFn (fun i => (i, w i))

theorem finEntries_size (n : Nat) (w : Fin n → ℚ) :
    (finEntries n w).size = n := by
  simp [finEntries]

theorem finEntries_weightedSum (n : Nat) (w : Fin n → ℚ)
    (f : Fin n → ℚ) :
    weightedSum (finEntries n w) f = ∑ i : Fin n, w i * f i := by
  simp [weightedSum, finEntries, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]

theorem finEntries_positive (n : Nat) (w : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) : SourcePositive (finEntries n w) := by
  apply Array.all_eq_true.mpr
  intro i hi
  simp [finEntries, hw]

theorem finEntries_mass (n : Nat) (w : Fin n → ℚ) :
    sourceMass (finEntries n w) = ∑ i : Fin n, w i := by
  rw [sourceMass_eq_weightedSum, finEntries_weightedSum]
  simp

theorem finEntries_cover (n : Nat) (w : Fin n → ℚ)
    (i : Fin n) : i ∈ ((finEntries n w).map Prod.fst).toList := by
  simp [finEntries]

theorem finEntries_pointMass (n : Nat) (w : Fin n → ℚ)
    (i : Fin n) :
    alphabetPointMass (finEntries n w) i = w i := by
  rw [alphabetPointMass, finEntries_weightedSum]
  simp

def finAlphabetTable (n : Nat) (μ : PositiveRationalLaw (Fin n)) :
    AlphabetTable (Fin n) μ where
  entries := finEntries n μ.weight
  positive := finEntries_positive n μ.weight μ.positive
  normalized := by simpa [finEntries_mass] using μ.total
  covers := finEntries_cover n μ.weight
  pointMass := finEntries_pointMass n μ.weight

def uniformFinEntries (n : Nat) : Array (Fin n × ℚ) :=
  finEntries n (fun _ => (n : ℚ)⁻¹)

theorem uniformFinEntries_size (n : Nat) :
    (uniformFinEntries n).size = n :=
  finEntries_size n _

noncomputable def uniformFinTable (n : Nat) [NeZero n] :
    AlphabetTable (Fin n) (PositiveRationalLaw.uniform (Fin n)) :=
  finAlphabetTable n (PositiveRationalLaw.uniform (Fin n))

theorem uniformFinTable_entries (n : Nat) [NeZero n] :
    (uniformFinTable n).entries = uniformFinEntries n := by
  simp [uniformFinTable, finAlphabetTable, uniformFinEntries,
    PositiveRationalLaw.uniform]

#print axioms finEntries_weightedSum
#print axioms finEntries_size
#print axioms finAlphabetTable
#print axioms uniformFinTable_entries

end CurrentAdditive.ExecutableCodeSource
