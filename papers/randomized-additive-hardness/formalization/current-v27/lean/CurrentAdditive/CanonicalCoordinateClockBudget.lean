import CurrentAdditive.CanonicalWriterClockEnvelope

namespace CurrentAdditive.FiniteFieldCoordinate

set_option maxHeartbeats 2000000

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open EthInapproximability.CurrentPaper

/-- The seven source-preserving copies at the start of the coordinate
subroutine pay only for the seven actual public input words. -/
theorem stage_fill_cost_le (S : Stack → List Bool) (B : ℕ)
    (h : ∀ k : Fin 7, (S ⟨k.val, by omega⟩).length ≤ B) :
    CopyFill.fillCost jobs S ≤ 14 * (B + 1) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have b0 : (S 0).length ≤ B := by simpa using h0
  have b1 : (S 1).length ≤ B := by simpa using h1
  have b2 : (S 2).length ≤ B := by simpa using h2
  have b3 : (S 3).length ≤ B := by simpa using h3
  have b4 : (S 4).length ≤ B := by simpa using h4
  have b5 : (S 5).length ≤ B := by simpa using h5
  have b6 : (S 6).length ≤ B := by simpa using h6
  simp only [jobs, CopyFill.fillCost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

/-- `CopyFill.fill` only reuses source words from the same bounded bank. -/
theorem fill_length_le (jobs' : List (Stack × List Stack))
    (S : Stack → List Bool) (B : ℕ)
    (hS : ∀ k, (S k).length ≤ B) (k : Stack) :
    (CopyFill.fill jobs' S k).length ≤ B := by
  induction jobs' with
  | nil => simpa [CopyFill.fill] using hS k
  | cons job rest ih =>
      simp only [CopyFill.fill]
      split
      · exact hS job.1
      · exact ih

/-- Every coordinate scratch cell immediately after the seven public copies
is either empty or a copy of one bounded public input. -/
theorem staged_scratch_bound_le (S : Stack → List Bool) (B : ℕ)
    (h : ∀ k : Fin 7, (S ⟨k.val, by omega⟩).length ≤ B)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    scratchBound (staged S) ≤ B := by
  have hS : ∀ k : Stack, (S k).length ≤ B := by
    intro k
    by_cases hk : k.val < 7
    · have h' := h ⟨k.val, hk⟩
      simpa only [Fin.eta] using h'
    · rw [hblank k (by omega)]
      simp
  unfold scratchBound
  apply Finset.sup_le
  intro i _
  exact fill_length_le jobs S B hS (scratchSlots i)

/-- The fixed selector program has a cubic transition envelope in a bound
for its unary inputs and the largest intermediate power. -/
theorem selectorClock_le_cubic (B H z g : ℕ)
    (hH : H ≤ B) (hz : z ≤ B) (hg : g ≤ B)
    (hpow : H ^ g ≤ B) :
    selectorClock 0 H z g ≤ 100 * (B + 1) ^ 3 := by
  have hp := MatrixWeightedPower.powerBound_polynomial H g
  have hp' : MatrixWeightedPower.powerBound H g ≤
      (B + 1) * (3 * (B + 1) * B + 5 * (B + 1) + 7) := by
    calc
      _ ≤ (g + 1) * (3 * (H ^ g + 1) * H +
          5 * (H ^ g + 1) + 7) := hp
      _ ≤ (B + 1) * (3 * (B + 1) * B +
          5 * (B + 1) + 7) := by gcongr
  have hdiv : z / H ^ g ≤ z := Nat.div_le_self _ _
  unfold selectorClock
  nlinarith [sq_nonneg (B : ℤ)]

/-- The incidence scanner reads each source token and spends at most
quadratic time in the lengths and numeric values visible in its bank. -/
theorem positionClock_le_cubic (B t a vertex : ℕ) (body : List Bool)
    (ht : t ≤ B) (ha : a ≤ B) (hv : vertex ≤ B)
    (hbody : body.length ≤ B)
    (hK : Paper2.YaoSourceCodec.arity t ≤ B) :
    positionClock t a vertex body ≤ 100 * (B + 1) ^ 3 := by
  have hAK : a * Paper2.YaoSourceCodec.arity t ≤ B ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul ha hK
  have hKV : Paper2.YaoSourceCodec.arity t * vertex ≤ B ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hK hv
  unfold positionClock
  nlinarith [sq_nonneg (B : ℤ)]

/-- The final arithmetic address step is quadratic in its three unary
inputs, including the extra incidence slot. -/
theorem payloadClock_le_cubic (B K α p : ℕ)
    (hK : K ≤ B) (hα : α ≤ B) (hp : p ≤ B) :
    payloadClock K α p ≤ 100 * (B + 1) ^ 3 := by
  unfold payloadClock
  nlinarith [sq_nonneg (B : ℤ)]

/-- One coefficient for the fixed finite-control programs. Each `pushBudget`
is a constant of the selected statement table, independent of source size. -/
noncomputable def coordinateProgramCoefficient : ℕ :=
  selectorPushBudget + positionPushBudget + widthPushBudget +
    payloadPushBudget + 1

noncomputable def coordinateStageClock (q H K z g t a vertex α p : ℕ)
    (body : List Bool) (S : Stack → List Bool) : ℕ :=
  CopyFill.fillCost jobs S + 1 +
    selectorClock q H z g + positionClock t a vertex body + 1 +
    payloadClock K α p +
    (32 * preclearBound q H K z g t a vertex α p body S + 34) + 5

/-- A common polynomial clock for the entire fixed coordinate program,
including preparation, selector, incidence, payload arithmetic, and clearing.
The hypotheses mention only values visible on its prepared input bank. -/
theorem coordinateStageClock_le (B q H K z g t a vertex α p : ℕ)
    (body : List Bool) (S : Stack → List Bool)
    (hS : ∀ k : Fin 7, (S ⟨k.val, by omega⟩).length ≤ B)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = [])
    (hH : H ≤ B) (hK : K ≤ B)
    (hArity : Paper2.YaoSourceCodec.arity t ≤ B)
    (hz : z ≤ B) (hg : g ≤ B) (hpow : H ^ g ≤ B)
    (ht : t ≤ B) (ha : a ≤ B) (hv : vertex ≤ B)
    (hbody : body.length ≤ B)
    (hα : α ≤ B) (hp : p ≤ B) :
    coordinateStageClock q H K z g t a vertex α p body S ≤
      10000 * (B + 1) ^ 3 * coordinateProgramCoefficient := by
  let Q := 100 * (B + 1) ^ 3
  let P := coordinateProgramCoefficient
  have hQ : B + 1 ≤ Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (B : ℤ)]
  have hP : 1 ≤ P := by
    dsimp [P, coordinateProgramCoefficient]
    omega
  have hstage : CopyFill.fillCost jobs S ≤ Q := by
    have h := stage_fill_cost_le S B hS
    dsimp [Q]
    nlinarith [sq_nonneg (B : ℤ)]
  have hscratch : scratchBound (staged S) ≤ B :=
    staged_scratch_bound_le S B hS hblank
  have hsel : selectorClock q H z g ≤ Q :=
    selectorClock_le_cubic B H z g hH hz hg hpow
  have hpos : positionClock t a vertex body ≤ Q :=
    positionClock_le_cubic B t a vertex body ht ha hv hbody hArity
  have hpay : payloadClock K α p ≤ Q :=
    payloadClock_le_cubic B K α p hK hα hp
  have hsP : selectorClock q H z g * selectorPushBudget ≤
      Q * selectorPushBudget := Nat.mul_le_mul_right _ hsel
  have hoP : positionClock t a vertex body * positionPushBudget ≤
      Q * positionPushBudget := Nat.mul_le_mul_right _ hpos
  have hpP : payloadClock K α p * payloadPushBudget ≤
      Q * payloadPushBudget := Nat.mul_le_mul_right _ hpay
  have hwP : widthPushBudget ≤ Q * widthPushBudget := by
    have : 1 ≤ Q := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right widthPushBudget this
  have hpre : preclearBound q H K z g t a vertex α p body S ≤
      B + Q * P := by
    unfold preclearBound
    dsimp only [P, coordinateProgramCoefficient]
    simp only [mul_add, mul_one]
    omega
  unfold coordinateStageClock
  have hresult : Q + 1 + Q + Q + 1 + Q +
        (32 * (B + Q * P) + 34) + 5 ≤ 100 * Q * P := by
    nlinarith
  calc
    _ ≤ Q + 1 + Q + Q + 1 + Q +
        (32 * (B + Q * P) + 34) + 5 := by omega
    _ ≤ 100 * Q * P := hresult
    _ = 10000 * (B + 1) ^ 3 * coordinateProgramCoefficient := by
      dsimp [Q, P]
      ring

#print axioms stage_fill_cost_le
#print axioms staged_scratch_bound_le
#print axioms selectorClock_le_cubic
#print axioms positionClock_le_cubic
#print axioms payloadClock_le_cubic
#print axioms coordinateStageClock_le

end CurrentAdditive.FiniteFieldCoordinate
