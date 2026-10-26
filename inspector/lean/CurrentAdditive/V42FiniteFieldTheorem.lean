import CurrentAdditive.V42FiniteFieldMachine

/-! The complete all-parameter v42 finite-field list algorithm. A fixed
arithmetic compiler computes the least dyadic field degree, and one fixed
finite Boolean-stack machine then searches for the irreducible modulus
and prints the full row-major list. -/

namespace CurrentAdditive.V42FiniteFieldTheorem

open Paper2 CurrentAdditive.SmallBias CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldMachine
open CurrentAdditive.V42FiniteFieldList
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition
open D22NatExpression

set_option maxHeartbeats 1500000

/-- Both public inputs are supplied in the fixed three-field unary encoding;
the unused third field is empty. -/
def input (n r : ℕ) : List Bool := D22NatExpression.input n r 0

def degreeExpr : Expr :=
  .unary .clog (.binary (.old .mul) (.var 0) (.unary .pow2 (.var 1)))
def widthExpr : Expr := .var 0

noncomputable def parameterMachine : BitMachine.Machine :=
  V22UnaryFork.machine degreeExpr.machine widthExpr.machine

noncomputable def parameterClock (n r : ℕ) : ℕ :=
  4 * (input n r).length + degreeExpr.clock n r 0 + widthExpr.clock n r 0 +
    3 * degree n r + 3 * n + 17

noncomputable def parameterCoefficient : ℕ :=
  100 * (degreeExpr.coefficient + widthExpr.coefficient) + 200

noncomputable def machine : BitMachine.Machine :=
  composition parameterMachine V42FiniteFieldMachine.machine

def fieldClock (d n c : ℕ) : ℕ :=
  d+n+3 + FieldSearchCompletion.FieldUnaryUnifiedMachine.prepTime d n +
    55 * 2 ^ d * 2 ^ (d / 2) * (d+1)^2 + 2 +
      FieldListOutputMachine.timeBound d c n

noncomputable def totalClock (n r c : ℕ) : ℕ :=
  parameterClock n r + 2 * (MatrixUnaryArithmetic.encodeInput (degree n r) n).length + 2 +
    fieldClock (degree n r) n c

noncomputable def coefficient : ℕ := parameterCoefficient + 1100

theorem parameterMachine_outputs (n r : ℕ) :
    parameterMachine.OutputsWithin (input n r)
      (MatrixUnaryArithmetic.encodeInput (degree n r) n) (parameterClock n r) := by
  have hd := degreeExpr.outputs n r 0
  have hn := widthExpr.outputs n r 0
  have h := V22UnaryFork.outputs degreeExpr.machine widthExpr.machine
    (input n r) (degree n r) n (degreeExpr.clock n r 0) (widthExpr.clock n r 0)
    (by simpa [degreeExpr, Expr.eval, Binary.value, V22UnaryExpression.Binary.value,
      V22UnaryExpression.Unary.value, values, degree, target, input] using hd)
    (by simpa [widthExpr, Expr.eval, values, input] using hn)
  exact h

private theorem parameter_bounds (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    n ≤ target n r ∧ r ≤ target n r ∧ 2 ^ r ≤ target n r ∧ degree n r ≤ target n r := by
  have hp : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hnN : n ≤ target n r := by unfold target; nlinarith
  have hpN : 2 ^ r ≤ target n r := by unfold target; nlinarith
  refine ⟨hnN, (Nat.lt_two_pow_self.le).trans hpN, hpN, ?_⟩
  exact (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).2 Nat.lt_two_pow_self.le

private theorem inputLength_le (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (input n r).length ≤ 7 * (target n r + 1) := by
  obtain ⟨hN, hrN, _, _⟩ := parameter_bounds n r hn hr
  unfold input D22NatExpression.input
  rw [BitMachineBankCodec.encode_length]
  simp only [List.length_replicate, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change 2*(n+(r+(0+0)))+3 ≤ _
  omega

private theorem degreeExpr_peak (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    degreeExpr.peak n r 0 ≤ target n r := by
  obtain ⟨hN, hrN, hpN, hdN⟩ := parameter_bounds n r hn hr
  change max (degree n r) (max (target n r) (max n (max (2 ^ r) r))) ≤ target n r
  exact max_le hdN (max_le le_rfl (max_le hN (max_le hpN hrN)))

theorem parameterClock_le (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    parameterClock n r ≤ parameterCoefficient * (target n r + 1)^2 := by
  let B := target n r + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hin := inputLength_le n r hn hr
  have hb : D22NatExpression.inputLength n r 0 + target n r + 2 ≤ 10*B := by
    change (input n r).length + target n r + 2 ≤ _
    dsimp [B] at *
    omega
  have hdc := degreeExpr.clock_le_of_peak n r 0 (target n r) (degreeExpr_peak n r hn hr)
  have hwc := widthExpr.clock_le_of_peak n r 0 (target n r)
    (by exact (parameter_bounds n r hn hr).1)
  have hs : (D22NatExpression.inputLength n r 0 + target n r + 2)^2 ≤ (10*B)^2 :=
    Nat.pow_le_pow_left hb 2
  have hd := hdc.trans (Nat.mul_le_mul_left degreeExpr.coefficient hs)
  have hw := hwc.trans (Nat.mul_le_mul_left widthExpr.coefficient hs)
  obtain ⟨hnN, hrN, hpN, hdN⟩ := parameter_bounds n r hn hr
  have hB2 : B ≤ B^2 := by nlinarith
  have htail : 4*(input n r).length + 3*degree n r + 3*n + 17 ≤ 200*B^2 := by
    dsimp [B] at hin hnN hdN hB2 ⊢
    nlinarith
  dsimp [parameterClock, parameterCoefficient]
  change _ ≤ (100 * (degreeExpr.coefficient + widthExpr.coefficient) + 200) * B^2
  nlinarith

/-- Search, unary-bank preparation, and the literal printer all fit one
polynomial in the source's integer `n 2^r`. Search is not omitted. -/
theorem fieldClock_le (n r c : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    fieldClock (degree n r) n c ≤ 1000 * (target n r+1)^5 := by
  let B := target n r+1
  let d := degree n r
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : 0 < d := degree_pos n r hn hr
  obtain ⟨hnN, hrN, hpN, hdN⟩ := parameter_bounds n r hn hr
  have hnB : n ≤ B := by dsimp [B]; omega
  have hdB : d+1 ≤ B := by dsimp [d, B]; omega
  have hR : 2 ^ d ≤ 2*B := (order_lt n r hn hr).le.trans (by dsimp [B]; omega)
  have hhR : 2 ^ (d/2) ≤ 2*B :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.div_le_self d 2)).trans hR
  have hs : 55 * 2 ^ d * 2 ^ (d/2) * (d+1)^2 ≤ 220 * B^4 := by
    calc
      _ ≤ 55*(2*B)*(2*B)*B^2 := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ hR) hhR) (Nat.pow_le_pow_left hdB 2)
      _ = _ := by ring
  have hp := FieldListOutputMachine.timeBound_le d c n hd (by omega)
  have hp' : 25*(2^d)^2*n*(d+1)^2 ≤ 100*B^5 := by
    calc
      _ ≤ 25*(2*B)^2*B*B^2 := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR 2)) hnB)
        (Nat.pow_le_pow_left hdB 2)
      _ = _ := by ring
  have hprint := hp.trans hp'
  have hB4 : B^4 ≤ B^5 := Nat.pow_le_pow_right hB (by omega)
  have hB1 : B ≤ B^5 := by simpa using Nat.pow_le_pow_right hB (by omega : 1 ≤ 5)
  have hB0 : 1 ≤ B^5 := one_le_pow₀ hB
  have hddiv : d/2 ≤ d := Nat.div_le_self d 2
  dsimp [fieldClock, FieldSearchCompletion.FieldUnaryUnifiedMachine.prepTime]
  change d+n+3+(2*d+d/2+2*n+7)+55*2^d*2^(d/2)*(d+1)^2+2+
    FieldListOutputMachine.timeBound d c n ≤ 1000 * B^5
  nlinarith

theorem totalClock_le (n r c : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    totalClock n r c ≤ coefficient * (target n r+1)^5 := by
  let B := target n r+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have h2 : B^2 ≤ B^5 := Nat.pow_le_pow_right hB (by omega)
  have hp := (parameterClock_le n r hn hr).trans (Nat.mul_le_mul_left parameterCoefficient h2)
  have hf := fieldClock_le n r c hn hr
  obtain ⟨hnN, _, _, hdN⟩ := parameter_bounds n r hn hr
  have h1 : B ≤ B^5 := by simpa using Nat.pow_le_pow_right hB (by omega : 1 ≤ 5)
  have h0 : 1 ≤ B^5 := one_le_pow₀ hB
  have hlen : (MatrixUnaryArithmetic.encodeInput (degree n r) n).length = degree n r+n+1 := by
    simp [MatrixUnaryArithmetic.encodeInput, Nat.add_assoc]
  dsimp [totalClock, coefficient]
  rw [hlen]
  dsimp [B] at hp hf h1 h0 ⊢
  nlinarith

/-- The deterministic physical computation begins with n,r, computes the
least dyadic degree itself, searches for an irreducible polynomial, and
outputs the complete ordered bit array. No field or cost certificate is a
premise. -/
theorem machine_outputs (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ∃ c < order n r,
      TrialSearch.firstPassing (degree n r) = some (TrialSearch.monicBits (degree n r) c) ∧
      machine.OutputsWithin (input n r)
        (UnifiedFieldListMachine.packedBits (degree n r) c n)
        (coefficient * (target n r+1)^5) := by
  obtain ⟨c, hc, hfirst, hout⟩ := V42FiniteFieldMachine.machine_outputs
    (degree n r) n (degree_pos n r hn hr)
  have h := composition_outputsWithin parameterMachine V42FiniteFieldMachine.machine
    (parameterMachine_outputs n r) hout
  refine ⟨c, hc, hfirst, ?_⟩
  exact BitMachine.outputsWithin_mono machine h (totalClock_le n r c hn hr)

#print axioms parameterMachine_outputs
#print axioms parameterClock_le
#print axioms fieldClock_le
#print axioms totalClock_le
#print axioms machine_outputs

end CurrentAdditive.V42FiniteFieldTheorem
