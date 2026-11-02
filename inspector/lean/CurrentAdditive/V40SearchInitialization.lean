import CurrentAdditive.V40DeterministicBoundedSearch
import CurrentAdditive.V22ExpressionClock
import EthInapproximability.CurrentPaper.BankFieldProjection

set_option autoImplicit false

namespace CurrentAdditive.V40SearchInitialization

open EthInapproximability.CurrentPaper BitMachineComposition
open V22UnaryExpression V39GeneratedConstruction

def input (floor n m : Nat) : List Bool :=
  BitMachineBankCodec.encode
    (![List.replicate floor true, List.replicate n true, List.replicate m true] : Fin 3 → List Bool)

theorem input_length (floor n m : Nat) :
    (input floor n m).length = 2 * (floor + n + m) + 3 := by
  simp [input, BitMachineBankCodec.encode_length, Fin.sum_univ_succ, Nat.add_assoc]

def startExpr : Expr := .unary .clog (.binary .max .vertex .iteration)

def upperExpr (p : SourceConstants) : Expr :=
  .binary .max startExpr (.const (GeneratedCutoff.cutoffLog p.degree p.deletion))

@[simp] theorem startExpr_value (floor n : Nat) :
    startExpr.eval floor n = V40DeterministicBoundedSearch.start floor n := rfl

@[simp] theorem upperExpr_value (p : SourceConstants) (floor n : Nat) :
    (upperExpr p).eval floor n = publicUpperLog p floor n := rfl

noncomputable def pairMachine : BitMachine.Machine :=
  V22UnaryFork.machine (BankFieldProjection.machine (0 : Fin 3))
    (BankFieldProjection.machine (1 : Fin 3))

def pairClock (floor n m : Nat) : Nat :=
  4 * (input floor n m).length + 20 * ((input floor n m).length + 1) +
    3 * floor + 3 * n + 17

theorem pair_outputs (floor n m : Nat) :
    pairMachine.OutputsWithin (input floor n m)
      (MatrixUnaryArithmetic.encodeInput floor n) (pairClock floor n m) := by
  have h0 := BankFieldProjection.outputs (0 : Fin 3) (input floor n m)
  have h1 := BankFieldProjection.outputs (1 : Fin 3) (input floor n m)
  have h0' : (BankFieldProjection.machine (0 : Fin 3)).OutputsWithin
      (input floor n m) (List.replicate floor true)
      (10 * ((input floor n m).length + 1)) := by
    simpa [BankFieldProjection.result, input] using h0
  have h1' : (BankFieldProjection.machine (1 : Fin 3)).OutputsWithin
      (input floor n m) (List.replicate n true)
      (10 * ((input floor n m).length + 1)) := by
    simpa [BankFieldProjection.result, input] using h1
  convert V22UnaryFork.outputs (BankFieldProjection.machine (0 : Fin 3))
      (BankFieldProjection.machine (1 : Fin 3)) (input floor n m) floor n
      (10 * ((input floor n m).length + 1)) (10 * ((input floor n m).length + 1)) h0' h1' using 1 <;>
    simp only [pairMachine, pairClock] <;> ring

noncomputable def expressionMachine (e : Expr) : BitMachine.Machine :=
  composition pairMachine e.machine

noncomputable def expressionClock (e : Expr) (floor n m : Nat) : Nat :=
  pairClock floor n m + 2 * (MatrixUnaryArithmetic.encodeInput floor n).length + 2 + e.clock floor n

theorem expression_outputs (e : Expr) (floor n m : Nat) :
    (expressionMachine e).OutputsWithin (input floor n m)
      (List.replicate (e.eval floor n) true) (expressionClock e floor n m) := by
  exact composition_outputsWithin pairMachine e.machine
    (pair_outputs floor n m) (e.outputs floor n)

theorem start_outputs (floor n m : Nat) :
    (expressionMachine startExpr).OutputsWithin (input floor n m)
      (List.replicate (Nat.clog 2 (max floor n)) true)
      (expressionClock startExpr floor n m) := expression_outputs startExpr floor n m

theorem upper_outputs (p : SourceConstants) (floor n m : Nat) :
    (expressionMachine (upperExpr p)).OutputsWithin (input floor n m)
      (List.replicate (publicUpperLog p floor n) true)
      (expressionClock (upperExpr p) floor n m) := expression_outputs (upperExpr p) floor n m

private theorem clog_le (a : Nat) : Nat.clog 2 a ≤ a :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))

theorem start_peak (floor n : Nat) : startExpr.peak floor n ≤ floor + n := by
  have h := clog_le (max floor n)
  have hm : max floor n ≤ floor + n := max_le (by omega) (by omega)
  change max (Nat.clog 2 (Nat.max floor n))
    (max (Nat.max floor n) (max floor n)) ≤ floor + n
  exact max_le (h.trans hm) (max_le hm hm)

theorem upper_peak (p : SourceConstants) (floor n : Nat) :
    (upperExpr p).peak floor n ≤ floor + n + GeneratedCutoff.cutoffLog p.degree p.deletion := by
  have hs := start_peak floor n
  have hv := startExpr.eval_le_peak floor n
  change max (Nat.max (startExpr.eval floor n) (GeneratedCutoff.cutoffLog p.degree p.deletion))
    (max (startExpr.peak floor n) (GeneratedCutoff.cutoffLog p.degree p.deletion)) ≤ _
  apply max_le
  · exact max_le ((hv.trans hs).trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)
  · exact max_le (hs.trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)

/-- The whole initializer's actual clock has fixed polynomial constants in
the original three-field input length, before every floor and graph count. -/
theorem expression_clock_bound (e : Expr) (c : Nat)
    (hpeak : ∀ floor n, e.peak floor n ≤ floor + n + c) :
    ∀ floor n m,
      expressionClock e floor n m ≤
        (60 + e.coefficient * (c + 4) ^ 2) * ((input floor n m).length + 1) ^ 2 := by
  intro floor n m
  let Z := (input floor n m).length + 1
  have hZ1 : 1 ≤ Z := by dsimp [Z]; omega
  have hin : floor + n ≤ Z := by simp only [Z, input_length]; omega
  have hZZ : Z ≤ Z ^ 2 := by nlinarith only [hZ1]
  have hc := e.clock_le_of_peak floor n (floor + n + c) (hpeak floor n)
  have harg : floor + n + (floor + n + c) + 2 ≤ (c + 4) * Z := by nlinarith only [hin, hZ1]
  have hclock : e.clock floor n ≤ e.coefficient * (c + 4) ^ 2 * Z ^ 2 := by
    calc
      _ ≤ e.coefficient * (floor + n + (floor + n + c) + 2) ^ 2 := hc
      _ ≤ e.coefficient * ((c + 4) * Z) ^ 2 := by gcongr
      _ = e.coefficient * (c + 4) ^ 2 * Z ^ 2 := by ring
  have hpair : pairClock floor n m +
      2 * (MatrixUnaryArithmetic.encodeInput floor n).length + 2 ≤ 60 * Z ^ 2 := by
    have he : (MatrixUnaryArithmetic.encodeInput floor n).length = floor + n + 1 := by
      simp [MatrixUnaryArithmetic.encodeInput, Nat.add_assoc]
    simp only [pairClock, he]
    dsimp only [Z] at hin hZZ ⊢
    nlinarith only [hin, hZZ]
  dsimp only [expressionClock, Z] at hclock hpair ⊢
  nlinarith only [hclock, hpair]

theorem start_clock_polynomial :
    ∃ C : Nat, ∀ floor n m,
      expressionClock startExpr floor n m ≤ C * ((input floor n m).length + 1) ^ 2 := by
  refine ⟨60 + startExpr.coefficient * 4 ^ 2, ?_⟩
  simpa using expression_clock_bound startExpr 0 (by intro floor n; simpa using start_peak floor n)

theorem upper_clock_polynomial (p : SourceConstants) :
    ∃ C : Nat, ∀ floor n m,
      expressionClock (upperExpr p) floor n m ≤ C * ((input floor n m).length + 1) ^ 2 := by
  exact ⟨_, expression_clock_bound (upperExpr p)
    (GeneratedCutoff.cutoffLog p.degree p.deletion) (upper_peak p)⟩

end CurrentAdditive.V40SearchInitialization
