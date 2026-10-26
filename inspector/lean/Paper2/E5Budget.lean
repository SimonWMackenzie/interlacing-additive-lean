import Paper2.E3Inner
import Paper2.A4Loops

/-! a-eth-owner-5 copy of frozen `a-eth-owner-4/E4Budget.lean` (SHA-256 d92d8ea9eb84a8233bfe442b13566d48300b0ef1cdb51376af71b298f0296c31). Changes: docstring D1 corrected (factor 2^4 instead of 2^8); nothing else. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 2 (obstacle O2): a decider tape that covers every cut request

`expLen N = 2^(N / llog N)` is not monotone, so the tape `expLen |x|` can be shorter than the cut request
`cutLen F = 2|encode F| + 2 expLen N + 3` (a-eth-owner-3 `E3Inner.cutLen_eq`). Here the decider tape is
`TL m = 2^(e0 m + 8)` with `e0 m = m / (llog m - 1)`. The numeric core `expExp_fit` shows that
`e0 m + 4` dominates the RUNNING MAXIMUM `max_{N ≤ m} expExp N`, so `TL m` dominates `2^4` times the
(monotone) running maximum of `expLen` (factor `2^4`, NOT `2^8`: read-back D1, at `m = 4` one has
`TL 4 = 256 < 2^8 · expLen 4`); monotonicity of `TL` itself is not needed. Consequences:
`cutLen F ≤ 2^(e0 |encode F| + 7)`, i.e. the cut request uses at most HALF of the decider tape, for EVERY
CNF word (valid or not); `TL` is subexponential; ONE fixed length machine `TLMachine` prints `1^(TL m)` from
`1^m` within `TLtime m ≤ (BT + 20) (m + TL m + 1)^2` (the R20 `lenPoly` shape).

Imports: frozen `E3Inner` (a-eth-owner-3; it imports frozen `SubexpBudget`, `SubexpLen` of a-eth-owner-1 and
frozen `ECutRun` of a-eth-owner-2), all hash-checked against their lanes' pins; admitted `Paper2.A4Loops`.
No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth4

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell
open Paper2.Unit4Shell.Loops
open Paper2.Unit4Shell.KofLoops
open Paper2.AEth (llog expExp expLen Subexp loglogMachine le_llog llog_le loglog_outputs)

/-- The exponent of the decider tape. -/
def e0 (m : ℕ) : ℕ := m / (llog m - 1)

/-- **The decider tape length** `2^(m / (llog m - 1) + 8)`. -/
def TL (m : ℕ) : ℕ := 2 ^ (e0 m + 8)

theorem le_two_pow_two_pow_llog (N : ℕ) : N ≤ 2 ^ (2 ^ llog N) := by
  have h1 : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (by norm_num) N
  have h2 : Nat.clog 2 N ≤ 2 ^ llog N := Nat.le_pow_clog (by norm_num) _
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)

theorem lt_of_llog {m L : ℕ} (hL : llog m = L + 1) : 2 ^ (2 ^ L) < m := by
  have hc : 2 ^ L < Nat.clog 2 m := by
    by_contra h
    push Not at h
    have : Nat.clog 2 (Nat.clog 2 m) ≤ L := Nat.clog_le_of_le_pow h
    unfold llog at hL
    omega
  by_contra h
  push Not at h
  have : Nat.clog 2 m ≤ 2 ^ L := Nat.clog_le_of_le_pow h
  omega

theorem llog_mono {a b : ℕ} (h : a ≤ b) : llog a ≤ llog b :=
  Nat.clog_mono_right 2 (Nat.clog_mono_right 2 h)

theorem small_of_llog {m : ℕ} (h : llog m ≤ 1) : m ≤ 4 := by
  have h1 : Nat.clog 2 m ≤ 2 ^ 1 := (Nat.clog_le_iff_le_pow (by norm_num)).1 (by unfold llog at h; exact h)
  have h2 : m ≤ 2 ^ 2 := (Nat.clog_le_iff_le_pow (by norm_num)).1 (by simpa using h1)
  simpa using h2

theorem succ_le_two_pow_two_pow (j : ℕ) : j + 1 ≤ 2 ^ (2 ^ j) := by
  have h1 : j < 2 ^ j := Nat.lt_two_pow_self
  have h2 : 2 ^ j ≤ 2 ^ (2 ^ j) := Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le
  omega

/-- **The running maximum of the exponent is dominated.** For EVERY `N ≤ m`,
`expExp N ≤ e0 m + 4`. -/
theorem expExp_fit (N m : ℕ) (hNm : N ≤ m) : expExp N ≤ e0 m + 4 := by
  unfold expExp e0
  rcases Nat.lt_or_ge (llog m) 2 with hL | hL
  · have hm := small_of_llog (by omega : llog m ≤ 1)
    have := Nat.div_le_self N (llog N)
    have := Nat.zero_le (m / (llog m - 1))
    omega
  · have hL' : llog N ≤ llog m := llog_mono hNm
    rcases Nat.eq_zero_or_pos (llog N) with h0 | hpos
    · rw [h0, Nat.div_zero]
      exact Nat.zero_le _
    · rcases Nat.lt_or_ge (llog N) (llog m - 1) with hlow | hhigh
      · -- low block: N ≤ 2^(2^(L-2)) and m > 2^(2^(L-1))
        obtain ⟨j, hj⟩ : ∃ j, llog m = j + 2 := ⟨llog m - 2, by omega⟩
        set b := 2 ^ (2 ^ j) with hb
        have hNb : N ≤ b := by
          have := le_two_pow_two_pow_llog N
          exact this.trans (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num)
            (show llog N ≤ j by omega)))
        have hmb : b * b < m := by
          have h := lt_of_llog (L := j + 1) (by omega)
          have hbb : b * b = 2 ^ (2 ^ (j + 1)) := by
            rw [hb, ← pow_add, pow_succ]
            congr 1
            ring
          omega
        have hj1 : j + 1 ≤ b := succ_le_two_pow_two_pow j
        have hbm : b ≤ m / (llog m - 1) := by
          rw [Nat.le_div_iff_mul_le (by omega)]
          have : b * (llog m - 1) ≤ b * b := Nat.mul_le_mul_left _ (by omega)
          omega
        have := Nat.div_le_self N (llog N)
        omega
      · have := Nat.div_le_div hNm hhigh (by omega)
        omega

theorem expLen_fit (N m : ℕ) (hNm : N ≤ m) : expLen N ≤ 2 ^ (e0 m + 4) :=
  Nat.pow_le_pow_right (by norm_num) (expExp_fit N m hNm)

/-- The linear part of the cut request fits as well. -/
theorem lin_fit (m : ℕ) : 2 * m + 3 ≤ 2 ^ (e0 m + 6) := by
  rcases Nat.lt_or_ge (llog m) 2 with hL | hL
  · have hm := small_of_llog (by omega : llog m ≤ 1)
    have h64 : 2 ^ 6 ≤ 2 ^ (e0 m + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h64
    omega
  · set c := Nat.clog 2 m with hc
    have hmc : m ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) m
    have hm5 : 5 ≤ m := by
      have := lt_of_llog (m := m) (L := llog m - 1) (by omega)
      have h4 : 4 ≤ 2 ^ (2 ^ (llog m - 1)) := by
        have : 2 ^ 2 ≤ 2 ^ (2 ^ (llog m - 1)) := Nat.pow_le_pow_right (by norm_num)
          (by
            have : 2 ^ 1 ≤ 2 ^ (llog m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            simpa using this)
        simpa using this
      omega
    have hc1 : 1 ≤ c := by
      rw [hc]
      exact Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
    have hcm : 2 ^ (c - 1) < m := by
      by_contra h
      push Not at h
      have : Nat.clog 2 m ≤ c - 1 := Nat.clog_le_of_le_pow h
      omega
    have hLc : llog m ≤ c := by
      show Nat.clog 2 c ≤ c
      exact Paper2.Unit4Shell.KofFront.clog_le_self c
    -- c ≤ e0 m + 4
    have hce : c ≤ e0 m + 4 := by
      have hprod : (c - 4) * (llog m - 1) ≤ m := by
        rcases Nat.lt_or_ge c 7 with hc7 | hc7
        · have hLc3 : llog m ≤ 3 := by
            show Nat.clog 2 c ≤ 3
            exact Nat.clog_le_of_le_pow (by
              have : c ≤ 8 := by omega
              simpa using this)
          have : (c - 4) * (llog m - 1) ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
          omega
        · have h1 : (c - 4) * (llog m - 1) ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
          have h2 := Paper2.AEth.sq_le_two_pow_pred c hc7
          omega
      have : c - 4 ≤ m / (llog m - 1) := (Nat.le_div_iff_mul_le (by omega)).2 hprod
      unfold e0
      omega
    have hpc : 2 * m + 3 ≤ 2 ^ (c + 2) := by
      have h2c : 5 ≤ 2 ^ c := by omega
      rw [pow_add]
      omega
    exact hpc.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **Every cut request fits in half of the decider tape.** For EVERY CNF `F` (valid or not),
the a-eth-owner-3 cut request satisfies `cutLen F ≤ 2^(e0 |encode F| + 7)`, hence `2 · cutLen F ≤ TL |encode F|`. -/
theorem cutLen_fit (F : EncodedCNF.Formula) :
    Paper2.AEth3.cutLen F ≤ 2 ^ (e0 (EncodedCNF.encode F).length + 7) := by
  rw [Paper2.AEth3.cutLen_eq]
  set m := (EncodedCNF.encode F).length
  have h1 := lin_fit m
  have h2 := expLen_fit F.variables m (Paper2.AEth.encode_length_ge F)
  have h6 : 2 ^ (e0 m + 6) = 4 * 2 ^ (e0 m + 4) := by rw [pow_add, pow_add]; ring
  have h7 : 2 ^ (e0 m + 7) = 8 * 2 ^ (e0 m + 4) := by rw [pow_add, pow_add]; ring
  omega

theorem cutLen_le_TL (F : EncodedCNF.Formula) :
    2 * Paper2.AEth3.cutLen F ≤ TL (EncodedCNF.encode F).length := by
  have h := cutLen_fit F
  have h8 : TL (EncodedCNF.encode F).length =
      2 * 2 ^ (e0 (EncodedCNF.encode F).length + 7) := by
    unfold TL
    rw [pow_succ]
    ring
  omega

/-- **The decider tape is subexponential.** -/
theorem TL_subexp : Subexp TL := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
  refine ⟨256, 0, 2 ^ (2 ^ (K + 1)), fun m hm => ?_⟩
  have hKl : K + 1 ≤ llog m := le_llog hm
  have hKpos : 0 < K := by
    have : (0 : ℝ) < 1 / ε := by positivity
    exact_mod_cast (lt_trans this hK)
  have hq : e0 m ≤ m / K := Nat.div_le_div_left (by omega) hKpos
  have hqR : (e0 m : ℝ) ≤ ε * m := by
    have h1 : ((m / K : ℕ) : ℝ) ≤ (m : ℝ) / K := Nat.cast_div_le
    have h2 : (m : ℝ) / K ≤ ε * m := by
      have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
      rw [div_le_iff₀ hKR]
      have h3 : 1 < ε * K := by
        have := hK
        rw [div_lt_iff₀ hε] at this
        linarith
      have hm0 : (0 : ℝ) ≤ m := by positivity
      nlinarith
    calc (e0 m : ℝ) ≤ ((m / K : ℕ) : ℝ) := by exact_mod_cast hq
      _ ≤ (m : ℝ) / K := h1
      _ ≤ ε * m := h2
  have hR : ((2 ^ e0 m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * m) := by
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hqR
  have hN : 2 ^ e0 m ≤ ⌈(2 : ℝ) ^ (ε * m)⌉₊ := by
    have := le_trans hR (Nat.le_ceil _)
    exact_mod_cast this
  unfold TL
  rw [pow_add]
  simp only [pow_zero, mul_one]
  norm_num
  omega

/-! ## The length machine -/

theorem one_step {α : Type*} {f : α → α} {a b : α} (h : f a = b) : f^[1] a = b := by
  rw [Function.iterate_one]
  exact h

namespace Pred

inductive PL
  | q1 | q2 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 2
abbrev Control := Option Bool × Unit

def program : PL → TM2.Stmt (fun _ : Stack => Bool) PL Control
  | .q1 => .pop 0 setBit (.goto fun _ => PL.q2)
  | .q2 => moveStmt 0 1 .q2 .done
  | .done => .halt

/-- `1^L ↦ 1^(L-1)` (input stack `0`, output stack `1`). -/
def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (1 : Stack) PL.q1 ((none, ()) : Control) program

theorem outputs (L : ℕ) :
    machine.OutputsWithin (List.replicate L true) (List.replicate (L - 1) true) (L + 3) := by
  let S0 : Stack → List Bool := fun j => if j = 0 then List.replicate L true else []
  have e1 : advance program ⟨some PL.q1, ((none, ()) : Control), S0⟩ =
      ⟨some PL.q2, ((List.replicate L true).head?, ()), Function.update S0 0 (List.replicate (L - 1) true)⟩ := by
    simp [advance, TM2.step, TM2.stepAux, program, setBit, S0, List.tail_replicate]
  set S1 := Function.update S0 0 (List.replicate (L - 1) true) with hS1
  have e2 := move_loop program (0 : Stack) 1 PL.q2 PL.done (by decide) rfl
    (List.replicate (L - 1) true) S1 (List.replicate L true).head? () (by simp [hS1])
  set S2 := Function.update (Function.update S1 1 ((List.replicate (L - 1) true).reverse ++ S1 1)) 0 []
    with hS2
  have e3 := halt_step program PL.done rfl (none, ()) S2
  have hrun := iter_chain (iter_chain (one_step e1) e2)
    (one_step e3)
  have hraw : rawInit (0 : Stack) PL.q1 ((none, ()) : Control) (List.replicate L true) =
      ⟨some PL.q1, (none, ()), S0⟩ := rfl
  have key : ∀ n, (advance program)^[n] (rawInit (0 : Stack) PL.q1 ((none, ()) : Control)
      (List.replicate L true)) = ⟨none, (none, ()), S2⟩ → n ≤ L + 3 →
      machine.OutputsWithin (List.replicate L true) (List.replicate (L - 1) true) (L + 3) := by
    intro n hn hle
    refine outputsWithin_of_raw_run (0 : Stack) (1 : Stack) PL.q1 ((none, ()) : Control)
      program _ _ n _ hle (by rw [hn]) (by rw [hn]; simp [hS2, hS1, S0])
  rw [← hraw] at hrun
  refine key _ hrun ?_
  simp only [List.length_replicate]
  omega

end Pred

namespace Plus8

inductive QL
  | q1 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 1
abbrev Control := Option Bool × Unit

def program : QL → TM2.Stmt (fun _ : Stack => Bool) QL Control
  | .q1 => pushTrues 0 8 (.goto fun _ => QL.done)
  | .done => .halt

/-- `1^e ↦ 1^(e+8)`. -/
def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) QL.q1 ((none, ()) : Control) program

theorem outputs (e : ℕ) :
    machine.OutputsWithin (List.replicate e true) (List.replicate (e + 8) true) 2 := by
  let S0 : Stack → List Bool := fun j => if j = 0 then List.replicate e true else []
  have e1 : advance program ⟨some QL.q1, ((none, ()) : Control), S0⟩ =
      ⟨some QL.done, ((none, ()) : Control),
        Function.update S0 0 (List.replicate 8 true ++ S0 0)⟩ := by
    simp only [advance, TM2.step, program, Option.getD_some]
    rw [stepAux_pushTrues]
    simp [TM2.stepAux]
  set S1 := Function.update S0 0 (List.replicate 8 true ++ S0 0) with hS1
  have e2 := halt_step program QL.done rfl (none, ()) S1
  have hrun := iter_chain (one_step e1)
    (one_step e2)
  have hraw : rawInit (0 : Stack) QL.q1 ((none, ()) : Control) (List.replicate e true) =
      ⟨some QL.q1, (none, ()), S0⟩ := rfl
  rw [← hraw] at hrun
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) QL.q1 ((none, ()) : Control)
    program _ _ 2 2 le_rfl (by rw [hrun]) ?_
  rw [hrun]
  simp only [hS1, Function.update_self]
  rw [Nat.add_comm e 8, List.replicate_add]
  simp [S0]

end Plus8

/-- `1^m ↦ 1^(llog m - 1)`. -/
def llogPred : BitMachine.Machine :=
  BitMachineComposition.composition loglogMachine Pred.machine

/-- **THE fixed length machine** `1^m ↦ 1^(TL m)`. -/
def TLMachine : BitMachine.Machine :=
  BitMachineComposition.composition WrapDup.machine
    (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine llogPred)
      (BitMachineComposition.composition Swap.machine
        (BitMachineComposition.composition DivFloor.machine
          (BitMachineComposition.composition Plus8.machine MatrixUnaryPower.machine))))

/-- The explicit constant of the polynomial part of the clock. -/
def BT : ℕ := 2 * UnaryBinaryEncoding.coefficient + 4000

/-- The explicit clock of the length machine. -/
def TLtime (m : ℕ) : ℕ := BT * (m + 1) ^ 2 + 20 * TL m

theorem e0_le (m : ℕ) : e0 m ≤ m := Nat.div_le_self m _

/-- **The length machine is correct and charged.** -/
theorem TLMachine_outputs (m : ℕ) :
    TLMachine.OutputsWithin (List.replicate m true) (List.replicate (TL m) true) (TLtime m) := by
  set C1 := Nat.clog 2 m with hC1
  set Q := llog m - 1 with hQdef
  set F4 : List Bool := [false, false, false, false] with hF4
  have h2 := WrapDup.machine_outputs m
  have hout : WrapDup.out m = EncodedComplexity.pair (List.replicate m true)
      (EncodedComplexity.pair (List.replicate m true) F4) := by
    simp [WrapDup.out, EncodedComplexity.pair, hF4]
  rw [hout] at h2
  have hlp := BitMachineComposition.composition_outputsWithin loglogMachine Pred.machine
    (loglog_outputs m) (Pred.outputs (llog m))
  have h3 := Paper2.Unit4Shell.PairMap.machine_outputs (M := llogPred)
    (List.replicate m true) (List.replicate Q true)
    (EncodedComplexity.pair (List.replicate m true) F4) _ hlp
  have h4 := Swap.machine_outputs (List.replicate Q true) (List.replicate m true) F4
  rw [← DivFloor.packedInput_eq m Q] at h4
  have h5 := DivFloor.outputs m Q
  have h6 := Plus8.outputs (m / Q)
  have h7 := MatrixUnaryPower.outputs (List.replicate (m / Q + 8) true)
  rw [List.length_replicate] at h7
  have hC := BitMachineComposition.composition_outputsWithin _ _ h2
    (BitMachineComposition.composition_outputsWithin _ _ h3
      (BitMachineComposition.composition_outputsWithin _ _ h4
        (BitMachineComposition.composition_outputsWithin _ _ h5
          (BitMachineComposition.composition_outputsWithin _ _ h6 h7))))
  have hE : 2 ^ (m / Q + 8) = TL m := rfl
  rw [hE] at hC
  apply BitMachine.outputsWithin_mono _ hC
  have hin := DivFloor.packedInput_length m Q
  rw [hin]
  simp only [List.length_replicate, EncodedComplexity.pair_length, hF4, List.length_cons,
    List.length_nil]
  have hC1m : C1 ≤ m := Paper2.Unit4Shell.KofFront.clog_le_self m
  have hLm : llog m ≤ m := llog_le m
  have hQm : Q ≤ m := by omega
  have hqm : m / Q ≤ m := Nat.div_le_self m Q
  have hq2 : m / Q + 8 < 2 ^ (m / Q + 8) := Nat.lt_two_pow_self
  rw [hE] at hq2
  have hsq : (C1 + 1) ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm1 : m + 1 ≤ (m + 1) ^ 2 := by nlinarith
  have hU := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 6) hsq
  unfold TLtime BT
  nlinarith

/-- **The R20 `lenPoly` shape.** -/
theorem TLtime_poly (m : ℕ) : TLtime m ≤ (BT + 20) * (m + TL m + 1) ^ 2 := by
  unfold TLtime
  have h1 : (m + 1) ^ 2 ≤ (m + TL m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : TL m ≤ (m + TL m + 1) ^ 2 :=
    le_trans (by omega) (Nat.le_self_pow two_ne_zero _)
  nlinarith

end Paper2.AEth4

end

#print axioms Paper2.AEth4.expExp_fit
#print axioms Paper2.AEth4.expLen_fit
#print axioms Paper2.AEth4.lin_fit
#print axioms Paper2.AEth4.cutLen_fit
#print axioms Paper2.AEth4.cutLen_le_TL
#print axioms Paper2.AEth4.TL_subexp
#print axioms Paper2.AEth4.Pred.outputs
#print axioms Paper2.AEth4.Plus8.outputs
#print axioms Paper2.AEth4.TLMachine_outputs
#print axioms Paper2.AEth4.TLtime_poly
