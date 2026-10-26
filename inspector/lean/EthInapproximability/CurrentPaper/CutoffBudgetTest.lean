import EthInapproximability.CurrentPaper.CutoffOutputDecoder
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# A charged cutoff-output comparison

Source: frozen v8 `05-iteration.tex`, success of a bounded cutoff run means
that its decoded output is at most the source budget. This six-stack program
first executes the literal output decoder, then the bounded binary-to-unary
comparison. Its statement starts from displayed physical stacks. Assembly
of those stacks by the outer clock remains separately charged.
-/

namespace EthInapproximability.CurrentPaper.CutoffBudgetTest

open Turing
open BitMachineEncoding BitMachineComposition BitMachineSubroutine BitMachineSubroutineRenaming

abbrev Stack := Fin 3 ⊕ Fin 3
abbrev Label := Fin 2 ⊕ ProtocolBoundedUnary.Label
abbrev Control := CutoffOutputDecoder.Control × ProtocolBoundedUnary.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def stackSwap : (Fin 4 ⊕ Fin 2) ≃ Stack where
  toFun := Sum.elim
    (fun i => if i = 0 then .inl 2 else if i = 1 then .inr 0 else if i = 2 then .inr 1 else .inr 2)
    (fun i => if i = 0 then .inl 0 else .inl 1)
  invFun := Sum.elim
    (fun i => if i = 0 then .inr 0 else if i = 1 then .inr 1 else .inl 0)
    (fun i => if i = 0 then .inl 1 else if i = 1 then .inl 2 else .inl 3)
  left_inv := by intro i; cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl
  right_inv := by intro i; cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl

def labelSwap : (ProtocolBoundedUnary.Label ⊕ Fin 2) ≃ Label := Equiv.sumComm _ _
def controlSwap : (ProtocolBoundedUnary.Control × CutoffOutputDecoder.Control) ≃ Control :=
  Equiv.prodComm _ _

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .zeroScan) (CutoffOutputDecoder.program l)
  | .inr l => renameStmt stackSwap labelSwap controlSwap
      (liftStmt none (ProtocolBoundedUnary.program l))

def start (input cap out : List Bool) : Config :=
  liftCfg (some .zeroScan) (none, false) ![cap, [], out]
    (CutoffOutputDecoder.cfg (some 0) (none, none) input [] [])

def comparison (v : CutoffOutputDecoder.Control) (input q cap out : List Bool) : Config :=
  renameCfg stackSwap labelSwap controlSwap
    (liftCfg none v ![input, []]
      (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) q cap [] out))

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem phase_eq (v : CutoffOutputDecoder.Control) (input q cap out : List Bool) :
    liftCfg (some ProtocolBoundedUnary.Label.zeroScan) (none, false) ![cap, [], out]
      (CutoffOutputDecoder.cfg none v input [] q) = comparison v input q cap out := by
  unfold comparison renameCfg liftCfg CutoffOutputDecoder.cfg ProtocolBoundedUnary.cfg
    ProtocolBoundedUnary.stackContents
  congr 1
  · funext i
    cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl

theorem decoder_phase (input cap out : List Bool) :
    ∃ t v, t ≤ input.length + 2 ∧
      run t (start input cap out) = comparison v (CutoffOutputDecoder.remainder input)
        (CutoffOutputDecoder.bits input) cap out := by
  obtain ⟨v, hr⟩ := CutoffOutputDecoder.decoder_run input [] (none, none)
  rw [List.append_nil] at hr
  have hh : (CutoffOutputDecoder.run
      (CutoffOutputDecoder.scans input + (CutoffOutputDecoder.bits input).length + 1)
      (CutoffOutputDecoder.cfg (some 0) (none, none) input [] [])).l = none := by
    rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := lift_outputs CutoffOutputDecoder.program program
    (some ProtocolBoundedUnary.Label.zeroScan) (fun _ => rfl) (none, false)
    ![cap, [], out] (CutoffOutputDecoder.cfg (some 0) (none, none) input [] [])
    (CutoffOutputDecoder.scans input + (CutoffOutputDecoder.bits input).length + 1) hh
  refine ⟨t, v, ht.trans (CutoffOutputDecoder.decoder_time input), ?_⟩
  change run t (start input cap out) = liftCfg _ _ _ (CutoffOutputDecoder.run _ _) at he
  rw [hr, phase_eq] at he
  exact he

theorem comparison_phase (v : CutoffOutputDecoder.Control) (input q cap out : List Bool) :
    ∃ t c, t ≤ (cap.length + 1) * (4 * q.length + 5) ∧
      run t (comparison v input q cap out) = c ∧ c.l = none ∧
      c.stk (.inr 2) = ProtocolBoundedUnary.result q cap out := by
  obtain ⟨bound, c, hb, hc, hh, ho⟩ := ProtocolBoundedUnary.bounded_run q cap out
  have hhalt : (ProtocolBoundedUnary.run bound
      (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) q cap [] out)).l = none := by
    rw [hc]; exact hh
  obtain ⟨t, ht, he⟩ := lift_outputs_renamed stackSwap labelSwap controlSwap
    ProtocolBoundedUnary.program program none (fun _ => rfl) v ![input, []]
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) q cap [] out) bound hhalt
  change run t (comparison v input q cap out) =
    renameCfg stackSwap labelSwap controlSwap
      (liftCfg none v ![input, []] (ProtocolBoundedUnary.run bound _)) at he
  rw [hc] at he
  refine ⟨t, _, ht.trans hb, he, ?_, ?_⟩
  · simp [renameCfg, liftCfg, hh]
  · simpa only [renameCfg, stackSwap, liftCfg, Sum.elim_inl] using ho

theorem bits_length_le (input : List Bool) :
    (CutoffOutputDecoder.bits input).length ≤ input.length := by
  have := CutoffOutputDecoder.decoder_time input
  have hs : 1 ≤ CutoffOutputDecoder.scans input := by
    induction input using CutoffOutputDecoder.bits.induct with
    | case1 a rest ih => simp only [CutoffOutputDecoder.scans]; omega
    | case2 input h =>
        cases input with
        | nil => decide
        | cons a tail => cases tail with
          | nil => exact Nat.le_refl 1
          | cons b tail => cases b with
            | false => exact (h a tail rfl).elim
            | true => exact Nat.le_refl 1
  omega

/-- Both computational phases are literal instructions of this one fixed
program. The returned first bit is the desired numerical comparison. -/
theorem test_run (input cap out : List Bool) :
    ∃ t c, t ≤ input.length + 2 + (cap.length + 1) * (4 * input.length + 5) ∧
      run t (start input cap out) = c ∧ c.l = none ∧
      c.stk (.inr 2) =
        decide (CutoffBitMachine.decodedNat input ≤ cap.length) ::
          (List.replicate (min (CutoffBitMachine.decodedNat input) cap.length) true ++ out) := by
  obtain ⟨s, v, hs, hdecode⟩ := decoder_phase input cap out
  obtain ⟨t, c, ht, hcompare, hh, ho⟩ := comparison_phase v
    (CutoffOutputDecoder.remainder input) (CutoffOutputDecoder.bits input) cap out
  refine ⟨s + t, c, ?_, ?_, hh, ?_⟩
  · have hlen := bits_length_le input
    nlinarith
  · change ((advance program)^[s + t]) _ = _
    rw [Nat.add_comm s t, Function.iterate_add_apply]
    change run t (run s _) = _
    rw [hdecode, hcompare]
  · simpa only [ProtocolBoundedUnary.result, CutoffOutputDecoder.bits_value] using ho

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inl 0 : Stack) (.inr 2) (.inl 0 : Label)
    ((none, none), (none, false)) program

noncomputable def encode (c : Config) : machine.Config :=
  renameCfg (Fintype.equivFin Stack) (Fintype.equivFin Label) (Fintype.equivFin Control) c

/-- The displayed program is literally a machine in the shared finite
Boolean-stack model. This is deliberately a loaded-state statement: the
outer caller must still supply the input and unary cap. -/
theorem machine_test_run (input cap out : List Bool) :
    ∃ t ≤ input.length + 2 + (cap.length + 1) * (4 * input.length + 5),
      (machine.run t (encode (start input cap out))).l = none ∧
      (machine.run t (encode (start input cap out))).stk machine.output =
        decide (CutoffBitMachine.decodedNat input ≤ cap.length) ::
          (List.replicate (min (CutoffBitMachine.decodedNat input) cap.length) true ++ out) := by
  obtain ⟨t, c, ht, hc, hh, ho⟩ := test_run input cap out
  have he := ofFinite_run (.inl 0 : Stack) (.inr 2) (.inl 0 : Label)
    ((none, none), (none, false)) program (start input cap out) t
  change machine.run t (encode (start input cap out)) = encode (run t (start input cap out)) at he
  rw [hc] at he
  refine ⟨t, ht, ?_, ?_⟩
  · rw [he]; simp only [encode, renameCfg, hh, Option.map_none]
  · rw [he]
    simp only [encode, renameCfg, machine, ofFinite]
    exact (congrArg c.stk ((Fintype.equivFin Stack).symm_apply_apply (.inr 2))).trans ho

end EthInapproximability.CurrentPaper.CutoffBudgetTest
