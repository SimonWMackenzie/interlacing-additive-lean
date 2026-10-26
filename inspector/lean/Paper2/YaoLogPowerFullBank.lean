import Paper2.YaoCountFullBank

/-! Exact preserved input banks of the two checked components inside the
joined edge-count-to-padded-count controller. -/

namespace Paper2.YaoParameterBank

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoParameterLoader

private theorem logCopy_start_rawInit (e : ℕ) :
    ETHParameterScaleMachineLogCopy.start (List.replicate e true) =
      rawInit (.inl (0 : Fin 1)) (.inl .scan)
        (ETHParameterScaleMachineLogCopy.copyControl none)
        (List.replicate e true) := by
  let q := List.replicate e true
  let S : ETHParameterScaleMachineLogCopy.Stack → List Bool :=
    fun k => if k = .inl (0 : Fin 1) then q else []
  have hs : ∀ p : Fin 3,
      (BitMachineCopy.cfg (some .scan) none q [] []).stk p =
        S (ETHParameterScaleMachineLogCopy.copyStack p) := by
    intro p
    fin_cases p <;> simp [S, ETHParameterScaleMachineLogCopy.copyStack,
      BitMachineCopy.cfg]
  have hb : BitMachineStackEmbedding.bank ETHParameterScaleMachineLogCopy.copyStack
      (fun _ => []) (BitMachineCopy.cfg (some .scan) none q [] []).stk = S := by
    funext k
    by_cases h : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = k
    · obtain ⟨p,rfl⟩ := h
      rw [BitMachineStackEmbedding.bank_at]
      exact hs p
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ k h]
      have hne : k ≠ (.inl (0 : Fin 1) : ETHParameterScaleMachineLogCopy.Stack) := by
        intro he
        exact h ⟨0, by simpa [ETHParameterScaleMachineLogCopy.copyStack] using he.symm⟩
      simp [S, hne]
  change (⟨some (.inl .scan), ETHParameterScaleMachineLogCopy.copyControl none,
      BitMachineStackEmbedding.bank ETHParameterScaleMachineLogCopy.copyStack
        (fun _ => []) (BitMachineCopy.cfg (some .scan) none q [] []).stk⟩ :
      ETHParameterScaleMachineLogCopy.Config) =
    ⟨some (.inl .scan), ETHParameterScaleMachineLogCopy.copyControl none, S⟩
  rw [hb]

/-- At the exact halt of the source-preserving physical log-copy machine,
its input bank still contains the original unary edge count and its output
bank contains the computed unary ceiling logarithm. -/
theorem logCopy_full_bank (e : ℕ) :
    ∃ steps ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2,
      let M := ETHParameterScaleMachineLogCopy.machine
      let c := M.run steps (M.init (List.replicate e true))
      c.l = none ∧ c.stk M.input = List.replicate e true ∧
        c.stk M.output = List.replicate (Nat.clog 2 e) true := by
  obtain ⟨steps,c,hs,hr,hhalt,hout⟩ :=
    ETHParameterScaleMachineLogCopy.copied_log_run e
  refine ⟨steps,hs,?_⟩
  let M := ETHParameterScaleMachineLogCopy.machine
  let ek := Fintype.equivFin ETHParameterScaleMachineLogCopy.Stack
  let el := Fintype.equivFin ETHParameterScaleMachineLogCopy.Label
  let ev := Fintype.equivFin ETHParameterScaleMachineLogCopy.Control
  have hi : M.init (List.replicate e true) = renameCfg ek el ev
      (ETHParameterScaleMachineLogCopy.start (List.replicate e true)) := by
    change (ofFinite (.inl (0 : Fin 1))
      (ETHParameterScaleMachineLogCopy.logStack
        ETHParameterScaleMachineLogCopy.logMachine.output)
      (.inl .scan) (ETHParameterScaleMachineLogCopy.copyControl none)
      ETHParameterScaleMachineLogCopy.program).init _ = _
    rw [ofFinite_init, logCopy_start_rawInit]
  have he : M.run steps (M.init (List.replicate e true)) =
      renameCfg ek el ev
        (ETHParameterScaleMachineLogCopy.afterLog (List.replicate e true) c) := by
    rw [hi]
    have hrun := ofFinite_run (.inl (0 : Fin 1))
      (ETHParameterScaleMachineLogCopy.logStack
        ETHParameterScaleMachineLogCopy.logMachine.output)
      (.inl .scan) (ETHParameterScaleMachineLogCopy.copyControl none)
      ETHParameterScaleMachineLogCopy.program
      (ETHParameterScaleMachineLogCopy.start (List.replicate e true)) steps
    change ((advance ETHParameterScaleMachineLogCopy.program)^[steps])
      (ETHParameterScaleMachineLogCopy.start (List.replicate e true)) = _ at hr
    rw [hr] at hrun
    simpa only [M, ETHParameterScaleMachineLogCopy.machine,
      ek, el, ev] using hrun
  change (M.run steps (M.init (List.replicate e true))).l = none ∧
    (M.run steps (M.init (List.replicate e true))).stk M.input =
      List.replicate e true ∧
    (M.run steps (M.init (List.replicate e true))).stk M.output =
      List.replicate (Nat.clog 2 e) true
  rw [he]
  constructor
  · simp [renameCfg, ETHParameterScaleMachineLogCopy.afterLog,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hhalt]
    rfl
  constructor
  · have hk : M.input = ek (.inl (0 : Fin 1)) := rfl
    rw [hk]
    simp only [renameCfg, Equiv.symm_apply_apply]
    exact ETHParameterScaleMachineLogCopy.afterLog_source e c
  · have hk : M.output = ek
        (ETHParameterScaleMachineLogCopy.logStack
          ETHParameterScaleMachineLogCopy.logMachine.output) := rfl
    rw [hk]
    simp only [renameCfg, Equiv.symm_apply_apply]
    rw [ETHParameterScaleMachineLogCopy.afterLog_output]
    exact hout

theorem power_full_bank (b : ℕ) :
    ∃ steps ≤ 4*2^b + 5*b + 7,
      let M := MatrixUnaryPower.machine
      let c := M.run steps (M.init (List.replicate b true))
      c.l = none ∧ c.stk M.input = List.replicate b true ∧
        c.stk M.output = List.replicate (2^b) true := by
  obtain ⟨steps,hs,hr⟩ := MatrixUnaryPower.unary_power_run b
  refine ⟨steps,hs,?_⟩
  let M := MatrixUnaryPower.machine
  let ek := Fintype.equivFin MatrixUnaryPower.Stack
  let el := Fintype.equivFin MatrixUnaryPower.Label
  let ev := Fintype.equivFin MatrixUnaryPower.Control
  have hi : M.init (List.replicate b true) = renameCfg ek el ev
      (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none)
        [] [] [] (List.replicate b true)) := by
    change (ofFinite (.inr () : MatrixUnaryPower.Stack)
      (.inl 0) (.inr false) ((false,false),none)
      MatrixUnaryPower.program).init _ = _
    rw [ofFinite_init]
    congr 1
    unfold rawInit MatrixUnaryPower.cfg MatrixUnaryPower.contents
    congr 1
    funext k
    rcases k with k | k
    · fin_cases k <;> rfl
    · cases k; rfl
  have he : M.run steps (M.init (List.replicate b true)) =
      renameCfg ek el ev
        (MatrixUnaryPower.cfg none ((false,false),none)
          (List.replicate (2^b) true) [] [] (List.replicate b true)) := by
    rw [hi]
    have hrun := ofFinite_run (.inr () : MatrixUnaryPower.Stack)
      (.inl 0) (.inr false) ((false,false),none)
      MatrixUnaryPower.program
      (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none)
        [] [] [] (List.replicate b true)) steps
    change ((advance MatrixUnaryPower.program)^[steps]) _ = _ at hr
    rw [hr] at hrun
    simpa only [M, MatrixUnaryPower.machine, ek, el, ev] using hrun
  change (M.run steps (M.init (List.replicate b true))).l = none ∧
    (M.run steps (M.init (List.replicate b true))).stk M.input =
      List.replicate b true ∧
    (M.run steps (M.init (List.replicate b true))).stk M.output =
      List.replicate (2^b) true
  rw [he]
  constructor
  · rfl
  constructor
  · have hk : M.input = ek (.inr ()) := rfl
    rw [hk]
    simp only [renameCfg, Equiv.symm_apply_apply]
    rfl
  · have hk : M.output = ek (.inl (0 : Fin 3)) := rfl
    rw [hk]
    simp only [renameCfg, Equiv.symm_apply_apply]
    rfl

theorem logCopy_halt_preserves_e (e n : ℕ)
    (hhalt : (ETHParameterScaleMachineLogCopy.machine.run n
      (ETHParameterScaleMachineLogCopy.machine.init
        (List.replicate e true))).l = none) :
    (ETHParameterScaleMachineLogCopy.machine.run n
      (ETHParameterScaleMachineLogCopy.machine.init
        (List.replicate e true))).stk
      ETHParameterScaleMachineLogCopy.machine.input =
        List.replicate e true := by
  obtain ⟨steps,_,hsHalt,hsInput,_⟩ := logCopy_full_bank e
  have he := equal_halting_runs ETHParameterScaleMachineLogCopy.machine
    (ETHParameterScaleMachineLogCopy.machine.init (List.replicate e true))
    n steps hhalt hsHalt
  rw [he]
  exact hsInput

theorem power_halt_preserves_b (b n : ℕ)
    (hhalt : (MatrixUnaryPower.machine.run n
      (MatrixUnaryPower.machine.init (List.replicate b true))).l = none) :
    (MatrixUnaryPower.machine.run n
      (MatrixUnaryPower.machine.init (List.replicate b true))).stk
      MatrixUnaryPower.machine.input = List.replicate b true := by
  obtain ⟨steps,_,hsHalt,hsInput,_⟩ := power_full_bank b
  have he := equal_halting_runs MatrixUnaryPower.machine
    (MatrixUnaryPower.machine.init (List.replicate b true))
    n steps hhalt hsHalt
  rw [he]
  exact hsInput

private theorem logCopy_input_ne_output :
    ETHParameterScaleMachineLogCopy.machine.input ≠
      ETHParameterScaleMachineLogCopy.machine.output := by
  intro h
  have hh := (Fintype.equivFin ETHParameterScaleMachineLogCopy.Stack).injective h
  exact Sum.inl_ne_inr hh

/-- Before machine-numbering conversion, the exact physical composite
configuration retains edge count, computed logarithm and computed padded
count on three distinct banks. The logarithm is the *input bank* preserved
by the power machine; no extra copy premise is used. -/
theorem logPower_raw_full_banks (e : ℕ) :
    ∃ (a b : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 ∧
      b ≤ 16*2^(Nat.clog 2 e) ∧
      let A := ETHParameterScaleMachineLogCopy.machine
      let B := MatrixUnaryPower.machine
      let ca := A.run a (A.init (List.replicate e true))
      let cb := B.run b (B.init (List.replicate (Nat.clog 2 e) true))
      let final := ((advance (program A B))^[
        a + 2*Nat.clog 2 e+2+b])
          (rawInit (.inl A.input) (.inl A.start)
            (A.initial,B.initial,none) (List.replicate e true))
      final = rightCfg A B ca.var
        (Function.update ca.stk A.output []) cb ∧
      final.l = none ∧
      final.stk (.inl A.input) = List.replicate e true ∧
      final.stk (.inr (.inl B.input)) =
        List.replicate (Nat.clog 2 e) true ∧
      final.stk (.inr (.inl B.output)) =
        List.replicate (2^(Nat.clog 2 e)) true := by
  let A := ETHParameterScaleMachineLogCopy.machine
  let B := MatrixUnaryPower.machine
  obtain ⟨a,b,ha,hb,hAhalt,_,hBhalt,hBout,hrun⟩ :=
    composition_full_run A B
      (ETHParameterScaleMachineLogCopy.outputs e)
      (MatrixUnaryPower.outputs (List.replicate (Nat.clog 2 e) true))
  have hrun' : ((advance (program A B))^[a + 2*Nat.clog 2 e+2+b])
      (rawInit (.inl A.input) (.inl A.start)
        (A.initial,B.initial,none) (List.replicate e true)) =
      rightCfg A B (A.run a (A.init (List.replicate e true))).var
        (Function.update (A.run a (A.init (List.replicate e true))).stk A.output [])
        (B.run b (B.init (List.replicate (Nat.clog 2 e) true))) := by
    simpa only [List.length_replicate] using hrun
  refine ⟨a,b,ha,?_,?_⟩
  · simpa only [List.length_replicate] using hb
  · dsimp only
    refine ⟨hrun', ?_, ?_, ?_, ?_⟩
    · rw [hrun']
      exact rightCfg_halt A B _ _ _ hBhalt
    · rw [hrun', rightCfg_left_bank]
      rw [Function.update_of_ne logCopy_input_ne_output]
      exact logCopy_halt_preserves_e e a hAhalt
    · rw [hrun', rightCfg_right_bank]
      exact power_halt_preserves_b (Nat.clog 2 e) b hBhalt
    · rw [hrun', rightCfg_right_bank]
      simpa only [List.length_replicate] using hBout

#print axioms logPower_raw_full_banks

/-- Numbered-stack version of the same one-program run: the original edge
count, computed `b`, and padded count `H` occupy three distinct machine
cells at halt. This is the bank interface consumed by the later selector
count composition. -/
theorem logPower_numbered_full_banks (e : ℕ) :
    ∃ steps ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*Nat.clog 2 e+2 + 16*2^(Nat.clog 2 e),
      let A := ETHParameterScaleMachineLogCopy.machine
      let B := MatrixUnaryPower.machine
      let M := composition A B
      let ek := Fintype.equivFin (BitMachineComposition.Stack A B)
      let c := M.run steps (M.init (List.replicate e true))
      c.l = none ∧
        c.stk (ek (.inl A.input)) = List.replicate e true ∧
        c.stk (ek (.inr (.inl B.input))) =
          List.replicate (Nat.clog 2 e) true ∧
        c.stk M.output = List.replicate (2^(Nat.clog 2 e)) true := by
  let A := ETHParameterScaleMachineLogCopy.machine
  let B := MatrixUnaryPower.machine
  obtain ⟨a,b,ha,hb,hrun,hh,hE,hBits,hH⟩ := logPower_raw_full_banks e
  let steps := a + 2*Nat.clog 2 e+2+b
  refine ⟨steps, by dsimp [steps]; omega, ?_⟩
  let ek := Fintype.equivFin (BitMachineComposition.Stack A B)
  let el := Fintype.equivFin (BitMachineComposition.Label A B)
  let ev := Fintype.equivFin (BitMachineComposition.Control A B)
  let raw := ((advance (program A B))^[steps])
      (rawInit (.inl A.input) (.inl A.start)
        (A.initial,B.initial,none) (List.replicate e true))
  have he : (composition A B).run steps
      ((composition A B).init (List.replicate e true)) =
      renameCfg ek el ev raw :=
    composition_numbered_run A B (List.replicate e true) steps
  change ((composition A B).run steps
      ((composition A B).init (List.replicate e true))).l = none ∧
    ((composition A B).run steps
      ((composition A B).init (List.replicate e true))).stk
      (ek (.inl A.input)) = List.replicate e true ∧
    ((composition A B).run steps
      ((composition A B).init (List.replicate e true))).stk
      (ek (.inr (.inl B.input))) = List.replicate (Nat.clog 2 e) true ∧
    ((composition A B).run steps
      ((composition A B).init (List.replicate e true))).stk
      (composition A B).output = List.replicate (2^(Nat.clog 2 e)) true
  rw [he]
  have hkey : (composition A B).output = ek (.inr (.inl B.output)) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change raw.l.map el = none
    rw [show raw.l = none from hh]
    rfl
  · simpa only [renameCfg, Equiv.symm_apply_apply, raw, steps] using hE
  · simpa only [renameCfg, Equiv.symm_apply_apply, raw, steps] using hBits
  · rw [hkey]
    simpa only [renameCfg, Equiv.symm_apply_apply, raw, steps] using hH

#print axioms logPower_numbered_full_banks

theorem logPower_halt_preserves_edge (e n : ℕ)
    (hhalt : (logPowerMachine.run n
      (logPowerMachine.init (List.replicate e true))).l = none) :
    let A := ETHParameterScaleMachineLogCopy.machine
    let B := MatrixUnaryPower.machine
    let ek := Fintype.equivFin (BitMachineComposition.Stack A B)
    (logPowerMachine.run n
      (logPowerMachine.init (List.replicate e true))).stk
        (ek (.inl A.input)) = List.replicate e true := by
  obtain ⟨steps,_,hsHalt,hsEdge,_,_⟩ := logPower_numbered_full_banks e
  have he := equal_halting_runs logPowerMachine
    (logPowerMachine.init (List.replicate e true))
    n steps hhalt hsHalt
  dsimp only
  rw [he]
  exact hsEdge

theorem logPower_halt_preserves_bits (e n : ℕ)
    (hhalt : (logPowerMachine.run n
      (logPowerMachine.init (List.replicate e true))).l = none) :
    let A := ETHParameterScaleMachineLogCopy.machine
    let B := MatrixUnaryPower.machine
    let ek := Fintype.equivFin (BitMachineComposition.Stack A B)
    (logPowerMachine.run n
      (logPowerMachine.init (List.replicate e true))).stk
        (ek (.inr (.inl B.input))) = List.replicate (Nat.clog 2 e) true := by
  obtain ⟨steps,_,hsHalt,_,hsBits,_⟩ := logPower_numbered_full_banks e
  have he := equal_halting_runs logPowerMachine
    (logPowerMachine.init (List.replicate e true))
    n steps hhalt hsHalt
  dsimp only
  rw [he]
  exact hsBits

#print axioms logCopy_full_bank
#print axioms power_full_bank

end Paper2.YaoParameterBank
