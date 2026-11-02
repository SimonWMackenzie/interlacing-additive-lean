import Paper2.CodeBranchAdapter
import Paper2.ResetReachedBound
import Paper2.CodeDrawResultHandler
import Paper2.CodeAdminResultJoin
import Mathlib.Tactic

/-! Reset clocks at actually consumed draw-result safe points. -/

namespace Paper2.CodeResultReset

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

noncomputable section

abbrev Stack := CodeInterpreterReset.Stack

/-- The branch adapter's final bank never enlarges a reset-cleared cell.
Header 1 is the only nonempty cleared cell it retains, and it is unchanged. -/
theorem branch_cleared_le (base : CodeBranchAdapter.BaseControl)
    (S : Stack → List Bool) (n out : List Bool)
    (hn : S (CodeBranchAdapter.h 1) = n)
    (i a b : Nat) (f s t : Code) (rest : List Bool)
    (k : Stack) (hk : ¬ CodeInterpreterReset.keep k) :
    ((CodeBranchAdapter.final base S n out i a b f s t rest).stk k).length ≤
      (S k).length := by
  rcases k with k | k
  · rcases k with j | j
    · fin_cases j <;>
        simp_all [CodeBranchAdapter.final, CodeBranchAdapter.framedBank,
          CodeInterpreterReset.keep]
    · rfl
  · rcases k with j | j
    · fin_cases j <;>
        simp_all [CodeBranchAdapter.final, CodeBranchAdapter.framedBank,
          CodeBranchAdapter.h, CodeInterpreterReset.keep]
    · exact False.elim (hk (by simp [CodeInterpreterReset.keep]))

theorem branch_clock_le (base : CodeBranchAdapter.BaseControl)
    (S : Stack → List Bool) (n out : List Bool)
    (hn : S (CodeBranchAdapter.h 1) = n)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    CodeInterpreterReset.clock
      (CodeBranchAdapter.final base S n out i a b f s t rest).stk ≤
    CodeInterpreterReset.clock S := by
  apply ResetReachedBound.safe_point_clock_le
  intro k hk
  exact branch_cleared_le base S n out hn i a b f s t rest k hk

theorem branch_result_clock_le (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (a b : Nat) (f s t : Code) (rest out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (i : Nat) :
    let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
      (BranchSelection.inputWord f s t rest)
      (List.replicate D true) (List.replicate a true)
      (List.replicate b true) out F
    CodeInterpreterReset.clock
      (CodeBranchAdapter.final result.var result.stk (List.replicate D true)
        out i a b f s t rest).stk ≤
      CodeInterpreterReset.clock result.stk := by
  intro result
  have hn : result.stk (CodeBranchAdapter.h 1) = List.replicate D true := by
    rfl
  exact branch_clock_le result.var result.stk (List.replicate D true)
    out hn i a b f s t rest

/-- The accepted ticket/bit handler modifies only the kept accumulated
output and the now-consumed ticket bank, which becomes empty. -/
theorem handler_cleared_le (saved : CodeDrawResultHandler.Saved)
    (S : Stack → List Bool) (newOutput : List Bool)
    (k : Stack) (hk : ¬ CodeInterpreterReset.keep k) :
    ((CodeDrawResultHandler.framed saved S
      (CodeDrawOutput.cfg none none [] newOutput)).stk k).length ≤
      (S k).length := by
  by_cases hi : ∃ j : Fin 2, CodeDrawResultHandler.outputSlot j = k
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j
    · change ((EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
          CodeDrawResultHandler.outputSlot S
          (CodeDrawOutput.cfg none none [] newOutput).stk)
            (CodeDrawResultHandler.outputSlot 0)).length ≤
        (S (CodeDrawResultHandler.outputSlot 0)).length
      rw [EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_at]
      simp [CodeDrawOutput.cfg, CodeDrawOutput.bank]
    · exact False.elim (hk (by simp [CodeDrawResultHandler.outputSlot,
        CodeHeaderDraw.output, CodeInterpreterReset.keep]))
  · rw [CodeDrawResultHandler.framed]
    simp only [EthInapproximability.CurrentPaper.BitMachineStackEmbedding.cfg,
      EthInapproximability.CurrentPaper.BitMachineStackEmbedding.stackCfg]
    rw [EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside
      _ _ _ _ hi]

theorem handler_clock_le (saved : CodeDrawResultHandler.Saved)
    (S : Stack → List Bool) (newOutput : List Bool) :
    CodeInterpreterReset.clock
      (CodeDrawResultHandler.framed saved S
        (CodeDrawOutput.cfg none none [] newOutput)).stk ≤
      CodeInterpreterReset.clock S := by
  apply ResetReachedBound.safe_point_clock_le
  intro k hk
  exact handler_cleared_le saved S newOutput k hk

/-- This is the exact `resultCfg (framed ...)` bank returned by the frozen
admin/result join for accepted ticket and bit heads. The saved status remains
in the finite control; reset receives that actual control as its flag. -/
theorem admin_handler_clock_le (saved : CodeDrawResultHandler.Saved)
    (S : Stack → List Bool) (newOutput : List Bool) :
    CodeInterpreterReset.clock
      (CodeAdminResultJoin.resultCfg
        (CodeDrawResultHandler.framed saved S
          (CodeDrawOutput.cfg none none [] newOutput))).stk ≤
      CodeInterpreterReset.clock S := by
  simpa [CodeAdminResultJoin.resultCfg,
    EthInapproximability.CurrentPaper.BitMachineInline.cfg] using
    handler_clock_le saved S newOutput

theorem admin_handler_reset_run (saved : CodeDrawResultHandler.Saved)
    (S : Stack → List Bool) (newOutput : List Bool) :
    let e := CodeAdminResultJoin.resultCfg
      (CodeDrawResultHandler.framed saved S
        (CodeDrawOutput.cfg none none [] newOutput))
    ((advance (CodeInterpreterReset.program
      (Flag := CodeAdminResultJoin.Control)))^[CodeInterpreterReset.clock e.stk])
        (CodeInterpreterReset.initial e.var e.stk) =
      CodeInterpreterReset.final e.var e.stk := by
  intro e
  exact CodeInterpreterReset.reset_run e.var e.stk

/-- The reached encoded branch draw, the successful branch adapter, and the
subsequent physical reset all share the same concrete bank. The reset clock
is bounded by the draw's public/code cap because every cell it clears has
only shrunk after the branch handler. The actual sampler flag is carried in
`branchFinal.var`, not reinitialized by a fixed handoff. -/
theorem encoded_branch_safe_reset (D a b B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q)
    (f s t : Code) (rest out : List Bool) :
    ∃ td F tb,
      td ≤ ResetReachedBound.drawClock (.branch3 D a b f s t) B R ∧
      CodeHeaderDraw.run td
        (CodeHeaderDraw.start
          (encodeCode (.branch3 D a b f s t) ++ rest) out
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        CodeHeaderDraw.resultCfg D B R N hB tape .branch3
          (BranchSelection.inputWord f s t rest)
          (List.replicate D true) (List.replicate a true)
          (List.replicate b true) out F ∧
      let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F
      let branchFinal := CodeBranchAdapter.final result.var result.stk
        (List.replicate D true) out q.val a b f s t rest
      tb ≤ 70 *
        (q.val+a+b+(BranchSelection.inputWord f s t rest).length+1) ∧
      CodeBranchAdapter.run tb
        ⟨some (.inr .route),
          (((.first, none), ChildSelect.idle .first), (result.var, none)),
          result.stk⟩ = branchFinal ∧
      CodeInterpreterReset.clock branchFinal.stk ≤
        ResetReachedBound.publicResetCap (.branch3 D a b f s t) B R ∧
      ((advance (CodeInterpreterReset.program
        (Flag := CodeBranchAdapter.Control)))^[
          CodeInterpreterReset.clock branchFinal.stk])
          (CodeInterpreterReset.initial branchFinal.var branchFinal.stk) =
        CodeInterpreterReset.final branchFinal.var branchFinal.stk := by
  let c : Code := .branch3 D a b f s t
  have hc : CodeHeaderDraw.DrawHead c := by
    dsimp [c]
    exact .branch3 D a b f s t hD
  have hb : Nat.clog 2 (CodeHeaderDraw.denominator c) ≤ B := by
    simpa [c, CodeHeaderDraw.denominator] using hB
  obtain ⟨td,F,htd,hrd,hclock⟩ :=
    ResetReachedBound.reached_result_clock c hc B R N hb tape rest out
  let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
    (BranchSelection.inputWord f s t rest)
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) out F
  have hrd' : CodeHeaderDraw.run td
      (CodeHeaderDraw.start (encodeCode c ++ rest) out
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
      result := by
    simpa [result, c, CodeHeaderDraw.denominator,
      CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail,
      CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
      CodeHeaderMachine.headerB, BranchSelection.inputWord] using hrd
  have hclock' : CodeInterpreterReset.clock result.stk ≤
      ResetReachedBound.publicResetCap c B R := by
    simpa [result, c, CodeHeaderDraw.denominator,
      CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail,
      CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
      CodeHeaderMachine.headerB, BranchSelection.inputWord] using hclock
  obtain ⟨tb,htb,hrb⟩ := CodeBranchAdapter.branch_from_result
    D B R N hB tape q hq a b f s t rest out F
  let branchFinal := CodeBranchAdapter.final result.var result.stk
    (List.replicate D true) out q.val a b f s t rest
  have hsmall := branch_result_clock_le D B R N hB tape a b
    f s t rest out F q.val
  have hreset := CodeInterpreterReset.reset_run branchFinal.var branchFinal.stk
  refine ⟨td,F,tb,?_,?_,?_,?_,?_,?_⟩
  · simpa [c] using htd
  · simpa [c] using hrd'
  · exact htb
  · simpa [result, branchFinal] using hrb
  · exact hsmall.trans hclock'
  · exact hreset

/-! A single fixed controller carries the branch adapter's entire finite
control, including the loaded success bit, into the physical reset. -/

abbrev JoinedControl := CodeInterpreterReset.Control CodeBranchAdapter.Control
abbrev JoinedLabel := CodeBranchAdapter.Label ⊕ CodeInterpreterReset.Label
abbrev JoinedConfig := TM2.Cfg (fun _ : Stack => Bool) JoinedLabel JoinedControl

noncomputable def joinedProgram : JoinedLabel →
    TM2.Stmt (fun _ : Stack => Bool) JoinedLabel JoinedControl
  | .inl l =>
      BitMachineInline.stmt Sum.inl (fun v => (v,none)) Prod.fst
        (some (.inr (.inl 0))) (CodeBranchAdapter.program l)
  | .inr l =>
      BitMachineInline.stmt Sum.inr id id none
        (CodeInterpreterReset.program (Flag := CodeBranchAdapter.Control) l)

def joinedRun (n : Nat) (c : JoinedConfig) :=
  ((advance joinedProgram)^[n]) c

def branchCfg (c : CodeBranchAdapter.Config) : JoinedConfig :=
  BitMachineInline.cfg Sum.inl (fun v => (v,none))
    (some (.inr (.inl 0))) c

def resetCfg (c : CodeInterpreterReset.Config CodeBranchAdapter.Control) :
    JoinedConfig :=
  BitMachineInline.cfg Sum.inr id none c

private theorem branch_read :
    Function.LeftInverse (Prod.fst : JoinedControl → CodeBranchAdapter.Control)
      (fun v : CodeBranchAdapter.Control => (v,(none : Option Bool))) := by
  intro v
  rfl

private theorem reset_read : Function.LeftInverse (id : JoinedControl → JoinedControl) id := by
  intro v
  rfl

theorem branch_to_reset (c d : CodeBranchAdapter.Config) (n : Nat)
    (hr : CodeBranchAdapter.run n c = d) (hd : d.l = none) :
    ∃ u ≤ n, joinedRun u (branchCfg c) =
      resetCfg (CodeInterpreterReset.initial d.var d.stk) := by
  have hh : (((advance CodeBranchAdapter.program)^[n]) c).l = none := by
    change (CodeBranchAdapter.run n c).l = none
    rw [hr]
    exact hd
  obtain ⟨u,hu,hru⟩ := BitMachineInline.outputs Sum.inl
    (fun v => (v,none)) Prod.fst branch_read
    (some (.inr (.inl 0))) CodeBranchAdapter.program joinedProgram
    (by intro l; rfl) c n hh
  refine ⟨u,hu,?_⟩
  change joinedRun u (branchCfg c) = branchCfg (CodeBranchAdapter.run n c) at hru
  rw [hr] at hru
  simpa [branchCfg, resetCfg, CodeInterpreterReset.initial,
    BitMachineInline.cfg, hd] using hru

theorem reset_to_end (c d : CodeInterpreterReset.Config CodeBranchAdapter.Control)
    (n : Nat)
    (hr : ((advance (CodeInterpreterReset.program
      (Flag := CodeBranchAdapter.Control)))^[n]) c = d)
    (hd : d.l = none) :
    ∃ u ≤ n, joinedRun u (resetCfg c) = resetCfg d := by
  have hh : (((advance (CodeInterpreterReset.program
      (Flag := CodeBranchAdapter.Control)))^[n]) c).l = none := by
    rw [hr]
    exact hd
  obtain ⟨u,hu,hru⟩ := BitMachineInline.outputs Sum.inr id id
    reset_read none (CodeInterpreterReset.program (Flag := CodeBranchAdapter.Control))
    joinedProgram (by intro l; rfl) c n hh
  refine ⟨u,hu,?_⟩
  change joinedRun u (resetCfg c) =
    resetCfg (((advance (CodeInterpreterReset.program
      (Flag := CodeBranchAdapter.Control)))^[n]) c) at hru
  rw [hr] at hru
  exact hru

theorem branch_then_reset (c d : CodeBranchAdapter.Config) (n : Nat)
    (hr : CodeBranchAdapter.run n c = d) (hd : d.l = none) :
    ∃ u ≤ n + CodeInterpreterReset.clock d.stk,
      joinedRun u (branchCfg c) =
        resetCfg (CodeInterpreterReset.final d.var d.stk) := by
  obtain ⟨u,hu,hbu⟩ := branch_to_reset c d n hr hd
  have hreset := CodeInterpreterReset.reset_run d.var d.stk
  have hhalt : (CodeInterpreterReset.final d.var d.stk).l = none := rfl
  obtain ⟨v,hv,hrv⟩ := reset_to_end
    (CodeInterpreterReset.initial d.var d.stk)
    (CodeInterpreterReset.final d.var d.stk)
    (CodeInterpreterReset.clock d.stk) hreset hhalt
  refine ⟨v+u,by omega,?_⟩
  have hadd : joinedRun (v+u) (branchCfg c) =
      joinedRun v (joinedRun u (branchCfg c)) := by
    simp [joinedRun, Function.iterate_add_apply]
  rw [hadd,hbu,hrv]

/-- A single fixed branch/reset machine starts at the frozen loaded/header
result. Its finite control keeps the data-dependent success bit intact, and
the subsequent reset runs only after the selector consumed ticket and cuts. -/
theorem branch_result_joined_reset (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q)
    (a b : Nat) (f s t : Code) (rest out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
      (BranchSelection.inputWord f s t rest)
      (List.replicate D true) (List.replicate a true)
      (List.replicate b true) out F
    let start : CodeBranchAdapter.Config :=
      ⟨some (.inr .route),
        (((.first, none), ChildSelect.idle .first), (result.var, none)),
        result.stk⟩
    let branchFinal := CodeBranchAdapter.final result.var result.stk
      (List.replicate D true) out q.val a b f s t rest
    ∃ clock ≤ 70 *
      (q.val+a+b+(BranchSelection.inputWord f s t rest).length+1) +
        CodeInterpreterReset.clock result.stk,
      joinedRun clock (branchCfg start) =
        resetCfg (CodeInterpreterReset.final branchFinal.var branchFinal.stk) := by
  intro result start branchFinal
  obtain ⟨tb,htb,hrb⟩ := CodeBranchAdapter.branch_from_result
    D B R N hB tape q hq a b f s t rest out F
  have hrun : CodeBranchAdapter.run tb start = branchFinal := by
    simpa [start, result, branchFinal] using hrb
  have hclock := branch_result_clock_le D B R N hB tape
    a b f s t rest out F q.val
  have hhalt : branchFinal.l = none := rfl
  obtain ⟨u,hu,hr⟩ := branch_then_reset start branchFinal tb hrun hhalt
  refine ⟨u, ?_, hr⟩
  have hclock' : CodeInterpreterReset.clock branchFinal.stk ≤
      CodeInterpreterReset.clock result.stk := by
    simpa [result, branchFinal] using hclock
  omega

/-- Both phases are reached: the encoded draw from its physical input, then
one fixed status-preserving branch/reset controller from that exact result.
The reset bound is public/code-dependent and includes residual log work. -/
theorem reached_branch_joined_reset (D a b B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q)
    (f s t : Code) (rest out : List Bool) :
    ∃ td F clock,
      td ≤ ResetReachedBound.drawClock (.branch3 D a b f s t) B R ∧
      CodeHeaderDraw.run td
        (CodeHeaderDraw.start
          (encodeCode (.branch3 D a b f s t) ++ rest) out
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        CodeHeaderDraw.resultCfg D B R N hB tape .branch3
          (BranchSelection.inputWord f s t rest)
          (List.replicate D true) (List.replicate a true)
          (List.replicate b true) out F ∧
      let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f s t rest)
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F
      let start : CodeBranchAdapter.Config :=
        ⟨some (.inr .route),
          (((.first, none), ChildSelect.idle .first), (result.var, none)),
          result.stk⟩
      let branchFinal := CodeBranchAdapter.final result.var result.stk
        (List.replicate D true) out q.val a b f s t rest
      clock ≤ 70 *
        (q.val+a+b+(BranchSelection.inputWord f s t rest).length+1) +
          ResetReachedBound.publicResetCap (.branch3 D a b f s t) B R ∧
      joinedRun clock (branchCfg start) =
        resetCfg (CodeInterpreterReset.final branchFinal.var branchFinal.stk) := by
  let c : Code := .branch3 D a b f s t
  have hc : CodeHeaderDraw.DrawHead c := by
    dsimp [c]
    exact .branch3 D a b f s t hD
  have hb : Nat.clog 2 (CodeHeaderDraw.denominator c) ≤ B := by
    simpa [c, CodeHeaderDraw.denominator] using hB
  obtain ⟨td,F,htd,hrd,hdrawClock⟩ :=
    ResetReachedBound.reached_result_clock c hc B R N hb tape rest out
  let result := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
    (BranchSelection.inputWord f s t rest)
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) out F
  have hdrawRun : CodeHeaderDraw.run td
      (CodeHeaderDraw.start (encodeCode c ++ rest) out
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) = result := by
    simpa [result, c, CodeHeaderDraw.denominator,
      CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail,
      CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
      CodeHeaderMachine.headerB, BranchSelection.inputWord] using hrd
  have hdrawCap : CodeInterpreterReset.clock result.stk ≤
      ResetReachedBound.publicResetCap c B R := by
    simpa [result, c, CodeHeaderDraw.denominator,
      CodeHeaderMachine.headerKind, CodeHeaderMachine.headerTail,
      CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
      CodeHeaderMachine.headerB, BranchSelection.inputWord] using hdrawClock
  obtain ⟨clock,hclock,hrun⟩ := branch_result_joined_reset
    D B R N hB tape q hq a b f s t rest out F
  refine ⟨td,F,clock,?_,?_,?_,?_⟩
  · simpa [c] using htd
  · simpa [c] using hdrawRun
  · have hcap := hclock.trans (Nat.add_le_add_left hdrawCap _)
    simpa [c, result] using hcap
  · simpa [result] using hrun

theorem joined_final_status (base : CodeBranchAdapter.BaseControl)
    (S : Stack → List Bool) (n out : List Bool)
    (i a b : Nat) (f s t : Code) (rest : List Bool) :
    let bfinal := CodeBranchAdapter.final base S n out i a b f s t rest
    (resetCfg (CodeInterpreterReset.final bfinal.var bfinal.stk)).var.1.2.1.1.2.2 =
      base.1.2.2 := by
  rfl

/-- Reached ticket/bit handler endpoints have the same public reset cap as
the draw result: the only changed clear cell is the consumed ticket. The
arbitrary `newOutput` is on a kept cell, so this also covers the exact
successful outputs supplied by `CodeAdminResultJoin`. -/
theorem reached_handler_clock (c : Code) (hc : CodeHeaderDraw.DrawHead c)
    (B R N : Nat) (hB : Nat.clog 2 (CodeHeaderDraw.denominator c) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (rest out newOutput : List Bool) :
    ∃ td F,
      td ≤ ResetReachedBound.drawClock c B R ∧
      CodeHeaderDraw.run td
        (CodeHeaderDraw.start (encodeCode c ++ rest) out
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        CodeHeaderDraw.resultCfg (CodeHeaderDraw.denominator c) B R N hB tape
          (CodeHeaderMachine.headerKind c)
          (CodeHeaderMachine.headerTail c rest)
          (CodeHeaderMachine.headerN c)
          (CodeHeaderMachine.headerA c)
          (CodeHeaderMachine.headerB c) out F ∧
      let d := CodeAdminDraw.drawResult
        (CodeHeaderDraw.denominator c) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c rest)
        (CodeHeaderMachine.headerN c)
        (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) out F
      CodeInterpreterReset.clock
        (CodeAdminResultJoin.resultCfg
          (CodeDrawResultHandler.framed d.var d.stk
            (CodeDrawOutput.cfg none none [] newOutput))).stk ≤
        ResetReachedBound.publicResetCap c B R := by
  obtain ⟨td,F,htd,hrd,hcap⟩ :=
    ResetReachedBound.reached_result_clock c hc B R N hB tape rest out
  refine ⟨td,F,htd,hrd,?_⟩
  let d := CodeAdminDraw.drawResult
    (CodeHeaderDraw.denominator c) B R N hB tape
    (CodeHeaderMachine.headerKind c)
    (CodeHeaderMachine.headerTail c rest)
    (CodeHeaderMachine.headerN c)
    (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) out F
  have hhandler := admin_handler_clock_le d.var d.stk newOutput
  have hbank : d.stk =
      (CodeHeaderDraw.resultCfg (CodeHeaderDraw.denominator c) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c rest)
        (CodeHeaderMachine.headerN c)
        (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) out F).stk := rfl
  simpa [d, hbank] using hhandler.trans (by simpa [hbank] using hcap)

#print axioms reached_branch_joined_reset
#print axioms reached_handler_clock

end
end Paper2.CodeResultReset
