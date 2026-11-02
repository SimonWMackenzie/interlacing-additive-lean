import Paper2.DrawCoefficients
import Paper2.SamplerLoopDraw
import Paper2.SamplerRejectionIdentity
import Paper2.SamplerBitWidthMachine
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! One fixed controller producing the physical draw count
`N = drawCap s q₁ q₂ w Q p k mX mY` and the rejection cap
`R = rejectionAttemptCap N = 13 + clog₂ N` from the nine raw unary counts
`s,q₁,q₂,w,Q,p,k,mX,mY` (Fin 32 cells 0..8, every other cell blank).

Phases, sequenced by `BitMachineRawSequence` and charged:
1. `DrawCoefficients.program` (A,B,C,D at cells 9..12);
2. `SamplerAffineInit.program` (active pair r=p, c=1 at 13/14);
3. `SamplerLoopDraw.program` (unary-k affine loop, parity dispatch, N at 22);
4. `ETHParameterScaleMachineLogCopy.program`, embedded with its source cell
   aliased to cell 22 (source-preserving copy, then physical clog);
5. fixed unary 13 written to cell 23;
6. source-preserving copy of the log output onto cell 23.

No coefficient, pair value, parity, N, log or R is supplied to the bank. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.SamplerNRProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

abbrev LogStack := ETHParameterScaleMachineLogCopy.Stack
abbrev Stack := Fin 32 ⊕ LogStack

def core : Fin 32 ↪ Stack := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

def logSlot : LogStack → Stack
  | .inl _ => .inl 22
  | .inr y => .inr (.inr y)

theorem logSlot_injective : Function.Injective logSlot := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subsingleton.elim a b)
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b =>
      have := Sum.inr_injective (Sum.inr_injective h)
      exact congrArg Sum.inr this

def logSlots : LogStack ↪ Stack := ⟨logSlot, logSlot_injective⟩

noncomputable def logOut : Stack :=
  logSlots (ETHParameterScaleMachineLogCopy.logStack
    ETHParameterScaleMachineLogCopy.logMachine.output)

def appendSlot : Fin 3 → Stack
  | 0 => .inr (.inr (.inl ETHParameterScaleMachineLogCopy.logMachine.output))
  | 1 => .inl 23
  | _ => .inl 24

theorem appendSlot_injective : Function.Injective appendSlot := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [appendSlot]

def appendSlots : Fin 3 ↪ Stack := ⟨appendSlot, appendSlot_injective⟩

theorem logOut_eq : logOut = appendSlots 0 := rfl

/-! ### The six phase programs and their sequence -/

def coeffProgram := fun l => stackStmt core (DrawCoefficients.program l)
def initProgram := fun l => stackStmt core (SamplerAffineInit.program l)
def loopProgram := fun l => stackStmt core (SamplerLoopDraw.program l)
noncomputable def logProgram :=
  fun l => stackStmt logSlots (ETHParameterScaleMachineLogCopy.program l)
def thirteenProgram := SourceClauseFixedUnary.program (.inl 23 : Stack) 13
def appendProgram := MatrixStage4ScalarPreparationOps.copyProgram appendSlots

def coeffStart : DrawCoefficients.Label := .copy 0 .scan
def initStart : SamplerAffineInit.Label := .inl .scan
def initControl0 : SamplerAffineInit.Control := (none, ())

def p12 := BitMachineRawSequence.program coeffProgram initProgram initStart
  DrawCoefficients.initialControl initControl0
def c12 := (DrawCoefficients.initialControl, initControl0)
def p123 := BitMachineRawSequence.program p12 loopProgram
  (SamplerLoopDraw.startLabel false) c12 SamplerLoopDraw.startControl
def c123 := (c12, SamplerLoopDraw.startControl)
noncomputable def p1234 := BitMachineRawSequence.program p123 logProgram
  (.inl .scan) c123 (ETHParameterScaleMachineLogCopy.copyControl none)
noncomputable def c1234 :=
  (c123, ETHParameterScaleMachineLogCopy.copyControl none)
noncomputable def p12345 := BitMachineRawSequence.program p1234
  thirteenProgram (0 : SourceClauseFixedUnary.Label 13) c1234 ()
noncomputable def c12345 := (c1234, ())
noncomputable def program := BitMachineRawSequence.program p12345
  appendProgram .scan c12345 (none : Option Bool)

def startLabel :=
  BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label)
    (BitMachineRawSequence.leftLabel (LB := SourceClauseFixedUnary.Label 13)
      (BitMachineRawSequence.leftLabel
        (LB := ETHParameterScaleMachineLogCopy.Label)
        (BitMachineRawSequence.leftLabel (LB := SamplerLoopDraw.Label)
          (BitMachineRawSequence.leftLabel (LB := SamplerAffineInit.Label)
            coeffStart))))
noncomputable def startControl := (c12345, (none : Option Bool))

def initialBank (s q₁ q₂ w Q p k mX mY : Nat) : Stack → List Bool :=
  Sum.elim (DrawCoefficients.initialBank s q₁ q₂ w Q p k mX mY) (fun _ => [])

/-! ### Embedding facts -/

theorem bank_core (X Z : Fin 32 → List Bool) (Y : LogStack → List Bool) :
    bank core (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext j
  cases j with
  | inl j => exact bank_at core _ Z j
  | inr j => exact bank_outside core _ Z (.inr j) (by rintro ⟨k, hk⟩; cases hk)

theorem core_run {L V : Type*} (P : L → TM2.Stmt (fun _ : Fin 32 => Bool) L V)
    (l : L) (v v' : V) (X X' : Fin 32 → List Bool) (Y : LogStack → List Bool)
    (t : Nat)
    (h : ((advance P)^[t]) (⟨some l, v, X⟩ : TM2.Cfg (fun _ : Fin 32 => Bool) L V) =
      ⟨none, v', X'⟩) :
    ((advance (fun l => stackStmt core (P l)))^[t])
      (⟨some l, v, Sum.elim X Y⟩ : TM2.Cfg (fun _ : Stack => Bool) L V) =
      ⟨none, v', Sum.elim X' Y⟩ := by
  have hr := BitMachineStackRun.run core (Sum.elim X Y) P
    (⟨some l, v, X⟩ : TM2.Cfg (fun _ : Fin 32 => Bool) L V) t
  rw [h] at hr
  simpa only [stackCfg, bank_core] using hr

/-! ### Bank facts along the run -/

abbrev A (s q₁ q₂ w Q : Nat) := SamplerAffineSource.coeffA s q₁ q₂ w Q
abbrev B (s q₁ q₂ w Q : Nat) := SamplerAffineSource.coeffB s q₁ q₂ w Q
abbrev C (s q₁ q₂ w Q : Nat) := SamplerAffineSource.coeffC s q₁ q₂ w Q
abbrev D (s q₁ q₂ w Q : Nat) := SamplerAffineSource.coeffD s q₁ q₂ w Q

def bankInit (s q₁ q₂ w Q p k mX mY : Nat) : Fin 32 → List Bool :=
  SamplerAffineInit.finalBank
    (DrawCoefficients.finalBank s q₁ q₂ w Q p k mX mY) p

theorem bankInit_at (s q₁ q₂ w Q p k mX mY : Nat) (j : Fin 32) :
    bankInit s q₁ q₂ w Q p k mX mY j =
      if j = 14 then [true] else if j = 13 then List.replicate p true else
        DrawCoefficients.finalBank s q₁ q₂ w Q p k mX mY j := by
  simp only [bankInit, SamplerAffineInit.finalBank, Function.update_apply]

theorem init_invariant (s q₁ q₂ w Q p k mX mY : Nat) :
    SamplerAffineRound.Invariant false (bankInit s q₁ q₂ w Q p k mX mY)
      (A s q₁ q₂ w Q) (B s q₁ q₂ w Q) (C s q₁ q₂ w Q) (D s q₁ q₂ w Q)
      p 1 0 0 := by
  constructor <;>
    simp [bankInit_at, SamplerAffineRound.row, SamplerAffineRound.col,
      DrawCoefficients.finalBank, DrawCoefficients.unary,
      SamplerAffineSource.coeffA, SamplerAffineSource.coeffB,
      SamplerAffineSource.coeffC, SamplerAffineSource.coeffD,
      DrawCoefficients.A, DrawCoefficients.B, DrawCoefficients.C,
      DrawCoefficients.D]

theorem bankInit_low (s q₁ q₂ w Q p k mX mY : Nat) :
    ∀ j : Fin 32, (j.val < 6 ∨ j.val = 7 ∨ j.val = 8) →
      bankInit s q₁ q₂ w Q p k mX mY j =
        DrawCoefficients.initialBank s q₁ q₂ w Q p k mX mY j := by
  intro j hj
  fin_cases j <;> first
    | (simp at hj; done)
    | simp [bankInit_at, DrawCoefficients.finalBank, DrawCoefficients.initialBank]

/-- The loop's active pair after `k` rounds. -/
def pair (s q₁ q₂ w Q p k : Nat) : Nat × Nat :=
  SamplerAffineLoop.values (A s q₁ q₂ w Q) (B s q₁ q₂ w Q)
    (C s q₁ q₂ w Q) (D s q₁ q₂ w Q) k p 1

theorem pair_N (s q₁ q₂ w Q p k mX mY : Nat) :
    1 + mY * (pair s q₁ q₂ w Q p k).2 + mX * (pair s q₁ q₂ w Q p k).1 =
      RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY :=
  SamplerAffineSource.exact_N s q₁ q₂ w Q p k mX mY

def N (s q₁ q₂ w Q p k mX mY : Nat) : Nat :=
  RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY

def R (s q₁ q₂ w Q p k mX mY : Nat) : Nat :=
  Paper2.rejectionAttemptCap (N s q₁ q₂ w Q p k mX mY)

theorem N_pos (s q₁ q₂ w Q p k mX mY : Nat) : 0 < N s q₁ q₂ w Q p k mX mY := by
  rw [N, ← pair_N]; omega

theorem R_eq (s q₁ q₂ w Q p k mX mY : Nat) :
    R s q₁ q₂ w Q p k mX mY = 13 + Nat.clog 2 (N s q₁ q₂ w Q p k mX mY) :=
  SamplerRejectionIdentity.rejection_eq _ (N_pos s q₁ q₂ w Q p k mX mY)

/-! ### Clock -/

def loopClock (s q₁ q₂ w Q p k mX mY : Nat) : Nat :=
  SamplerAffineLoop.loopCap (A s q₁ q₂ w Q) (B s q₁ q₂ w Q)
    (C s q₁ q₂ w Q) (D s q₁ q₂ w Q) k p 1 0 0 + 1 +
    SamplerLoopDraw.drawTime (pair s q₁ q₂ w Q p k).1
      (pair s q₁ q₂ w Q p k).2 mX mY

def logClock (n : Nat) : Nat :=
  2*n+2 + (UnaryBinaryEncoding.coefficient+6)*(n+1)^2

def clock (s q₁ q₂ w Q p k mX mY : Nat) : Nat :=
  DrawCoefficients.clock s q₁ q₂ w Q + (2*p+5) +
    loopClock s q₁ q₂ w Q p k mX mY +
    logClock (N s q₁ q₂ w Q p k mX mY) + 14 +
    (2 * Nat.clog 2 (N s q₁ q₂ w Q p k mX mY) + 2) + 5

/-! ### The run -/

theorem log_bank (U : Fin 32 → List Bool) (n : Nat)
    (h22 : U 22 = List.replicate n true) :
    bank logSlots (Sum.elim U (fun _ => []))
      (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk =
      Sum.elim U (fun _ => []) := by
  apply bank_eq_self
  intro k
  rw [SamplerBitWidthMachine.log_start_word]
  cases k with
  | inl k =>
    have hk : (Sum.inl k : LogStack) = .inl 0 := by
      rw [Subsingleton.elim k 0]
    rw [if_pos hk]
    exact h22.symm
  | inr k =>
    rw [if_neg (by simp)]
    rfl

theorem logSlots_outside (j : Fin 32) (hj : j ≠ 22) :
    ¬ ∃ k, logSlots k = (.inl j : Stack) := by
  rintro ⟨k, hk⟩
  cases k with
  | inl k =>
    apply hj
    exact (Sum.inl_injective hk).symm
  | inr k => cases hk

theorem run (s q₁ q₂ w Q p k mX mY : Nat) :
    ∃ (t : Nat) (F : Stack → List Bool),
      t ≤ clock s q₁ q₂ w Q p k mX mY ∧
      ((advance program)^[t])
        (⟨some startLabel, startControl,
          initialBank s q₁ q₂ w Q p k mX mY⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (c12345, none), F⟩ ∧
      F (.inl 23) = List.replicate (R s q₁ q₂ w Q p k mX mY) true ∧
      F (.inl 22) = List.replicate (N s q₁ q₂ w Q p k mX mY) true ∧
      (∀ j : Fin 32, (j.val < 6 ∨ j.val = 7 ∨ j.val = 8) →
        F (.inl j) = DrawCoefficients.initialBank s q₁ q₂ w Q p k mX mY j) := by
  let Y : LogStack → List Bool := fun _ => []
  let U0 := DrawCoefficients.initialBank s q₁ q₂ w Q p k mX mY
  let U1 := DrawCoefficients.finalBank s q₁ q₂ w Q p k mX mY
  let U2 := bankInit s q₁ q₂ w Q p k mX mY
  let n := N s q₁ q₂ w Q p k mX mY
  -- phase 1: coefficients
  obtain ⟨t1, ht1, h1⟩ := DrawCoefficients.whole_run s q₁ q₂ w Q p k mX mY
  have h1' := core_run DrawCoefficients.program coeffStart
    DrawCoefficients.initialControl DrawCoefficients.initialControl
    U0 U1 Y t1 h1
  -- phase 2: affine initialisation
  have hU1 : ∀ j : Fin 32, U1 j = DrawCoefficients.finalBank s q₁ q₂ w Q p k mX mY j :=
    fun _ => rfl
  obtain ⟨t2, ht2, h2⟩ := SamplerAffineInit.run U1 p
    (by simp [U1, DrawCoefficients.finalBank, DrawCoefficients.unary])
    (by simp [U1, DrawCoefficients.finalBank])
    (by simp [U1, DrawCoefficients.finalBank])
    (by simp [U1, DrawCoefficients.finalBank])
  have h2' := core_run SamplerAffineInit.program initStart initControl0
    initControl0 U1 (SamplerAffineInit.finalBank U1 p) Y t2 h2
  -- phase 3: loop, dispatch, draw count
  obtain ⟨t3, T, b', u', v', ht3, h3, hInv, hT6, hframe⟩ :=
    SamplerLoopDraw.run k false U2 (A s q₁ q₂ w Q) (B s q₁ q₂ w Q)
      (C s q₁ q₂ w Q) (D s q₁ q₂ w Q) p 1 0 0 mX mY
      (init_invariant s q₁ q₂ w Q p k mX mY)
      (by simp [U2, bankInit_at, DrawCoefficients.finalBank, DrawCoefficients.unary])
      (by simp [U2, bankInit_at, DrawCoefficients.finalBank, DrawCoefficients.unary])
      (by simp [U2, bankInit_at, DrawCoefficients.finalBank, DrawCoefficients.unary])
      (by simp [U2, bankInit_at, DrawCoefficients.finalBank])
      (by simp [U2, bankInit_at, DrawCoefficients.finalBank])
      (by simp [U2, bankInit_at, DrawCoefficients.finalBank])
  let U3 := SamplerDrawCount.finalBank T mY mX
    (pair s q₁ q₂ w Q p k).2 (pair s q₁ q₂ w Q p k).1
  have h3' := core_run SamplerLoopDraw.program (SamplerLoopDraw.startLabel false)
    SamplerLoopDraw.startControl
    (SamplerAffineLoop.endControl b', SamplerLoopDraw.drawControl)
    U2 U3 Y t3 h3
  have hU3_22 : U3 22 = List.replicate n true := by
    simp only [U3, SamplerDrawCount.finalBank, Function.update_self]
    rw [pair_N]
    rfl
  have hU3_frame : ∀ j : Fin 32, ¬ SamplerLoopDraw.Moving j → j ≠ 21 → j ≠ 22 →
      U3 j = U2 j := by
    intro j hj h21 h22
    simp only [U3, SamplerDrawCount.finalBank, Function.update_of_ne h21,
      Function.update_of_ne h22]
    exact hframe j hj
  have hU3_23 : U3 23 = [] := by
    rw [hU3_frame 23 (by simp [SamplerLoopDraw.Moving]) (by decide) (by decide)]
    simp [U2, bankInit_at, DrawCoefficients.finalBank]
  have hU3_24 : U3 24 = [] := by
    rw [hU3_frame 24 (by simp [SamplerLoopDraw.Moving]) (by decide) (by decide)]
    simp [U2, bankInit_at, DrawCoefficients.finalBank]
  -- phase 4: physical clog of the draw count, source aliased to cell 22
  obtain ⟨t4, c4, ht4, h4, hc4, ho4⟩ :=
    ETHParameterScaleMachineLogCopy.copied_log_run n
  let W3 : Stack → List Bool := Sum.elim U3 Y
  let W4 : Stack → List Bool := bank logSlots W3 (ETHParameterScaleMachineLogCopy.afterLog
    (List.replicate n true) c4).stk
  have h4' : ((advance logProgram)^[t4])
      (⟨some (.inl .scan), ETHParameterScaleMachineLogCopy.copyControl none, W3⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (ETHParameterScaleMachineLogCopy.afterLog
        (List.replicate n true) c4).var, W4⟩ := by
    have hr := BitMachineStackRun.run logSlots W3
      ETHParameterScaleMachineLogCopy.program
      (ETHParameterScaleMachineLogCopy.start (List.replicate n true)) t4
    change ((advance ETHParameterScaleMachineLogCopy.program)^[t4])
      (ETHParameterScaleMachineLogCopy.start (List.replicate n true)) = _ at h4
    rw [h4] at hr
    have hlabel : (ETHParameterScaleMachineLogCopy.afterLog
        (List.replicate n true) c4).l = none := by
      simp [ETHParameterScaleMachineLogCopy.afterLog,
        BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hc4]
    have hstart : bank logSlots W3
        (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk = W3 :=
      log_bank U3 n hU3_22
    have hl : (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).l =
        some (.inl .scan) := rfl
    have hv : (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).var =
        ETHParameterScaleMachineLogCopy.copyControl none := rfl
    simp only [stackCfg] at hr
    rw [hstart, hl, hv, hlabel] at hr
    exact hr
  have hW4_out : W4 logOut = List.replicate (Nat.clog 2 n) true := by
    change bank logSlots W3 _ (logSlots (ETHParameterScaleMachineLogCopy.logStack
      ETHParameterScaleMachineLogCopy.logMachine.output)) = _
    rw [bank_at, ETHParameterScaleMachineLogCopy.afterLog_output]
    exact ho4
  have hW4_core : ∀ j : Fin 32, j ≠ 22 → W4 (.inl j) = U3 j := by
    intro j hj
    exact bank_outside logSlots W3 _ _ (logSlots_outside j hj)
  have hW4_22 : W4 (.inl 22) = List.replicate n true := by
    change bank logSlots W3 _ (logSlots (.inl 0)) = _
    rw [bank_at]
    exact ETHParameterScaleMachineLogCopy.afterLog_source n c4
  -- phase 5: fixed unary thirteen at cell 23
  have h5 := SourceClauseFixedUnary.run (.inl 23 : Stack) W4 13
    (by rw [hW4_core 23 (by decide)]; exact hU3_23)
  let W5 := Function.update W4 (.inl 23 : Stack) (List.replicate 13 true)
  -- phase 6: append the log output to cell 23
  have h6 := MatrixStage4ScalarPreparationOps.copy_run appendSlots W5
    (by
      change W5 (.inl 24) = []
      simp only [W5, Function.update_of_ne (by decide : (.inl 24 : Stack) ≠ .inl 23)]
      rw [hW4_core 24 (by decide)]
      exact hU3_24)
  have hW5_out : W5 (appendSlots 0) = List.replicate (Nat.clog 2 n) true := by
    change W5 logOut = _
    simp only [W5, Function.update_of_ne (show logOut ≠ (.inl 23 : Stack) by
      simp [logOut, logSlots, logSlot, ETHParameterScaleMachineLogCopy.logStack])]
    exact hW4_out
  have hW5_23 : W5 (appendSlots 1) = List.replicate 13 true := by
    change W5 (.inl 23) = _
    simp only [W5, Function.update_self]
  rw [hW5_out, hW5_23, List.length_replicate] at h6
  let F := Function.update W5 (appendSlots 1)
    (List.replicate (Nat.clog 2 n) true ++ List.replicate 13 true)
  -- sequence the six phases
  obtain ⟨s12, hs12, r12⟩ := BitMachineRawSequence.runs coeffProgram initProgram
    coeffStart initStart DrawCoefficients.initialControl
    DrawCoefficients.initialControl initControl0 initControl0
    (Sum.elim U0 Y) (Sum.elim U1 Y) (Sum.elim U2 Y) t1 t2 h1' h2'
  obtain ⟨s123, hs123, r123⟩ := BitMachineRawSequence.runs p12 loopProgram
    (BitMachineRawSequence.leftLabel coeffStart)
    (SamplerLoopDraw.startLabel false) c12 c12
    SamplerLoopDraw.startControl
    (SamplerAffineLoop.endControl b', SamplerLoopDraw.drawControl)
    (Sum.elim U0 Y) (Sum.elim U2 Y) W3 s12 t3 r12 h3'
  obtain ⟨s1234, hs1234, r1234⟩ := BitMachineRawSequence.runs p123 logProgram
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel coeffStart))
    (.inl .scan) c123 (c12, (SamplerAffineLoop.endControl b', SamplerLoopDraw.drawControl))
    (ETHParameterScaleMachineLogCopy.copyControl none)
    (ETHParameterScaleMachineLogCopy.afterLog (List.replicate n true) c4).var
    (Sum.elim U0 Y) W3 W4 s123 t4 r123 h4'
  obtain ⟨s5, hs5, r5⟩ := BitMachineRawSequence.runs p1234 thirteenProgram
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel coeffStart)))
    (0 : SourceClauseFixedUnary.Label 13) c1234
    (c123, (ETHParameterScaleMachineLogCopy.afterLog (List.replicate n true) c4).var) () ()
    (Sum.elim U0 Y) W4 W5 s1234 (13+1) r1234 h5
  obtain ⟨s6, hs6, r6⟩ := BitMachineRawSequence.runs p12345 appendProgram
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel coeffStart))))
    .scan c12345 c12345 none none
    (Sum.elim U0 Y) W5 F s5 (2 * Nat.clog 2 n + 2) r5 h6
  have hlow := bankInit_low s q₁ q₂ w Q p k mX mY
  refine ⟨s6, F, ?_, ?_, ?_, ?_, ?_⟩
  · have ht3' : t3 ≤ loopClock s q₁ q₂ w Q p k mX mY := ht3
    have ht4' : t4 ≤ 2*(N s q₁ q₂ w Q p k mX mY)+2 +
        (UnaryBinaryEncoding.coefficient+6)*((N s q₁ q₂ w Q p k mX mY)+1)^2 := ht4
    have hs6' : s6 ≤ s5 + (2 * Nat.clog 2 (N s q₁ q₂ w Q p k mX mY) + 2) + 1 := hs6
    simp only [clock, logClock]
    omega
  · exact r6
  · change Function.update W5 (.inl 23 : Stack) _ (.inl 23) = _
    rw [Function.update_self, List.replicate_append_replicate, R_eq]
    congr 1
    show Nat.clog 2 (N s q₁ q₂ w Q p k mX mY) + 13 =
      13 + Nat.clog 2 (N s q₁ q₂ w Q p k mX mY)
    omega
  · change Function.update W5 (.inl 23 : Stack) _ (.inl 22) = _
    rw [Function.update_of_ne (by decide),
      show W5 (.inl 22) = W4 (.inl 22) from
        Function.update_of_ne (by decide) _ _]
    exact hW4_22
  · intro j hj
    have hv : j.val ≤ 8 ∧ j.val ≠ 6 := by omega
    have hne : ∀ m : Fin 32, 9 ≤ m.val → j ≠ m := by
      intro m hm h
      subst h
      omega
    have h23 : (.inl j : Stack) ≠ .inl 23 :=
      fun h => hne 23 (by decide) (Sum.inl_injective h)
    have hj22 : j ≠ 22 := hne 22 (by decide)
    have hj21 : j ≠ 21 := hne 21 (by decide)
    have hjm : ¬ SamplerLoopDraw.Moving j := by
      intro h
      rcases h with h | h | h | h | h
      · exact hv.2 (by rw [h]; rfl)
      · exact hne 13 (by decide) h
      · exact hne 14 (by decide) h
      · exact hne 15 (by decide) h
      · exact hne 16 (by decide) h
    change Function.update W5 (.inl 23 : Stack) _ (.inl j) = _
    rw [Function.update_of_ne h23,
      show W5 (.inl j) = W4 (.inl j) from Function.update_of_ne h23 _ _,
      hW4_core j hj22, hU3_frame j hjm hj21 hj22]
    exact hlow j hj

end

#print axioms run

end Paper2.SamplerNRProducer
