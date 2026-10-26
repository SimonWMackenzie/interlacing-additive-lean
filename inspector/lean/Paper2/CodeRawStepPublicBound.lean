import Paper2.CodeAdminBranchJoin
import Mathlib.Tactic

/-! Public polynomial clock for every actual raw arm of the joined one-step
code interpreter. The cap does not depend on a sampled index or parsed field. -/

namespace Paper2.CodeRawStepPublicBound

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorStateSize GeneratorPositive

noncomputable section

private theorem clog_le (D : Nat) : Nat.clog 2 D ≤ D := by
  rw [ExactParameterMachineLog.clog_eq_pred_bits_length]
  exact (UnaryBinaryEncoding.bits_length_le _).trans (Nat.sub_le D 1)

private theorem attempt_bound (D : Nat) :
    CappedLoop.Comparator.attemptBound D ≤ 40*(D+1)^2 := by
  have hl := clog_le D
  have hn : D-1 ≤ D := Nat.sub_le _ _
  calc
    CappedLoop.Comparator.attemptBound D ≤
        3*D+4+(2*D+2+(D+1)*(4*D+5))+(D+2*D+5) := by
      have hm : (D-1+1)*(4*Nat.clog 2 D+5) ≤
          (D+1)*(4*D+5) := Nat.mul_le_mul (by omega) (by omega)
      dsimp only [CappedLoop.Comparator.attemptBound]
      nlinarith [hm]
    _ ≤ 40*(D+1)^2 := by nlinarith

private theorem draw_bound (D B R : Nat) :
    TicketWordScratch.drawBound D B R ≤ 100*(D+B+R+2)^3 := by
  let K := D+B+R+2
  have hk : 2 ≤ K := by dsimp [K]; omega
  have hd : D ≤ K := by dsimp [K]; omega
  have hb : B ≤ K := by dsimp [K]; omega
  have hr : R ≤ K := by dsimp [K]; omega
  have hl : Nat.clog 2 D ≤ K := (clog_le D).trans hd
  have hdn : D-1 ≤ K := (Nat.sub_le _ _).trans hd
  have hbp : B-Nat.clog 2 D ≤ K := (Nat.sub_le _ _).trans hb
  have ha : CappedLoop.Comparator.attemptBound D ≤ 40*K^2 := by
    exact (attempt_bound D).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by dsimp [K]; omega) 2))
  have h1 : K ≤ K^2 := by nlinarith
  have h2 : K^2 ≤ K^3 := by
    have := Nat.mul_le_mul_left (K^2) (show 1 ≤ K by omega)
    nlinarith [this]
  calc
    TicketWordScratch.drawBound D B R ≤
        K*(2*K+K+6)+3+(K+K+2)+
        (K*(40*K^2+(2*K+3))+3)+2+2*K+2*K+11 := by
      unfold TicketWordScratch.drawBound
      gcongr
    _ ≤ 100*K^3 := by nlinarith

private theorem loaded_bound (D B R : Nat) :
    LoadedTicketMachine.loaderBound D B R +
        LoadedTicketMachine.ticketBound D B R + 1 ≤
      (UnaryBinaryEncoding.coefficient+130)*(D+B+R+2)^3 := by
  have hl := DrawParameterLoader.loader_bound_polynomial D B R
  change LoadedTicketMachine.loaderBound D B R ≤
    (UnaryBinaryEncoding.coefficient+26)*(D+B+R+2)^2 at hl
  have hd := draw_bound D B R
  let K := D+B+R+2
  have hk : 2 ≤ K := by dsimp [K]; omega
  have hD : D+3 ≤ 2*K := by dsimp [K]; omega
  have h1 : K ≤ K^2 := by nlinarith
  have h2 : K^2 ≤ K^3 := by
    have := Nat.mul_le_mul_left (K^2) (show 1 ≤ K by omega)
    nlinarith [this]
  have hu := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+26) h2
  change LoadedTicketMachine.loaderBound D B R ≤
    (UnaryBinaryEncoding.coefficient+26)*K^2 at hl
  change TicketWordScratch.drawBound D B R ≤ 100*K^3 at hd
  change LoadedTicketMachine.loaderBound D B R +
      LoadedTicketMachine.ticketBound D B R + 1 ≤
    (UnaryBinaryEncoding.coefficient+130)*K^3
  unfold LoadedTicketMachine.ticketBound
  nlinarith

def rawStepCap (root : Code) (B R : Nat) : Nat :=
  13*(codeSize root+3)^2 +
    (UnaryBinaryEncoding.coefficient+130)*(codeSize root+B+R+2)^3 +
    72*codeSize root+77

private theorem normalized_budget (root : Code) (s : State)
    (ht : Trace root s) (c : Code) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨c::cs,outputWord.reverse⟩) :
    codeSize c + codesSize cs + outputWord.length ≤ codeSize root := by
  have hn := normalize_potential_le s
  have hr := trace_potential_le root s ht
  simp only [hstate,potential,codesSize,List.length_reverse] at hn
  dsimp [potential] at hr
  omega

private theorem request_le_root (root : Code) (s : State)
    (ht : Trace root s) (c : Code) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨c::cs,outputWord.reverse⟩) :
    request (GeneratorCode.normalize s) ≤ codeSize root := by
  have hb := normalized_budget root s ht c cs outputWord hstate
  have hlocal : request ⟨c::cs,outputWord.reverse⟩ ≤ codeSize c := by
    cases c with
    | emit bits => simp [request,codeSize]; omega
    | ticket n => cases n <;> simp [request,codeSize]; omega
    | bit => simp [request,codeSize]
    | append f g => simp [request,codeSize]; omega
    | branch3 n a b f g h =>
        cases n <;> simp [request,codeSize] <;> omega
  rw [hstate]
  omega

private theorem todoWord_length (cs : List Code) :
    (CodeAdminNormalization.todoWord cs).length = codesSize cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      change (encodeCode c ++ CodeAdminNormalization.todoWord cs).length =
        codeSize c + codesSize cs
      simp [encodeCode_length,ih]

private theorem branch_cost_le_root (root : Code) (s : State)
    (ht : Trace root s) (D a b : Nat) (f g h : Code)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 D a b f g h :: cs,outputWord.reverse⟩)
    (q : Fin D) :
    q.val+a+b+
      (BranchSelection.inputWord f g h
        (CodeAdminNormalization.todoWord cs)).length ≤ codeSize root := by
  have hb := normalized_budget root s ht
    (.branch3 D a b f g h) cs outputWord hstate
  have hq := q.isLt
  simp only [BranchSelection.inputWord,List.length_append,
    encodeCode_length,todoWord_length,codeSize] at *
  omega

private theorem drawClock_le (root : Code) (D B R : Nat)
    (hD : D ≤ codeSize root) :
    CodeAdminDraw.drawClock D B R ≤
      2*codeSize root+4+
        (UnaryBinaryEncoding.coefficient+130)*
          (codeSize root+B+R+2)^3 := by
  have hl := loaded_bound D B R
  have hp : (D+B+R+2)^3 ≤ (codeSize root+B+R+2)^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hm := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient+130) hp
  unfold CodeAdminDraw.drawClock
  omega

theorem done_public (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (h : (GeneratorCode.normalize s).todo = [])
    (tape : List Bool) (B R : Nat) :
    ∃ t ≤ rawStepCap root B R,
      let d := CodeAdminDraw.doneCfg
        (GeneratorCode.normalize s).output.reverse tape B R
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      CodeAdminBranchJoin.run t (CodeAdminBranchJoin.start s tape B R) =
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩ := by
  obtain ⟨t,ht',hr⟩ := CodeAdminBranchJoin.done_from_raw
    root s hp ht h tape B R
  exact ⟨t,by unfold rawStepCap; omega,hr⟩

theorem failure_public (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (c : Code) (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨c::cs,outputWord.reverse⟩)
    (hc : GeneratorPositive.DrawHead c)
    (B R N : Nat)
    (hB : Nat.clog 2 (request (GeneratorCode.normalize s)) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (hq : CappedSampler.runWideBits
      (request (GeneratorCode.normalize s)) B R hB tape.1 = none) :
    ∃ t F, t ≤ rawStepCap root B R ∧
      let d := CodeAdminDraw.drawResult
        (request (GeneratorCode.normalize s)) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) outputWord F
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      CodeAdminBranchJoin.run t
        (CodeAdminBranchJoin.start s
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩ := by
  obtain ⟨t,F,ht',hr⟩ := CodeAdminBranchJoin.failure_from_raw
    root s hp ht c cs outputWord hstate hc B R N hB tape hq
  have hD := request_le_root root s ht c cs outputWord hstate
  have hd := drawClock_le root
    (request (GeneratorCode.normalize s)) B R hD
  exact ⟨t,F,by unfold rawStepCap; omega,hr⟩

theorem ticket_public (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D : Nat) (hD : 0 < D) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.ticket D :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ t F, t ≤ rawStepCap root B R ∧
      let d := CodeAdminDraw.drawResult D B R N hB tape .ticket
        (CodeAdminNormalization.todoWord cs) (List.replicate D true)
        [] [] outputWord F
      let e := CodeDrawResultHandler.framed d.var d.stk
        (CodeDrawOutput.cfg none none []
          (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ outputWord))
      let j := CodeAdminResultJoin.resultCfg e
      CodeAdminBranchJoin.run t
        (CodeAdminBranchJoin.start s
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩ := by
  obtain ⟨t,F,ht',hr⟩ := CodeAdminBranchJoin.ticket_success_from_raw
    root s hp ht D hD cs outputWord hstate B R N hB tape q hq
  have hsize := normalized_budget root s ht (.ticket D) cs outputWord hstate
  have hden : D ≤ codeSize root := by simp [codeSize] at hsize; omega
  have hd := drawClock_le root D B R hden
  exact ⟨t,F,by unfold rawStepCap; omega,hr⟩

theorem bit_public (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.bit :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin 2) (hq : CappedSampler.runWideBits 2 B R hB tape.1 = some q) :
    ∃ t F, t ≤ rawStepCap root B R ∧
      let d := CodeAdminDraw.drawResult 2 B R N hB tape .bit
        (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F
      let e := CodeDrawResultHandler.framed d.var d.stk
        (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))
      let j := CodeAdminResultJoin.resultCfg e
      CodeAdminBranchJoin.run t
        (CodeAdminBranchJoin.start s
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩ := by
  obtain ⟨t,F,ht',hr⟩ := CodeAdminBranchJoin.bit_success_from_raw
    root s hp ht cs outputWord hstate B R N hB tape q hq
  have hd := drawClock_le root 2 B R (by
    have := codeSize_ge_three root
    omega)
  exact ⟨t,F,by unfold rawStepCap; omega,hr⟩

theorem branch_public (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D a b : Nat) (hD : 0 < D) (f g h : Code)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 D a b f g h :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ t F, t ≤ rawStepCap root B R ∧
      let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F
      let d := CodeAdminDraw.drawResult D B R N hB tape .branch3
        (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      CodeAdminBranchJoin.run t
        (CodeAdminBranchJoin.start s
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        CodeAdminBranchJoin.branchCfg j.var
          (CodeBranchAdapter.final base.var base.stk
            (List.replicate D true) outputWord q.val a b f g h
            (CodeAdminNormalization.todoWord cs)) := by
  obtain ⟨t,F,ht',hr⟩ := CodeAdminBranchJoin.branch_selected_from_raw
    root s hp ht D a b hD f g h cs outputWord hstate B R N hB tape q hq
  have hb := normalized_budget root s ht
    (.branch3 D a b f g h) cs outputWord hstate
  have hden : D ≤ codeSize root := by simp [codeSize] at hb; omega
  have hc := branch_cost_le_root root s ht D a b f g h cs outputWord hstate q
  have hd := drawClock_le root D B R hden
  exact ⟨t,F,by unfold rawStepCap; omega,hr⟩

#print axioms done_public
#print axioms failure_public
#print axioms ticket_public
#print axioms bit_public
#print axioms branch_public

end
end Paper2.CodeRawStepPublicBound
