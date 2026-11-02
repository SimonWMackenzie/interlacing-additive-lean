import Paper2.CodeFullPadding
import Paper2.CappedLoopSerializationBridge
import Mathlib.Tactic

/-! Source-faithful decomposition of the actual capped generator run. -/

namespace Paper2.CodeFullRun

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize
open Turing EthInapproximability.CurrentPaper

noncomputable section

theorem writeTape_cons (B R N : Nat)
    (t : CappedSampler.Adaptive.Tape B R (N+1)) :
    (RecursiveSamplingTape.writeTape B R (N+1) t).val =
      CappedLoop.BlockTransfer.flatBitTape B R t.1 ++
        (RecursiveSamplingTape.writeTape B R N t.2).val := by
  rw [← CappedLoop.SerializationBridge.flatAdaptiveTape_eq_writeTape,
    ← CappedLoop.SerializationBridge.flatAdaptiveTape_eq_writeTape]
  rfl

theorem read_normalize (s : State) :
    read (GeneratorCode.normalize s) = read s := by
  rw [GeneratorCode.read_eq, GeneratorCode.read_eq,
    GeneratorCode.normalize_meaning]

theorem done_next (M : Nat) (s : BoundedState M)
    (hd : (GeneratorCode.normalize s.val).todo = [])
    (q : Fin (den s)) :
    (next s q).val = GeneratorCode.normalize s.val := by
  simp [next,nextRaw,GeneratorCode.advance,hd]

theorem done_den (M : Nat) (s : BoundedState M)
    (hd : (GeneratorCode.normalize s.val).todo = []) : den s = 1 := by
  simp [den,request,hd]

theorem done_step_read (M : Nat) (s : BoundedState M)
    (hd : (GeneratorCode.normalize s.val).todo = [])
    (q : Fin (den s)) : read (next s q).val = read s.val := by
  rw [done_next M s hd q, read_normalize]

theorem done_step_done (M : Nat) (s : BoundedState M)
    (hd : (GeneratorCode.normalize s.val).todo = [])
    (q : Fin (den s)) :
    (GeneratorCode.normalize (next s q).val).todo = [] := by
  rw [done_next M s hd q]
  have hready := GeneratorCode.normalize_ready s.val
  rw [GeneratorCode.normalize]
  split
  · exact hd
  · rename_i t ht
    simp [hready] at ht

theorem done_draw (M B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (s : BoundedState M) (hd : (GeneratorCode.normalize s.val).todo = [])
    (hR : 0 < R) (block : CappedSampler.BitTape B R) :
    CappedSampler.runWideBits (den s) B R (den_width hMB s) block =
      some ⟨0, den_pos s⟩ := by
  have h : ∀ (D : Nat) (hB : Nat.clog 2 D ≤ B) (q : Fin D),
      D = 1 → CappedSampler.runWideBits D B R hB block = some q := by
    intro D hB q he
    subst D
    have hq : q = (⟨0,by decide⟩ : Fin 1) := Subsingleton.elim _ _
    subst q
    simpa [CappedSampler.runWideBits] using
      (CappedSampler.singleton_success R hR
        (CappedSampler.prefixBitTape hB R block))
  exact h (den s) (den_width hMB s) ⟨0,den_pos s⟩
    (done_den M s hd)

theorem capped_done (M B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (hR : 0 < R) (N : Nat) (s : BoundedState M)
    (hd : (GeneratorCode.normalize s.val).todo = [])
    (t : CappedSampler.Adaptive.Tape B R N) :
    ∃ u, capped B R hMB N s t = some u ∧
      read u.val = read s.val := by
  induction N generalizing s with
  | zero => exact ⟨s,rfl,rfl⟩
  | succ N ih =>
      let q : Fin (den s) := ⟨0,den_pos s⟩
      have hdraw : CappedSampler.runWideBits (den s) B R
          (den_width hMB s) t.1 = some q := done_draw M B R hMB s hd hR t.1
      obtain ⟨u,hu,hread⟩ := ih (next s q) (done_step_done M s hd q) t.2
      refine ⟨u,?_,?_⟩
      · simpa [capped,CappedSampler.Adaptive.run,hdraw] using hu
      · exact hread.trans (done_step_read M s hd q)

theorem zero_attempt_failure (M B N : Nat) (hMB : Nat.clog 2 M ≤ B)
    (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B 0 (N+1)) :
    capped B 0 hMB (N+1) s t = none := by
  simp [capped,CappedSampler.Adaptive.run,CappedSampler.runWideBits,
    CappedSampler.runBits,CappedSampler.run]

theorem draw_cast (D E B R : Nat) (hDE : D = E)
    (hD : Nat.clog 2 D ≤ B) (hE : Nat.clog 2 E ≤ B)
    (block : CappedSampler.BitTape B R) (q : Fin D)
    (hq : CappedSampler.runWideBits D B R hD block = some q) :
    CappedSampler.runWideBits E B R hE block =
      some (Fin.cast hDE q) := by
  subst E
  simpa using hq

theorem accepted_of_draw (root : Code) (M B R N : Nat)
    (hMB : Nat.clog 2 M ≤ B) (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (hne : (GeneratorCode.normalize s.val).todo ≠ [])
    (t : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin (den s))
    (hq : CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 = some q) :
    CodeFullRepeatPath.Accepted root B R s.val
      (RecursiveSamplingTape.writeTape B R (N+1) t).val
      (next s q).val
      (RecursiveSamplingTape.writeTape B R N t.2).val := by
  obtain ⟨c,cs,hcs,hc⟩ := ready_positive_draw
    (GeneratorCode.normalize s.val) (normalize_positive s.val hp)
    (GeneratorCode.normalize_ready s.val) hne
  have hstate₀ : GeneratorCode.normalize s.val =
      ⟨c::cs,(GeneratorCode.normalize s.val).output⟩ := by
    cases hns : GeneratorCode.normalize s.val with
    | mk todo out =>
      simp only [hns] at hcs ⊢
      cases hcs
      rfl
  cases c with
  | ticket D =>
      cases D with
      | zero => simp [DrawHead] at hc
      | succ d =>
          let D := d+1
          have hstate : GeneratorCode.normalize s.val =
              ⟨.ticket D::cs,((GeneratorCode.normalize s.val).output.reverse).reverse⟩ := by
            simpa [D] using hstate₀
          have hden : den s = D := by simp [den,request,hcs,D]
          let q' : Fin D := Fin.cast hden q
          have hB : Nat.clog 2 D ≤ B := by
            simpa [← hden] using den_width hMB s
          have hq' := draw_cast (den s) D B R hden
            (den_width hMB s) hB t.1 q hq
          have ha := CodeFullRepeatPath.Accepted.ticket s.val hp ht
            D (by omega) cs (GeneratorCode.normalize s.val).output.reverse
            hstate N hB t q' hq'
          have hn : (next s q).val =
              GeneratorCode.advance
                ⟨.ticket D::cs,
                  ((GeneratorCode.normalize s.val).output.reverse).reverse⟩ q'.val := by
            change GeneratorCode.advance (GeneratorCode.normalize s.val) q.val = _
            rw [hstate]
            simp [q']
          rw [hn]
          exact ha
  | bit =>
      have hstate : GeneratorCode.normalize s.val =
          ⟨.bit::cs,((GeneratorCode.normalize s.val).output.reverse).reverse⟩ := by
        simpa using hstate₀
      have hden : den s = 2 := by simp [den,request,hcs]
      let q' : Fin 2 := Fin.cast hden q
      have hB : Nat.clog 2 2 ≤ B := by
        simpa [← hden] using den_width hMB s
      have hq' := draw_cast (den s) 2 B R hden
        (den_width hMB s) hB t.1 q hq
      have ha := CodeFullRepeatPath.Accepted.bit s.val hp ht
        cs (GeneratorCode.normalize s.val).output.reverse
        hstate N hB t q' hq'
      have hn : (next s q).val =
          GeneratorCode.advance
            ⟨.bit::cs,
              ((GeneratorCode.normalize s.val).output.reverse).reverse⟩ q'.val := by
        change GeneratorCode.advance (GeneratorCode.normalize s.val) q.val = _
        rw [hstate]
        simp [q']
      rw [hn]
      exact ha
  | branch3 D a b f g h =>
      cases D with
      | zero => simp [DrawHead] at hc
      | succ d =>
          let D := d+1
          have hstate : GeneratorCode.normalize s.val =
              ⟨.branch3 D a b f g h::cs,
                ((GeneratorCode.normalize s.val).output.reverse).reverse⟩ := by
            simpa [D] using hstate₀
          have hden : den s = D := by simp [den,request,hcs,D]
          let q' : Fin D := Fin.cast hden q
          have hB : Nat.clog 2 D ≤ B := by
            simpa [← hden] using den_width hMB s
          have hq' := draw_cast (den s) D B R hden
            (den_width hMB s) hB t.1 q hq
          have ha := CodeFullRepeatPath.Accepted.branch s.val hp ht
            D a b (by omega) f g h cs
            (GeneratorCode.normalize s.val).output.reverse
            hstate N hB t q' hq'
          have hn : (next s q).val =
              GeneratorCode.advance
                ⟨.branch3 D a b f g h::cs,
                  ((GeneratorCode.normalize s.val).output.reverse).reverse⟩ q'.val := by
            change GeneratorCode.advance (GeneratorCode.normalize s.val) q.val = _
            rw [hstate]
            simp [q']
          rw [hn]
          exact ha
  | emit bits => simp [DrawHead] at hc
  | append left right => simp [DrawHead] at hc

theorem read_some_done (s : State) (bytes : List Bool)
    (hr : GeneratorCode.read s = some bytes) :
    (GeneratorCode.normalize s).todo = [] ∧
      (GeneratorCode.normalize s).output = bytes := by
  unfold GeneratorCode.read GeneratorCode.readReady at hr
  cases htodo : (GeneratorCode.normalize s).todo with
  | nil =>
      simp only [htodo] at hr
      exact ⟨rfl,Option.some.inj hr⟩
  | cons c cs => simp [htodo] at hr

/-- An actual successful capped source execution supplies its own accepted
draw path, ending at the first normalized-done state. Its residual tape is the
literal suffix of the same typed source tape; no Path is an input premise. -/
theorem source_success_path (root : Code) (M B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (N : Nat) (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (t : CappedSampler.Adaptive.Tape B R N)
    (u : BoundedState M) (bytes : List Bool)
    (hu : capped B R hMB N s t = some u)
    (hr : GeneratorCode.read u.val = some bytes) :
    ∃ (m : Nat) (rest : CappedSampler.Adaptive.Tape B R m)
      (mid : BoundedState M),
      m ≤ N ∧
      Nonempty (CodeFullRepeatPath.Path root B R s.val
        (RecursiveSamplingTape.writeTape B R N t).val mid.val
        (RecursiveSamplingTape.writeTape B R m rest).val) ∧
      (GeneratorCode.normalize mid.val).todo = [] ∧
      GeneratorCode.read mid.val = some bytes ∧
      PositiveState mid.val ∧ Trace root mid.val := by
  induction N generalizing s u with
  | zero =>
      have he : s = u := by simpa [capped,CappedSampler.Adaptive.run] using hu
      subst u
      obtain ⟨hd,_⟩ := read_some_done s.val bytes hr
      exact ⟨0,(),s,le_refl _,⟨.refl _ _⟩,hd,hr,hp,ht⟩
  | succ N ih =>
      by_cases hdone : (GeneratorCode.normalize s.val).todo = []
      · obtain ⟨v,hv,hread⟩ := capped_done M B R hMB hR (N+1) s hdone t
        have he : v = u := by rw [hu] at hv; exact Option.some.inj hv.symm
        subst v
        exact ⟨N+1,t,s,le_refl _,⟨.refl _ _⟩,hdone,
          hread.symm.trans hr,hp,ht⟩
      · cases hdraw : CappedSampler.runWideBits (den s) B R
          (den_width hMB s) t.1 with
        | none =>
            simp [capped,CappedSampler.Adaptive.run,hdraw] at hu
        | some q =>
            have htail : capped B R hMB N (next s q) t.2 = some u := by
              simpa [capped,CappedSampler.Adaptive.run,hdraw] using hu
            obtain ⟨m,rest,mid,hm,hpath,hd,hmread,hpm,htm⟩ := ih
              (next s q) (next_positive s hp q)
              (trace_nextRaw root s ht q) t.2 u htail hr
            have hhead := accepted_of_draw root M B R N hMB s hp ht
              hdone t q hdraw
            exact ⟨m,rest,mid,by omega,
              ⟨.cons hhead (Classical.choice hpath)⟩,hd,hmread,hpm,htm⟩

/-- When the actual capped run fails with a positive attempt count, it has a
source-derived successful prefix followed by its first failing draw. -/
theorem source_failure_path (root : Code) (M B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (N : Nat) (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (t : CappedSampler.Adaptive.Tape B R N)
    (hf : capped B R hMB N s t = none) :
    ∃ (m : Nat) (rest : CappedSampler.Adaptive.Tape B R (m+1))
      (mid : BoundedState M),
      m+1 ≤ N ∧
      Nonempty (CodeFullRepeatPath.Path root B R s.val
        (RecursiveSamplingTape.writeTape B R N t).val mid.val
        (RecursiveSamplingTape.writeTape B R (m+1) rest).val) ∧
      PositiveState mid.val ∧ Trace root mid.val ∧
      (GeneratorCode.normalize mid.val).todo ≠ [] ∧
      CappedSampler.runWideBits (den mid) B R
        (den_width hMB mid) rest.1 = none := by
  induction N generalizing s with
  | zero => simp [capped,CappedSampler.Adaptive.run] at hf
  | succ N ih =>
      by_cases hdone : (GeneratorCode.normalize s.val).todo = []
      · obtain ⟨u,hu,_⟩ := capped_done M B R hMB hR (N+1) s hdone t
        rw [hf] at hu
        contradiction
      · cases hdraw : CappedSampler.runWideBits (den s) B R
          (den_width hMB s) t.1 with
        | none =>
            exact ⟨N,t,s,le_refl _,⟨.refl _ _⟩,hp,ht,hdone,hdraw⟩
        | some q =>
            have htail : capped B R hMB N (next s q) t.2 = none := by
              simpa [capped,CappedSampler.Adaptive.run,hdraw] using hf
            obtain ⟨m,rest,mid,hm,hpath,hpm,htm,hndraw,hfail⟩ := ih
              (next s q) (next_positive s hp q)
              (trace_nextRaw root s ht q) t.2 htail
            have hhead := accepted_of_draw root M B R N hMB s hp ht
              hdone t q hdraw
            exact ⟨m,rest,mid,by omega,
              ⟨.cons hhead (Classical.choice hpath)⟩,
              hpm,htm,hndraw,hfail⟩

theorem padding_reenter_public_from_reached (root : Code)
    (s next : State) (tape residual : List Bool) (B R : Nat)
    (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none)
    (ht : t ≤ CodeRawStepPublicBound.rawStepCap root B R)
    (hs : CodeFullRepeat.success
      ((d.var,none) : CodeFullPadding.Control) = true)
    (hbank : (CodeInterpreterReset.final d.var d.stk).stk =
      (CodeAdminBranchJoin.start next residual B R).stk) :
    ∃ u ≤ CodeFullRepeatPublic.repeatStepCap root B R,
      CodeFullPadding.run u (CodeFullPadding.start s tape B R) =
        CodeFullPadding.start next residual B R := by
  obtain ⟨u,hu,hru⟩ := CodeFullPadding.reenter_from_reached
    s next tape residual B R d t hr hd hs hbank
  have hc := CodeUniformResetBound.raw_terminal_clock_mono
    s tape B R t (CodeRawStepPublicBound.rawStepCap root B R) d hr ht
  refine ⟨u,?_,hru⟩
  unfold CodeFullRepeatPublic.repeatStepCap CodeFullCleanBound.publicStepCap
  omega

private theorem padding_run_add (a b : Nat) (c : CodeFullPadding.Config) :
    CodeFullPadding.run (a+b) c =
      CodeFullPadding.run b (CodeFullPadding.run a c) := by
  change ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance
      CodeFullPadding.program)^[a+b]) c =
    ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance
      CodeFullPadding.program)^[b])
      (((EthInapproximability.CurrentPaper.BitMachineEncoding.advance
        CodeFullPadding.program)^[a]) c)
  rw [Nat.add_comm a b,Function.iterate_add_apply]

theorem padding_failure_public_from_reached (root : Code)
    (s : State) (tape : List Bool) (B R : Nat)
    (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none)
    (ht : t ≤ CodeRawStepPublicBound.rawStepCap root B R)
    (hs : CodeFullRepeat.success
      ((d.var,none) : CodeFullPadding.Control) = false)
    (hf : CodeFullPadding.doneStatus
      ((d.var,none) : CodeFullPadding.Control) = false) :
    ∃ u ≤ CodeFullRepeatPublic.repeatStepCap root B R,
      CodeFullPadding.run u (CodeFullPadding.start s tape B R) =
        ⟨none,(d.var,none),CodeInterpreterReset.resetBank d.stk⟩ := by
  obtain ⟨a,ha,har⟩ := CodeFullCleanBound.raw_clean_public
    s tape B R d t (CodeRawStepPublicBound.rawStepCap root B R)
    hr hd ht
  let clean := CodeFullCleanStep.resetCfg
    (CodeInterpreterReset.final d.var d.stk)
  obtain ⟨b,hb,hbr⟩ := CodeFullPadding.source_to_route
    (CodeFullCleanStep.start s tape B R) clean a har rfl
  have hroute := CodeFullPadding.route_failure
    ((d.var,none) : CodeFullPadding.Control)
    (CodeInterpreterReset.resetBank d.stk) hs hf
  change CodeFullPadding.run 1
    (CodeFullPadding.routeCfg clean.var clean.stk) =
    ⟨none,(d.var,none),CodeInterpreterReset.resetBank d.stk⟩ at hroute
  change CodeFullPadding.run b (CodeFullPadding.start s tape B R) =
    CodeFullPadding.routeCfg clean.var clean.stk at hbr
  refine ⟨b+1,?_,?_⟩
  · unfold CodeFullRepeatPublic.repeatStepCap
    omega
  · rw [padding_run_add b 1,hbr]
    exact hroute

theorem failing_draw_halts_public (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (c : Code) (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨c::cs,outputWord.reverse⟩)
    (hc : DrawHead c) (B R N : Nat)
    (hB : Nat.clog 2 (request (GeneratorCode.normalize s)) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (hq : CappedSampler.runWideBits
      (request (GeneratorCode.normalize s)) B R hB tape.1 = none) :
    ∃ u F, u ≤ CodeFullRepeatPublic.repeatStepCap root B R ∧
      let d := CodeAdminDraw.drawResult
        (request (GeneratorCode.normalize s)) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) outputWord F
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
      CodeFullPadding.run u
        (CodeFullPadding.start s
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,(endpoint.var,none),CodeInterpreterReset.resetBank endpoint.stk⟩ := by
  obtain ⟨t,F,ht0,hr⟩ := CodeRawStepPublicBound.failure_public
    root s hp ht c cs outputWord hstate hc B R N hB tape hq
  let d := CodeAdminDraw.drawResult
    (request (GeneratorCode.normalize s)) B R N hB tape
    (CodeHeaderMachine.headerKind c)
    (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
    (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) outputWord F
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  have hraw : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
      endpoint := hr
  have hsraw := (CodeDrawResultHandler.result_status
    (request (GeneratorCode.normalize s)) B R N hB tape
    (CodeHeaderMachine.headerKind c)
    (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
    (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) outputWord F).1
  have hs : CodeFullRepeat.success ((endpoint.var,none) :
      CodeFullPadding.Control) = false := by
    change (CodeDrawResultHandler.savedStatus d.var == some true) = false
    rw [hsraw,hq]
    rfl
  have hf : CodeFullPadding.doneStatus ((endpoint.var,none) :
      CodeFullPadding.Control) = false := by
    change (CodeDrawResultHandler.savedStatus d.var).isNone = false
    rw [hsraw,hq]
    rfl
  obtain ⟨u,hu,hru⟩ := padding_failure_public_from_reached root s
    (RecursiveSamplingTape.writeTape B R (N+1) tape).val
    B R endpoint t hraw rfl ht0 hs hf
  exact ⟨u,F,hu,hru⟩

/-- One accepted source draw re-enters the same canonical bank in the *padding*
controller, not merely the older early-halt repeat controller. -/
theorem accepted_run_padding_public {root : Code} {B R : Nat}
    {s s' : State} {tape tape' : List Bool}
    (h : CodeFullRepeatPath.Accepted root B R s tape s' tape') :
    ∃ u ≤ CodeFullRepeatPublic.repeatStepCap root B R,
      CodeFullPadding.run u (CodeFullPadding.start s tape B R) =
        CodeFullPadding.start s' tape' B R := by
  cases h with
  | ticket hp ht D hD cs out hstate N hB tape q hq =>
      obtain ⟨t,F,ht0,hr⟩ := CodeRawStepPublicBound.ticket_public
        root _ hp ht D hD cs out hstate B R N hB tape q hq
      let raw := CodeAdminDraw.drawResult D B R N hB tape .ticket
        (CodeAdminNormalization.todoWord cs) (List.replicate D true)
        [] [] out F
      let handled := CodeDrawResultHandler.framed raw.var raw.stk
        (CodeDrawOutput.cfg none none []
          (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ out))
      let joined := CodeAdminResultJoin.resultCfg handled
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
      have hsraw := (CodeDrawResultHandler.result_status D B R N hB tape
        .ticket (CodeAdminNormalization.todoWord cs)
        (List.replicate D true) [] [] out F).1
      have hs : CodeFullRepeat.success ((endpoint.var,none) :
          CodeFullPadding.Control) = true := by
        change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
        rw [hsraw,hq]; rfl
      have hbank := CodeFullCleanMeaning.ticket_ready_bank D B R N hD hB
        tape cs out.reverse F q
      have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
          (CodeAdminBranchJoin.start
            (GeneratorCode.advance ⟨.ticket D::cs,out.reverse⟩ q.val)
            (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
        simpa [raw,handled,joined,endpoint] using hbank
      exact padding_reenter_public_from_reached root _ _ _ _ B R endpoint t
        hr rfl ht0 hs hbank'
  | bit hp ht cs out hstate N hB tape q hq =>
      obtain ⟨t,F,ht0,hr⟩ := CodeRawStepPublicBound.bit_public
        root _ hp ht cs out hstate B R N hB tape q hq
      let raw := CodeAdminDraw.drawResult 2 B R N hB tape .bit
        (CodeAdminNormalization.todoWord cs) [] [] [] out F
      let handled := CodeDrawResultHandler.framed raw.var raw.stk
        (CodeDrawOutput.cfg none none [] (decide (q.val=1)::out))
      let joined := CodeAdminResultJoin.resultCfg handled
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
      have hsraw := (CodeDrawResultHandler.result_status 2 B R N hB tape
        .bit (CodeAdminNormalization.todoWord cs) [] [] [] out F).1
      have hs : CodeFullRepeat.success ((endpoint.var,none) :
          CodeFullPadding.Control) = true := by
        change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
        rw [hsraw,hq]; rfl
      have hbank := CodeFullCleanMeaning.bit_ready_bank B R N hB
        tape cs out.reverse F q
      have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
          (CodeAdminBranchJoin.start
            (GeneratorCode.advance ⟨.bit::cs,out.reverse⟩ q.val)
            (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
        simpa [raw,handled,joined,endpoint] using hbank
      exact padding_reenter_public_from_reached root _ _ _ _ B R endpoint t
        hr rfl ht0 hs hbank'
  | branch hp ht D a b hD f g h cs out hstate N hB tape q hq =>
      obtain ⟨t,F,ht0,hr⟩ := CodeRawStepPublicBound.branch_public
        root _ hp ht D a b hD f g h cs out hstate B R N hB tape q hq
      let tail := BranchSelection.inputWord f g h
        (CodeAdminNormalization.todoWord cs)
      let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3 tail
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F
      let raw := CodeAdminDraw.drawResult D B R N hB tape .branch3 tail
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F
      let joined : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(raw.var,none),raw.stk⟩
      let selected := CodeBranchAdapter.final base.var base.stk
        (List.replicate D true) out q.val a b f g h
        (CodeAdminNormalization.todoWord cs)
      let endpoint := CodeAdminBranchJoin.branchCfg joined.var selected
      have hsraw := (CodeDrawResultHandler.result_status D B R N hB tape
        .branch3 tail (List.replicate D true) (List.replicate a true)
        (List.replicate b true) out F).1
      have hs : CodeFullRepeat.success ((endpoint.var,none) :
          CodeFullPadding.Control) = true := by
        change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
        rw [hsraw,hq]; rfl
      have hbank := CodeFullCleanMeaning.branch_ready_bank D a b B R N
        hD hB tape f g h cs out.reverse F q
      have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
          (CodeAdminBranchJoin.start
            (GeneratorCode.advance
              ⟨.branch3 D a b f g h::cs,out.reverse⟩ q.val)
            (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
        simpa [tail,base,raw,joined,selected,endpoint] using hbank
      exact padding_reenter_public_from_reached root _ _ _ _ B R endpoint t
        hr rfl ht0 hs hbank'

theorem path_run_padding_public {root : Code} {B R : Nat}
    {s last : State} {tape tapeLast : List Bool}
    (h : CodeFullRepeatPath.Path root B R s tape last tapeLast) :
    ∃ u ≤ h.length * CodeFullRepeatPublic.repeatStepCap root B R,
      CodeFullPadding.run u (CodeFullPadding.start s tape B R) =
        CodeFullPadding.start last tapeLast B R := by
  induction h with
  | refl s tape =>
      exact ⟨0,by simp [CodeFullRepeatPath.Path.length],rfl⟩
  | cons head tail ih =>
      obtain ⟨a,ha,hra⟩ := accepted_run_padding_public head
      obtain ⟨b,hb,hrb⟩ := ih
      refine ⟨a+b,?_,?_⟩
      · simp only [CodeFullRepeatPath.Path.length,Nat.add_mul]
        omega
      · rw [padding_run_add a b,hra,hrb]

/-- A source done state enters the physical drain; the terminal tape is empty,
while every non-tape bank is exactly the physically reached clean bank. -/
theorem done_drains_public (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (hd : (GeneratorCode.normalize s).todo = [])
    (tape : List Bool) (B R : Nat) :
    ∃ u ≤ CodeFullRepeatPublic.repeatStepCap root B R + tape.length + 2,
      let d := CodeAdminDraw.doneCfg
        (GeneratorCode.normalize s).output.reverse tape B R
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
      CodeFullPadding.run u (CodeFullPadding.start s tape B R) =
        ⟨none,(endpoint.var,none),Function.update
          (CodeInterpreterReset.resetBank endpoint.stk)
          CodeFullPadding.tapeSlot []⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeRawStepPublicBound.done_public
    root s hp ht hd tape B R
  let d := CodeAdminDraw.doneCfg
    (GeneratorCode.normalize s).output.reverse tape B R
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  have hraw : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = endpoint := hr
  obtain ⟨a,ha,har⟩ := CodeFullCleanBound.raw_clean_public
    s tape B R endpoint t (CodeRawStepPublicBound.rawStepCap root B R)
    hraw rfl ht
  let clean := CodeFullCleanStep.resetCfg
    (CodeInterpreterReset.final endpoint.var endpoint.stk)
  obtain ⟨b,hb,hbr⟩ := CodeFullPadding.source_to_route
    (CodeFullCleanStep.start s tape B R) clean a har rfl
  have hs : CodeFullRepeat.success ((endpoint.var,none) :
      CodeFullPadding.Control) = false := by
    simp [CodeFullRepeat.success,endpoint,j,d,
      CodeAdminBranchJoin.joinLift,CodeAdminResultJoin.resultCfg,
      BitMachineInline.cfg,CodeDrawResultHandler.savedStatus,
      CodeAdminDraw.doneCfg,CodeAdminDraw.drawControl,
      CodeHeaderDraw.drawInitialControl,
      LoadedTicketMachine.statusStartControl]
  have hdone : CodeFullPadding.doneStatus ((endpoint.var,none) :
      CodeFullPadding.Control) = true := by
    simp [CodeFullPadding.doneStatus,endpoint,j,d,
      CodeAdminBranchJoin.joinLift,CodeAdminResultJoin.resultCfg,
      BitMachineInline.cfg,CodeDrawResultHandler.savedStatus,
      CodeAdminDraw.doneCfg,CodeAdminDraw.drawControl,
      CodeHeaderDraw.drawInitialControl,
      LoadedTicketMachine.statusStartControl]
  have htape : (CodeInterpreterReset.resetBank endpoint.stk)
      CodeFullPadding.tapeSlot = tape := by
    rw [CodeInterpreterReset.reset_kept _ _ (by
      simp [CodeInterpreterReset.keep,CodeFullPadding.tapeSlot,
        CodeHeaderDraw.d])]
    simp [endpoint,j,d,
      CodeFullPadding.tapeSlot,CodeAdminDraw.doneCfg,
      CodeAdminDraw.doneBank,DrawParameterLoader.initialBank,
      DrawParameterLoader.mainBank,CodeHeaderDraw.d,
      CodeAdminResultJoin.resultCfg,BitMachineInline.cfg]
  refine ⟨b+(1+(tape.length+2)),?_,?_⟩
  · unfold CodeFullRepeatPublic.repeatStepCap
    omega
  · change CodeFullPadding.run b (CodeFullPadding.start s tape B R) =
      CodeFullPadding.routeCfg clean.var clean.stk at hbr
    rw [padding_run_add b (1+(tape.length+2)),hbr]
    rw [padding_run_add 1 (tape.length+2)]
    have hroute := CodeFullPadding.route_done
      ((endpoint.var,none) : CodeFullPadding.Control)
      (CodeInterpreterReset.resetBank endpoint.stk) hs hdone
    change CodeFullPadding.run 1
      (CodeFullPadding.routeCfg clean.var clean.stk) =
      ⟨some CodeFullPadding.padLabel,(endpoint.var,none),
        CodeInterpreterReset.resetBank endpoint.stk⟩ at hroute
    rw [hroute]
    have hpad := CodeFullPadding.pad_halt endpoint.var
      (CodeInterpreterReset.resetBank endpoint.stk)
    rw [htape] at hpad
    exact hpad

/-- The same fixed program executes the successful part of an *actual* capped
source run and then physically empties the entire remaining input tape. -/
theorem capped_success_run (root : Code) (M B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (N : Nat) (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (t : CappedSampler.Adaptive.Tape B R N)
    (u : BoundedState M) (bytes : List Bool)
    (hu : capped B R hMB N s t = some u)
    (hr : GeneratorCode.read u.val = some bytes) :
    ∃ (m : Nat) (rest : CappedSampler.Adaptive.Tape B R m)
      (mid : BoundedState M) (clock : Nat),
      m ≤ N ∧ GeneratorCode.read mid.val = some bytes ∧
      clock ≤ (codeSize root+1) *
        CodeFullRepeatPublic.repeatStepCap root B R +
        N * (R * B) + 2 ∧
      let tapeLast := (RecursiveSamplingTape.writeTape B R m rest).val
      let d := CodeAdminDraw.doneCfg
        (GeneratorCode.normalize mid.val).output.reverse tapeLast B R
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
      CodeFullPadding.run clock
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N t).val B R) =
        ⟨none,(endpoint.var,none),Function.update
          (CodeInterpreterReset.resetBank endpoint.stk)
          CodeFullPadding.tapeSlot []⟩ := by
  obtain ⟨m,rest,mid,hm,hpath,hd,hmread,hpm,htm⟩ :=
    source_success_path root M B R hMB hR N s hp ht t u bytes hu hr
  let p := Classical.choice hpath
  obtain ⟨a,ha,hra⟩ := path_run_padding_public p
  obtain ⟨b,hb,hrb⟩ := done_drains_public root mid.val hpm htm hd
    (RecursiveSamplingTape.writeTape B R m rest).val B R
  have hl := CodeFullRepeatFuel.path_length_le_root ht p
  refine ⟨m,rest,mid,a+b,hm,hmread,?_,?_⟩
  · have hmul := Nat.mul_le_mul_right
      (CodeFullRepeatPublic.repeatStepCap root B R) hl
    have hbits := Nat.mul_le_mul_right (R*B) hm
    have hlen := RecursiveSamplingTape.writeTape_length B R m rest
    simp only [RecursiveSamplingTape.bitCount] at hlen
    simp only [Nat.add_mul,one_mul]
    omega
  · rw [padding_run_add a b,hra]
    exact hrb

/-- The actual failed source run determines its own first failing draw and the
fixed physical controller reaches the matching failure control, without a
caller-provided path, decoded word, or prepared bank. -/
theorem capped_failure_run (root : Code) (M B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (N : Nat) (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (t : CappedSampler.Adaptive.Tape B R N)
    (hf : capped B R hMB N s t = none) :
    ∃ (m : Nat) (rest : CappedSampler.Adaptive.Tape B R (m+1))
      (mid : BoundedState M) (c : Code) (cs : List Code)
      (F : DrawParameterLoader.LogCopyStack → List Bool) (clock : Nat),
      m+1 ≤ N ∧
      CappedSampler.runWideBits
        (request (GeneratorCode.normalize mid.val)) B R
        (den_width hMB mid) rest.1 = none ∧
      clock ≤ (codeSize root+1) *
        CodeFullRepeatPublic.repeatStepCap root B R ∧
      let out := (GeneratorCode.normalize mid.val).output.reverse
      let hB := den_width hMB mid
      let d := CodeAdminDraw.drawResult
        (request (GeneratorCode.normalize mid.val)) B R m hB rest
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) out F
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
      CodeFullPadding.run clock
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N t).val B R) =
        ⟨none,(endpoint.var,none),CodeInterpreterReset.resetBank endpoint.stk⟩ := by
  obtain ⟨m,rest,mid,hm,hpath,hpm,htm,hndraw,hfail⟩ :=
    source_failure_path root M B R hMB hR N s hp ht t hf
  obtain ⟨c,cs,hcs,hc⟩ := ready_positive_draw
    (GeneratorCode.normalize mid.val)
    (normalize_positive mid.val hpm)
    (GeneratorCode.normalize_ready mid.val) hndraw
  let out := (GeneratorCode.normalize mid.val).output.reverse
  have hstate : GeneratorCode.normalize mid.val = ⟨c::cs,out.reverse⟩ := by
    cases hns : GeneratorCode.normalize mid.val with
    | mk todo output =>
      simp only [hns] at hcs ⊢
      cases hcs
      simp [out,hns]
  have hB : Nat.clog 2 (request (GeneratorCode.normalize mid.val)) ≤ B := by
    simpa [den] using den_width hMB mid
  have hq : CappedSampler.runWideBits
      (request (GeneratorCode.normalize mid.val)) B R hB rest.1 = none := by
    simpa [den] using hfail
  let p := Classical.choice hpath
  obtain ⟨a,ha,hra⟩ := path_run_padding_public p
  obtain ⟨b,F,hb,hrb⟩ := failing_draw_halts_public root mid.val
    hpm htm c cs out hstate hc B R m hB rest hq
  have hl := CodeFullRepeatFuel.path_length_le_root ht p
  refine ⟨m,rest,mid,c,cs,F,a+b,hm,?_,?_,?_⟩
  · exact hq
  · have hmul := Nat.mul_le_mul_right
      (CodeFullRepeatPublic.repeatStepCap root B R) hl
    simp only [Nat.add_mul,one_mul]
    omega
  · rw [padding_run_add a b,hra]
    simpa [out,den] using hrb

theorem done_terminal_output (s : State) (tape : List Bool)
    (B R : Nat) :
    let d := CodeAdminDraw.doneCfg
      (GeneratorCode.normalize s).output.reverse tape B R
    let j : CodeAdminResultJoin.Config :=
      CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
    (Function.update (CodeInterpreterReset.resetBank endpoint.stk)
      CodeFullPadding.tapeSlot []) CodeHeaderDraw.output =
      (GeneratorCode.normalize s).output.reverse := by
  let d := CodeAdminDraw.doneCfg
    (GeneratorCode.normalize s).output.reverse tape B R
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  change (Function.update (CodeInterpreterReset.resetBank endpoint.stk)
      CodeFullPadding.tapeSlot []) CodeHeaderDraw.output = _
  rw [Function.update_of_ne (by
    simp [CodeFullPadding.tapeSlot,CodeHeaderDraw.output,CodeHeaderDraw.d])]
  rw [CodeInterpreterReset.reset_kept _ _ (by
    simp [CodeInterpreterReset.keep,CodeHeaderDraw.output])]
  rfl

theorem done_terminal_tape (S : CodeFullPadding.Stack → List Bool) :
    (Function.update S CodeFullPadding.tapeSlot [])
      CodeFullPadding.tapeSlot = [] := by simp

/-- Read-only observation of the final control and output bank. In particular,
the failure control never exposes a partially accumulated output word. -/
def observed (c : CodeFullPadding.Config) : Option (List Bool) :=
  if CodeFullPadding.doneStatus c.var then
    some (c.stk CodeHeaderDraw.output).reverse else none

theorem done_terminal_observed (s : State) (tape : List Bool)
    (B R : Nat) (bytes : List Bool)
    (hr : GeneratorCode.read s = some bytes) :
    let d := CodeAdminDraw.doneCfg
      (GeneratorCode.normalize s).output.reverse tape B R
    let j : CodeAdminResultJoin.Config :=
      CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
    observed ⟨none,(endpoint.var,none),Function.update
      (CodeInterpreterReset.resetBank endpoint.stk)
      CodeFullPadding.tapeSlot []⟩ = some bytes := by
  let d := CodeAdminDraw.doneCfg
    (GeneratorCode.normalize s).output.reverse tape B R
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  have hstatus : CodeFullPadding.doneStatus
      ((endpoint.var,none) : CodeFullPadding.Control) = true := by
    simp [CodeFullPadding.doneStatus,endpoint,j,d,
      CodeAdminBranchJoin.joinLift,CodeAdminResultJoin.resultCfg,
      BitMachineInline.cfg,CodeDrawResultHandler.savedStatus,
      CodeAdminDraw.doneCfg,CodeAdminDraw.drawControl,
      CodeHeaderDraw.drawInitialControl,
      LoadedTicketMachine.statusStartControl]
  have houtput := done_terminal_output s tape B R
  have hs := (read_some_done s bytes hr).2
  change observed ⟨none,(endpoint.var,none),Function.update
      (CodeInterpreterReset.resetBank endpoint.stk)
      CodeFullPadding.tapeSlot []⟩ = some bytes
  simp only [observed,hstatus,ite_true]
  rw [houtput,hs,List.reverse_reverse]

theorem failure_terminal_observed (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind)
    (tail n a b out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (hq : CappedSampler.runWideBits D B R hB tape.1 = none) :
    let d := CodeAdminDraw.drawResult D B R N hB tape
      kind tail n a b out F
    let j : CodeAdminResultJoin.Config :=
      CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
    observed ⟨none,(endpoint.var,none),
      CodeInterpreterReset.resetBank endpoint.stk⟩ = none := by
  let d := CodeAdminDraw.drawResult D B R N hB tape
    kind tail n a b out F
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  have hsraw := (CodeDrawResultHandler.result_status D B R N hB tape
    kind tail n a b out F).1
  have hf : CodeFullPadding.doneStatus
      ((endpoint.var,none) : CodeFullPadding.Control) = false := by
    change (CodeDrawResultHandler.savedStatus d.var).isNone = false
    rw [hsraw,hq]
    rfl
  change observed ⟨none,(endpoint.var,none),
    CodeInterpreterReset.resetBank endpoint.stk⟩ = none
  simp [observed,hf]

theorem failure_completed_zero (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind)
    (tail n a b out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (hq : CappedSampler.runWideBits D B R hB tape.1 = none)
    (zero : List Bool) :
    let d := CodeAdminDraw.drawResult D B R N hB tape
      kind tail n a b out F
    let j : CodeAdminResultJoin.Config :=
      CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
    CappedSampler.completed
      (observed ⟨none,(endpoint.var,none),
        CodeInterpreterReset.resetBank endpoint.stk⟩) zero = zero := by
  simpa only [CappedSampler.completed,Option.getD_none]
    using congrArg (fun o : Option (List Bool) => o.getD zero)
      (failure_terminal_observed D B R N hB tape kind tail n a b out F hq)

/-- Public Appendix-D schedules always allocate at least one rejection
attempt, including the zero-draw schedule. -/
theorem scheduled_attempts_pos (N : Nat) :
    0 < Paper2.rejectionAttemptCap N := by
  simp [Paper2.rejectionAttemptCap]

theorem capped_success_observed (root : Code) (M B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (N : Nat) (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (t : CappedSampler.Adaptive.Tape B R N)
    (u : BoundedState M) (bytes : List Bool)
    (hu : capped B R hMB N s t = some u)
    (hr : GeneratorCode.read u.val = some bytes) :
    ∃ clock ≤ (codeSize root+1) *
      CodeFullRepeatPublic.repeatStepCap root B R + N*(R*B)+2,
      let c := CodeFullPadding.run clock
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N t).val B R)
      c.l = none ∧ observed c = some bytes ∧
        c.stk CodeFullPadding.tapeSlot = [] := by
  obtain ⟨m,rest,mid,clock,hm,hread,hclock,hrun⟩ :=
    capped_success_run root M B R hMB hR N s hp ht t u bytes hu hr
  refine ⟨clock,hclock,?_,?_,?_⟩
  · rw [hrun]
  · rw [hrun]
    exact done_terminal_observed mid.val
      (RecursiveSamplingTape.writeTape B R m rest).val B R bytes hread
  · rw [hrun]
    simp

theorem capped_failure_observed (root : Code) (M B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (N : Nat) (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (t : CappedSampler.Adaptive.Tape B R N)
    (hf : capped B R hMB N s t = none)
    (zero : List Bool) :
    ∃ clock ≤ (codeSize root+1) *
      CodeFullRepeatPublic.repeatStepCap root B R,
      let c := CodeFullPadding.run clock
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N t).val B R)
      c.l = none ∧ observed c = none ∧
        CappedSampler.completed (observed c) zero = zero := by
  obtain ⟨m,rest,mid,c,cs,F,clock,hm,hq,hclock,hrun⟩ :=
    capped_failure_run root M B R hMB hR N s hp ht t hf
  refine ⟨clock,hclock,?_,?_,?_⟩
  · rw [hrun]
  · rw [hrun]
    exact failure_terminal_observed
      (request (GeneratorCode.normalize mid.val)) B R m
      (den_width hMB mid) rest (CodeHeaderMachine.headerKind c)
      (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
      (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
      (CodeHeaderMachine.headerB c)
      (GeneratorCode.normalize mid.val).output.reverse F hq
  · rw [hrun]
    exact failure_completed_zero
      (request (GeneratorCode.normalize mid.val)) B R m
      (den_width hMB mid) rest (CodeHeaderMachine.headerKind c)
      (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
      (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
      (CodeHeaderMachine.headerB c)
      (GeneratorCode.normalize mid.val).output.reverse F hq zero

#print axioms writeTape_cons
#print axioms capped_done
#print axioms zero_attempt_failure
#print axioms accepted_of_draw
#print axioms source_success_path
#print axioms accepted_run_padding_public
#print axioms path_run_padding_public
#print axioms done_drains_public
#print axioms source_failure_path
#print axioms failing_draw_halts_public
#print axioms capped_success_run
#print axioms capped_failure_run
#print axioms done_terminal_output
#print axioms done_terminal_observed
#print axioms failure_terminal_observed
#print axioms failure_completed_zero
#print axioms scheduled_attempts_pos
#print axioms capped_success_observed
#print axioms capped_failure_observed

end
end Paper2.CodeFullRun
