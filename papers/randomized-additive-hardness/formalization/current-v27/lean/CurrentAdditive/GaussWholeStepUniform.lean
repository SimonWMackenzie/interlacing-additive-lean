import CurrentAdditive.GaussWholeStepCorrect
import CurrentAdditive.GaussWholeStepClockCaps
import CurrentAdditive.GaussCanonicalPacketClock

namespace CurrentAdditive.GaussWholeStepUniform
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low frame)
open GaussWholeStepProgram GaussWholeStepSizeCaps GaussWholeStepClockCaps

theorem search_bank_bound {m k : Nat} (s : GaussControlTrace.State m k)
    (a : Nat) (ha : a≤GaussPreparedGuard64.clock s+GaussGuardedFront64.activeClock s+2)
    (vf : GaussFlagSearch.Control) (Sf : Fin 32 → List Bool)
    (hfront : run a (initial (GaussControlTrace.statePacket s))=
      ⟨some .afterFront,eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)),
        frame (GaussPivotSearchHigh64.searched s Sf)⟩) :
    ∀j,((GaussPivotSearchHigh64.searched s Sf) j).length≤
      frontBank (GaussControlTrace.statePacket s).length := by
  intro j
  have h:=run_bank_length (GaussControlTrace.statePacket s) a (low j)
  rw [hfront] at h
  simp only [GaussSearchGridInvoke.frame_at] at h
  exact h.trans (bankCap_mono (ha.trans (front_clock_le s)))

theorem noPivot_outputs {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=none) :
    machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s))
      (wholeClock (GaussControlTrace.statePacket s).length) := by
  obtain ⟨a,ha,vf,Sf,hfront,t,ht,hout⟩:=GaussWholeStepNoPivot.detailed_noPivot s hr hc hp
  let n:=(GaussControlTrace.statePacket s).length
  let S:=GaussPivotSearchHigh64.searched s Sf
  have hb : ∀j,(S j).length≤rewriteBank n := fun j =>
    (search_bank_bound s a ha vf Sf hfront j).trans (frontBank_le_rewriteBank n)
  have hf:=noPivot_clock_le s S (rewriteBank n) hb
  have h62:=hb 62
  have hn:=GaussCanonicalFieldClock.noPivot_packet_length s
  have ha':=ha.trans (front_clock_le s)
  apply BitMachine.outputsWithin_mono machine hout
  apply ht.trans
  change a+2+GaussNextStateFieldsFrame64.noPivotClock s S (S 22)+(S 62).length+
    2*(GaussControlTrace.statePacket (GaussBranchFields32.noPivotState s)).length+8≤wholeClock n
  unfold wholeClock
  dsimp only [n] at *
  omega

theorem pivot_outputs {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩=some pivot)
    (hcount : s.r=s.pivots.length) :
    machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s))
      (wholeClock (GaussControlTrace.statePacket s).length) := by
  obtain ⟨a,ha,vf,Sf,hfront,d,hd,sf,hrew,t,ht,hout⟩:=
    GaussWholeStepPivot.detailed_pivot s hr hc pivot hp hcount
  let n:=(GaussControlTrace.statePacket s).length
  let S:=GaussPivotSearchHigh64.searched s Sf
  let answer:=GaussGridPreparedInput.answer s.B ⟨s.r,hr⟩ pivot ⟨s.c,hc⟩
  let R:=Function.update (GaussSearchGridInvoke.serialized64 S sf) 22 answer
  have hs : ∀j,(S j).length≤frontBank n:=search_bank_bound s a ha vf Sf hfront
  have hd' : d≤rewriteBudget n:=hd.trans (rewrite_clock_le S (frontBank n) hs)
  have hR : ∀j,(R j).length≤rewriteBank n := by
    intro j
    have hg:=BitMachineStackGrowth.run_growth program
      (⟨some (.rewrite GaussSearchGridInvoke.start),eRewrite GaussSearchGridInvoke.control,
        frame S⟩ : Config) d (low j)
    change ((run d _).stk (low j)).length≤_ at hg
    rw [hrew] at hg
    simp only [GaussSearchGridInvoke.frame_at] at hg
    change (R j).length≤(S j).length+pushConstant*d at hg
    apply hg.trans
    unfold rewriteBank frontBank bankCap at *
    have hd'' := Nat.mul_le_mul_left pushConstant hd'
    have hj:=hs j
    simp only [Nat.mul_add] at *
    omega
  have hmatrix : answer=GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B := by
    simp [answer,GaussGridPreparedInput.answer,GaussControlTrace.step,hr,hc,hp,
      MaterializedGauss.materialize_eq]
  have h22 : R 22=GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B := by
    simp [R,hmatrix]
  have hf:=pivot_clock_le s R (rewriteBank n) hr hc hcount hR h22
  have hm : (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B).length≤rewriteBank n := by
    rw [←h22]; exact hR 22
  have hn:=GaussCanonicalFieldClock.nextPacket_pivot_linear s hr hc pivot hp hcount
  have hn' : (GaussControlTrace.statePacket (GaussControlTrace.step s)).length≤
      200*(n+rewriteBank n+1) := by exact hn.trans (by gcongr)
  have h62:=hR 62
  have ha':=ha.trans (front_clock_le s)
  apply BitMachine.outputsWithin_mono machine hout
  apply ht.trans
  change a+2+d+1+GaussNextStateFields64.pivotClock s R hr hc+(R 62).length+
    2*(GaussControlTrace.statePacket (GaussControlTrace.step s)).length+8≤wholeClock n
  unfold wholeClock
  dsimp only [R,answer,S,n] at *
  omega

/-- One fixed finite instruction table implements a whole Gauss step, with
one polynomial in the original state bytes chosen before every typed input. -/
theorem outputs_step {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) (hcount : s.r=s.pivots.length) :
    machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s))
      (wholeClock (GaussControlTrace.statePacket s).length) := by
  by_cases hr : s.r < m
  · cases hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩ with
    | none => exact noPivot_outputs s hr hc hp
    | some pivot => exact pivot_outputs s hr hc pivot hp hcount
  · have hout:=GaussWholeStepTerminal.terminal_outputs s hr
    have hfront:=front_clock_le s
    have ht : GaussWholeStepTerminal.terminalClock s≤frontCap (GaussControlTrace.statePacket s).length := by
      unfold GaussWholeStepTerminal.terminalClock
      unfold GaussGuardedFront64.activeClock at hfront
      omega
    have ht' : frontCap (GaussControlTrace.statePacket s).length≤
        wholeClock (GaussControlTrace.statePacket s).length := by unfold wholeClock; omega
    apply BitMachine.outputsWithin_mono machine _ (ht.trans ht')
    simpa only [GaussControlTrace.step,hr,↓reduceDIte] using hout

theorem uniform_outputs : ∃C e : Nat,∀{m k : Nat} (s : GaussControlTrace.State m k),
    s.c < k → s.r=s.pivots.length →
    machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s))
      (C*((GaussControlTrace.statePacket s).length+1)^e) := by
  obtain ⟨C,e,hclock⟩:=whole_polynomial
  refine ⟨C,e,?_⟩
  intro m k s hc hcount
  exact BitMachine.outputsWithin_mono machine (outputs_step s hc hcount)
    (by simpa only [Nat.zero_add] using hclock 0 (GaussControlTrace.statePacket s).length)

def coefficient : Nat := Classical.choose uniform_outputs
def exponent : Nat := Classical.choose (Classical.choose_spec uniform_outputs)
def polynomialClock (n : Nat) : Nat := coefficient*(n+1)^exponent

theorem outputs_polynomial {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) (hcount : s.r=s.pivots.length) :
    machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s))
      (polynomialClock (GaussControlTrace.statePacket s).length) :=
  Classical.choose_spec (Classical.choose_spec uniform_outputs) s hc hcount

#print axioms noPivot_outputs
#print axioms pivot_outputs
#print axioms outputs_step
#print axioms uniform_outputs
end
end CurrentAdditive.GaussWholeStepUniform
