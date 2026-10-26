import CurrentAdditive.GaussPostloopEndpoint
import CurrentAdditive.CodeDPostGaussStopping

namespace CurrentAdditive.GaussPostloopDecision
noncomputable section

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open GaussPostloopSerialized GaussCellPolynomialClock
open CurrentAdditive.MinimumRatioContext

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

private abbrev ProgramControl {K L V : Type} (_ : L → TM2.Stmt (fun _ : K => Bool) L V) := V
abbrev StopControl := ProgramControl CodeDPostGaussStopping.program
abbrev StopLabel := CodeDPostGaussStopping.Label ⊕ Unit
def flagCell : Stack := .inr 1
def stopSlots : CodeDPostGaussStopping.Bank ↪ Stack :=
  ⟨fun i => .inl (GaussWideVectorInvoke.oldEmbed i),by
    intro a b h
    exact GaussWideVectorInvoke.oldEmbed.injective (Sum.inl.inj h)⟩
def bit (v : StopControl) : Bool := match v.2 with
  | .choose (some b) => b
  | _ => false
def stopProgram : StopLabel → TM2.Stmt (fun _ : Stack => Bool) StopLabel StopControl
  | .inl l => BitMachineStackEmbedding.stmt stopSlots Sum.inl id id (some (.inr ()))
      (CodeDPostGaussStopping.program l)
  | .inr _ => .push flagCell bit .halt
def stopStart : StopLabel := .inl CodeDPostGaussStopping.start

theorem stop_bank (S : CodeDPostGaussStopping.Bank → List Bool) :
    BitMachineStackEmbedding.bank stopSlots (fun _ => []) S=
      Sum.elim (GaussWideVectorInvoke.wide S) (fun _ => []) := by
  funext z
  cases z with
  | inr j =>
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨i,hi⟩
    cases hi
  | inl b =>
    by_cases h : ∃ i,GaussWideVectorInvoke.oldEmbed i=b
    · obtain ⟨i,rfl⟩:=h
      change BitMachineStackEmbedding.bank stopSlots (fun _ => []) S (stopSlots i)=_
      rw [BitMachineStackEmbedding.bank_at]
      exact (GaussWideVectorInvoke.wide_at S i).symm
    · have ho : ¬∃i,stopSlots i=Sum.inl b := by
        rintro ⟨i,hi⟩
        exact h ⟨i,Sum.inl.inj hi⟩
      rw [BitMachineStackEmbedding.bank_outside stopSlots (fun _ => []) S _ ho]
      exact (BitMachineStackEmbedding.bank_outside GaussWideVectorInvoke.oldEmbed (fun _ => []) S b h).symm

def program := BitMachineRawSequence.program parserProgram stopProgram stopStart
  (none:Option Bool) CodeDPostGaussStopping.initialControl
abbrev Label := BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 2) StopLabel
def start : Label := BitMachineRawSequence.leftLabel (.scan 0)
def control := ((none:Option Bool),CodeDPostGaussStopping.initialControl)
def machine : BitMachine.Machine := ofFinite inputCell flagCell start control program

theorem actual_outputs {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j,A i j=0 ∨ A i j=1) :
    let s:=GaussControlTrace.after (fun i j => (A i j:ℚ)) k
    let f:=GaussPivotPrefixPhysical.prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
    machine.OutputsWithin (packet (GaussControlTrace.statePacket s) k) [decide (f<k)]
      (5*((packet (GaussControlTrace.statePacket s) k).length+1)+
        CodeDPostGaussStopping.selectorClock (GaussControlTrace.statePacket s) m k+
        CodeDIndependenceGuardRun.clock f k+4) ∧
      (SequentialTotality.typedFree s.pivots=none ↔ ¬f<k) := by
  let s:=GaussControlTrace.after (fun i j => (A i j:ℚ)) k
  let f:=GaussPivotPrefixPhysical.prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
  let S:=GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
  let T:=Function.update (Function.update S GaussStateMatrixContext.selectorSlots.target
    (List.replicate f true)) GaussStateMatrixContext.matrixSlots.target (GaussPhysical.encodeTypedMatrix s.B)
  let v : StopControl:=((MachineInvokeFull.control GaussStateMatrixContext.selectorSlots,
    MachineInvokeFull.control GaussStateMatrixContext.matrixSlots),.choose (some (decide (f<k))))
  obtain ⟨b,hb,hstop,hnone⟩:=CodeDPostGaussStopping.outputs A h01
  let c : TM2.Cfg (fun _ : CodeDPostGaussStopping.Bank => Bool) _ _ :=
    ⟨some CodeDPostGaussStopping.start,CodeDPostGaussStopping.initialControl,S⟩
  have hr : ((advance CodeDPostGaussStopping.program)^[b]) c=⟨none,v,T⟩ := hstop
  obtain ⟨u,hu,hlift⟩:=BitMachineStackEmbedding.outputs stopSlots (fun _ => []) Sum.inl id id
    (by intro; rfl) (some (.inr ())) CodeDPostGaussStopping.program stopProgram
    (by intro; rfl) c b (by rw [hr])
  rw [hr] at hlift
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,
    id_eq,c,stop_bank] at hlift
  have hflag : (Sum.elim (GaussWideVectorInvoke.wide T) (fun _ => [])) flagCell=[] := rfl
  have hemit : advance stopProgram
      (⟨some (.inr ()),v,Sum.elim (GaussWideVectorInvoke.wide T) (fun _ => [])⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _)=
      ⟨none,v,Function.update (Sum.elim (GaussWideVectorInvoke.wide T) (fun _ => [])) flagCell [decide (f<k)]⟩ := by
    simp [advance,stopProgram,TM2.step,TM2.stepAux,bit,v,hflag]
  have hbody : ((advance stopProgram)^[u+1])
      (⟨some stopStart,CodeDPostGaussStopping.initialControl,installed (GaussControlTrace.statePacket s) k⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _)=
      ⟨none,v,Function.update (Sum.elim (GaussWideVectorInvoke.wide T) (fun _ => [])) flagCell [decide (f<k)]⟩ := by
    have hlift' : ((advance stopProgram)^[u])
        (⟨some stopStart,CodeDPostGaussStopping.initialControl,installed (GaussControlTrace.statePacket s) k⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _)=
        ⟨some (.inr ()),v,Sum.elim (GaussWideVectorInvoke.wide T) (fun _ => [])⟩ := hlift
    rw [show u+1=1+u by omega,Function.iterate_add_apply]
    change advance stopProgram (((advance stopProgram)^[u]) _) = _
    rw [hlift']
    exact hemit
  obtain ⟨a,ha,hparse⟩:=parse_run (words (GaussControlTrace.statePacket s) k)
  rw [parsed_exact] at hparse
  obtain ⟨t,ht,hfull⟩:=BitMachineRawSequence.runs parserProgram stopProgram (.scan 0) stopStart
    (none:Option Bool) (some true) CodeDPostGaussStopping.initialControl v
    (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2) (none:Option Bool)
      (packet (GaussControlTrace.statePacket s) k)).stk
    (installed (GaussControlTrace.statePacket s) k)
    (Function.update (Sum.elim (GaussWideVectorInvoke.wide T) (fun _ => [])) flagCell [decide (f<k)])
    a (u+1) hparse hbody
  have hfull' : ((advance program)^[t]) (rawInit inputCell start control (packet (GaussControlTrace.statePacket s) k))=
      ⟨none,((none:Option Bool),v),Function.update (Sum.elim (GaussWideVectorInvoke.wide T) (fun _ => [])) flagCell [decide (f<k)]⟩ := hfull
  constructor
  · apply outputsWithin_of_raw_run inputCell flagCell start control program _ _ t _
    · dsimp only [s,f,packet] at ha hb ⊢
      omega
    · rw [hfull']
    · rw [hfull']
      simp [s,f]
  · exact hnone

def clock (n : Nat) : Nat := 25*(n+1)+GaussPostloopClock.workCap n+4

theorem clock_polynomial : PolynomialBound (fun _ n => clock n) := by
  unfold clock
  exact add (add (mul (constant 25) (add second (constant 1))) GaussPostloopClock.workCap_polynomial) (constant 4)

theorem uniform_outputs : ∃ C e : Nat,
    ∀ {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ) (h01 : ∀ i j,A i j=0 ∨ A i j=1),
    let s:=GaussControlTrace.after (fun i j => (A i j:ℚ)) k
    let f:=GaussPivotPrefixPhysical.prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
    machine.OutputsWithin (packet (GaussControlTrace.statePacket s) k) [decide (f<k)]
      (C*((packet (GaussControlTrace.statePacket s) k).length+1)^e) ∧
      (SequentialTotality.typedFree s.pivots=none ↔ ¬f<k) := by
  obtain ⟨C,e,hpoly⟩:=clock_polynomial
  refine ⟨C,e,?_⟩
  intro m k A h01
  let s:=GaussControlTrace.after (fun i j => (A i j:ℚ)) k
  let f:=GaussPivotPrefixPhysical.prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
  let n:=(packet (GaussControlTrace.statePacket s) k).length
  obtain ⟨hout,hnone⟩:=actual_outputs A h01
  obtain ⟨hstate,hB,hm,hk⟩:=GaussPostloopEndpoint.packet_bounds s
  have hs : (GaussControlTrace.statePacket s).length ≤ GaussActualWorkListClock.stateCap m k := by
    simpa [s,GaussActualWorkListClock.stateCap,GaussPivotPrefixClock.stateCap] using
      GaussControlTrace.actual_statePacket_length A h01 k (by omega)
  have hsel:=GaussActualWorkListClock.uniformBound_mono GaussStateMatrixContext.Sel
    (xs:=GaussControlTrace.statePacket s) (ys:=List.replicate (GaussActualWorkListClock.stateCap m k) true)
    (a:=GaussPivotPrefixClock.prefixClock m k) (b:=GaussPivotPrefixClock.prefixClock m k)
    (by simpa using hs) le_rfl
  have hproj:=GaussActualWorkListClock.uniformBound_mono GaussStateMatrixContext.Proj
    (xs:=GaussControlTrace.statePacket s) (ys:=List.replicate (GaussActualWorkListClock.stateCap m k) true)
    (a:=12*((GaussControlTrace.statePacket s).length+1)) (b:=12*(GaussActualWorkListClock.stateCap m k+1))
    (by simpa using hs) (by omega)
  have hselector : CodeDPostGaussStopping.selectorClock (GaussControlTrace.statePacket s) m k ≤ GaussPostloopClock.workCap n := by
    have hw:=GaussPostloopClock.workCap_mono hm hk
    change GaussActualWorkListClock.clock m k ≤ GaussPostloopClock.workCap n at hw
    unfold CodeDPostGaussStopping.selectorClock
    apply (show _ ≤ GaussActualWorkListClock.clock m k from by unfold GaussActualWorkListClock.clock; omega).trans hw
  have hprefix : f ≤ m := by
    have ht : ((GaussPivotPrefixPhysical.pivotFlags (GaussPivotPacketBridge.natPivots s.pivots)).takeWhile id).length ≤ s.pivots.length := by
      calc _ ≤ (GaussPivotPrefixPhysical.pivotFlags (GaussPivotPacketBridge.natPivots s.pivots)).length :=
             (List.takeWhile_sublist id).length_le
           _ = _ := by simp [GaussPivotPrefixPhysical.pivotFlags,GaussPivotPacketBridge.natPivots]
    have hp:=GaussControlTrace.after_pivotCount (fun i j => (A i j:ℚ)) k
    have hr:=GaussControlTrace.after_row_le (fun i j => (A i j:ℚ)) k
    change s.r=s.pivots.length at hp
    change s.r ≤ m at hr
    exact ht.trans (by omega)
  have hguard : CodeDIndependenceGuardRun.clock f k ≤ 20*(n+1) := by
    have hf:=hprefix.trans hm
    have hmax : max f k ≤ n := max_le hf hk
    unfold CodeDIndependenceGuardRun.clock
    omega
  refine ⟨BitMachine.outputsWithin_mono _ hout ?_,hnone⟩
  have hp:=hpoly 0 n
  simp only [Nat.zero_add] at hp
  apply (show _ ≤ clock n from by
    unfold clock
    dsimp only [s,f,n] at hselector hguard ⊢
    omega).trans hp

#print axioms actual_outputs
#print axioms uniform_outputs

end
end CurrentAdditive.GaussPostloopDecision
