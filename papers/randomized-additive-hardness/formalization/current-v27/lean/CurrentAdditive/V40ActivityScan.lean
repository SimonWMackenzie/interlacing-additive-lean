import CurrentAdditive.V40PackedProgram
import CurrentAdditive.EdgeScanRunBound
import CurrentAdditive.OrdinaryBitBranch
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding
import EthInapproximability.CurrentPaper.BankFieldProjection
import Paper2.StepXGrowth

/-! The ordinary-input activity cell machine calls the actual graph-byte
scanner. A literal dispatch returns the scanned rank on an active cell and
the retained unary s on an inactive cell. -/
namespace CurrentAdditive.V40ActivityScan
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper BitMachineEncoding
open BitMachineStackEmbedding LiteralEdgeScanJoin LiteralEdgeScanFuel
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 65536
set_option maxSynthPendingDepth 128
deriving instance Fintype for Paper2.CanonicalEndpointRankMachine.Control

private abbrev ProgramLabel {K L V : Type} (_P : L → TM2.Stmt (fun _ : K => Bool) L V) := L
private abbrev ProgramControl {K L V : Type} (_P : L → TM2.Stmt (fun _ : K => Bool) L V) := V
abbrev Label := ProgramLabel full
abbrev Control := ProgramControl full
abbrev K := JJ ⊕ Fin 1
def scanSlots : JJ ↪ K := ⟨Sum.inl,Sum.inl_injective⟩
def program (l : Label) := stackStmt scanSlots (full l)
def start : Label := BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel .start))
def control : Control :=
  (testCtl,((none:Option Bool),((),(opCtl,RankRun.startCtl))))
def initial (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) : K → List Bool :=
  Sum.elim (W0 g a r ig xv kb) (fun _ => List.replicate s true)
def final (g : EncodedGraph.Graph) (hg : g.Valid) (s a r ig xv : Nat) (kb : Bool) : K → List Bool :=
  Sum.elim (scanExit g hg a r ig xv kb) (fun _ => List.replicate s true)
def input (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :=
  V40PackedProgram.pack (initial g s a r ig xv kb)
def flagPort : K := .inl actC
def rankPort : K := .inl (.inr (.inr 3))
def sentinelPort : K := .inr 0
def gateMachine := V40PackedProgram.machine program start control flagPort
def rankMachine := V40PackedProgram.machine program start control rankPort
def sentinelMachine := BankFieldProjection.machine (V40PackedProgram.numbering sentinelPort)
def unaryMachine := OrdinaryBitBranch.machine gateMachine sentinelMachine rankMachine
def machine := BitMachineComposition.composition unaryMachine UnaryBinaryEncoding.machine

def scanClock (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :=
  (2*Fintype.card K+1)*((input g s a r ig xv kb).length+1)+1000*(bankBits g a r ig xv kb+1)^3+1
def branchClock (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :=
  OrdinaryBitBranch.invocationBound gateMachine (input g s a r ig xv kb).length (scanClock g s a r ig xv kb)+
  OrdinaryBitBranch.invocationBound sentinelMachine (input g s a r ig xv kb).length
    ((2*Fintype.card K+4)*((input g s a r ig xv kb).length+1))+
  OrdinaryBitBranch.invocationBound rankMachine (input g s a r ig xv kb).length (scanClock g s a r ig xv kb)+1
def clock (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :=
  branchClock g s a r ig xv kb+2*(s+xv+2)+2+
    UnaryBinaryEncoding.coefficient*(s+xv+3)^2

theorem scan_run (g : EncodedGraph.Graph) (hg : g.Valid) (s a r ig xv : Nat) (kb : Bool) :
    ∃t ≤ 1000*(bankBits g a r ig xv kb+1)^3, ∃v,
      ((advance program)^[t])
        (⟨some start,control,initial g s a r ig xv kb⟩ : TM2.Cfg (fun _ : K => Bool) Label Control)=
          ⟨none,v,final g hg s a r ig xv kb⟩ := by
  obtain ⟨t,ht,v,hr⟩:=join_cubic g hg a r ig xv kb
  let c : TM2.Cfg (fun _ : JJ => Bool) Label Control:=⟨some start,control,W0 g a r ig xv kb⟩
  have he:=BitMachineStackRun.run scanSlots (initial g s a r ig xv kb) full c t
  change ((advance full)^[t]) c=⟨none,v,scanExit g hg a r ig xv kb⟩ at hr
  rw [hr] at he
  have hin : bank scanSlots (initial g s a r ig xv kb) (W0 g a r ig xv kb)=initial g s a r ig xv kb :=
    bank_eq_self _ _ _ (fun _ => rfl)
  have hout : bank scanSlots (initial g s a r ig xv kb) (scanExit g hg a r ig xv kb)=final g hg s a r ig xv kb := by
    funext z
    cases z with
    | inl z => exact bank_at _ _ _ z
    | inr z => exact bank_outside _ _ _ _ (by rintro ⟨i,h⟩; cases h)
  simp only [stackCfg,c,hin,hout] at he
  exact ⟨t,ht,v,he⟩

theorem port_outputs (g : EncodedGraph.Graph) (hg : g.Valid)
    (s a r ig xv : Nat) (kb : Bool) (port : K) :
    (V40PackedProgram.machine program start control port).OutputsWithin
      (input g s a r ig xv kb) (final g hg s a r ig xv kb port) (scanClock g s a r ig xv kb) := by
  obtain ⟨t,ht,v,hr⟩:=scan_run g hg s a r ig xv kb
  exact V40PackedProgram.outputs program start control port _ _ v t _ ht hr

theorem scan_value {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :
    ∃b rank, final g hg s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight flagPort=[b] ∧
      (b=true → final g hg s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight rankPort=
        List.replicate rank true) ∧ rank ≤ CanonicalEndpointRankBridge.itemValue z+2 ∧
      (match LiteralEdgeEncoder.activity hs (LiteralEdgeEncoder.edge g hg) (ig,z) a with
        | some p => p.val | none => s) = if b then rank else s := by
  by_cases h : 0<g.edges.length ∧ a.val/r/g.edges.length=ig.val
  · obtain ⟨b,rank,hb,hr,hv⟩:=LiteralEdgeScanValue.scan_value_some g hg hs ig z a h
    have hb' : final g hg s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight flagPort=[b] := by
      simpa only [final,flagPort,Sum.elim_inl,scanExit,dif_pos h] using hb
    have hr' : final g hg s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight rankPort=
        List.replicate rank true := by
      simpa only [final,rankPort,Sum.elim_inl,scanExit,dif_pos h] using hr
    have hrk : rank ≤ CanonicalEndpointRankBridge.itemValue z+2 := by
      have he:=Wtrue_rank g hg a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight
        ⟨a.val/r%g.edges.length,Nat.mod_lt _ h.1⟩
      rw [hr] at he
      have he' : rank=CanonicalEndpointRankMachine.semanticRank (RankRun.kindOfNat 0)
          (RankRun.itemOfBool z.isRight)
          (CanonicalEdgeTape.graphEdge g hg ⟨a.val/r%g.edges.length,Nat.mod_lt _ h.1⟩ false).val
          (CanonicalEdgeTape.graphEdge g hg ⟨a.val/r%g.edges.length,Nat.mod_lt _ h.1⟩ true).val
          (CanonicalEndpointRankBridge.itemValue z) := by
        simpa using congrArg List.length he
      rw [he']
      exact semanticRank_le _ _ _ _
    refine ⟨b,rank,hb',fun _ => hr',hrk,?_⟩
    cases ha : LiteralEdgeEncoder.activity hs (LiteralEdgeEncoder.edge g hg) (ig,z) a with
    | none => cases b <;> simp_all
    | some p => cases b <;> simp_all
  · refine ⟨false,0,?_,by simp,by omega,?_⟩
    · simp [final,flagPort,scanExit,h,Function.update_apply,actC,ansC]
    · rw [LiteralEdgeScanValue.scan_value_none g hg hs ig z a h]
      rfl

theorem outputs {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :
    let value := match LiteralEdgeEncoder.activity hs (LiteralEdgeEncoder.edge g hg) (ig,z) a with
      | some p => p.val | none => s
    machine.OutputsWithin (input g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight)
      value.bits (clock g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight) := by
  intro value
  let x:=input g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight
  let T:=scanClock g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight
  obtain ⟨b,rank,hb,hr,hrk,hv⟩:=scan_value g hg hs ig z a
  have hgout : gateMachine.OutputsWithin x [b] T := by
    simpa only [hb] using port_outputs g hg s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight flagPort
  have hp : (OrdinaryBitBranch.selected sentinelMachine rankMachine b).OutputsWithin x
      (List.replicate value true)
      (if b then T else (2*Fintype.card K+4)*(x.length+1)) := by
    cases b with
    | false =>
      have he : BankFieldProjection.result (V40PackedProgram.numbering sentinelPort) x=List.replicate s true := by
        simp [x,input,V40PackedProgram.pack,BankFieldProjection.result_encode,initial,sentinelPort]
      have hh:=BankFieldProjection.outputs (V40PackedProgram.numbering sentinelPort) x
      change value=s at hv
      rw [hv]
      simpa only [OrdinaryBitBranch.selected,Bool.false_eq_true,↓reduceIte,he] using hh
    | true =>
      have hh:=port_outputs g hg s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight rankPort
      change value=rank at hv
      rw [hv]
      simpa only [OrdinaryBitBranch.selected,↓reduceIte,hr rfl] using hh
  have hbout:=OrdinaryBitBranch.outputsWithin gateMachine sentinelMachine rankMachine x
    (List.replicate value true) b T _ hgout hp
  have ht : OrdinaryBitBranch.invocationBound gateMachine x.length T+
      OrdinaryBitBranch.invocationBound (OrdinaryBitBranch.selected sentinelMachine rankMachine b) x.length
        (if b then T else (2*Fintype.card K+4)*(x.length+1))+1 ≤
      branchClock g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight := by
    cases b <;> simp [branchClock,OrdinaryBitBranch.selected,T,x] <;> omega
  have hu:=BitMachine.outputsWithin_mono unaryMachine hbout ht
  have hh:=BitMachineComposition.composition_outputsWithin unaryMachine UnaryBinaryEncoding.machine hu
    (UnaryBinaryEncoding.outputs (List.replicate value true))
  apply BitMachine.outputsWithin_mono machine (by simpa only [List.length_replicate] using hh)
  have hval : value ≤ s+CanonicalEndpointRankBridge.itemValue z+2 := by
    dsimp only [value]
    rw [hv]
    cases b <;> simp <;> omega
  have hpow:=Nat.pow_le_pow_left (show value+1 ≤ s+CanonicalEndpointRankBridge.itemValue z+3 by omega) 2
  have hmul:=Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hpow
  dsimp only [clock]
  omega

#print axioms outputs
end
end CurrentAdditive.V40ActivityScan
