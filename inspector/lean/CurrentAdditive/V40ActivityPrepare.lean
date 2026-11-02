import CurrentAdditive.V40SourceLocal
import CurrentAdditive.V40ActivityScan

namespace CurrentAdditive.V40ActivityPrepare
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open PhysicalProducer V40ActivityScan
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxSynthPendingDepth 128
abbrev P:=PhysicalProducer.Producer
def empty : P:=V40SeedProducer.constant []
def decoder : Fin 14 → P:=![PhysicalProducer.projection (1:Fin 8),PhysicalProducer.projection (2:Fin 8),PhysicalProducer.projection (3:Fin 8),
  empty,empty,empty,empty,empty,empty,empty,empty,empty,PhysicalProducer.projection (4:Fin 8),empty]
def graphFields : Fin 8 → P:=![PhysicalProducer.projection (0:Fin 8),empty,empty,empty,empty,empty,empty,empty]
def graphLayout : EndpointOperands.KE → P:=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim graphFields (fun _=>empty)) (fun _=>empty)) (fun _=>empty))
    (fun _=>empty)
def terminated : P:=concat (PhysicalProducer.projection (5:Fin 8)) (V40SeedProducer.constant [false])
def rankFields : Fin 7 → P:=![empty,empty,terminated,empty,empty,PhysicalProducer.projection (6:Fin 8),empty]
def layout : V40ActivityScan.K → P:=
  Sum.elim (Sum.elim decoder (Sum.elim graphLayout rankFields)) (fun _=>PhysicalProducer.projection (7:Fin 8))
def producer : P:=V40SourceLocal.physicalBank (fun i=>layout ((V40PackedProgram.numbering (K:=V40ActivityScan.K)).symm i))

def raw (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :=
  BitMachineBankCodec.encode ![EncodedGraph.encode g,List.replicate a true,List.replicate r true,
    List.replicate g.edges.length true,List.replicate ig true,List.replicate xv true,[kb],List.replicate s true]

macro "finish_layout" : tactic => `(tactic|
  simp [layout,decoder,graphLayout,graphFields,rankFields,terminated,concat,compose,
    PhysicalProducer.projection,empty,V40SeedProducer.constant,raw,BankFieldProjection.result_encode,
    V40ActivityScan.initial,LiteralEdgeScanJoin.W0,LiteralEdgeDecodeMachine.initialBank,
    LiteralEdgeDecodeDependency.u,EndpointOperands.entry,GraphPrefixBind.initBank,
    PublicGraphEndpointMachine.initialBank,SourceNormalizationMachineDecode.start,
    RankRun.RB,CanonicalEndpointRankMachine.unaryWord])

theorem layout_result (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) (j : V40ActivityScan.K) :
    (layout j).result (raw g s a r ig xv kb)=V40ActivityScan.initial g s a r ig xv kb j := by
  rcases j with j|j
  · rcases j with j|j
    · fin_cases j <;> finish_layout
    · rcases j with j|j
      · rcases j with j|j
        · rcases j with j|j
          · rcases j with j|j
            · rcases j with j|j
              · fin_cases j <;> finish_layout
              · fin_cases j <;> finish_layout
            · fin_cases j <;> finish_layout
          · rcases j with j|j <;> fin_cases j <;> finish_layout
        · fin_cases j <;> finish_layout
      · fin_cases j <;> finish_layout
  · fin_cases j <;> finish_layout

theorem result (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :
    producer.result (raw g s a r ig xv kb)=V40ActivityScan.input g s a r ig xv kb := by
  rw [producer,V40SourceLocal.physicalBank_result]
  apply congrArg BitMachineBankCodec.encode
  funext i
  exact layout_result g s a r ig xv kb _

def machine:=BitMachineComposition.composition producer.machine V40ActivityScan.machine
def clock (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :=
  producer.coefficient*((raw g s a r ig xv kb).length+1)^producer.degree+
  2*(V40ActivityScan.input g s a r ig xv kb).length+2+V40ActivityScan.clock g s a r ig xv kb

theorem outputs {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :
    let value:=match LiteralEdgeEncoder.activity hs (LiteralEdgeEncoder.edge g hg) (ig,z) a with
      | some p=>p.val | none=>s
    machine.OutputsWithin (raw g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight)
      value.bits (clock g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight) := by
  have h:=V40ActivityScan.outputs g hg hs ig z a
  rw [←result] at h
  have hh:=BitMachineComposition.composition_outputsWithin producer.machine V40ActivityScan.machine
    (producer.outputs (raw g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight)) h
  simpa only [machine,clock,result] using hh

#print axioms outputs
end
end CurrentAdditive.V40ActivityPrepare
