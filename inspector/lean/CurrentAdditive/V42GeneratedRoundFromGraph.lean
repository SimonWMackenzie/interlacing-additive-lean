import CurrentAdditive.V42GeneratedRound
import CurrentAdditive.V42GeneratedRank
import CurrentAdditive.V42SourceWidths
import CurrentAdditive.V40GraphConstructorFront
import CurrentAdditive.V40LawJobsClock

/-! One actual round from graph bytes, the public dyadic exponent and an
arbitrary stored rational base. The program computes counts, all widths,
the original indexed item law and every activity cell before the step. -/
namespace CurrentAdditive.V42GeneratedEmbedding
open Paper2 V39GeneratedConstruction
variable {q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (st : src.Streams (w := w) (μI := μI))
  (out : ExactList 8192 Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
  (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))

/-- Decoding changes neither the original generated row indices nor their law. -/
theorem numbered_original_row_law : (src.numbered st out R activity).rowLaw=out.law := rfl

/-- The original stream-product law and its exact column ordering are retained. -/
theorem numbered_original_column_law : (src.numbered st out R activity).colLaw=
    reindex (SourceData.successorColumnOrder src st) (product (uniform Q) (SourceData.Streams.law src st)) := rfl
end CurrentAdditive.V42GeneratedEmbedding

namespace CurrentAdditive.V42GeneratedRoundFromGraph
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V42Schedule V39GeneratedConstruction PhysicalProducer V40LawJobsClock
open GaussCellPolynomialClock
set_option maxHeartbeats 300000
set_option maxRecDepth 32768

structure Data where
  graph : EncodedGraph.Graph
  valid : graph.Valid
  k : ℕ
  hk : 2   ≤   k
  nonempty : 0 < graph.vertices
  width : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) graph.edges.length
    (V42RuntimePacket.repetition k graph.edges.length)
  base : StoredMatrix

def input (g:EncodedGraph.Graph) (k:ℕ) (R:StoredMatrix) :=
  BitMachineBankCodec.encode ![EncodedGraph.encode g,List.replicate k true,StoredWeightedState.encode R]
def Data.input (a:Data) := V42GeneratedRoundFromGraph.input a.graph a.k a.base
def Data.raw (a:Data) := V42RuntimePacket.input (EncodedGraph.encode a.graph)
  a.graph.vertices a.graph.edges.length a.k 0
def Data.scalar (a:Data) := V42RuntimeSource.input a.graph a.k 0
def Data.source (a:Data) := V42RuntimeWords.source a.graph a.valid a.k 0 a.hk a.nonempty a.width
def Data.prepared (a:Data) := V42GeneratedRound.input a.graph a.valid a.k a.hk a.nonempty a.width a.base
def Data.output (a:Data) := V42GeneratedRound.output a.graph a.valid a.k a.hk a.nonempty a.width a.base

def graph := PhysicalProducer.projection (0:Fin 3)
def exponent := PhysicalProducer.projection (1:Fin 3)
def base := PhysicalProducer.projection (2:Fin 3)
def vertices := PhysicalProducer.compose graph V40GraphConstructorFront.vertexCount
def edges := PhysicalProducer.compose graph V40GraphConstructorFront.edgeCount
def raw := V40GraphConstructorFront.bank5 graph vertices edges exponent
  (V40StoredOutputPrimitives.UnaryProducer.constant 0).producer
def start := V40LawJobsClock.pair base raw

def srcField (i:Fin 14) := PhysicalProducer.compose (PhysicalProducer.projection (1:Fin 2))
  (PhysicalProducer.projection i)
def context := PhysicalProducer.concat
  (V40GraphConstructorFront.bank5 (srcField 5) (srcField 6) (srcField 7) (srcField 8) (srcField 9))
  (PhysicalProducer.concat (PhysicalProducer.compose (srcField 12) PhysicalProducer.field)
    (PhysicalProducer.compose (srcField 13) PhysicalProducer.field))
def finish := V40LawJobsClock.pair context (PhysicalProducer.projection (0:Fin 2))

theorem raw_result (g:EncodedGraph.Graph) (hg:g.Valid) (k:ℕ) (R:StoredMatrix) :
    raw.result (input g k R)=V42RuntimePacket.input (EncodedGraph.encode g) g.vertices g.edges.length k 0 := by
  simp only [raw,V40GraphConstructorFront.bank5_result,vertices,edges,graph,exponent,base,
    PhysicalProducer.compose,Function.comp_apply,PhysicalProducer.projection,input,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    V40GraphConstructorFront.vertex_result g hg,V40GraphConstructorFront.edge_result g hg]
  rfl

theorem start_result (a:Data) : start.result a.input=
    V40LawPacket.packet (StoredWeightedState.encode a.base) a.raw := by
  change start.result (input a.graph a.k a.base)=_
  rw [start,pair_result,raw_result a.graph a.valid a.k a.base]
  simp only [base,PhysicalProducer.projection,Data.input,input,BankFieldProjection.result_encode,
    Matrix.cons_val_two,packet_eq,Data.raw]
  rfl

theorem context_packet_result (header graph:List Bool) (n m k:ℕ) (law activity:List Bool) :
    context.result (V40LawPacket.packet header (V42RuntimePacket.withSource graph n m k 0 law activity))=
      V42RuntimePacket.context k law activity := by
  simp only [context,PhysicalProducer.concat,PhysicalProducer.compose,Function.comp_apply,
    V40GraphConstructorFront.bank5_result,srcField,PhysicalProducer.projection,PhysicalProducer.field,
    packet_eq,V42RuntimePacket.withSource,V42RuntimePacket.withSourceWords,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ]
  simp [V42RuntimePacket.context,BitMachineBankCodec.encode_eq_list,List.ofFn_succ,List.append_assoc]

theorem finish_packet_result (header graph:List Bool) (n m k:ℕ) (law activity:List Bool) :
    finish.result (V40LawPacket.packet header (V42RuntimePacket.withSource graph n m k 0 law activity))=
      BitMachineBankCodec.encode ![V42RuntimePacket.context k law activity,header] := by
  rw [finish,pair_result,context_packet_result]
  simp only [PhysicalProducer.projection,packet_eq,BankFieldProjection.result_encode,Matrix.cons_val_zero]

theorem finish_result (a:Data) :
    finish.result (V40LawPacket.packet (StoredWeightedState.encode a.base) a.source)=a.prepared := by
  exact finish_packet_result (StoredWeightedState.encode a.base) (EncodedGraph.encode a.graph)
    a.graph.vertices a.graph.edges.length a.k
    (StoredWeightedState.lawBytes (V42RuntimeWords.law a.graph a.k a.hk a.nonempty))
    (StoredStepContext.activityWords (V42RuntimeWords.activity a.graph a.valid a.k a.hk a.width))

def tailMachine := BitMachineComposition.composition
  (BitMachineComposition.composition (V40LawBankMap.liftMachine V42RuntimeSource.machine) finish.machine)
  StoredMatrixPhysicalStep.machine

theorem tail_realizes : Realizes tailMachine
    (fun a:Data=>V40LawPacket.packet (StoredWeightedState.encode a.base) a.scalar) Data.output := by
  have hsrc:Realizes V42RuntimeSource.machine Data.scalar Data.source := by
    refine ⟨V42RuntimeSource.coefficient,V42RuntimeSource.degree,?_⟩
    intro a
    letI:NeZero (s a.k):=⟨(s_pos a.k).ne'⟩
    exact V42RuntimeSource.outputs a.graph a.valid a.k 0 a.nonempty
      (V42GeneratedConstruction.s_ge_four a.k a.hk) a.width
  have h0:=V40LawJobsClock.bank_map V42RuntimeSource.machine
    (fun a:Data=>StoredWeightedState.encode a.base) Data.scalar Data.source hsrc
  have h1:=V40LawJobsClock.producer finish
    (fun a:Data=>V40LawPacket.packet (StoredWeightedState.encode a.base) a.source)
  simp only [finish_result] at h1
  have h2:Realizes StoredMatrixPhysicalStep.machine Data.prepared Data.output :=
    ⟨StoredMatrixPhysicalStep.coefficient,StoredMatrixPhysicalStep.degree,fun a=>
      V42GeneratedRound.one_round_outputs a.graph a.valid a.k a.hk a.nonempty a.width a.base⟩
  exact V40LawJobsClock.compose _ _ _ _ _ (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2

def tailCoefficient := Classical.choose tail_realizes
def tailDegree := Classical.choose (Classical.choose_spec tail_realizes)
theorem tail_outputs (a:Data) : tailMachine.OutputsWithin
    (V40LawPacket.packet (StoredWeightedState.encode a.base) a.scalar) a.output
      (tailCoefficient*((V40LawPacket.packet (StoredWeightedState.encode a.base) a.scalar).length+1)^tailDegree) :=
  Classical.choose_spec (Classical.choose_spec tail_realizes) a

def machine := BitMachineComposition.composition
  (BitMachineComposition.composition start.machine (V40LawBankMap.liftMachine V42RuntimePacket.machine)) tailMachine

def initialCap (Δ N len:ℕ) := V42GeneratedRound.rawCap Δ N+2*len
def rawPacketCap (Δ N len:ℕ) := 2*len+2*V42GeneratedRound.rawCap Δ N+2
def scalarPacketCap (Δ N len:ℕ) := 2*len+2*V42GeneratedRound.scalarCap Δ N+2
def scalarTimeCap (Δ N:ℕ) := V42RuntimePacket.coefficient*
  (N+V42GeneratedRound.rawCap Δ N+1)^V42RuntimePacket.degree
def liftedScalarCap (Δ N len:ℕ) := 7*(rawPacketCap Δ N len+2)+
  (1+4*V42RuntimePacket.machine.pushBound)*scalarTimeCap Δ N
def prefixCap (Δ N len:ℕ) := start.coefficient*(initialCap Δ N len+1)^start.degree+
  2*rawPacketCap Δ N len+2+liftedScalarCap Δ N len
def timeCap (Δ N len:ℕ) := prefixCap Δ N len+2*scalarPacketCap Δ N len+2+
  tailCoefficient*(scalarPacketCap Δ N len+1)^tailDegree

theorem timeCap_polynomial (Δ:ℕ) : PolynomialBound (timeCap Δ) := by
  have hr:PolynomialBound (fun N _=>V42GeneratedRound.rawCap Δ N) :=
    mul (constant _) (power (add first (constant 1)) 2)
  have hs:PolynomialBound (fun N _=>V42GeneratedRound.scalarCap Δ N) :=
    mul (constant _) (power (add (add first hr) (constant 1)) _)
  have hi:PolynomialBound (initialCap Δ) := add hr (mul (constant 2) second)
  have hp:PolynomialBound (rawPacketCap Δ) := add (add (mul (constant 2) second) (mul (constant 2) hr)) (constant 2)
  have hq:PolynomialBound (scalarPacketCap Δ) := add (add (mul (constant 2) second) (mul (constant 2) hs)) (constant 2)
  have ht:PolynomialBound (fun N _=>scalarTimeCap Δ N) := mul (constant _) (power (add (add first hr) (constant 1)) _)
  have hl:PolynomialBound (liftedScalarCap Δ) :=
    add (mul (constant 7) (add hp (constant 2))) (mul (constant _) ht)
  have hpre:PolynomialBound (prefixCap Δ) :=
    add (add (add (mul (constant _) (power (add hi (constant 1)) _)) (mul (constant 2) hp)) (constant 2)) hl
  exact add (add (add hpre (mul (constant 2) hq)) (constant 2))
    (mul (constant _) (power (add hq (constant 1)) _))

theorem initial_length (a:Data) (Δ:ℕ)
    (hnN:a.graph.vertices  ≤  V42PublicSchedule.generatedN a.k)
    (hdeg:2*a.graph.edges.length  ≤  Δ*a.graph.vertices) :
    a.input.length  ≤  initialCap Δ (V42PublicSchedule.generatedN a.k) (StoredWeightedState.encode a.base).length := by
  have h:=V42GeneratedRound.raw_length a.graph a.valid a.k Δ hnN hdeg
  simp only [Data.input,input,Data.raw,V42RuntimePacket.input,V42RuntimePacket.rawWords,
    BitMachineBankCodec.encode_length,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,List.length_replicate,List.length_nil,Nat.add_zero] at h ⊢
  unfold initialCap
  omega

theorem canonical_outputs (a:Data) (Δ:ℕ)
    (hnN:a.graph.vertices  ≤  V42PublicSchedule.generatedN a.k)
    (hdeg:2*a.graph.edges.length  ≤  Δ*a.graph.vertices) :
    machine.OutputsWithin a.input a.output
      (timeCap Δ (V42PublicSchedule.generatedN a.k) (StoredWeightedState.encode a.base).length) := by
  let N:=V42PublicSchedule.generatedN a.k
  let len:=(StoredWeightedState.encode a.base).length
  change machine.OutputsWithin a.input a.output (timeCap Δ N len)
  have hi:=initial_length a Δ hnN hdeg
  have hr:=V42GeneratedRound.raw_length a.graph a.valid a.k Δ hnN hdeg
  change a.raw.length   ≤   V42GeneratedRound.rawCap Δ N at hr
  have hraw:(V40LawPacket.packet (StoredWeightedState.encode a.base) a.raw).length  ≤  rawPacketCap Δ N len := by
    rw [V40LawPacket.packet_length]
    unfold rawPacketCap
    omega
  have hscalar:(V40LawPacket.packet (StoredWeightedState.encode a.base) a.scalar).length  ≤  scalarPacketCap Δ N len := by
    rw [V40LawPacket.packet_length]
    have hs:=V42GeneratedRound.scalar_length a.graph a.valid a.k Δ hnN hdeg
    change a.scalar.length   ≤   V42GeneratedRound.scalarCap Δ N at hs
    unfold scalarPacketCap
    omega
  have hsk:2^a.k  ≤  N := by
    unfold N
    rw [V42PublicSchedule.generatedN_exact]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hp0:=V42RuntimePacket.outputs (EncodedGraph.encode a.graph) a.graph.vertices a.graph.edges.length a.k 0
  have hp:V42RuntimePacket.machine.OutputsWithin a.raw a.scalar (scalarTimeCap Δ N) :=
    BitMachine.outputsWithin_mono _ hp0 (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by omega : 2^a.k+a.raw.length+1  ≤  N+V42GeneratedRound.rawCap Δ N+1) _))
  have hl:=V40LawBankMap.outputs_charged V42RuntimePacket.machine
    (StoredWeightedState.encode a.base) a.raw a.scalar (scalarTimeCap Δ N) hp
  have hl':(V40LawBankMap.liftMachine V42RuntimePacket.machine).OutputsWithin
      (V40LawPacket.packet (StoredWeightedState.encode a.base) a.raw)
      (V40LawPacket.packet (StoredWeightedState.encode a.base) a.scalar) (liftedScalarCap Δ N len) :=
    BitMachine.outputsWithin_mono _ hl (by unfold liftedScalarCap;omega)
  have hs0:=start.outputs a.input
  rw [start_result] at hs0
  have hs:start.machine.OutputsWithin a.input
      (V40LawPacket.packet (StoredWeightedState.encode a.base) a.raw)
      (start.coefficient*(initialCap Δ N len+1)^start.degree) :=
    BitMachine.outputsWithin_mono _ hs0
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) _))
  have hfirst:=BitMachineComposition.composition_outputsWithin _ _ hs hl'
  have hpre:(BitMachineComposition.composition start.machine (V40LawBankMap.liftMachine V42RuntimePacket.machine)).OutputsWithin
      a.input (V40LawPacket.packet (StoredWeightedState.encode a.base) a.scalar) (prefixCap Δ N len) :=
    BitMachine.outputsWithin_mono _ hfirst (by unfold prefixCap;omega)
  have ht0:=tail_outputs a
  have ht:tailMachine.OutputsWithin (V40LawPacket.packet (StoredWeightedState.encode a.base) a.scalar)
      a.output (tailCoefficient*(scalarPacketCap Δ N len+1)^tailDegree) :=
    BitMachine.outputsWithin_mono _ ht0
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hscalar 1) _))
  have hall:=BitMachineComposition.composition_outputsWithin _ _ hpre ht
  exact BitMachine.outputsWithin_mono _ hall (by unfold timeCap;omega)

theorem width_from_geometry (Δ k:ℕ) (g:EncodedGraph.Graph)
    (hnN:g.vertices  ≤  V42PublicSchedule.generatedN k) (hdeg:2*g.edges.length  ≤  Δ*g.vertices) (hcut:2*Δ  ≤  k) :
    q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length (V42RuntimePacket.repetition k g.edges.length) := by
  have hn:g.vertices  ≤  2^(4*k) := by simpa only [V42PublicSchedule.generatedN_exact] using hnN
  have hw:=source_width Δ g.vertices g.edges.length k (4*k) hn hdeg hcut
  change q₂ k (4*k)=EdgeSource.sourceQ0 (Fin (4*s k)) (Fin g.edges.length)*V42RuntimePacket.repetition k g.edges.length
  rw [EdgeSource.sourceQ0_literal]
  simpa only [Fintype.card_fin,V42RuntimePacket.repetition,sourceQ0,V42Schedule.repetition,
    V38Schedule.pow2Ceil,SourcePadding.powTwoCeil] using repetition_exact k (4*k) g.edges.length hw

/-- One fixed physical program computes the context from the actual graph
and public k, then performs one round on every complete rational base. No
prepared context, source table, successful run or output is an input premise. -/
theorem one_round_from_graph_polynomial (Δ:ℕ) : ∃ C E:ℕ,
    ∀ (g:EncodedGraph.Graph) (hg:g.Valid) (k:ℕ) (hk:2  ≤  k) (hn:0<g.vertices)
      (hnN:g.vertices  ≤  V42PublicSchedule.generatedN k) (hdeg:2*g.edges.length  ≤  Δ*g.vertices)
      (hcut:2*Δ  ≤  k) (R:StoredMatrix),
    let hq:=width_from_geometry Δ k g hnN hdeg hcut
    machine.OutputsWithin (input g k R) (V42GeneratedRound.output g hg k hk hn hq R)
      (C*(V42PublicSchedule.generatedN k+(StoredWeightedState.encode R).length+1)^E) := by
  obtain ⟨C,E,hpoly⟩:=timeCap_polynomial Δ
  refine ⟨C,E,?_⟩
  intro g hg k hk hn hnN hdeg hcut R
  exact BitMachine.outputsWithin_mono _
    (canonical_outputs ⟨g,hg,k,hk,hn,width_from_geometry Δ k g hnN hdeg hcut,R⟩ Δ hnN hdeg)
    (hpoly (V42PublicSchedule.generatedN k) (StoredWeightedState.encode R).length)

def completeCap (Δ N len:ℕ) := timeCap Δ N len+initialCap Δ N len+
  timeCap Δ N len*machine.pushBound

theorem completeCap_polynomial (Δ:ℕ) : PolynomialBound (completeCap Δ) := by
  have hr:PolynomialBound (fun N _=>V42GeneratedRound.rawCap Δ N) :=
    mul (constant _) (power (add first (constant 1)) 2)
  have hi:PolynomialBound (initialCap Δ) := add hr (mul (constant 2) second)
  have ht:=timeCap_polynomial Δ
  exact add (add ht hi) (mul ht (constant machine.pushBound))

theorem charged_time_and_size (M:BitMachine.Machine) (x y:List Bool) (u v:ℕ)
    (h:M.OutputsWithin x y u) (hx:x.length ≤ v) :
    M.OutputsWithin x y (u+v+u*M.pushBound) ∧ y.length ≤ u+v+u*M.pushBound := by
  have htime:u ≤ u+v+u*M.pushBound :=
    (Nat.le_add_right u v).trans (Nat.le_add_right (u+v) (u*M.pushBound))
  have hy:=BitMachine.output_length_bound M h
  have hv:y.length ≤ v+u*M.pushBound := hy.trans (Nat.add_le_add_right hx _)
  exact ⟨BitMachine.outputsWithin_mono M h htime,
    hv.trans (Nat.add_le_add_right (Nat.le_add_left v u) _)⟩

/-- Both actual time and every printed output byte are charged by one fixed
polynomial, including context preparation and complete rational encodings. -/
theorem one_round_size_and_time_polynomial (Δ:ℕ) : ∃ C E:ℕ,
    ∀ (g:EncodedGraph.Graph) (hg:g.Valid) (k:ℕ) (hk:2 ≤ k) (hn:0<g.vertices)
      (hnN:g.vertices ≤ V42PublicSchedule.generatedN k) (hdeg:2*g.edges.length ≤ Δ*g.vertices)
      (hcut:2*Δ ≤ k) (R:StoredMatrix),
    let hq:=width_from_geometry Δ k g hnN hdeg hcut
    let Y:=V42GeneratedRound.output g hg k hk hn hq R
    machine.OutputsWithin (input g k R) Y
      (C*(V42PublicSchedule.generatedN k+(StoredWeightedState.encode R).length+1)^E) ∧
      Y.length ≤ C*(V42PublicSchedule.generatedN k+(StoredWeightedState.encode R).length+1)^E := by
  obtain ⟨C,E,hpoly⟩:=completeCap_polynomial Δ
  refine ⟨C,E,?_⟩
  intro g hg k hk hn hnN hdeg hcut R
  let a:Data:=⟨g,hg,k,hk,hn,width_from_geometry Δ k g hnN hdeg hcut,R⟩
  have h:=charged_time_and_size machine a.input a.output
    (timeCap Δ (V42PublicSchedule.generatedN k) (StoredWeightedState.encode R).length)
    (initialCap Δ (V42PublicSchedule.generatedN k) (StoredWeightedState.encode R).length)
    (canonical_outputs a Δ hnN hdeg) (initial_length a Δ hnN hdeg)
  have hp:=hpoly (V42PublicSchedule.generatedN k) (StoredWeightedState.encode R).length
  exact ⟨BitMachine.outputsWithin_mono machine h.1 hp,h.2.trans hp⟩

#print axioms V42GeneratedEmbedding.numbered_original_row_law
#print axioms V42GeneratedEmbedding.numbered_original_column_law
#print axioms one_round_size_and_time_polynomial

#print axioms tail_realizes
#print axioms canonical_outputs
#print axioms one_round_from_graph_polynomial
end
end CurrentAdditive.V42GeneratedRoundFromGraph

