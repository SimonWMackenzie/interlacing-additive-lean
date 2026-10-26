import CurrentAdditive.V40ActivityClock
import CurrentAdditive.V40ActivityIndex

/-! The complete ordinary-input cell query starts from graph bytes and
unary public/item/coordinate fields. All scanner operands are physically
computed and installed. Its local result metadata is the word in the
actual fixed machine's bounded run, identified below with current activity. -/
namespace CurrentAdditive.V40SourceCell
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineBankCodec
open D22PacketPrimitives V40SourceLocal
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxSynthPendingDepth 128
abbrev P:=V40SourceLocal.Producer

def bitProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 2=>Bool) Unit (Option Bool) :=
  .pop 0 (fun _ b=>b) (.push 1 (fun v=>v.isSome) .halt)
def bitMachine : BitMachine.Machine:=ofFinite (0:Fin 2) 1 () none bitProgram
theorem bit_outputs (x : List Bool) : bitMachine.OutputsWithin x [x.head?.isSome] 1 := by
  apply outputsWithin_of_raw_run (0:Fin 2) 1 () none bitProgram x [x.head?.isSome] 1 1 le_rfl
  · simp [Function.iterate_one,advance,rawInit,bitProgram,TM2.step,TM2.stepAux]
  · simp [Function.iterate_one,advance,rawInit,bitProgram,TM2.step,TM2.stepAux]
def bitProducer : PhysicalProducer.Producer :=
  ⟨bitMachine,fun x=>[x.head?.isSome],1,0,by simpa using bit_outputs⟩

def raw (g : EncodedGraph.Graph) (s r i a : Nat) := encode ![EncodedGraph.encode g,
  List.replicate g.edges.length true,List.replicate s true,List.replicate r true,
  List.replicate i true,List.replicate a true,List.replicate g.vertices true]
def group : P:=scalar (4:Fin 7) 6 2 V40IndexedLawLoop.lower
def remainderQuery : P:=⟨V40ActivityIndex.remainderMachine,
  fun x=>(V40ActivityIndex.remainderMachine.run (17*(x.length+1))
    (V40ActivityIndex.remainderMachine.init x)).stk V40ActivityIndex.remainderMachine.output,
  fun x=>17*(x.length+1)⟩
theorem remainder_result (u v : Nat) :
    remainderQuery.result (MatrixUnaryArithmetic.encodeInput u v)=List.replicate (u%v) true := by
  have h:=BitMachine.outputsWithin_mono V40ActivityIndex.remainderMachine (V40ActivityIndex.remainder_outputs u v)
    (show 9*u+4*v+7 ≤ 17*((MatrixUnaryArithmetic.encodeInput u v).length+1) by
      simp [MatrixUnaryArithmetic.encodeInput]; omega)
  exact (BitMachine.outputsWithin_at_bound V40ActivityIndex.remainderMachine h).2
theorem remainder_query_outputs (u v : Nat) :
    remainderQuery.machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput u v)
      (remainderQuery.result (MatrixUnaryArithmetic.encodeInput u v))
      (remainderQuery.clock (MatrixUnaryArithmetic.encodeInput u v)) := by
  rw [remainder_result]
  apply BitMachine.outputsWithin_mono _ (V40ActivityIndex.remainder_outputs u v)
  simp [remainderQuery,MatrixUnaryArithmetic.encodeInput]
  omega

def pair : P:=append (scalar (4:Fin 7) 6 2 V40ActivityIndex.shiftedTerm)
  (append (constant [false]) (scalar (4:Fin 7) 6 2 V40IndexedLawLoop.divisor))
def itemValue : P:=V40SourceLocal.compose pair remainderQuery

theorem pair_result (g : EncodedGraph.Graph) (s r i a : Nat) :
    pair.result (raw g s r i a)=MatrixUnaryArithmetic.encodeInput
      (V40ActivityIndex.shiftedTerm.eval i g.vertices s) (V40IndexedLawLoop.divisor.eval i g.vertices s) := by
  simp [pair,append,scalar,constant,physical,V40SeedProducer.constant,raw,
    BankFieldProjection.result_encode,MatrixUnaryArithmetic.encodeInput]
theorem itemValue_result (g : EncodedGraph.Graph) (s r i a : Nat) :
    itemValue.result (raw g s r i a)=List.replicate (V40ActivityIndex.value s g.vertices i) true := by
  change remainderQuery.result (pair.result (raw g s r i a))=_
  rw [pair_result,remainder_result,V40ActivityIndex.shiftedTerm_eval,V40ActivityIndex.divisor_eval]
  rfl
theorem itemValue_outputs (g : EncodedGraph.Graph) (s r i a : Nat) :
    itemValue.machine.OutputsWithin (raw g s r i a) (itemValue.result (raw g s r i a))
      (itemValue.clock (raw g s r i a)) := by
  apply compose_outputs
  · apply append_outputs
    · apply scalar_outputs (4:Fin 7) 6 2 _ _ i g.vertices s <;> simp [raw,BankFieldProjection.result_encode]
    · apply append_outputs
      · exact constant_outputs _ _
      · apply scalar_outputs (4:Fin 7) 6 2 _ _ i g.vertices s <;> simp [raw,BankFieldProjection.result_encode]
  · rw [pair_result]
    exact remainder_query_outputs _ _

def kind : P:=V40SourceLocal.compose (scalar (4:Fin 7) 6 2 V40ActivityIndex.kindTerm) (physical bitProducer)
def fields : Fin 8 → P:=![project (0:Fin 7),project (5:Fin 7),project (3:Fin 7),project (1:Fin 7),
  group,itemValue,kind,project (2:Fin 7)]
def prepare : P:=serialise fields

theorem prepare_outputs (g : EncodedGraph.Graph) (s r i a : Nat) :
    prepare.machine.OutputsWithin (raw g s r i a) (prepare.result (raw g s r i a))
      (prepare.clock (raw g s r i a)) := by
  apply serialise_outputs
  intro k
  fin_cases k
  · exact project_outputs _ _
  · exact project_outputs _ _
  · exact project_outputs _ _
  · exact project_outputs _ _
  · apply scalar_outputs (4:Fin 7) 6 2 _ _ i g.vertices s <;> simp [raw,BankFieldProjection.result_encode]
  · change itemValue.machine.OutputsWithin _ (itemValue.result _) (itemValue.clock _)
    exact itemValue_outputs g s r i a
  · apply compose_outputs
    · apply scalar_outputs (4:Fin 7) 6 2 _ _ i g.vertices s <;> simp [raw,BankFieldProjection.result_encode]
    · exact physical_outputs _ _
  · exact project_outputs _ _

theorem prepare_result (g : EncodedGraph.Graph) (s r : Nat) (hn : 0<g.vertices)
    (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) (a : Nat) :
    prepare.result (raw g s r (LiteralEdgeEncoder.itemNumber s g.vertices (ig,z)).val a)=
      V40ActivityPrepare.raw g s a r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight := by
  rw [prepare,serialise_result]
  apply congrArg encode
  funext k
  cases z with
  | inl v =>
    obtain ⟨hg,hk,hv⟩:=V40ActivityIndex.vertex s g.vertices hn ig v
    have hi:=itemValue_result g s r (LiteralEdgeEncoder.itemNumber s g.vertices (ig,.inl v)).val a
    rw [hv] at hi
    simp only [raw,LiteralEdgeEncoder.itemNumber_vertex] at hi
    simp only [LiteralEdgeEncoder.itemNumber_vertex] at hg hk hv
    fin_cases k <;> simp [fields,project,group,scalar,hi,kind,V40SourceLocal.compose,
      physical,bitProducer,raw,V40ActivityPrepare.raw,BankFieldProjection.result_encode,
      V40ActivityIndex.lower_eval,V40ActivityIndex.kindTerm_eval,hg,hk,hv,
      CanonicalEndpointRankBridge.itemValue]
  | inr v =>
    obtain ⟨hg,hk,hv⟩:=V40ActivityIndex.auxiliary s g.vertices hn ig v
    have hi:=itemValue_result g s r (LiteralEdgeEncoder.itemNumber s g.vertices (ig,.inr v)).val a
    rw [hv] at hi
    simp only [raw,LiteralEdgeEncoder.itemNumber_auxiliary] at hi
    simp only [LiteralEdgeEncoder.itemNumber_auxiliary] at hg hk hv
    fin_cases k <;> simp [fields,project,group,scalar,hi,kind,V40SourceLocal.compose,
      physical,bitProducer,raw,V40ActivityPrepare.raw,BankFieldProjection.result_encode,
      V40ActivityIndex.lower_eval,V40ActivityIndex.kindTerm_eval,hg,hk,hv,
      CanonicalEndpointRankBridge.itemValue]

def query : P :=
  ⟨V40ActivityPrepare.machine,
    fun x=>(V40ActivityPrepare.machine.run (V40ActivityClock.coefficient*(x.length+1)^V40ActivityClock.degree)
      (V40ActivityPrepare.machine.init x)).stk V40ActivityPrepare.machine.output,
    fun x=>V40ActivityClock.coefficient*(x.length+1)^V40ActivityClock.degree⟩
def producer : P:=V40SourceLocal.compose prepare query

def value {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (i : Fin (4*s*(g.vertices+(s-3)))) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :=
  match LiteralEdgeEncoder.indexedActivity hs (LiteralEdgeEncoder.edge g hg) i a with
    | some p=>p.val | none=>s

theorem result {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0<g.vertices) (hs : 3 ≤ s)
    (i : Fin (4*s*(g.vertices+(s-3)))) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :
    producer.result (raw g s r i.val a.val)=(value g hg hs i a).bits := by
  obtain ⟨⟨ig,z⟩,rfl⟩:=(LiteralEdgeEncoder.itemNumber s g.vertices).surjective i
  change query.result (prepare.result (raw g s r _ a.val))=_
  rw [prepare_result g s r hn ig z a.val]
  have h:=V40ActivityClock.outputs g hg hs ig z a
  simpa [query,value,LiteralEdgeEncoder.indexedActivity] using
    (BitMachine.outputsWithin_at_bound V40ActivityPrepare.machine h).2

theorem outputs {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0<g.vertices) (hs : 3 ≤ s)
    (i : Fin (4*s*(g.vertices+(s-3)))) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :
    producer.machine.OutputsWithin (raw g s r i.val a.val) (value g hg hs i a).bits
      (producer.clock (raw g s r i.val a.val)) := by
  obtain ⟨⟨ig,z⟩,rfl⟩:=(LiteralEdgeEncoder.itemNumber s g.vertices).surjective i
  let i0:=(LiteralEdgeEncoder.itemNumber s g.vertices (ig,z)).val
  let x:=raw g s r i0 a.val
  have h:=V40ActivityClock.outputs g hg hs ig z a
  have he:=prepare_result g s r hn ig z a.val
  have hq : query.machine.OutputsWithin (prepare.result x)
      (match LiteralEdgeEncoder.activity hs (LiteralEdgeEncoder.edge g hg) (ig,z) a with
        | some p=>p.val | none=>s).bits (query.clock (prepare.result x)) := by
    dsimp only [x,i0]
    rw [he]
    exact h
  have hh:=BitMachineComposition.composition_outputsWithin prepare.machine query.machine
    (prepare_outputs g s r i0 a.val) hq
  simpa [producer,V40SourceLocal.compose,value,LiteralEdgeEncoder.indexedActivity,x,i0] using hh

#print axioms outputs
end
end CurrentAdditive.V40SourceCell
