import CurrentAdditive.V40ActivityRowBounds

/-! The outer fixed loop visits every original numbered item, calls the
complete physical coordinate loop, frames that row, and appends it to the
activity table. No decoded graph function or preprinted row is an input. -/
namespace CurrentAdditive.V40ActivityTable
noncomputable section
open Paper2 EthInapproximability.CurrentPaper BitMachineBankCodec EncodedCommunication
open D22PacketPrimitives V40SourceLocal
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
abbrev P:=V40SourceLocal.Producer
abbrev count:=V40ActivityRow.count
def entries (g : EncodedGraph.Graph) (s r q2 j : Nat):=
  (List.range j).map (fun i=>V40ActivityRow.packet g s r q2 i)
def accumulator (g : EncodedGraph.Graph) (s r q2 j : Nat):=
  natField (count s g.vertices)++SourceListEncoding.fields (entries g s r q2 j)
def state (g : EncodedGraph.Graph) (s r q2 j : Nat):=
  V40ActivityRow.input g s r q2 j (accumulator g s r q2 j)
def input (g : EncodedGraph.Graph) (s r q2 : Nat):=encode ![EncodedGraph.encode g,
  List.replicate g.edges.length true,List.replicate s true,List.replicate r true,List.replicate g.vertices true,
  List.replicate q2 true,List.replicate (count s g.vertices) true]
def packet (g : EncodedGraph.Graph) (s r q2 : Nat):=
  SourceListEncoding.encode (entries g s r q2 (count s g.vertices))

def row : P:=⟨V40ActivityRow.machine,
  fun x=>(V40ActivityRow.machine.run (V40ActivityRow.coefficient*(x.length+1)^V40ActivityRow.degree)
    (V40ActivityRow.machine.init x)).stk V40ActivityRow.machine.output,
  fun x=>V40ActivityRow.coefficient*(x.length+1)^V40ActivityRow.degree⟩
def newItem : P:=V40SourceLocal.compose row (physical PhysicalProducer.item)
def nextIndex : P:=append (constant [true]) (project (7:Fin 10))
def nextAccumulator : P:=append (project (9:Fin 10)) newItem
def bodyFields : Fin 10 → P:=![project (0:Fin 10),project (1:Fin 10),project (2:Fin 10),
  project (3:Fin 10),project (4:Fin 10),project (5:Fin 10),project (6:Fin 10),nextIndex,
  constant [],nextAccumulator]
def body : P:=serialise bodyFields

theorem row_result {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) : row.result (state g s r q2 i.val)=V40ActivityRow.packet g s r q2 i.val :=
  (BitMachine.outputsWithin_at_bound V40ActivityRow.machine
    (V40ActivityRow.outputs_polynomial g hg hn hs hq i (accumulator g s r q2 i.val))).2
theorem accumulator_succ (g : EncodedGraph.Graph) (s r q2 j : Nat) :
    accumulator g s r q2 (j+1)=accumulator g s r q2 j++
      SourceListMachineWriter.result true (V40ActivityRow.packet g s r q2 j) := by
  simp [accumulator,entries,List.range_succ,List.map_append,V40IndexedLawLoop.fields_append,
    SourceListEncoding.fields,SourceListMachineWriter.result,List.append_assoc]
theorem body_result {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) : body.result (state g s r q2 i.val)=state g s r q2 (i.val+1) := by
  rw [body,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k
  all_goals first
    | solve | simp [bodyFields,project,state,V40ActivityRow.input,BankFieldProjection.result_encode,
        constant,physical,V40SeedProducer.constant]
    | skip
  · simp [bodyFields,nextIndex,append,constant,physical,V40SeedProducer.constant,project,
      state,V40ActivityRow.input,BankFieldProjection.result_encode,List.replicate_succ]
  · change nextAccumulator.result (state g s r q2 i.val)=accumulator g s r q2 (i.val+1)
    simp only [nextAccumulator,append,project,state,V40ActivityRow.input,BankFieldProjection.result_encode]
    change accumulator g s r q2 i.val++SourceListMachineWriter.result true (row.result (state g s r q2 i.val))=_
    rw [row_result g hg hn hs hq i]
    exact (accumulator_succ g s r q2 i.val).symm

theorem body_outputs {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) :
    body.machine.OutputsWithin (state g s r q2 i.val) (state g s r q2 (i.val+1)) (body.clock (state g s r q2 i.val)) := by
  have hr : row.machine.OutputsWithin (state g s r q2 i.val) (row.result (state g s r q2 i.val))
      (row.clock (state g s r q2 i.val)) := by
    rw [row_result g hg hn hs hq i]
    exact V40ActivityRow.outputs_polynomial g hg hn hs hq i (accumulator g s r q2 i.val)
  have hi:=compose_outputs row (physical PhysicalProducer.item) _ hr (physical_outputs _ _)
  have hb : body.machine.OutputsWithin (state g s r q2 i.val) (body.result (state g s r q2 i.val))
      (body.clock (state g s r q2 i.val)) := by
    apply serialise_outputs
    intro k
    fin_cases k
    all_goals first | exact project_outputs _ _ | skip
    · exact append_outputs _ _ _ (constant_outputs _ _) (project_outputs _ _)
    · exact constant_outputs _ _
    · exact append_outputs _ _ _ (project_outputs _ _) hi
  simpa only [body_result g hg hn hs hq i] using hb

def initialFields : Fin 10 → P:=![project (0:Fin 7),project (1:Fin 7),project (2:Fin 7),
  project (3:Fin 7),project (4:Fin 7),project (5:Fin 7),project (6:Fin 7),constant [],constant [],
  V40SourceLocal.compose (project (6:Fin 7)) unaryField]
def initial : P:=serialise initialFields
def withFuel : P:=serialise ![initial,project (6:Fin 7)]
theorem initial_result (g : EncodedGraph.Graph) (s r q2 : Nat) :
    initial.result (input g s r q2)=state g s r q2 0 := by
  rw [initial,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k <;> simp [initialFields,project,constant,physical,V40SeedProducer.constant,
    V40SourceLocal.compose,unaryField,input,state,V40ActivityRow.input,accumulator,entries,
    SourceListEncoding.fields,BankFieldProjection.result_encode]
theorem withFuel_outputs (x : List Bool) :
    withFuel.machine.OutputsWithin x (withFuel.result x) (withFuel.clock x) := by
  apply serialise_outputs
  intro k
  fin_cases k
  · apply serialise_outputs
    intro k
    fin_cases k
    all_goals first | exact project_outputs _ _ | skip
    · exact constant_outputs _ _
    · exact constant_outputs _ _
    · exact compose_outputs _ _ _ (project_outputs _ _) (unaryField_outputs _)
  · exact project_outputs _ _
theorem withFuel_result (g : EncodedGraph.Graph) (s r q2 : Nat) :
    withFuel.result (input g s r q2)=WeightedIterationDriver.input (state g s r q2 0) (count s g.vertices) := by
  rw [withFuel,serialise_result]
  rw [show WeightedIterationDriver.input (state g s r q2 0) (count s g.vertices)=
    encode ![state g s r q2 0,List.replicate (count s g.vertices) true] from rfl]
  apply congrArg encode
  funext k
  fin_cases k
  · exact initial_result g s r q2
  · simp [project,input,BankFieldProjection.result_encode]

def loopMachine:=WeightedIterationDriver.machine body.machine
def loopClock (g : EncodedGraph.Graph) (s r q2 : Nat):=WeightedIterationDriver.clock body.machine
  (state g s r q2) (fun j=>body.clock (state g s r q2 j)) (count s g.vertices)
def machine:=BitMachineComposition.composition
  (BitMachineComposition.composition withFuel.machine loopMachine) (BankFieldProjection.machine (9:Fin 10))
def clock (g : EncodedGraph.Graph) (s r q2 : Nat):=
  withFuel.clock (input g s r q2)+2*(withFuel.result (input g s r q2)).length+2+loopClock g s r q2+
  2*(state g s r q2 (count s g.vertices)).length+2+24*((state g s r q2 (count s g.vertices)).length+1)
theorem outputs {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r) :
    machine.OutputsWithin (input g s r q2) (packet g s r q2) (clock g s r q2) := by
  have hl : loopMachine.OutputsWithin (WeightedIterationDriver.input (state g s r q2 0) (count s g.vertices))
      (state g s r q2 (count s g.vertices)) (loopClock g s r q2) := by
    apply WeightedIterationDriver.outputs
    intro j hj
    exact body_outputs g hg hn hs hq ⟨j,hj⟩
  rw [←withFuel_result] at hl
  have hh:=BitMachineComposition.composition_outputsWithin _ _ (withFuel_outputs (input g s r q2)) hl
  have hp:=BankFieldProjection.outputs (9:Fin 10) (state g s r q2 (count s g.vertices))
  have he : BankFieldProjection.result (9:Fin 10) (state g s r q2 (count s g.vertices))=packet g s r q2 := by
    simp [state,V40ActivityRow.input,packet,BankFieldProjection.result_encode,accumulator,SourceListEncoding.encode,entries]
  have h:=BitMachineComposition.composition_outputsWithin _ _ hh hp
  simpa only [machine,clock,he] using h

#print axioms outputs
end
end CurrentAdditive.V40ActivityTable
