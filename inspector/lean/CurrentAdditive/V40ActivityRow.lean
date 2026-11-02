import CurrentAdditive.V40SourceCell

/-! The fixed inner loop prints every coordinate of one numbered item.
The actual unary coordinate counter is supplied to the concrete source-cell
machine, and each returned word is physically framed before accumulation. -/
namespace CurrentAdditive.V40ActivityRow
noncomputable section
open Paper2 EthInapproximability.CurrentPaper BitMachineBankCodec EncodedCommunication
open D22PacketPrimitives V40SourceLocal
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
abbrev P:=V40SourceLocal.Producer
def count (s n : Nat):=4*s*(n+(s-3))
def entries (g : EncodedGraph.Graph) (s r i j : Nat) : List (List Bool):=
  (List.range j).map (fun a=>V40SourceCell.producer.result (V40SourceCell.raw g s r i a))
def accumulator (g : EncodedGraph.Graph) (s r q2 i j : Nat):=
  natField q2++SourceListEncoding.fields (entries g s r i j)
def state (g : EncodedGraph.Graph) (s r q2 i j : Nat):=encode ![EncodedGraph.encode g,
  List.replicate g.edges.length true,List.replicate s true,List.replicate r true,List.replicate g.vertices true,
  List.replicate q2 true,List.replicate (count s g.vertices) true,List.replicate i true,
  List.replicate j true,accumulator g s r q2 i j]
def input (g : EncodedGraph.Graph) (s r q2 i : Nat) (carry : List Bool):=encode ![EncodedGraph.encode g,
  List.replicate g.edges.length true,List.replicate s true,List.replicate r true,List.replicate g.vertices true,
  List.replicate q2 true,List.replicate (count s g.vertices) true,List.replicate i true,[],carry]
def packet (g : EncodedGraph.Graph) (s r q2 i : Nat):=SourceListEncoding.encode (entries g s r i q2)

def cellInput : P:=serialise ![project (0:Fin 10),project (1:Fin 10),project (2:Fin 10),
  project (3:Fin 10),project (7:Fin 10),project (8:Fin 10),project (4:Fin 10)]
def cell : P:=V40SourceLocal.compose cellInput V40SourceCell.producer
def newItem : P:=V40SourceLocal.compose cell (physical PhysicalProducer.item)
def nextIndex : P:=append (constant [true]) (project (8:Fin 10))
def nextAccumulator : P:=append (project (9:Fin 10)) newItem
def bodyFields : Fin 10 → P:=![project (0:Fin 10),project (1:Fin 10),project (2:Fin 10),
  project (3:Fin 10),project (4:Fin 10),project (5:Fin 10),project (6:Fin 10),project (7:Fin 10),
  nextIndex,nextAccumulator]
def body : P:=serialise bodyFields

theorem cellInput_result (g : EncodedGraph.Graph) (s r q2 i j : Nat) :
    cellInput.result (state g s r q2 i j)=V40SourceCell.raw g s r i j := by
  rw [cellInput,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k <;> simp [project,state,V40SourceCell.raw,BankFieldProjection.result_encode]
theorem cellInput_outputs (x : List Bool) :
    cellInput.machine.OutputsWithin x (cellInput.result x) (cellInput.clock x) := by
  apply serialise_outputs
  intro k
  fin_cases k <;> exact project_outputs _ _

theorem accumulator_succ (g : EncodedGraph.Graph) (s r q2 i j : Nat) :
    accumulator g s r q2 i (j+1)=accumulator g s r q2 i j++
      SourceListMachineWriter.result true (V40SourceCell.producer.result (V40SourceCell.raw g s r i j)) := by
  simp [accumulator,entries,List.range_succ,List.map_append,V40IndexedLawLoop.fields_append,
    SourceListEncoding.fields,SourceListMachineWriter.result,List.append_assoc]
theorem body_result (g : EncodedGraph.Graph) (s r q2 i j : Nat) :
    body.result (state g s r q2 i j)=state g s r q2 i (j+1) := by
  rw [body,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k
  all_goals first
    | solve | simp [bodyFields,project,state,BankFieldProjection.result_encode]
    | skip
  · simp [bodyFields,nextIndex,append,constant,physical,V40SeedProducer.constant,project,
      state,BankFieldProjection.result_encode,List.replicate_succ]
  · change nextAccumulator.result (state g s r q2 i j)=accumulator g s r q2 i (j+1)
    simp only [nextAccumulator,append,project,state,BankFieldProjection.result_encode]
    change accumulator g s r q2 i j++SourceListMachineWriter.result true
      (V40SourceCell.producer.result (cellInput.result (state g s r q2 i j)))=_
    rw [cellInput_result]
    exact (accumulator_succ g s r q2 i j).symm

theorem body_outputs {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) (j : Fin q2) :
    body.machine.OutputsWithin (state g s r q2 i.val j.val)
      (state g s r q2 i.val (j.val+1)) (body.clock (state g s r q2 i.val j.val)) := by
  have hc:=V40SourceCell.outputs g hg hn hs i (Fin.cast hq j)
  rw [←V40SourceCell.result g hg hn hs i (Fin.cast hq j)] at hc
  have hcell : cell.machine.OutputsWithin (state g s r q2 i.val j.val)
      (cell.result (state g s r q2 i.val j.val)) (cell.clock (state g s r q2 i.val j.val)) := by
    apply compose_outputs _ _ _ (cellInput_outputs _)
    rw [cellInput_result]
    exact hc
  have hitem:=compose_outputs cell (physical PhysicalProducer.item) _ hcell (physical_outputs _ _)
  have hbody : body.machine.OutputsWithin (state g s r q2 i.val j.val)
      (body.result (state g s r q2 i.val j.val)) (body.clock (state g s r q2 i.val j.val)) := by
    apply serialise_outputs
    intro k
    fin_cases k
    all_goals first | exact project_outputs _ _ | skip
    · exact append_outputs _ _ _ (constant_outputs _ _) (project_outputs _ _)
    · exact append_outputs _ _ _ (project_outputs _ _) hitem
  simpa only [body_result] using hbody

def initialFields : Fin 10 → P:=![project (0:Fin 10),project (1:Fin 10),project (2:Fin 10),
  project (3:Fin 10),project (4:Fin 10),project (5:Fin 10),project (6:Fin 10),project (7:Fin 10),
  constant [],V40SourceLocal.compose (project (5:Fin 10)) unaryField]
def initial : P:=serialise initialFields
def withFuel : P:=serialise ![initial,project (5:Fin 10)]
theorem initial_result (g : EncodedGraph.Graph) (s r q2 i : Nat) (carry : List Bool) :
    initial.result (input g s r q2 i carry)=state g s r q2 i 0 := by
  rw [initial,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k <;> simp [initialFields,project,constant,physical,V40SeedProducer.constant,
    V40SourceLocal.compose,unaryField,input,state,accumulator,entries,SourceListEncoding.fields,
    BankFieldProjection.result_encode]
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
    · exact compose_outputs _ _ _ (project_outputs _ _) (unaryField_outputs _)
  · exact project_outputs _ _
theorem withFuel_result (g : EncodedGraph.Graph) (s r q2 i : Nat) (carry : List Bool) :
    withFuel.result (input g s r q2 i carry)=WeightedIterationDriver.input (state g s r q2 i 0) q2 := by
  rw [withFuel,serialise_result]
  rw [show WeightedIterationDriver.input (state g s r q2 i 0) q2=
    encode ![state g s r q2 i 0,List.replicate q2 true] from rfl]
  apply congrArg encode
  funext k
  fin_cases k
  · exact initial_result g s r q2 i carry
  · simp [project,input,BankFieldProjection.result_encode]

def loopMachine:=WeightedIterationDriver.machine body.machine
def loopClock (g : EncodedGraph.Graph) (s r q2 i : Nat):=WeightedIterationDriver.clock body.machine
  (state g s r q2 i) (fun j=>body.clock (state g s r q2 i j)) q2
def machine:=BitMachineComposition.composition
  (BitMachineComposition.composition withFuel.machine loopMachine) (BankFieldProjection.machine (9:Fin 10))
def clock (g : EncodedGraph.Graph) (s r q2 i : Nat) (carry : List Bool):=
  withFuel.clock (input g s r q2 i carry)+2*(withFuel.result (input g s r q2 i carry)).length+2+
  loopClock g s r q2 i+2*(state g s r q2 i q2).length+2+24*((state g s r q2 i q2).length+1)

theorem outputs {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) (carry : List Bool) :
    machine.OutputsWithin (input g s r q2 i.val carry) (packet g s r q2 i.val)
      (clock g s r q2 i.val carry) := by
  have hl : loopMachine.OutputsWithin (WeightedIterationDriver.input (state g s r q2 i.val 0) q2)
      (state g s r q2 i.val q2) (loopClock g s r q2 i.val) := by
    apply WeightedIterationDriver.outputs
    intro j hj
    exact body_outputs g hg hn hs hq i ⟨j,hj⟩
  rw [←withFuel_result g s r q2 i.val carry] at hl
  have hh:=BitMachineComposition.composition_outputsWithin _ _ (withFuel_outputs (input g s r q2 i.val carry)) hl
  have hp:=BankFieldProjection.outputs (9:Fin 10) (state g s r q2 i.val q2)
  have he : BankFieldProjection.result (9:Fin 10) (state g s r q2 i.val q2)=packet g s r q2 i.val := by
    simp [state,packet,BankFieldProjection.result_encode,accumulator,SourceListEncoding.encode,entries]
  have h:=BitMachineComposition.composition_outputsWithin _ _ hh hp
  simpa only [machine,clock,he] using h

#print axioms outputs
end
end CurrentAdditive.V40ActivityRow
