import CurrentAdditive.V40LawJobsClock
import CurrentAdditive.LawProductFormatter
import CurrentAdditive.CylinderEvalMapPolynomial
import CurrentAdditive.CylinderEvalReassociateMachine

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawCartesianRows
open EthInapproximability.CurrentPaper
open PhysicalProducer V40LawJobsClock
noncomputable section

/-- The physical formatter is followed by the existing per-item V2 frame.
Raw contextual maps then concatenate these frames without nested counts. -/
def callback : Producer := PhysicalProducer.compose LawProductFormatter.producer item

def rowMachine : BitMachine.Machine :=
  BitMachineComposition.composition CylinderEvalReassociate.machine
    (FeatureContextMap.machine callback.machine false)

abbrev RowData := List Bool × (List Bool × List (List Bool))

def rowInput (a : RowData) : List Bool :=
  V40LawPacket.packet (V40LawPacket.packet a.1 (SourceListEncoding.encode a.2.2)) a.2.1

def rowRouted (a : RowData) : List Bool :=
  V40LawPacket.packet (V40LawPacket.packet a.1 a.2.1) (SourceListEncoding.encode a.2.2)

def rowOutput (a : RowData) : List Bool :=
  a.2.2.flatMap (fun w => callback.result (V40LawPacket.packet
    (V40LawPacket.packet a.1 a.2.1) w))

theorem row_realizes : Realizes rowMachine rowInput rowOutput := by
  have hR : Realizes CylinderEvalReassociate.machine rowInput rowRouted := by
    refine ⟨30,1,?_⟩
    intro a
    simpa only [rowInput,rowRouted,packet_eq,pow_one] using
      CylinderEvalReassociate.outputs a.1 (SourceListEncoding.encode a.2.2) a.2.1
  obtain ⟨c,e,hCallback⟩ := V40LawJobsClock.producer callback (id : List Bool → List Bool)
  obtain ⟨C,d,hC⟩ := CylinderEvalMapPolynomial.uniform_from_callback
    callback.machine false c e
  have hMap : Realizes (FeatureContextMap.machine callback.machine false)
      rowRouted rowOutput := by
    refine ⟨C,d,?_⟩
    intro a
    let context := V40LawPacket.packet a.1 a.2.1
    let f := fun w => callback.result (V40LawPacket.packet context w)
    let b := fun w : List Bool => c*((V40LawPacket.packet context w).length+1)^e
    have hM : ∀w∈a.2.2,callback.machine.OutputsWithin
        (FeatureMapPairLoader.packet context w) (f w) (b w) := by
      intro w _
      simpa only [f,b,FeatureMapPairLoader.packet,packet_eq] using
        hCallback (V40LawPacket.packet context w)
    have h := FeatureContextMap.outputs_explicit callback.machine false context a.2.2 f b hM
    have hb := hC context a.2.2 f b hM (by
      intro w _
      simp only [b,FeatureMapPairLoader.packet,packet_eq]
      rfl)
    simpa only [rowRouted,rowOutput,FeatureContextMap.result,FeatureMapPairLoader.packet,
      packet_eq,context,f,↓reduceIte] using BitMachine.outputsWithin_mono _ h hb
  exact V40LawJobsClock.compose _ _ _ _ _ hR hMap

abbrev Data := List Bool × (List (List Bool) × List (List Bool))

def input (a : Data) : List Bool :=
  V40LawPacket.packet (V40LawPacket.packet a.1 (SourceListEncoding.encode a.2.2))
    (SourceListEncoding.encode a.2.1)

def output (a : Data) : List Bool :=
  a.2.1.flatMap (fun left => rowOutput (a.1,left,a.2.2))

def machine : BitMachine.Machine := FeatureContextMap.machine rowMachine false

/-- Both nested traversals are the accepted contextual mapper. Every
ordered pair receives the same concrete formatter; no callback is assumed. -/
theorem realizes : Realizes machine input output := by
  obtain ⟨c,e,hRow⟩ := row_realizes
  obtain ⟨C,d,hC⟩ := CylinderEvalMapPolynomial.uniform_from_callback rowMachine false c e
  refine ⟨C,d,?_⟩
  intro a
  let context := V40LawPacket.packet a.1 (SourceListEncoding.encode a.2.2)
  let f := fun left => rowOutput (a.1,left,a.2.2)
  let b := fun left => c*((rowInput (a.1,left,a.2.2)).length+1)^e
  have hM : ∀left∈a.2.1,rowMachine.OutputsWithin
      (FeatureMapPairLoader.packet context left) (f left) (b left) := by
    intro left _
    simpa only [rowInput,FeatureMapPairLoader.packet,packet_eq,context,f,b] using
      hRow (a.1,left,a.2.2)
  have h := FeatureContextMap.outputs_explicit rowMachine false context a.2.1 f b hM
  have hb := hC context a.2.1 f b hM (by
    intro w _
    simp only [b,rowInput,FeatureMapPairLoader.packet,context,packet_eq]
    rfl)
  simpa only [machine,input,output,FeatureContextMap.result,FeatureMapPairLoader.packet,
    packet_eq,context,f,↓reduceIte] using BitMachine.outputsWithin_mono _ h hb

theorem callback_input (n i j : ℕ) (x y : ℚ) :
    callback.result (LawProductFormatter.input n i j x y) =
      EncodedCommunication.natField (LawProductFormatter.output n i j x y).length ++
        LawProductFormatter.output n i j x y := by
  simp only [callback,PhysicalProducer.compose,Function.comp_apply,
    LawProductFormatter.result_input,item,SourceListMachineWriter.result,
    ↓reduceIte]

theorem row_typed (n i : ℕ) (x : ℚ) (ys : List (ℕ × ℚ)) :
    rowOutput (n.bits,CodeDTargetV2.alphabetEntry (i,x),ys.map CodeDTargetV2.alphabetEntry) =
      SourceListEncoding.fields (ys.map (fun y => LawProductFormatter.output n i y.1 x y.2)) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [rowOutput,List.map_cons,List.flatMap_cons,SourceListEncoding.fields] at *
    have hi := callback_input n i y.1 x y.2
    simp only [LawProductFormatter.input] at hi
    simpa only [packet_eq,hi,List.append_assoc] using congrArg
      (fun tail => callback.result
        (BitMachineBankCodec.encode ![BitMachineBankCodec.encode
          ![n.bits,CodeDTargetV2.alphabetEntry (i,x)],CodeDTargetV2.alphabetEntry y]) ++ tail) ih

theorem output_typed (n : ℕ) (xs ys : List (ℕ × ℚ)) :
    output (n.bits,xs.map CodeDTargetV2.alphabetEntry,ys.map CodeDTargetV2.alphabetEntry)=
      SourceListEncoding.fields (xs.flatMap (fun x => ys.map
        (fun y => LawProductFormatter.output n x.1 y.1 x.2 y.2))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [output,List.map_cons,List.flatMap_cons] at *
    rw [row_typed,AppendEntryPhysical.fields_append]
    exact congrArg (fun tail => SourceListEncoding.fields
      (ys.map (fun y => LawProductFormatter.output n x.1 y.1 x.2 y.2)) ++ tail) ih

#print axioms row_realizes
#print axioms realizes
#print axioms row_typed
end
end CurrentAdditive.V40LawCartesianRows
