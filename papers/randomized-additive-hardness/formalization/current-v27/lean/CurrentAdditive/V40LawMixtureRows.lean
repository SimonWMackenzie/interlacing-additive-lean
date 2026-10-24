import CurrentAdditive.V40LawJobsClock
import CurrentAdditive.LawMixtureFormatter
import CurrentAdditive.CylinderEvalMapPolynomial

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawMixtureRows
open EthInapproximability.CurrentPaper
open PhysicalProducer V40LawJobsClock
noncomputable section

def callback (branch : Bool) : Producer :=
  PhysicalProducer.compose (LawMixtureFormatter.producer branch) item

abbrev Data := List Bool × List (List Bool)
def input (a : Data) : List Bool := V40LawPacket.packet a.1 (SourceListEncoding.encode a.2)
def output (branch : Bool) (a : Data) : List Bool :=
  a.2.flatMap (fun w => (callback branch).result (V40LawPacket.packet a.1 w))
def machine (branch : Bool) : BitMachine.Machine :=
  FeatureContextMap.machine (callback branch).machine false

theorem realizes (branch : Bool) : Realizes (machine branch) input (output branch) := by
  obtain ⟨c,e,hCallback⟩ := V40LawJobsClock.producer (callback branch) (id : List Bool → List Bool)
  obtain ⟨C,d,hC⟩ := CylinderEvalMapPolynomial.uniform_from_callback
    (callback branch).machine false c e
  refine ⟨C,d,?_⟩
  intro a
  let f := fun w => (callback branch).result (V40LawPacket.packet a.1 w)
  let b := fun w : List Bool => c*((V40LawPacket.packet a.1 w).length+1)^e
  have hM : ∀w∈a.2,(callback branch).machine.OutputsWithin
      (FeatureMapPairLoader.packet a.1 w) (f w) (b w) := by
    intro w _
    simpa only [f,b,FeatureMapPairLoader.packet,packet_eq] using
      hCallback (V40LawPacket.packet a.1 w)
  have h := FeatureContextMap.outputs_explicit (callback branch).machine false a.1 a.2 f b hM
  have hb := hC a.1 a.2 f b hM (by
    intro w _
    simp only [b,FeatureMapPairLoader.packet,packet_eq]
    rfl)
  simpa only [machine,input,output,FeatureContextMap.result,FeatureMapPairLoader.packet,
    packet_eq,f,↓reduceIte] using BitMachine.outputsWithin_mono _ h hb

theorem callback_input (branch : Bool) (offset j : ℕ) (y : ℚ) :
    (callback branch).result (LawMixtureFormatter.input offset j y) =
      EncodedCommunication.natField (LawMixtureFormatter.output branch offset j y).length ++
        LawMixtureFormatter.output branch offset j y := by
  simp only [callback,PhysicalProducer.compose,Function.comp_apply,
    LawMixtureFormatter.result_input,item,SourceListMachineWriter.result,↓reduceIte]

theorem output_typed (branch : Bool) (offset : ℕ) (xs : List (ℕ × ℚ)) :
    output branch (offset.bits,xs.map CodeDTargetV2.alphabetEntry)=
      SourceListEncoding.fields (xs.map (fun x => LawMixtureFormatter.output branch offset x.1 x.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [output,List.map_cons,List.flatMap_cons,SourceListEncoding.fields] at *
    have hi := callback_input branch offset x.1 x.2
    simp only [LawMixtureFormatter.input] at hi
    simpa only [packet_eq,hi,List.append_assoc] using congrArg
      (fun tail => (callback branch).result (BitMachineBankCodec.encode
        ![offset.bits,CodeDTargetV2.alphabetEntry x]) ++ tail) ih

#print axioms realizes
#print axioms output_typed
end
end CurrentAdditive.V40LawMixtureRows
