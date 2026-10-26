import CurrentAdditive.CodeDWholeConstructor
import CurrentAdditive.IndexedLawBytesSource
import CurrentAdditive.V40LawJobsClock
import CurrentAdditive.CodeDSourceTupleMachine
import CurrentAdditive.V39ExecutableGenerated

/-! One actual CodeD invocation followed by actual positional-law and tuple
projections. All four stages read their original packed inputs physically;
the output contains the very same array and every indexed weight/tuple. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredSourcePhase
open Paper2 EthInapproximability.CurrentPaper PhysicalProducer V40LawJobsClock
open V39GeneratedConstruction
noncomputable section

structure Data where
  q : Nat
  n : Nat
  law : PositiveRationalLaw (Fin n)

def array (a : Data) := IndexedLaw.construct 8192 a.law.weight a.q
def source (a : Data) := (executableCodeD 8192).run a.q a.n a.law
def input (a : Data) := V40LawPacket.packet (List.replicate a.q true) (StoredWeightedState.lawBytes a.law)
def sourceBytes (a : Data) := CodeDCanonicalSourceV2.encodedSource (array a)
def lawBytes (a : Data) := StoredWeightedState.lawBytes (source a).law
def tupleBytes (a : Data) := SourceListEncoding.encode (CylinderProductionProjection.tupleWords (array a))
def output (a : Data) := BitMachineBankCodec.encode ![sourceBytes a,lawBytes a,tupleBytes a]

def prepare := pair identity identity
def requestSource := projection (1 : Fin 2)
def routeLaw := pair identity requestSource
def routeTuple := pair identity (PhysicalProducer.compose (projection (0 : Fin 2)) requestSource)
def finish := triple
  (PhysicalProducer.compose (PhysicalProducer.compose (projection (0 : Fin 2)) (projection (0 : Fin 2))) requestSource)
  (PhysicalProducer.compose (projection (0 : Fin 2)) (projection (1 : Fin 2)))
  (projection (1 : Fin 2))

def w0 (a : Data) := V40LawPacket.packet (input a) (input a)
def w1 (a : Data) := V40LawPacket.packet (input a) (sourceBytes a)
def w2 (a : Data) := V40LawPacket.packet (w1 a) (sourceBytes a)
def w3 (a : Data) := V40LawPacket.packet (w1 a) (lawBytes a)
def w4 (a : Data) := V40LawPacket.packet (w3 a) (sourceBytes a)
def w5 (a : Data) := V40LawPacket.packet (w3 a) (tupleBytes a)

def first := BitMachineComposition.composition prepare.machine (V40LawBankMap.liftMachine CodeDWholeConstructor.machine)
def second := BitMachineComposition.composition first routeLaw.machine
def third := BitMachineComposition.composition second (V40LawBankMap.liftMachine IndexedLawBytes.machine)
def fourth := BitMachineComposition.composition third routeTuple.machine
def fifth := BitMachineComposition.composition fourth (V40LawBankMap.liftMachine CodeDSourceTupleMachine.machine)
def machine := BitMachineComposition.composition fifth finish.machine

theorem prepare_result (a : Data) : prepare.result (input a)=w0 a := by simp [prepare,w0]
theorem routeLaw_result (a : Data) : routeLaw.result (w1 a)=w2 a := by
  simp [routeLaw,requestSource,w1,w2,projection,packet_eq]
theorem routeTuple_result (a : Data) : routeTuple.result (w3 a)=w4 a := by
  simp [routeTuple,requestSource,w1,w3,w4,PhysicalProducer.compose,projection,packet_eq]
theorem finish_result (a : Data) : finish.result (w5 a)=output a := by
  simp [finish,requestSource,w1,w3,w5,output,PhysicalProducer.compose,projection,packet_eq]

theorem construct_realizes : Realizes CodeDWholeConstructor.machine input sourceBytes := by
  refine ⟨CodeDWholeConstructor.coefficient,CodeDWholeConstructor.exponent,?_⟩
  intro a
  have h := CodeDWholeConstructor.indexed_outputs a.law.weight
    (fun i=>(a.law.positive i).le) a.law.total a.q
  simpa [input,sourceBytes,array,CodeDWholeConstructor.input,CodeDInitializer.input,
    StoredWeightedState.lawBytes,StoredWeightedState.lawAlphabet,IndexedLaw.indexedAlphabet,packet_eq] using h

theorem law_realizes : Realizes IndexedLawBytes.machine sourceBytes lawBytes := by
  obtain ⟨C,E,h⟩ := IndexedLawBytes.law_uniform
  exact ⟨C,E,fun a=>h a.q (array a) (source a).law (fun _=>rfl)⟩

theorem tuples_realizes : Realizes CodeDSourceTupleMachine.machine sourceBytes tupleBytes :=
  ⟨CodeDSourceTupleMachine.coefficient,3,fun a=>CodeDSourceTupleMachine.outputs (array a)⟩

/-- A single fixed source-generation phase prints the literal construct
array, its complete position-indexed law and its complete ordered tuple list.
Only a genuine positive rational input law is given. -/
theorem realizes : Realizes machine input output := by
  have h0 := producer prepare input
  simp only [prepare_result] at h0
  have h1 := bank_map CodeDWholeConstructor.machine input input sourceBytes construct_realizes
  have h2 := producer routeLaw w1
  simp only [routeLaw_result] at h2
  have h3 := bank_map IndexedLawBytes.machine w1 sourceBytes lawBytes law_realizes
  have h4 := producer routeTuple w3
  simp only [routeTuple_result] at h4
  have h5 := bank_map CodeDSourceTupleMachine.machine w3 sourceBytes tupleBytes tuples_realizes
  have h6 := producer finish w5
  simp only [finish_result] at h6
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _
          (V40LawJobsClock.compose _ _ _ _ _
            (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6

end
end CurrentAdditive.StoredSourcePhase

#print axioms CurrentAdditive.StoredSourcePhase.realizes
