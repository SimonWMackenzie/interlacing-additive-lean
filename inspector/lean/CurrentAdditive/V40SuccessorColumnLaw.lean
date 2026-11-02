import CurrentAdditive.V40LawRetained
import CurrentAdditive.V40NumberedLawAlgebra

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40SuccessorColumnLaw
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction PhysicalProducer V40LawJobsClock
noncomputable section

structure Data where
  Q : ℕ
  m : ℕ
  b : ℕ
  t : ℕ
  hQ : 0<Q
  metadata : PositiveRationalLaw (Fin m)
  base : PositiveRationalLaw (Fin b)
  selector : PositiveRationalLaw (Fin t)

def input (a : Data) := BitMachineBankCodec.encode
  (![List.replicate a.Q true,StoredWeightedState.lawBytes a.metadata,
    StoredWeightedState.lawBytes a.base,StoredWeightedState.lawBytes a.selector] : Fin 4 → List Bool)
def baseData (a : Data) : V40StoredLawOperations.Data := ⟨a.b,a.t,a.base,a.selector⟩
def streamData (a : Data) : V40StoredLawOperations.Data :=
  ⟨a.m,a.b*a.t,a.metadata,V40StoredLawOperations.productLaw (baseData a)⟩
def uniformData (a : Data) : V40UniformLawJobs.Data :=
  ⟨0,a.Q,a.m*(a.b*a.t),a.hQ,V40StoredLawOperations.productLaw (streamData a)⟩
def law (a : Data) := reindex finProdFinEquiv
  (product (V40UniformLawJobs.uniformLaw (uniformData a))
    (V40StoredLawOperations.productLaw (streamData a)))
def baseComp (a : Data) := V40LawJobOrder.companions a.base a.selector
def streamComp (a : Data) := V40LawJobOrder.companions a.metadata
  (V40StoredLawOperations.productLaw (baseData a))
def uniformComp (a : Data) := V40LawJobOrder.companions
  (V40UniformLawJobs.uniformLaw (uniformData a))
  (V40StoredLawOperations.productLaw (streamData a))
def output (a : Data) := BitMachineBankCodec.encode
  (![input a,StoredWeightedState.lawBytes (law a),
    BitMachineBankCodec.encode (![baseComp a,streamComp a,uniformComp a] : Fin 3 → List Bool)] : Fin 3 → List Bool)

def prepare : Producer := pair identity (pair (projection (2 : Fin 4)) (projection (3 : Fin 4)))
def source1 : Producer := projection (0 : Fin 2)
def pair1 : Producer := projection (1 : Fin 2)
def prepareStream : Producer := pair
  (pair source1 (PhysicalProducer.compose pair1 (projection (1 : Fin 2))))
  (pair (PhysicalProducer.compose source1 (projection (1 : Fin 4)))
    (PhysicalProducer.compose pair1 (projection (0 : Fin 2))))
def saved : Producer := projection (0 : Fin 2)
def streamResult : Producer := projection (1 : Fin 2)
def original : Producer := PhysicalProducer.compose saved (projection (0 : Fin 2))
def oldComp : Producer := PhysicalProducer.compose saved (projection (1 : Fin 2))
def streamLaw : Producer := PhysicalProducer.compose streamResult (projection (0 : Fin 2))
def newComp : Producer := PhysicalProducer.compose streamResult (projection (1 : Fin 2))
def prepareUniform : Producer := pair (triple original oldComp newComp)
  (triple LawJobBitPrimitives.empty (PhysicalProducer.compose original (projection (0 : Fin 4))) streamLaw)
def finalHeader : Producer := projection (0 : Fin 2)
def finalUniform : Producer := projection (1 : Fin 2)
def finish : Producer := triple
  (PhysicalProducer.compose finalHeader (projection (0 : Fin 3)))
  (PhysicalProducer.compose (PhysicalProducer.compose finalUniform (projection (1 : Fin 3))) (projection (1 : Fin 2)))
  (triple (PhysicalProducer.compose finalHeader (projection (1 : Fin 3)))
    (PhysicalProducer.compose finalHeader (projection (2 : Fin 3)))
    (PhysicalProducer.compose finalUniform (projection (2 : Fin 3))))

def w0 (a : Data) := V40LawPacket.packet (input a) (V40StoredLawOperations.input (baseData a))
def w1 (a : Data) := V40LawPacket.packet (input a) (V40StoredLawOperations.productOutput (baseData a))
def header1 (a : Data) := V40LawPacket.packet (input a) (baseComp a)
def w2 (a : Data) := V40LawPacket.packet (header1 a) (V40StoredLawOperations.input (streamData a))
def w3 (a : Data) := V40LawPacket.packet (header1 a) (V40StoredLawOperations.productOutput (streamData a))
def header2 (a : Data) := BitMachineBankCodec.encode (![input a,baseComp a,streamComp a] : Fin 3 → List Bool)
def w4 (a : Data) := V40LawPacket.packet (header2 a) (V40UniformLawJobs.input (uniformData a))
def w5 (a : Data) := V40LawPacket.packet (header2 a) (V40UniformLawJobs.output false (uniformData a))

def first := BitMachineComposition.composition prepare.machine
  (V40LawBankMap.liftMachine V40StoredLawOperations.productWithCompanion)
def second := BitMachineComposition.composition first prepareStream.machine
def third := BitMachineComposition.composition second
  (V40LawBankMap.liftMachine V40StoredLawOperations.productWithCompanion)
def fourth := BitMachineComposition.composition third prepareUniform.machine
def fifth := BitMachineComposition.composition fourth
  (V40LawBankMap.liftMachine (V40UniformLawJobs.machine false))
def machine := BitMachineComposition.composition fifth finish.machine

theorem prepare_input (a : Data) : prepare.result (input a)=w0 a := by
  simp [prepare,input,w0,V40StoredLawOperations.input,baseData,projection,packet_eq]
theorem prepareStream_input (a : Data) : prepareStream.result (w1 a)=w2 a := by
  simp [prepareStream,source1,pair1,w1,w2,header1,input,V40StoredLawOperations.productOutput,
    V40StoredLawOperations.input,streamData,baseData,baseComp,PhysicalProducer.compose,projection,packet_eq]
theorem prepareUniform_input (a : Data) : prepareUniform.result (w3 a)=w4 a := by
  simp [prepareUniform,original,oldComp,newComp,streamLaw,saved,streamResult,
    w3,w4,header1,header2,input,uniformData,V40UniformLawJobs.input,
    V40StoredLawOperations.productOutput,streamComp,PhysicalProducer.compose,projection,
    LawJobBitPrimitives.empty,packet_eq]
  rfl
theorem finish_input (a : Data) : finish.result (w5 a)=output a := by
  simp [finish,finalHeader,finalUniform,w5,header2,output,V40UniformLawJobs.output,
    V40UniformLawJobs.law,V40UniformLawJobs.companions,law,uniformComp,
    PhysicalProducer.compose,projection,packet_eq]
  rfl

/-- The final column law is physically built in the exact order
uniform Q × (metadata × (base × selector)). The complete input and the
three ordered coordinate-companion lists remain available. -/
theorem realizes : Realizes machine input output := by
  have h0 := producer prepare input
  simp only [prepare_input] at h0
  have hp : Realizes V40StoredLawOperations.productWithCompanion
      (fun a : Data => V40StoredLawOperations.input (baseData a))
      (fun a => V40StoredLawOperations.productOutput (baseData a)) := by
    obtain ⟨C,d,h⟩ := V40StoredLawOperations.product_realizes
    exact ⟨C,d,fun a => h (baseData a)⟩
  have h1 := bank_map _ input _ _ hp
  have h2 := producer prepareStream w1
  simp only [prepareStream_input] at h2
  have hs : Realizes V40StoredLawOperations.productWithCompanion
      (fun a : Data => V40StoredLawOperations.input (streamData a))
      (fun a => V40StoredLawOperations.productOutput (streamData a)) := by
    obtain ⟨C,d,h⟩ := V40StoredLawOperations.product_realizes
    exact ⟨C,d,fun a => h (streamData a)⟩
  have h3 := bank_map _ header1 _ _ hs
  have h4 := producer prepareUniform w3
  simp only [prepareUniform_input] at h4
  have hu : Realizes (V40UniformLawJobs.machine false)
      (fun a : Data => V40UniformLawJobs.input (uniformData a))
      (fun a => V40UniformLawJobs.output false (uniformData a)) := by
    obtain ⟨C,d,h⟩ := V40UniformLawJobs.realizes false
    exact ⟨C,d,fun a => h (uniformData a)⟩
  have h5 := bank_map _ header2 _ _ hu
  have h6 := producer finish w5
  simp only [finish_input] at h6
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _
          (V40LawJobsClock.compose _ _ _ _ _
            (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6

theorem actual_column {D q₁ q₂ s w Q nx ny ni : ℕ}
    [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
    {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
    {μI : PositiveRationalLaw (Fin ni)}
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (st : src.Streams (w := w) (μI := μI)) :
    law ⟨Q,st.metadata.size,st.base.size,st.selector.size,NeZero.pos Q,
      st.metadata.law,st.base.law,st.selector.law⟩=
      reindex (SourceData.successorColumnOrder src st)
        (product (uniform Q) (SourceData.Streams.law src st)) :=
  V40NumberedLawAlgebra.successor_column_law (Q := Q) src st

#print axioms realizes
#print axioms actual_column
end
end CurrentAdditive.V40SuccessorColumnLaw
