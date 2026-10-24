import CurrentAdditive.V40LawRetained
import CurrentAdditive.V40NumberedLawAlgebra

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40SourceColumnLaw
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction PhysicalProducer V40LawJobsClock
noncomputable section

structure Data where
  q₂ : ℕ
  outerSize : ℕ
  gammaSize : ℕ
  hq : 0<q₂
  outerLaw : PositiveRationalLaw (Fin outerSize)
  gammaLaw : PositiveRationalLaw (Fin gammaSize)

def input (a : Data) := BitMachineBankCodec.encode
  (![List.replicate a.q₂ true,StoredWeightedState.lawBytes a.outerLaw,
    StoredWeightedState.lawBytes a.gammaLaw] : Fin 3 → List Bool)
def productData (a : Data) : V40StoredLawOperations.Data :=
  ⟨a.outerSize,a.gammaSize,a.outerLaw,a.gammaLaw⟩
def uniformData (a : Data) : V40UniformLawJobs.Data :=
  ⟨0,a.q₂,a.gammaSize,a.hq,a.gammaLaw⟩
def secondLaw (a : Data) := reindex finProdFinEquiv
  (product (V40UniformLawJobs.uniformLaw (uniformData a)) a.gammaLaw)
def mixData (a : Data) : V40StoredLawOperations.Data :=
  ⟨a.outerSize*a.gammaSize,a.q₂*a.gammaSize,
    V40StoredLawOperations.productLaw (productData a),secondLaw a⟩
def law (a : Data) := V40StoredLawOperations.mixtureLaw (mixData a)
def firstComp (a : Data) := V40LawJobOrder.companions a.outerLaw a.gammaLaw
def secondComp (a : Data) := V40LawJobOrder.companions
  (V40UniformLawJobs.uniformLaw (uniformData a)) a.gammaLaw
def mixComp (a : Data) := V40LawMixtureOrder.companions
  (V40StoredLawOperations.productLaw (productData a)) (secondLaw a)
def output (a : Data) := BitMachineBankCodec.encode
  (![input a,StoredWeightedState.lawBytes (law a),
    BitMachineBankCodec.encode (![firstComp a,secondComp a,mixComp a] : Fin 3 → List Bool)] : Fin 3 → List Bool)

def prepare : Producer := pair identity (pair (projection (1 : Fin 3)) (projection (2 : Fin 3)))
def source1 : Producer := projection (0 : Fin 2)
def prepareUniform : Producer := pair identity (triple LawJobBitPrimitives.empty
  (PhysicalProducer.compose source1 (projection (0 : Fin 3)))
  (PhysicalProducer.compose source1 (projection (2 : Fin 3))))
def saved : Producer := projection (0 : Fin 2)
def uniformResult : Producer := projection (1 : Fin 2)
def original : Producer := PhysicalProducer.compose saved (projection (0 : Fin 2))
def oldProduct : Producer := PhysicalProducer.compose saved (projection (1 : Fin 2))
def oldLaw : Producer := PhysicalProducer.compose oldProduct (projection (0 : Fin 2))
def oldComp : Producer := PhysicalProducer.compose oldProduct (projection (1 : Fin 2))
def newLaw : Producer := PhysicalProducer.compose
  (PhysicalProducer.compose uniformResult (projection (1 : Fin 3))) (projection (1 : Fin 2))
def newComp : Producer := PhysicalProducer.compose uniformResult (projection (2 : Fin 3))
def prepareMix : Producer := pair (triple original oldComp newComp) (pair oldLaw newLaw)
def mixHeader : Producer := projection (0 : Fin 2)
def mixResult : Producer := projection (1 : Fin 2)
def finish : Producer := triple
  (PhysicalProducer.compose mixHeader (projection (0 : Fin 3)))
  (PhysicalProducer.compose mixResult (projection (0 : Fin 2)))
  (triple (PhysicalProducer.compose mixHeader (projection (1 : Fin 3)))
    (PhysicalProducer.compose mixHeader (projection (2 : Fin 3)))
    (PhysicalProducer.compose mixResult (projection (1 : Fin 2))))

def w0 (a : Data) := V40LawPacket.packet (input a) (V40StoredLawOperations.input (productData a))
def w1 (a : Data) := V40LawPacket.packet (input a) (V40StoredLawOperations.productOutput (productData a))
def w2 (a : Data) := V40LawPacket.packet (w1 a) (V40UniformLawJobs.input (uniformData a))
def w3 (a : Data) := V40LawPacket.packet (w1 a) (V40UniformLawJobs.output false (uniformData a))
def header (a : Data) := BitMachineBankCodec.encode (![input a,firstComp a,secondComp a] : Fin 3 → List Bool)
def w4 (a : Data) := V40LawPacket.packet (header a) (V40StoredLawOperations.input (mixData a))
def w5 (a : Data) := V40LawPacket.packet (header a) (V40StoredLawOperations.mixtureOutput (mixData a))

def first := BitMachineComposition.composition prepare.machine
  (V40LawBankMap.liftMachine V40StoredLawOperations.productWithCompanion)
def second := BitMachineComposition.composition first prepareUniform.machine
def third := BitMachineComposition.composition second
  (V40LawBankMap.liftMachine (V40UniformLawJobs.machine false))
def fourth := BitMachineComposition.composition third prepareMix.machine
def fifth := BitMachineComposition.composition fourth
  (V40LawBankMap.liftMachine V40StoredLawOperations.mixtureWithCompanion)
def machine := BitMachineComposition.composition fifth finish.machine

theorem prepare_input (a : Data) : prepare.result (input a)=w0 a := by
  simp [prepare,input,w0,V40StoredLawOperations.input,productData,projection,packet_eq]
theorem prepareUniform_input (a : Data) : prepareUniform.result (w1 a)=w2 a := by
  simp [prepareUniform,source1,w1,w2,input,uniformData,V40UniformLawJobs.input,
    PhysicalProducer.compose,projection,LawJobBitPrimitives.empty,packet_eq]
theorem prepareMix_input (a : Data) : prepareMix.result (w3 a)=w4 a := by
  simp [prepareMix,original,oldComp,newComp,oldLaw,newLaw,oldProduct,saved,uniformResult,
    w3,w1,w4,header,firstComp,secondComp,V40StoredLawOperations.input,mixData,
    V40StoredLawOperations.productOutput,V40UniformLawJobs.output,V40UniformLawJobs.law,
    V40UniformLawJobs.companions,secondLaw,PhysicalProducer.compose,projection,packet_eq]
  rfl
theorem finish_input (a : Data) : finish.result (w5 a)=output a := by
  simp [finish,mixHeader,mixResult,w5,header,output,V40StoredLawOperations.mixtureOutput,
    law,mixData,mixComp,PhysicalProducer.compose,projection,packet_eq]
  rfl

/-- The two products and their 255/256--1/256 mixture are actually run,
including the uniform q₂ factor generated from unary q₂. All earlier input
bytes and all three exact decoder-companion lists remain in the output. -/
theorem realizes : Realizes machine input output := by
  have h0 := producer prepare input
  simp only [prepare_input] at h0
  have hp : Realizes V40StoredLawOperations.productWithCompanion
      (fun a : Data => V40StoredLawOperations.input (productData a))
      (fun a => V40StoredLawOperations.productOutput (productData a)) := by
    obtain ⟨C,d,h⟩ := V40StoredLawOperations.product_realizes
    exact ⟨C,d,fun a => h (productData a)⟩
  have h1 := bank_map _ input _ _ hp
  have h2 := producer prepareUniform w1
  simp only [prepareUniform_input] at h2
  have hu : Realizes (V40UniformLawJobs.machine false)
      (fun a : Data => V40UniformLawJobs.input (uniformData a))
      (fun a => V40UniformLawJobs.output false (uniformData a)) := by
    obtain ⟨C,d,h⟩ := V40UniformLawJobs.realizes false
    exact ⟨C,d,fun a => h (uniformData a)⟩
  have h3 := bank_map _ w1 _ _ hu
  have h4 := producer prepareMix w3
  simp only [prepareMix_input] at h4
  have hm : Realizes V40StoredLawOperations.mixtureWithCompanion
      (fun a : Data => V40StoredLawOperations.input (mixData a))
      (fun a => V40StoredLawOperations.mixtureOutput (mixData a)) := by
    obtain ⟨C,d,h⟩ := V40StoredLawOperations.mixture_realizes
    exact ⟨C,d,fun a => h (mixData a)⟩
  have h5 := bank_map _ header _ _ hm
  have h6 := producer finish w5
  simp only [finish_input] at h6
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _
          (V40LawJobsClock.compose _ _ _ _ _
            (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6

theorem actual_column {D q₁ q₂ s nx ny : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) :
    law ⟨q₂,src.outer.size,src.gamma.size,NeZero.pos q₂,src.outer.law,src.gamma.law⟩=
      reindex src.columnOrder src.columnLaw := V40NumberedLawAlgebra.column_eq src

#print axioms realizes
#print axioms actual_column
end
end CurrentAdditive.V40SourceColumnLaw
