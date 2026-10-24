import CurrentAdditive.V40SourceColumnLaw

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40FinalSourceRequest
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction PhysicalProducer V40LawJobsClock
noncomputable section

structure Data where
  Q : ℕ
  w : ℕ
  q₂ : ℕ
  outerSize : ℕ
  gammaSize : ℕ
  hw : 0<w
  hq : 0<q₂
  outerLaw : PositiveRationalLaw (Fin outerSize)
  gammaLaw : PositiveRationalLaw (Fin gammaSize)

def input (a : Data) := BitMachineBankCodec.encode
  (![List.replicate a.Q true,List.replicate a.w true,List.replicate a.q₂ true,
    StoredWeightedState.lawBytes a.outerLaw,StoredWeightedState.lawBytes a.gammaLaw] : Fin 5 → List Bool)
def columnData (a : Data) : V40SourceColumnLaw.Data :=
  ⟨a.q₂,a.outerSize,a.gammaSize,a.hq,a.outerLaw,a.gammaLaw⟩
def uniformData (a : Data) : V40UniformLawJobs.Data :=
  ⟨a.Q,a.w,a.outerSize*a.gammaSize+a.q₂*a.gammaSize,a.hw,V40SourceColumnLaw.law (columnData a)⟩
def law (a : Data) := reindex finProdFinEquiv
  (product (V40UniformLawJobs.uniformLaw (uniformData a)) (V40SourceColumnLaw.law (columnData a)))
def columnComp (a : Data) := BitMachineBankCodec.encode
  (![V40SourceColumnLaw.firstComp (columnData a),V40SourceColumnLaw.secondComp (columnData a),
    V40SourceColumnLaw.mixComp (columnData a)] : Fin 3 → List Bool)
def uniformComp (a : Data) := V40LawJobOrder.companions
  (V40UniformLawJobs.uniformLaw (uniformData a)) (V40SourceColumnLaw.law (columnData a))
def request (a : Data) := V40LawPacket.packet (List.replicate a.Q true) (StoredWeightedState.lawBytes (law a))
def output (a : Data) := BitMachineBankCodec.encode
  (![input a,request a,V40LawPacket.packet (columnComp a) (uniformComp a)] : Fin 3 → List Bool)

def prepare : Producer := pair identity
  (triple (projection (2 : Fin 5)) (projection (3 : Fin 5)) (projection (4 : Fin 5)))
def source : Producer := projection (0 : Fin 2)
def columnResult : Producer := projection (1 : Fin 2)
def route : Producer := pair
  (pair source (PhysicalProducer.compose columnResult (projection (2 : Fin 3))))
  (triple (PhysicalProducer.compose source (projection (0 : Fin 5)))
    (PhysicalProducer.compose source (projection (1 : Fin 5)))
    (PhysicalProducer.compose columnResult (projection (1 : Fin 3))))
def saved : Producer := projection (0 : Fin 2)
def uniformResult : Producer := projection (1 : Fin 2)
def finish : Producer := triple
  (PhysicalProducer.compose saved (projection (0 : Fin 2)))
  (PhysicalProducer.compose uniformResult (projection (1 : Fin 3)))
  (pair (PhysicalProducer.compose saved (projection (1 : Fin 2)))
    (PhysicalProducer.compose uniformResult (projection (2 : Fin 3))))

def w0 (a : Data) := V40LawPacket.packet (input a) (V40SourceColumnLaw.input (columnData a))
def w1 (a : Data) := V40LawPacket.packet (input a) (V40SourceColumnLaw.output (columnData a))
def header (a : Data) := V40LawPacket.packet (input a) (columnComp a)
def w2 (a : Data) := V40LawPacket.packet (header a) (V40UniformLawJobs.input (uniformData a))
def w3 (a : Data) := V40LawPacket.packet (header a) (V40UniformLawJobs.output false (uniformData a))
def first := BitMachineComposition.composition prepare.machine (V40LawBankMap.liftMachine V40SourceColumnLaw.machine)
def second := BitMachineComposition.composition first route.machine
def third := BitMachineComposition.composition second (V40LawBankMap.liftMachine (V40UniformLawJobs.machine false))
def machine := BitMachineComposition.composition third finish.machine

theorem prepare_input (a : Data) : prepare.result (input a)=w0 a := by
  simp [prepare,input,w0,columnData,V40SourceColumnLaw.input,projection,packet_eq]
theorem route_input (a : Data) : route.result (w1 a)=w2 a := by
  simp [route,source,columnResult,w1,w2,header,input,columnComp,uniformData,
    V40SourceColumnLaw.output,V40UniformLawJobs.input,PhysicalProducer.compose,projection,packet_eq]
  rfl
theorem finish_input (a : Data) : finish.result (w3 a)=output a := by
  simp [finish,saved,uniformResult,w3,header,output,request,law,uniformComp,
    V40UniformLawJobs.output,V40UniformLawJobs.law,V40UniformLawJobs.companions,
    PhysicalProducer.compose,projection,packet_eq]
  rfl

/-- The seventh request is built from the original outer/gamma law vectors
and the unary public counts. Its source-column mixture and uniform w factor
are actually constructed; no precomputed final alphabet is supplied. -/
theorem realizes : Realizes machine input output := by
  have h0 := producer prepare input
  simp only [prepare_input] at h0
  have hc : Realizes V40SourceColumnLaw.machine
      (fun a : Data => V40SourceColumnLaw.input (columnData a))
      (fun a => V40SourceColumnLaw.output (columnData a)) := by
    obtain ⟨C,d,h⟩ := V40SourceColumnLaw.realizes
    exact ⟨C,d,fun a => h (columnData a)⟩
  have h1 := bank_map _ input _ _ hc
  have h2 := producer route w1
  simp only [route_input] at h2
  have hu : Realizes (V40UniformLawJobs.machine false)
      (fun a : Data => V40UniformLawJobs.input (uniformData a))
      (fun a => V40UniformLawJobs.output false (uniformData a)) := by
    obtain ⟨C,d,h⟩ := V40UniformLawJobs.realizes false
    exact ⟨C,d,fun a => h (uniformData a)⟩
  have h3 := bank_map _ header _ _ hu
  have h4 := producer finish w3
  simp only [finish_input] at h4
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2) h3) h4

theorem actual_law {D q₁ q₂ s w Q nx ny : ℕ}
    [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w]
    {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) :
    law ⟨Q,w,q₂,src.outer.size,src.gamma.size,NeZero.pos w,NeZero.pos q₂,src.outer.law,src.gamma.law⟩=
      reindex ((Equiv.prodCongr (Equiv.refl _) src.columnOrder).trans finProdFinEquiv)
        (product (uniform w) src.columnLaw) := V40NumberedLawAlgebra.final_input_law (w := w) src

#print axioms realizes
#print axioms actual_law
end
end CurrentAdditive.V40FinalSourceRequest
