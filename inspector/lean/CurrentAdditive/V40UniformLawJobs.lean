import CurrentAdditive.V40StoredLawOperations
import CurrentAdditive.V40UniformLawClock

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40UniformLawJobs
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction PhysicalProducer V40LawJobsClock
noncomputable section

structure Data where
  q : ℕ
  n : ℕ
  m : ℕ
  hn : 0<n
  μ : PositiveRationalLaw (Fin m)

def uniformLaw (a : Data) : PositiveRationalLaw (Fin a.n) :=
  @V39GeneratedConstruction.uniform a.n ⟨Nat.ne_of_gt a.hn⟩

theorem law_ext {A : Type*} [Fintype A] (μ ν : PositiveRationalLaw A)
    (h : μ.weight=ν.weight) : μ=ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem uniformLaw_eq (a : Data) : uniformLaw a=
    @PositiveRationalLaw.uniform (Fin a.n) _ ⟨⟨0,a.hn⟩⟩ := by
  apply law_ext
  funext i
  simp [uniformLaw,V39GeneratedConstruction.uniform,PositiveRationalLaw.uniform]

def input (a : Data) : List Bool := BitMachineBankCodec.encode
  (![List.replicate a.q true,List.replicate a.n true,StoredWeightedState.lawBytes a.μ] : Fin 3 → List Bool)
def opInput (a : Data) := V40LawProductMachine.input a.q (uniformLaw a) a.μ
def opOutput (branch : Bool) (a : Data) : List Bool :=
  if branch then V40LawMixtureMachine.output a.q (uniformLaw a) a.μ
  else V40LawProductMachine.output a.q (uniformLaw a) a.μ
def opMachine (branch : Bool) : BitMachine.Machine :=
  if branch then V40LawMixtureMachine.machine else V40LawProductMachine.machine

def prepare : Producer := pair identity (projection (1 : Fin 3))
def source : Producer := projection (0 : Fin 2)
def generated : Producer := projection (1 : Fin 2)
def qPort : Producer := PhysicalProducer.compose source (projection (0 : Fin 3))
def other : Producer := PhysicalProducer.compose source (projection (2 : Fin 3))
def route : Producer := pair source (triple qPort generated other)
def answer : Producer := projection (1 : Fin 2)
def finish : Producer := triple source
  (PhysicalProducer.compose answer (projection (1 : Fin 3)))
  (PhysicalProducer.compose answer (projection (2 : Fin 3)))

def first := BitMachineComposition.composition prepare.machine
  (V40LawBankMap.liftMachine V40UniformLaw.machine)
def second := BitMachineComposition.composition first route.machine
def third (branch : Bool) := BitMachineComposition.composition second
  (V40LawBankMap.liftMachine (opMachine branch))
def machine (branch : Bool) := BitMachineComposition.composition (third branch) finish.machine

def law (branch : Bool) (a : Data) : List Bool :=
  if branch then StoredWeightedState.lawBytes (reindex finSumFinEquiv (mixture (uniformLaw a) a.μ))
  else StoredWeightedState.lawBytes (reindex finProdFinEquiv (product (uniformLaw a) a.μ))
def companions (branch : Bool) (a : Data) : List Bool :=
  if branch then V40LawMixtureOrder.companions (uniformLaw a) a.μ
  else V40LawJobOrder.companions (uniformLaw a) a.μ
def output (branch : Bool) (a : Data) := BitMachineBankCodec.encode
  (![input a,V40LawPacket.packet (List.replicate a.q true) (law branch a),
    companions branch a] : Fin 3 → List Bool)

theorem prepare_input (a : Data) : prepare.result (input a)=
    V40LawPacket.packet (input a) (List.replicate a.n true) := by
  simp [prepare,input,projection,packet_eq]

theorem route_input (a : Data) : route.result
    (V40LawPacket.packet (input a) (StoredWeightedState.lawBytes (uniformLaw a)))=
      V40LawPacket.packet (input a) (opInput a) := by
  simp [route,source,qPort,other,generated,PhysicalProducer.compose,projection,input,
    opInput,V40LawProductMachine.input,packet_eq]

theorem finish_input (branch : Bool) (a : Data) :
    finish.result (V40LawPacket.packet (input a) (opOutput branch a))=output branch a := by
  cases branch <;>
    simp [finish,source,answer,PhysicalProducer.compose,projection,opOutput,output,law,
      companions,V40LawProductMachine.output,V40LawMixtureMachine.output,
      V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,
      StoredWeightedState.lawAlphabet,IndexedLaw.indexedAlphabet,packet_eq]

theorem operation_realizes (branch : Bool) : Realizes (opMachine branch) opInput (opOutput branch) := by
  cases branch with
  | false =>
    obtain ⟨C,d,h⟩ := V40LawProductMachine.outputs_polynomial
    exact ⟨C,d,fun a => h a.q a.n a.m (uniformLaw a) a.μ⟩
  | true =>
    obtain ⟨C,d,h⟩ := V40LawMixtureMachine.outputs_polynomial
    exact ⟨C,d,fun a => h a.q a.n a.m (uniformLaw a) a.μ⟩

/-- The uniform factor is generated from its actual unary size by the
frozen uniform-law writer. Neither a precomputed uniform vector nor any
product/mixture result is present in the input. -/
theorem realizes (branch : Bool) : Realizes (machine branch) input (output branch) := by
  have h0 := producer prepare input
  simp only [prepare_input] at h0
  have hUniform : Realizes V40UniformLaw.machine
      (fun a : Data => List.replicate a.n true)
      (fun a => StoredWeightedState.lawBytes (uniformLaw a)) := by
    obtain ⟨C,d,h⟩ := V40UniformLaw.outputs_polynomial
    refine ⟨C,d,?_⟩
    intro a
    simpa only [uniformLaw_eq,List.length_replicate] using h a.n a.hn
  have h1 := bank_map _ input _ _ hUniform
  have h2 := producer route
    (fun a : Data => V40LawPacket.packet (input a) (StoredWeightedState.lawBytes (uniformLaw a)))
  simp only [route_input] at h2
  have h3 := bank_map _ input _ _ (operation_realizes branch)
  have h4 := producer finish (fun a => V40LawPacket.packet (input a) (opOutput branch a))
  simp only [finish_input] at h4
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _
      (V40LawJobsClock.compose _ _ _ _ _
        (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2) h3) h4

#print axioms realizes
end
end CurrentAdditive.V40UniformLawJobs
