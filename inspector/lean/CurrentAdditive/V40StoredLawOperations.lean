import CurrentAdditive.V40LawProductMachine
import CurrentAdditive.V40LawMixtureMachine

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40StoredLawOperations
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction PhysicalProducer V40LawJobsClock
noncomputable section

structure Data where
  m : ℕ
  n : ℕ
  μ : PositiveRationalLaw (Fin m)
  ν : PositiveRationalLaw (Fin n)

def input (a : Data) : List Bool := BitMachineBankCodec.encode
  (![StoredWeightedState.lawBytes a.μ,StoredWeightedState.lawBytes a.ν] : Fin 2 → List Bool)

def prepare : Producer := triple LawJobBitPrimitives.empty (projection (0 : Fin 2)) (projection (1 : Fin 2))
def request : Producer := projection (1 : Fin 3)
def resultLaw : Producer := PhysicalProducer.compose request (projection (1 : Fin 2))
def retain : Producer := pair resultLaw (projection (2 : Fin 3))

def productWithCompanion : BitMachine.Machine := BitMachineComposition.composition
  (BitMachineComposition.composition prepare.machine V40LawProductMachine.machine) retain.machine
def mixtureWithCompanion : BitMachine.Machine := BitMachineComposition.composition
  (BitMachineComposition.composition prepare.machine V40LawMixtureMachine.machine) retain.machine

def productLaw (a : Data) := reindex finProdFinEquiv (product a.μ a.ν)
def mixtureLaw (a : Data) := reindex finSumFinEquiv (mixture a.μ a.ν)
def productOutput (a : Data) : List Bool := V40LawPacket.packet
  (StoredWeightedState.lawBytes (productLaw a)) (V40LawJobOrder.companions a.μ a.ν)
def mixtureOutput (a : Data) : List Bool := V40LawPacket.packet
  (StoredWeightedState.lawBytes (mixtureLaw a)) (V40LawMixtureOrder.companions a.μ a.ν)

theorem prepare_input (a : Data) : prepare.result (input a)=V40LawProductMachine.input 0 a.μ a.ν := by
  simp [prepare,input,projection,LawJobBitPrimitives.empty,V40LawProductMachine.input]

theorem retain_product (a : Data) :
    retain.result (V40LawProductMachine.output 0 a.μ a.ν)=productOutput a := by
  simp [retain,resultLaw,request,PhysicalProducer.compose,projection,V40LawProductMachine.output,
    productOutput,productLaw,V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,
    StoredWeightedState.lawAlphabet,IndexedLaw.indexedAlphabet,packet_eq]

theorem retain_mixture (a : Data) :
    retain.result (V40LawMixtureMachine.output 0 a.μ a.ν)=mixtureOutput a := by
  simp [retain,resultLaw,request,PhysicalProducer.compose,projection,V40LawMixtureMachine.output,
    mixtureOutput,mixtureLaw,V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,
    StoredWeightedState.lawAlphabet,IndexedLaw.indexedAlphabet,packet_eq]

theorem product_realizes : Realizes productWithCompanion input productOutput := by
  have h0 := producer prepare input
  simp only [prepare_input] at h0
  have h1 : Realizes V40LawProductMachine.machine
      (fun a : Data => V40LawProductMachine.input 0 a.μ a.ν)
      (fun a => V40LawProductMachine.output 0 a.μ a.ν) := by
    obtain ⟨C,d,h⟩ := V40LawProductMachine.outputs_polynomial
    exact ⟨C,d,fun a => h 0 a.m a.n a.μ a.ν⟩
  have h2 := producer retain (fun a : Data => V40LawProductMachine.output 0 a.μ a.ν)
  simp only [retain_product] at h2
  exact V40LawJobsClock.compose _ _ _ _ _ (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2

theorem mixture_realizes : Realizes mixtureWithCompanion input mixtureOutput := by
  have h0 := producer prepare input
  simp only [prepare_input] at h0
  have h1 : Realizes V40LawMixtureMachine.machine
      (fun a : Data => V40LawMixtureMachine.input 0 a.μ a.ν)
      (fun a => V40LawMixtureMachine.output 0 a.μ a.ν) := by
    obtain ⟨C,d,h⟩ := V40LawMixtureMachine.outputs_polynomial
    exact ⟨C,d,fun a => h 0 a.m a.n a.μ a.ν⟩
  have h2 := producer retain (fun a : Data => V40LawMixtureMachine.output 0 a.μ a.ν)
  simp only [retain_mixture] at h2
  exact V40LawJobsClock.compose _ _ _ _ _ (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2

/-- Public law operations consume only the two actual stored law vectors.
Their output includes the exact original-position decoder companions. -/
theorem product_outputs : ∃ C d : ℕ, ∀ a : Data,
    productWithCompanion.OutputsWithin (input a) (productOutput a)
      (C*((input a).length+1)^d) := product_realizes

theorem mixture_outputs : ∃ C d : ℕ, ∀ a : Data,
    mixtureWithCompanion.OutputsWithin (input a) (mixtureOutput a)
      (C*((input a).length+1)^d) := mixture_realizes

#print axioms product_outputs
#print axioms mixture_outputs
end
end CurrentAdditive.V40StoredLawOperations
