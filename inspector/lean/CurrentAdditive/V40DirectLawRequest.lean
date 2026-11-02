import CurrentAdditive.V40LawRetained

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40DirectLawRequest
open EthInapproximability.CurrentPaper
open Paper2 PhysicalProducer V40LawJobsClock
noncomputable section

structure Data where
  q : ℕ
  n : ℕ
  μ : PositiveRationalLaw (Fin n)

def input (a : Data) := V40LawPacket.packet (List.replicate a.q true) (StoredWeightedState.lawBytes a.μ)
def output (a : Data) := BitMachineBankCodec.encode
  (![input a,V40LawCodeDPacket.codeDInput a.q (IndexedLaw.indexedAlphabet a.μ.weight),[]] : Fin 3 → List Bool)
def implementation : Producer := triple identity identity LawJobBitPrimitives.empty
def machine := implementation.machine

theorem result_input (a : Data) : implementation.result (input a)=output a := by
  simp [implementation,output,input,LawJobBitPrimitives.empty,V40LawCodeDPacket.codeDInput,
    StoredWeightedState.lawBytes,StoredWeightedState.lawAlphabet,IndexedLaw.indexedAlphabet,packet_eq]

/-- Gamma, base, and selector requests reuse their literal stored law
vector. Their original packet is copied and the companion list is empty. -/
theorem realizes : Realizes machine input output := by
  have h := producer implementation input
  simpa only [result_input] using h

#print axioms realizes
end
end CurrentAdditive.V40DirectLawRequest
