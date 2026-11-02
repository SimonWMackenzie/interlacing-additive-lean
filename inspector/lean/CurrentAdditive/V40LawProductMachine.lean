import CurrentAdditive.V40LawProductJobs
import CurrentAdditive.V40LawSerializeJobs
import CurrentAdditive.StoredWeightedState

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawProductMachine
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction V40LawJobsClock
noncomputable section

def input {m n : ℕ} (q : ℕ) (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List Bool :=
  BitMachineBankCodec.encode (![List.replicate q true,
    StoredWeightedState.lawBytes μ,StoredWeightedState.lawBytes ν] : Fin 3 → List Bool)

def output {m n : ℕ} (q : ℕ) (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List Bool :=
  BitMachineBankCodec.encode (![input q μ ν,
    V40LawCodeDPacket.codeDInput q
      (IndexedLaw.indexedAlphabet (reindex finProdFinEquiv (product μ ν)).weight),
    V40LawJobOrder.companions μ ν] : Fin 3 → List Bool)

def machine : BitMachine.Machine := BitMachineComposition.composition
  V40LawProductJobs.machine V40LawSerializeJobs.machine

theorem storedBytes_entries {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    StoredWeightedState.lawBytes μ=SourceListEncoding.encode (V40LawJobOrder.entries μ) :=
  V40LawJobOrder.lawBytes_entries μ

theorem input_eq (a : V40LawProductJobs.Data) :
    input a.q a.μ a.ν=V40LawProductJobs.input a := by
  simp only [input,storedBytes_entries,V40LawProductJobs.input,V40LawJobsRouting.input]

/-- A fixed finite Boolean-stack program consumes the two stored law
vectors, builds the ordered jobs and coordinate companions, and physically
normalizes every rational product. Its Code D field is the exact canonical
alphabet of the current numbered product law. -/
theorem realizes : Realizes machine
    (fun a : V40LawProductJobs.Data => input a.q a.μ a.ν)
    (fun a => output a.q a.μ a.ν) := by
  have h0 := V40LawProductJobs.realizes
  have h1 := V40LawSerializeJobs.realizes V40LawProductJobs.input
    V40LawProductJobs.Data.q
    (fun a => V40LawActualProduct.productJobs a.μ a.ν)
    (fun a => V40LawJobOrder.companions a.μ a.ν)
  have h := V40LawJobsClock.compose _ _ _ _ _ h0 h1
  have hi : V40LawProductJobs.input=(fun a => input a.q a.μ a.ν) :=
    funext (fun a => (input_eq a).symm)
  simpa only [hi,machine,V40LawSerializeJobs.output,V40LawActualProduct.product_alphabet,output]
    using h

theorem outputs_polynomial : ∃ C d : ℕ, ∀ (q m n : ℕ)
    (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)),
    machine.OutputsWithin (input q μ ν) (output q μ ν)
      (C*((input q μ ν).length+1)^d) := by
  obtain ⟨C,d,h⟩ := realizes
  exact ⟨C,d,fun q m n μ ν => h ⟨q,m,n,μ,ν⟩⟩

#print axioms realizes
#print axioms outputs_polynomial
end
end CurrentAdditive.V40LawProductMachine
