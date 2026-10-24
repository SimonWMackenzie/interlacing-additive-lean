import CurrentAdditive.V40LawMixtureJobs
import CurrentAdditive.V40LawProductMachine

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawMixtureMachine
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction V40LawJobsClock
noncomputable section

def input := @V40LawProductMachine.input

def output {m n : ℕ} (q : ℕ) (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List Bool :=
  BitMachineBankCodec.encode (![input q μ ν,
    V40LawCodeDPacket.codeDInput q
      (IndexedLaw.indexedAlphabet (reindex finSumFinEquiv (mixture μ ν)).weight),
    V40LawMixtureOrder.companions μ ν] : Fin 3 → List Bool)

def machine : BitMachine.Machine := BitMachineComposition.composition
  V40LawMixtureJobs.machine V40LawSerializeJobs.machine

/-- The literal current mixture law, with canonical rational products,
original packet, left-then-right positions and exact branch companions. -/
theorem realizes : Realizes machine
    (fun a : V40LawProductJobs.Data => input a.q a.μ a.ν)
    (fun a => output a.q a.μ a.ν) := by
  have h0 := V40LawMixtureJobs.realizes
  have h1 := V40LawSerializeJobs.realizes V40LawMixtureJobs.input
    V40LawProductJobs.Data.q
    (fun a => V40LawActualProduct.mixtureJobs a.μ a.ν)
    (fun a => V40LawMixtureOrder.companions a.μ a.ν)
  have h := V40LawJobsClock.compose _ _ _ _ _ h0 h1
  have hi : V40LawMixtureJobs.input=(fun a => input a.q a.μ a.ν) :=
    funext (fun a => (V40LawProductMachine.input_eq a).symm)
  simpa only [hi,machine,V40LawSerializeJobs.output,V40LawActualProduct.mixture_alphabet,output]
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
end CurrentAdditive.V40LawMixtureMachine
