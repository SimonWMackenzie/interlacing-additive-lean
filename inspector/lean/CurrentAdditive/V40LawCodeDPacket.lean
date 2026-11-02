import CurrentAdditive.V40LawActualProduct

set_option autoImplicit false
namespace CurrentAdditive.V40LawCodeDPacket
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V39GeneratedConstruction V40LawProductList V40LawActualProduct
set_option maxHeartbeats 4000000

def input (q : ℕ) (jobs : List Job) : List Bool :=
  V40LawPacket.packet (List.replicate q true) (SourceListEncoding.encode (inputItems jobs))

def machine : BitMachine.Machine:=V40LawBankMap.liftMachine V40LawProductList.machine

def codeDInput (q : ℕ) (alphabet : Array (ℕ×ℚ)) : List Bool:=
  BitMachineBankCodec.encode (![List.replicate q true,CodeDTargetV2.alphabetBytes alphabet] : Fin 2→List Bool)

theorem outputs : ∃ C d : ℕ, ∀ q jobs,
    machine.OutputsWithin (input q jobs) (codeDInput q (alphabet jobs))
      (C*((input q jobs).length+3)^d) := by
  obtain ⟨c,d,h⟩:=V40LawProductList.outputs_polynomial
  refine ⟨10*(c+1)*(V40LawProductList.machine.pushBound+1),d+1,?_⟩
  intro q jobs
  have hr:=V40LawBankMap.outputs_polynomial V40LawProductList.machine c d
    (List.replicate q true) _ _ (h jobs)
  have he : V40LawPacket.packet (List.replicate q true)
      (CodeDTargetV2.alphabetBytes (alphabet jobs))=codeDInput q (alphabet jobs) := by
    unfold V40LawPacket.packet codeDInput
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [he] at hr
  exact hr

/-- Exact raw two-field input for a live Code D call on a current product law. -/
theorem product : ∃ C d : ℕ, ∀ (q m n : ℕ)
    (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)),
    machine.OutputsWithin (input q (productJobs μ ν))
      (codeDInput q (IndexedLaw.indexedAlphabet
        (reindex finProdFinEquiv (V39GeneratedConstruction.product μ ν)).weight))
      (C*((input q (productJobs μ ν)).length+3)^d) := by
  obtain ⟨C,d,h⟩:=outputs
  exact ⟨C,d,fun q m n μ ν => by rw [←product_alphabet]; exact h _ _⟩

/-- Exact raw two-field input with canonical ordered 255/256--1/256 weights. -/
theorem mixture : ∃ C d : ℕ, ∀ (q m n : ℕ)
    (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)),
    machine.OutputsWithin (input q (mixtureJobs μ ν))
      (codeDInput q (IndexedLaw.indexedAlphabet
        (reindex finSumFinEquiv (V39GeneratedConstruction.mixture μ ν)).weight))
      (C*((input q (mixtureJobs μ ν)).length+3)^d) := by
  obtain ⟨C,d,h⟩:=outputs
  exact ⟨C,d,fun q m n μ ν => by rw [←mixture_alphabet]; exact h _ _⟩

#print axioms outputs
#print axioms product
#print axioms mixture
end
end CurrentAdditive.V40LawCodeDPacket
