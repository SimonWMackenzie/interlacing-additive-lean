import CurrentAdditive.V40LawProductList
import CurrentAdditive.IndexedLaw

set_option autoImplicit false
namespace CurrentAdditive.V40LawActualProduct
noncomputable section
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
open V40LawProductList
set_option maxHeartbeats 4000000

/-- Consecutive canonical Fin-product positions, with both original
factors retained. Equal weights and equal decoded values remain positions. -/
def productJobs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List Job :=
  List.ofFn (fun j : Fin (m*n) =>
    (j.val,(μ.weight (finProdFinEquiv.symm j).1,ν.weight (finProdFinEquiv.symm j).2)))

theorem product_alphabet {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    alphabet (productJobs μ ν)=IndexedLaw.indexedAlphabet (reindex finProdFinEquiv (product μ ν)).weight := by
  simp [alphabet,productJobs,List.map_ofFn,IndexedLaw.indexedAlphabet,reindex,product,
    Function.comp_def]

def mixtureJobs {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : List Job :=
  List.ofFn (fun j : Fin (m+n) => match finSumFinEquiv.symm j with
    | .inl i => (j.val,((255:ℚ)/256,μ.weight i))
    | .inr i => (j.val,((1:ℚ)/256,ν.weight i)))

theorem mixture_alphabet {m n : ℕ} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) :
    alphabet (mixtureJobs μ ν)=IndexedLaw.indexedAlphabet (reindex finSumFinEquiv (mixture μ ν)).weight := by
  apply Array.ext
  · simp [alphabet,mixtureJobs,IndexedLaw.indexedAlphabet]
  · intro i hi hj
    simp only [alphabet,mixtureJobs,List.getElem_toArray,List.getElem_map,List.getElem_ofFn,
      IndexedLaw.indexedAlphabet,Array.getElem_ofFn]
    cases h : finSumFinEquiv.symm (⟨i,by simpa [alphabet,mixtureJobs] using hi⟩ : Fin (m+n)) with
    | inl a => simp [reindex,mixture,h]
    | inr a => simp [reindex,mixture,h]

/-- Exact canonical input alphabet for every current Fin-product law.
The input word contains the ordered factors, never their supplied products. -/
theorem physical_product : ∃ C d : ℕ, ∀ (m n : ℕ)
    (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)),
    V40LawProductList.machine.OutputsWithin
      (SourceListEncoding.encode (inputItems (productJobs μ ν)))
      (CodeDTargetV2.alphabetBytes
        (IndexedLaw.indexedAlphabet (reindex finProdFinEquiv (product μ ν)).weight))
      (C*((SourceListEncoding.encode (inputItems (productJobs μ ν))).length+1)^d) := by
  obtain ⟨C,d,h⟩:=outputs_polynomial
  refine ⟨C,d,?_⟩
  intro m n μ ν
  rw [←product_alphabet]
  exact h _

/-- The literal 255/256 and 1/256 mixture, left positions before right. -/
theorem physical_mixture : ∃ C d : ℕ, ∀ (m n : ℕ)
    (μ : PositiveRationalLaw (Fin m)) (ν : PositiveRationalLaw (Fin n)),
    V40LawProductList.machine.OutputsWithin
      (SourceListEncoding.encode (inputItems (mixtureJobs μ ν)))
      (CodeDTargetV2.alphabetBytes
        (IndexedLaw.indexedAlphabet (reindex finSumFinEquiv (mixture μ ν)).weight))
      (C*((SourceListEncoding.encode (inputItems (mixtureJobs μ ν))).length+1)^d) := by
  obtain ⟨C,d,h⟩:=outputs_polynomial
  refine ⟨C,d,?_⟩
  intro m n μ ν
  rw [←mixture_alphabet]
  exact h _

#print axioms product_alphabet
#print axioms mixture_alphabet
#print axioms physical_product
#print axioms physical_mixture
end
end CurrentAdditive.V40LawActualProduct
