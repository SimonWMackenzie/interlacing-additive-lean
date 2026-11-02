import CurrentAdditive.IndexedLawBytesMachine
import CurrentAdditive.StoredWeightedState

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper BitMachineBankCodec
open CodeDTargetV2 CodeDSourceCodecV2 CodeDCanonicalSourceV2 CodeDCodec

def sourceItems {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :=
  (canonicalSource source).map encodeEntry

def indexedAlphabet {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :=
  Array.ofFn (fun i : Fin source.size => (i.val,source[i].2))

theorem indexedWord_canonical (i : Nat) {q : Nat} (e : (Fin q → Nat) × ℚ) :
    indexedWord i (encodeEntry (canonicalEntry e))=alphabetEntry (i,e.2) := by
  simp [indexedWord,weightWord,encodeEntry,canonicalEntry,alphabetEntry,
    BankFieldProjection.result_encode]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem indexed_items_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    outputItems (sourceItems source)=(indexedAlphabet source).toList.map alphabetEntry := by
  apply List.ext_getElem
  · simp [outputItems,sourceItems,canonicalSource,indexedAlphabet]
  · intro i hi hj
    have hb : i<source.size := by simpa [outputItems,sourceItems,canonicalSource] using hi
    simp [outputItems,sourceItems,canonicalSource,indexedAlphabet,hb,indexedWord_canonical]

theorem source_output_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    output (sourceItems source)=alphabetBytes (indexedAlphabet source) := by
  unfold output alphabetBytes
  rw [indexed_items_exact]
  rfl

/-- This codec endpoint includes empty arrays, duplicate tuples and arbitrary
signed rational weights. It neither searches by tuple value nor merges entries. -/
theorem source_uniform : ∃ C E : Nat,∀ (q : Nat) (source : Array ((Fin q → Nat) × ℚ)),
    machine.OutputsWithin (encodedSource source) (alphabetBytes (indexedAlphabet source))
      (C*((encodedSource source).length+1)^E) := by
  obtain ⟨C,E,h⟩ := uniform
  refine ⟨C,E,?_⟩
  intro q source
  have hr := h (sourceItems source)
  rw [source_output_exact] at hr
  exact hr

theorem lawAlphabet_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (μ : Paper2.PositiveRationalLaw (Fin source.size))
    (hw : ∀i,μ.weight i=source[i].2) : indexedAlphabet source=StoredWeightedState.lawAlphabet μ := by
  apply Array.ext
  · simp [indexedAlphabet,StoredWeightedState.lawAlphabet]
  · intro i hi hj
    simp [indexedAlphabet,StoredWeightedState.lawAlphabet,hw]

theorem law_uniform : ∃ C E : Nat,∀ (q : Nat) (source : Array ((Fin q → Nat) × ℚ))
    (μ : Paper2.PositiveRationalLaw (Fin source.size)),
    (∀i,μ.weight i=source[i].2) →
    machine.OutputsWithin (encodedSource source) (StoredWeightedState.lawBytes μ)
      (C*((encodedSource source).length+1)^E) := by
  obtain ⟨C,E,h⟩ := source_uniform
  refine ⟨C,E,?_⟩
  intro q source μ hw
  have hr := h q source
  rw [lawAlphabet_exact source μ hw] at hr
  exact hr

#print axioms source_uniform
#print axioms law_uniform
end CurrentAdditive.IndexedLawBytes
