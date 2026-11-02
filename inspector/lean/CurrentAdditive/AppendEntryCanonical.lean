import CurrentAdditive.AppendEntryPhysical

namespace CurrentAdditive.AppendEntryCanonical
open EthInapproximability.CurrentPaper
open CodeDSourceCodecV2 CodeDCanonicalSourceV2 AppendEntryPhysical

theorem word_append {q : Nat} (v : Fin q → Nat) (a : Nat) :
    List.ofFn (fun j : Fin (q+1) => (SequentialCode.appendWord v a j).bits) =
      (List.ofFn (fun j : Fin q => (v j).bits)) ++ [a.bits] := by
  rw [List.ofFn_succ_last]
  congr 1
  · apply congrArg List.ofFn
    funext j
    simp [SequentialCode.appendWord,j.isLt]
  · simp [SequentialCode.appendWord]

theorem canonical_append {q : Nat} (x : (Fin q → Nat) × ℚ) (y : Nat × ℚ) :
    (⟨(canonicalEntry x).word++[y.1.bits],
      rawOfRat ((canonicalEntry x).weight.value*y.2)⟩ : Entry) =
      canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2) := by
  apply congrArg₂ Entry.mk
  · exact (word_append x.1 y.1).symm
  · simp [canonicalEntry,rawOfRat_value]

theorem outputs_canonical {q : Nat} (x : (Fin q → Nat) × ℚ) (y : Nat × ℚ) :
    machine.OutputsWithin (packet (canonicalEntry x) y)
      (encodeEntry (canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2)))
      (producer.coefficient*((packet (canonicalEntry x) y).length+1)^producer.degree) := by
  have h := outputs_packet (canonicalEntry x) y (canonicalEntry_valid x)
  rw [canonical_append] at h
  exact h

/-- One fixed evaluator and one clock polynomial cover every actual indexed
source/alphabet pair; no positivity or distinctness condition is needed. -/
theorem uniform_canonical : ∃ c d : Nat, ∀ q : Nat,
    ∀ x : (Fin q → Nat) × ℚ, ∀ y : Nat × ℚ,
    machine.OutputsWithin (packet (canonicalEntry x) y)
      (encodeEntry (canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2)))
      (c*((packet (canonicalEntry x) y).length+1)^d) :=
  ⟨producer.coefficient,producer.degree,fun _ x y => outputs_canonical x y⟩

#print axioms outputs_canonical
#print axioms uniform_canonical
end CurrentAdditive.AppendEntryCanonical
