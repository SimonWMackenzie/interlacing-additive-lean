import CurrentAdditive.IndexedCodeDGetterRun

/-! The record selected by the physical V2 getter is the canonical encoding
of precisely the requested materialized Code D array entry. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2

theorem codeDRecords_get {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size) :
    (codeDRecords out)[codeDRecordIndex out j] =
      encodeEntry (canonicalEntry out[j]) := by
  simp [codeDRecords, codeDRecordIndex, canonicalSource]

#print axioms codeDRecords_get

end CurrentAdditive.IndexedExecutableStepRecovery
