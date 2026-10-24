import CurrentAdditive.PreservingV2Run
import CurrentAdditive.CodeDCanonicalSourceV2

/-! A physical indexed getter on the actual V2 serialization of a
materialized Code D output array.  Its input is the source's serialized
bytes and a numeric array position; it returns the selected encoded record
while preserving those source bytes. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext

def codeDRecords {q : ℕ} (out : Array ((Fin q → Nat) × ℚ)) :
    List (List Bool) := (canonicalSource out).map encodeEntry

theorem codeDRecords_length {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) :
    (codeDRecords out).length = out.size := by
  simp [codeDRecords, canonicalSource]

def codeDRecordIndex {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size) :
    Fin (codeDRecords out).length :=
  j.cast (codeDRecords_length out).symm

theorem codeDRecord_split {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size) :
    codeDRecords out =
      (codeDRecords out).take j.val ++
        (codeDRecords out)[codeDRecordIndex out j] ::
          (codeDRecords out).drop (j.val + 1) := by
  let k := codeDRecordIndex out j
  have hk : k.val < (codeDRecords out).length := k.isLt
  have h := List.take_append_drop k.val (codeDRecords out)
  rw [List.drop_eq_getElem_cons hk] at h
  simpa [k, codeDRecordIndex] using h.symm

theorem indexed_codeD_getter_run {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size) :
    let pre := (codeDRecords out).take j.val
    let word := (codeDRecords out)[codeDRecordIndex out j]
    let suffix := (codeDRecords out).drop (j.val + 1)
    let source := encodedSource out
    ∃ t ≤ 2 * source.length + 5 +
        (4 * (pre ++ word :: suffix).length.bits.length + 6 +
          CurrentAdditive.GaussListContext.IndexedFieldProgram.fieldCost
            (pre ++ [word])),
      PreservingV2Program.run t (PreservingV2Program.initial source j.val) =
        ⟨none,
         PreservingV2Program.v2Control
           (CurrentAdditive.GaussListContext.IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl
               (some true, false), none)),
         ![EthInapproximability.CurrentPaper.SourceListEncoding.fields suffix,
           [], [], [], [], List.replicate word.length true,
           word, [], source, []]⟩ := by
  dsimp only
  let pre := (codeDRecords out).take j.val
  let word := (codeDRecords out)[codeDRecordIndex out j]
  let suffix := (codeDRecords out).drop (j.val + 1)
  have hsplit : codeDRecords out = pre ++ word :: suffix :=
    codeDRecord_split out j
  have hpre : pre.length = j.val := by
    simp [pre, codeDRecords_length]
  have henc : encodedSource out =
      SourceListEncoding.encode (pre ++ word :: suffix) := by
    change SourceListEncoding.encode (codeDRecords out) =
      SourceListEncoding.encode (pre ++ word :: suffix)
    rw [hsplit]
  have hrun := PreservingV2Program.select_preserving pre word suffix
  simpa only [hpre, ← henc] using hrun

#print axioms codeDRecord_split
#print axioms indexed_codeD_getter_run

end CurrentAdditive.IndexedExecutableStepRecovery
