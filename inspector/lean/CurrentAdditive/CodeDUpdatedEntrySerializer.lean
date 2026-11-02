import CurrentAdditive.CodeDCompactSequentialBridge
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-!
The preceding entry writer starts after arithmetic has produced a canonical
updated weight. Its two physical input banks hold the original encoded word
and the updated RawRat packet. The literal bank serializer writes the new
Entry packet. A separate physical projection extracts the original word
from an old Entry packet, preserving its bytes exactly.
-/

namespace CurrentAdditive.CodeDUpdatedEntrySerializer

open EthInapproximability.CurrentPaper
open CodeDSourceCodecV2 CodeDCanonicalSourceV2 CodeDCodec

def wordBytes (old : Entry) : List Bool :=
  BankFieldProjection.result (0 : Fin 2) (encodeEntry old)

def updatedWeightBytes (updated : ℚ) : List Bool :=
  encodeRawRat (rawOfRat updated)

def writerBank (old : Entry) (updated : ℚ) : Fin 2 → List Bool :=
  fun i => if i = 0 then wordBytes old else updatedWeightBytes updated

def output (old : Entry) (updated : ℚ) : List Bool :=
  BitMachineBankCodec.encode (writerBank old updated)

theorem wordBytes_exact (old : Entry) :
    wordBytes old = CodeDCodecV2.encodeItems old.word := by
  simp [wordBytes, encodeEntry, BankFieldProjection.result_encode]

theorem output_exact (old : Entry) (updated : ℚ) :
    output old updated = encodeEntry ⟨old.word, rawOfRat updated⟩ := by
  unfold output encodeEntry
  congr 1
  funext i
  fin_cases i <;> simp [writerBank, wordBytes_exact, updatedWeightBytes]

theorem word_projection_physical (old : Entry) :
    (BankFieldProjection.machine (0 : Fin 2)).OutputsWithin
      (encodeEntry old) (CodeDCodecV2.encodeItems old.word)
      ((2*2+4)*((encodeEntry old).length+1)) := by
  have h := BankFieldProjection.outputs (0 : Fin 2) (encodeEntry old)
  change (BankFieldProjection.machine (0 : Fin 2)).OutputsWithin
    (encodeEntry old) (wordBytes old)
    ((2*2+4)*((encodeEntry old).length+1)) at h
  rw [wordBytes_exact] at h
  exact h

theorem writer_physical (old : Entry) (updated : ℚ) :
    ∃ t ≤ 2*(output old updated).length+2,
      ∃ S' : Fin 2 → List Bool,
        BitMachineBankSerialize.run t
          (BitMachineBankSerialize.cfg
            (some (.emit 0)) none (writerBank old updated) [] [] []) =
          BitMachineBankSerialize.cfg none none S' [] []
            (encodeEntry ⟨old.word, rawOfRat updated⟩) := by
  obtain ⟨t, S', ht, hr⟩ :=
    BitMachineBankSerialize.serialize (writerBank old updated) [] []
  refine ⟨t, ?_, S', ?_⟩
  · simpa [output, BitMachineBankCodec.encode_eq_list,
      BitMachineBankSerialize.encode] using ht
  · have he : BitMachineBankSerialize.encode
        (List.ofFn (writerBank old updated)) = output old updated := by
      simp [output, BitMachineBankCodec.encode_eq_list,
        BitMachineBankSerialize.encode]
    rw [List.append_nil, he, output_exact] at hr
    exact hr

theorem output_canonical {q : Nat}
    (old : (Fin q → Nat) × ℚ) (updated : ℚ) :
    output (canonicalEntry old) updated =
      encodeEntry (canonicalEntry (old.1, updated)) := by
  simpa only [canonicalEntry] using
    (output_exact (canonicalEntry old) updated)

def writtenItems {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    List (List Bool) :=
  (List.range updated.size).filterMap (fun i =>
    (source[i]?).map (fun old =>
      output (canonicalEntry old) (updated[i]?.getD 0)))

theorem writtenItems_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    writtenItems source updated =
      (CodeDCompactSequentialBridge.updatedEntries source updated).map encodeEntry := by
  simp [writtenItems, CodeDCompactSequentialBridge.updatedEntries,
    CodeDCompactSequentialBridge.updatedAt, List.map_filterMap,
    output_canonical, Function.comp_def]

theorem written_compactor {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (hupdated : updated.all (fun w => decide (0 ≤ w)) = true) :
    CodeDCompactJoinV2.machine.OutputsWithin
      (CodeDCodecV2.encodeItems (writtenItems source updated))
      (encodedSource (CodeDCompactSequentialBridge.retainedSource source updated))
      (CodeDCompactJoinV2.clock (writtenItems source updated)) := by
  rw [writtenItems_exact]
  exact CodeDCompactSequentialBridge.physical_compact_updated
    source updated hupdated

theorem materialized_written_compactor {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source out : Array ((Fin q → Nat) × ℚ))
    (h : SequentialSourceCode.compressSourceOnceMaterialized n φ source = some out) :
    ∃ updated : Array ℚ,
      CodeDCompactJoinV2.machine.OutputsWithin
        (CodeDCodecV2.encodeItems (writtenItems source updated))
        (encodedSource out)
        (CodeDCompactJoinV2.clock (writtenItems source updated)) := by
  obtain ⟨updated, hnonneg, hout⟩ :=
    CodeDCompactSequentialBridge.materialized_success_updated φ source out h
  exact ⟨updated, hout ▸ written_compactor source updated hnonneg⟩

#print axioms word_projection_physical
#print axioms writer_physical
#print axioms writtenItems_exact
#print axioms materialized_written_compactor

end CurrentAdditive.CodeDUpdatedEntrySerializer
