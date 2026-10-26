import CurrentAdditive.CodeDCanonicalSourceV2
import CurrentAdditive.SequentialSourceCode

/-!
Exact input/output target for the fixed-D physical Code D machine.  This
module specifies the currently checked `sequentialMaterialized` program,
serializes each of its indexed output entries, and proves that the serialized
answer decodes back to those very entries and rational weights.  It does not
claim a finite-stack implementation or a clock.
-/

namespace CurrentAdditive.CodeDTargetV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.EncodedCommunication
open CodeDCodec CodeDSourceCodecV2 CodeDCanonicalSourceV2 SequentialSourceCode

def alphabetEntry (entry : Nat × ℚ) : List Bool :=
  encode (fun i : Fin 2 =>
    if i = 0 then entry.1.bits else encodeRawRat (rawOfRat entry.2))

def alphabetBytes (alphabet : Array (Nat × ℚ)) : List Bool :=
  CodeDCodecV2.encodeItems (alphabet.toList.map alphabetEntry)

def alphabetDecodeEntry (input : List Bool) : Option (Nat × RawRat) := do
  let S ← decode 2 input
  let r ← decodeRawRat (S 1)
  pure (bitsValue (S 0), r)

def alphabetDecode (input : List Bool) : Option (List (Nat × RawRat)) := do
  let items ← CodeDCodecV2.decodeItems input
  items.mapM alphabetDecodeEntry

theorem alphabetDecodeEntry_correct (entry : Nat × ℚ) :
    alphabetDecodeEntry (alphabetEntry entry) =
      some (entry.1, rawOfRat entry.2) := by
  simp [alphabetDecodeEntry, alphabetEntry, decodeRawRat_encodeRawRat,
    rawOfRat_valid]

theorem alphabetDecode_correct (alphabet : Array (Nat × ℚ)) :
    alphabetDecode (alphabetBytes alphabet) =
      some (alphabet.toList.map (fun x => (x.1, rawOfRat x.2))) := by
  have hm : ∀ l : List (Nat × ℚ),
      (l.map alphabetEntry).mapM alphabetDecodeEntry =
        some (l.map fun x => (x.1, rawOfRat x.2)) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
        simp [List.mapM_cons, alphabetDecodeEntry_correct, ih]
  simp [alphabetDecode, alphabetBytes, hm]

theorem alphabet_values_correct (alphabet : Array (Nat × ℚ)) :
    (alphabet.toList.map (fun x => (x.1, rawOfRat x.2))).map
      (fun x => (x.1, x.2.value)) = alphabet.toList := by
  rw [List.map_map]
  calc
    alphabet.toList.map ((fun x => (x.1, x.2.value)) ∘
        fun x => (x.1, rawOfRat x.2)) = alphabet.toList.map id := by
      apply List.map_congr_left
      intro x hx
      rcases x with ⟨n, r⟩
      simp [Function.comp_def, rawOfRat_value]
    _ = alphabet.toList := by simp

def targetBytes (D : Nat) (alphabet : Array (Nat × ℚ))
    (q : Nat) : Option (List Bool) :=
  (sequentialMaterialized D alphabet q).map encodedSource

theorem targetBytes_exact (D : Nat) (alphabet : Array (Nat × ℚ))
    (q : Nat) (out : Array ((Fin q → Nat) × ℚ))
    (h : sequentialMaterialized D alphabet q = some out) :
    targetBytes D alphabet q = some (encodedSource out) ∧
    decodeSource q (encodedSource out) = some (canonicalSource out) ∧
    (canonicalSource out).map (fun e => (valueWord e, valueWeight e)) =
      out.toList.map (fun x => (List.ofFn x.1, x.2)) := by
  exact ⟨by simp [targetBytes, h], decode_encodedSource out,
    canonicalSource_values out⟩

theorem targetBytes_total (D : Nat) (alphabet : Array (Nat × ℚ))
    (halphabet : SourcePositive alphabet) (q : Nat) :
    ∃ out bytes, sequentialMaterialized D alphabet q = some out ∧
      targetBytes D alphabet q = some bytes ∧
      decodeSource q bytes = some (canonicalSource out) ∧
      (canonicalSource out).map (fun e => (valueWord e, valueWeight e)) =
        out.toList.map (fun x => (List.ofFn x.1, x.2)) := by
  obtain ⟨out, hout, _⟩ := sequentialMaterialized_total D alphabet halphabet q
  refine ⟨out, encodedSource out, hout, ?_⟩
  exact (targetBytes_exact D alphabet q out hout)

#print axioms alphabetDecode_correct
#print axioms targetBytes_exact
#print axioms targetBytes_total

end CurrentAdditive.CodeDTargetV2
