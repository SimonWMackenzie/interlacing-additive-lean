import CurrentAdditive.CodeDCodecV2

/-!
The indexed source representation used by the physical Code D controller.
Each entry has its own framed record even when two decoded words coincide.
The word is a counted sequence of little-endian symbol codes; the weight is
the signed rational record from `CodeDCodec`.  Decoding checks the expected
word length and positive denominator but does not silently merge entries.
-/

namespace CurrentAdditive.CodeDSourceCodecV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CodeDCodec CodeDCodecV2

structure Entry where
  word : List (List Bool)
  weight : RawRat
  deriving DecidableEq

def encodeEntry (entry : Entry) : List Bool :=
  encode (fun i : Fin 2 =>
    if i = 0 then CodeDCodecV2.encodeItems entry.word else encodeRawRat entry.weight)

def decodeEntry (input : List Bool) : Option Entry := do
  let S ← decode 2 input
  let word ← CodeDCodecV2.decodeItems (S 0)
  let weight ← decodeRawRat (S 1)
  pure ⟨word, weight⟩

theorem decodeEntry_encodeEntry (entry : Entry) (hw : entry.weight.Valid) :
    decodeEntry (encodeEntry entry) = some entry := by
  cases entry with
  | mk word weight =>
      simp [decodeEntry, encodeEntry, CodeDCodecV2.decodeItems_encodeItems,
        decodeRawRat_encodeRawRat, hw]

def encodeSource (entries : List Entry) : List Bool :=
  CodeDCodecV2.encodeItems (entries.map encodeEntry)

def decodeSource (q : Nat) (input : List Bool) : Option (List Entry) := do
  let itemBits ← CodeDCodecV2.decodeItems input
  let entries ← itemBits.mapM decodeEntry
  if entries.all (fun e => decide (e.word.length = q)) then some entries else none

theorem mapM_decodeEntry_encodeEntry (entries : List Entry)
    (hvalid : ∀ e ∈ entries, e.weight.Valid) :
    (entries.map encodeEntry).mapM decodeEntry = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have he : entry.weight.Valid := hvalid entry (by simp)
      have hr : ∀ e ∈ rest, e.weight.Valid := by
        intro e he
        exact hvalid e (by simp [he])
      simp [List.mapM_cons, decodeEntry_encodeEntry entry he, ih hr]

theorem decodeSource_encodeSource (q : Nat) (entries : List Entry)
    (hvalid : ∀ e ∈ entries, e.weight.Valid)
    (hlen : ∀ e ∈ entries, e.word.length = q) :
    decodeSource q (encodeSource entries) = some entries := by
  have hm := mapM_decodeEntry_encodeEntry entries hvalid
  simp [decodeSource, encodeSource, hm]
  exact hlen

theorem decodeSource_length (q : Nat) (input : List Bool)
    (entries : List Entry) (h : decodeSource q input = some entries) :
    ∀ e ∈ entries, e.word.length = q := by
  unfold decodeSource at h
  cases hd : CodeDCodecV2.decodeItems input with
  | none => simp [hd] at h
  | some itemBits =>
      simp only [hd] at h
      cases he : itemBits.mapM decodeEntry with
      | none => simp [he] at h
      | some decoded =>
          simp [he] at h
          rcases h with ⟨hgood, rfl⟩
          exact hgood

def valueWord (entry : Entry) : List Nat :=
  entry.word.map EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue

def valueWeight (entry : Entry) : ℚ := entry.weight.value

#print axioms decodeEntry_encodeEntry
#print axioms decodeSource_encodeSource
#print axioms decodeSource_length

end CurrentAdditive.CodeDSourceCodecV2
