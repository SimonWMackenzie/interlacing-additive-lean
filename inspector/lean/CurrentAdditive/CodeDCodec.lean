import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineBinaryMultiply
import Mathlib.Tactic

/-!
Private packet ABI for the physical implementation of the selected v27
Appendix H `det:code` constructor.  This is a codec, not a machine or a
runtime claim.  A variable array is a canonical natural-number count followed
by exactly that many framed Boolean words.  A rational is a three-field bank:
sign, little-endian unsigned numerator, and most-significant-first positive
denominator.  The outer controller has twelve fixed fields.
-/

namespace CurrentAdditive.CodeDCodec

open EthInapproximability.CurrentPaper
open EncodedCommunication BitMachineBankCodec

def encodeItems (items : List (List Bool)) : List Bool :=
  natField items.length ++ (items.map field).flatten

def readItemsN : Nat → List Bool → Option (List (List Bool) × List Bool)
  | 0, input => some ([], input)
  | n + 1, input => do
      let (item, rest) ← readField input
      let (items, suffix) ← readItemsN n rest
      pure (item :: items, suffix)

def readItems (input : List Bool) : Option (List (List Bool) × List Bool) := do
  let (n, rest) ← readNat input
  readItemsN n rest

def decodeItems (input : List Bool) : Option (List (List Bool)) := do
  let (items, rest) ← readItems input
  if rest.isEmpty then some items else none

theorem readItemsN_append (items : List (List Bool)) (suffix : List Bool) :
    readItemsN items.length ((items.map field).flatten ++ suffix) =
      some (items, suffix) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp [readItemsN, List.map_cons, List.flatten_cons, List.append_assoc,
        readField_append, ih]

theorem readItems_append (items : List (List Bool)) (suffix : List Bool) :
    readItems (encodeItems items ++ suffix) = some (items, suffix) := by
  simp [readItems, encodeItems, List.append_assoc, readNat_append,
    readItemsN_append]

@[simp] theorem decodeItems_encodeItems (items : List (List Bool)) :
    decodeItems (encodeItems items) = some items := by
  have h := readItems_append items []
  simp only [List.append_nil] at h
  simp [decodeItems, h]

theorem readItemsN_sound {n : Nat} {input suffix : List Bool}
    {items : List (List Bool)}
    (h : readItemsN n input = some (items, suffix)) :
    items.length = n ∧ (items.map field).flatten ++ suffix = input := by
  induction n generalizing input items suffix with
  | zero =>
      simp [readItemsN] at h
      rcases h with ⟨rfl, rfl⟩
      simp
  | succ n ih =>
      unfold readItemsN at h
      cases hf : readField input with
      | none => simp [hf] at h
      | some pair =>
          rcases pair with ⟨item, rest⟩
          simp only [hf] at h
          cases hi : readItemsN n rest with
          | none => simp [hi] at h
          | some pair =>
              rcases pair with ⟨tail, tailRest⟩
              simp [hi] at h
              rcases h with ⟨hitems, hsuffix⟩
              subst items
              subst suffix
              obtain ⟨hlen, hcode⟩ := ih hi
              constructor
              · simp [hlen]
              ·
                simp [List.map_cons, List.flatten_cons, List.append_assoc,
                  hcode, readField_sound hf]

theorem readItems_sound {input suffix : List Bool}
    {items : List (List Bool)}
    (h : readItems input = some (items, suffix)) :
    encodeItems items ++ suffix = input := by
  unfold readItems at h
  cases hn : readNat input with
  | none => simp [hn] at h
  | some pair =>
      rcases pair with ⟨n, rest⟩
      simp only [hn] at h
      obtain ⟨hlen, hcode⟩ := readItemsN_sound h
      rw [encodeItems, hlen]
      calc
        natField n ++ (items.map field).flatten ++ suffix =
            natField n ++ rest := by simp [List.append_assoc, hcode]
        _ = input := readNat_sound hn

theorem encodeItems_length (items : List (List Bool)) :
    (encodeItems items).length =
      (natField items.length).length +
        ((items.map field).flatten).length := by
  simp [encodeItems]

structure RawRat where
  negative : Bool
  numerator : List Bool
  denominator : List Bool
  deriving DecidableEq

def rawRatBank (r : RawRat) : Bank 3 :=
  fun i => if i = 0 then (if r.negative then [true] else []) else
    if i = 1 then r.numerator else r.denominator

def encodeRawRat (r : RawRat) : List Bool := encode (rawRatBank r)

def decodeRawRat (bits : List Bool) : Option RawRat := do
  let S ← decode 3 bits
  let sign ← if S 0 = [] then some false else
    if S 0 = [true] then some true else none
  if BitMachineBinaryMultiply.msbValue (S 2) = 0 then none else
    some ⟨sign, S 1, S 2⟩

def RawRat.Valid (r : RawRat) : Prop :=
  0 < BitMachineBinaryMultiply.msbValue r.denominator

theorem decodeRawRat_encodeRawRat (r : RawRat) (hr : r.Valid) :
    decodeRawRat (encodeRawRat r) = some r := by
  cases r with
  | mk sign num den =>
      cases sign <;> simp [decodeRawRat, encodeRawRat, rawRatBank, RawRat.Valid,
        Nat.ne_of_gt hr] at *

def RawRat.value (r : RawRat) : ℚ :=
  (if r.negative then -1 else 1) *
    ((bitsValue r.numerator : ℚ) /
      (BitMachineBinaryMultiply.msbValue r.denominator : ℚ))

abbrev CodeBank := Bank 12

def codePacket (D q : Nat) (alphabet source features matrix weights : List Bool) :
    CodeBank := fun i =>
  if i = 0 then List.replicate D true else
  if i = 1 then List.replicate q true else
  if i = 2 then alphabet else
  if i = 3 then source else
  if i = 4 then features else
  if i = 5 then matrix else
  if i = 6 then weights else []

@[simp] theorem codePacket_D (D q : Nat)
    (a s f m w : List Bool) : (codePacket D q a s f m w) 0 = List.replicate D true := rfl
@[simp] theorem codePacket_q (D q : Nat)
    (a s f m w : List Bool) : (codePacket D q a s f m w) 1 = List.replicate q true := rfl
@[simp] theorem codePacket_alphabet (D q : Nat)
    (a s f m w : List Bool) : (codePacket D q a s f m w) 2 = a := rfl
@[simp] theorem codePacket_source (D q : Nat)
    (a s f m w : List Bool) : (codePacket D q a s f m w) 3 = s := rfl
@[simp] theorem codePacket_features (D q : Nat)
    (a s f m w : List Bool) : (codePacket D q a s f m w) 4 = f := rfl
@[simp] theorem codePacket_matrix (D q : Nat)
    (a s f m w : List Bool) : (codePacket D q a s f m w) 5 = m := rfl
@[simp] theorem codePacket_weights (D q : Nat)
    (a s f m w : List Bool) : (codePacket D q a s f m w) 6 = w := rfl

@[simp] theorem decode_codePacket (D q : Nat)
    (a s f m w : List Bool) :
    decode 12 (encode (codePacket D q a s f m w)) =
      some (codePacket D q a s f m w) := decode_encode _

#print axioms readItemsN_append
#print axioms readItems_sound
#print axioms decodeRawRat_encodeRawRat

end CurrentAdditive.CodeDCodec
