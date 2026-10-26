import EthInapproximability.CurrentPaper.ProtocolCertificateCodec
import Mathlib.Data.Nat.Bits
import EthInapproximability.CurrentPaper.BitMachine

/-!
# The explicit communication decision language

Source: v8 `01-introduction.tex`, `thm:exact-main`, and NP membership in
`03-exact-hardness.tex`. Dimensions and threshold use self-delimiting binary
fields, followed by the literal row-major Boolean table. Zero dimensions,
noncanonical fields, truncation and wrong table lengths are rejected.

The witness theorem below concerns this exact encoded language. Actual
finite-stack verifier runtime remains a distinct theorem, not a premise
silently hidden in the language definition.
-/

namespace EthInapproximability.CurrentPaper.EncodedCommunication

open Workspace.Types.CommComplexity ProtocolVerifier ProtocolCertificateCodec

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

@[simp] theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n h ih => simp [Nat.bits_append_bit n b h, bitsValue, ih]

/-- A field consists of `true,b` for each payload bit followed by `false`. -/
def field : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: field bs

def readField : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: b :: rest => do
      let (bs, suffix) ← readField rest
      pure (b :: bs, suffix)

theorem readField_append (bs suffix : List Bool) :
    readField (field bs ++ suffix) = some (bs, suffix) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [field, readField, ih]

theorem field_length (bs : List Bool) : (field bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [field, ih]; omega

theorem readField_sound {input bs rest : List Bool}
    (h : readField input = some (bs, rest)) : field bs ++ rest = input := by
  induction input using readField.induct generalizing bs rest with
  | case1 => simp [readField] at h
  | case2 suffix =>
      simp only [readField, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | case3 => simp [readField] at h
  | case4 b input ih =>
      cases hp : readField input with
      | none => simp [readField, hp] at h
      | some pair =>
          rcases pair with ⟨ys, tail⟩
          simp only [readField, hp, pure] at h
          rcases h with ⟨rfl, rfl⟩
          simp [field, ih hp]

def natField (n : ℕ) := field n.bits

def readNat (input : List Bool) : Option (ℕ × List Bool) := do
  let (bs, rest) ← readField input
  let n := bitsValue bs
  if n.bits = bs then some (n, rest) else none

theorem readNat_append (n : ℕ) (rest : List Bool) :
    readNat (natField n ++ rest) = some (n, rest) := by
  simp [readNat, natField, readField_append]

theorem readNat_sound {input rest : List Bool} {n : ℕ}
    (h : readNat input = some (n, rest)) : natField n ++ rest = input := by
  unfold readNat at h
  cases hf : readField input with
  | none => simp [hf] at h
  | some p =>
      rcases p with ⟨bs, suffix⟩
      simp only [hf, Bind.bind, Option.bind] at h
      split at h
      · rename_i hc
        have he := Option.some.inj h
        cases he
        simpa only [natField, hc] using readField_sound hf
      · contradiction

structure Instance where
  rows : ℕ
  cols : ℕ
  threshold : ℕ
  table : List Bool
  deriving DecidableEq

def Instance.Valid (i : Instance) : Prop :=
  0 < i.rows ∧ 0 < i.cols ∧ i.table.length = i.rows * i.cols

instance (i : Instance) : Decidable i.Valid := inferInstanceAs
  (Decidable (0 < i.rows ∧ 0 < i.cols ∧ i.table.length = i.rows * i.cols))

def encodeInstance (i : Instance) : List Bool :=
  natField i.rows ++ natField i.cols ++ natField i.threshold ++ i.table

theorem encodeInstance_length (i : Instance) :
    (encodeInstance i).length =
      2 * (i.rows.bits.length + i.cols.bits.length + i.threshold.bits.length) +
        3 + i.table.length := by
  simp only [encodeInstance, List.length_append, natField, field_length]
  omega

def decodeInstance (input : List Bool) : Option Instance := do
  let (rows, rest₁) ← readNat input
  let (cols, rest₂) ← readNat rest₁
  let (threshold, table) ← readNat rest₂
  let i : Instance := ⟨rows, cols, threshold, table⟩
  if i.Valid then some i else none

theorem decode_encode (i : Instance) (hi : i.Valid) :
    decodeInstance (encodeInstance i) = some i := by
  simp [decodeInstance, encodeInstance, List.append_assoc, readNat_append, hi]

theorem decode_valid {input : List Bool} {i : Instance}
    (h : decodeInstance input = some i) : i.Valid := by
  unfold decodeInstance at h
  cases h₁ : readNat input with
  | none => simp [h₁] at h
  | some p₁ =>
      rcases p₁ with ⟨r, tail₁⟩
      cases h₂ : readNat tail₁ with
      | none => simp [h₁, h₂] at h
      | some p₂ =>
          rcases p₂ with ⟨c, tail₂⟩
          cases h₃ : readNat tail₂ with
          | none => simp [h₁, h₂, h₃] at h
          | some p₃ =>
              rcases p₃ with ⟨k, table⟩
              simp only [h₁, h₂, h₃, Bind.bind, Option.bind] at h
              split at h
              · rename_i hv
                cases Option.some.inj h
                exact hv
              · contradiction

theorem decode_sound {input : List Bool} {i : Instance}
    (h : decodeInstance input = some i) : encodeInstance i = input := by
  unfold decodeInstance at h
  cases h₁ : readNat input with
  | none => simp [h₁] at h
  | some p₁ =>
      rcases p₁ with ⟨r, tail₁⟩
      cases h₂ : readNat tail₁ with
      | none => simp [h₁, h₂] at h
      | some p₂ =>
          rcases p₂ with ⟨c, tail₂⟩
          cases h₃ : readNat tail₂ with
          | none => simp [h₁, h₂, h₃] at h
          | some p₃ =>
              rcases p₃ with ⟨k, table⟩
              simp only [h₁, h₂, h₃, Bind.bind, Option.bind] at h
              split at h
              · cases Option.some.inj h
                simp only [encodeInstance, List.append_assoc, readNat_sound h₃,
                  readNat_sound h₂, readNat_sound h₁]
              · contradiction

theorem decoded_table_length {input : List Bool} {i : Instance}
    (h : decodeInstance input = some i) : i.table.length ≤ input.length := by
  have he := congrArg List.length (decode_sound h)
  simp only [encodeInstance, List.length_append] at he
  omega

def Language : Set (List Bool) :=
  { input | ∃ i, decodeInstance input = some i ∧
      D (tableGame i.rows i.cols i.table) ≤ i.threshold }

def verifyEncoded (input witness : List Bool) : Bool :=
  match decodeInstance input with
  | none => false
  | some i => rawVerify i.rows i.cols i.threshold i.table witness

theorem verifyEncoded_sound (input witness : List Bool)
    (h : verifyEncoded input witness = true) : input ∈ Language := by
  cases hd : decodeInstance input with
  | none => simp [verifyEncoded, hd] at h
  | some i =>
      refine ⟨i, hd, ?_⟩
      exact rawVerify_sound i.rows i.cols i.threshold i.table witness
        (by simpa [verifyEncoded, hd] using h)

theorem verifyEncoded_complete (input : List Bool) (h : input ∈ Language) :
    ∃ witness, verifyEncoded input witness = true := by
  obtain ⟨i, hi, hc⟩ := h
  have hv := decode_valid hi
  obtain ⟨w, hw⟩ := rawVerify_complete i.rows i.cols i.threshold i.table hv.2.2 hc
  exact ⟨w, by simpa [verifyEncoded, hi] using hw⟩

theorem language_iff_witness (input : List Bool) :
    input ∈ Language ↔ ∃ witness, verifyEncoded input witness = true :=
  ⟨verifyEncoded_complete input, fun ⟨w, hw⟩ => verifyEncoded_sound input w hw⟩

/-- The certificate polynomial is in the actual complete encoded input length,
including arbitrary binary thresholds. No bound on the threshold is assumed. -/
theorem verifyEncoded_complete_polynomial (input : List Bool) (h : input ∈ Language) :
    ∃ witness, verifyEncoded input witness = true ∧
      witness.length ≤ (input.length + 2) * (2 * input.length + 1) := by
  obtain ⟨i, hi, hc⟩ := h
  have hv := decode_valid hi
  obtain ⟨w, hw, hb⟩ := rawVerify_complete_table_polynomial
    i.rows i.cols i.threshold i.table hv.2.2 hc
  refine ⟨w, by simpa [verifyEncoded, hi] using hw, hb.trans ?_⟩
  have hlength := decoded_table_length hi
  gcongr

theorem language_iff_polynomial_witness (input : List Bool) :
    input ∈ Language ↔ ∃ witness, verifyEncoded input witness = true ∧
      witness.length ≤ (input.length + 2) * (2 * input.length + 1) :=
  ⟨verifyEncoded_complete_polynomial input,
    fun ⟨w, hw, _⟩ => verifyEncoded_sound input w hw⟩

end EthInapproximability.CurrentPaper.EncodedCommunication
