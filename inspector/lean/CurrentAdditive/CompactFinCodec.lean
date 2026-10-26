import Paper2.RecursiveLabelCodec

/-! Self-delimiting binary indices. A payload bit b is framed as `true,b`;
`false` terminates the word. The code is prefix-free and has length at most
twice the binary length of the carrier bound plus one. -/

namespace Paper2.CompactFinCodec

open Paper2.RecursiveLabelCodecScratch

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

def unframe : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: b :: rest => do
      let (bits, tail) ← unframe rest
      pure (b :: bits, tail)

theorem unframe_frame (bits rest : List Bool) :
    unframe (frame bits ++ rest) = some (bits, rest) := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [frame, unframe, ih]

theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [frame, ih]; omega

def value (bits : List Bool) : ℕ :=
  Nat.ofDigits 2 (bits.map fun b => cond b 1 0)

theorem value_bits (m : ℕ) : value m.bits = m := by
  simp only [value, ← Nat.digits_two_eq_bits]
  exact Nat.ofDigits_digits 2 m

def codec (n : ℕ) : PrefixCodec (Fin n) where
  encode i := frame i.val.bits
  decode bits := do
    let (payload, rest) ← unframe bits
    if h : value payload < n then some (⟨value payload, h⟩, rest)
    else none
  roundtrip := by
    intro i rest
    simp [unframe_frame, value_bits, i.isLt]
  maxLen := 2 * Nat.size n + 1
  length_le := by
    intro i
    rw [frame_length, Nat.size_eq_bits_len]
    have h := Nat.size_le_size (Nat.le_of_lt i.isLt)
    omega

theorem encoded_length_le_log {n L : ℕ} (hn : n ≤ 2 ^ L)
    (i : Fin n) : ((codec n).encode i).length ≤ 2 * L + 1 := by
  change (frame i.val.bits).length ≤ 2 * L + 1
  rw [frame_length, Nat.size_eq_bits_len]
  have hi : i.val < 2 ^ L := lt_of_lt_of_le i.isLt hn
  have hs : Nat.size i.val ≤ L := Nat.size_le.mpr hi
  omega

#print axioms unframe_frame
#print axioms value_bits
#print axioms encoded_length_le_log

end Paper2.CompactFinCodec
