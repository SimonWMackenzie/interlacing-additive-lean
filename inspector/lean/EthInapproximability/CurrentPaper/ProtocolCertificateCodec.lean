import EthInapproximability.CurrentPaper.ProtocolVerifier

/-!
# A literal bit encoding for protocol certificates

Source: current paper v8, `03-exact-hardness.tex`, NP membership.
The dimensions of the matrix determine the lengths of the query tables.
Every node therefore needs only its two tag bits and its literal query table.
The parser is total on every bit string, including malformed strings. Its fuel
is the input length; exhaustion rejects rather than assuming well-formed input.

The results here concern this concrete finite parser and verifier. A running
time theorem in the eventual machine model is a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.ProtocolCertificateCodec

open ProtocolVerifier
open Workspace.Types.CommComplexity

def encode : Certificate → List Bool
  | .leaf b => [false, b]
  | .alice q l r => [true, false] ++ q ++ encode l ++ encode r
  | .bob q l r => [true, true] ++ q ++ encode l ++ encode r

theorem encode_length (p : Certificate) : (encode p).length = p.bits := by
  induction p with
  | leaf b => rfl
  | alice q l r hl hr => simp [encode, Certificate.bits, hl, hr]; omega
  | bob q l r hl hr => simp [encode, Certificate.bits, hl, hr]; omega

theorem depth_lt_bits (p : Certificate) : p.depth < p.bits := by
  induction p with
  | leaf b => simp [Certificate.depth, Certificate.bits]
  | alice q l r hl hr => simp only [Certificate.depth, Certificate.bits]; omega
  | bob q l r hl hr => simp only [Certificate.depth, Certificate.bits]; omega

/-- Read one tree and return the unused suffix. Each successful recursive call
is allowed one fewer level; malformed tags or short query tables reject. -/
def parseFuel (rows cols : Nat) : Nat → List Bool → Option (Certificate × List Bool)
  | 0, _ => none
  | _ + 1, false :: b :: rest => some (.leaf b, rest)
  | fuel + 1, true :: speaker :: rest => do
      let width := if speaker then cols else rows
      if width ≤ rest.length then
        let query := rest.take width
        let (l, rest₁) ← parseFuel rows cols fuel (rest.drop width)
        let (r, rest₂) ← parseFuel rows cols fuel rest₁
        pure (if speaker then .bob query l r else .alice query l r, rest₂)
      else none
  | _ + 1, _ => none

theorem parseFuel_encode (rows cols : Nat) (p : Certificate)
    (hw : p.wellFormed rows cols = true) (suffix : List Bool) (fuel : Nat)
    (hf : p.depth < fuel) :
    parseFuel rows cols fuel (encode p ++ suffix) = some (p, suffix) := by
  induction p generalizing suffix fuel with
  | leaf b =>
      cases fuel with
      | zero => simp [Certificate.depth] at hf
      | succ fuel => simp [encode, parseFuel]
  | alice q l r hl hr =>
      simp only [Certificate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hq := hw.1.1
      subst rows
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hleft : l.depth < fuel := by simp only [Certificate.depth] at hf; omega
          have hright : r.depth < fuel := by simp only [Certificate.depth] at hf; omega
          simp [encode, parseFuel, List.append_assoc,
            hl hw.1.2 (encode r ++ suffix) fuel hleft, hr hw.2 suffix fuel hright]
  | bob q l r hl hr =>
      simp only [Certificate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hq := hw.1.1
      subst cols
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hleft : l.depth < fuel := by simp only [Certificate.depth] at hf; omega
          have hright : r.depth < fuel := by simp only [Certificate.depth] at hf; omega
          simp [encode, parseFuel, List.append_assoc,
            hl hw.1.2 (encode r ++ suffix) fuel hleft, hr hw.2 suffix fuel hright]

/-- Total parser with fuel obtained from the raw input, not an auxiliary
certificate or an unbounded search. -/
def parse (rows cols : Nat) (input : List Bool) : Option (Certificate × List Bool) :=
  parseFuel rows cols input.length input

theorem parse_encode (rows cols : Nat) (p : Certificate)
    (hw : p.wellFormed rows cols = true) (suffix : List Bool) :
    parse rows cols (encode p ++ suffix) = some (p, suffix) := by
  apply parseFuel_encode rows cols p hw
  simp only [List.length_append, encode_length]
  exact (depth_lt_bits p).trans_le (Nat.le_add_right _ _)

/-- Reject trailing bytes: a certificate is exactly one encoded tree. -/
def decode (rows cols : Nat) (input : List Bool) : Option Certificate := do
  let (p, rest) ← parse rows cols input
  if rest.isEmpty then some p else none

theorem decode_encode (rows cols : Nat) (p : Certificate)
    (hw : p.wellFormed rows cols = true) :
    decode rows cols (encode p) = some p := by
  have hp := parse_encode rows cols p hw []
  simp only [List.append_nil] at hp
  rw [decode, hp]
  rfl

theorem encode_injective_on_wellFormed (rows cols : Nat) (p q : Certificate)
    (hp : p.wellFormed rows cols = true) (hq : q.wellFormed rows cols = true)
    (he : encode p = encode q) : p = q := by
  have h := congrArg (decode rows cols) he
  simpa only [decode_encode rows cols p hp, decode_encode rows cols q hq,
    Option.some.injEq] using h

/-- The verifier consumes an ordinary bit string, not an already parsed tree. -/
def rawVerify (rows cols threshold : Nat) (table input : List Bool) : Bool :=
  match decode rows cols input with
  | none => false
  | some p => verify rows cols threshold table p

theorem rawVerify_encode (rows cols threshold : Nat) (table : List Bool)
    (p : Certificate) (hw : p.wellFormed rows cols = true) :
    rawVerify rows cols threshold table (encode p) = verify rows cols threshold table p := by
  simp only [rawVerify, decode_encode rows cols p hw]

theorem rawVerify_sound (rows cols threshold : Nat) (table input : List Bool)
    (h : rawVerify rows cols threshold table input = true) :
    D (tableGame rows cols table) ≤ threshold := by
  unfold rawVerify at h
  split at h
  · contradiction
  · exact verify_sound rows cols threshold table _ h

theorem rawVerify_complete (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols)
    (h : D (tableGame rows cols table) ≤ threshold) :
    ∃ input : List Bool, rawVerify rows cols threshold table input = true := by
  obtain ⟨p, hp⟩ := verify_complete rows cols threshold table ht h
  have hw := ((verify_iff rows cols threshold table p).1 hp).2.1
  exact ⟨encode p, (rawVerify_encode rows cols threshold table p hw).trans hp⟩

theorem rawVerify_exists_iff (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols) :
    (∃ input : List Bool, rawVerify rows cols threshold table input = true) ↔
      D (tableGame rows cols table) ≤ threshold := by
  exact ⟨fun ⟨input, h⟩ => rawVerify_sound rows cols threshold table input h,
    rawVerify_complete rows cols threshold table ht⟩

/-- The polynomial certificate bound applies to the actual bit string passed
to the verifier, not merely to an abstract tree size. -/
theorem rawVerify_complete_polynomial (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols)
    (h : D (tableGame rows cols table) ≤ threshold) :
    ∃ input : List Bool, rawVerify rows cols threshold table input = true ∧
      input.length ≤ (rows + cols + 2) * (2 * (rows * cols) + 1) := by
  obtain ⟨p, hp, _, hb⟩ := verify_complete_polynomial rows cols threshold table ht h
  have hw := ((verify_iff rows cols threshold table p).1 hp).2.1
  refine ⟨encode p, (rawVerify_encode rows cols threshold table p hw).trans hp, ?_⟩
  simpa only [encode_length] using hb

theorem small_raw_certificate_iff (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols) :
    D (tableGame rows cols table) ≤ threshold ↔
      ∃ input : List Bool, rawVerify rows cols threshold table input = true ∧
        input.length ≤ (rows + cols + 2) * (2 * (rows * cols) + 1) := by
  exact ⟨rawVerify_complete_polynomial rows cols threshold table ht,
    fun ⟨input, h, _⟩ => rawVerify_sound rows cols threshold table input h⟩

/-- The stronger bound depends only on the number of explicit table entries.
It covers empty matrices without charging for unused local input labels. -/
theorem rawVerify_complete_table_polynomial (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols)
    (h : D (tableGame rows cols table) ≤ threshold) :
    ∃ input : List Bool, rawVerify rows cols threshold table input = true ∧
      input.length ≤ (table.length + 2) * (2 * table.length + 1) := by
  obtain ⟨p, hp, _, hb⟩ := verify_complete_table_polynomial rows cols threshold table ht h
  have hw := ((verify_iff rows cols threshold table p).1 hp).2.1
  refine ⟨encode p, (rawVerify_encode rows cols threshold table p hw).trans hp, ?_⟩
  simpa only [encode_length] using hb

theorem table_bounded_raw_certificate_iff (rows cols threshold : Nat) (table : List Bool)
    (ht : table.length = rows * cols) :
    D (tableGame rows cols table) ≤ threshold ↔
      ∃ input : List Bool, rawVerify rows cols threshold table input = true ∧
        input.length ≤ (table.length + 2) * (2 * table.length + 1) := by
  exact ⟨rawVerify_complete_table_polynomial rows cols threshold table ht,
    fun ⟨input, h, _⟩ => rawVerify_sound rows cols threshold table input h⟩

theorem decode_nonempty_suffix (rows cols : Nat) (p : Certificate)
    (hw : p.wellFormed rows cols = true) (suffix : List Bool) (hs : suffix ≠ []) :
    decode rows cols (encode p ++ suffix) = none := by
  rw [decode, parse_encode rows cols p hw suffix]
  simpa using hs

/-- Truncation and nonempty trailing data are not alternative certificates. -/
theorem malformed_regression :
    decode 1 1 [false] = none ∧ decode 1 1 [true, false, true] = none ∧
      decode 1 1 [false, true, false] = none := by decide

end EthInapproximability.CurrentPaper.ProtocolCertificateCodec
