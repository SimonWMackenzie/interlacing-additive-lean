import EthInapproximability.CurrentPaper.EncodedGraph

/-!
# Ordered three-CNF formulas as explicit Boolean strings

Source: frozen v8 `06-eth.tex`, the fixed ordered three-CNF source convention
in `thm:paper-sparse-gap-source` and the ETH conclusion. This file fixes the
concrete convention: a unary variable count; a canonical self-delimiting
binary clause count; then three signed zero-based variable indices per
ordered clause. Each sign is one bit (`true` means positive), followed by
the canonical binary index field from `EncodedCommunication`.

Repeated literals and clauses are allowed and keep their positions. Zero
variables are permitted only with no clauses; the empty conjunction is true.
The cited source-hardness theorems must concern this explicit language.
Neither their proofs nor any machine-runtime claim is asserted here.
-/

namespace EthInapproximability.CurrentPaper.EncodedCNF

open EncodedCommunication
open EncodedGraph (unary readUnary readUnary_append readUnary_sound)

structure Literal where
  «variable» : ℕ
  positive : Bool
  deriving DecidableEq

structure Clause where
  first : Literal
  second : Literal
  third : Literal
  deriving DecidableEq

structure Formula where
  «variables» : ℕ
  clauses : List Clause
  deriving DecidableEq

def Clause.Valid (c : Clause) (n : ℕ) : Prop :=
  c.first.variable < n ∧ c.second.variable < n ∧ c.third.variable < n

def Formula.Valid (f : Formula) : Prop := ∀ c ∈ f.clauses, c.Valid f.variables

instance (c : Clause) (n : ℕ) : Decidable (c.Valid n) := inferInstanceAs
  (Decidable (c.first.variable < n ∧ c.second.variable < n ∧ c.third.variable < n))

instance (f : Formula) : Decidable f.Valid := inferInstanceAs
  (Decidable (∀ c ∈ f.clauses, c.Valid f.variables))

def encodeLiteral (l : Literal) : List Bool := l.positive :: natField l.variable

def readLiteral : List Bool → Option (Literal × List Bool)
  | [] => none
  | sign :: bits => do
      let (index, rest) ← readNat bits
      pure (⟨index, sign⟩, rest)

theorem readLiteral_append (l : Literal) (rest : List Bool) :
    readLiteral (encodeLiteral l ++ rest) = some (l, rest) := by
  cases l
  simp [readLiteral, encodeLiteral, readNat_append]

theorem readLiteral_sound {input rest : List Bool} {l : Literal}
    (h : readLiteral input = some (l, rest)) : encodeLiteral l ++ rest = input := by
  cases input with
  | nil => simp [readLiteral] at h
  | cons b bits =>
    cases hp : readNat bits with
    | none => simp [readLiteral, hp] at h
    | some p =>
      obtain ⟨n, suffix⟩ := p
      simp only [readLiteral, hp, Bind.bind, Option.bind, pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa only [encodeLiteral, List.cons_append] using congrArg (List.cons b) (readNat_sound hp)

def encodeClause (c : Clause) : List Bool :=
  encodeLiteral c.first ++ encodeLiteral c.second ++ encodeLiteral c.third

def readClause (input : List Bool) : Option (Clause × List Bool) := do
  let (first, tail₁) ← readLiteral input
  let (second, tail₂) ← readLiteral tail₁
  let (third, rest) ← readLiteral tail₂
  pure (⟨first, second, third⟩, rest)

theorem readClause_append (c : Clause) (rest : List Bool) :
    readClause (encodeClause c ++ rest) = some (c, rest) := by
  cases c
  simp [readClause, encodeClause, List.append_assoc, readLiteral_append]

theorem readClause_sound {input rest : List Bool} {c : Clause}
    (h : readClause input = some (c, rest)) : encodeClause c ++ rest = input := by
  unfold readClause at h
  cases h₁ : readLiteral input with
  | none => simp [h₁] at h
  | some p₁ =>
    obtain ⟨a, tail₁⟩ := p₁
    cases h₂ : readLiteral tail₁ with
    | none => simp [h₁, h₂] at h
    | some p₂ =>
      obtain ⟨b, tail₂⟩ := p₂
      cases h₃ : readLiteral tail₂ with
      | none => simp [h₁, h₂, h₃] at h
      | some p₃ =>
        obtain ⟨d, suffix⟩ := p₃
        simp only [h₁, h₂, h₃, Bind.bind, Option.bind, pure,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [encodeClause, List.append_assoc, readLiteral_sound h₃,
          readLiteral_sound h₂, readLiteral_sound h₁]

def clauseFields : List Clause → List Bool
  | [] => []
  | c :: cs => encodeClause c ++ clauseFields cs

def readClauses : ℕ → List Bool → Option (List Clause × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (c, tail) ← readClause bits
      let (cs, rest) ← readClauses n tail
      pure (c :: cs, rest)

theorem readClauses_append (cs : List Clause) (rest : List Bool) :
    readClauses cs.length (clauseFields cs ++ rest) = some (cs, rest) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [readClauses, clauseFields, List.append_assoc, readClause_append, ih]

theorem readClauses_sound {k : ℕ} {input rest : List Bool} {cs : List Clause}
    (h : readClauses k input = some (cs, rest)) :
    cs.length = k ∧ clauseFields cs ++ rest = input := by
  induction k generalizing input cs with
  | zero =>
      simp only [readClauses, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [clauseFields]
  | succ k ih =>
      cases h₁ : readClause input with
      | none => simp [readClauses, h₁] at h
      | some p₁ =>
        obtain ⟨c, tail⟩ := p₁
        cases h₂ : readClauses k tail with
        | none => simp [readClauses, h₁, h₂] at h
        | some p₂ =>
          obtain ⟨ds, suffix⟩ := p₂
          simp only [readClauses, h₁, h₂, Bind.bind, Option.bind, pure,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hl, hs⟩ := ih h₂
          constructor
          · simpa using congrArg Nat.succ hl
          · simp only [clauseFields, List.append_assoc, hs, readClause_sound h₁]

def encode (f : Formula) : List Bool :=
  unary f.variables ++ natField f.clauses.length ++ clauseFields f.clauses

def decode (input : List Bool) : Option Formula := do
  let (n, tail₁) ← readUnary input
  let (count, tail₂) ← readNat tail₁
  let (clauses, rest) ← readClauses count tail₂
  let f : Formula := ⟨n, clauses⟩
  if rest = [] ∧ f.Valid then some f else none

theorem decode_encode (f : Formula) (hf : f.Valid) : decode (encode f) = some f := by
  have he := readClauses_append f.clauses []
  simp only [List.append_nil] at he
  simp [decode, encode, List.append_assoc, readUnary_append, readNat_append, he, hf]

theorem decode_spec {input : List Bool} {f : Formula} (h : decode input = some f) :
    f.Valid ∧ encode f = input := by
  unfold decode at h
  cases h₁ : readUnary input with
  | none => simp [h₁] at h
  | some p₁ =>
    obtain ⟨n, tail₁⟩ := p₁
    cases h₂ : readNat tail₁ with
    | none => simp [h₁, h₂] at h
    | some p₂ =>
      obtain ⟨k, tail₂⟩ := p₂
      cases h₃ : readClauses k tail₂ with
      | none => simp [h₁, h₂, h₃] at h
      | some p₃ =>
        obtain ⟨cs, rest⟩ := p₃
        simp only [h₁, h₂, h₃, Bind.bind, Option.bind] at h
        split at h
        · rename_i hv
          obtain ⟨rfl, hv⟩ := hv
          cases Option.some.inj h
          refine ⟨hv, ?_⟩
          obtain ⟨hl, hs⟩ := readClauses_sound h₃
          simp only [List.append_nil] at hs
          simp only [encode, hl, hs, List.append_assoc, readNat_sound h₂, readUnary_sound h₁]
        · contradiction

theorem decode_valid {input : List Bool} {f : Formula} (h : decode input = some f) :
    f.Valid := (decode_spec h).1

theorem decode_sound {input : List Bool} {f : Formula} (h : decode input = some f) :
    encode f = input := (decode_spec h).2

theorem encodeLiteral_length (l : Literal) :
    (encodeLiteral l).length = 2 * l.variable.bits.length + 2 := by
  simp [encodeLiteral, natField, field_length]

theorem encodeClause_length_lower (c : Clause) : 6 ≤ (encodeClause c).length := by
  simp only [encodeClause, List.length_append, encodeLiteral_length]
  omega

theorem clauseFields_length_lower (cs : List Clause) :
    6 * cs.length ≤ (clauseFields cs).length := by
  induction cs with
  | nil => simp [clauseFields]
  | cons c cs ih =>
      have h := encodeClause_length_lower c
      simp only [clauseFields, List.length_append, List.length_cons]
      omega

theorem encode_length_lower (f : Formula) :
    f.variables + 6 * f.clauses.length + 2 ≤ (encode f).length := by
  have h := clauseFields_length_lower f.clauses
  simp only [encode, unary, List.length_append, List.length_replicate,
    List.length_singleton, natField, field_length]
  omega

theorem decoded_size_bound {input : List Bool} {f : Formula}
    (h : decode input = some f) :
    f.variables + 6 * f.clauses.length + 2 ≤ input.length := by
  rw [← decode_sound h]
  exact encode_length_lower f

theorem decoded_variables_bound {input : List Bool} {f : Formula}
    (h : decode input = some f) : f.variables ≤ input.length := by
  have := decoded_size_bound h
  omega

theorem decoded_clauses_bound {input : List Bool} {f : Formula}
    (h : decode input = some f) : f.clauses.length ≤ input.length := by
  have := decoded_size_bound h
  omega

def Formula.literalOccurrences (f : Formula) : ℕ := 3 * f.clauses.length

theorem decoded_occurrences_bound {input : List Bool} {f : Formula}
    (h : decode input = some f) : f.literalOccurrences ≤ input.length := by
  have := decoded_size_bound h
  unfold Formula.literalOccurrences
  omega

theorem encodeLiteral_length_upper (l : Literal) :
    (encodeLiteral l).length ≤ 2 * l.variable + 2 := by
  have h := EncodedGraph.natField_length_upper l.variable
  simp only [encodeLiteral, List.length_cons]
  omega

theorem encodeClause_length_upper (c : Clause) {n : ℕ} (h : c.Valid n) :
    (encodeClause c).length ≤ 6 * n + 6 := by
  have ha := encodeLiteral_length_upper c.first
  have hb := encodeLiteral_length_upper c.second
  have hc := encodeLiteral_length_upper c.third
  simp only [encodeClause, List.length_append]
  unfold Clause.Valid at h
  omega

theorem clauseFields_length_upper (n : ℕ) (cs : List Clause)
    (h : ∀ c ∈ cs, c.Valid n) : (clauseFields cs).length ≤ cs.length * (6 * n + 6) := by
  induction cs with
  | nil => simp [clauseFields]
  | cons c cs ih =>
      have hc := encodeClause_length_upper c (h c (by simp))
      have hi := ih (fun d hd => h d (by simp [hd]))
      simp only [clauseFields, List.length_append, List.length_cons]
      nlinarith

theorem encode_length_upper (f : Formula) (hf : f.Valid) :
    (encode f).length ≤ f.variables + 2 + f.clauses.length * (6 * f.variables + 8) := by
  have hc := clauseFields_length_upper f.variables f.clauses hf
  have hh := EncodedGraph.natField_length_upper f.clauses.length
  simp only [encode, unary, List.length_append, List.length_replicate, List.length_singleton]
  nlinarith

/-- A total literal evaluator; a well-formed assignment supplies every
validated variable. The default is used only outside that valid situation. -/
def Literal.eval (l : Literal) (assignment : List Bool) : Bool :=
  if l.positive then assignment.getD l.variable false else !(assignment.getD l.variable false)

def Clause.eval (c : Clause) (assignment : List Bool) : Bool :=
  c.first.eval assignment || c.second.eval assignment || c.third.eval assignment

def Formula.eval (f : Formula) (assignment : List Bool) : Bool :=
  f.clauses.all (fun c => c.eval assignment)

/-- The witness is literally a finite Boolean assignment of the declared
length, not an abstract satisfiability oracle. -/
def Satisfiable (f : Formula) : Prop :=
  ∃ assignment : List Bool, assignment.length = f.variables ∧ f.eval assignment = true

def Language : Set (List Bool) := { input | ∃ f, decode input = some f ∧ Satisfiable f }

theorem language_iff_decoded {input : List Bool} {f : Formula}
    (h : decode input = some f) : input ∈ Language ↔ Satisfiable f := by
  constructor
  · rintro ⟨g, hg, hs⟩
    rw [h] at hg
    cases Option.some.inj hg
    exact hs
  · intro hs
    exact ⟨f, h, hs⟩

theorem encode_mem_iff (f : Formula) (hf : f.Valid) :
    encode f ∈ Language ↔ Satisfiable f := language_iff_decoded (decode_encode f hf)

theorem malformed_not_mem {input : List Bool} (h : decode input = none) : input ∉ Language := by
  rintro ⟨f, hf, _⟩
  rw [h] at hf
  contradiction

theorem empty_satisfiable (n : ℕ) : Satisfiable ⟨n, []⟩ := by
  refine ⟨List.replicate n false, ?_, ?_⟩ <;> simp [Formula.eval]

theorem zero_variables_iff_empty (f : Formula) (hf : f.Valid) (hzero : f.variables = 0) :
    f.clauses = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  have h := (hf c hc).1
  omega

def verifyEncoded (input assignment : List Bool) : Bool :=
  match decode input with
  | none => false
  | some f => decide (assignment.length = f.variables) && f.eval assignment

theorem language_iff_assignment (input : List Bool) :
    input ∈ Language ↔ ∃ assignment, verifyEncoded input assignment = true := by
  cases hd : decode input with
  | none => simp [Language, hd, verifyEncoded]
  | some f =>
      rw [language_iff_decoded hd]
      simp [Satisfiable, verifyEncoded, hd]

theorem language_iff_short_assignment (input : List Bool) :
    input ∈ Language ↔ ∃ assignment, assignment.length ≤ input.length ∧
      verifyEncoded input assignment = true := by
  constructor
  · rintro ⟨f, hf, assignment, hlen, hsat⟩
    refine ⟨assignment, hlen ▸ decoded_variables_bound hf, ?_⟩
    simp [verifyEncoded, hf, hlen, hsat]
  · rintro ⟨assignment, _, h⟩
    exact (language_iff_assignment input).mpr ⟨assignment, h⟩

end EthInapproximability.CurrentPaper.EncodedCNF
