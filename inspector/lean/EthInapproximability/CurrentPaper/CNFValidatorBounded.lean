import EthInapproximability.CurrentPaper.EncodedCNF

/-!
# Early-rejecting bounded ordered-3CNF parser specification (unit 4, B4-S1)

Source: frozen v8 `06-eth.tex`, the ordered three-CNF convention of
`EncodedCNF`. This is an executable parser specification with a literal
input-length clause-count cap and immediate `index < n` checks, in the exact
order in which the finite validator reads the word. Its equality to the
admitted all-input parser `EncodedCNF.decode` is proved; no machine claim is
made here. Imports: admitted production modules only (shared with Paper A).
-/

namespace EthInapproximability.CurrentPaper.CNFValidator.Bounded

open EncodedCommunication EncodedCNF
open EncodedGraph (unary readUnary readUnary_append readUnary_sound)

def readCheckedLiteral (n : ℕ) : List Bool → Option (Literal × List Bool)
  | [] => none
  | sign :: bits => do
      let (k, rest) ← readNat bits
      if k < n then some (⟨k, sign⟩, rest) else none

def readCheckedClauses (n : ℕ) : ℕ → List Bool → Option (List Clause × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (a, t₁) ← readCheckedLiteral n bits
      let (b, t₂) ← readCheckedLiteral n t₁
      let (c, t₃) ← readCheckedLiteral n t₂
      let (cs, rest) ← readCheckedClauses n count t₃
      pure (⟨a, b, c⟩ :: cs, rest)

def ValidClauses (n : ℕ) (cs : List Clause) : Prop := ∀ c ∈ cs, c.Valid n

instance (n : ℕ) (cs : List Clause) : Decidable (ValidClauses n cs) :=
  inferInstanceAs (Decidable (∀ c ∈ cs, c.Valid n))

theorem readCheckedLiteral_eq (n : ℕ) (bits : List Bool) :
    readCheckedLiteral n bits =
      (readLiteral bits).bind (fun p => if p.1.variable < n then some p else none) := by
  cases bits with
  | nil => rfl
  | cons s bits =>
      cases h : readNat bits with
      | none => simp [readCheckedLiteral, readLiteral, h]
      | some p =>
          obtain ⟨k, rest⟩ := p
          by_cases hk : k < n <;> simp [readCheckedLiteral, readLiteral, h, hk]

theorem validClauses_cons (n : ℕ) (c : Clause) (cs : List Clause) :
    ValidClauses n (c :: cs) ↔
      (c.first.variable < n ∧ c.second.variable < n ∧ c.third.variable < n) ∧
        ValidClauses n cs := by
  simp [ValidClauses, Clause.Valid]

theorem readCheckedClauses_eq (n count : ℕ) (bits : List Bool) :
    readCheckedClauses n count bits =
      (readClauses count bits).bind
        (fun p => if ValidClauses n p.1 then some p else none) := by
  induction count generalizing bits with
  | zero => simp [readCheckedClauses, readClauses, ValidClauses]
  | succ count ih =>
      simp only [readCheckedClauses, readClauses, readClause, readCheckedLiteral_eq, ih]
      cases h₁ : readLiteral bits with
      | none => simp
      | some p₁ =>
        obtain ⟨a, t₁⟩ := p₁
        cases h₂ : readLiteral t₁ with
        | none => by_cases ha : a.variable < n <;> simp [h₂, ha]
        | some p₂ =>
          obtain ⟨b, t₂⟩ := p₂
          cases h₃ : readLiteral t₂ with
          | none =>
              by_cases ha : a.variable < n <;> by_cases hb : b.variable < n <;>
                simp [h₂, h₃, ha, hb]
          | some p₃ =>
            obtain ⟨c, t₃⟩ := p₃
            cases h₄ : readClauses count t₃ with
            | none =>
                by_cases ha : a.variable < n <;> by_cases hb : b.variable < n <;>
                  by_cases hc : c.variable < n <;> simp [h₂, h₃, h₄, ha, hb, hc]
            | some p₄ =>
              obtain ⟨cs, rest⟩ := p₄
              by_cases ha : a.variable < n <;> by_cases hb : b.variable < n <;>
                by_cases hc : c.variable < n <;> by_cases hv : ValidClauses n cs <;>
                simp [h₂, h₃, h₄, ha, hb, hc, hv, validClauses_cons]

theorem readCheckedClauses_sound {n count : ℕ} {bits rest : List Bool}
    {cs : List Clause} (h : readCheckedClauses n count bits = some (cs, rest)) :
    readClauses count bits = some (cs, rest) ∧ ValidClauses n cs := by
  rw [readCheckedClauses_eq] at h
  cases hp : readClauses count bits with
  | none => simp [hp] at h
  | some p =>
      simp only [hp, Option.bind_some] at h
      split at h
      · rename_i hv
        cases Option.some.inj h
        exact ⟨rfl, hv⟩
      · contradiction

theorem readCheckedClauses_append (n : ℕ) (cs : List Clause)
    (h : ValidClauses n cs) (rest : List Bool) :
    readCheckedClauses n cs.length (clauseFields cs ++ rest) = some (cs, rest) := by
  simp [readCheckedClauses_eq, readClauses_append, h]

def decode (input : List Bool) : Option Formula := do
  let (n, tail₁) ← readUnary input
  let (count, tail₂) ← readNat tail₁
  if count ≤ input.length then do
    let (clauses, rest) ← readCheckedClauses n count tail₂
    if rest = [] then some ⟨n, clauses⟩ else none
  else none

theorem decode_encode (f : Formula) (hf : f.Valid) : decode (encode f) = some f := by
  have he := readCheckedClauses_append f.variables f.clauses hf []
  simp only [List.append_nil] at he
  have hcount : f.clauses.length ≤ (encode f).length := by
    have := encode_length_lower f
    omega
  simp only [encode, List.append_assoc] at hcount
  unfold decode
  simp only [encode, List.append_assoc, readUnary_append, readNat_append,
    Bind.bind, Option.bind]
  simp only [hcount, ↓reduceIte, he]

theorem decode_sound {input : List Bool} {f : Formula} (h : decode input = some f) :
    EncodedCNF.decode input = some f := by
  unfold decode at h
  cases h₁ : readUnary input with
  | none => simp [h₁] at h
  | some p₁ =>
    obtain ⟨n, tail₁⟩ := p₁
    cases h₂ : readNat tail₁ with
    | none => simp [h₁, h₂] at h
    | some p₂ =>
      obtain ⟨count, tail₂⟩ := p₂
      simp only [h₁, h₂, Bind.bind, Option.bind] at h
      split at h
      · cases h₃ : readCheckedClauses n count tail₂ with
        | none => simp [h₃] at h
        | some p₃ =>
          obtain ⟨cs, rest⟩ := p₃
          simp only [h₃] at h
          split at h
          · rename_i hrest
            subst rest
            cases Option.some.inj h
            obtain ⟨hr, hv⟩ := readCheckedClauses_sound h₃
            have hv' : (EncodedCNF.Formula.mk n cs).Valid := hv
            simp [EncodedCNF.decode, h₁, h₂, hr, hv']
          · contradiction
      · contradiction

theorem decode_eq (input : List Bool) : decode input = EncodedCNF.decode input := by
  cases hd : decode input with
  | some g => exact (decode_sound hd).symm
  | none =>
      cases hg : EncodedCNF.decode input with
      | none => rfl
      | some g =>
          have hs := EncodedCNF.decode_sound hg
          have hv := EncodedCNF.decode_valid hg
          have hc := decode_encode g hv
          rw [hs, hd] at hc
          contradiction

theorem readCheckedLiteral_length {n : ℕ} {bits rest : List Bool} {l : Literal}
    (h : readCheckedLiteral n bits = some (l, rest)) : rest.length < bits.length := by
  rw [readCheckedLiteral_eq] at h
  cases hp : readLiteral bits with
  | none => simp [hp] at h
  | some p =>
      simp only [hp, Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        have hl := congrArg List.length (readLiteral_sound hp)
        simp only [List.length_append, encodeLiteral, List.length_cons] at hl
        omega
      · contradiction

end EthInapproximability.CurrentPaper.CNFValidator.Bounded
