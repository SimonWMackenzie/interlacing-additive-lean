import EthInapproximability.CurrentPaper.SourceBooleanDefinitions

/-!
# The literal PCP constraint encoding

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
Numeric headers and query labels use the existing canonical natural-number
fields; truth tables follow the explicit finite-function enumeration.
-/

namespace EthInapproximability.CurrentPaper.EncodedETHSource

structure ConstraintInstance (a q : ℕ) where
  vertices : ℕ
  constraints : ℕ
  system : SourceBooleanEncoding.CSP vertices constraints a q

def constraintBits {a q : ℕ} (P : ConstraintInstance a q) : List Bool :=
  EncodedCommunication.natField P.vertices ++
  EncodedCommunication.natField P.constraints ++
  EncodedCommunication.natField a ++ EncodedCommunication.natField q ++
  (List.ofFn fun j : Fin P.constraints =>
    (List.ofFn fun t : Fin q => EncodedCommunication.natField (P.system.query j t).val).flatten ++
    List.ofFn fun z : Fin (a ^ q) => P.system.accept j (finFunctionFinEquiv.symm z)).flatten

end EthInapproximability.CurrentPaper.EncodedETHSource

namespace EthInapproximability.CurrentPaper.SourceCSPCodec

open EncodedCommunication EncodedETHSource

/-- Encode a finite vector in its literal index order. -/
def fnFields {α : Type*} (encode : α → List Bool) {k : ℕ} (v : Fin k → α) : List Bool :=
  (List.ofFn fun i => encode (v i)).flatten

/-- A prefix reader for a fixed number of entries. This does not invoke
an unbounded search or assume that the input has enough bits. -/
def readFn {α : Type*} (read : List Bool → Option (α × List Bool)) :
    (k : ℕ) → List Bool → Option ((Fin k → α) × List Bool)
  | 0, bits => some (Fin.elim0, bits)
  | k + 1, bits => do
      let (x, tail) ← read bits
      let (xs, rest) ← readFn read k tail
      pure (Fin.cases x xs, rest)

theorem fnFields_zero {α : Type*} (enc : α → List Bool) (v : Fin 0 → α) :
    fnFields enc v = [] := rfl

theorem fnFields_succ {α : Type*} (enc : α → List Bool) {k : ℕ}
    (v : Fin (k + 1) → α) :
    fnFields enc v = enc (v 0) ++ fnFields enc (fun i => v i.succ) := by
  simp only [fnFields, List.ofFn_succ, List.flatten_cons]

theorem readFn_append {α : Type*} (enc : α → List Bool)
    (read : List Bool → Option (α × List Bool))
    (hread : ∀ x rest, read (enc x ++ rest) = some (x, rest))
    (k : ℕ) (v : Fin k → α) (rest : List Bool) :
    readFn read k (fnFields enc v ++ rest) = some (v, rest) := by
  induction k with
  | zero =>
      have hv : v = Fin.elim0 := funext fun i => Fin.elim0 i
      simp only [fnFields_zero, List.nil_append, readFn, hv]
  | succ k ih =>
      rw [fnFields_succ, List.append_assoc]
      simp only [readFn, hread, Bind.bind, Option.bind, ih, pure]
      congr 1
      apply Prod.ext
      · funext i
        cases i using Fin.cases <;> rfl
      · rfl

theorem readFn_sound {α : Type*} (enc : α → List Bool)
    (read : List Bool → Option (α × List Bool))
    (hread : ∀ {bits x rest}, read bits = some (x, rest) → enc x ++ rest = bits)
    {k : ℕ} {bits rest : List Bool} {v : Fin k → α}
    (h : readFn read k bits = some (v, rest)) : fnFields enc v ++ rest = bits := by
  induction k generalizing bits rest with
  | zero =>
      simp only [readFn, Option.some.injEq, Prod.mk.injEq] at h
      simp only [fnFields_zero, List.nil_append, h.2]
  | succ k ih =>
      cases h₁ : read bits with
      | none => simp [readFn, h₁] at h
      | some p =>
          obtain ⟨x, tail⟩ := p
          cases h₂ : readFn read k tail with
          | none => simp [readFn, h₁, h₂] at h
          | some p₂ =>
              obtain ⟨xs, suffix⟩ := p₂
              simp only [readFn, h₁, h₂, Bind.bind, Option.bind, pure,
                Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [fnFields_succ]
              simp only [Fin.cases_zero, Fin.cases_succ, List.append_assoc]
              rw [ih h₂, hread h₁]

def readIndex (n : ℕ) (bits : List Bool) : Option (Fin n × List Bool) := do
  let (v, rest) ← readNat bits
  if h : v < n then some (⟨v, h⟩, rest) else none

theorem readIndex_append (n : ℕ) (v : Fin n) (rest : List Bool) :
    readIndex n (natField v.val ++ rest) = some (v, rest) := by
  simp [readIndex, readNat_append, v.isLt]

theorem readIndex_sound {n : ℕ} {bits rest : List Bool} {v : Fin n}
    (h : readIndex n bits = some (v, rest)) : natField v.val ++ rest = bits := by
  unfold readIndex at h
  cases hp : readNat bits with
  | none => simp [hp] at h
  | some pair =>
      obtain ⟨j, tail⟩ := pair
      simp only [hp, Bind.bind, Option.bind] at h
      split at h
      · cases Option.some.inj h
        exact readNat_sound hp
      · contradiction

def readBit : List Bool → Option (Bool × List Bool)
  | [] => none
  | b :: rest => some (b, rest)

theorem readBit_append (b : Bool) (rest : List Bool) :
    readBit ([b] ++ rest) = some (b, rest) := rfl

theorem readBit_sound {bits rest : List Bool} {b : Bool}
    (h : readBit bits = some (b, rest)) : [b] ++ rest = bits := by
  cases bits with
  | nil => simp [readBit] at h
  | cons c cs =>
      cases Option.some.inj h
      rfl

abbrev Row (n a q : ℕ) := (Fin q → Fin n) × (Fin (a ^ q) → Bool)

def rowFields {n a q : ℕ} (row : Row n a q) : List Bool :=
  fnFields (fun v => natField v.val) row.1 ++ fnFields (fun b => [b]) row.2

def readRow (n a q : ℕ) (bits : List Bool) : Option (Row n a q × List Bool) := do
  let (query, tail) ← readFn (readIndex n) q bits
  let (table, rest) ← readFn readBit (a ^ q) tail
  pure ((query, table), rest)

theorem readRow_append {n a q : ℕ} (row : Row n a q) (rest : List Bool) :
    readRow n a q (rowFields row ++ rest) = some (row, rest) := by
  obtain ⟨query, table⟩ := row
  simp only [rowFields, List.append_assoc, readRow,
    readFn_append _ _ (readIndex_append n), Bind.bind, Option.bind,
    readFn_append _ _ readBit_append, pure]

theorem readRow_sound {n a q : ℕ} {bits rest : List Bool} {row : Row n a q}
    (h : readRow n a q bits = some (row, rest)) : rowFields row ++ rest = bits := by
  unfold readRow at h
  cases h₁ : readFn (readIndex n) q bits with
  | none => simp [h₁] at h
  | some p₁ =>
      obtain ⟨query, tail⟩ := p₁
      cases h₂ : readFn readBit (a ^ q) tail with
      | none => simp [h₁, h₂] at h
      | some p₂ =>
          obtain ⟨table, suffix⟩ := p₂
          simp only [h₁, h₂, Bind.bind, Option.bind, pure,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [rowFields, List.append_assoc,
            readFn_sound _ _ (fun h => readBit_sound h) h₂,
            readFn_sound _ _ (fun h => readIndex_sound h) h₁]

def rowsOf {a q : ℕ} (P : ConstraintInstance a q) : Fin P.constraints → Row P.vertices a q :=
  fun j => (P.system.query j, fun z => P.system.accept j (finFunctionFinEquiv.symm z))

def fromRows (n m a q : ℕ) (rows : Fin m → Row n a q) : ConstraintInstance a q where
  vertices := n
  constraints := m
  system := {
    query := fun j => (rows j).1
    accept := fun j τ => (rows j).2 (finFunctionFinEquiv τ) }

theorem rowsOf_fromRows (n m a q : ℕ) (rows : Fin m → Row n a q) :
    rowsOf (fromRows n m a q rows) = rows := by
  funext j
  apply Prod.ext
  · rfl
  · funext z
    simp [rowsOf, fromRows]

theorem fromRows_rowsOf {a q : ℕ} (P : ConstraintInstance a q) :
    fromRows P.vertices P.constraints a q (rowsOf P) = P := by
  cases P with
  | mk n m system =>
      cases system with
      | mk query accept =>
          simp only [fromRows, rowsOf, Equiv.symm_apply_apply]

theorem ofFn_singleton_flatten {α : Type*} {k : ℕ} (v : Fin k → α) :
    (List.ofFn fun i => [v i]).flatten = List.ofFn v := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.ofFn_succ, List.flatten_cons, List.singleton_append, ih]

theorem constraintBits_eq {a q : ℕ} (P : ConstraintInstance a q) :
    constraintBits P = natField P.vertices ++ natField P.constraints ++
      natField a ++ natField q ++ fnFields rowFields (rowsOf P) := by
  simp only [constraintBits, fnFields, rowsOf, rowFields, ofFn_singleton_flatten]

/-- Decode the literal four headers and all labelled rows. The alphabet
and query width are fixed parameters, checked against their header values.
Malformed labels, truncated tables and all trailing bits are rejected. -/
def decode (a q : ℕ) (bits : List Bool) : Option (ConstraintInstance a q) := do
  let (n, tail₁) ← readNat bits
  let (m, tail₂) ← readNat tail₁
  let (a', tail₃) ← readNat tail₂
  let (q', tail₄) ← readNat tail₃
  if a' = a ∧ q' = q then
    let (rows, rest) ← readFn (readRow n a q) m tail₄
    if rest = [] then some (fromRows n m a q rows) else none
  else none

theorem decode_encode {a q : ℕ} (P : ConstraintInstance a q) :
    decode a q (constraintBits P) = some P := by
  rw [constraintBits_eq]
  have hr := readFn_append rowFields (readRow P.vertices a q) readRow_append
    P.constraints (rowsOf P) []
  simp only [List.append_nil] at hr
  simp only [decode, List.append_assoc, readNat_append, Bind.bind, Option.bind,
    and_self, ↓reduceIte, hr, fromRows_rowsOf]

/-- Every successful parse is the canonical encoding of exactly the
returned indexed constraint system, with no omitted trailing data. -/
theorem decode_sound {a q : ℕ} {bits : List Bool} {P : ConstraintInstance a q}
    (h : decode a q bits = some P) : constraintBits P = bits := by
  unfold decode at h
  cases h₁ : readNat bits with
  | none => simp [h₁] at h
  | some p₁ =>
      obtain ⟨n, tail₁⟩ := p₁
      cases h₂ : readNat tail₁ with
      | none => simp [h₁, h₂] at h
      | some p₂ =>
          obtain ⟨m, tail₂⟩ := p₂
          cases h₃ : readNat tail₂ with
          | none => simp [h₁, h₂, h₃] at h
          | some p₃ =>
              obtain ⟨a', tail₃⟩ := p₃
              cases h₄ : readNat tail₃ with
              | none => simp [h₁, h₂, h₃, h₄] at h
              | some p₄ =>
                  obtain ⟨q', tail₄⟩ := p₄
                  simp only [h₁, h₂, h₃, h₄, Bind.bind, Option.bind] at h
                  split at h
                  · rename_i hh
                    obtain ⟨ha, hq⟩ := hh
                    subst a'
                    subst q'
                    cases hrow : readFn (readRow n a q) m tail₄ with
                    | none => simp [hrow] at h
                    | some p =>
                        obtain ⟨rows, rest⟩ := p
                        simp only [hrow, Bind.bind, Option.bind] at h
                        split at h
                        · rename_i hrest
                          subst rest
                          cases Option.some.inj h
                          rw [constraintBits_eq, rowsOf_fromRows]
                          have he := readFn_sound rowFields (readRow n a q)
                            (fun h => readRow_sound h) hrow
                          simp only [List.append_nil] at he
                          simp only [fromRows, List.append_assoc, he,
                            readNat_sound h₄, readNat_sound h₃,
                            readNat_sound h₂, readNat_sound h₁]
                        · contradiction
                  · contradiction

theorem constraintBits_injective (a q : ℕ) :
    Function.Injective (@constraintBits a q) := by
  intro P Q h
  have he := congrArg (decode a q) h
  simpa only [decode_encode, Option.some.injEq] using he

theorem decode_iff {a q : ℕ} {bits : List Bool} {P : ConstraintInstance a q} :
    decode a q bits = some P ↔ constraintBits P = bits := by
  constructor
  · exact decode_sound
  · intro h
    rw [← h]
    exact decode_encode P

theorem fnFields_length_lower {α : Type*} (enc : α → List Bool) (L : ℕ)
    (hL : ∀ x, L ≤ (enc x).length) {k : ℕ} (v : Fin k → α) :
    k * L ≤ (fnFields enc v).length := by
  induction k with
  | zero => simp [fnFields_zero]
  | succ k ih =>
      rw [fnFields_succ, List.length_append]
      have hh := hL (v 0)
      have ht := ih (fun i => v i.succ)
      nlinarith

theorem natField_length_pos (n : ℕ) : 1 ≤ (natField n).length := by
  simp only [natField, field_length]
  omega

theorem rowFields_length_lower {n a q : ℕ} (row : Row n a q) :
    q + a ^ q ≤ (rowFields row).length := by
  have hq := fnFields_length_lower (fun v : Fin n => natField v.val) 1
    (fun v => natField_length_pos v.val) row.1
  have ht := fnFields_length_lower (fun b : Bool => [b]) 1 (fun _ => le_rfl) row.2
  simp only [rowFields, List.length_append]
  omega

theorem constraintBits_length_lower {a q : ℕ} (P : ConstraintInstance a q) :
    4 + P.constraints * (q + a ^ q) ≤ (constraintBits P).length := by
  have hn := natField_length_pos P.vertices
  have hm := natField_length_pos P.constraints
  have ha := natField_length_pos a
  have hq := natField_length_pos q
  have hr := fnFields_length_lower rowFields (q + a ^ q)
    (fun row : Row P.vertices a q => rowFields_length_lower row) (rowsOf P)
  rw [constraintBits_eq]
  simp only [List.length_append]
  omega

theorem constraints_le_bits {a q : ℕ} (P : ConstraintInstance a q) :
    P.constraints ≤ (constraintBits P).length := by
  have h := constraintBits_length_lower P
  have hfactor : 1 ≤ q + a ^ q := by
    by_cases hq : q = 0
    · simp [hq]
    · omega
  have hm := Nat.mul_le_mul_left P.constraints hfactor
  omega

/-- This is the separately exposed size promise needed by unary-loop
implementations. The raw decoder above does not silently discard isolated
variables or reject large declared vertex counts. -/
def ValidSize {a q : ℕ} (P : ConstraintInstance a q) : Prop :=
  P.vertices ≤ q * P.constraints

instance {a q : ℕ} (P : ConstraintInstance a q) : Decidable (ValidSize P) :=
  inferInstanceAs (Decidable (P.vertices ≤ q * P.constraints))

def decodeBounded (a q : ℕ) (bits : List Bool) : Option (ConstraintInstance a q) := do
  let P ← decode a q bits
  if ValidSize P then some P else none

theorem decodeBounded_encode {a q : ℕ} (P : ConstraintInstance a q) (hP : ValidSize P) :
    decodeBounded a q (constraintBits P) = some P := by
  simp [decodeBounded, decode_encode, hP]

theorem decodeBounded_spec {a q : ℕ} {bits : List Bool} {P : ConstraintInstance a q}
    (h : decodeBounded a q bits = some P) :
    constraintBits P = bits ∧ ValidSize P ∧
      P.constraints ≤ bits.length ∧ P.vertices ≤ q * bits.length := by
  unfold decodeBounded at h
  cases hd : decode a q bits with
  | none => simp [hd] at h
  | some Q =>
      simp only [hd, Bind.bind, Option.bind] at h
      split at h
      · rename_i hQ
        cases Option.some.inj h
        have he := decode_sound hd
        have hm := constraints_le_bits P
        rw [he] at hm
        exact ⟨he, hQ, hm, hQ.trans (Nat.mul_le_mul_left q hm)⟩
      · contradiction

end EthInapproximability.CurrentPaper.SourceCSPCodec
