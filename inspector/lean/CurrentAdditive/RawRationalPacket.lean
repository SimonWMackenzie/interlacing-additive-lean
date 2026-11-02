import CurrentAdditive.CompactSeedLabelSize

/-! Proof-free native input arrays are validated to an exact finite rational
matrix packet. This is not a byte-level parser or a physical machine clock. -/

namespace Paper2.RawRationalPacket

open scoped BigOperators
open Paper2.CompactRationalPacket
open Paper2.YaoMaterialization
open Paper2.CompactFinCodec

structure RawLaw (n : ℕ) where
  numerator : Fin n → ℕ
  denominator : Fin n → ℕ

def RawLaw.Valid {n : ℕ} (R : RawLaw n) : Prop :=
  (∀ i, 0 < R.numerator i ∧ 0 < R.denominator i) ∧
    (∑ i, (R.numerator i : ℚ) / R.denominator i) = 1

instance RawLaw.validDecidable {n : ℕ} (R : RawLaw n) : Decidable R.Valid := by
  unfold Valid
  infer_instance

/-- The validation check is executable for a finite indexed array. -/
def RawLaw.valid (R : RawLaw n) : Bool := decide R.Valid

def RawLaw.toLaw? {n : ℕ} (R : RawLaw n) :
    Option (PositiveRationalLaw (Fin n)) :=
  if h : R.Valid then
    some {
      weight := fun i => (R.numerator i : ℚ) / R.denominator i
      positive := by
        intro i
        have hi := h.1 i
        exact div_pos (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
      total := h.2
    }
  else none

theorem RawLaw.toLaw?_some_iff {n : ℕ} (R : RawLaw n) :
    (∃ μ, R.toLaw? = some μ) ↔ R.Valid := by
  unfold toLaw?
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
  · constructor
    · rintro ⟨_, hh⟩
      cases hh
    · intro hv
      exact False.elim (h hv)

theorem RawLaw.toLaw?_weight {n : ℕ} (R : RawLaw n)
    (μ : PositiveRationalLaw (Fin n)) (h : R.toLaw? = some μ)
    (i : Fin n) :
    μ.weight i = (R.numerator i : ℚ) / R.denominator i := by
  unfold toLaw? at h
  split_ifs at h with hv
  cases h
  rfl

structure RawPacket (rows cols : ℕ) where
  bits : List Bool
  row : RawLaw rows
  col : RawLaw cols

/-- Validate dimensions and both input laws before constructing the
single indexed table used by generators and entry lookup. -/
def RawPacket.compile? {rows cols : ℕ} (R : RawPacket rows cols) :
    Option (Packet rows cols) := do
  if h : R.bits.length = rows * cols then
    let μ ← R.row.toLaw?
    let ν ← R.col.toLaw?
    some {
      table := ⟨R.bits, h⟩
      rowLaw := μ
      colLaw := ν
    }
  else none

theorem RawPacket.compile?_some_iff {rows cols : ℕ}
    (R : RawPacket rows cols) :
    (∃ P, R.compile? = some P) ↔
      R.bits.length = rows * cols ∧ R.row.Valid ∧ R.col.Valid := by
  unfold compile?
  split_ifs with hlen
  · constructor
    · rintro ⟨P, hP⟩
      cases hr : R.row.toLaw? with
      | none => simp [hr] at hP
      | some μ =>
        cases hc : R.col.toLaw? with
        | none => simp [hr, hc] at hP
        | some ν =>
          exact ⟨hlen, (RawLaw.toLaw?_some_iff R.row).mp ⟨μ, hr⟩,
            (RawLaw.toLaw?_some_iff R.col).mp ⟨ν, hc⟩⟩
    · rintro ⟨_, hr, hc⟩
      obtain ⟨μ, hμ⟩ := (RawLaw.toLaw?_some_iff R.row).mpr hr
      obtain ⟨ν, hν⟩ := (RawLaw.toLaw?_some_iff R.col).mpr hc
      refine ⟨{table := ⟨R.bits, hlen⟩, rowLaw := μ, colLaw := ν}, ?_⟩
      simp [hμ, hν]
  · simp [hlen]

theorem RawPacket.compiled_lookup_encoded {rows cols : ℕ}
    (R : RawPacket rows cols) (P : Packet rows cols)
    (h : R.compile? = some P) (i : Fin rows) (j : Fin cols) :
    lookup P ((codec rows).encode i) ((codec cols).encode j) =
      some (R.bits.get (Fin.cast (by
        have hh : R.bits.length = rows * cols :=
          (R.compile?_some_iff.mp ⟨P, h⟩).1
        exact hh.symm) (rowMajorIndex i j))) := by
  have hlen : R.bits.length = rows * cols :=
    (R.compile?_some_iff.mp ⟨P, h⟩).1
  unfold compile? at h
  simp only [dif_pos hlen] at h
  cases hr : R.row.toLaw? with
  | none => simp [hr] at h
  | some μ =>
    cases hc : R.col.toLaw? with
    | none => simp [hr, hc] at h
    | some ν =>
      simp [hr, hc] at h
      subst P
      rw [lookup_encoded]
      rfl

/-- The validated packet uses exactly the supplied numerator/denominator
arrays and table bits; validation does not substitute another law. -/
theorem RawPacket.compiled_fields {rows cols : ℕ}
    (R : RawPacket rows cols) (P : Packet rows cols)
    (h : R.compile? = some P) :
    P.table.bits = R.bits ∧
    (∀ i, P.rowLaw.weight i =
      (R.row.numerator i : ℚ) / R.row.denominator i) ∧
    (∀ j, P.colLaw.weight j =
      (R.col.numerator j : ℚ) / R.col.denominator j) := by
  have hlen : R.bits.length = rows * cols :=
    (R.compile?_some_iff.mp ⟨P, h⟩).1
  unfold compile? at h
  simp only [dif_pos hlen] at h
  cases hr : R.row.toLaw? with
  | none => simp [hr] at h
  | some μ =>
    cases hc : R.col.toLaw? with
    | none => simp [hr, hc] at h
    | some ν =>
      simp [hr, hc] at h
      subst P
      exact ⟨rfl,
        fun i => RawLaw.toLaw?_weight R.row μ hr i,
        fun j => RawLaw.toLaw?_weight R.col ν hc j⟩

#print axioms RawLaw.toLaw?_some_iff
#print axioms RawPacket.compile?_some_iff
#print axioms RawPacket.compiled_lookup_encoded
#print axioms RawPacket.compiled_fields

end Paper2.RawRationalPacket
