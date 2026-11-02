import CurrentAdditive.V38Resource

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

/-! Actual complete recursive labels of selected v39, `appendices/access.tex`.
The mathematics is unchanged from v38. No product carrier is enumerated by
the generators. The exact two-tag and 512-ticket choices are V38OneStep. -/

namespace CurrentAdditive.V39RecursiveGenerator

open Paper2 Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open CurrentAdditive.V38OneStep CurrentAdditive.V38Resource

def bitEquiv : Fin 2 ≃ Bool where
  toFun t := decide (t.val = 1)
  invFun b := if b then 1 else 0
  left_inv t := by fin_cases t <;> rfl
  right_inv b := by cases b <;> rfl

def carriers (n p₀ q₁ q₂ s w Q : ℕ) : ℕ → Type × Type
  | 0 => (Fin p₀ → Bool, Fin p₀)
  | k + 1 =>
    (RowLabel q₁ q₂ s w Q (carriers n p₀ q₁ q₂ s w Q k).2,
      ColumnLabel q₁ q₂ s w Q (carriers n p₀ q₁ q₂ s w Q k).1 (Fin n))

abbrev Row (n p₀ q₁ q₂ s w Q k : ℕ) := (carriers n p₀ q₁ q₂ s w Q k).1
abbrev Column (n p₀ q₁ q₂ s w Q k : ℕ) := (carriers n p₀ q₁ q₂ s w Q k).2

noncomputable def carrierFintypes (n p₀ q₁ q₂ s w Q : ℕ) :
    (k : ℕ) → Fintype (Row n p₀ q₁ q₂ s w Q k) ×
      Fintype (Column n p₀ q₁ q₂ s w Q k)
  | 0 => (inferInstanceAs (Fintype (Fin p₀ → Bool)), inferInstanceAs (Fintype (Fin p₀)))
  | k + 1 => by
    letI : Fintype (Row n p₀ q₁ q₂ s w Q k) := (carrierFintypes n p₀ q₁ q₂ s w Q k).1
    letI : Fintype (Column n p₀ q₁ q₂ s w Q k) := (carrierFintypes n p₀ q₁ q₂ s w Q k).2
    exact (inferInstanceAs (Fintype (RowLabel q₁ q₂ s w Q (Column n p₀ q₁ q₂ s w Q k))),
      inferInstanceAs (Fintype (ColumnLabel q₁ q₂ s w Q (Row n p₀ q₁ q₂ s w Q k) (Fin n))))

noncomputable instance rowFintype (n p₀ q₁ q₂ s w Q k : ℕ) :
    Fintype (Row n p₀ q₁ q₂ s w Q k) := (carrierFintypes n p₀ q₁ q₂ s w Q k).1
noncomputable instance columnFintype (n p₀ q₁ q₂ s w Q k : ℕ) :
    Fintype (Column n p₀ q₁ q₂ s w Q k) := (carrierFintypes n p₀ q₁ q₂ s w Q k).2

section Recursion
variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

/-- The lookup seed uses independent bits, then the complete successor
rules alternate row and column generators at every level. -/
def programs : (k : ℕ) → Program (Row n p₀ q₁ q₂ s w Q k) ×
    Program (Column n p₀ q₁ q₂ s w Q k)
  | 0 => (iid (Program.map bitEquiv (Paper2.RecursiveSampling.uniform 2)) p₀,
      Paper2.RecursiveSampling.uniform p₀)
  | k + 1 =>
    (successorRow (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) (Q := Q)
      (programs k).2,
    successorColumn (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) (Q := Q)
      (Paper2.RecursiveSampling.uniform n) (programs k).1)

noncomputable def laws : (k : ℕ) → PositiveRationalLaw (Row n p₀ q₁ q₂ s w Q k) ×
    PositiveRationalLaw (Column n p₀ q₁ q₂ s w Q k)
  | 0 => ((PositiveRationalLaw.uniform Bool).iid p₀,
      PositiveRationalLaw.uniform (Fin p₀))
  | k + 1 =>
    (successorRowLaw (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) (Q := Q)
      (laws k).2,
    successorColumnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) (Q := Q)
      (V := Fin n) (laws k).1
      (by have h := Nat.pos_of_ne_zero (NeZero.ne (s - 3)); omega))

theorem generates_programs (k : ℕ) :
    Generates (programs n p₀ q₁ q₂ s w Q k).1 (laws n p₀ q₁ q₂ s w Q k).1.toFiniteLaw ∧
    Generates (programs n p₀ q₁ q₂ s w Q k).2 (laws n p₀ q₁ q₂ s w Q k).2.toFiniteLaw := by
  induction k with
  | zero =>
    exact ⟨generates_rational_iid (generates_uniform_equiv 2 bitEquiv) p₀,
      generates_uniform p₀⟩
  | succ k ih =>
    exact ⟨generates_successorRow ih.2, generates_successorColumn (generates_uniform n) ih.1⟩

/-- The literal ordered independent sample at level k. Repeated labels
remain distinct sample positions. The zero-level sample is included. -/
def sampleProgram (k m : ℕ) :
    Program ((Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) :=
  prod (iid (programs n p₀ q₁ q₂ s w Q k).1 m)
    (iid (programs n p₀ q₁ q₂ s w Q k).2 m)

noncomputable def sampleLaw (k m : ℕ) :
    PositiveRationalLaw ((Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) :=
  ((laws n p₀ q₁ q₂ s w Q k).1.iid m).prod
    ((laws n p₀ q₁ q₂ s w Q k).2.iid m)

theorem generates_sampleProgram (k m : ℕ) :
    Generates (sampleProgram n p₀ q₁ q₂ s w Q k m)
      (sampleLaw n p₀ q₁ q₂ s w Q k m).toFiniteLaw :=
  generates_rational_prod (generates_rational_iid (generates_programs n p₀ q₁ q₂ s w Q k).1 m)
    (generates_rational_iid (generates_programs n p₀ q₁ q₂ s w Q k).2 m)

end Recursion

section Draws
variable {X Y : Type*} {n q₁ q₂ s w Q : ℕ}

theorem draws_tagged_le [NeZero q₂] (hs : 1 ≤ s) (p : Program Y) :
    (tagged (q₁ := q₁) (q₂ := q₂) (s := s) p).maxDraws ≤
      1 + s + ((s + 1) + s * (q₁ + s + 1)) * p.maxDraws := by
  have hr := Paper2.RecursiveSampling.maxDraws_raw_le
    (q₁ := q₁) (q₂ := q₂) (s := s) p
  have ho := Paper2.RecursiveSampling.maxDraws_outer_le
    (q₁ := q₁) (q₂ := q₂) (s := s) p
  have hm : 1 + (q₁ + s + 1) * p.maxDraws ≤
      s * (1 + (q₁ + s + 1) * p.maxDraws) := Nat.le_mul_of_pos_left _ (by omega)
  change 1 + Finset.univ.sup _ ≤ _
  have hb : Finset.univ.sup (fun t : Fin 256 =>
      (if t.val < 255 then Program.map Sum.inl (Paper2.RecursiveSampling.raw
          (q₁ := q₁) (q₂ := q₂) (s := s) p)
       else Program.map Sum.inr (Paper2.RecursiveSampling.outer
          (q₁ := q₁) (q₂ := q₂) (s := s) p)).maxDraws) ≤
        s + ((s + 1) + s * (q₁ + s + 1)) * p.maxDraws := by
    apply Finset.sup_le
    intro t ht
    split_ifs <;> rw [Program.maxDraws_map] <;> nlinarith
  simpa only [← Nat.add_assoc] using Nat.add_le_add_left hb 1

theorem draws_rawRows_le [NeZero n] [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] (p : Program X) :
    (rawRows (q₁ := q₁) (q₂ := q₂) (s := s)
      (Paper2.RecursiveSampling.uniform n) p).maxDraws ≤
      3 + q₂ * (1 + p.maxDraws) := by
  rw [rawRows, Program.maxDraws_map]
  apply Paper2.RecursiveSampling.maxDraws_rows_le
  · exact (maxDraws_prod_le _ _).trans (by
      simp only [Paper2.RecursiveSampling.uniform, Program.maxDraws_uniform]; omega)
  · exact (maxDraws_prod_le _ _).trans (by
      simp only [Paper2.RecursiveSampling.uniform, Program.maxDraws_uniform]; omega)

theorem draws_successorRow_le [NeZero q₂] [NeZero w]
    (hs : 1 ≤ s) (p : Program Y) :
    (successorRow (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) (Q := Q) p).maxDraws ≤
      Q * (2 + s + ((s + 1) + s * (q₁ + s + 1)) * p.maxDraws) := by
  apply (maxDraws_iid_le _ _).trans
  apply Nat.mul_le_mul_left
  have h := maxDraws_prod_le (Paper2.RecursiveSampling.uniform w)
    (tagged (q₁ := q₁) (q₂ := q₂) (s := s) p)
  simp only [Paper2.RecursiveSampling.uniform, Program.maxDraws_uniform] at h
  have h := h.trans (Nat.add_le_add_left (draws_tagged_le (q₁ := q₁) hs p) 1)
  simpa only [Paper2.RecursiveSampling.uniform, Program.maxDraws_uniform,
    ← Nat.add_assoc] using h

theorem draws_successorColumn_le [NeZero n] [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero Q] (p : Program X) :
    (successorColumn (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) (Q := Q)
      (Paper2.RecursiveSampling.uniform n) p).maxDraws ≤
      1 + w * (3 + q₂ * (1 + p.maxDraws)) := by
  exact (maxDraws_prod_le _ _).trans (by
    simpa only [Paper2.RecursiveSampling.uniform, Program.maxDraws_uniform] using
      Nat.add_le_add_left ((maxDraws_iid_le _ w).trans
        (Nat.mul_le_mul_left w (draws_rawRows_le p))) 1)

/-- A single explicit polynomial multiplier covers either complete label.
The base-column factor becomes 2s²+1 when q₁=s-2. -/
def drawFactor (q₁ q₂ s w Q : ℕ) : ℕ :=
  max (Q * (2 + s + ((s + 1) + s * (q₁ + s + 1))))
    (1 + w * (3 + 2 * q₂))

def drawBudget (p₀ q₁ q₂ s w Q k : ℕ) : ℕ :=
  drawFactor q₁ q₂ s w Q ^ k * (p₀ + 1)

theorem drawBudget_pos (p₀ q₁ q₂ s w Q k : ℕ) :
    0 < drawBudget p₀ q₁ q₂ s w Q k := by
  have hf : 0 < drawFactor q₁ q₂ s w Q := by
    unfold drawFactor
    exact lt_of_lt_of_le (by omega : 0 < 1 + w * (3 + 2 * q₂)) (Nat.le_max_right _ _)
  exact Nat.mul_pos (pow_pos hf _) (by omega)

end Draws

section Bounds
variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

theorem draws_programs_le (k : ℕ) :
    (programs n p₀ q₁ q₂ s w Q k).1.maxDraws ≤ drawBudget p₀ q₁ q₂ s w Q k ∧
    (programs n p₀ q₁ q₂ s w Q k).2.maxDraws ≤ drawBudget p₀ q₁ q₂ s w Q k := by
  induction k with
  | zero =>
    constructor
    · exact (maxDraws_iid_le _ p₀).trans (by
        simp only [Program.maxDraws_map, Paper2.RecursiveSampling.uniform,
          Program.maxDraws_uniform, drawBudget, pow_zero, one_mul]; omega)
    · change (Paper2.RecursiveSampling.uniform p₀).maxDraws ≤ _
      simp only [Paper2.RecursiveSampling.uniform, Program.maxDraws_uniform,
        drawBudget, pow_zero, one_mul]; omega
  | succ k ih =>
    have hpos := drawBudget_pos p₀ q₁ q₂ s w Q k
    have hs : 1 ≤ s := Nat.pos_of_ne_zero (NeZero.ne s)
    have hrec : drawBudget p₀ q₁ q₂ s w Q (k + 1) =
        drawFactor q₁ q₂ s w Q * drawBudget p₀ q₁ q₂ s w Q k := by
      simp only [drawBudget, pow_succ]; ring
    constructor
    · apply (draws_successorRow_le hs (programs n p₀ q₁ q₂ s w Q k).2).trans
      rw [hrec]
      have hfac := Nat.le_max_left
        (Q * (2 + s + ((s + 1) + s * (q₁ + s + 1)))) (1 + w * (3 + 2 * q₂))
      change _ ≤ drawFactor q₁ q₂ s w Q at hfac
      have hc := Nat.mul_le_mul_right (drawBudget p₀ q₁ q₂ s w Q k) hfac
      nlinarith [Nat.mul_le_mul_left (2 + s) hpos,
        Nat.mul_le_mul_left (Q * ((s + 1) + s * (q₁ + s + 1))) ih.2]
    · apply (draws_successorColumn_le (programs n p₀ q₁ q₂ s w Q k).1).trans
      rw [hrec]
      have hfac := Nat.le_max_right
        (Q * (2 + s + ((s + 1) + s * (q₁ + s + 1)))) (1 + w * (3 + 2 * q₂))
      change _ ≤ drawFactor q₁ q₂ s w Q at hfac
      have hc := Nat.mul_le_mul_right (drawBudget p₀ q₁ q₂ s w Q k) hfac
      nlinarith [Nat.mul_le_mul_left (w * q₂) ih.1,
        Nat.mul_le_mul_left (w * (3 + q₂)) hpos]

def sampleDrawBudget (k m : ℕ) : ℕ := max 1 (2 * m * drawBudget p₀ q₁ q₂ s w Q k)

theorem draws_sampleProgram_le (k m : ℕ) :
    (sampleProgram n p₀ q₁ q₂ s w Q k m).maxDraws ≤ sampleDrawBudget p₀ q₁ q₂ s w Q k m := by
  have hr := (maxDraws_iid_le (programs n p₀ q₁ q₂ s w Q k).1 m).trans
    (Nat.mul_le_mul_left m (draws_programs_le n p₀ q₁ q₂ s w Q k).1)
  have hc := (maxDraws_iid_le (programs n p₀ q₁ q₂ s w Q k).2 m).trans
    (Nat.mul_le_mul_left m (draws_programs_le n p₀ q₁ q₂ s w Q k).2)
  have hb := (maxDraws_prod_le _ _).trans (Nat.add_le_add hr hc)
  apply hb.trans
  calc
    _ = 2 * m * drawBudget p₀ q₁ q₂ s w Q k := by ring
    _ ≤ sampleDrawBudget p₀ q₁ q₂ s w Q k m := Nat.le_max_right _ _

end Bounds

end CurrentAdditive.V39RecursiveGenerator
