import Paper2.IndexedMatrices
import Paper2.CappedSamplerBits

/-!
# Square power-of-two padding by repetitions of actual input labels

Frozen source: v12 `sections/06-reduction.tex`, the square-padding paragraphs
after the uniform reduction and at the end of quantitative hardness (U17).
The construction uses explicit remainder maps on finite integer labels. Every
original row and column occurs in the initial block, so the same Boolean table
has exactly the same communication complexity and every supplied protocol
pulls back without any increase in depth. Dimensions are computed from the
input dimensions alone; no colouring, promise, or optimal protocol selects them.

This is the finite construction and size calculation, not a machine-time proof,
the quantitative logarithmic asymptotics, or a complexity-hardness theorem.
-/

namespace Paper2.SquarePadding

open Workspace.Types.CommComplexity Workspace.Types.Protocol

/-- The binary input length for the square output. -/
def exponent (m n : ℕ) : ℕ := Nat.clog 2 (max m n)

/-- The least power of two not smaller than either input dimension. -/
def side (m n : ℕ) : ℕ := 2 ^ exponent m n

theorem side_pos (m n : ℕ) : 0 < side m n := Nat.two_pow_pos _

theorem max_le_side (m n : ℕ) : max m n ≤ side m n :=
  Nat.le_pow_clog (by decide) _

theorem rows_le_side (m n : ℕ) : m ≤ side m n :=
  (le_max_left m n).trans (max_le_side m n)

theorem cols_le_side (m n : ℕ) : n ≤ side m n :=
  (le_max_right m n).trans (max_le_side m n)

/-- Minimality is an inequality about the actual computed exponent. -/
theorem exponent_le_iff (m n e : ℕ) :
    exponent m n ≤ e ↔ max m n ≤ 2 ^ e :=
  Nat.clog_le_iff_le_pow (by decide)

theorem side_minimal (m n e : ℕ) (hm : m ≤ 2 ^ e) (hn : n ≤ 2 ^ e) :
    side m n ≤ 2 ^ e := by
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  exact (exponent_le_iff m n e).2 (max_le hm hn)

/-- A positive dimension rounds up by a factor strictly less than two,
including the singleton case. -/
theorem side_lt_twice_max {m n : ℕ} (hmn : 0 < max m n) :
    side m n < 2 * max m n := by
  by_cases hone : max m n = 1
  · simp [side, exponent, hone]
  · have hlarge : 1 < max m n := by omega
    have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hlarge
    have hlog := Nat.clog_pos (by decide : 1 < 2) hlarge
    have he : Nat.clog 2 (max m n) = (Nat.clog 2 (max m n)).pred + 1 := by
      simp only [Nat.pred_eq_sub_one]
      omega
    unfold side exponent
    rw [he, pow_succ]
    omega

/-- The output side has exactly this binary exponent, including exponent zero. -/
@[simp] theorem clog_side (m n : ℕ) : Nat.clog 2 (side m n) = exponent m n :=
  Nat.clog_pow 2 _ (by decide)

/-- Repeat the original labels cyclically. Positivity rules out an empty
source alphabet, and the computation is integer remainder. -/
def repeatIndex {d : ℕ} (hd : 0 < d) {s : ℕ} (i : Fin s) : Fin d :=
  ⟨i.val % d, Nat.mod_lt _ hd⟩

/-- Every original label is retained at its original integer index. -/
@[simp] theorem repeatIndex_castLE {d s : ℕ} (hd : 0 < d) (hds : d ≤ s)
    (i : Fin d) : repeatIndex hd (Fin.castLE hds i) = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem repeatIndex_surjective {d s : ℕ} (hd : 0 < d) (hds : d ≤ s) :
    Function.Surjective (repeatIndex hd : Fin s → Fin d) := by
  intro i
  exact ⟨Fin.castLE hds i, repeatIndex_castLE hd hds i⟩

def rowIndex {m n : ℕ} (hm : 0 < m) : Fin (side m n) → Fin m := repeatIndex hm

def colIndex {m n : ℕ} (hn : 0 < n) : Fin (side m n) → Fin n := repeatIndex hn

theorem rowIndex_surjective {m n : ℕ} (hm : 0 < m) :
    Function.Surjective (rowIndex (n := n) hm) :=
  repeatIndex_surjective hm (rows_le_side m n)

theorem colIndex_surjective {m n : ℕ} (hn : 0 < n) :
    Function.Surjective (colIndex (m := m) hn) :=
  repeatIndex_surjective hn (cols_le_side m n)

/-- The actual square table; the only new entries repeat old entries. -/
def matrix {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (F : Fin m → Fin n → Bool) :
    Fin (side m n) → Fin (side m n) → Bool :=
  fun i j => F (rowIndex hm i) (colIndex hn j)

@[simp] theorem matrix_apply {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (F : Fin m → Fin n → Bool) (i j : Fin (side m n)) :
    matrix hm hn F i j = F (repeatIndex hm i) (repeatIndex hn j) := rfl

/-- The top-left original rectangle is literally unchanged. -/
@[simp] theorem matrix_original_entry {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (F : Fin m → Fin n → Bool) (i : Fin m) (j : Fin n) :
    matrix hm hn F (Fin.castLE (rows_le_side m n) i)
      (Fin.castLE (cols_le_side m n) j) = F i j := by
  simp only [matrix_apply, repeatIndex_castLE]

/-- Exact preservation, not just an upper bound on the padded table. -/
theorem D_matrix {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (F : Fin m → Fin n → Bool) : D (matrix hm hn F) = D F :=
  pullback_D_eq_of_surjective F (rowIndex hm) (colIndex hn)
    (rowIndex_surjective hm) (colIndex_surjective hn)

/-- A concrete supplied protocol is transformed, preserving its exact depth.
This applies to both universal and YES protocols on every generated table. -/
def protocol {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (P : Protocol (Fin m) (Fin n) Bool) :
    Protocol (Fin (side m n)) (Fin (side m n)) Bool :=
  Workspace.UpperBound.Protocol.comap (rowIndex hm) (colIndex hn) P

@[simp] theorem protocol_cost {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Protocol (Fin m) (Fin n) Bool) : (protocol hm hn P).cost = P.cost :=
  Workspace.UpperBound.Protocol.comap_cost _ _ _

@[simp] theorem protocol_eval {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Protocol (Fin m) (Fin n) Bool) (i j : Fin (side m n)) :
    (protocol hm hn P).eval i j = P.eval (rowIndex hm i) (colIndex hn j) :=
  Workspace.UpperBound.Protocol.comap_eval _ _ _ _ _

theorem protocol_computes {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (F : Fin m → Fin n → Bool) (P : Protocol (Fin m) (Fin n) Bool)
    (hP : P.Computes F) : (protocol hm hn P).Computes (matrix hm hn F) := by
  intro i j
  rw [protocol_eval]
  exact hP _ _

theorem upper_bound {m n c : ℕ} (hm : 0 < m) (hn : 0 < n)
    (F : Fin m → Fin n → Bool) (hF : D F ≤ c) : D (matrix hm hn F) ≤ c := by
  rwa [D_matrix]

theorem exact_gap {m n B k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (F : Fin m → Fin n → Bool) (hF : D F = B + k) : D (matrix hm hn F) = B + k := by
  rwa [D_matrix]

/-- Exact output entry count, depending only on the original dimensions. -/
def entries (m n : ℕ) : ℕ := side m n * side m n

theorem card_entries (m n : ℕ) :
    Fintype.card (Fin (side m n) × Fin (side m n)) = entries m n := by
  simp [entries]

theorem entries_pow (m n : ℕ) : entries m n = 2 ^ (2 * exponent m n) := by
  simp only [entries, side, ← pow_add]
  congr 1
  omega

theorem entries_lt_four_max_sq {m n : ℕ} (hmn : 0 < max m n) :
    entries m n < 4 * (max m n) ^ 2 := by
  have hs := side_lt_twice_max hmn
  have hp := side_pos m n
  unfold entries
  nlinarith

/-- A rectangular input with `m*n` entries becomes a square with fewer than
`4*(m*n)^2` entries. This is a size bound, not a runtime certificate. -/
theorem entries_lt_four_input_sq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    entries m n < 4 * (m * n) ^ 2 := by
  have hmax : max m n ≤ m * n := by
    apply max_le <;> nlinarith
  have hpos : 0 < max m n := hm.trans_le (le_max_left m n)
  have hs := entries_lt_four_max_sq hpos
  have hsq := Nat.pow_le_pow_left hmax 2
  omega

/-- If the aspect ratio is at most `c`, the square uses less than `4*c`
times as many entries as the rectangle. This finite bound isolates the size
fact needed for the later logarithmic accounting. -/
theorem entries_lt_four_ratio {m n c : ℕ} (hn : 0 < n)
    (hmn : m ≤ n) (hratio : n ≤ c * m) :
    entries m n < 4 * c * (m * n) := by
  have hmax : max m n = n := max_eq_right hmn
  have hpos : 0 < max m n := by rwa [hmax]
  have hs := entries_lt_four_max_sq hpos
  rw [hmax] at hs
  have hmul := Nat.mul_le_mul_right n hratio
  nlinarith

/-- Explicit little-endian binary labels for the same output table. -/
def bitMatrix {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (F : Fin m → Fin n → Bool) :
    (Fin (exponent m n) → Bool) → (Fin (exponent m n) → Bool) → Bool :=
  fun x y => matrix hm hn F (CappedSampler.bitsTicketEquiv _ x)
    (CappedSampler.bitsTicketEquiv _ y)

theorem D_bitMatrix {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (F : Fin m → Fin n → Bool) : D (bitMatrix hm hn F) = D F := by
  calc
    _ = D (matrix hm hn F) :=
      pullback_D_eq_of_surjective (matrix hm hn F)
        (CappedSampler.bitsTicketEquiv _) (CappedSampler.bitsTicketEquiv _)
        (CappedSampler.bitsTicketEquiv _).surjective (CappedSampler.bitsTicketEquiv _).surjective
    _ = _ := D_matrix hm hn F

end Paper2.SquarePadding

#print axioms Paper2.SquarePadding.D_matrix
#print axioms Paper2.SquarePadding.protocol_computes
#print axioms Paper2.SquarePadding.entries_lt_four_input_sq
#print axioms Paper2.SquarePadding.D_bitMatrix
