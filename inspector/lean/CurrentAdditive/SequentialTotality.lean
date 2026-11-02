import CurrentAdditive.SequentialCode

/-!
Toward totality of the executable support-compression constructor. This file
is separate from the frozen `SequentialCode.lean` review bytes.

The first argument gives a small *integer* dependence for any overfull
zero--one feature matrix by a finite pigeonhole count. It avoids assuming an
output certificate and gives coefficient magnitude at most `(n+1)^n` for
`n` rows and `n+1` columns. Connecting this existence theorem to the exact
Gauss--Jordan implementation and its polynomial runtime is separate work.
-/

namespace CurrentAdditive.SequentialTotality

open Finset

private theorem image_coordinate_bound (n : Nat)
    (A : Fin n → Fin (n + 1) → Nat)
    (h01 : ∀ i j, A i j ≤ 1)
    (x : Fin (n + 1) → Fin ((n + 1) ^ n + 1)) (i : Fin n) :
    ∑ j : Fin (n + 1), (x j).val * A i j ≤
      (n + 1) * ((n + 1) ^ n) := by
  let B := (n + 1) ^ n
  calc
    ∑ j : Fin (n + 1), (x j).val * A i j ≤
        ∑ _j : Fin (n + 1), B := by
          apply Finset.sum_le_sum
          intro j _
          have hx : (x j).val ≤ B := by have := (x j).isLt; omega
          have ha := h01 i j
          have hmul : (x j).val * A i j ≤ (x j).val := by
            simpa using Nat.mul_le_mul_left (x j).val ha
          omega
    _ = (n + 1) * B := by simp [B]

private def image (n : Nat) (A : Fin n → Fin (n + 1) → Nat)
    (h01 : ∀ i j, A i j ≤ 1)
    (x : Fin (n + 1) → Fin ((n + 1) ^ n + 1)) :
    Fin n → Fin ((n + 1) * ((n + 1) ^ n) + 1) :=
  fun i => ⟨∑ j : Fin (n + 1), (x j).val * A i j,
    by have h := image_coordinate_bound n A h01 x i; omega⟩

private theorem pigeonhole_bound (n : Nat) :
    ((n + 1) * ((n + 1) ^ n) + 1) ^ n <
      (((n + 1) ^ n + 1) ^ (n + 1)) := by
  let k := n + 1
  let B := k ^ n
  have hstep : k * B + 1 ≤ k * (B + 1) := by
    have hk : 1 ≤ k := by dsimp [k]; omega
    calc
      k * B + 1 ≤ k * B + k := Nat.add_le_add_left hk _
      _ = k * (B + 1) := by ring
  have hpositive : 0 < (B + 1) ^ n := pow_pos (by omega) _
  calc
    (k * B + 1) ^ n ≤ (k * (B + 1)) ^ n := Nat.pow_le_pow_left hstep n
    _ = B * (B + 1) ^ n := by simp [B, mul_pow]
    _ < (B + 1) ^ (n + 1) := by
      rw [pow_succ]
      simpa only [Nat.succ_eq_add_one, mul_comm] using
        (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self B) hpositive)

/-- Finite zero--one columns in excess of row count admit an integer
dependence with polynomial *coefficient bit length*. This is an existence
theorem; the pigeonhole proof alone is not a polynomial-time finder. -/
theorem exists_small_integer_dependence (n : Nat)
    (A : Fin n → Fin (n + 1) → Nat)
    (h01 : ∀ i j, A i j ≤ 1) :
    ∃ z : Fin (n + 1) → ℤ,
      (∃ j, z j ≠ 0) ∧
      (∀ i : Fin n, ∑ j : Fin (n + 1), z j * (A i j : ℤ) = 0) ∧
      (∀ j, -( ((n + 1) ^ n : Nat) : ℤ) ≤ z j ∧
        z j ≤ ((n + 1) ^ n : Nat)) := by
  let f := image n A h01
  have hcard :
      Fintype.card (Fin (n + 1) → Fin ((n + 1) ^ n + 1)) >
      Fintype.card (Fin n → Fin ((n + 1) * ((n + 1) ^ n) + 1)) := by
    simpa using pigeonhole_bound n
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have hle := Fintype.card_le_of_injective f hinj
    omega
  simp only [Function.Injective] at hnotinj
  push Not at hnotinj
  obtain ⟨x, y, hxy, hne⟩ := hnotinj
  let z : Fin (n + 1) → ℤ :=
    fun j => ((x j).val : ℤ) - ((y j).val : ℤ)
  have hznonzero : ∃ j, z j ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext j
    have hz := h j
    dsimp [z] at hz
    have hval : (x j).val = (y j).val := by omega
    exact Fin.ext hval
  refine ⟨z, hznonzero, ?_, ?_⟩
  · intro i
    have hi := congrArg (fun g => (g i).val) hxy
    dsimp [f, image] at hi
    have hint :
        (∑ j : Fin (n + 1), ((x j).val : ℤ) * (A i j : ℤ)) =
        ∑ j : Fin (n + 1), ((y j).val : ℤ) * (A i j : ℤ) := by
      exact_mod_cast hi
    dsimp [z]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hint
  · intro j
    have hx : (x j).val ≤ (n + 1) ^ n := by have := (x j).isLt; omega
    have hy : (y j).val ≤ (n + 1) ^ n := by have := (y j).isLt; omega
    have hx' : ((x j).val : ℤ) ≤ (((n + 1) ^ n : Nat) : ℤ) := by exact_mod_cast hx
    have hy' : ((y j).val : ℤ) ≤ (((n + 1) ^ n : Nat) : ℤ) := by exact_mod_cast hy
    have hBcast : (((n + 1) ^ n : Nat) : ℤ) = ((n : ℤ) + 1) ^ n := by
      norm_num
    rw [hBcast] at hx' hy'
    dsimp [z]
    constructor <;> omega

#print axioms exists_small_integer_dependence

/-- A typed matrix model for proving the executable pivot operations correct. -/
def rowDot {m k : Nat} (A : Fin m → Fin k → ℚ)
    (x : Fin k → ℚ) (i : Fin m) : ℚ :=
  ∑ j, A i j * x j

def clearTyped {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) : Fin m → Fin k → ℚ :=
  fun i j =>
    if i = r then A r j / A r c
    else A i j - (A i c / A r c) * A r j

theorem rowDot_clearTyped {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) (x : Fin k → ℚ) (i : Fin m) :
    rowDot (clearTyped A r c) x i =
      if i = r then rowDot A x r / A r c
      else rowDot A x i - (A i c / A r c) * rowDot A x r := by
  by_cases hir : i = r
  · subst i
    simp only [rowDot, clearTyped, ↓reduceIte]
    calc
      ∑ j, A r j / A r c * x j =
          ∑ j, (A r j * x j) / A r c := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j, A r j * x j) / A r c := by rw [Finset.sum_div]
  · simp only [rowDot, clearTyped, hir, ↓reduceIte]
    calc
      ∑ j, (A i j - A i c / A r c * A r j) * x j =
          ∑ j, (A i j * x j - (A i c / A r c) * (A r j * x j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j, A i j * x j) -
          (A i c / A r c) * (∑ j, A r j * x j) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Normalizing one nonzero pivot row and clearing its column leaves the
nullspace unchanged. This is the algebraic invariant required by the array
`clearPivot` implementation. -/
theorem kernel_clearTyped_iff {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) (hp : A r c ≠ 0) (x : Fin k → ℚ) :
    (∀ i, rowDot (clearTyped A r c) x i = 0) ↔
      (∀ i, rowDot A x i = 0) := by
  constructor
  · intro h
    have hr' := h r
    rw [rowDot_clearTyped] at hr'
    simp only [↓reduceIte, div_eq_zero_iff, hp, or_false] at hr'
    intro i
    by_cases hir : i = r
    · simpa [hir] using hr'
    · have hi := h i
      rw [rowDot_clearTyped] at hi
      simp only [hir, ↓reduceIte, hr', mul_zero, sub_zero] at hi
      exact hi
  · intro h i
    rw [rowDot_clearTyped]
    by_cases hir : i = r <;> simp [hir, h]

def swapTyped {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r s : Fin m) : Fin m → Fin k → ℚ :=
  fun i => A (Equiv.swap r s i)

/-- Swapping two rows also preserves the nullspace. -/
theorem kernel_swapTyped_iff {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r s : Fin m) (x : Fin k → ℚ) :
    (∀ i, rowDot (swapTyped A r s) x i = 0) ↔
      (∀ i, rowDot A x i = 0) := by
  constructor
  · intro h i
    have hi := h (Equiv.swap r s i)
    simpa [rowDot, swapTyped, Equiv.swap_apply_self] using hi
  · intro h i
    simpa [rowDot, swapTyped] using h (Equiv.swap r s i)

#print axioms kernel_clearTyped_iff
#print axioms kernel_swapTyped_iff

def pivotTyped {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r : Nat) (c : Fin k) : Option (Fin m) :=
  (List.finRange m).find? (fun i => decide (r ≤ i.val ∧ A i c ≠ 0))

theorem pivotTyped_spec {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r : Nat) (c : Fin k) (i : Fin m)
    (h : pivotTyped A r c = some i) : r ≤ i.val ∧ A i c ≠ 0 := by
  have hp := List.find?_some h
  simpa [pivotTyped] using hp

theorem pivotTyped_none {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r : Nat) (c : Fin k) (h : pivotTyped A r c = none) :
    ∀ i : Fin m, r ≤ i.val → A i c = 0 := by
  intro i hi
  have hf := List.find?_eq_none.mp h i (List.mem_finRange i)
  simpa [hi] using hf

def BelowZero {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c : Nat) : Prop :=
  ∀ (i : Fin m) (j : Fin k), r ≤ i.val → j.val < c → A i j = 0

theorem belowZero_advance_no_pivot {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r c : Nat) (hc : c < k)
    (hbelow : BelowZero A r c)
    (hnone : pivotTyped A r ⟨c, hc⟩ = none) :
    BelowZero A r (c + 1) := by
  intro i j hi hj
  by_cases hjo : j.val < c
  · exact hbelow i j hi hjo
  · have heq : j = (⟨c, hc⟩ : Fin k) := by
      apply Fin.ext
      change j.val = c
      omega
    subst j
    exact pivotTyped_none A r ⟨c, hc⟩ hnone i hi

theorem belowZero_swap {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c : Nat) (hr : r < m) (s : Fin m)
    (hs : r ≤ s.val) (hbelow : BelowZero A r c) :
    BelowZero (swapTyped A ⟨r, hr⟩ s) r c := by
  intro i j hi hj
  have hactive : r ≤ (Equiv.swap ⟨r, hr⟩ s i).val := by
    by_cases hir : i = ⟨r, hr⟩
    · subst i
      simp [hs]
    · by_cases his : i = s
      · subst i
        simp
      · simpa [Equiv.swap_apply_of_ne_of_ne hir his] using hi
  exact hbelow _ j hactive hj

theorem swapTyped_left {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c : Nat) (hr : r < m) (s : Fin m)
    (hs : r ≤ s.val) (hbelow : BelowZero A r c) :
    ∀ (i : Fin m) (j : Fin k), j.val < c →
      swapTyped A ⟨r, hr⟩ s i j = A i j := by
  intro i j hj
  by_cases hi : r ≤ i.val
  · have hz1 := (belowZero_swap A r c hr s hs hbelow) i j hi hj
    have hz2 := hbelow i j hi hj
    rw [hz1, hz2]
  · have hir : i ≠ (⟨r, hr⟩ : Fin m) := by
      intro heq
      have := congrArg Fin.val heq
      change i.val = r at this
      omega
    have his : i ≠ s := by
      intro heq
      have := congrArg Fin.val heq
      omega
    simp [swapTyped, Equiv.swap_apply_of_ne_of_ne hir his]

theorem clearTyped_left {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r : Fin m) (c j : Fin k) (hzero : A r j = 0) :
    ∀ i, clearTyped A r c i j = A i j := by
  intro i
  by_cases hir : i = r
  · subst i
    simp [clearTyped, hzero]
  · simp [clearTyped, hir, hzero]

theorem belowZero_clear {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c : Nat) (hr : r < m) (hc : c < k)
    (hbelow : BelowZero A r c)
    (hp : A ⟨r, hr⟩ ⟨c, hc⟩ ≠ 0) :
    BelowZero (clearTyped A ⟨r, hr⟩ ⟨c, hc⟩) (r + 1) (c + 1) := by
  intro i j hi hj
  have hir : i ≠ (⟨r, hr⟩ : Fin m) := by
    intro heq
    have : i.val = r := congrArg Fin.val heq
    omega
  by_cases hjc : j.val < c
  · have hzi := hbelow i j (by omega) hjc
    have hzr := hbelow ⟨r, hr⟩ j (by simp) hjc
    simp [clearTyped, hir, hzi, hzr]
  · have heq : j = (⟨c, hc⟩ : Fin k) := by
      apply Fin.ext
      change j.val = c
      omega
    subst j
    simp only [clearTyped, hir, ↓reduceIte]
    field_simp
    ring

theorem pivotStep_left {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c : Nat) (hr : r < m) (hc : c < k) (s : Fin m)
    (hs : r ≤ s.val) (hbelow : BelowZero A r c) :
    ∀ (i : Fin m) (j : Fin k), j.val < c →
      clearTyped (swapTyped A ⟨r, hr⟩ s) ⟨r, hr⟩ ⟨c, hc⟩ i j = A i j := by
  intro i j hj
  have hsbelow := belowZero_swap A r c hr s hs hbelow
  rw [clearTyped_left _ _ _ j (hsbelow ⟨r, hr⟩ j (by simp) hj) i]
  exact swapTyped_left A r c hr s hs hbelow i j hj

/-- Typed, executable Gauss--Jordan loop with a structurally decreasing
column fuel. This mirrors the finite array routine while making row algebra
amenable to kernel proofs. -/
def echelonTyped {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c fuel : Nat) : (Fin m → Fin k → ℚ) × List (Fin m × Fin k) :=
  match fuel with
  | 0 => (A, [])
  | fuel + 1 =>
    if hr : r < m then
      if hc : c < k then
        let rf : Fin m := ⟨r, hr⟩
        let cf : Fin k := ⟨c, hc⟩
        match pivotTyped A r cf with
        | none => echelonTyped A r (c + 1) fuel
        | some i =>
          let B := swapTyped A rf i
          let C := clearTyped B rf cf
          let (out, pivots) := echelonTyped C (r + 1) (c + 1) fuel
          (out, (rf, cf) :: pivots)
      else (A, [])
    else (A, [])

theorem echelonTyped_kernel_iff {m k : Nat} (A : Fin m → Fin k → ℚ)
    (r c fuel : Nat) (x : Fin k → ℚ) :
    (∀ i, rowDot (echelonTyped A r c fuel).1 x i = 0) ↔
      (∀ i, rowDot A x i = 0) := by
  induction fuel generalizing A r c with
  | zero => rfl
  | succ fuel ih =>
      simp only [echelonTyped]
      split_ifs with hr hc <;> try rfl
      cases hpivot : pivotTyped A r ⟨c, hc⟩ with
      | none =>
          exact ih A r (c + 1)
      | some i =>
          have hp : A i ⟨c, hc⟩ ≠ 0 :=
            (pivotTyped_spec A r ⟨c, hc⟩ i hpivot).2
          have hswap : (swapTyped A ⟨r, hr⟩ i) ⟨r, hr⟩ ⟨c, hc⟩ ≠ 0 := by
            simpa [swapTyped] using hp
          exact (ih _ (r + 1) (c + 1)).trans
            ((kernel_clearTyped_iff _ _ _ hswap x).trans
              (kernel_swapTyped_iff A ⟨r, hr⟩ i x))

/-- The loop scans every column in its fuel range. Rows below the final
active row are zero in all scanned columns, and columns already scanned on
entry are not changed anywhere. -/
theorem echelonTyped_staircase {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r c fuel : Nat)
    (hbound : c + fuel ≤ k) (hbelow : BelowZero A r c) :
    let out := echelonTyped A r c fuel
    BelowZero out.1 (r + out.2.length) (c + fuel) ∧
      (∀ (i : Fin m) (j : Fin k), j.val < c → out.1 i j = A i j) := by
  induction fuel generalizing A r c with
  | zero =>
      simpa [echelonTyped] using
        (show BelowZero A (r + 0) (c + 0) ∧
          (∀ (i : Fin m) (j : Fin k), j.val < c → A i j = A i j) from
          ⟨by simpa using hbelow, by intros; rfl⟩)
  | succ fuel ih =>
      have hc : c < k := by omega
      by_cases hr : r < m
      · cases hp : pivotTyped A r ⟨c, hc⟩ with
        | none =>
            have hb := belowZero_advance_no_pivot A r c hc hbelow hp
            have hrec := ih A r (c + 1) (by omega) hb
            constructor
            · simpa [echelonTyped, hr, hc, hp, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hrec.1
            · intro i j hj
              have hleft := hrec.2 i j (by omega)
              simpa [echelonTyped, hr, hc, hp] using hleft
        | some s =>
            have hs := (pivotTyped_spec A r ⟨c, hc⟩ s hp).1
            let B := swapTyped A ⟨r, hr⟩ s
            let C := clearTyped B ⟨r, hr⟩ ⟨c, hc⟩
            have hbs : BelowZero B r c := belowZero_swap A r c hr s hs hbelow
            have hpnz : B ⟨r, hr⟩ ⟨c, hc⟩ ≠ 0 := by
              simpa [B, swapTyped] using (pivotTyped_spec A r ⟨c, hc⟩ s hp).2
            have hbc : BelowZero C (r + 1) (c + 1) :=
              belowZero_clear B r c hr hc hbs hpnz
            have hrec := ih C (r + 1) (c + 1) (by omega) hbc
            constructor
            · have hst := hrec.1
              simpa [echelonTyped, hr, hc, hp, B, C, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hst
            · intro i j hj
              have hfirst := pivotStep_left A r c hr hc s hs hbelow i j hj
              have hlater := hrec.2 i j (by omega)
              simpa [echelonTyped, hr, hc, hp, B, C] using hlater.trans hfirst
      · constructor
        · intro i j hi _
          have := i.isLt
          simp only [echelonTyped, hr, ↓reduceDIte]
          omega
        · intro i j _
          simp [echelonTyped, hr]

theorem clearTyped_pivot_column {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k)
    (hp : A r c ≠ 0) (i : Fin m) :
    clearTyped A r c i c = if i = r then 1 else 0 := by
  by_cases hir : i = r
  · subst i
    simp [clearTyped, hp]
  · simp only [clearTyped, hir, ↓reduceIte]
    field_simp
    ring

/-- Every recorded pivot column remains a unit column in the final matrix.
Later pivots cannot change it because their active rows have zero there. -/
theorem echelonTyped_pivot_units {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r c fuel : Nat)
    (hbound : c + fuel ≤ k) (hbelow : BelowZero A r c) :
    let out := echelonTyped A r c fuel
    ∀ p ∈ out.2, ∀ i : Fin m,
      out.1 i p.2 = if i = p.1 then 1 else 0 := by
  induction fuel generalizing A r c with
  | zero => simp [echelonTyped]
  | succ fuel ih =>
      have hc : c < k := by omega
      by_cases hr : r < m
      · cases hp : pivotTyped A r ⟨c, hc⟩ with
        | none =>
            have hb := belowZero_advance_no_pivot A r c hc hbelow hp
            have hrec := ih A r (c + 1) (by omega) hb
            simpa [echelonTyped, hr, hc, hp] using hrec
        | some s =>
            have hs := (pivotTyped_spec A r ⟨c, hc⟩ s hp).1
            let B := swapTyped A ⟨r, hr⟩ s
            let C := clearTyped B ⟨r, hr⟩ ⟨c, hc⟩
            have hbs : BelowZero B r c := belowZero_swap A r c hr s hs hbelow
            have hpnz : B ⟨r, hr⟩ ⟨c, hc⟩ ≠ 0 := by
              simpa [B, swapTyped] using (pivotTyped_spec A r ⟨c, hc⟩ s hp).2
            have hbc : BelowZero C (r + 1) (c + 1) :=
              belowZero_clear B r c hr hc hbs hpnz
            have hrec := ih C (r + 1) (c + 1) (by omega) hbc
            have hleft := (echelonTyped_staircase C (r + 1) (c + 1) fuel
              (by omega) hbc).2
            dsimp only
            intro p hmem i
            have hmem' : p = (⟨r, hr⟩, ⟨c, hc⟩) ∨
                p ∈ (echelonTyped C (r + 1) (c + 1) fuel).2 := by
              simpa [echelonTyped, hr, hc, hp, B, C] using hmem
            rcases hmem' with hfirst | hlater
            · subst p
              have hcol := clearTyped_pivot_column B ⟨r, hr⟩ ⟨c, hc⟩ hpnz i
              simpa [echelonTyped, hr, hc, hp, B, C] using
                (hleft i ⟨c, hc⟩ (by simp)).trans hcol
            · simpa [echelonTyped, hr, hc, hp, B, C] using hrec p hlater i
      · simp [echelonTyped, hr]

/-- Pivot rows are consecutive from the starting row, with no gaps. -/
theorem echelonTyped_pivot_rows {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r c fuel : Nat) (hrle : r ≤ m) :
    let ps := (echelonTyped A r c fuel).2
    r + ps.length ≤ m ∧
      (∀ i : Fin m, r ≤ i.val → i.val < r + ps.length →
        ∃ p ∈ ps, p.1 = i) := by
  induction fuel generalizing A r c with
  | zero =>
      simp [echelonTyped, hrle]
  | succ fuel ih =>
      by_cases hr : r < m
      · by_cases hc : c < k
        · cases hp : pivotTyped A r ⟨c, hc⟩ with
          | none =>
              have hrec := ih A r (c + 1) hrle
              simpa [echelonTyped, hr, hc, hp] using hrec
          | some s =>
              let B := swapTyped A ⟨r, hr⟩ s
              let C := clearTyped B ⟨r, hr⟩ ⟨c, hc⟩
              have hrec := ih C (r + 1) (c + 1) (by omega)
              dsimp only
              constructor
              · have hb := hrec.1
                simpa [echelonTyped, hr, hc, hp, B, C,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
              · intro i hi hlo
                by_cases hir : i.val = r
                · refine ⟨(⟨r, hr⟩, ⟨c, hc⟩), ?_, Fin.ext ?_⟩
                  · simp [echelonTyped, hr, hc, hp]
                  · simpa using hir.symm
                · have hlow : r + 1 ≤ i.val := by omega
                  have hhigh : i.val < r + 1 + (echelonTyped C (r + 1) (c + 1) fuel).2.length := by
                    simpa [echelonTyped, hr, hc, hp, B, C,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlo
                  obtain ⟨p, hmem, heq⟩ := hrec.2 i hlow hhigh
                  refine ⟨p, ?_, heq⟩
                  simpa [echelonTyped, hr, hc, hp, B, C] using
                    (Or.inr hmem : p = (⟨r, hr⟩, ⟨c, hc⟩) ∨
                      p ∈ (echelonTyped C (r + 1) (c + 1) fuel).2)
        · simp [echelonTyped, hr, hc, hrle]
      · simp [echelonTyped, hr, hrle]

theorem echelonTyped_pivot_row_lower {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r c fuel : Nat) :
    ∀ p ∈ (echelonTyped A r c fuel).2, r ≤ p.1.val := by
  induction fuel generalizing A r c with
  | zero => simp [echelonTyped]
  | succ fuel ih =>
      by_cases hr : r < m
      · by_cases hc : c < k
        · cases hp : pivotTyped A r ⟨c, hc⟩ with
          | none =>
              simpa [echelonTyped, hr, hc, hp] using ih A r (c + 1)
          | some s =>
              let C := clearTyped (swapTyped A ⟨r, hr⟩ s) ⟨r, hr⟩ ⟨c, hc⟩
              intro p hmem
              have hm : p = (⟨r, hr⟩, ⟨c, hc⟩) ∨
                  p ∈ (echelonTyped C (r + 1) (c + 1) fuel).2 := by
                simpa [echelonTyped, hr, hc, hp, C] using hmem
              rcases hm with hfirst | hlater
              · subst p; simp
              · have := ih C (r + 1) (c + 1) p hlater
                omega
        · simp [echelonTyped, hr, hc]
      · simp [echelonTyped, hr]

theorem echelonTyped_pivot_rows_nodup {m k : Nat}
    (A : Fin m → Fin k → ℚ) (r c fuel : Nat) :
    ((echelonTyped A r c fuel).2.map Prod.fst).Nodup := by
  induction fuel generalizing A r c with
  | zero => simp [echelonTyped]
  | succ fuel ih =>
      by_cases hr : r < m
      · by_cases hc : c < k
        · cases hp : pivotTyped A r ⟨c, hc⟩ with
          | none =>
              simpa [echelonTyped, hr, hc, hp] using ih A r (c + 1)
          | some s =>
              let C := clearTyped (swapTyped A ⟨r, hr⟩ s) ⟨r, hr⟩ ⟨c, hc⟩
              have hrec := ih C (r + 1) (c + 1)
              have hnot : (⟨r, hr⟩ : Fin m) ∉
                  (echelonTyped C (r + 1) (c + 1) fuel).2.map Prod.fst := by
                intro hmem
                obtain ⟨p, hp, hfirst⟩ := List.mem_map.mp hmem
                have hlower := echelonTyped_pivot_row_lower C
                  (r + 1) (c + 1) fuel p hp
                have heq : p.1.val = r := by
                  have := congrArg Fin.val hfirst
                  simpa using this
                omega
              simpa [echelonTyped, hr, hc, hp, C] using
                (List.nodup_cons.mpr ⟨hnot, hrec⟩)
        · simp [echelonTyped, hr, hc]
      · simp [echelonTyped, hr]

/-- More columns than rows leaves at least one column outside the pivot list.
The witness is finite and can be found by scanning columns in order. -/
theorem echelonTyped_free_column {m k : Nat}
    (A : Fin m → Fin k → ℚ) (hkm : m < k) :
    ∃ f : Fin k, f ∉ (echelonTyped A 0 0 k).2.map Prod.snd := by
  let ps := (echelonTyped A 0 0 k).2
  have hlen : ps.length ≤ m := by
    have h := (echelonTyped_pivot_rows A 0 0 k (by omega)).1
    simpa [ps] using h
  by_contra! hn
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ (ps.map Prod.snd).toFinset := by
    intro f _
    simpa using hn f
  have hc := Finset.card_le_card hsub
  have hl := List.toFinset_card_le (ps.map Prod.snd)
  simp only [Finset.card_univ, Fintype.card_fin, List.length_map] at hc hl
  omega

/-- A finite back-substitution formula. Summing over pivot pairs retains
their indexing; the row-distinctness theorem will control cancellation. -/
def typedCandidate {m k : Nat} (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) (f : Fin k) : Fin k → ℚ :=
  fun j => (if j = f then 1 else 0) -
    ∑ p ∈ ps.toFinset, if j = p.2 then B p.1 f else 0

theorem rowDot_typedCandidate {m k : Nat} (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) (f : Fin k) (i : Fin m) :
    rowDot B (typedCandidate B ps f) i =
      B i f - ∑ p ∈ ps.toFinset, B i p.2 * B p.1 f := by
  simp only [rowDot, typedCandidate, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp

theorem typedCandidate_reduced_kernel {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f : Fin k) (hfree : f ∉ ps.map Prod.snd)
    (hunit : ∀ p ∈ ps, ∀ i : Fin m,
      B i p.2 = if i = p.1 then 1 else 0)
    (hbelow : ∀ i : Fin m, ps.length ≤ i.val → ∀ j, B i j = 0)
    (hcover : ∀ i : Fin m, i.val < ps.length → ∃ p ∈ ps, p.1 = i)
    (hnodup : (ps.map Prod.fst).Nodup) :
    typedCandidate B ps f f ≠ 0 ∧
      ∀ i, rowDot B (typedCandidate B ps f) i = 0 := by
  have hpsnodup : ps.Nodup := hnodup.of_map
  have hinj := (List.nodup_map_iff_inj_on hpsnodup).mp hnodup
  have hfree' : ∀ p ∈ ps, f ≠ p.2 := by
    intro p hp heq
    apply hfree
    exact List.mem_map.mpr ⟨p, hp, heq.symm⟩
  constructor
  · have hsum : (∑ p ∈ ps.toFinset,
        if f = p.2 then B p.1 f else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hpmem : p ∈ ps := by simpa using hp
      simp [hfree' p hpmem]
    simp [typedCandidate, hsum]
  · intro i
    by_cases hi : ps.length ≤ i.val
    · simp [rowDot, hbelow i hi]
    · obtain ⟨p0, hp0, hp0i⟩ := hcover i (by omega)
      have hp0set : p0 ∈ ps.toFinset := by simpa using hp0
      have hsum : (∑ p ∈ ps.toFinset,
          B i p.2 * B p.1 f) = B i f := by
        calc
          (∑ p ∈ ps.toFinset, B i p.2 * B p.1 f) =
              B i p0.2 * B p0.1 f := by
                apply Finset.sum_eq_single p0
                · intro p hp hne
                  have hpmem : p ∈ ps := by simpa using hp
                  have hrow : i ≠ p.1 := by
                    intro heq
                    have hsame : p = p0 :=
                      hinj p hpmem p0 hp0 (heq.symm.trans hp0i.symm)
                    exact hne hsame
                  simp [hunit p hpmem i, hrow]
                · intro hnot
                  exact False.elim (hnot hp0set)
          _ = B i f := by
            rw [hunit p0 hp0 i]
            simp [hp0i]
      rw [rowDot_typedCandidate, hsum]
      simp

/-- Scan for the first nonpivot column. -/
def typedFree {m k : Nat} (ps : List (Fin m × Fin k)) : Option (Fin k) :=
  (List.finRange k).find? (fun f => decide (f ∉ ps.map Prod.snd))

theorem typedFree_spec {m k : Nat} (ps : List (Fin m × Fin k))
    (f : Fin k) (h : typedFree ps = some f) :
    f ∉ ps.map Prod.snd := by
  have := List.find?_some h
  simpa [typedFree] using this

theorem typedFree_exists {m k : Nat} (ps : List (Fin m × Fin k))
    (h : ∃ f : Fin k, f ∉ ps.map Prod.snd) :
    ∃ f, typedFree ps = some f := by
  obtain ⟨f, hf⟩ := h
  cases ht : typedFree ps with
  | some g => exact ⟨g, rfl⟩
  | none =>
      have hn := List.find?_eq_none.mp ht f (List.mem_finRange f)
      simp [hf] at hn

/-- Fully deterministic typed dependence finder: Gauss--Jordan plus a
first-free-column scan and finite back substitution. -/
def typedDependence {m k : Nat} (A : Fin m → Fin k → ℚ) :
    Option (Fin k → ℚ) :=
  let (B, ps) := echelonTyped A 0 0 k
  (typedFree ps).map (typedCandidate B ps)

theorem typedDependence_total {m k : Nat}
    (A : Fin m → Fin k → ℚ) (hkm : m < k) :
    ∃ x, typedDependence A = some x ∧
      (∃ j : Fin k, x j ≠ 0) ∧
      ∀ i, rowDot A x i = 0 := by
  let B := (echelonTyped A 0 0 k).1
  let ps := (echelonTyped A 0 0 k).2
  obtain ⟨f, hf⟩ := typedFree_exists ps
    (by simpa [ps] using echelonTyped_free_column A hkm)
  have hfree := typedFree_spec ps f hf
  have hbelow : BelowZero A 0 0 := by
    intro i j _ hj
    omega
  have hstair := (echelonTyped_staircase A 0 0 k (by simp) hbelow).1
  have hunit := echelonTyped_pivot_units A 0 0 k (by simp) hbelow
  have hrows := echelonTyped_pivot_rows A 0 0 k (by omega)
  have hnodup := echelonTyped_pivot_rows_nodup A 0 0 k
  have hred : typedCandidate B ps f f ≠ 0 ∧
      ∀ i, rowDot B (typedCandidate B ps f) i = 0 := by
    apply typedCandidate_reduced_kernel B ps f hfree
    · simpa [B, ps] using hunit
    · intro i hi j
      exact hstair i j (by simpa [ps] using hi) (by omega)
    · intro i hi
      have h := hrows.2 i (by omega) (by simpa [ps] using hi)
      simpa [ps] using h
    · simpa [ps] using hnodup
  refine ⟨typedCandidate B ps f, ?_, ⟨f, hred.1⟩, ?_⟩
  · simp [typedDependence, B, ps, hf]
  · exact (echelonTyped_kernel_iff A 0 0 k (typedCandidate B ps f)).mp hred.2

#print axioms echelonTyped_staircase
#print axioms echelonTyped_pivot_units
#print axioms typedDependence_total

#print axioms echelonTyped_kernel_iff

end CurrentAdditive.SequentialTotality
