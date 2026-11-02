import EthInapproximability.CurrentPaper.EntryRunsRaw

/-!
# Uniform polynomial bounds: the framework and the arithmetic leaf clocks

Lane owner:b-entry-clock-1 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic.

`PolyIn U f` says: ONE pair of constants `K D` (independent of the index) bounds
`f i ≤ K * (U i + 1)^D` for EVERY index `i`. The closure lemmas keep the constants
uniform, so a `PolyIn` statement over a type of instances is a genuinely uniform
(absolute-constant) polynomial bound.

Leaf lemmas: the admitted clock functions `MatrixUnaryDivision.totalTime`,
`MatrixWeightedPower.iterateBound` / `powerBound`,
`MatrixStage4LowDigitStream.timeBudget`, `MatrixStage4AlignmentStream.budget`
are majorized by explicit polynomials in their arguments (and, for the power
clock, the size of the computed power).
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

/-- A uniform polynomial bound in the size `U`. -/
def PolyIn {ι : Type*} (U : ι → ℕ) (f : ι → ℕ) : Prop :=
  ∃ K D : ℕ, ∀ i, f i ≤ K * (U i + 1) ^ D

namespace PolyIn

variable {ι : Type*} {U : ι → ℕ}

theorem mono {f g : ι → ℕ} (h : ∀ i, f i ≤ g i) (hg : PolyIn U g) : PolyIn U f := by
  obtain ⟨K, D, hK⟩ := hg
  exact ⟨K, D, fun i => (h i).trans (hK i)⟩

theorem const (c : ℕ) : PolyIn U (fun _ => c) := ⟨c, 0, fun i => by simp⟩

theorem self : PolyIn U U := ⟨1, 1, fun i => by simp⟩

theorem of_le {f : ι → ℕ} (h : ∀ i, f i ≤ U i) : PolyIn U f := mono h self

theorem add {f g : ι → ℕ} (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => f i + g i) := by
  obtain ⟨K1, D1, h1⟩ := hf
  obtain ⟨K2, D2, h2⟩ := hg
  refine ⟨K1 + K2, D1 + D2, fun i => ?_⟩
  have hX : 1 ≤ U i + 1 := Nat.le_add_left 1 (U i)
  have e1 : (U i + 1) ^ D1 ≤ (U i + 1) ^ (D1 + D2) :=
    Nat.pow_le_pow_right hX (Nat.le_add_right _ _)
  have e2 : (U i + 1) ^ D2 ≤ (U i + 1) ^ (D1 + D2) :=
    Nat.pow_le_pow_right hX (Nat.le_add_left _ _)
  calc f i + g i ≤ K1 * (U i + 1) ^ D1 + K2 * (U i + 1) ^ D2 := Nat.add_le_add (h1 i) (h2 i)
    _ ≤ K1 * (U i + 1) ^ (D1 + D2) + K2 * (U i + 1) ^ (D1 + D2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (K1 + K2) * (U i + 1) ^ (D1 + D2) := by ring

theorem mul {f g : ι → ℕ} (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => f i * g i) := by
  obtain ⟨K1, D1, h1⟩ := hf
  obtain ⟨K2, D2, h2⟩ := hg
  refine ⟨K1 * K2, D1 + D2, fun i => ?_⟩
  calc f i * g i ≤ (K1 * (U i + 1) ^ D1) * (K2 * (U i + 1) ^ D2) := Nat.mul_le_mul (h1 i) (h2 i)
    _ = K1 * K2 * (U i + 1) ^ (D1 + D2) := by ring

theorem pow {f : ι → ℕ} (hf : PolyIn U f) (k : ℕ) : PolyIn U (fun i => f i ^ k) := by
  induction k with
  | zero => simpa using (const 1 : PolyIn U (fun _ => 1))
  | succ k ih =>
    simp only [pow_succ]
    exact mul ih hf

theorem max {f g : ι → ℕ} (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => Max.max (f i) (g i)) :=
  mono (fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)) (add hf hg)

theorem div {f : ι → ℕ} (g : ι → ℕ) (hf : PolyIn U f) : PolyIn U (fun i => f i / g i) :=
  mono (fun _ => Nat.div_le_self _ _) hf

theorem mod {f : ι → ℕ} (g : ι → ℕ) (hf : PolyIn U f) : PolyIn U (fun i => f i % g i) :=
  mono (fun _ => Nat.mod_le _ _) hf

theorem sub {f : ι → ℕ} (g : ι → ℕ) (hf : PolyIn U f) : PolyIn U (fun i => f i - g i) :=
  mono (fun _ => Nat.sub_le _ _) hf

/-- Transport along a map of index types that does not increase the size. -/
theorem comap {κ : Type*} {V : κ → ℕ} {f : ι → ℕ} (φ : κ → ι) (hU : ∀ k, U (φ k) ≤ V k)
    (hf : PolyIn U f) : PolyIn V (fun k => f (φ k)) := by
  obtain ⟨K, D, h⟩ := hf
  refine ⟨K, D, fun k => (h (φ k)).trans (Nat.mul_le_mul_left _ ?_)⟩
  exact Nat.pow_le_pow_left (Nat.add_le_add_right (hU k) 1) _

end PolyIn

/-! ## Arithmetic leaf clocks -/

theorem totalTime_le (n m : ℕ) : MatrixUnaryDivision.totalTime n m ≤ 8 * n + 3 * m + 4 := by
  unfold MatrixUnaryDivision.totalTime
  split
  · omega
  · unfold MatrixUnaryDivision.exactTime
    have h1 : n / m * m ≤ n := Nat.div_mul_le_self n m
    have h2 : n / m ≤ n := Nat.div_le_self n m
    have e : n / m * (4 * m + 4) = 4 * (n / m * m) + 4 * (n / m) := by ring
    rw [e]
    omega

theorem iterate_le_aux (acc base B : ℕ) :
    ∀ m k, (∀ j, j ≤ m + k → base ^ j ≤ B) →
      MatrixWeightedPower.iterateBound (acc * base ^ k) base m ≤ m * (9 * (acc * B) + 7) := by
  intro m
  induction m with
  | zero => intro k _; simp [MatrixWeightedPower.iterateBound]
  | succ m ih =>
    intro k hB
    have hk : acc * base ^ k * base = acc * base ^ (k + 1) := by ring
    have ih' := ih (k + 1) (fun j hj => hB j (by omega))
    have b1 : base ^ k ≤ B := hB k (by omega)
    have b2 : base ^ (k + 1) ≤ B := hB (k + 1) (by omega)
    have c1 : acc * base ^ k ≤ acc * B := Nat.mul_le_mul_left _ b1
    have c2 : acc * base ^ (k + 1) ≤ acc * B := Nat.mul_le_mul_left _ b2
    have hr : MatrixWeightedPower.roundBound (acc * base ^ k) base =
        3 * (acc * base ^ (k + 1)) + 5 * (acc * base ^ k) + 7 := by
      unfold MatrixWeightedPower.roundBound MatrixAddressMachine.exactTime
      ring
    simp only [MatrixWeightedPower.iterateBound]
    rw [hk, hr]
    have e : (m + 1) * (9 * (acc * B) + 7) = (9 * (acc * B) + 7) + m * (9 * (acc * B) + 7) := by
      ring
    rw [e]
    omega

theorem iterate_le (base m : ℕ) :
    MatrixWeightedPower.iterateBound 1 base m ≤ m * (9 * (base ^ m + 1) + 7) := by
  have h := iterate_le_aux 1 base (base ^ m + 1) m 0 (by
    intro j hj
    rcases Nat.eq_zero_or_pos base with h0 | hpos
    · subst h0
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp
      · rw [Nat.zero_pow hj0]; exact Nat.zero_le _
    · have := Nat.pow_le_pow_right hpos (show j ≤ m by omega)
      omega)
  simpa using h

theorem powerBound_le (base m : ℕ) :
    MatrixWeightedPower.powerBound base m ≤ m * (9 * (base ^ m + 1) + 7) + 1 := by
  unfold MatrixWeightedPower.powerBound
  have := iterate_le base m
  omega

theorem roundCost_le (n base w : ℕ) :
    MatrixStage4LowDigitStream.roundCost n base w ≤ 18 * n + 3 * base + 3 * w + 11 := by
  unfold MatrixStage4LowDigitStream.roundCost MatrixStage4LowDigitStream.selector
  have h1 := totalTime_le n base
  have h2 := totalTime_le (n % base) w
  have h3 : n % base ≤ n := Nat.mod_le _ _
  have h4 : n % base / w ≤ n % base := Nat.div_le_self _ _
  omega

theorem adminCost_le (n base w : ℕ) :
    MatrixStage4LowDigitStream.adminCost n base w ≤ 3 * n + 4 := by
  unfold MatrixStage4LowDigitStream.adminCost MatrixStage4LowDigitStream.selector
    MatrixStage4LowDigitStream.remainder
  have h3 : n % base ≤ n := Nat.mod_le _ _
  have h4 : n % base / w ≤ n % base := Nat.div_le_self _ _
  have h5 : n % base % w ≤ n % base := Nat.mod_le _ _
  have h6 : n / base ≤ n := Nat.div_le_self _ _
  omega

theorem timeBudget_le (base w : ℕ) :
    ∀ k n, MatrixStage4LowDigitStream.timeBudget n base w k ≤
      (k + 1) * (21 * n + 3 * base + 3 * w + 15) := by
  intro k
  induction k with
  | zero =>
    intro n
    simp only [MatrixStage4LowDigitStream.timeBudget]
    have := roundCost_le n base w
    omega
  | succ k ih =>
    intro n
    simp only [MatrixStage4LowDigitStream.timeBudget]
    have h1 := roundCost_le n base w
    have h2 := adminCost_le n base w
    have h3 := ih (n / base)
    have h4 : n / base ≤ n := Nat.div_le_self _ _
    have h5 : (k + 1) * (21 * (n / base) + 3 * base + 3 * w + 15) ≤
        (k + 1) * (21 * n + 3 * base + 3 * w + 15) := Nat.mul_le_mul_left _ (by omega)
    have e : (k + 1 + 1) * (21 * n + 3 * base + 3 * w + 15) =
        (21 * n + 3 * base + 3 * w + 15) + (k + 1) * (21 * n + 3 * base + 3 * w + 15) := by ring
    rw [e]
    omega

theorem budget_le (ps : List ℕ) (q B : ℕ) (h : ∀ p ∈ ps, p ≤ B) :
    MatrixStage4AlignmentStream.budget ps q ≤ ps.length * (4 * (B + q + 1)) := by
  unfold MatrixStage4AlignmentStream.budget
  have := MatrixMaterialization.sum_le_length_mul (ps.map fun p => 4 * (p + q + 1))
    (4 * (B + q + 1)) (by
      intro x hx
      rcases List.mem_map.1 hx with ⟨p, hp, rfl⟩
      have := h p hp
      omega)
  simpa using this

theorem selectorDigit_le {a s q cy : ℕ} (code : Fin (cols a s q cy)) (p : Fin s) :
    MatrixStage4AlignmentDigits.selectorDigit code p ≤ code.val := by
  unfold MatrixStage4AlignmentDigits.selectorDigit binDigit
  calc _ ≤ code.val % binBase a s q cy ^ s / binBase a s q cy ^ (s - 1 - p.val) %
          binBase a s q cy := Nat.div_le_self _ _
    _ ≤ code.val % binBase a s q cy ^ s / binBase a s q cy ^ (s - 1 - p.val) := Nat.mod_le _ _
    _ ≤ code.val % binBase a s q cy ^ s := Nat.div_le_self _ _
    _ ≤ code.val := Nat.mod_le _ _

theorem selectorBudget_le {a s q cy : ℕ} (code : Fin (cols a s q cy)) (r : ℕ) :
    MatrixStage4AlignmentStream.budget (MatrixStage4AlignmentCorrect.selectorWords code) r ≤
      s * (4 * (code.val + r + 1)) := by
  have := budget_le (MatrixStage4AlignmentCorrect.selectorWords code) r code.val (by
    intro p hp
    unfold MatrixStage4AlignmentCorrect.selectorWords at hp
    rcases List.mem_ofFn.1 hp with ⟨j, rfl⟩
    exact selectorDigit_le code j)
  simpa [MatrixStage4AlignmentCorrect.selectorWords] using this

theorem activeRank_le {n q : ℕ} (vectors : Fin n → Fin q → Bool) (α : Fin q) (i : Fin n) :
    activeRank vectors α i ≤ n := by
  unfold activeRank
  simpa using Finset.card_le_univ (activeBefore vectors α i)

/-! ## Seed-length leaves -/

theorem update_len {α : Type*} [DecidableEq α] (g : α → List Bool) (a : α) (v : List Bool)
    (S : ℕ) (hg : ∀ k, (g k).length ≤ S) (hv : v.length ≤ S) :
    ∀ k, (Function.update g a v k).length ≤ S := by
  intro k
  by_cases h : k = a
  · subst h; simpa using hv
  · rw [Function.update_of_ne h]; exact hg k

#print axioms totalTime_le
#print axioms iterate_le
#print axioms powerBound_le
#print axioms timeBudget_le
#print axioms selectorBudget_le
#print axioms activeRank_le

end EthInapproximability.CurrentPaper.EntryClockPoly
