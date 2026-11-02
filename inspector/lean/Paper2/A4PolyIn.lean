import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Unit 4 (Paper A): closure lemmas for "polynomially bounded in a size function"

Owner lane `owner:a-unit4-shell-2` (private, 25 September 2026). Pure arithmetic, used by the
A4-S3 envelope and front composition. `PolyIn sz a` says `a i ≤ C·(sz i + 1)^E` for fixed
`C, E`. **Not a ledger row.**
-/

namespace Paper2.Unit4Shell.Poly

/-- `a` is bounded by a fixed polynomial of `sz`. -/
def PolyIn {ι : Type*} (sz : ι → ℕ) (a : ι → ℕ) : Prop :=
  ∃ C E : ℕ, ∀ i, a i ≤ C * (sz i + 1) ^ E

variable {ι : Type*} {sz : ι → ℕ}

theorem mono {a b : ι → ℕ} (h : ∀ i, a i ≤ b i) (hb : PolyIn sz b) : PolyIn sz a := by
  obtain ⟨C, E, hC⟩ := hb
  exact ⟨C, E, fun i => (h i).trans (hC i)⟩

theorem const (c : ℕ) : PolyIn sz (fun _ => c) := ⟨c, 0, fun _ => by simp⟩

theorem self : PolyIn sz sz := ⟨1, 1, fun i => by simp⟩

private theorem pow_le_pow_of_le {x a b : ℕ} (h : a ≤ b) : (x + 1) ^ a ≤ (x + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos x) h

theorem add {a b : ι → ℕ} (ha : PolyIn sz a) (hb : PolyIn sz b) :
    PolyIn sz (fun i => a i + b i) := by
  obtain ⟨C1, E1, h1⟩ := ha
  obtain ⟨C2, E2, h2⟩ := hb
  refine ⟨C1 + C2, E1 + E2, fun i => ?_⟩
  have p1 : (sz i + 1) ^ E1 ≤ (sz i + 1) ^ (E1 + E2) := pow_le_pow_of_le (by omega)
  have p2 : (sz i + 1) ^ E2 ≤ (sz i + 1) ^ (E1 + E2) := pow_le_pow_of_le (by omega)
  have q1 := Nat.mul_le_mul_left C1 p1
  have q2 := Nat.mul_le_mul_left C2 p2
  have := h1 i
  have := h2 i
  calc a i + b i ≤ C1 * (sz i + 1) ^ (E1 + E2) + C2 * (sz i + 1) ^ (E1 + E2) := by omega
    _ = (C1 + C2) * (sz i + 1) ^ (E1 + E2) := by ring

theorem mul {a b : ι → ℕ} (ha : PolyIn sz a) (hb : PolyIn sz b) :
    PolyIn sz (fun i => a i * b i) := by
  obtain ⟨C1, E1, h1⟩ := ha
  obtain ⟨C2, E2, h2⟩ := hb
  refine ⟨C1 * C2, E1 + E2, fun i => ?_⟩
  calc a i * b i ≤ (C1 * (sz i + 1) ^ E1) * (C2 * (sz i + 1) ^ E2) := Nat.mul_le_mul (h1 i) (h2 i)
    _ = C1 * C2 * (sz i + 1) ^ (E1 + E2) := by rw [pow_add]; ring

theorem pow {a : ι → ℕ} (ha : PolyIn sz a) (e : ℕ) : PolyIn sz (fun i => a i ^ e) := by
  obtain ⟨C1, E1, h1⟩ := ha
  refine ⟨C1 ^ e, E1 * e, fun i => ?_⟩
  calc a i ^ e ≤ (C1 * (sz i + 1) ^ E1) ^ e := Nat.pow_le_pow_left (h1 i) e
    _ = C1 ^ e * (sz i + 1) ^ (E1 * e) := by rw [mul_pow, ← pow_mul]

/-- Change of size function: if `sz ≤ poly(sz')` pointwise then `PolyIn sz a → PolyIn sz' a`. -/
theorem transfer {sz' : ι → ℕ} (hs : PolyIn sz' sz) {a : ι → ℕ} (ha : PolyIn sz a) :
    PolyIn sz' a := by
  obtain ⟨C, E, h⟩ := ha
  obtain ⟨Cs, Es, hs⟩ := hs
  refine ⟨C * (Cs + 1) ^ E, Es * E, fun i => ?_⟩
  have h1 : sz i + 1 ≤ (Cs + 1) * (sz' i + 1) ^ Es := by
    have := hs i
    have h0 : 1 ≤ (sz' i + 1) ^ Es := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith
  calc a i ≤ C * (sz i + 1) ^ E := h i
    _ ≤ C * ((Cs + 1) * (sz' i + 1) ^ Es) ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 E)
    _ = C * (Cs + 1) ^ E * (sz' i + 1) ^ (Es * E) := by rw [mul_pow, ← pow_mul]; ring

end Paper2.Unit4Shell.Poly
