import Mathlib

/-!
Private composition lemma for the selected v27 manuscript,
`sections/09-deterministic.tex`, `det:reduction` and the resource calculation
used by `det:eth`. This file does not construct the deterministic amplifier,
its effective schedule, or its output machine. Those are explicit premises.

The same seed and step function produce every state. The YES induction uses
only a YES upper-bound contract; the NO induction alone uses exact input cost
and the recurring restriction profile. The resource calculation is independent
of both graph promises.
-/

namespace CurrentAdditive.DeterministicIteration

universe u v

/-- Data of one proposed deterministic construction, indexed by the source
graph. `size` charges the complete table, indexed labels, and rational laws;
`stepTime` charges one step on that complete encoding. -/
structure Construction (Graph : Type u) (State : Type v) where
  seed : Graph → State
  step : Graph → State → State
  cost : State → ℕ
  valid : Graph → State → Prop
  profile : Graph → State → Prop
  size : State → ℕ
  stepTime : State → ℕ

variable {Graph : Type u} {State : Type v}

/-- The object after exactly `k` applications of the *same* step. -/
def state (C : Construction Graph State) (G : Graph) : ℕ → State
  | 0 => C.seed G
  | k + 1 => C.step G (state C G k)

/-- Public guards, admissible rational laws, and any other domain conditions
needed for a concrete step, retained on the same iterated object. -/
structure ValidContract (C : Construction Graph State) (G : Graph) : Prop where
  seed_valid : C.valid G (C.seed G)
  step_valid : ∀ R, C.valid G R → C.valid G (C.step G R)

theorem state_valid (C : Construction Graph State) (G : Graph)
    (k : ℕ) (V : ValidContract C G) : C.valid G (state C G k) := by
  induction k with
  | zero => exact V.seed_valid
  | succ k ih => exact V.step_valid _ ih

/-- Public YES budget in `det:reduction`. -/
def budget (d₀ h k : ℕ) : ℕ := d₀ + k * h

/-- The promise-free upper protocol supplied by `det:amplifier`. -/
structure UniversalContract (C : Construction Graph State) (G : Graph)
    (d₀ h : ℕ) : Prop where
  seed_upper : C.cost (C.seed G) ≤ d₀
  step_upper : ∀ R, C.valid G R → C.cost (C.step G R) ≤ C.cost R + h + 1

/-- The YES part of `det:amplifier` requires no exact input cost and no profile. -/
structure YesContract (C : Construction Graph State) (G : Graph)
    (d₀ h : ℕ) : Prop where
  seed_upper : C.cost (C.seed G) ≤ d₀
  step_upper : ∀ R, C.valid G R → C.cost (C.step G R) ≤ C.cost R + h

/-- The NO part of `det:amplifier`, including the guard `d ≥ 3`. -/
structure NoContract (C : Construction Graph State) (G : Graph)
    (d₀ h : ℕ) : Prop where
  seed_exact : C.cost (C.seed G) = d₀
  seed_profile : C.profile G (C.seed G)
  seed_cost_ge : 3 ≤ d₀
  step_exact_profile : ∀ R, C.valid G R → 3 ≤ C.cost R → C.profile G R →
    C.cost (C.step G R) = C.cost R + h + 1 ∧
    C.profile G (C.step G R)

/-- `Z_i = N + S_i + 2` in the manuscript. The premise here is the
*absorbed* power recurrence; a proof from fixed polynomial bit arithmetic
and the concrete constructor remains a separate obligation. -/
def envelope (C : Construction Graph State) (N : ℕ) (R : State) : ℕ :=
  N + C.size R + 2

/-- Complete-encoding size and step clock, after absorption into `A`. -/
structure ResourceContract (C : Construction Graph State) (G : Graph)
    (N A C₁ : ℕ) : Prop where
  base : envelope C N (C.seed G) ≤ N ^ C₁
  successor : ∀ R, C.valid G R →
    envelope C N (C.step G R) ≤ (envelope C N R) ^ A
  step_clock : ∀ R, C.valid G R →
    C.stepTime R ≤ (envelope C N R) ^ A

/-- Sum of the actual charged clocks for the first `k` constructed steps. -/
def totalStepTime (C : Construction Graph State) (G : Graph) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, C.stepTime (state C G i)

theorem universal_iteration (C : Construction Graph State) (G : Graph)
    (d₀ h k : ℕ) (V : ValidContract C G)
    (H : UniversalContract C G d₀ h) :
    C.cost (state C G k) ≤ d₀ + k * (h + 1) := by
  induction k with
  | zero => simpa [state] using H.seed_upper
  | succ k ih =>
      calc
        C.cost (state C G (k + 1))
            = C.cost (C.step G (state C G k)) := rfl
        _ ≤ C.cost (state C G k) + h + 1 :=
          H.step_upper _ (state_valid C G k V)
        _ ≤ (d₀ + k * (h + 1)) + h + 1 := by omega
        _ = d₀ + (k + 1) * (h + 1) := by
          simp [Nat.succ_mul]
          omega

theorem yes_iteration (C : Construction Graph State) (G : Graph)
    (d₀ h k : ℕ) (V : ValidContract C G)
    (H : YesContract C G d₀ h) :
    C.cost (state C G k) ≤ budget d₀ h k := by
  induction k with
  | zero => simpa [state, budget] using H.seed_upper
  | succ k ih =>
      calc
        C.cost (state C G (k + 1))
            = C.cost (C.step G (state C G k)) := rfl
        _ ≤ C.cost (state C G k) + h :=
          H.step_upper _ (state_valid C G k V)
        _ ≤ budget d₀ h k + h := Nat.add_le_add_right ih h
        _ = budget d₀ h (k + 1) := by simp [budget, Nat.succ_mul, add_assoc]

theorem no_iteration (C : Construction Graph State) (G : Graph)
    (d₀ h k : ℕ) (V : ValidContract C G)
    (H : NoContract C G d₀ h) :
    C.cost (state C G k) = d₀ + k * (h + 1) ∧
    C.profile G (state C G k) := by
  induction k with
  | zero => simpa [state] using And.intro H.seed_exact H.seed_profile
  | succ k ih =>
      have hcost : 3 ≤ C.cost (state C G k) := by
        rw [ih.1]
        exact le_trans H.seed_cost_ge (Nat.le_add_right d₀ (k * (h + 1)))
      obtain ⟨heq, hp⟩ := H.step_exact_profile _
        (state_valid C G k V) hcost ih.2
      constructor
      · change C.cost (C.step G (state C G k)) = _
        rw [heq, ih.1]
        simp [Nat.succ_mul]
        omega
      · exact hp

theorem no_iteration_gap (C : Construction Graph State) (G : Graph)
    (d₀ h k : ℕ) (V : ValidContract C G)
    (H : NoContract C G d₀ h) :
    C.cost (state C G k) = budget d₀ h k + k ∧
    C.profile G (state C G k) := by
  obtain ⟨heq, hp⟩ := no_iteration C G d₀ h k V H
  constructor
  · rw [heq]
    dsimp [budget]
    simp only [Nat.mul_add, mul_one]
    omega
  · exact hp

theorem growth_iteration (C : Construction Graph State) (G : Graph)
    (N A C₁ k : ℕ) (V : ValidContract C G)
    (H : ResourceContract C G N A C₁) :
    envelope C N (state C G k) ≤ N ^ (C₁ * A ^ k) := by
  induction k with
  | zero => simpa [state] using H.base
  | succ k ih =>
      calc
        envelope C N (state C G (k + 1))
            = envelope C N (C.step G (state C G k)) := rfl
        _ ≤ (envelope C N (state C G k)) ^ A :=
          H.successor _ (state_valid C G k V)
        _ ≤ (N ^ (C₁ * A ^ k)) ^ A := pow_le_pow_left₀ (by omega) ih A
        _ = N ^ (C₁ * A ^ (k + 1)) := by
          rw [← pow_mul, pow_succ]
          congr 1
          ring

/-- Elementary numerical bound needed to absorb the number of steps. -/
private theorem le_pow_self (b : ℕ) (hb : 2 ≤ b) : ∀ n : ℕ, n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 1 ≤ b ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
      calc
        n + 1 ≤ b ^ n + 1 := by omega
        _ ≤ b ^ n + b ^ n := by omega
        _ ≤ b ^ n * b := by nlinarith
        _ = b ^ (n + 1) := by rw [pow_succ]

private theorem pow_exp_mono (b : ℕ) (hb : 1 ≤ b) {i k : ℕ} (hik : i ≤ k) :
    b ^ i ≤ b ^ k := by
  exact pow_le_pow_right₀ hb hik

theorem time_each_le_final (C : Construction Graph State) (G : Graph)
    (N A C₁ k i : ℕ) (hN : 2 ≤ N) (hA : 2 ≤ A)
    (V : ValidContract C G) (H : ResourceContract C G N A C₁)
    (hik : i < k) :
    C.stepTime (state C G i) ≤ N ^ (C₁ * A ^ k) := by
  have hclock := H.step_clock (state C G i) (state_valid C G i V)
  have hgrowth := growth_iteration C G N A C₁ i V H
  have hindex : i + 1 ≤ k := by omega
  have hexp : C₁ * A ^ (i + 1) ≤ C₁ * A ^ k :=
    Nat.mul_le_mul_left C₁ (pow_exp_mono A (by omega) hindex)
  calc
    C.stepTime (state C G i)
        ≤ (envelope C N (state C G i)) ^ A := hclock
    _ ≤ (N ^ (C₁ * A ^ i)) ^ A := pow_le_pow_left₀ (by omega) hgrowth A
    _ = N ^ (C₁ * A ^ (i + 1)) := by
      rw [← pow_mul, pow_succ]
      congr 1
      ring
    _ ≤ N ^ (C₁ * A ^ k) := pow_exp_mono N (by omega) hexp

theorem total_time_le_multiple (C : Construction Graph State) (G : Graph)
    (N A C₁ k : ℕ) (hN : 2 ≤ N) (hA : 2 ≤ A)
    (V : ValidContract C G) (H : ResourceContract C G N A C₁) :
    totalStepTime C G k ≤ k * N ^ (C₁ * A ^ k) := by
  unfold totalStepTime
  calc
    ∑ i ∈ Finset.range k, C.stepTime (state C G i)
        ≤ ∑ _i ∈ Finset.range k, N ^ (C₁ * A ^ k) := by
          apply Finset.sum_le_sum
          intro i hi
          exact time_each_le_final C G N A C₁ k i hN hA V H
            (Finset.mem_range.mp hi)
    _ = k * N ^ (C₁ * A ^ k) := by simp

/-- The complete `k`-step clock is absorbed in one extra copy of `A^k`
in the exponent. This is the arithmetic part of `det:eth`'s subexponential
runtime estimate, before choosing `k` as a function of a SAT instance size. -/
theorem total_time_power (C : Construction Graph State) (G : Graph)
    (N A C₁ k : ℕ) (hN : 2 ≤ N) (hA : 2 ≤ A)
    (V : ValidContract C G) (H : ResourceContract C G N A C₁) :
    totalStepTime C G k ≤ N ^ ((C₁ + 1) * A ^ k) := by
  have hkA : k ≤ A ^ k := le_pow_self A hA k
  have hAN : A ^ k ≤ N ^ (A ^ k) := le_pow_self N hN (A ^ k)
  calc
    totalStepTime C G k ≤ k * N ^ (C₁ * A ^ k) :=
      total_time_le_multiple C G N A C₁ k hN hA V H
    _ ≤ N ^ (A ^ k) * N ^ (C₁ * A ^ k) := by
      exact Nat.mul_le_mul_right _ (hkA.trans hAN)
    _ = N ^ ((C₁ + 1) * A ^ k) := by
      rw [← pow_add]
      congr 1
      ring

/-- One common public exponent bounds the complete stage encoding and the
sum of all `k` step clocks. The final Boolean-only writer and square padding
need their own concrete implementation and accounting. -/
theorem size_and_steps_at_public_exponent
    (C : Construction Graph State) (G : Graph)
    (N A C₁ C₀ k : ℕ) (hN : 2 ≤ N) (hA : 2 ≤ A)
    (hC₀ : C₁ + 1 ≤ C₀)
    (V : ValidContract C G)
    (H : ResourceContract C G N A C₁) :
    C.size (state C G k) ≤ N ^ (C₀ * A ^ k) ∧
    totalStepTime C G k ≤ N ^ (C₀ * A ^ k) := by
  have hsmall : C₁ * A ^ k ≤ C₀ * A ^ k := by
    exact Nat.mul_le_mul_right (A ^ k) (by omega : C₁ ≤ C₀)
  have htime : (C₁ + 1) * A ^ k ≤ C₀ * A ^ k :=
    Nat.mul_le_mul_right (A ^ k) hC₀
  constructor
  · calc
      C.size (state C G k) ≤ envelope C N (state C G k) := by
        unfold envelope
        omega
      _ ≤ N ^ (C₁ * A ^ k) := growth_iteration C G N A C₁ k V H
      _ ≤ N ^ (C₀ * A ^ k) := pow_exp_mono N (by omega) hsmall
  · exact (total_time_power C G N A C₁ k hN hA V H).trans
      (pow_exp_mono N (by omega) htime)

/-- A downstream conditional version of the arithmetic content of
`det:reduction`: one actual `state C G k` satisfies both promise implications
and the complete size/clock bounds. Its hypotheses are intended to be
instantiated by the as-yet-unformalized concrete constructor and schedule. -/
theorem conditional_reduction
    (C : Construction Graph State) (G : Graph)
    (Yes No : Graph → Prop) (N A C₁ C₀ d₀ h k : ℕ)
    (hN : 2 ≤ N) (hA : 2 ≤ A) (hC₀ : C₁ + 1 ≤ C₀)
    (hValid : ValidContract C G)
    (hUniversal : UniversalContract C G d₀ h)
    (hYes : Yes G → YesContract C G d₀ h)
    (hNo : No G → NoContract C G d₀ h)
    (hResources : ResourceContract C G N A C₁) :
    C.cost (state C G k) ≤ budget d₀ h k + k ∧
    (Yes G → C.cost (state C G k) ≤ budget d₀ h k) ∧
    (No G → C.cost (state C G k) = budget d₀ h k + k ∧
      C.profile G (state C G k)) ∧
    C.size (state C G k) ≤ N ^ (C₀ * A ^ k) ∧
    totalStepTime C G k ≤ N ^ (C₀ * A ^ k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hu := universal_iteration C G d₀ h k hValid hUniversal
    simpa only [budget, Nat.mul_add, mul_one, add_assoc] using hu
  · intro hy
    exact yes_iteration C G d₀ h k hValid (hYes hy)
  · intro hn
    exact no_iteration_gap C G d₀ h k hValid (hNo hn)
  · exact (size_and_steps_at_public_exponent C G N A C₁ C₀ k hN hA
      hC₀ hValid hResources).1
  · exact (size_and_steps_at_public_exponent C G N A C₁ C₀ k hN hA
      hC₀ hValid hResources).2

#print axioms state_valid
#print axioms universal_iteration
#print axioms yes_iteration
#print axioms no_iteration
#print axioms growth_iteration
#print axioms total_time_power
#print axioms size_and_steps_at_public_exponent
#print axioms conditional_reduction

end CurrentAdditive.DeterministicIteration
