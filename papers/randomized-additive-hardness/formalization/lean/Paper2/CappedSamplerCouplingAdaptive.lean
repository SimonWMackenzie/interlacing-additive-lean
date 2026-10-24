import Paper2.CappedSamplerCoupling
import Paper2.CappedSamplerCouplingPrefix

/-!
# Bounded adaptive finite-alphabet draws on one fixed fair-bit tape

Frozen source: v12, `appendices/D-implementation.tex:83--102` (U15).
The denominator and state transition may depend on the entire current state.
Each draw receives a fresh block of the same public width; unused high bits
are ignored. Thus the execution uses one fixed finite product of independent
fair bits, rather than conditioning the complete adaptive process on success.
The draw-count and width hypotheses are explicit; their verification for the
manuscript's label generator, and machine-time accounting, remain separate.
-/

namespace Paper2.CappedSampler.Adaptive

open scoped BigOperators

/-- `n` fresh blocks, each containing `R` attempts of `B` bits. -/
def Tape (B R : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => BitTape B R × Tape B R n

instance tapeFintype (B R n : ℕ) : Fintype (Tape B R n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (BitTape B R × Tape B R n))

noncomputable def law (B R : ℕ) : (n : ℕ) → FiniteLaw (Tape B R n)
  | 0 => { weight := fun _ => 1, nonneg := fun _ => by norm_num, total := by simp [Tape] }
  | n + 1 => (bitTapeLaw B R).prod (law B R n)

variable {S : Type*} (D : S → ℕ) (next : (s : S) → Fin (D s) → S)
  (B R : ℕ) (hB : ∀ s, Nat.clog 2 (D s) ≤ B)

/-- The adaptive algorithm; failure aborts before any later transition. -/
def run : (n : ℕ) → S → Tape B R n → Option S
  | 0, s, _ => some s
  | n + 1, s, t => (runWideBits (D s) B R (hB s) t.1).bind
      (fun a => run n (next s a) t.2)

/-- Number of bits allocated to the complete input tape. -/
def allocatedBits (n : ℕ) : ℕ := n * (B * R)

/-- Bit queries made by the inspected attempts in one draw. -/
def drawBits (s : S) (t : BitTape B R) : ℕ :=
  Nat.clog 2 (D s) * used (D s) (ticketSize (D s)) R
    (bitTapeEquiv (Nat.clog 2 (D s)) R (prefixBitTape (hB s) R t))

/-- Exact query counter for the same execution: later draws are counted
only if the current draw accepts. This is not a machine-time counter. -/
def inspectedBits : (n : ℕ) → S → Tape B R n → ℕ
  | 0, _, _ => 0
  | n + 1, s, t => drawBits D B R hB s t.1 +
      match runWideBits (D s) B R (hB s) t.1 with
      | none => 0
      | some a => inspectedBits n (next s a) t.2

theorem drawBits_le (s : S) (t : BitTape B R) : drawBits D B R hB s t ≤ B * R :=
  (used_bit_budget (D s) R (prefixBitTape (hB s) R t)).trans
    (Nat.mul_le_mul_right R (hB s))

theorem inspectedBits_le (n : ℕ) (s : S) (t : Tape B R n) :
    inspectedBits D next B R hB n s t ≤ allocatedBits B R n := by
  induction n generalizing s with
  | zero => simp [inspectedBits, allocatedBits]
  | succ n ih =>
    have hd := drawBits_le D B R hB s t.1
    simp only [inspectedBits, allocatedBits, Nat.succ_mul]
    cases hr : runWideBits (D s) B R (hB s) t.1 with
    | none => dsimp only; omega
    | some a =>
      have hi := ih (next s a) t.2
      unfold allocatedBits at hi
      dsimp only
      omega

/-- Ideal adaptive execution: each step draws a fresh exact uniform element
of its state-dependent alphabet. This is a recursively defined probability,
not a conditional law of the capped algorithm. -/
noncomputable def idealMass (hD : ∀ s, 0 < D s) : (n : ℕ) → S → (S → Prop) → ℝ
  | 0, s, E => by
      classical
      exact if E s then 1 else 0
  | n + 1, s, E => ∑ a : Fin (D s), (uniformTicket (D s) (hD s)).weight a *
      idealMass hD n (next s a) E

noncomputable def successMass (n : ℕ) (s : S) (E : S → Prop) : ℝ :=
  (law B R n).prob (fun t => ∃ u, run D next B R hB n s t = some u ∧ E u)

/-- Disintegrate one actual step by its accepted value. -/
theorem product_success {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : FiniteLaw α) (ν : FiniteLaw γ) (f : α → Option β)
    (g : β → γ → Option S) (E : S → Prop) :
    (μ.prod ν).prob (fun z => ∃ u, (f z.1).bind (fun a => g a z.2) = some u ∧ E u) =
      ∑ a : β, μ.prob (fun t => f t = some a) *
        ν.prob (fun t => ∃ u, g a t = some u ∧ E u) := by
  classical
  rw [FiniteLaw.prod_prob μ ν
    (fun t v => ∃ u, (f t).bind (fun a => g a v) = some u ∧ E u)]
  have he (t : α) :
      ν.prob (fun v => ∃ u, (f t).bind (fun a => g a v) = some u ∧ E u) =
        ∑ a : β, if f t = some a then ν.prob (fun v => ∃ u, g a v = some u ∧ E u) else 0 := by
    cases hf : f t with
    | none => simp
    | some a => simp
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [FiniteLaw.prob]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem success_recurrence (hD : ∀ s, 0 < D s) (n : ℕ) (s : S) (E : S → Prop) :
    successMass D next B R hB (n + 1) s E =
      (1 - rejectionMass (D s) (ticketSize (D s)) ^ R) *
        ∑ a : Fin (D s), (uniformTicket (D s) (hD s)).weight a *
          successMass D next B R hB n (next s a) E := by
  change ((bitTapeLaw B R).prod (law B R n)).prob
    (fun z => ∃ u, (runWideBits (D s) B R (hB s) z.1).bind
      (fun a => run D next B R hB n (next s a) z.2) = some u ∧ E u) = _
  rw [product_success (bitTapeLaw B R) (law B R n)
    (runWideBits (D s) B R (hB s)) (fun a t => run D next B R hB n (next s a) t) E]
  simp_rw [runWideBits_accepted_exact (D s) B R (hD s) (hB s)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [uniformTicket, successMass, div_eq_mul_inv]
  ring

@[simp] theorem run_zero (s : S) (t : Tape B R 0) :
    run D next B R hB 0 s t = some s := rfl

/-- Exhaustion probability is bounded for every initial state, even though
all future denominators depend on previously sampled values. -/
theorem failure_le (hD : ∀ s, 0 < D s) (n : ℕ) (s : S) :
    (law B R n).prob (fun t => run D next B R hB n s t = none) ≤
      (n : ℝ) * (1 / 2 : ℝ) ^ R := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    change ((bitTapeLaw B R).prod (law B R n)).prob
      (fun t => (runWideBits (D s) B R (hB s) t.1).bind
        (fun a => run D next B R hB n (next s a) t.2) = none) ≤ _
    rw [FiniteLaw.prod_prob (bitTapeLaw B R) (law B R n)
      (fun t u => (runWideBits (D s) B R (hB s) t).bind
        (fun a => run D next B R hB n (next s a) u) = none)]
    have hp : 0 ≤ (n : ℝ) * (1 / 2 : ℝ) ^ R := by positivity
    have he (t : BitTape B R) :
        (law B R n).prob (fun u => (runWideBits (D s) B R (hB s) t).bind
          (fun a => run D next B R hB n (next s a) u) = none) ≤
        (if runWideBits (D s) B R (hB s) t = none then 1 else 0) +
          (n : ℝ) * (1 / 2 : ℝ) ^ R := by
      cases hr : runWideBits (D s) B R (hB s) t with
      | none => simpa using hp
      | some a => simpa using ih (next s a)
    calc
      _ ≤ ∑ t : BitTape B R, (bitTapeLaw B R).weight t *
          ((if runWideBits (D s) B R (hB s) t = none then 1 else 0) +
            (n : ℝ) * (1 / 2 : ℝ) ^ R) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (he t) ((bitTapeLaw B R).nonneg t)
      _ = (bitTapeLaw B R).prob (fun t => runWideBits (D s) B R (hB s) t = none) +
          (n : ℝ) * (1 / 2 : ℝ) ^ R := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, FiniteLaw.total, one_mul]
        congr 1
        unfold FiniteLaw.prob
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> simp
      _ ≤ (1 / 2 : ℝ) ^ R + (n : ℝ) * (1 / 2 : ℝ) ^ R := by
        have := runWideBits_failure_le (D s) B R (hD s) (hB s)
        linarith
      _ = (↑(n + 1) : ℝ) * (1 / 2 : ℝ) ^ R := by push_cast; ring

theorem success_le_ideal (hD : ∀ s, 0 < D s) (n : ℕ) (s : S) (E : S → Prop) :
    successMass D next B R hB n s E ≤ idealMass D next hD n s E := by
  classical
  induction n generalizing s with
  | zero => by_cases hs : E s <;> simp [successMass, run, idealMass, hs]
  | succ n ih =>
    rw [success_recurrence D next B R hB hD n s E]
    let A := ∑ a : Fin (D s), (uniformTicket (D s) (hD s)).weight a *
      successMass D next B R hB n (next s a) E
    have ha : 0 ≤ A := Finset.sum_nonneg fun a _ =>
      mul_nonneg ((uniformTicket (D s) (hD s)).nonneg a) ((law B R n).prob_nonneg _)
    have hq : 0 ≤ rejectionMass (D s) (ticketSize (D s)) ^ R :=
      pow_nonneg (rejectionMass_nonneg _ _) _
    calc
      _ ≤ A := by dsimp only [A] at ha ⊢; nlinarith
      _ ≤ idealMass D next hD (n + 1) s E := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (ih (next s a)) ((uniformTicket (D s) (hD s)).nonneg a)

/-- An arbitrary final event loses at most `n * 2^-R` probability under the
actual adaptive capped implementation. No global conditioning is used. -/
theorem ideal_le_success_add_error (hD : ∀ s, 0 < D s)
    (n : ℕ) (s : S) (E : S → Prop) :
    idealMass D next hD n s E ≤
      successMass D next B R hB n s E + (n : ℝ) * (1 / 2 : ℝ) ^ R := by
  classical
  induction n generalizing s with
  | zero => by_cases hs : E s <;> simp [successMass, run, idealMass, hs]
  | succ n ih =>
    let μ := uniformTicket (D s) (hD s)
    let A := ∑ a : Fin (D s), μ.weight a * successMass D next B R hB n (next s a) E
    have ha0 : 0 ≤ A := Finset.sum_nonneg fun a _ =>
      mul_nonneg (μ.nonneg a) ((law B R n).prob_nonneg _)
    have ha1 : A ≤ 1 := by
      calc
        _ ≤ ∑ a : Fin (D s), μ.weight a * 1 :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left ((law B R n).prob_le_one _) (μ.nonneg a)
        _ = 1 := by simp [μ.total]
    have hi : idealMass D next hD (n + 1) s E ≤ A + (n : ℝ) * (1 / 2 : ℝ) ^ R := by
      calc
        _ ≤ ∑ a : Fin (D s), μ.weight a *
            (successMass D next B R hB n (next s a) E + (n : ℝ) * (1 / 2 : ℝ) ^ R) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih (next s a)) (μ.nonneg a)
        _ = A + (n : ℝ) * (1 / 2 : ℝ) ^ R := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.total, one_mul]
    have hq0 : 0 ≤ rejectionMass (D s) (ticketSize (D s)) ^ R :=
      pow_nonneg (rejectionMass_nonneg _ _) _
    have hq : rejectionMass (D s) (ticketSize (D s)) ^ R ≤ (1 / 2 : ℝ) ^ R :=
      pow_le_pow_left₀ (rejectionMass_nonneg _ _) (rejectionMass_le_half (D s) (hD s)) _
    have hqa : rejectionMass (D s) (ticketSize (D s)) ^ R * A ≤ (1 / 2 : ℝ) ^ R :=
      (mul_le_mul_of_nonneg_left ha1 hq0).trans (by simpa using hq)
    have hc := success_recurrence D next B R hB hD n s E
    change successMass D next B R hB (n + 1) s E =
      (1 - rejectionMass (D s) (ticketSize (D s)) ^ R) * A at hc
    push_cast
    nlinarith

theorem idealMass_nonneg (hD : ∀ s, 0 < D s) (n : ℕ) (s : S) (E : S → Prop) :
    0 ≤ idealMass D next hD n s E := by
  classical
  induction n generalizing s with
  | zero => simp only [idealMass]; split_ifs <;> norm_num
  | succ n ih =>
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg ((uniformTicket (D s) (hD s)).nonneg a) (ih (next s a))

theorem idealMass_le_one (hD : ∀ s, 0 < D s) (n : ℕ) (s : S) (E : S → Prop) :
    idealMass D next hD n s E ≤ 1 := by
  classical
  induction n generalizing s with
  | zero => simp only [idealMass]; split_ifs <;> norm_num
  | succ n ih =>
    calc
      _ ≤ ∑ a : Fin (D s), (uniformTicket (D s) (hD s)).weight a * 1 :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (ih (next s a)) ((uniformTicket (D s) (hD s)).nonneg a)
      _ = 1 := by simp [(uniformTicket (D s) (hD s)).total]

@[simp] theorem idealMass_true (hD : ∀ s, 0 < D s) (n : ℕ) (s : S) :
    idealMass D next hD n s (fun _ => True) = 1 := by
  induction n generalizing s with
  | zero => simp [idealMass]
  | succ n ih => simp [idealMass, ih, (uniformTicket (D s) (hD s)).total]

theorem abort_event_decomposition {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (f : α → Option S) (s₀ : S) (E : S → Prop) [DecidablePred E] :
    μ.prob (fun t => E (completed (f t) s₀)) =
      μ.prob (fun t => ∃ s, f t = some s ∧ E s) +
        (if E s₀ then μ.prob (fun t => f t = none) else 0) := by
  classical
  by_cases hs : E s₀
  · simp only [hs, ↓reduceIte, FiniteLaw.prob]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rcases Option.eq_none_or_eq_some (f t) with hf | ⟨a, hf⟩
    · simp [hf, completed, hs]
    · by_cases ha : E a <;> simp [hf, completed, ha]
  · simp only [hs, ↓reduceIte, add_zero, FiniteLaw.prob]
    apply Finset.sum_congr rfl
    intro t _
    rcases Option.eq_none_or_eq_some (f t) with hf | ⟨a, hf⟩
    · simp [hf, completed, hs]
    · by_cases ha : E a <;> simp [hf, completed, ha]

/-- Full event-error guarantee for the adaptive fixed-tape implementation,
including an arbitrary deterministic abort output. -/
theorem abort_event_error (hD : ∀ s, 0 < D s) (n : ℕ) (s s₀ : S) (E : S → Prop) :
    |(law B R n).prob (fun t => E (completed (run D next B R hB n s t) s₀)) -
        idealMass D next hD n s E| ≤ (n : ℝ) * (1 / 2 : ℝ) ^ R := by
  classical
  have hu := success_le_ideal D next B R hB hD n s E
  have hl := ideal_le_success_add_error D next B R hB hD n s E
  have hf := failure_le D next B R hB hD n s
  have hf0 := (law B R n).prob_nonneg (fun t => run D next B R hB n s t = none)
  rw [abort_event_decomposition (law B R n) (run D next B R hB n s) s₀ E]
  change |successMass D next B R hB n s E +
      (if E s₀ then (law B R n).prob (fun t => run D next B R hB n s t = none) else 0) -
      idealMass D next hD n s E| ≤ _
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Instantiating the manuscript's public attempt cap gives its claimed
`2^-13` exhaustion bound for this actual adaptive execution. -/
theorem scheduled_failure_le (hD : ∀ s, 0 < D s) (N : ℕ) (s : S) :
    (law B (rejectionAttemptCap N) N).prob
      (fun t => run D next B (rejectionAttemptCap N) hB N s t = none) ≤
        (1 / 2 : ℝ) ^ 13 :=
  (failure_le D next B (rejectionAttemptCap N) hB hD N s).trans (rejection_cap_error_real N)

theorem scheduled_event_error (hD : ∀ s, 0 < D s) (N : ℕ) (s s₀ : S) (E : S → Prop) :
    |(law B (rejectionAttemptCap N) N).prob
        (fun t => E (completed (run D next B (rejectionAttemptCap N) hB N s t) s₀)) -
      idealMass D next hD N s E| ≤ (1 / 2 : ℝ) ^ 13 :=
  (abort_event_error D next B (rejectionAttemptCap N) hB hD N s s₀ E).trans
    (rejection_cap_error_real N)

end Paper2.CappedSampler.Adaptive

#print axioms Paper2.CappedSampler.Adaptive.failure_le
#print axioms Paper2.CappedSampler.Adaptive.ideal_le_success_add_error
#print axioms Paper2.CappedSampler.Adaptive.abort_event_error
#print axioms Paper2.CappedSampler.Adaptive.scheduled_event_error
#print axioms Paper2.CappedSampler.Adaptive.inspectedBits_le
