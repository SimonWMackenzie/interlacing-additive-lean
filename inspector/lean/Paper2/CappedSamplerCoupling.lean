import Paper2.CappedSampler
import Paper2.RationalTupleTransport

/-!
# Coupling capped fair-bit draws with ideal uniform draws

Frozen source: v12, `appendices/D-implementation.tex:83--102` (U15).
The coupling uses the actual bounded fair-bit algorithm. An independent
uniform value fills in an exhausted draw in the mathematical coupling only;
the bounded algorithm itself still returns `none` and does not use this value.
The ideal coordinate is proved uniform, and agreement fails exactly when the
actual cap is exhausted. No coupling or error bound is assumed as a field.

This file does not supply a machine-time model or the manuscript-specific
bound on the number of elementary draws.
-/

namespace Paper2.CappedSampler

open scoped BigOperators

/-- Complete a failed draw with an independent auxiliary value. This is a
mathematical coupling coordinate, not an extra operation of the sampler. -/
def completed {α : Type*} (o : Option α) (a : α) : α := o.getD a

theorem completion_atom {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → Option β) (b : β) :
    (μ.prod ν).prob (fun z => completed (f z.1) z.2 = b) =
      μ.prob (fun a => f a = some b) + μ.prob (fun a => f a = none) * ν.weight b := by
  classical
  rw [FiniteLaw.prod_prob μ ν (fun a x => completed (f a) x = b)]
  have he (a : α) :
      μ.weight a * ν.prob (fun x => completed (f a) x = b) =
        (if f a = some b then μ.weight a else 0) +
          (if f a = none then μ.weight a else 0) * ν.weight b := by
    cases hf : f a with
    | none => simp [completed]
    | some c => by_cases hc : c = b <;> simp [completed, hc]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  unfold FiniteLaw.prob
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a = some b <;> simp [ha]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a = none <;> simp [ha]

/-- Sample the actual finite fair-bit tape and an independent auxiliary
uniform value. Only the first coordinate is read by the bounded algorithm. -/
noncomputable def couplingLaw (D R : ℕ) (hD : 0 < D) :
    FiniteLaw (BitTape (Nat.clog 2 D) R × Fin D) :=
  (bitTapeLaw (Nat.clog 2 D) R).prod (uniformTicket D hD)

def idealOutput (D R : ℕ) (z : BitTape (Nat.clog 2 D) R × Fin D) : Fin D :=
  completed (runBits D R z.1) z.2

theorem bit_failure_exact (D R : ℕ) :
    (bitTapeLaw (Nat.clog 2 D) R).prob (fun t => runBits D R t = none) =
      rejectionMass D (ticketSize D) ^ R := by
  unfold runBits
  rw [bitTape_prob (Nat.clog 2 D) R (fun t => run D (ticketSize D) R t = none)]
  exact failure_exact D (ticketSize D) R (ticketSize_pos D) (le_ticketSize D)

/-- The completed coordinate is exactly uniform, including a zero attempt cap. -/
theorem ideal_atom (D R : ℕ) (hD : 0 < D) (a : Fin D) :
    (couplingLaw D R hD).prob (fun z => idealOutput D R z = a) = (D : ℝ)⁻¹ := by
  unfold couplingLaw idealOutput
  rw [completion_atom, bit_accepted_exact D R hD a, bit_failure_exact]
  change (1 - rejectionMass D (ticketSize D) ^ R) / D +
    rejectionMass D (ticketSize D) ^ R * (D : ℝ)⁻¹ = (D : ℝ)⁻¹
  ring

/-- Every event, not only singleton events, has its ideal uniform law. -/
theorem ideal_prob (D R : ℕ) (hD : 0 < D) (E : Fin D → Prop) :
    (couplingLaw D R hD).prob (fun z => E (idealOutput D R z)) =
      (uniformTicket D hD).prob E :=
  FiniteLaw.prob_preimage_eq_of_fibres (couplingLaw D R hD) (uniformTicket D hD)
    (idealOutput D R) (ideal_atom D R hD) E

@[simp] theorem disagrees_iff (D R : ℕ) (z : BitTape (Nat.clog 2 D) R × Fin D) :
    runBits D R z.1 ≠ some (idealOutput D R z) ↔ runBits D R z.1 = none := by
  unfold idealOutput completed
  cases h : runBits D R z.1 <;> simp

theorem actual_marginal (D R : ℕ) (hD : 0 < D)
    (E : BitTape (Nat.clog 2 D) R → Prop) :
    (couplingLaw D R hD).prob (fun z => E z.1) =
      (bitTapeLaw (Nat.clog 2 D) R).prob E := by
  classical
  unfold couplingLaw
  rw [FiniteLaw.prod_prob (bitTapeLaw (Nat.clog 2 D) R) (uniformTicket D hD)
    (fun t _ => E t)]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a <;> simp [ha, (uniformTicket D hD).total]

/-- The coupling disagrees exactly on exhaustion of the concrete sampler. -/
theorem disagreement_exact (D R : ℕ) (hD : 0 < D) :
    (couplingLaw D R hD).prob
        (fun z => runBits D R z.1 ≠ some (idealOutput D R z)) =
      rejectionMass D (ticketSize D) ^ R := by
  simp_rw [disagrees_iff]
  rw [actual_marginal D R hD (fun t => runBits D R t = none), bit_failure_exact]

theorem disagreement_le (D R : ℕ) (hD : 0 < D) :
    (couplingLaw D R hD).prob
        (fun z => runBits D R z.1 ≠ some (idealOutput D R z)) ≤ (1 / 2 : ℝ) ^ R := by
  simp_rw [disagrees_iff]
  rw [actual_marginal D R hD (fun t => runBits D R t = none)]
  exact bit_failure_le D R hD

/-- A coupling loses no more event mass than its disagreement probability. -/
theorem event_prob_le_add_disagreement {α β : Type*} [Fintype α]
    (μ : FiniteLaw α) (f g : α → β) (E : β → Prop) :
    μ.prob (fun a => E (f a)) ≤
      μ.prob (fun a => E (g a)) + μ.prob (fun a => f a ≠ g a) := by
  classical
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : f a = g a
  · simp [h]
  · by_cases hf : E (f a) <;> by_cases hg : E (g a) <;> simp [h, hf, hg, μ.nonneg]

/-- Replacing exhaustion by any fixed output changes any event probability
by at most the cap-exhaustion bound. The ideal distribution is proved above. -/
theorem abort_event_error (D R : ℕ) (hD : 0 < D) (a₀ : Fin D) (E : Fin D → Prop) :
    |(bitTapeLaw (Nat.clog 2 D) R).prob (fun t => E (completed (runBits D R t) a₀)) -
        (uniformTicket D hD).prob E| ≤ (1 / 2 : ℝ) ^ R := by
  let μ := couplingLaw D R hD
  let f : BitTape (Nat.clog 2 D) R × Fin D → Fin D :=
    fun z => completed (runBits D R z.1) a₀
  let g := idealOutput D R
  have hab : μ.prob (fun z => f z ≠ g z) ≤ (1 / 2 : ℝ) ^ R := by
    apply (μ.prob_mono (E := fun z => f z ≠ g z)
      (F := fun z => runBits D R z.1 = none) ?_).trans
    · rw [actual_marginal D R hD (fun t => runBits D R t = none)]
      exact bit_failure_le D R hD
    · intro z hz
      cases hr : runBits D R z.1 with
      | none => rfl
      | some a => exact False.elim (hz (by simp [f, g, idealOutput, completed, hr]))
  have hfg := event_prob_le_add_disagreement μ f g E
  have hgf := event_prob_le_add_disagreement μ g f E
  have hsym : μ.prob (fun z => g z ≠ f z) = μ.prob (fun z => f z ≠ g z) := by
    simp_rw [ne_comm]
  rw [hsym] at hgf
  have hf : μ.prob (fun z => E (f z)) =
      (bitTapeLaw (Nat.clog 2 D) R).prob (fun t => E (completed (runBits D R t) a₀)) :=
    actual_marginal D R hD (fun t => E (completed (runBits D R t) a₀))
  have hg : μ.prob (fun z => E (g z)) = (uniformTicket D hD).prob E := ideal_prob D R hD E
  rw [hf, hg] at hfg hgf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Paper2.CappedSampler

#print axioms Paper2.CappedSampler.ideal_prob
#print axioms Paper2.CappedSampler.disagreement_exact
#print axioms Paper2.CappedSampler.abort_event_error
