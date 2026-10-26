import Paper2.FiniteSampling

/-!
# Fair bits as uniform tickets

Frozen source: v12, Appendix D, `app:implementation`, bounded random tapes
paragraph (lines 83 onward).  The encoding below is executable binary
expansion, not a cardinality-only chosen equivalence.  Its probability
identity holds for arbitrary ticket events.  Rejection, the cap, and the
recursive matrix generator are separate components.
-/

namespace Paper2.CappedSampler

open scoped BigOperators

/-- Little-endian binary encoding of exactly `b` bits. -/
def bitsTicketEquiv (b : ℕ) : (Fin b → Bool) ≃ Fin (2 ^ b) :=
  (Equiv.piCongrRight fun _ : Fin b => finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Binary expansion makes the computational meaning of the equivalence explicit. -/
theorem bitsTicketEquiv_value (b : ℕ) (x : Fin b → Bool) :
    (bitsTicketEquiv b x).val =
      ∑ i : Fin b, (finTwoEquiv.symm (x i)).val * 2 ^ i.val := rfl

@[simp] theorem bitsTicketEquiv_inverse (b : ℕ) (x : Fin b → Bool) :
    (bitsTicketEquiv b).symm (bitsTicketEquiv b x) = x :=
  (bitsTicketEquiv b).symm_apply_apply x

@[simp] theorem bitsTicketEquiv_right_inverse (b : ℕ) (j : Fin (2 ^ b)) :
    bitsTicketEquiv b ((bitsTicketEquiv b).symm j) = j :=
  (bitsTicketEquiv b).apply_symm_apply j

/-- A single actual fair Boolean bit. -/
noncomputable def fairBit : FiniteLaw Bool where
  weight _ := (2 : ℝ)⁻¹
  nonneg _ := by positivity
  total := by norm_num [Fintype.sum_bool]

/-- Exactly `b` independent fair bits, including the singleton empty tape. -/
noncomputable def fairBits (b : ℕ) : FiniteLaw (Fin b → Bool) :=
  fairBit.iid b

@[simp] theorem fairBits_weight (b : ℕ) (x : Fin b → Bool) :
    (fairBits b).weight x = (2 ^ b : ℝ)⁻¹ := by
  simp [fairBits, fairBit, FiniteLaw.iid, ← inv_pow]

/-- Fair bits push forward to the exact uniform ticket law.  The target
law is supplied only through its individual constant weights, so this
lemma can instantiate any equivalent uniform-ticket definition. -/
theorem fairBits_ticket_prob (b : ℕ) (ν : FiniteLaw (Fin (2 ^ b)))
    (hν : ∀ j, ν.weight j = (2 ^ b : ℝ)⁻¹)
    (E : Fin (2 ^ b) → Prop) :
    (fairBits b).prob (fun x => E (bitsTicketEquiv b x)) = ν.prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [fairBits_weight, hν]
  exact (bitsTicketEquiv b).sum_comp (fun j => if E j then (2 ^ b : ℝ)⁻¹ else 0)

/-- Each individual ticket has exactly its uniform mass. -/
theorem fairBits_ticket_singleton (b : ℕ) (j : Fin (2 ^ b)) :
    (fairBits b).prob (fun x => bitsTicketEquiv b x = j) = (2 ^ b : ℝ)⁻¹ := by
  classical
  unfold FiniteLaw.prob
  simp_rw [fairBits_weight]
  rw [(bitsTicketEquiv b).sum_comp (fun k => if k = j then (2 ^ b : ℝ)⁻¹ else 0)]
  simp

end Paper2.CappedSampler
