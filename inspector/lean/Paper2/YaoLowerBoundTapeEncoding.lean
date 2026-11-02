import Paper2.CappedSamplerBits
import Paper2.YaoSelectorEvents

/-!
# Fair-bit implementation of the selector samples

Frozen source: Paper 2 v12, Appendix B, `yao:random-bits` and the independent
selector sampling specified before `yao:entry` in Section 7.

Each address is decoded by the executable little-endian binary equivalence
from `CappedSamplerBits`, not by a cardinality-only chosen bijection. The
weight and event equalities below hold for the entire labelled sample
array, including correlated events and the empty tape cases.

This is the finite selector component. The payload tape, complete matrix
generator, and machine-runtime accounting are separate obligations.
-/

namespace Paper2.Yao

open scoped BigOperators

/-- `q` independent blocks of exactly `b` fair bits. -/
noncomputable def selectorBitsLaw (q b : ℕ) : FiniteLaw (Fin q → Fin b → Bool) :=
  FiniteLaw.pi (fun _ : Fin q => CappedSampler.fairBits b)

/-- Decode every address by its actual binary expansion. -/
def decodeSelector (q b : ℕ) (x : Fin q → Fin b → Bool) : Fin q → Fin (2 ^ b) :=
  fun g => CappedSampler.bitsTicketEquiv b (x g)

/-- Coordinatewise binary decoding is a bijection, even for zero-length
words or an empty coordinate index. -/
def selectorEquiv (q b : ℕ) : (Fin q → Fin b → Bool) ≃ (Fin q → Fin (2 ^ b)) :=
  Equiv.piCongrRight (fun _ : Fin q => CappedSampler.bitsTicketEquiv b)

@[simp] theorem selectorEquiv_apply (q b : ℕ) (x : Fin q → Fin b → Bool) :
    selectorEquiv q b x = decodeSelector q b x := rfl

theorem decodeSelector_bijective (q b : ℕ) : Function.Bijective (decodeSelector q b) :=
  (selectorEquiv q b).bijective

/-- Pointwise probability preservation under actual binary decoding. -/
theorem selectorBitsLaw_weight (q b : ℕ) (x : Fin q → Fin b → Bool) :
    (selectorBitsLaw q b).weight x =
      (selectorLaw q (2 ^ b)).weight (decodeSelector q b x) := by
  simp [selectorBitsLaw, selectorLaw, FiniteLaw.pi, FiniteLaw.uniform,
    CappedSampler.fairBits_weight]

/-- Exact pushforward for every event, not merely coordinate rectangles. -/
theorem selectorBitsLaw_prob (q b : ℕ) (E : (Fin q → Fin (2 ^ b)) → Prop) :
    (selectorBitsLaw q b).prob (fun x => E (decodeSelector q b x)) =
      (selectorLaw q (2 ^ b)).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [selectorBitsLaw_weight]
  exact (selectorEquiv q b).sum_comp
    (fun c => if E c then (selectorLaw q (2 ^ b)).weight c else 0)

/-- Independent tapes for every labelled selector sample. -/
noncomputable def selectorArrayBitsLaw (samples q b : ℕ) :
    FiniteLaw (Fin samples → Fin q → Fin b → Bool) :=
  (selectorBitsLaw q b).iid samples

def decodeSelectorArray (samples q b : ℕ)
    (x : Fin samples → Fin q → Fin b → Bool) : Fin samples → Fin q → Fin (2 ^ b) :=
  fun z => decodeSelector q b (x z)

/-- Bijection on full labelled selector arrays. Duplicate decoded values
retain their distinct sample labels. -/
def selectorArrayEquiv (samples q b : ℕ) :
    (Fin samples → Fin q → Fin b → Bool) ≃ (Fin samples → Fin q → Fin (2 ^ b)) :=
  Equiv.piCongrRight (fun _ : Fin samples => selectorEquiv q b)

@[simp] theorem selectorArrayEquiv_apply (samples q b : ℕ)
    (x : Fin samples → Fin q → Fin b → Bool) :
    selectorArrayEquiv samples q b x = decodeSelectorArray samples q b x := rfl

theorem decodeSelectorArray_bijective (samples q b : ℕ) :
    Function.Bijective (decodeSelectorArray samples q b) :=
  (selectorArrayEquiv samples q b).bijective

/-- Pointwise equality of the full independent-array weights. This can be
multiplied with an independent payload weight to transport the joint law. -/
theorem selectorArrayBitsLaw_weight (samples q b : ℕ)
    (x : Fin samples → Fin q → Fin b → Bool) :
    (selectorArrayBitsLaw samples q b).weight x =
      ((selectorLaw q (2 ^ b)).iid samples).weight (decodeSelectorArray samples q b x) := by
  simp only [selectorArrayBitsLaw, FiniteLaw.iid, decodeSelectorArray]
  exact Finset.prod_congr rfl (fun _ _ => selectorBitsLaw_weight q b _)

/-- Exact full-array transport includes events chosen after observing the
sample; no product shape or independence of the event is required. -/
theorem selectorArrayBitsLaw_prob (samples q b : ℕ)
    (E : (Fin samples → Fin q → Fin (2 ^ b)) → Prop) :
    (selectorArrayBitsLaw samples q b).prob (fun x => E (decodeSelectorArray samples q b x)) =
      ((selectorLaw q (2 ^ b)).iid samples).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [selectorArrayBitsLaw_weight]
  exact (selectorArrayEquiv samples q b).sum_comp
    (fun C => if E C then ((selectorLaw q (2 ^ b)).iid samples).weight C else 0)

/-- Number of individual Boolean positions, not the number of tape values. -/
theorem selector_bit_count (samples q b : ℕ) :
    Fintype.card (Fin samples × Fin q × Fin b) = samples * q * b := by
  simp [Nat.mul_assoc]

/-- The law is uniform over exactly the stated number of fair-bit positions. -/
theorem selectorArrayBitsLaw_weight_uniform (samples q b : ℕ)
    (x : Fin samples → Fin q → Fin b → Bool) :
    (selectorArrayBitsLaw samples q b).weight x = ((2 : ℝ) ^ (samples * q * b))⁻¹ := by
  simp [selectorArrayBitsLaw, selectorBitsLaw, FiniteLaw.iid, FiniteLaw.pi,
    CappedSampler.fairBits_weight, ← inv_pow, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm]

end Paper2.Yao
