import Paper2.FiniteSampling
import Paper2.SamplingBounds
import Paper2.CappedSamplerBits

/-!
# A bounded rejection sampler on an explicit independent ticket tape

Frozen source: v12, `appendices/D-implementation.tex:83--102` (U15).
Each ticket is an integer in a power-of-two range. The sampler returns the
first in-range ticket, or failure after a fixed number of attempts.

The finite algorithm, its pointwise bound, and its probability law are
proved here. This component does not construct the manuscript's recursive
labels, bound their adaptive draw count, or establish machine running time.
-/

namespace Paper2.CappedSampler

open scoped BigOperators

/-- A concrete tape consisting of exactly `R` tickets. -/
def Tape (M : ℕ) : ℕ → Type
  | 0 => Unit
  | R + 1 => Fin M × Tape M R

instance tapeFintype (M R : ℕ) : Fintype (Tape M R) := by
  induction R with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ R ih => exact inferInstanceAs (Fintype (Fin M × Tape M R))

/-- Uniform ticket, including the singleton power-of-two range. -/
noncomputable def uniformTicket (M : ℕ) (hM : 0 < M) : FiniteLaw (Fin M) where
  weight _ := (M : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg M)
  total := by simp [mul_inv_cancel₀ (by exact_mod_cast hM.ne' : (M : ℝ) ≠ 0)]

/-- The tape law is the actual iterated product of independent tickets. -/
noncomputable def tapeLaw (M : ℕ) (hM : 0 < M) : (R : ℕ) → FiniteLaw (Tape M R)
  | 0 => { weight := fun _ => 1, nonneg := fun _ => by norm_num, total := by simp [Tape] }
  | R + 1 => (uniformTicket M hM).prod (tapeLaw M hM R)

/-- Bounded first-accepted-ticket algorithm; no choice or search oracle is used. -/
def run (D M : ℕ) : (R : ℕ) → Tape M R → Option (Fin D)
  | 0, _ => none
  | R + 1, t => if h : t.1.val < D then some ⟨t.1.val, h⟩ else run D M R t.2

/-- Number of tickets inspected by the same algorithm. -/
def used (D M : ℕ) : (R : ℕ) → Tape M R → ℕ
  | 0, _ => 0
  | R + 1, t => if t.1.val < D then 1 else 1 + used D M R t.2

theorem used_le (D M R : ℕ) (t : Tape M R) : used D M R t ≤ R := by
  induction R with
  | zero => simp [used]
  | succ R ih =>
    simp only [used]
    split_ifs
    · omega
    · have := ih t.2; omega

/-- If one ticket uses `b` bits, every tape consumes at most `b*R` bits. -/
theorem bit_budget (D M R b : ℕ) (t : Tape M R) :
    b * used D M R t ≤ b * R := Nat.mul_le_mul_left b (used_le D M R t)

theorem output_in_range (D M R : ℕ) (t : Tape M R) (a : Fin D)
    (_h : run D M R t = some a) : a.val < D := a.isLt

/-- Probability of rejecting one ticket. -/
noncomputable def rejectionMass (D M : ℕ) : ℝ := (M - D : ℕ) / M

theorem rejected_ticket_count (D M : ℕ) (hDM : D ≤ M) :
    (Finset.univ.filter (fun i : Fin M => ¬ i.val < D)).card = M - D := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_subtype_compl, Fintype.card_fin_lt_of_le hDM, Fintype.card_fin]

theorem rejected_ticket_sum (D M : ℕ) (hDM : D ≤ M) (c : ℝ) :
    (∑ i : Fin M, if i.val < D then 0 else c) = (M - D : ℕ) * c := by
  have hh (i : Fin M) : (if i.val < D then (0 : ℝ) else c) =
      (if ¬i.val < D then c else 0) := by split_ifs <;> rfl
  simp_rw [hh]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, rejected_ticket_count D M hDM]

theorem failure_recurrence (D M R : ℕ) (hM : 0 < M) (hDM : D ≤ M) :
    (tapeLaw M hM (R + 1)).prob (fun t => run D M (R + 1) t = none) =
      rejectionMass D M * (tapeLaw M hM R).prob (fun t => run D M R t = none) := by
  change ((uniformTicket M hM).prod (tapeLaw M hM R)).prob
    (fun t => (if h : t.1.val < D then some (⟨t.1.val, h⟩ : Fin D)
      else run D M R t.2) = none) = _
  rw [FiniteLaw.prod_prob (uniformTicket M hM) (tapeLaw M hM R)
    (fun i t => (if h : i.val < D then some (⟨i.val, h⟩ : Fin D)
      else run D M R t) = none)]
  have he (i : Fin M) :
      (uniformTicket M hM).weight i *
        (tapeLaw M hM R).prob (fun t =>
          (if h : i.val < D then some (⟨i.val, h⟩ : Fin D) else run D M R t) = none) =
      if i.val < D then 0 else
        (M : ℝ)⁻¹ * (tapeLaw M hM R).prob (fun t => run D M R t = none) := by
    by_cases hi : i.val < D <;> simp [hi, uniformTicket]
  simp_rw [he]
  rw [rejected_ticket_sum D M hDM]
  simp only [rejectionMass, div_eq_mul_inv, mul_assoc]

theorem failure_exact (D M R : ℕ) (hM : 0 < M) (hDM : D ≤ M) :
    (tapeLaw M hM R).prob (fun t => run D M R t = none) =
      rejectionMass D M ^ R := by
  induction R with
  | zero => simp [run]
  | succ R ih => rw [failure_recurrence D M R hM hDM, ih, pow_succ'];

theorem accepted_recurrence (D M R : ℕ) (hM : 0 < M) (hDM : D ≤ M) (a : Fin D) :
    (tapeLaw M hM (R + 1)).prob (fun t => run D M (R + 1) t = some a) =
      (M : ℝ)⁻¹ + rejectionMass D M *
        (tapeLaw M hM R).prob (fun t => run D M R t = some a) := by
  change ((uniformTicket M hM).prod (tapeLaw M hM R)).prob
    (fun t => (if h : t.1.val < D then some (⟨t.1.val, h⟩ : Fin D)
      else run D M R t.2) = some a) = _
  rw [FiniteLaw.prod_prob (uniformTicket M hM) (tapeLaw M hM R)
    (fun i t => (if h : i.val < D then some (⟨i.val, h⟩ : Fin D)
      else run D M R t) = some a)]
  have he (i : Fin M) :
      (uniformTicket M hM).weight i *
        (tapeLaw M hM R).prob (fun t =>
          (if h : i.val < D then some (⟨i.val, h⟩ : Fin D) else run D M R t) = some a) =
      (if i.val = a.val then (M : ℝ)⁻¹ else 0) +
        (if i.val < D then 0 else
          (M : ℝ)⁻¹ * (tapeLaw M hM R).prob (fun t => run D M R t = some a)) := by
    by_cases hi : i.val < D
    · by_cases ha : i.val = a.val <;> simp [hi, ha, Fin.ext_iff, uniformTicket]
    · have ha : i.val ≠ a.val := by intro h; rw [h] at hi; exact hi a.isLt
      simp [hi, ha, uniformTicket]
  simp_rw [he]
  rw [Finset.sum_add_distrib, rejected_ticket_sum D M hDM]
  have hs : (∑ i : Fin M, if i.val = a.val then (M : ℝ)⁻¹ else 0) = (M : ℝ)⁻¹ := by
    let aM : Fin M := ⟨a.val, lt_of_lt_of_le a.isLt hDM⟩
    have hh (i : Fin M) : i.val = a.val ↔ i = aM := by
      exact (@Fin.ext_iff M i aM).symm
    simp_rw [hh]
    simp
  rw [hs]
  simp only [rejectionMass, div_eq_mul_inv, mul_assoc]

/-- Every accepted value has its exact truncated-geometric probability. -/
theorem accepted_exact (D M R : ℕ) (hD : 0 < D) (hM : 0 < M)
    (hDM : D ≤ M) (a : Fin D) :
    (tapeLaw M hM R).prob (fun t => run D M R t = some a) =
      (1 - rejectionMass D M ^ R) / D := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hq : rejectionMass D M = 1 - (D : ℝ) / M := by
    unfold rejectionMass
    rw [Nat.cast_sub hDM]
    field_simp
  induction R with
  | zero => simp [run]
  | succ R ih =>
    rw [accepted_recurrence D M R hM hDM a, ih, pow_succ']
    rw [hq]
    field_simp
    ring

/-- Power-of-two ticket range used by the manuscript's fair-bit algorithm. -/
def ticketSize (D : ℕ) : ℕ := 2 ^ Nat.clog 2 D

theorem ticketSize_pos (D : ℕ) : 0 < ticketSize D := pow_pos (by decide) _

theorem le_ticketSize (D : ℕ) : D ≤ ticketSize D := Nat.le_pow_clog (by decide) D

theorem ticketSize_le_twice (D : ℕ) (hD : 0 < D) : ticketSize D ≤ 2 * D := by
  by_cases h : D = 1
  · subst D; simp [ticketSize]
  · have hd : 1 < D := by omega
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hd
    simp only [Nat.pred_eq_sub_one] at hp
    have he : Nat.clog 2 D = (Nat.clog 2 D - 1) + 1 := by
      have := Nat.clog_pos (by decide : 1 < 2) hd
      omega
    unfold ticketSize
    rw [he, pow_succ]
    omega

theorem rejectionMass_nonneg (D M : ℕ) : 0 ≤ rejectionMass D M := by
  unfold rejectionMass; positivity

theorem rejectionMass_le_half (D : ℕ) (hD : 0 < D) :
    rejectionMass D (ticketSize D) ≤ (1 / 2 : ℝ) := by
  have hc : (ticketSize D : ℝ) ≤ 2 * D := by exact_mod_cast ticketSize_le_twice D hD
  have hp : (0 : ℝ) < ticketSize D := by exact_mod_cast ticketSize_pos D
  unfold rejectionMass
  rw [Nat.cast_sub (le_ticketSize D)]
  apply (div_le_iff₀ hp).mpr
  linarith

/-- Failure of the actual bounded algorithm has probability at most `2^-R`. -/
theorem failure_le_half_pow (D R : ℕ) (hD : 0 < D) :
    (tapeLaw (ticketSize D) (ticketSize_pos D) R).prob
      (fun t => run D (ticketSize D) R t = none) ≤ (1 / 2 : ℝ) ^ R := by
  rw [failure_exact D (ticketSize D) R (ticketSize_pos D) (le_ticketSize D)]
  exact pow_le_pow_left₀ (rejectionMass_nonneg _ _) (rejectionMass_le_half D hD) _

/-- Positive success probability when the cap permits at least one attempt. -/
theorem success_mass_pos (D R : ℕ) (hD : 0 < D) (hR : 0 < R) :
    0 < 1 - (tapeLaw (ticketSize D) (ticketSize_pos D) R).prob
      (fun t => run D (ticketSize D) R t = none) := by
  have hf := failure_le_half_pow D R hD
  have hp : (1 / 2 : ℝ) ^ R ≤ (1 / 2 : ℝ) :=
    pow_le_of_le_one (by norm_num) (by norm_num) hR.ne'
  linarith

/-- The actual accepted output has uniform conditional probability on every value.
This conditions one fixed-denominator draw, not a whole adaptive generator. -/
theorem accepted_conditional_uniform (D R : ℕ) (hD : 0 < D) (hR : 0 < R) (a : Fin D) :
    (tapeLaw (ticketSize D) (ticketSize_pos D) R).prob
        (fun t => run D (ticketSize D) R t = some a) /
      (1 - (tapeLaw (ticketSize D) (ticketSize_pos D) R).prob
        (fun t => run D (ticketSize D) R t = none)) = (D : ℝ)⁻¹ := by
  have hn := ne_of_gt (success_mass_pos D R hD hR)
  rw [failure_exact D (ticketSize D) R (ticketSize_pos D) (le_ticketSize D)] at hn ⊢
  rw [accepted_exact D (ticketSize D) R hD (ticketSize_pos D) (le_ticketSize D) a]
  field_simp

/-- A tape with `R` explicit blocks, each containing `b` fair bits. -/
def BitTape (b : ℕ) : ℕ → Type
  | 0 => Unit
  | R + 1 => (Fin b → Bool) × BitTape b R

instance bitTapeFintype (b R : ℕ) : Fintype (BitTape b R) := by
  induction R with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ R ih => exact inferInstanceAs (Fintype ((Fin b → Bool) × BitTape b R))

/-- All bits in all blocks are independent. -/
noncomputable def bitTapeLaw (b : ℕ) : (R : ℕ) → FiniteLaw (BitTape b R)
  | 0 => { weight := fun _ => 1, nonneg := fun _ => by norm_num, total := by simp [BitTape] }
  | R + 1 => (fairBits b).prod (bitTapeLaw b R)

/-- Executable block-by-block binary decoding. -/
def bitTapeEquiv (b : ℕ) : (R : ℕ) → BitTape b R ≃ Tape (2 ^ b) R
  | 0 => Equiv.refl Unit
  | R + 1 => (bitsTicketEquiv b).prodCongr (bitTapeEquiv b R)

theorem bitTapeLaw_weight (b R : ℕ) (x : BitTape b R) :
    (bitTapeLaw b R).weight x = ((2 ^ b : ℝ)⁻¹) ^ R := by
  induction R with
  | zero => simp [bitTapeLaw]
  | succ R ih =>
    change (fairBits b).weight x.1 * (bitTapeLaw b R).weight x.2 = _
    rw [fairBits_weight, ih, pow_succ']

theorem tapeLaw_weight (M R : ℕ) (hM : 0 < M) (x : Tape M R) :
    (tapeLaw M hM R).weight x = ((M : ℝ)⁻¹) ^ R := by
  induction R with
  | zero => simp [tapeLaw]
  | succ R ih =>
    change (M : ℝ)⁻¹ * (tapeLaw M hM R).weight x.2 = _
    rw [ih, pow_succ']

/-- Every event in the decoded ticket tape has exactly its independent-ticket mass. -/
theorem bitTape_prob (b R : ℕ) (E : Tape (2 ^ b) R → Prop) :
    (bitTapeLaw b R).prob (fun x => E (bitTapeEquiv b R x)) =
      (tapeLaw (2 ^ b) (pow_pos (by decide) b) R).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [bitTapeLaw_weight, tapeLaw_weight]
  push_cast
  exact (bitTapeEquiv b R).sum_comp (fun t => if E t then ((2 ^ b : ℝ)⁻¹) ^ R else 0)

/-- The actual fair-bit sampler uses `ceil(log₂ D)` bits per attempt. -/
def runBits (D R : ℕ) (t : BitTape (Nat.clog 2 D) R) : Option (Fin D) :=
  run D (ticketSize D) R (bitTapeEquiv (Nat.clog 2 D) R t)

theorem bit_failure_le (D R : ℕ) (hD : 0 < D) :
    (bitTapeLaw (Nat.clog 2 D) R).prob (fun t => runBits D R t = none) ≤
      (1 / 2 : ℝ) ^ R := by
  unfold runBits
  rw [bitTape_prob (Nat.clog 2 D) R (fun t => run D (ticketSize D) R t = none)]
  exact failure_le_half_pow D R hD

theorem bit_accepted_exact (D R : ℕ) (hD : 0 < D) (a : Fin D) :
    (bitTapeLaw (Nat.clog 2 D) R).prob (fun t => runBits D R t = some a) =
      (1 - rejectionMass D (ticketSize D) ^ R) / D := by
  unfold runBits
  rw [bitTape_prob (Nat.clog 2 D) R (fun t => run D (ticketSize D) R t = some a)]
  exact accepted_exact D (ticketSize D) R hD (ticketSize_pos D) (le_ticketSize D) a

/-- Exact conditional law of the fair-bit implementation of one draw. -/
theorem bit_accepted_conditional_uniform (D R : ℕ) (hD : 0 < D) (hR : 0 < R)
    (a : Fin D) :
    (bitTapeLaw (Nat.clog 2 D) R).prob (fun t => runBits D R t = some a) /
      (1 - (bitTapeLaw (Nat.clog 2 D) R).prob (fun t => runBits D R t = none)) =
        (D : ℝ)⁻¹ := by
  unfold runBits
  rw [bitTape_prob (Nat.clog 2 D) R (fun t => run D (ticketSize D) R t = some a),
    bitTape_prob (Nat.clog 2 D) R (fun t => run D (ticketSize D) R t = none)]
  exact accepted_conditional_uniform D R hD hR a

/-- Pointwise inspected-bit budget; the complete supplied tape has this same fixed cap. -/
theorem used_bit_budget (D R : ℕ) (t : BitTape (Nat.clog 2 D) R) :
    Nat.clog 2 D * used D (ticketSize D) R (bitTapeEquiv (Nat.clog 2 D) R t) ≤
      Nat.clog 2 D * R := bit_budget D (ticketSize D) R (Nat.clog 2 D) _

@[simp] theorem zero_cap (D : ℕ) (t : BitTape (Nat.clog 2 D) 0) :
    runBits D 0 t = none := rfl

theorem singleton_zero_bits : Nat.clog 2 1 = 0 := by simp

theorem singleton_success (R : ℕ) (hR : 0 < R) (t : BitTape (Nat.clog 2 1) R) :
    runBits 1 R t = some ⟨0, by decide⟩ := by
  cases R with
  | zero => omega
  | succ R => simp [runBits, run, ticketSize]

end Paper2.CappedSampler
