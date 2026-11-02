import Paper2.CappedSampler
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary

/-!
Interface for one capped fair-bit attempt in the locked Paper 2 v12
Appendix D algorithm.  This is a physical TM2 execution, not a machine for the
whole R-attempt loop or the full recursive sampler.
-/

namespace Paper2.CappedTicketMachine

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication (bitsValue)

def ticketWord {b : ℕ} (x : Fin b → Bool) : List Bool := List.ofFn x

theorem ticketWord_length {b : ℕ} (x : Fin b → Bool) : (ticketWord x).length = b := by
  simp [ticketWord]

theorem bitsValue_cons (c : Bool) (q : List Bool) :
    bitsValue (c :: q) = c.toNat + 2 * bitsValue q := by
  cases c <;> simp [bitsValue, Nat.bit_val, Nat.add_comm]

theorem bitsValue_ofFn_sum {b : ℕ} (x : Fin b → Bool) :
    bitsValue (List.ofFn x) = ∑ i : Fin b, (x i).toNat * 2 ^ i.val := by
  induction b with
  | zero => simp [bitsValue]
  | succ b ih =>
      rw [List.ofFn_succ, bitsValue_cons, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      rw [ih (fun i => x i.succ)]
      simp_rw [pow_succ]
      simp only [← mul_assoc, ← Finset.sum_mul]
      omega

theorem bitsValue_ofFn {b : ℕ} (x : Fin b → Bool) :
    bitsValue (ticketWord x) = (CappedSampler.bitsTicketEquiv b x).val := by
  rw [CappedSampler.bitsTicketEquiv_value, ticketWord, bitsValue_ofFn_sum]
  congr 1
  funext i
  cases x i <;> rfl

/-- The alphabet is supplied as a physical unary word of length `D-1`.
The machine's bounded comparison is non-strict; this predecessor convention
turns its output into the sampler's strict `ticket < D` range test. -/
def alphabetCap (D : ℕ) : List Bool := List.replicate (D - 1) true

/-- One bounded TM2 attempt. The program is fixed independently of `b` and
`D`; the ticket and alphabet cap are input stacks. The output starts with the
acceptance bit and then contains a unary copy of the truncated ticket value.
No Nat register or unit-cost input-dependent control is used by this run. -/
theorem one_attempt (D b : ℕ) (hD : 0 < D) (x : Fin b → Bool) :
    ∃ t c,
      t ≤ D * (4 * b + 5) ∧
      ProtocolBoundedUnary.run t
        (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
          (ticketWord x) (alphabetCap D) [] []) = c ∧
      c.l = none ∧
      c.stk 3 =
        decide ((CappedSampler.bitsTicketEquiv b x).val < D) ::
          List.replicate (min (CappedSampler.bitsTicketEquiv b x).val (D - 1)) true := by
  obtain ⟨t, c, ht, hr, hh, ho⟩ :=
    ProtocolBoundedUnary.bounded_run (ticketWord x) (alphabetCap D) []
  refine ⟨t, c, ?_, hr, hh, ?_⟩
  · simpa [alphabetCap, ticketWord_length, Nat.sub_add_cancel hD] using ht
  · rw [ho]
    simp only [ProtocolBoundedUnary.result, alphabetCap, List.length_replicate,
      bitsValue_ofFn, List.append_nil]
    congr 1
    have he : (CappedSampler.bitsTicketEquiv b x).val ≤ D - 1 ↔
        (CappedSampler.bitsTicketEquiv b x).val < D := by omega
    simp only [he]

/-- The machine's acceptance bit is exactly the one-attempt Paper 2
`runBits` result, not merely a same-distribution Boolean event. -/
theorem sampler_one_accepts_iff (D : ℕ)
    (x : Fin (Nat.clog 2 D) → Bool) :
    (CappedSampler.runBits D 1 (x, ())).isSome ↔
      (CappedSampler.bitsTicketEquiv (Nat.clog 2 D) x).val < D := by
  have hr : CappedSampler.runBits D 1 (x, ()) =
      if h : (CappedSampler.bitsTicketEquiv (Nat.clog 2 D) x).val < D
      then some (⟨_, h⟩ : Fin D) else none := rfl
  rw [hr]
  simp

theorem one_attempt_matches_sampler (D : ℕ) (hD : 0 < D)
    (x : Fin (Nat.clog 2 D) → Bool) :
    ∃ t c,
      t ≤ D * (4 * Nat.clog 2 D + 5) ∧
      ProtocolBoundedUnary.run t
        (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
          (ticketWord x) (alphabetCap D) [] []) = c ∧
      c.l = none ∧
      c.stk 3 =
        decide (CappedSampler.runBits D 1 (x, ())).isSome ::
          List.replicate
            (min (CappedSampler.bitsTicketEquiv (Nat.clog 2 D) x).val (D - 1)) true := by
  obtain ⟨t, c, ht, hr, hh, ho⟩ := one_attempt D (Nat.clog 2 D) hD x
  refine ⟨t, c, ht, hr, hh, ?_⟩
  rw [ho]
  congr 1
  by_cases hs : (CappedSampler.bitsTicketEquiv (Nat.clog 2 D) x).val < D
  · have hr := (sampler_one_accepts_iff D x).mpr hs
    simp [hs, hr]
  · have hr := (sampler_one_accepts_iff D x).not.mpr hs
    simp [hs, hr]





end Paper2.CappedTicketMachine
