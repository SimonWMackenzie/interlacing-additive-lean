import CurrentAdditive.RestrictionBridge

/-! Private source-specific prefix readout for v27 `det:fullboost`. The
post-prefix suffix obstruction remains separate. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2
open Workspace.Types.Protocol

variable {I X S : Type*} [Fintype I] [Fintype X] [Fintype S]

private theorem positive_event_nonempty {T : Type*} [Fintype T]
    (ρ : FiniteLaw T) (E : Set T) (h : 0 < ρ.prob (· ∈ E)) :
    E.Nonempty := by
  by_contra hn
  have hall : ∀ t, t ∉ E := by intro t ht; exact hn ⟨t,ht⟩
  have hz : ρ.prob (· ∈ E) = 0 := by simp [FiniteLaw.prob, hall]
  linarith

/-- The manuscript's `a`-message prefix for full-strength amplification.
For `a=0`, more than `2^(-1)` blocks means one block. For `a≥1`, the
integer threshold is `2^(a-1)+1`. -/
theorem full_prefix_state
    (μ : FiniteLaw X) (ν : FiniteLaw S)
    (F : (I × X) → S → Bool) (Q : Finset I)
    (R : I → Set X) (Y : Set S)
    (Dbase a : ℕ) (x : ℝ)
    (hDbase : 1 ≤ Dbase) (hx : 0 < x)
    (hQ : (if a = 0 then 1 else 2^(a-1)+1) ≤ Q.card)
    (hR : ∀ i ∈ Q, (2 : ℝ)^a * x ≤ μ.prob (· ∈ R i))
    (hY : 0 < ν.prob (· ∈ Y))
    (hD : Compression.restrictionD F (rowRectangle Q R) Y ≤ Dbase+a-1) :
    ∃ (A B : ℕ) (Q' : Finset I) (R' : I → Set X) (Y' : Set S)
      (P' : Protocol (I × X) S Bool),
      A + B = a ∧ 1 ≤ Q'.card ∧
      (B ≥ 1 → 2^(B-1)+1 ≤ Q'.card) ∧
      (∀ i ∈ Q', (2 : ℝ)^B * x ≤ μ.prob (· ∈ R' i)) ∧
      (1 : ℝ) / ((2 : ℝ)^B) ≤
        ν.prob (· ∈ Y') / ν.prob (· ∈ Y) ∧
      Q' ⊆ Q ∧ (∀ i ∈ Q', R' i ⊆ R i) ∧ Y' ⊆ Y ∧
      P'.cost ≤ Dbase-1 ∧
      (∀ i ∈ Q', ∀ u ∈ R' i, ∀ s ∈ Y',
        P'.eval (i,u) s = F (i,u) s) := by
  have hQone : 1 ≤ Q.card := by
    by_cases ha0 : a = 0
    · simpa [ha0] using hQ
    · have hpow := Nat.zero_le (2^(a-1))
      simp [ha0] at hQ
      omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
  have hri : 0 < μ.prob (· ∈ R i) :=
    lt_of_lt_of_le (mul_pos (by positivity) hx) (hR i hi)
  obtain ⟨u,hu⟩ := positive_event_nonempty μ (R i) hri
  have hnonempty : (rowRectangle Q R).Nonempty ∧ Y.Nonempty :=
    ⟨⟨(i,u), ⟨hi,hu⟩⟩, positive_event_nonempty ν Y hY⟩
  obtain ⟨A, B, Q', R', Y', P', hab, hQsub, hRsub, hYsub,
    hcount, hrow, hcol, hsuf, heval⟩ :=
    restriction_prefix μ ν F Q R Y hnonempty.1 hnonempty.2
      a (Dbase+a-1) hD (by omega)
  refine ⟨A, B, Q', R', Y', P', hab, ?_, ?_, ?_, ?_,
    hQsub, hRsub, hYsub, ?_, heval⟩
  · by_contra hn
    have hz : Q'.card = 0 := by omega
    rw [hz, mul_zero] at hcount
    omega
  · intro hB
    have ha0 : a ≠ 0 := by omega
    have hlarge : 2^(a-1)+1 ≤ Q.card := by simpa [ha0] using hQ
    by_contra hn
    have hsmall : Q'.card ≤ 2^(B-1) := by omega
    have hm := Nat.mul_le_mul_left (2^A) hsmall
    have hexp : A+(B-1)=a-1 := by omega
    have hp : 2^A * 2^(B-1) = 2^(a-1) := by rw [← pow_add, hexp]
    rw [hp] at hm
    omega
  · intro i hi
    have hstart := hR i (hQsub hi)
    have hremain := hrow i hi
    have hscaled : (2 : ℝ)^A * ((2 : ℝ)^B * x) ≤
        (2 : ℝ)^A * μ.prob (· ∈ R' i) := by
      calc
        _ = (2 : ℝ)^a * x := by rw [← hab, pow_add]; ring
        _ ≤ μ.prob (· ∈ R i) := hstart
        _ ≤ _ := hremain
    exact (mul_le_mul_iff_of_pos_left
      (by positivity : (0 : ℝ) < 2 ^ A)).mp hscaled
  · have hcond := conditional_column_mass ν Y Y Y' B hY hcol
    have hone : ν.prob (· ∈ Y) / ν.prob (· ∈ Y) = 1 :=
      div_self hY.ne'
    rw [hone] at hcond
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ B)).2
      (by simpa [mul_comm] using hcond)
  · omega

#print axioms CurrentAdditive.ArbitraryPrefix.full_prefix_state

end CurrentAdditive.ArbitraryPrefix
