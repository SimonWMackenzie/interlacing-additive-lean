import CurrentAdditive.ArbitraryPrefix
import Paper2.Compression
import Workspace.UpperBound

namespace CurrentAdditive.ArbitraryPrefix

open Paper2
open Workspace.Types.CommComplexity
open Workspace.Types.Protocol

variable {I X S : Type*} [Fintype I] [Fintype X] [Fintype S]

/-- The actual restriction complexity is attained by a finite protocol on
the genuine retained subtype inputs. -/
theorem restrictionD_minimizer (F : (I × X) → S → Bool)
    (U : Set (I × X)) (V : Set S) :
    ∃ P : Protocol U V Bool,
      P.cost = Compression.restrictionD F U V ∧
      P.Computes (fun a s => F a.1 s.1) := by
  classical
  let f : U → V → Bool := fun a s => F a.1 s.1
  have hne : (AchievableCosts f).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty f
  have hmem : D f ∈ AchievableCosts f := by
    simpa [D] using (Nat.sInf_mem hne)
  obtain ⟨P, hPcost, hPcomp⟩ := hmem
  refine ⟨P, ?_, hPcomp⟩
  simpa [f, Compression.restrictionD] using hPcost

/-- The source's starting row rectangle. Each block keeps its own base-row
set, while columns remain indexed labels (duplicates stay distinct). -/
def rowRectangle (Q : Finset I) (R : I → Set X) : Set (I × X) :=
  {a | a.1 ∈ Q ∧ a.2 ∈ R a.1}

/-- Starting with an optimal protocol for the actual retained matrix, follow
an arbitrary speaking schedule for a fixed total prefix. -/
theorem restriction_prefix
    (μ : FiniteLaw X) (ν : FiniteLaw S)
    (F : (I × X) → S → Bool) (Q : Finset I)
    (R : I → Set X) (C : Set S)
    (hrow_nonempty : (rowRectangle Q R).Nonempty)
    (hcol_nonempty : C.Nonempty)
    (k H : ℕ) (hD : Compression.restrictionD F (rowRectangle Q R) C ≤ H)
    (hk : k ≤ H) :
    ∃ (A B : ℕ) (Q' : Finset I) (R' : I → Set X) (C' : Set S)
      (P' : Protocol (I × X) S Bool),
      A + B = k ∧ Q' ⊆ Q ∧
      (∀ i ∈ Q', R' i ⊆ R i) ∧ C' ⊆ C ∧
      Q.card ≤ 2 ^ A * Q'.card ∧
      (∀ i ∈ Q', μ.prob (· ∈ R i) ≤
        (2 : ℝ) ^ A * μ.prob (· ∈ R' i)) ∧
      ν.prob (· ∈ C) ≤ (2 : ℝ) ^ B * ν.prob (· ∈ C') ∧
      P'.cost ≤ H - k ∧
      (∀ i ∈ Q', ∀ x ∈ R' i, ∀ s ∈ C',
        P'.eval (i,x) s = F (i,x) s) := by
  obtain ⟨P, hpCost, hpComp⟩ :=
    restrictionD_minimizer F (rowRectangle Q R) C
  obtain ⟨Pfull, hfullCost, hfullEval⟩ :=
    extend_restriction_protocol (rowRectangle Q R) C
      hrow_nonempty hcol_nonempty P
  have hbound : Pfull.cost ≤ H := by omega
  obtain ⟨A, B, Q', R', C', P', hab, hQ, hR, hC,
    hcount, hrow, hcol, hsuf, heval⟩ :=
    fixed_total_prefix μ ν (padTo H Pfull) Q R C k H
      (le_of_eq (padTo_cost H Pfull hbound)) hk
  refine ⟨A, B, Q', R', C', P', hab, hQ, hR, hC,
    hcount, hrow, hcol, hsuf, ?_⟩
  intro i hi x hx s hs
  rw [heval i hi x hx s hs, padTo_eval]
  have hqi : i ∈ Q := hQ hi
  have hxi : x ∈ R i := hR i hi hx
  have hsi : s ∈ C := hC hs
  rw [hfullEval (i,x) ⟨hqi, hxi⟩ s hsi]
  exact hpComp ⟨(i,x), ⟨hqi,hxi⟩⟩ ⟨s,hsi⟩

private theorem nonempty_of_prob_pos (μ : FiniteLaw X) (E : Set X)
    (h : 0 < μ.prob (· ∈ E)) : E.Nonempty := by
  by_contra hn
  have hall : ∀ x, x ∉ E := by
    intro x hx
    exact hn ⟨x, hx⟩
  have hz : μ.prob (· ∈ E) = 0 := by
    simp [FiniteLaw.prob, hall]
  linarith

private theorem initial_nonempty (μ : FiniteLaw X) (ν : FiniteLaw S)
    (Q : Finset I) (R : I → Set X) (C : Set S)
    (x c : ℝ) (hx : 0 < x) (hc : 0 < c)
    (hQ : 1 ≤ Q.card)
    (hR : ∀ i ∈ Q, x ≤ μ.prob (· ∈ R i))
    (hC : c ≤ ν.prob (· ∈ C)) :
    (rowRectangle Q R).Nonempty ∧ C.Nonempty := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
  have hri : 0 < μ.prob (· ∈ R i) := lt_of_lt_of_le hx (hR i hi)
  obtain ⟨u, hu⟩ := nonempty_of_prob_pos μ (R i) hri
  exact ⟨⟨(i,u), ⟨hi,hu⟩⟩,
    nonempty_of_prob_pos ν C (lt_of_lt_of_le hc hC)⟩

/-- The numerical tradeoff at the source's `a-1` stopping point, for any
positive initial indexed-column mass `c`. It is independent of the later
suffix obstruction. -/
theorem source_prefix_thresholds
    (μ : FiniteLaw X) (ν : FiniteLaw S)
    (F : (I × X) → S → Bool) (Q : Finset I)
    (R : I → Set X) (C : Set S)
    (d a : ℕ) (x c : ℝ)
    (ha : 1 ≤ a) (hx : 0 < x) (hc : 0 < c)
    (hQ : 2 ^ (a-1) + 1 ≤ Q.card)
    (hR : ∀ i ∈ Q, (2 : ℝ) ^ a * x ≤ μ.prob (· ∈ R i))
    (hC : c ≤ ν.prob (· ∈ C))
    (hD : Compression.restrictionD F (rowRectangle Q R) C ≤ d+a-1) :
    ∃ (A B : ℕ) (Q' : Finset I) (R' : I → Set X) (C' : Set S)
      (P' : Protocol (I × X) S Bool),
      A + B = a-1 ∧ 2 ^ B + 1 ≤ Q'.card ∧
      (∀ i ∈ Q', (2 : ℝ) ^ (B+1) * x ≤ μ.prob (· ∈ R' i)) ∧
      c / ((2 : ℝ) ^ B) ≤ ν.prob (· ∈ C') ∧
      Q' ⊆ Q ∧ (∀ i ∈ Q', R' i ⊆ R i) ∧ C' ⊆ C ∧
      P'.cost ≤ d ∧
      (∀ i ∈ Q', ∀ u ∈ R' i, ∀ s ∈ C',
        P'.eval (i,u) s = F (i,u) s) := by
  have hnonempty := initial_nonempty μ ν Q R C ((2 : ℝ)^a*x) c
    (by positivity) hc (by have := Nat.zero_le (2^(a-1)); omega) hR hC
  obtain ⟨A, B, Q', R', C', P', hab, hQsub, hRsub, hCsub,
    hcount, hrow, hcol, hsuf, heval⟩ :=
    restriction_prefix μ ν F Q R C hnonempty.1 hnonempty.2
      (a-1) (d+a-1) hD (by omega)
  refine ⟨A, B, Q', R', C', P', hab, ?_, ?_, ?_,
    hQsub, hRsub, hCsub, ?_, heval⟩
  · have haexp : A + B = a-1 := hab
    have hlarge : 2 ^ (A+B) + 1 ≤ Q.card := by
      simpa [← haexp] using hQ
    by_contra hn
    have hsmall : Q'.card ≤ 2 ^ B := by omega
    have hm := Nat.mul_le_mul_left (2 ^ A) hsmall
    have hp : 2 ^ A * 2 ^ B = 2 ^ (A+B) := by rw [pow_add]
    rw [hp] at hm
    omega
  · intro i hi
    have hstart := hR i (hQsub hi)
    have hremain := hrow i hi
    have haeq : a = A + (B+1) := by omega
    have hscaled : (2 : ℝ)^A * ((2 : ℝ)^(B+1) * x) ≤
        (2 : ℝ)^A * μ.prob (· ∈ R' i) := by
      calc
        _ = (2 : ℝ)^a * x := by rw [haeq, pow_add]; ring
        _ ≤ μ.prob (· ∈ R i) := hstart
        _ ≤ _ := hremain
    exact (mul_le_mul_iff_of_pos_left
      (by positivity : (0 : ℝ) < 2 ^ A)).mp hscaled
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ B)).2
    simpa [mul_comm] using hC.trans hcol
  · omega

/-- Exact-source form of H:(det:exact-prefix), before selecting a small
projection in the suffix. -/
theorem exact_prefix_state
    (μ : FiniteLaw X) (ν : FiniteLaw S)
    (F : (I × X) → S → Bool) (Q : Finset I)
    (R : I → Set X) (C : Set S)
    (d a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hx : 0 < x)
    (hQ : 2 ^ (a-1) + 1 ≤ Q.card)
    (hR : ∀ i ∈ Q, (2 : ℝ) ^ a * x ≤ μ.prob (· ∈ R i))
    (hC : (9/25 : ℝ) ≤ ν.prob (· ∈ C))
    (hD : Compression.restrictionD F (rowRectangle Q R) C ≤ d+a-1) :
    ∃ (A B : ℕ) (Q' : Finset I) (R' : I → Set X) (C' : Set S)
      (P' : Protocol (I × X) S Bool),
      A + B = a-1 ∧ 2 ^ B + 1 ≤ Q'.card ∧
      (∀ i ∈ Q', (2 : ℝ) ^ (B+1) * x ≤ μ.prob (· ∈ R' i)) ∧
      (9/25 : ℝ) / ((2 : ℝ) ^ B) ≤ ν.prob (· ∈ C') ∧
      Q' ⊆ Q ∧ (∀ i ∈ Q', R' i ⊆ R i) ∧ C' ⊆ C ∧
      P'.cost ≤ d ∧
      (∀ i ∈ Q', ∀ u ∈ R' i, ∀ s ∈ C',
        P'.eval (i,u) s = F (i,u) s) := by
  exact source_prefix_thresholds μ ν F Q R C d a x (9/25) ha hx
    (by norm_num) hQ hR hC hD

/-- Rare-event source form of H:(det:rare-prefix). All probabilities are
computed on the original indexed source; only the final displayed ratio is
conditional on the positive event `Y`. -/
theorem rare_prefix_state
    (μ : FiniteLaw X) (ν : FiniteLaw S)
    (F : (I × X) → S → Bool) (Q : Finset I)
    (R : I → Set X) (Y C : Set S)
    (d a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hx : 0 < x)
    (hQ : 2 ^ (a-1) + 1 ≤ Q.card)
    (hR : ∀ i ∈ Q, (2 : ℝ) ^ a * x ≤ μ.prob (· ∈ R i))
    (hY : 0 < ν.prob (· ∈ Y)) (hCY : C ⊆ Y)
    (hC : (1/2 : ℝ) ≤ ν.prob (· ∈ C) / ν.prob (· ∈ Y))
    (hD : Compression.restrictionD F (rowRectangle Q R) C ≤ d+a-1) :
    ∃ (A B : ℕ) (Q' : Finset I) (R' : I → Set X) (C' : Set S)
      (P' : Protocol (I × X) S Bool),
      A + B = a-1 ∧ 2 ^ B + 1 ≤ Q'.card ∧
      (∀ i ∈ Q', (2 : ℝ) ^ (B+1) * x ≤ μ.prob (· ∈ R' i)) ∧
      (1 : ℝ) / ((2 : ℝ) ^ (B+1)) ≤
        ν.prob (· ∈ C') / ν.prob (· ∈ Y) ∧
      Q' ⊆ Q ∧ (∀ i ∈ Q', R' i ⊆ R i) ∧
      C' ⊆ C ∧ C' ⊆ Y ∧ P'.cost ≤ d ∧
      (∀ i ∈ Q', ∀ u ∈ R' i, ∀ s ∈ C',
        P'.eval (i,u) s = F (i,u) s) := by
  have hCpos : 0 < ν.prob (· ∈ C) := by
    have hh := (le_div_iff₀ hY).mp hC
    nlinarith
  obtain ⟨A, B, Q', R', C', P', hab, hcount, hrow,
    hcol, hQsub, hRsub, hCsub, hsuf, heval⟩ :=
    source_prefix_thresholds μ ν F Q R C d a x (ν.prob (· ∈ C))
      ha hx hCpos hQ hR le_rfl hD
  refine ⟨A, B, Q', R', C', P', hab, hcount, hrow, ?_,
    hQsub, hRsub, hCsub, hCsub.trans hCY, hsuf, heval⟩
  have hcolmul : ν.prob (· ∈ C) ≤
      (2 : ℝ)^B * ν.prob (· ∈ C') := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2^B)).mp hcol
    simpa [mul_comm] using hh
  have hcondcol := conditional_column_mass ν Y C C' B hY hcolmul
  have hhalf : (1/2 : ℝ) ≤
      (2 : ℝ)^B * (ν.prob (· ∈ C') / ν.prob (· ∈ Y)) :=
    hC.trans hcondcol
  have hdiv : (1/2 : ℝ) / ((2 : ℝ)^B) ≤
      ν.prob (· ∈ C') / ν.prob (· ∈ Y) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^B)).2
    simpa [mul_comm] using hhalf
  have heq : (1 : ℝ) / ((2 : ℝ) ^ (B+1)) =
      (1/2 : ℝ) / ((2 : ℝ)^B) := by
    rw [pow_succ]
    field_simp
  rw [heq]
  exact hdiv

/-- A residual protocol from the prefix theorem is an actual short protocol
for precisely its retained indexed rectangle, with no assumed lower-bound
certificate. -/
theorem residual_restriction_upper
    (F : (I × X) → S → Bool)
    (Q : Finset I) (R : I → Set X) (C : Set S)
    (P : Protocol (I × X) S Bool) (d : ℕ)
    (hcost : P.cost ≤ d)
    (heval : ∀ i ∈ Q, ∀ u ∈ R i, ∀ s ∈ C,
      P.eval (i,u) s = F (i,u) s) :
    Compression.restrictionD F (rowRectangle Q R) C ≤ d := by
  classical
  let Psub : Protocol (rowRectangle Q R) C Bool :=
    NPCC.Protocol.pullback Subtype.val Subtype.val P
  have hcomp : Psub.Computes (fun a s => F a.1 s.1) := by
    intro ⟨⟨i,u⟩, hu⟩ ⟨s,hs⟩
    change (NPCC.Protocol.pullback Subtype.val Subtype.val P).eval
      ⟨(i,u),hu⟩ ⟨s,hs⟩ = F (i,u) s
    rw [NPCC.Protocol.pullback_eval]
    exact heval i hu.1 u hu.2 s hs
  have hmem : Psub.cost ∈ AchievableCosts
      (fun (a : rowRectangle Q R) (s : C) => F a.1 s.1) :=
    ⟨Psub, rfl, hcomp⟩
  have hD : Compression.restrictionD F (rowRectangle Q R) C ≤ Psub.cost := by
    simpa [Compression.restrictionD, D] using (Nat.sInf_le hmem)
  exact hD.trans (by simpa [Psub] using hcost)

#print axioms CurrentAdditive.ArbitraryPrefix.restrictionD_minimizer
#print axioms CurrentAdditive.ArbitraryPrefix.restriction_prefix
#print axioms CurrentAdditive.ArbitraryPrefix.source_prefix_thresholds
#print axioms CurrentAdditive.ArbitraryPrefix.exact_prefix_state
#print axioms CurrentAdditive.ArbitraryPrefix.rare_prefix_state
#print axioms CurrentAdditive.ArbitraryPrefix.residual_restriction_upper

end CurrentAdditive.ArbitraryPrefix
