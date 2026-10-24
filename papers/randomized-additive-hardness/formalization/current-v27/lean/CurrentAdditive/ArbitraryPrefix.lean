import Paper2.FiniteSampling
import NPCC.Control

/-!
Private proof of the fixed-total arbitrary-speaker prefix choice in
v27 `appendices/H-deterministic-core.tex`, before `det:exact`.
The source uses actual indexed column labels and arbitrary protocol nodes.
-/

namespace CurrentAdditive.ArbitraryPrefix

open Workspace.Types.Protocol
open Paper2

variable {I X S Z : Type*} [Fintype I] [Fintype X] [Fintype S]

private theorem prob_partition (μ : FiniteLaw X) (R : Set X) (p : X → Prop) :
    μ.prob (fun x => x ∈ R ∧ p x) +
      μ.prob (fun x => x ∈ R ∧ ¬ p x) = μ.prob (· ∈ R) := by
  classical
  simp only [FiniteLaw.prob, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ R <;> by_cases hp : p x <;> simp [hx, hp]

private theorem prob_heavy_or (μ : FiniteLaw X) (R : Set X) (p : X → Prop) :
    2 * μ.prob (fun x => x ∈ R ∧ p x) ≥ μ.prob (· ∈ R) ∨
      2 * μ.prob (fun x => x ∈ R ∧ ¬ p x) ≥ μ.prob (· ∈ R) := by
  have h := prob_partition μ R p
  by_cases hp : 2 * μ.prob (fun x => x ∈ R ∧ p x) ≥ μ.prob (· ∈ R)
  · exact Or.inl hp
  · exact Or.inr (by linarith)

/-- The row blocks on an actual Alice child can be chosen with both the
majority block count and half of each chosen block's original row mass. -/
theorem alice_child (μ : FiniteLaw X) (Q : Finset I) (R : I → Set X)
    (pred : I × X → Bool) :
    ∃ (bit : Bool) (Q' : Finset I) (R' : I → Set X),
      Q' ⊆ Q ∧ 2 * Q'.card ≥ Q.card ∧
      (∀ i ∈ Q', R' i ⊆ R i ∧
        (∀ x ∈ R' i, pred (i,x) = bit) ∧
        2 * μ.prob (· ∈ R' i) ≥ μ.prob (· ∈ R i)) := by
  classical
  let t (i : I) : Set X := {x | x ∈ R i ∧ pred (i,x) = true}
  let f (i : I) : Set X := {x | x ∈ R i ∧ ¬ pred (i,x) = true}
  let good (i : I) : Prop := 2 * μ.prob (· ∈ t i) ≥ μ.prob (· ∈ R i)
  by_cases h : 2 * (Q.filter good).card ≥ Q.card
  · refine ⟨true, Q.filter good, t, Finset.filter_subset _ _, h, ?_⟩
    intro i hi
    have hgood : good i := (Finset.mem_filter.mp hi).2
    refine ⟨?_, ?_, hgood⟩
    · intro x hx; exact hx.1
    · intro x hx; exact hx.2
  · have hcard : 2 * (Q.filter (fun i => ¬good i)).card ≥ Q.card := by
      have hs := Finset.card_filter_add_card_filter_not (s := Q) good
      omega
    refine ⟨false, Q.filter (fun i => ¬good i), f,
      Finset.filter_subset _ _, hcard, ?_⟩
    intro i hi
    have hbad : ¬good i := (Finset.mem_filter.mp hi).2
    have hsplit := prob_partition μ (R i) (fun x => pred (i,x) = true)
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; exact hx.1
    · intro x hx
      exact Bool.eq_false_iff.mpr hx.2
    · change 2 * μ.prob (fun x => x ∈ R i ∧ ¬ pred (i,x) = true) ≥ _
      change ¬(2 * μ.prob (fun x => x ∈ R i ∧ pred (i,x) = true) ≥ _) at hbad
      linarith

/-- An actual Bob child keeps at least half of the indexed column mass. -/
theorem bob_child (ν : FiniteLaw S) (C : Set S) (pred : S → Bool) :
    ∃ (bit : Bool) (C' : Set S), C' ⊆ C ∧
      (∀ s ∈ C', pred s = bit) ∧
      2 * ν.prob (· ∈ C') ≥ ν.prob (· ∈ C) := by
  classical
  rcases prob_heavy_or ν C (fun s => pred s = true) with ht | hf
  · refine ⟨true, {s | s ∈ C ∧ pred s = true}, ?_, ?_, ht⟩
    · intro s hs; exact hs.1
    · intro s hs; exact hs.2
  · refine ⟨false, {s | s ∈ C ∧ ¬ pred s = true}, ?_, ?_, hf⟩
    · intro s hs; exact hs.1
    · intro s hs; exact Bool.eq_false_iff.mpr hs.2

/-- Pad a short leaf by a fixed false Alice message. Repeating this at every
leaf gives a protocol with a full first `H` levels whenever the original
cost is at most `H`. -/
def padTo : (H : ℕ) → Protocol (I × X) S Z → Protocol (I × X) S Z
  | 0, P => P
  | H+1, .leaf z =>
      .aNode (fun _ => false) (padTo H (.leaf z)) (padTo H (.leaf z))
  | H+1, .aNode q l r => .aNode q (padTo H l) (padTo H r)
  | H+1, .bNode q l r => .bNode q (padTo H l) (padTo H r)

/-- Every root-to-leaf route has at least the displayed number of messages. -/
def FullPrefix : ℕ → Protocol (I × X) S Z → Prop
  | 0, _ => True
  | _+1, .leaf _ => False
  | H+1, .aNode _ l r => FullPrefix H l ∧ FullPrefix H r
  | H+1, .bNode _ l r => FullPrefix H l ∧ FullPrefix H r

theorem padTo_full (H : ℕ) (P : Protocol (I × X) S Z) :
    FullPrefix H (padTo H P) := by
  induction H generalizing P with
  | zero => trivial
  | succ H ih =>
      cases P <;> simp [padTo, FullPrefix, ih]

theorem padTo_eval (H : ℕ) (P : Protocol (I × X) S Z)
    (a : I × X) (s : S) : (padTo H P).eval a s = P.eval a s := by
  induction H generalizing P with
  | zero => rfl
  | succ H ih =>
      cases P with
      | leaf z => simp [padTo, Protocol.eval, ih]
      | aNode q l r =>
          by_cases h : q a <;> simp [padTo, Protocol.eval, h, ih]
      | bNode q l r =>
          by_cases h : q s <;> simp [padTo, Protocol.eval, h, ih]

theorem padTo_cost (H : ℕ) (P : Protocol (I × X) S Z)
    (h : P.cost ≤ H) : (padTo H P).cost = H := by
  induction H generalizing P with
  | zero =>
      have hz : P.cost = 0 := by omega
      simpa [padTo] using hz
  | succ H ih =>
      cases P with
      | leaf z => simp [padTo, Protocol.cost, ih]; omega
      | aNode q l r =>
          have hl : l.cost ≤ H := by simp only [Protocol.cost] at h; omega
          have hr : r.cost ≤ H := by simp only [Protocol.cost] at h; omega
          simp [padTo, Protocol.cost, ih l hl, ih r hr]; omega
      | bNode q l r =>
          have hl : l.cost ≤ H := by simp only [Protocol.cost] at h; omega
          have hr : r.cost ≤ H := by simp only [Protocol.cost] at h; omega
          simp [padTo, Protocol.cost, ih l hl, ih r hr]; omega

/-- The multiplicative block-count invariant gives the exact rounded count
stated in the manuscript. -/
theorem ceil_blocks {A start retained : ℕ}
    (h : start ≤ 2 ^ A * retained) :
    ⌈(start : ℝ) / ((2 : ℝ) ^ A)⌉₊ ≤ retained := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ A)).2
  have hr : (start : ℝ) ≤ (2 : ℝ) ^ A * (retained : ℝ) := by
    exact_mod_cast h
  simpa [mul_comm] using hr

/-- Dividing both actual column masses by the same positive event mass
preserves the Bob-prefix estimate. No independence after conditioning is
asserted here. -/
theorem conditional_column_mass (ν : FiniteLaw S)
    (Y C C' : Set S) (B : ℕ)
    (hY : 0 < ν.prob (· ∈ Y))
    (h : ν.prob (· ∈ C) ≤ (2 : ℝ) ^ B * ν.prob (· ∈ C')) :
    ν.prob (· ∈ C) / ν.prob (· ∈ Y) ≤
      (2 : ℝ) ^ B * (ν.prob (· ∈ C') / ν.prob (· ∈ Y)) := by
  calc
    ν.prob (· ∈ C) / ν.prob (· ∈ Y) ≤
        ((2 : ℝ) ^ B * ν.prob (· ∈ C')) / ν.prob (· ∈ Y) :=
      (div_le_div_iff_of_pos_right hY).2 h
    _ = (2 : ℝ) ^ B * (ν.prob (· ∈ C') / ν.prob (· ∈ Y)) := by ring

set_option maxHeartbeats 1000000 in
/-- Select a rectangle below an actual arbitrary-speaker protocol after a
fixed total of `k` messages. At an early leaf, the unused positions are
constant Alice messages. The returned subtree is the leaf itself, whose
evaluation agrees with the padded tree on the selected rectangle. -/
theorem fixed_total_prefix (μ : FiniteLaw X) (ν : FiniteLaw S)
    (P : Protocol (I × X) S Z) (Q : Finset I) (R : I → Set X) (C : Set S)
    (k H : ℕ) (hcost : P.cost ≤ H) (hk : k ≤ H) :
    ∃ (A B : ℕ) (Q' : Finset I) (R' : I → Set X) (C' : Set S)
      (P' : Protocol (I × X) S Z),
      A + B = k ∧ Q' ⊆ Q ∧
      (∀ i ∈ Q', R' i ⊆ R i) ∧ C' ⊆ C ∧
      2 ^ A * Q'.card ≥ Q.card ∧
      (∀ i ∈ Q', (2 : ℝ) ^ A * μ.prob (· ∈ R' i) ≥ μ.prob (· ∈ R i)) ∧
      (2 : ℝ) ^ B * ν.prob (· ∈ C') ≥ ν.prob (· ∈ C) ∧
      P'.cost ≤ H - k ∧
      (∀ i ∈ Q', ∀ x ∈ R' i, ∀ s ∈ C',
        P'.eval (i,x) s = P.eval (i,x) s) := by
  induction k generalizing P Q R C H with
  | zero =>
      refine ⟨0, 0, Q, R, C, P, by simp, (fun _ h => h), ?_, (fun _ h => h),
        by simp, ?_, ?_, by simpa using hcost, ?_⟩
      · intro i hi x hx; exact hx
      · intro i hi; simp
      · simp
      · intros; rfl
  | succ k ih =>
      cases P with
      | leaf z =>
          refine ⟨k+1, 0, Q, R, C, Protocol.leaf z, by simp,
            (fun _ h => h), ?_, (fun _ h => h), ?_, ?_, ?_, ?_, ?_⟩
          · intro i hi x hx; exact hx
          · have hp : 1 ≤ 2 ^ (k+1) := by exact Nat.one_le_pow _ _ (by omega)
            nlinarith
          · intro i hi
            have hp : (1 : ℝ) ≤ 2 ^ (k+1) := one_le_pow₀ (by norm_num)
            have hm := μ.prob_nonneg (· ∈ R i)
            nlinarith
          · simp
          · simp [Protocol.cost]
          · intros; rfl
      | aNode pred l r =>
          obtain ⟨bit, Q₁, R₁, hQsub, hQhalf, hR₁⟩ := alice_child μ Q R pred
          let P₁ := if bit then r else l
          have hc₁ : P₁.cost ≤ H - 1 := by
            dsimp [P₁]
            split_ifs <;> simp only [Protocol.cost] at hcost <;> omega
          have hk₁ : k ≤ H - 1 := by omega
          obtain ⟨A, B, Q₂, R₂, C₂, P₂, hab, hQ₂, hR₂, hC₂,
            hQcount, hRmass, hCmass, hcost₂, heval₂⟩ :=
            ih P₁ Q₁ R₁ C (H-1) hc₁ hk₁
          refine ⟨A+1, B, Q₂, R₂, C₂, P₂, by omega,
            hQ₂.trans hQsub, ?_, hC₂, ?_, ?_, hCmass, ?_, ?_⟩
          · intro i hi
            exact (hR₂ i hi).trans (hR₁ i (hQ₂ hi)).1
          · have hmul := Nat.mul_le_mul_left 2 hQcount
            have hstep := Nat.le_trans hQhalf hmul
            simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm] using hstep
          · intro i hi
            have hm₂ := hRmass i hi
            have hm₁ := (hR₁ i (hQ₂ hi)).2.2
            have h2 := mul_le_mul_of_nonneg_left hm₂ (by norm_num : (0:ℝ) ≤ 2)
            calc
              μ.prob (· ∈ R i) ≤ 2 * μ.prob (· ∈ R₁ i) := hm₁
              _ ≤ 2 * ((2 : ℝ)^A * μ.prob (· ∈ R₂ i)) := h2
              _ = (2 : ℝ)^(A+1) * μ.prob (· ∈ R₂ i) := by ring
          · omega
          · intro i hi x hx s hs
            rw [heval₂ i hi x hx s hs]
            have hb := (hR₁ i (hQ₂ hi)).2.1 x ((hR₂ i hi) hx)
            cases bit <;> simp [P₁, Protocol.eval, hb]
      | bNode pred l r =>
          obtain ⟨bit, C₁, hC₁, hb₁, hmass₁⟩ := bob_child ν C pred
          let P₁ := if bit then r else l
          have hc₁ : P₁.cost ≤ H - 1 := by
            dsimp [P₁]
            split_ifs <;> simp only [Protocol.cost] at hcost <;> omega
          have hk₁ : k ≤ H - 1 := by omega
          obtain ⟨A, B, Q₂, R₂, C₂, P₂, hab, hQ₂, hR₂, hC₂,
            hQcount, hRmass, hCmass, hcost₂, heval₂⟩ :=
            ih P₁ Q R C₁ (H-1) hc₁ hk₁
          refine ⟨A, B+1, Q₂, R₂, C₂, P₂, by omega,
            hQ₂, hR₂, hC₂.trans hC₁, hQcount, hRmass, ?_, ?_, ?_⟩
          · have h2 := mul_le_mul_of_nonneg_left hCmass (by norm_num : (0:ℝ) ≤ 2)
            calc
              ν.prob (· ∈ C) ≤ 2 * ν.prob (· ∈ C₁) := hmass₁
              _ ≤ 2 * ((2 : ℝ)^B * ν.prob (· ∈ C₂)) := h2
              _ = (2 : ℝ)^(B+1) * ν.prob (· ∈ C₂) := by ring
          · omega
          · intro i hi x hx s hs
            rw [heval₂ i hi x hx s hs]
            have hb := hb₁ s (hC₂ hs)
            cases bit <;> simp [P₁, Protocol.eval, hb]

/-- Source-shaped readout on the explicitly padded protocol. The selected
subtree evaluates the original Boolean protocol on every surviving indexed
row and column, while the fixed prefix spends exactly `k = A+B` messages. -/
theorem padded_prefix (μ : FiniteLaw X) (ν : FiniteLaw S)
    (P : Protocol (I × X) S Z) (Q : Finset I) (R : I → Set X) (C : Set S)
    (k H : ℕ) (hcost : P.cost ≤ H) (hk : k ≤ H) :
    ∃ (A B : ℕ) (Q' : Finset I) (R' : I → Set X) (C' : Set S)
      (P' : Protocol (I × X) S Z),
      A + B = k ∧ Q' ⊆ Q ∧
      (∀ i ∈ Q', R' i ⊆ R i) ∧ C' ⊆ C ∧
      ⌈(Q.card : ℝ) / ((2 : ℝ) ^ A)⌉₊ ≤ Q'.card ∧
      (∀ i ∈ Q', μ.prob (· ∈ R i) / ((2 : ℝ) ^ A) ≤
        μ.prob (· ∈ R' i)) ∧
      ν.prob (· ∈ C) / ((2 : ℝ) ^ B) ≤ ν.prob (· ∈ C') ∧
      P'.cost ≤ H - k ∧
      (∀ i ∈ Q', ∀ x ∈ R' i, ∀ s ∈ C',
        P'.eval (i,x) s = P.eval (i,x) s) := by
  obtain ⟨A, B, Q', R', C', P', hab, hQ, hR, hC,
    hcount, hrow, hcol, hsuf, heval⟩ :=
    fixed_total_prefix μ ν (padTo H P) Q R C k H
      (le_of_eq (padTo_cost H P hcost)) hk
  refine ⟨A, B, Q', R', C', P', hab, hQ, hR, hC,
    ceil_blocks hcount, ?_, ?_, hsuf, ?_⟩
  · intro i hi
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ A)).2
    simpa [mul_comm] using hrow i hi
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ B)).2
    simpa [mul_comm] using hcol
  · intro i hi x hx s hs
    rw [heval i hi x hx s hs, padTo_eval]

/-- A protocol for the concrete retained rectangle can be run on the ambient
indexed labels by extending its queries arbitrarily outside that rectangle.
This is the existing `Protocol.pullback` interface; no behaviour outside the
retained input sets is used by the prefix theorem. -/
theorem extend_restriction_protocol
    (U : Set (I × X)) (V : Set S)
    (hU : U.Nonempty) (hV : V.Nonempty)
    (P : Protocol U V Z) :
    ∃ Pfull : Protocol (I × X) S Z,
      Pfull.cost = P.cost ∧
      (∀ a (ha : a ∈ U) s (hs : s ∈ V),
        Pfull.eval a s = P.eval ⟨a, ha⟩ ⟨s, hs⟩) := by
  classical
  let a₀ : U := ⟨hU.choose, hU.choose_spec⟩
  let s₀ : V := ⟨hV.choose, hV.choose_spec⟩
  let φ : I × X → U := fun a => if h : a ∈ U then ⟨a,h⟩ else a₀
  let ψ : S → V := fun s => if h : s ∈ V then ⟨s,h⟩ else s₀
  refine ⟨NPCC.Protocol.pullback φ ψ P, by simp, ?_⟩
  intro a ha s hs
  simp [φ, ψ, ha, hs]

end CurrentAdditive.ArbitraryPrefix

#print axioms CurrentAdditive.ArbitraryPrefix.alice_child
#print axioms CurrentAdditive.ArbitraryPrefix.bob_child
#print axioms CurrentAdditive.ArbitraryPrefix.padTo_full
#print axioms CurrentAdditive.ArbitraryPrefix.padTo_eval
#print axioms CurrentAdditive.ArbitraryPrefix.padTo_cost
#print axioms CurrentAdditive.ArbitraryPrefix.fixed_total_prefix
#print axioms CurrentAdditive.ArbitraryPrefix.padded_prefix
#print axioms CurrentAdditive.ArbitraryPrefix.ceil_blocks
#print axioms CurrentAdditive.ArbitraryPrefix.conditional_column_mass
#print axioms CurrentAdditive.ArbitraryPrefix.extend_restriction_protocol
