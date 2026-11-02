import Paper2.YaoCapacity
import CurrentAdditive.SmallBiasPatterns

/-!
# One actual Bob--Alice rectangle step

Source: v27 `sections/07a-small-bias.tex`, proof of
`yao:small-bias-escape`, paragraph "Follow a rectangle to the cut".
The column law remains the original normalized law throughout.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

private theorem prob_bob_partition (μ : Paper2.FiniteLaw Λ)
    (Y : Λ → Prop) (f : Λ → Bool) :
    μ.prob (fun ℓ => Y ℓ ∧ f ℓ = false) +
      μ.prob (fun ℓ => Y ℓ ∧ f ℓ = true) = μ.prob Y := by
  classical
  unfold Paper2.FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ℓ _
  by_cases hY : Y ℓ <;> cases hf : f ℓ <;> simp [hY, hf]

/-- One actual Bob branch retains at least half of the original-law mass. -/
theorem exists_bob_half (μ : Paper2.FiniteLaw Λ)
    (Y : Λ → Prop) (f : Λ → Bool) :
    ∃ b : Bool, μ.prob Y ≤ 2 * μ.prob (fun ℓ => Y ℓ ∧ f ℓ = b) := by
  have hsplit := prob_bob_partition μ Y f
  by_cases h : μ.prob Y ≤ 2 * μ.prob (fun ℓ => Y ℓ ∧ f ℓ = false)
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    linarith

private theorem exists_alice_half (X : Finset Ω) (a : Ω → Bool) :
    ∃ c : Bool, X.card ≤ 2 * (X.filter (fun x => a x = c)).card := by
  classical
  have hsplit : (X.filter (fun x => a x = false)).card +
      (X.filter (fun x => a x = true)).card = X.card := by
    have htrue : X.filter (fun x => a x = true) =
        X.filter (fun x => ¬ a x = false) := by
      ext x
      cases a x <;> simp
    have h := Finset.card_filter_add_card_filter_not
      (s := X) (p := fun x => a x = false)
    rw [htrue]
    exact h
  by_cases h : X.card ≤ 2 * (X.filter (fun x => a x = false)).card
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    omega

/-- A single real transcript step from an actual complete alternating tree.
The returned `Q` is an actual depth-two descendant. Bob's branch is common
across the retained rows, and Alice's branch restricts those rows. The two
half-loss estimates refer to the original law `μ` and original row labels. -/
theorem one_pair_rectangle
    (μ : Paper2.FiniteLaw Λ) (P : Protocol Ω Λ Bool) (d : ℕ)
    (hc : IsComplete P (d + 2)) (ha : Alternates .bob P)
    (X : Finset Ω) (Y : Λ → Prop) :
    ∃ (X' : Finset Ω) (Y' : Λ → Prop) (Q : Protocol Ω Λ Bool),
      X' ⊆ X ∧
      (∀ ℓ, Y' ℓ → Y ℓ) ∧
      X.card ≤ 2 * X'.card ∧
      μ.prob Y ≤ 2 * μ.prob Y' ∧
      IsComplete Q d ∧ Alternates .bob Q ∧
      (∀ x ∈ X', ∀ ℓ, Y' ℓ → P.eval x ℓ = Q.eval x ℓ) := by
  classical
  -- Extract the root Bob map from the actual tree.
  cases P with
  | leaf v => exact False.elim hc
  | aNode a l r => exact False.elim ha
  | bNode f l r =>
      have hcbranches : IsComplete l (d + 1) ∧ IsComplete r (d + 1) := by
        change IsComplete l (d + 1) ∧ IsComplete r (d + 1) at hc
        exact hc
      obtain ⟨b, hb⟩ := exists_bob_half μ Y f
      let T : Protocol Ω Λ Bool := if b then r else l
      have hT : IsComplete T (d + 1) ∧ Alternates .alice T := by
        cases b <;> simp [T, hcbranches.1, hcbranches.2, ha.1, ha.2]
      obtain ⟨a, q0, q1, hshape⟩ := alice_root_of_complete T d hT.1 hT.2
      obtain ⟨c, hcrows⟩ := exists_alice_half X a
      let X' := X.filter (fun x => a x = c)
      let Y' : Λ → Prop := fun ℓ => Y ℓ ∧ f ℓ = b
      let Q : Protocol Ω Λ Bool := if c then q1 else q0
      have hQ : IsComplete Q d ∧ Alternates .bob Q := by
        have hqc : Paper2.Yao.IsComplete q0 d ∧ Paper2.Yao.IsComplete q1 d := by
          have hh := hT.1
          rw [hshape] at hh
          exact hh
        have hqa : Alternates .bob q0 ∧ Alternates .bob q1 := by
          have hh := hT.2
          rw [hshape] at hh
          exact hh
        cases c <;> simp [Q, hqc.1, hqc.2, hqa.1, hqa.2]
      refine ⟨X', Y', Q, Finset.filter_subset _ _, (fun _ h => h.1),
        hcrows, hb, hQ.1, hQ.2, ?_⟩
      intro x hx ℓ hℓ
      have hax : a x = c := (Finset.mem_filter.mp hx).2
      have hfℓ : f ℓ = b := hℓ.2
      cases b <;> cases c <;>
        simp_all [T, Q, Y', Protocol.eval]

/-- Iterating the actual one-pair choice yields a genuine rectangle after
`i` Bob--Alice pairs. The output laws are still measured by the original
`μ`; no conditioned distribution is introduced. -/
theorem rectangle_after_pairs
    (μ : Paper2.FiniteLaw Λ) (i h : ℕ)
    (P : Protocol Ω Λ Bool)
    (hc : IsComplete P (2 * i + 2 * h)) (ha : Alternates .bob P)
    (X : Finset Ω) (Y : Λ → Prop) :
    ∃ (X' : Finset Ω) (Y' : Λ → Prop) (Q : Protocol Ω Λ Bool),
      X' ⊆ X ∧
      (∀ ℓ, Y' ℓ → Y ℓ) ∧
      X.card ≤ 2 ^ i * X'.card ∧
      μ.prob Y ≤ (2 ^ i : ℝ) * μ.prob Y' ∧
      IsComplete Q (2 * h) ∧ Alternates .bob Q ∧
      (∀ x ∈ X', ∀ ℓ, Y' ℓ → P.eval x ℓ = Q.eval x ℓ) := by
  induction i generalizing P X Y with
  | zero =>
      refine ⟨X, Y, P, Finset.Subset.rfl, (fun _ h => h), ?_, ?_, ?_, ha, ?_⟩
      · simp
      · simp
      · simpa using hc
      · intro x _ ℓ _
        rfl
  | succ i ih =>
      have hc' : IsComplete P ((2 * i + 2 * h) + 2) := by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
      obtain ⟨X₁, Y₁, P₁, hX₁, hY₁, hcard₁, hmass₁, hc₁, ha₁, heval₁⟩ :=
        one_pair_rectangle μ P (2 * i + 2 * h) hc' ha X Y
      obtain ⟨X₂, Y₂, P₂, hX₂, hY₂, hcard₂, hmass₂, hc₂, ha₂, heval₂⟩ :=
        ih P₁ hc₁ ha₁ X₁ Y₁
      refine ⟨X₂, Y₂, P₂, hX₂.trans hX₁, (fun ℓ h => hY₁ ℓ (hY₂ ℓ h)),
        ?_, ?_, hc₂, ha₂, ?_⟩
      · calc
          X.card ≤ 2 * X₁.card := hcard₁
          _ ≤ 2 * (2 ^ i * X₂.card) := Nat.mul_le_mul_left 2 hcard₂
          _ = 2 ^ (i + 1) * X₂.card := by ring
      · calc
          μ.prob Y ≤ 2 * μ.prob Y₁ := hmass₁
          _ ≤ 2 * ((2 ^ i : ℝ) * μ.prob Y₂) :=
            mul_le_mul_of_nonneg_left hmass₂ (by norm_num)
          _ = (2 ^ (i + 1) : ℝ) * μ.prob Y₂ := by ring
      · intro x hx ℓ hℓ
        exact (heval₁ x (hX₂ hx) ℓ (hY₂ ℓ hℓ)).trans
          (heval₂ x hx ℓ hℓ)

#print axioms CurrentAdditive.SmallBias.one_pair_rectangle
#print axioms CurrentAdditive.SmallBias.rectangle_after_pairs
#print axioms CurrentAdditive.SmallBias.exists_bob_half

end CurrentAdditive.SmallBias
