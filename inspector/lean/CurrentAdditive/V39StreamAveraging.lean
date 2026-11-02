import CurrentAdditive.IndependentStreams
import Paper2.SourceProjection
import Workspace.UpperBound

namespace CurrentAdditive.V39StreamAveraging

open Paper2
open scoped BigOperators

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- The non-strict version needed at equality in the current receipt proof.
The complete first stream is chosen once, for the already selected event. -/
theorem exists_section_ge (α : PositiveRationalLaw A) (β : FiniteLaw B)
    (E : A → B → Prop) (θ : ℝ)
    (h : θ ≤ (α.toFiniteLaw.prod β).prob (fun z => E z.1 z.2)) :
    ∃ a, θ ≤ β.prob (E a) := by
  classical
  by_contra hn
  have hall : ∀ a, β.prob (E a) < θ := by
    intro a
    exact lt_of_not_ge (fun ha => hn ⟨a,ha⟩)
  have ha : Nonempty A := α.toFiniteLaw.nonempty
  let a₀ : A := Classical.choice ha
  have hsum : (∑ a, α.toFiniteLaw.weight a * β.prob (E a)) <
      ∑ a, α.toFiniteLaw.weight a * θ := by
    apply Finset.sum_lt_sum
    · intro a _
      exact mul_le_mul_of_nonneg_left (le_of_lt (hall a)) (α.toFiniteLaw.nonneg a)
    · refine ⟨a₀, Finset.mem_univ _, ?_⟩
      apply mul_lt_mul_of_pos_left (hall a₀)
      change (0 : ℝ) < (α.weight a₀ : ℝ)
      exact_mod_cast α.positive a₀
  rw [← Finset.sum_mul, α.toFiniteLaw.total, one_mul] at hsum
  rw [FiniteLaw.prod_prob α.toFiniteLaw β E] at h
  linarith

/-- Choose metadata and base streams by two finite averaging steps. A
retained event of mass at least theta has one selector section of mass at
least theta, with no unjustified strictness. -/
theorem exists_two_complete_sections_ge (α : PositiveRationalLaw A)
    (β : PositiveRationalLaw B) (γ : FiniteLaw C)
    (E : A × (B × C) → Prop) (θ : ℝ)
    (h : θ ≤ (α.toFiniteLaw.prod (β.toFiniteLaw.prod γ)).prob E) :
    ∃ a b, θ ≤ γ.prob (fun c => E (a,(b,c))) := by
  obtain ⟨a,ha⟩ := exists_section_ge α (β.toFiniteLaw.prod γ)
    (fun a bc => E (a,bc)) θ h
  obtain ⟨b,hb⟩ := exists_section_ge β γ (fun b c => E (a,(b,c))) θ ha
  exact ⟨a,b,hb⟩

/-- A law pushforward to a positive finite law cannot omit an actual label.
This is used only for lifting actual restrictions to an auxiliary carrier. -/
theorem surjective_of_positive_pushes (α : FiniteLaw A)
    (β : PositiveRationalLaw B) (f : A → B)
    (hf : α.PushesTo β.toFiniteLaw f) : Function.Surjective f := by
  intro b
  by_contra hn
  have hempty : (fun a => f a = b) = (fun _ => False) := by
    funext a
    exact propext ⟨fun ha => hn ⟨a,ha⟩, False.elim⟩
  have hb := hf (fun b' => b' = b)
  rw [hempty, FiniteLaw.prob_false, FiniteLaw.prob_singleton] at hb
  have hp : 0 < β.toFiniteLaw.weight b := by
    change (0 : ℝ) < (β.weight b : ℝ)
    exact_mod_cast β.positive b
  linarith

section Protocol

open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {X Y T : Type*} [Fintype X] [Fintype Y] [Fintype T]

/-- The actual protocol is pulled back, rather than replaced by a new
protocol on extra visible columns. Its depth is unchanged. -/
theorem pullback_protocol (F : X → Y → Bool) (f : T → Y)
    (U : Set X) (V : Set Y) (P : Protocol U V Bool)
    (hP : P.Computes (fun x y => F x.val y.val)) :
    ∃ Q : Protocol U (f ⁻¹' V) Bool,
      Q.cost = P.cost ∧ Q.Computes (fun x t => F x.val (f t.val)) := by
  let Q := Workspace.UpperBound.Protocol.comap id
    (fun t : f ⁻¹' V => (⟨f t.val,t.property⟩ : V)) P
  refine ⟨Q,?_,?_⟩
  · exact Workspace.UpperBound.Protocol.comap_cost _ _ P
  · intro x t
    simpa [Q, Workspace.UpperBound.Protocol.comap_eval] using
      hP x (⟨f t.val,t.property⟩ : V)

end Protocol

end CurrentAdditive.V39StreamAveraging

#print axioms CurrentAdditive.V39StreamAveraging.exists_section_ge
#print axioms CurrentAdditive.V39StreamAveraging.exists_two_complete_sections_ge
#print axioms CurrentAdditive.V39StreamAveraging.surjective_of_positive_pushes
#print axioms CurrentAdditive.V39StreamAveraging.pullback_protocol
