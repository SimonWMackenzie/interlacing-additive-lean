import CurrentAdditive.V38LocalDiagram
import CurrentAdditive.V38Fin2Exact

/-! v39/v38 src:near-full local supplier (ii), robustness.tex:272--276.
The source's actual Fin 2 exact bound is applied only under the ambient
eight-wise law. The actual Alice child is chosen before all capacities.
-/

namespace CurrentAdditive.V38LocalDiagram

open Paper2 CurrentAdditive.ArbitraryPrefix
open Workspace.Types.Protocol

variable {A C T W J : Type*}
  [Fintype A] [Fintype C] [Fintype T] [Fintype W] [Fintype J]
  {q : ℕ}

theorem after_alice_cost
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J) (σ : FiniteLaw T)
    (F : A → C → Bool) (B : W → J → Bool)
    (row : T → A) (input : Fin q → W → C)
    (decode : T → Fin q → J)
    (hentry : ∀ t w i, F (row t) (input i w) = B w (decode t i))
    (hwise : IsDWise 8 σ decode ν.toFiniteLaw)
    (H : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile B
      μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (K : Set T) (V : Set A)
    (hrow : ∀ t ∈ K, row t ∈ V)
    (hK : (998 / 1000 : ℝ) < σ.prob (· ∈ K))
    (U : Set C) (query : V → Bool) :
    ∃ bit : Bool, ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ k * x ≤ 1 →
      ∀ (Good : Finset (Fin q)) (Supports : Fin q → Finset W),
        2 ^ (k - 1) + 1 ≤ Good.card →
        (∀ i ∈ Good, (2 : ℝ) ^ k * x ≤
          SourceSupportStep.mass μ.toFiniteLaw (Supports i) ∧
          ∀ w ∈ Supports i, input i w ∈ U) →
        ∀ child : Protocol {a : V // query a = bit} U Bool,
          child.Computes (fun a c => F a.val.val c.val) →
          H + k ≤ child.cost := by
  classical
  obtain ⟨bit, hbit⟩ := dense_selector_child σ row K V query hK
  refine ⟨bit, ?_⟩
  intro k hk hscale Good Supports hcount hs child hchild
  let Rows : Fin q → Set W := fun i => (Supports i : Set W)
  have hm (i : Fin q) (hi : i ∈ Good) :
      (2 : ℝ) ^ k * x ≤ μ.toFiniteLaw.prob (· ∈ Rows i) := (hs i hi).1
  have hinput : ∀ i ∈ Good, ∀ w ∈ Rows i, input i w ∈ U :=
    fun i hi => (hs i hi).2
  have hKbit : (9 / 25 : ℝ) ≤
      σ.prob (· ∈ selectorFibre row K V query bit) := by linarith
  have hl := V38Fin2Exact.exactboost μ ν B σ decode hwise Good Rows
    (selectorFibre row K V query bit) H k x hk hH hx hscale
    hprofile hcount hm hKbit
  exact hl.trans (after_alice_interlace_le F B row input decode hentry K V
    query bit hrow Good Rows U hinput child hchild)

end CurrentAdditive.V38LocalDiagram

#print axioms CurrentAdditive.V38LocalDiagram.after_alice_cost
