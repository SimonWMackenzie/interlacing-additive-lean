import CurrentAdditive.ConditioningFiniteTV
import CurrentAdditive.IndependentStreams

/-! Convert the current-paper indexed-source definition to the finite-TV
interface. This leaves the frozen TV and covering files unchanged. -/

namespace CurrentAdditive

open Paper2 Paper2.FiniteLaw

theorem exactlyKWiseIndependent_of_isDWise
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q D : ℕ}
    (ν : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z)
    (hwise : IsDWise D ν draw μ) :
    ExactlyKWiseIndependent ν μ draw D := by
  classical
  intro J hJ A
  have hsource := hwise J hJ (fun x => x ∈ A)
  have hproduct := FiniteLaw.pi_prob_restrict
    (fun _ : Fin q => μ) (fun j : J => j.1)
    Subtype.val_injective (fun x : J → Z => x ∈ A)
  have hiid : μ.iid q = FiniteLaw.pi (fun _ : Fin q => μ) := rfl
  calc
    ν.prob (fun ω => projection draw J ω ∈ A) =
        (FiniteLaw.pi (fun _ : J => μ)).prob (fun x => x ∈ A) := by
      simpa only [projection] using hsource
    _ = (μ.iid q).prob (fun z => projection id J z ∈ A) := by
      rw [hiid]
      simpa only [projection] using hproduct.symm

#print axioms exactlyKWiseIndependent_of_isDWise

end CurrentAdditive
