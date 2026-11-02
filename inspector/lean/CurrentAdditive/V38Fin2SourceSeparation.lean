import CurrentAdditive.V38Fin2Exact
import CurrentAdditive.V38Fin2Separation

/-! Current-source `cl:separation` on the original indexed tuple labels.
The only communication premise is the base matrix's two-threshold profile;
the independent exact-block theorem is discharged by the checked proof. -/

namespace CurrentAdditive.V38Fin2Exact

open Paper2 Workspace.Types.Protocol

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]
  {t : ℕ}

theorem separation
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin (2^t) → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Rows : Fin (2^t) → Set X) (K : Set S)
    (d : ℕ) (ρ z : ℝ)
    (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t*ρ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ i, z ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hgap : 2*(2 : ℝ)^t*ρ < z)
    (hK : (18/25 : ℝ) ≤ source.prob (· ∈ K))
    (P : Protocol (Fin (2^t) × X) S Bool)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i, ∀ x ∈ Rows i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i)) :
    SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      (∀ w, z/(2 : ℝ)^t ≤ μ.toFiniteLaw.prob
        (fun x => x ∈ Rows (dom w) ∧
          NPCC.Protocol.prefixCodeRaw t P (dom w,x) = w)) ∧
      (∀ w j, j ≠ dom w → μ.toFiniteLaw.prob
        (fun x => x ∈ Rows j ∧ NPCC.Protocol.prefixCodeRaw t P (j,x) = w) < 2*ρ) ∧
      (∀ w, z-2*((2^t : ℕ)-1 : ℕ)*ρ < μ.toFiniteLaw.prob
        (fun x => x ∈ Rows (dom w) ∧
          NPCC.Protocol.prefixCodeRaw t P (dom w,x) = w)) := by
  exact V38Fin2Prefix.dominant_prefix_parts μ F source decode Rows K d ρ z
    ht hd hρ hscale
    (exactBlockBound_of_twoThreshold μ ν F source decode hwise d ρ hd hρ hprofile)
    hrow hgap hK P hcost heval

#print axioms separation

end CurrentAdditive.V38Fin2Exact
