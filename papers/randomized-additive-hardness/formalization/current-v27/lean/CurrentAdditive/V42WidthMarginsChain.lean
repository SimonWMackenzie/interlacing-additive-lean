import CurrentAdditive.V42NumericAllowances
import CurrentAdditive.V42ExactWidthMargins

/-! Complete literal chain displayed in replacement v42 eq:width-margins:
each pair below is actual quantity <= printed middle <= required allowance.
Both sides are proved from the literal recipe and its sufficient cutoff. -/

namespace CurrentAdditive.V42WidthMarginsChain
noncomputable section
open V42Schedule

theorem width_margins_chain (δv ζ : ℚ) (k b n m Δ : ℕ)
    (hδ : 0 < δv) (hζ : 0 < ζ) (hk : commonCutoff δv ζ Δ ≤ k)
    (hb : 4*k ≤ b) (hn : n ≤ 2^b) (hdeg : 2*m ≤ Δ*n) :
    ((s k:ℝ)*(eta k:ℝ) ≤ (s k:ℝ)^(-(1:ℝ)) ∧
      (s k:ℝ)^(-(1:ℝ)) ≤ (2:ℝ)^(-(16:ℝ))*min 1 (min (δv:ℝ) ((1/256:ℝ)*(ζ:ℝ)))) ∧
    (4*(s k:ℝ)*m/(q₂ k b:ℝ) ≤ 2*(Δ:ℝ)/(s k:ℝ) ∧
      2*(Δ:ℝ)/(s k:ℝ) ≤ 1) ∧
    ((s k:ℝ)^2*(rho b:ℝ) ≤ (s k:ℝ)^(-(2:ℝ)) ∧
      (s k:ℝ)^(-(2:ℝ)) ≤ 1/4) ∧
    ((s k:ℝ)*(q₁ k:ℝ)/(q₂ k b:ℝ) ≤ (s k:ℝ)^(-(4:ℝ)) ∧
      (s k:ℝ)^(-(4:ℝ)) ≤ (ζ:ℝ)/128) ∧
    (max ((q₂ k b:ℝ)*(x b:ℝ)) (max ((s k:ℝ)*(x b:ℝ)) ((w k:ℝ)*(x b:ℝ))) ≤
      (s k:ℝ)^(-(24:ℝ)) ∧ (s k:ℝ)^(-(24:ℝ)) ≤ 1/10000) ∧
    ((w k:ℝ)^2*(x b:ℝ)/(eta k:ℝ) ≤ (s k:ℝ)^(-(14:ℝ)) ∧
      (s k:ℝ)^(-(14:ℝ)) ≤ 1/(32*(255/256:ℝ))) ∧
    ((w k:ℝ)^2*(q₂ k b:ℝ)*(x b:ℝ) ≤ (s k:ℝ)^(-(10:ℝ)) ∧
      (s k:ℝ)^(-(10:ℝ)) ≤ 1) ∧
    ((w k:ℝ)*(q₂ k b:ℝ)*(x b:ℝ)/(eta k:ℝ) ≤ (s k:ℝ)^(-(16:ℝ)) ∧
      (s k:ℝ)^(-(16:ℝ)) ≤ 1/(128*(1/256:ℝ))) ∧
    ((V38Moments.exceptionCount ((theta k:ℝ)/4) 1:ℝ)/((s k:ℝ)*(q₂ k b:ℝ)) ≤
      (2:ℝ)^85*(s k:ℝ)^(-(53:ℝ)/8) ∧
      (2:ℝ)^85*(s k:ℝ)^(-(53:ℝ)/8) ≤ 1) ∧
    ((V38Schedule.C128:ℝ)*(s k:ℝ)^(-(128:ℝ))/(theta k:ℝ) ≤
      512*(V38Schedule.C128:ℝ)*(s k:ℝ)^(-(104:ℝ)) ∧
      512*(V38Schedule.C128:ℝ)*(s k:ℝ)^(-(104:ℝ)) ≤ 1/4) ∧
    (2*(s k:ℝ)*(2*(V38Moments.exceptionCount (theta k:ℝ) ((eta k:ℝ)/2):ℝ))/
      ((eta k:ℝ)*(w k:ℝ)) ≤ (2:ℝ)^89*(s k:ℝ)^(-(5:ℝ)/8) ∧
      (2:ℝ)^89*(s k:ℝ)^(-(5:ℝ)/8) ≤ 1/16) := by
  have hk200:200 ≤ k := (cutoff_small δv ζ Δ k hδ hζ hk).1
  obtain ⟨q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11⟩ :=
    V42NumericMargins.width_margins_middle k b n m Δ (by omega) hb hn hdeg
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11⟩ :=
    V42NumericAllowances.middle_allowances δv ζ Δ k hδ hζ hk
  exact ⟨⟨q1,a1⟩,⟨q2,a2⟩,⟨q3,a3⟩,⟨q4,a4⟩,⟨q5,a5⟩,⟨q6,a6⟩,
    ⟨q7,a7⟩,⟨q8,a8⟩,⟨q9,a9⟩,⟨q10.le,a10⟩,⟨q11,a11⟩⟩

#print axioms V42NumericAllowances.sourceAllowance_real
#print axioms V42NumericAllowances.middle_allowances
#print axioms width_margins_chain
#print axioms V42NumericMargins.exception_substitutions

end
end CurrentAdditive.V42WidthMarginsChain
