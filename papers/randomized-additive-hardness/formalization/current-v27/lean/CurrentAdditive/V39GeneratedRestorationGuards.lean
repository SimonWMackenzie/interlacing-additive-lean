import CurrentAdditive.V39GeneratedAlignmentGuards

/-! Every numerical premise of final current two-threshold restoration from
the literal generated passing tests, including the seventh-source width.
-/

namespace CurrentAdditive.V39GeneratedRestorationGuards

open V38Schedule V39GeneratedAlignmentGuards

noncomputable section

abbrev Rho (L : ℕ) : ℝ := ((generatedRho L:ℚ):ℝ)
abbrev Delta (c : ℚ) (L : ℕ) : ℝ := Eta c L/(16*generatedW L)

theorem rho_eq_dyadic (L : ℕ) : Rho L=V39ExceptionBudget.dyadic L := by
  unfold Rho generatedRho generatedN V39ExceptionBudget.dyadic
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  push_cast
  simp only [one_div]

theorem delta_eq_cast (c : ℚ) (L : ℕ) :
    Delta c L=((deltaU (generatedEta c L) (generatedW L):ℚ):ℝ) := by
  simp only [Delta,deltaU,Eta,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]

structure Guards (c : ℚ) (L : ℕ) : Prop where
  phi_pos : 0 < Rho L
  phi_le_one : Rho L ≤ 1
  delta_pos : 0 < Delta c L
  delta_le : Delta c L ≤ 1/64
  width : 128*((V38Moments.exceptionCount (Rho L) (Delta c L/2):ℝ)+1) ≤ generatedQ L
  theta_budget : (generatedQ L:ℝ)*Theta L ≤ 1/20

theorem guards_of_tests (c δv ζ : ℚ) (L m : ℕ) (hc : 0 < c)
    (htests : GeneratedTests c L m δv ζ) : Guards c L := by
  have g := V39GeneratedAlignmentGuards.guards_of_tests c δv ζ L m hc htests
  have hφ : 0 < Rho L := by rw [rho_eq_dyadic]; exact V39ExceptionBudget.dyadic_pos _
  have hφ1 : Rho L ≤ 1 := by rw [rho_eq_dyadic]; exact V39ExceptionBudget.dyadic_le_one _
  have hw : (1:ℝ) ≤ generatedW L := by
    have hp : 0 < generatedW L := by unfold generatedW generatedN; positivity
    exact_mod_cast hp
  have hdpos : 0 < Delta c L := div_pos g.eta_pos (by positivity)
  have hdle : Delta c L ≤ 1/64 := by
    have hηs := htests.1.2.1
    change (generatedS L:ℚ)*generatedEta c L ≤ min 1 (min δv (ζ/256))/2^16 at hηs
    have hηs' : (generatedS L:ℚ)*generatedEta c L ≤ 1/2^16 :=
      hηs.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
    have hs : (1:ℚ) ≤ generatedS L := by exact_mod_cast (Nat.one_le_two_pow (n:=quarterCeil L))
    have hηpos : (0:ℚ) < generatedEta c L := by exact_mod_cast g.eta_pos
    have hηsmall : generatedEta c L ≤ 1/65536 := by norm_num at hηs'; nlinarith
    have hηR : Eta c L ≤ 1/65536 := by
      have h : ((generatedEta c L:ℚ):ℝ) ≤ ((1/65536:ℚ):ℝ) := by exact_mod_cast hηsmall
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
      exact h
    apply (div_le_iff₀ (by positivity : (0:ℝ)<16*generatedW L)).2
    nlinarith
  have hwidth : 128*((V38Moments.exceptionCount (Rho L) (Delta c L/2):ℝ)+1) ≤ generatedQ L := by
    let τ : ℚ := deltaU (generatedEta c L) (generatedW L)/2
    have hτpos : 0 < τ := by
      have hτ : (0:ℝ) < (τ:ℝ) := by
        have he : (τ:ℝ)=Delta c L/2 := by simp only [τ,Rat.cast_div,Rat.cast_ofNat,← delta_eq_cast]
        rw [he]
        positivity
      exact_mod_cast hτ
    have hτ1 : τ ≤ 1 := by
      have hτ : (τ:ℝ) ≤ 1 := by
        have he : (τ:ℝ)=Delta c L/2 := by simp only [τ,Rat.cast_div,Rat.cast_ofNat,← delta_eq_cast]
        rw [he]
        linarith
      exact_mod_cast hτ
    have hexc := V39GeneralExceptionBudget.exception_le_ebar L τ hτpos hτ1
    have hfinal := htests.2.2
    have hn : 128*(V38Moments.exceptionCount (V39ExceptionBudget.dyadic L) (τ:ℝ)+1) ≤ generatedQ L :=
      (Nat.mul_le_mul_left 128 (Nat.add_le_add_right hexc 1)).trans hfinal
    rw [rho_eq_dyadic]
    have he : (τ:ℝ)=Delta c L/2 := by simp only [τ,Rat.cast_div,Rat.cast_ofNat,← delta_eq_cast]
    rw [← he]
    exact_mod_cast hn
  have hθ := congrArg (fun z : ℚ => (z:ℝ)) (generated_Qtheta L)
  push_cast at hθ
  refine ⟨hφ,hφ1,hdpos,hdle,hwidth,?_⟩
  change (generatedQ L:ℝ)*((theta (generatedQ L):ℚ):ℝ) ≤ 1/20
  rw [hθ]
  norm_num

end
end CurrentAdditive.V39GeneratedRestorationGuards

#print axioms CurrentAdditive.V39GeneratedRestorationGuards.guards_of_tests
