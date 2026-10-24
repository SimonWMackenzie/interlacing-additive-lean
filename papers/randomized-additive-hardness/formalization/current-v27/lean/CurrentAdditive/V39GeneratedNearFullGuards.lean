import CurrentAdditive.V39GeneratedProfileGuards
import Paper2.SourceSurvivingCollisionsItems

namespace CurrentAdditive.V39GeneratedNearFullGuards

open Paper2 Paper2.SourceSurvivingCollisions V38Schedule

theorem source_guards (γ c : ℚ) (Δ L n m : ℕ)
    (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ)) :
    let s := generatedS L
    let x : ℝ := ((generatedX L : ℚ) : ℝ)
    let ρ : ℝ := ((generatedRho L : ℚ) : ℝ)
    let η : ℝ := ((generatedEta c L : ℚ) : ℝ)
    0 < η ∧ η < 1/100 ∧ (256/255 : ℝ)*s*η ≤ 1/1000 ∧
    η ≤ deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ s ∧
    4*(s : ℝ)^2*ρ ≤ 1 ∧
    8*(s : ℝ)*(generatedQ₁ L)+1024*s*η*(generatedQ₂ L) <
      ((γ : ℝ)/24)*(generatedQ₂ L)/4 ∧
    2*(generatedQ₂ L : ℝ)*x ≤ 1/8 ∧
    2*(2 : ℝ)^quarterCeil L*x < 999/1000 ∧
    (998/1000 : ℝ) ≤ 999/1000-2*((s-1 : ℕ) : ℝ)*x := by
  dsimp only
  let s := generatedS L
  let η : ℝ := ((generatedEta c L : ℚ) : ℝ)
  let x : ℝ := ((generatedX L : ℚ) : ℝ)
  let δ : ℝ := ((sourceDeltaV γ Δ n m : ℚ) : ℝ)
  let ζ : ℝ := ((sourceZeta γ : ℚ) : ℝ)
  rcases htests.1 with ⟨hs,hη,_hq,h4,hcount,hqx,hsx,hrest⟩
  change 256 ≤ s at hs
  change (generatedS L : ℚ)*generatedEta c L ≤
    min 1 (min (sourceDeltaV γ Δ n m) (sourceZeta γ/256))/2^16 at hη
  have hηR : (s : ℝ)*η ≤ min 1 (min δ (ζ/256))/65536 := by
    have hh : (((generatedS L : ℚ)*generatedEta c L : ℚ) : ℝ) ≤
        ((min 1 (min (sourceDeltaV γ Δ n m) (sourceZeta γ/256))/2^16 : ℚ) : ℝ) := by
      exact_mod_cast hη
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_min,Rat.cast_one,
      Rat.cast_pow,Rat.cast_ofNat,show (2 : ℝ)^16=65536 by norm_num] using hh
  have hη1 : (s : ℝ)*η ≤ 1/65536 := by
    have hh := min_le_left (1 : ℝ) (min δ (ζ/256))
    linarith
  have hηζ : (s : ℝ)*η ≤ ζ/16777216 := by
    have hh := (min_le_right (1 : ℝ) (min δ (ζ/256))).trans (min_le_right δ (ζ/256))
    linarith
  have hsR : (256 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hηpos : 0 < η := by
    dsimp [η,generatedEta]
    norm_num only [Rat.cast_div,Rat.cast_natCast]
    exact div_pos (by exact_mod_cast hc) hspos
  have hallow : η ≤ deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ s := by
    unfold deletionAllowance SourceDeletionParameters.eta vertexTolerance witnessDensity
    simp only [Fintype.card_fin]
    have hδ : δ=(γ : ℝ)*m/(2*(Δ : ℝ)*n) := by
      simp [δ,sourceDeltaV,Rat.cast_div,Rat.cast_mul]
    have hζ : ζ=(γ : ℝ)/24 := by simp [ζ,sourceZeta]
    rw [← hδ,← hζ,show (1/256 : ℝ)*ζ=ζ/256 by ring,min_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<65536*s)).2
    nlinarith
  have h4R : 4*(s : ℝ)^2*((generatedRho L : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h4
  have hcountR : 8*(s : ℝ)*(generatedQ₁ L) ≤ ζ*(generatedQ₂ L)/16 := by
    change 8*(generatedS L : ℚ)*(generatedQ₁ L) ≤ sourceZeta γ*(generatedQ₂ L)/16 at hcount
    dsimp only [s,ζ]
    exact_mod_cast hcount
  have hqxR : (generatedQ₂ L : ℝ)*x ≤ 1/10000 := by
    have hh : (((generatedQ₂ L : ℚ)*generatedX L : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by exact_mod_cast hqx
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hsxR : (s : ℝ)*x ≤ 1/10000 := by
    have hh : (((generatedS L : ℚ)*generatedX L : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by exact_mod_cast hsx
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hx : 0 < x := by
    have hh := (V39GeneratedProfileGuards.scalar_parameters c
      (sourceDeltaV γ Δ n m) (sourceZeta γ) L m htests).2.2.2.1
    exact hh
  have hζpos : 0 < ζ := by
    dsimp [ζ,sourceZeta]
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    positivity
  have hqpos : (0 : ℝ) < generatedQ₂ L := by
    unfold generatedQ₂ generatedN
    positivity
  have hmargin : 8*(s : ℝ)*(generatedQ₁ L)+1024*s*η*(generatedQ₂ L) <
      ((γ : ℝ)/24)*(generatedQ₂ L)/4 := by
    have hm := mul_le_mul_of_nonneg_right hηζ hqpos.le
    have hζq : 0 < ζ*(generatedQ₂ L) := mul_pos hζpos hqpos
    have hζ : ζ=(γ : ℝ)/24 := by simp [ζ,sourceZeta]
    rw [← hζ]
    nlinarith
  refine ⟨hηpos,?_,?_,hallow,h4R,hmargin,?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · linarith
  · have hpow : (2 : ℝ)^quarterCeil L=(s : ℝ) := by simp [s,generatedS]
    rw [hpow]
    linarith
  · have hm : ((s-1 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
    have hh := mul_le_mul_of_nonneg_right hm hx.le
    linarith

end CurrentAdditive.V39GeneratedNearFullGuards

#print axioms CurrentAdditive.V39GeneratedNearFullGuards.source_guards
