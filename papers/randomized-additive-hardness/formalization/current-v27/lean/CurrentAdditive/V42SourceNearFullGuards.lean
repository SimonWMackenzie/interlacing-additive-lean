import CurrentAdditive.V42NearFullMargins
import CurrentAdditive.V39ActualGeneratedSource

namespace CurrentAdditive.V42SourceNearFullGuards

open Paper2 Paper2.SourceSurvivingCollisions V42Schedule

theorem source_guards_common (γ : ℚ) (Δ k b n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k) (hb : 4*k ≤ b) :
    0 < (eta k : ℝ) ∧ (eta k : ℝ) < 1/100 ∧
    (256/255 : ℝ)*(s k : ℝ)*(eta k : ℝ) ≤ 1/1000 ∧
    (eta k : ℝ) ≤ deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (s k) ∧
    4*(s k : ℝ)^2*(rho b : ℝ) ≤ 1 ∧
    8*(s k : ℝ)*(q₁ k : ℝ)+1024*(s k : ℝ)*(eta k : ℝ)*(q₂ k b : ℝ) <
      ((γ : ℝ)/24)*(q₂ k b : ℝ)/4 ∧
    2*(q₂ k b : ℝ)*(x b : ℝ) ≤ 1/8 ∧
    2*(2 : ℝ)^k*(x b : ℝ) < 999/1000 ∧
    (998/1000 : ℝ) ≤ 999/1000-2*((s k-1 : ℕ) : ℝ)*(x b : ℝ) := by
  let δv := V38Schedule.sourceDeltaV γ Δ n m
  let ζ := V38Schedule.sourceZeta γ
  have hδ : 0 < δv := by dsimp [δv,V38Schedule.sourceDeltaV]; positivity
  have hζ : 0 < ζ := by dsimp [ζ,V38Schedule.sourceZeta]; positivity
  obtain ⟨hη,hηsmall,hηtemplate,hallow,_hitem,hmargin,hsmall,hprefix,hdominant⟩ :=
    numeric_margins δv ζ Δ k b hδ hζ hk hb
  have hassign := (scalar_smallness k b
    (by have hh := (cutoff_small δv ζ Δ k hδ hζ hk).1; omega) hb).2.1
  have hallowR : (eta k : ℝ) ≤ ((sourceAllowance δv ζ/(s k : ℚ) : ℚ) : ℝ) :=
    Rat.cast_le.mpr hallow
  have he : ((sourceAllowance δv ζ/(s k : ℚ) : ℚ) : ℝ) =
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (s k) := by
    unfold sourceAllowance deletionAllowance SourceDeletionParameters.eta vertexTolerance witnessDensity
    simp only [Fintype.card_fin,Rat.cast_div,Rat.cast_min,Rat.cast_one,Rat.cast_pow,
      Rat.cast_ofNat,Rat.cast_natCast]
    have hδeq : (δv : ℝ)=(γ : ℝ)*m/(2*(Δ : ℝ)*n) := by
      simp [δv,V38Schedule.sourceDeltaV,Rat.cast_div,Rat.cast_mul]
    have hζeq : (ζ : ℝ)=(γ : ℝ)/24 := by simp [ζ,V38Schedule.sourceZeta]
    rw [hδeq,hζeq,show (1/256 : ℝ)*((γ : ℝ)/24)=((γ : ℝ)/24)/256 by ring,min_assoc]
    norm_num
    ring
  refine ⟨?_,?_,?_,hallowR.trans_eq he,?_,?_,?_,?_,?_⟩
  · exact_mod_cast hη
  · have hh := Rat.cast_lt (K := ℝ).mpr hηsmall
    push_cast at hh
    exact hh
  · have hh := Rat.cast_le (K := ℝ).mpr hηtemplate
    push_cast at hh
    exact hh
  · have hh := Rat.cast_le (K := ℝ).mpr hassign
    push_cast at hh
    exact hh
  · have hh := Rat.cast_lt (K := ℝ).mpr hmargin
    push_cast at hh
    simpa only [ζ,V38Schedule.sourceZeta,Rat.cast_div,Rat.cast_ofNat] using hh
  · have hh := Rat.cast_le (K := ℝ).mpr hsmall
    push_cast at hh
    exact hh
  · have hh := Rat.cast_lt (K := ℝ).mpr hprefix
    push_cast at hh
    simpa only [s,Nat.cast_pow,Nat.cast_ofNat] using hh
  · have hh := Rat.cast_le (K := ℝ).mpr hdominant
    push_cast at hh
    exact hh

theorem source_guards (γ : ℚ) (Δ k n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k) :
    0 < (eta k : ℝ) ∧ (eta k : ℝ) < 1/100 ∧
    (256/255 : ℝ)*(s k : ℝ)*(eta k : ℝ) ≤ 1/1000 ∧
    (eta k : ℝ) ≤ deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (s k) ∧
    4*(s k : ℝ)^2*(rho (4*k) : ℝ) ≤ 1 ∧
    8*(s k : ℝ)*(q₁ k : ℝ)+1024*(s k : ℝ)*(eta k : ℝ)*(q₂ k (4*k) : ℝ) <
      ((γ : ℝ)/24)*(q₂ k (4*k) : ℝ)/4 ∧
    2*(q₂ k (4*k) : ℝ)*(x (4*k) : ℝ) ≤ 1/8 ∧
    2*(2 : ℝ)^k*(x (4*k) : ℝ) < 999/1000 ∧
    (998/1000 : ℝ) ≤ 999/1000-2*((s k-1 : ℕ) : ℝ)*(x (4*k) : ℝ) :=
  source_guards_common γ Δ k (4*k) n m hγ hΔ hn hm hk le_rfl

#print axioms source_guards_common
#print axioms source_guards

end CurrentAdditive.V42SourceNearFullGuards

