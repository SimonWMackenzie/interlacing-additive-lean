import CurrentAdditive.V42FullProfiles
import CurrentAdditive.V39ThreeTail

/-! Source-facing full-product collision clause of v42 src:profiles.
The retained columns are original Gamma words with their original iid law.
Their jointly selected head/tail coordinates are used only in the proof-side
projection; the conclusion keeps every original retained word label. -/
namespace CurrentAdditive.V42FullGammaTail

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42FullSuccessor V42PublicSchedule

def headTailPositions {q₁ s : ℕ} (tail : Fin 3 → Fin (s+1))
    (i : Fin (q₁+3)) : Fin (q₁+s+1) :=
  if hi : i.val<q₁ then ⟨i.val,by omega⟩
  else ⟨q₁+(tail ⟨i.val-q₁,by omega⟩).val,by
    have h := (tail ⟨i.val-q₁,by omega⟩).isLt
    omega⟩

theorem headTailPositions_injective {q₁ s : ℕ}
    (tail : Fin 3 → Fin (s+1)) (htail : Function.Injective tail) :
    Function.Injective (headTailPositions (q₁ := q₁) tail) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  by_cases hi : i.val<q₁ <;> by_cases hj : j.val<q₁
  · simp only [headTailPositions,dif_pos hi,dif_pos hj] at hv
    exact Fin.ext hv
  · simp only [headTailPositions,dif_pos hi,dif_neg hj] at hv
    omega
  · simp only [headTailPositions,dif_neg hi,dif_pos hj] at hv
    omega
  · simp only [headTailPositions,dif_neg hi,dif_neg hj] at hv
    have he : tail ⟨i.val-q₁,by omega⟩=tail ⟨j.val-q₁,by omega⟩ := by
      apply Fin.ext
      omega
    have hh := congrArg Fin.val (htail he)
    change i.val-q₁=j.val-q₁ at hh
    apply Fin.ext
    omega

theorem head_position {q₁ s : ℕ} (tail : Fin 3 → Fin (s+1)) (i : Fin q₁) :
    headTailPositions tail (Fin.castAdd 3 i)=Fin.castAdd (s+1) i := by
  simp only [headTailPositions,Fin.val_castAdd,dif_pos i.isLt]
  rfl

theorem tail_position {q₁ s : ℕ} (tail : Fin 3 → Fin (s+1)) (i : Fin 3) :
    (headTailPositions tail (Fin.natAdd q₁ i)).val=q₁+(tail i).val := by
  have hnot : ¬q₁+i.val<q₁ := by omega
  simp [headTailPositions,Fin.val_natAdd,hnot]

/-- The exact original-Gamma statement before fixing a public schedule.
The tail function may select any three pairwise distinct tail positions. -/
theorem gamma_tail_lower {X Y : Type*} [Fintype X] [Fintype Y] {q₁ s : ℕ}
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (R : X → Y → Bool)
    (d a : ℕ) (ρ : ℝ) (hd : 2≤d) (hρ : 0<ρ) (hs : s=2^a)
    (hq : q₁+3=s+1) (hscale : 2*(s:ℝ)*ρ≤1)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d:ℤ))
    (tail : Fin 3 → Fin (s+1)) (htail : Function.Injective tail)
    (Rows : Set (Fin (q₁+3) × X)) (Gamma : Set (Word q₁ s Y))
    (hRows : ∀ i,2*(s:ℝ)*ρ≤μ.toFiniteLaw.prob (fun u => (i,u)∈Rows))
    (hGamma : (1/2:ℝ)<(ν.iid (q₁+s+1)).toFiniteLaw.prob (·∈Gamma)) :
    d+a+1≤Compression.restrictionD
      (fun (i : Fin (q₁+3) × X) (γ : Word q₁ s Y) =>
        R i.2 (γ (headTailPositions tail i.1))) Rows Gamma :=
  V39ThreeTail.word_positions_lower μ ν R d a ρ hd hρ hs hq hscale hp
    (headTailPositions tail) (headTailPositions_injective tail htail) Rows Gamma hRows hGamma

theorem full_capacity (L : ℕ) (hb : 4*fullExponent L≤L) :
    2*(fullS L:ℝ)*(V42Schedule.rho L:ℝ)≤1 := by
  have hk : 1≤fullExponent L := by unfold fullExponent; omega
  have he : 2*(V42Schedule.s (fullExponent L):ℚ)*V42Schedule.rho L=
      (2:ℚ)^(1+fullExponent L)/2^L := by
    simp only [V42Schedule.s,V42Schedule.rho,Nat.cast_pow,Nat.cast_ofNat,pow_add,pow_one]
    ring
  have hh : 2*(V42Schedule.s (fullExponent L):ℚ)*V42Schedule.rho L≤1 := by
    rw [he]
    simpa using V42Schedule.ratio_le (1+fullExponent L) L 0 0 (by omega)
  change 2*(V42Schedule.s (fullExponent L):ℝ)*(V42Schedule.rho L:ℝ)≤1
  exact_mod_cast hh

/-- Full-product public recipe, final collision clause of src:profiles.
H1=d+log(s)=d+fullExponent(L); x_cap=2s*rho. The retained column
set stays in the original Gamma domain with the original whole-word law. -/
theorem full_gamma_tail_lower {X Y : Type*} [Fintype X] [Fintype Y]
    (L : ℕ) (hb : 4*fullExponent L≤L)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (R : X → Y → Bool)
    (d : ℕ) (hd : 3≤d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      (V42Schedule.rho L:ℝ) (d:ℤ))
    (tail : Fin 3 → Fin (fullS L+1)) (htail : Function.Injective tail)
    (Rows : Set (Fin (fullQ₁ L+3) × X)) (Gamma : Set (Word (fullQ₁ L) (fullS L) Y))
    (hRows : ∀ i,2*(fullS L:ℝ)*(V42Schedule.rho L:ℝ)≤
      μ.toFiniteLaw.prob (fun u => (i,u)∈Rows))
    (hGamma : (1/2:ℝ)<(ν.iid (fullQ₁ L+fullS L+1)).toFiniteLaw.prob (·∈Gamma)) :
    d+fullExponent L+1≤Compression.restrictionD
      (fun (i : Fin (fullQ₁ L+3) × X) (γ : Word (fullQ₁ L) (fullS L) Y) =>
        R i.2 (γ (headTailPositions tail i.1))) Rows Gamma := by
  have hs := fullS_ge_256 L
  have hq : fullQ₁ L+3=fullS L+1 := by unfold fullQ₁; omega
  exact gamma_tail_lower μ ν R d (fullExponent L) (V42Schedule.rho L:ℝ)
    (by omega) (by unfold V42Schedule.rho; positivity) rfl hq (full_capacity L hb)
    hp tail htail Rows Gamma hRows hGamma

#print axioms headTailPositions_injective
#print axioms gamma_tail_lower
#print axioms full_gamma_tail_lower

end CurrentAdditive.V42FullGammaTail
