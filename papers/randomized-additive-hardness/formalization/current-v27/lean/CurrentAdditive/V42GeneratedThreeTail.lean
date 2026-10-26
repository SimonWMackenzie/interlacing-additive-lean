import CurrentAdditive.V42IndexedCollisionInterface
import CurrentAdditive.V42GeneratedSourceProfiles

/-! The full ANY-three-tail clause of v42 src:profiles for the actual
indexed Code D Gamma law. No product law for the entire decoded word is
assumed; the exact boost requests at most eight coordinates at a time. -/

namespace CurrentAdditive.V42GeneratedThreeTail

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open V42IndexedCollisionInterface

def coordinate (q₁ s : ℕ) (positions : Fin 3 ↪ Fin (s+1))
    (i : Fin (q₁+3)) : Fin (q₁+s+1) :=
  match finSumFinEquiv.symm i with
  | .inl r => ⟨r.val,by omega⟩
  | .inr j => ⟨q₁+(positions j).val,by have h:=(positions j).isLt; omega⟩

theorem coordinate_injective (q₁ s : ℕ) (positions : Fin 3 ↪ Fin (s+1)) :
    Function.Injective (coordinate q₁ s positions) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  apply finSumFinEquiv.symm.injective
  cases ha : finSumFinEquiv.symm a with
  | inl i =>
    cases hb : finSumFinEquiv.symm b with
    | inl j =>
      simp only [coordinate,ha,hb] at hv
      exact congrArg Sum.inl (Fin.ext hv)
    | inr j =>
      simp only [coordinate,ha,hb] at hv
      have hi := i.isLt
      omega
  | inr i =>
    cases hb : finSumFinEquiv.symm b with
    | inl j =>
      simp only [coordinate,ha,hb] at hv
      have hj := j.isLt
      omega
    | inr j =>
      simp only [coordinate,ha,hb] at hv
      apply congrArg Sum.inr
      apply positions.injective
      apply Fin.ext
      omega

section Generic

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

omit [NeZero s] in
theorem word_eq_coordinate (positions : Fin 3 ↪ Fin (s+1)) :
    threeTailWord src positions =
      fun γ i => src.gamma.decode γ (coordinate q₁ s positions i) := by
  funext γ i
  cases h : finSumFinEquiv.symm i with
  | inl r => simp only [threeTailWord,coordinate,h]; rfl
  | inr j => simp only [threeTailWord,coordinate,h]; rfl

omit [NeZero s] in
theorem original_gamma_eightwise (positions : Fin 3 ↪ Fin (s+1)) :
    IsDWise 8 src.gamma.law.toFiniteLaw (threeTailWord src positions) μY.toFiniteLaw := by
  classical
  rw [word_eq_coordinate src positions]
  intro J hJ E
  let e := coordinate q₁ s positions
  let T : Finset (Fin (q₁+s+1)) := J.image e
  have hT : T.card ≤ 8192 := (Finset.card_image_le).trans (hJ.trans (by norm_num))
  have hemem (j : J) : e j.val ∈ T := Finset.mem_image.mpr ⟨j.val,j.property,rfl⟩
  let f : J → T := fun j => ⟨e j.val,hemem j⟩
  have hf : Function.Injective f := by
    intro j k h
    exact Subtype.ext ((coordinate_injective q₁ s positions) (congrArg Subtype.val h))
  let E' : (T → Y) → Prop := fun z => E (fun j => z (f j))
  calc
    src.gamma.law.toFiniteLaw.prob
      (fun γ => E (fun j : J => src.gamma.decode γ (e j.val))) =
        (FiniteLaw.pi (fun _ : T => μY.toFiniteLaw)).prob E' := by
          simpa only [E',f] using src.gamma.exactLaw T hT E'
    _ = (FiniteLaw.pi (fun _ : J => μY.toFiniteLaw)).prob E := by
      simpa only [E',FiniteLaw.iid] using
        FiniteLaw.pi_prob_restrict (fun _ : T => μY.toFiniteLaw) f hf E

omit [NeZero s] in
theorem cost_of_two_threshold
    (R : X → Y → Bool) (d a : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hs : s=2^a) (hq : q₁+3=s+1) (hscale : 2*(s : ℝ)*ρ ≤ 1)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ)) :
    ThreeTailBound src R (d+a) (2*(s : ℝ)*ρ) := by
  classical
  intro positions Rows Words hrows hwords
  have hpow : (2 : ℝ)^(a+1)=2*(s : ℝ) := by rw [hs,pow_succ]; push_cast; ring
  have hcount : 2^((a+1)-1)+1 ≤ (Finset.univ : Finset (Fin (q₁+3))).card := by
    simp only [Nat.add_sub_cancel_right,Finset.card_univ,Fintype.card_fin]
    omega
  let fibers : Fin (q₁+3) → Set X := fun i u => (i,u) ∈ Rows
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin (q₁+3))),
      (2 : ℝ)^(a+1)*ρ ≤ μX.toFiniteLaw.prob (· ∈ fibers i) := by
    intro i _
    rw [hpow]
    exact hrows i
  have hrect : ArbitraryPrefix.rowRectangle (Finset.univ : Finset (Fin (q₁+3))) fibers=Rows := by
    ext a
    simp only [ArbitraryPrefix.rowRectangle,Finset.mem_univ,true_and,fibers]
    rfl
  have hl := V38Fin2Exact.exactboost μX μY R src.gamma.law.toFiniteLaw
    (threeTailWord src positions) (original_gamma_eightwise src positions)
    Finset.univ fibers Words d (a+1) ρ (by omega) hd hρ
    (by rw [hpow]; exact hscale) hp hcount hrow (by linarith)
  rw [hrect] at hl
  simpa only [Nat.add_assoc] using hl

end Generic

open V42Schedule

theorem generated_three_tail_bound
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {k : ℕ} [NeZero (q₁ k)] [NeZero (q₂ k (4*k))] [NeZero (s k)]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k) μX μY)
    (R : X → Y → Bool) (d : ℕ) (hk : 200 ≤ k) (hd : 2 ≤ d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      (rho (4*k) : ℝ) (d : ℤ)) :
    ThreeTailBound src R (d+k) (2*(s k : ℝ)*(rho (4*k) : ℝ)) := by
  obtain ⟨_,_,hρ,_,_,hsρ,_⟩ := V42GeneratedProfileGuards.scalar_parameters k hk
  have hs := (scalar_smallness k (4*k) (by omega) le_rfl).1
  exact cost_of_two_threshold src R d k (rho (4*k) : ℝ) hd hρ rfl
    (by unfold q₁; omega) (by linarith) hp

#print axioms coordinate_injective
#print axioms original_gamma_eightwise
#print axioms cost_of_two_threshold
#print axioms generated_three_tail_bound

end CurrentAdditive.V42GeneratedThreeTail
