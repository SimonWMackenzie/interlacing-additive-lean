import CurrentAdditive.V38Fin2Exact
import CurrentAdditive.V39SourceProfiles

/-!
Selected v39 `src:profiles`, final three-tail assertion. The word set is
an actual retained set in the original full-product word law. Projection
is joint, with the same originally retained representative for every row.
-/

namespace CurrentAdditive.V39ThreeTail

open Workspace.Types.CommComplexity Paper2
open Paper2.SourceMatrix Paper2.SourceProjection
open CurrentAdditive.ArbitraryPrefix

variable {X Y : Type*} [Fintype X] [Fintype Y] {q₁ s : ℕ}

theorem iid_eight_wise (ν : PositiveRationalLaw Y) (p : ℕ) :
    IsDWise 8 (ν.toFiniteLaw.iid p) (fun z : Fin p → Y => z) ν.toFiniteLaw := by
  intro J _ E
  exact FiniteLaw.pi_prob_restrict (fun _ : Fin p => ν.toFiniteLaw)
    (fun j : J => j.val) Subtype.val_injective E

/-- `q₁+3=s+1` real positions at the exact source capacity `2sρ`.
This uses only the current two-threshold base profile and its proved exact
eight-wise product-block bound. No lower bound on the desired restriction
is a hypothesis. -/
theorem interlace_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (d a : ℕ) (ρ : ℝ)
    (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hs : s=2^a) (hq : q₁+3=s+1)
    (hscale : 2*(s : ℝ)*ρ ≤ 1)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (U : Set (Fin (q₁+3) × X)) (W : Set (Fin (q₁+3) → Y))
    (hU : ∀ i, 2*(s : ℝ)*ρ ≤ μ.toFiniteLaw.prob (fun x => (i,x) ∈ U))
    (hW : (1/2 : ℝ) < (ν.toFiniteLaw.iid (q₁+3)).prob (· ∈ W)) :
    d+a+1 ≤ Compression.restrictionD (fullInterlace R (q₁+3)) U W := by
  classical
  have hpow : (2 : ℝ)^(a+1)=2*(s : ℝ) := by
    rw [hs, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    ring
  have hcount : 2^((a+1)-1)+1 ≤ (Finset.univ : Finset (Fin (q₁+3))).card := by
    simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
    omega
  let Rows : Fin (q₁+3) → Set X := fun i => {x | (i,x) ∈ U}
  have hRows : rowRectangle Finset.univ Rows=U := by
    ext z
    simp [rowRectangle, Rows]
  have hlower := V38Fin2Exact.exactboost μ ν R (ν.toFiniteLaw.iid (q₁+3))
    (fun z : Fin (q₁+3) → Y => z) (iid_eight_wise ν (q₁+3))
    Finset.univ Rows W d (a+1) ρ (by omega) hd hρ
    (by simpa only [hpow] using hscale) hp hcount
    (fun i _ => by simpa only [hpow, Rows, Set.mem_setOf_eq] using hU i)
    (by linarith : (9/25 : ℝ) ≤ (ν.toFiniteLaw.iid (q₁+3)).prob (· ∈ W))
  change d+(a+1) ≤ Compression.restrictionD (fullInterlace R (q₁+3))
    (rowRectangle Finset.univ Rows) W at hlower
  simpa only [hRows, Nat.add_assoc] using hlower

/-- Any injective selection of the head positions and three distinct tail
positions works. The theorem keeps the original whole-word labels and
therefore does not turn surviving correlated tuples into a product. -/
theorem word_positions_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (d a : ℕ) (ρ : ℝ)
    (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hs : s=2^a) (hq : q₁+3=s+1)
    (hscale : 2*(s : ℝ)*ρ ≤ 1)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (e : Fin (q₁+3) → Fin (q₁+s+1)) (he : Function.Injective e)
    (U : Set (Fin (q₁+3) × X)) (W : Set (Word q₁ s Y))
    (hU : ∀ i, 2*(s : ℝ)*ρ ≤ μ.toFiniteLaw.prob (fun x => (i,x) ∈ U))
    (hW : (1/2 : ℝ) < (ν.iid (q₁+s+1)).toFiniteLaw.prob (· ∈ W)) :
    d+a+1 ≤ Compression.restrictionD
      (fun (i : Fin (q₁+3) × X) (γ : Word q₁ s Y) => R i.2 (γ (e i.1))) U W := by
  have hmass := word_projection_mass ν e he W
  have hprojected : (1/2 : ℝ) <
      (ν.toFiniteLaw.iid (q₁+3)).prob (· ∈ wordProjection e '' W) := by
    simpa only [PositiveRationalLaw.toFiniteLaw_iid] using hW.trans_le hmass
  have hlower := interlace_lower μ ν R d a ρ hd hρ hs hq hscale hp
    U (wordProjection e '' W) hU hprojected
  exact hlower.trans (restrictionD_projected_le
    (fun (i : Fin (q₁+3) × X) (γ : Word q₁ s Y) => R i.2 (γ (e i.1)))
    (fullInterlace R (q₁+3)) id (wordProjection e) U W U
    (fun _ h => h) (fun _ _ _ _ => rfl))

#print axioms iid_eight_wise
#print axioms interlace_lower
#print axioms word_positions_lower

end CurrentAdditive.V39ThreeTail
