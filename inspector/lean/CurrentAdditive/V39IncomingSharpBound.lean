import CurrentAdditive.V39IncomingCapOne

namespace CurrentAdditive.V39IncomingSharpBound

open Paper2 Paper2.ProtectedDensityGroups
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- The current 512*mu incoming receipt bound on the actual two-tag
indexed internal matrix. The source profile has only its current two
thresholds and conditioning uses cap one exactly as in the manuscript. -/
theorem incoming_diagonal_mass_lt
    (r κ d a : ℕ) (x θ : ℝ)
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (I₀ : Finset (Fin w))
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s Y)
    (hw : w = 2^r) (hκ : 1 ≤ κ) (ha : 1 ≤ a) (hd : 2 ≤ d)
    (hpow : 2^a = 2*s*κ*q₂) (hx : 0 < x) (hθ : 0 < θ)
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (d : ℤ))
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : ∀ m : ℕ, 256*(s : ℝ)*κ ≤ m →
      2*((64 : ℝ)*m)^128 / (((255/256 : ℝ)-1/2)*m)^256 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (hnode : Compression.restrictionD
      (V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀) R Ystar < d+a) :
    ∑ i ∈ I₀, V39IncomingDensity.receipt (diagonalLaw src).toFiniteLaw w R i <
      512*(1/256 : ℝ)*(r+2)*s*κ := by
  classical
  by_contra hn
  have hmass := le_of_not_gt hn
  obtain ⟨hlarge,j,hVI,hδpos,hδone,hδlow,hrow,hsize,hcard⟩ :=
    V39IncomingDensity.sharp_density_group (diagonalLaw src).toFiniteLaw
      w r s κ R I₀ hw (NeZero.pos s) (by omega) hmass
  let dens := V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀
  let D₀ : ℝ := ∑ i, dens i
  let δ : ℝ := (1/2 : ℝ)^j.val
  let V := dyadicGroup dens D₀ j
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast (by omega : 0 < κ)
  have hVnon : V.Nonempty := by
    have hspos : (0 : ℝ) < s := Nat.cast_pos.mpr (NeZero.pos s)
    have hp : (0 : ℝ) < 256*(s : ℝ)*κ :=
      mul_pos (mul_pos (by norm_num) hspos) hκpos
    exact Finset.card_pos.mp (by exact_mod_cast lt_of_lt_of_le hp hcard)
  obtain ⟨md,base,hsection,E,Q,hQcard,hQ,hTV⟩ :=
    V39IncomingCapOne.select_cap_one_diagonal_blocks src streams κ R I₀ V δ θ
      Ystar hκ hδpos hθ hVnon hVI (fun i hi => (hrow i hi).1)
      hsize hYstar (hguard V.card hcard) hException
  have hwposNat : 0 < w := by rw [hw]; positivity
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hwposNat
  have hwone : (1 : ℝ) ≤ w := by
    exact_mod_cast (by omega : 1 ≤ w)
  have hr : (2 : ℝ) ≤ r+2 := by exact_mod_cast (by omega : 2 ≤ r+2)
  have hsκ : (0 : ℝ) ≤ (s : ℝ)*κ := by positivity
  have hDδ : D₀ ≤ 2*(w : ℝ)*δ := by
    calc
      D₀ ≤ δ*(2*(w : ℝ)) :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2*w)).mp hδlow
      _ = _ := by ring
  have hDlarge : 1024*(s : ℝ)*κ ≤ D₀ := by nlinarith
  have hwδ : (w : ℝ)*δ ≤ (w : ℝ)^2*δ := by
    have hh := mul_le_mul_of_nonneg_right hwone
      (mul_nonneg hwpos.le hδpos.le)
    nlinarith
  have h8 : 8*(s : ℝ)*κ ≤ (w : ℝ)^2*δ := by nlinarith
  have hpowR : (2 : ℝ)^a = 2*(s : ℝ)*κ*q₂ := by exact_mod_cast hpow
  have hthreshold : (2 : ℝ)^a*x ≤ δ/4 := by
    have hh := mul_le_mul_of_nonneg_left hwidth
      (show 0 ≤ 2*(s : ℝ)*κ by positivity)
    rw [hpowR]
    nlinarith [sq_pos_of_pos hwpos]
  have hscale : (2 : ℝ)^a*x ≤ 1 := by linarith
  let e : Fin (w*q₂) ≃ Fin w × Fin q₂ := incomingCoord
  let Good := Q.image e.symm
  let Bad := E.image e.symm
  have hmem (i : Fin (w*q₂)) (hi : i ∈ Good) : e i ∈ Q := by
    obtain ⟨z,hz,hzi⟩ := Finset.mem_image.mp hi
    have he : e i = z := by rw [← hzi,e.apply_symm_apply]
    simpa [he] using hz
  have hBad (i : Fin (w*q₂)) (hi : i ∈ Bad) : e i ∈ E := by
    obtain ⟨z,hz,hzi⟩ := Finset.mem_image.mp hi
    have he : e i = z := by rw [← hzi,e.apply_symm_apply]
    simpa [he] using hz
  have hcount : 2^(a-1)+1 ≤ Good.card := by
    rw [show Good.card = Q.card from Finset.card_image_of_injective Q e.symm.injective,
      hQcard]
    have he : 2^a = 2*2^(a-1) := by
      rw [← pow_succ']
      congr 1
      omega
    nlinarith
  have hOutside : ∀ i ∈ Good, i ∉ Bad := by
    intro i hi hn
    exact (hQ (e i) (hmem i hi)).1 (hBad i hn)
  have hrows : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob
      (fun γ => ((e i).1,Sum.inr ((e i).2,γ)) ∈ R) := by
    intro i hi
    exact hthreshold.trans (hQ (e i) (hmem i hi)).2.2
  have hflags : ∀ i ∈ Good, ∃ p : Fin s,
      streams.metadataStream.decode md (e i).1 = .inl p := by
    intro i hi
    exact (hQ (e i) (hmem i hi)).2.1
  have hv : 0 < θ/4 := by linarith
  have hv1 : θ/4 ≤ 1 :=
    hsection.trans (streams.selectorStream.law.toFiniteLaw.prob_le_one _)
  have hlower := V39IndexedIncomingLocal.selected_diagonal_section_cost
    src streams R₀ activity ξ₀ R Ystar md base Good Bad d a x (θ/4) 1
    ha hd hx hscale hprofile hcount hOutside hrows hflags hv hv1
    (by norm_num) hsection hTV
  omega

end CurrentAdditive.V39IncomingSharpBound

#print axioms CurrentAdditive.V39IncomingSharpBound.incoming_diagonal_mass_lt
