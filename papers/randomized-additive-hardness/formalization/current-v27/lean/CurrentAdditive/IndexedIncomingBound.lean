import CurrentAdditive.IndexedIncomingCost

/-! The local incoming-mass contradiction on an actual first-Bob or final
node.  Numerical schedule and node-budget guards are exposed; no lower-bound
certificate or replacement matrix is a premise. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ProtectedDensityGroups
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- Appendix I `det:incoming` for the original indexed node.  Its mass
threshold is `K_*κ` in units of one complete source copy. -/
theorem incoming_protected_mass_lt
    (r κ H₁ a : ℕ) (x θ : ℝ)
    (R : Set (Fin w × Column src)) (I₀ : Finset (Fin w))
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (hw : w = 2^r) (hs : 0 < s) (hκ : 1 ≤ κ)
    (ha : 1 ≤ a) (hd : 2 ≤ H₁) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x (H₁ : ℤ))
    (hblocks : 2^(a-1) ≤ s*κ*q₂)
    (hδscale : ∀ j : Fin (r+2),
      (2 : ℝ)^a * x ≤ ((1/2 : ℝ)^j.val)/4)
    (hθ : 0 < θ)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : ∀ m : ℕ,
      256 * (s : ℝ) * κ ≤ m →
      2 * ((64 : ℝ) * m) ^ 128 /
        (((255 / 256 : ℝ) - 1/2) * m) ^ 256 ≤ θ/4)
    (hException : ∀ j : Fin (r+2),
      conditioningExceptionCountR 1024 (θ/4)
        (((1/2 : ℝ)^j.val)/2) ≤ s*q₂)
    (hnode : Paper2.Compression.restrictionD
      (fun pc t => W src streams R₀ activity ξ₀ t pc) R Ystar < H₁+a) :
    ∑ i ∈ I₀, protectedReceipt src w R i <
      1024 * (1/256 : ℝ) * (r+2) * s * κ := by
  classical
  by_contra hn
  have hmass : 1024 * (1/256 : ℝ) * (r+2) * s * κ ≤
      ∑ i ∈ I₀, protectedReceipt src w R i := le_of_not_gt hn
  obtain ⟨b, hlarge, j, hVI, hδpos, _hδone, _hδlow,
      hrow, hcount, hVcard⟩ :=
    incoming_density_group src w r κ R I₀ hw hs (by omega) hmass
  let δ : ℝ := (1/2 : ℝ)^j.val
  let V : Finset (Fin w) := dyadicGroup
    (protectedDensity src w R I₀ b)
    (∑ i, protectedDensity src w R I₀ b i) j
  have hVnon : V.Nonempty := by
    have hp : (0 : ℝ) < 256 * (s : ℝ) * κ := by positivity
    have hc : (0 : ℝ) < V.card := lt_of_lt_of_le hp hVcard
    exact Finset.card_pos.mp (Nat.cast_pos.mp hc)
  have hscaled : 256 * (s : ℝ) * κ ≤
      (∑ i, protectedDensity src w R I₀ b i) /
        (2 * (r+2 : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(r+2 : ℝ))).2
    nlinarith [hlarge]
  have hsize : 256 * (s : ℝ) * κ ≤ (V.card : ℝ) * δ :=
    hscaled.trans hcount
  obtain ⟨md, base, hsection, E, Q, _hEcard, hQcard,
      hQ, hTV⟩ :=
    incoming_section_selected src streams κ R I₀ V b δ Ystar θ
      hδpos hVnon hVI (fun i hi => (hrow i hi).1)
      hsize hκ hθ hYstar (hguard V.card hVcard)
      (hException j)
  have hQcount : 2^(a-1)+1 ≤ Q.card := by omega
  have hcost := incoming_section_cost src streams R b Ystar R₀
    activity ξ₀ md base E Q H₁ a x θ δ ha hd hx hscale
    hprofile hQcount (hδscale j) hθ hsection hQ hTV
  exact (not_lt_of_ge hcost) hnode

#print axioms incoming_protected_mass_lt

end CurrentAdditive.DeterministicIndexedMatrix.Sources
