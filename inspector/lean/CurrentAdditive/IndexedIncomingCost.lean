import CurrentAdditive.IndexedIncomingSection

/-! Apply the proved rare-boost theorem to the original selector section and
transfer the resulting lower bound to the actual retained W-node rectangle. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

theorem incoming_section_cost
    (R : Set (Fin w × Column src)) (b : Bool)
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y) (md : streams.metadataStream.Label)
    (base : streams.baseStream.Label)
    (E Q : Finset (Fin w × Fin q₂))
    (H₁ a : ℕ) (x θ δ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ H₁) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x (H₁ : ℤ))
    (hcount : 2^(a-1)+1 ≤ Q.card)
    (hδscale : (2 : ℝ)^a * x ≤ δ/4)
    (hθ : 0 < θ)
    (hsection : θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
      (fun sel => (md, (base, sel)) ∈ Ystar))
    (hQ : ∀ z ∈ Q, z ∉ E ∧
      streams.metadataStream.decode md z.1 =
        .inl (templateBin src streams md z.1) ∧
      δ/4 ≤ src.gamma.law.toFiniteLaw.prob
        (fun γ => γ ∈ protectedFibre src w R b z.1
          (templateBin src streams md z.1) z.2))
    (hTV : ∀ J : Finset (Fin (w*q₂)),
      J ⊆ Finset.univ \ E.image
        (incomingCoord (q₂ := q₂) (w := w)).symm → J.card ≤ 8 →
      projectionTV
        (condition streams.selectorStream.law.toFiniteLaw
          (fun sel => (md, (base, sel)) ∈ Ystar)
          (lt_of_lt_of_le (by linarith : 0 < θ/4) hsection))
        (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
        (incomingDecode src streams) J ≤
          conditioningEpsilonR 1024 (θ/4) (δ/2)) :
    H₁+a ≤ Paper2.Compression.restrictionD
      (fun pc t => W src streams R₀ activity ξ₀ t pc) R Ystar := by
  classical
  let e : Fin (w*q₂) ≃ Fin w × Fin q₂ := incomingCoord
  let Good : Finset (Fin (w*q₂)) := Q.image e.symm
  let Bad : Finset (Fin (w*q₂)) := E.image e.symm
  let Rows : Fin (w*q₂) → Set src.gamma.Label :=
    fun i => incomingRows src streams R b md (e i)
  let K : Set streams.selectorStream.Label :=
    fun sel => (md, (base, sel)) ∈ Ystar
  have hGood (i : Fin (w*q₂)) (hi : i ∈ Good) : e i ∈ Q := by
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    have heq : e i = z := by
      calc
        e i = e (e.symm z) := congrArg e hzi.symm
        _ = z := e.apply_symm_apply z
    simpa only [heq] using hz
  have hBad (i : Fin (w*q₂)) (hi : i ∈ Bad) : e i ∈ E := by
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    have heq : e i = z := by
      calc
        e i = e (e.symm z) := congrArg e hzi.symm
        _ = z := e.apply_symm_apply z
    simpa only [heq] using hz
  have hGoodcard : Good.card = Q.card :=
    Finset.card_image_of_injective Q e.symm.injective
  have hcount' : 2^(a-1)+1 ≤ Good.card := by rw [hGoodcard]; exact hcount
  have houtside : ∀ i ∈ Good, i ∉ Bad := by
    intro i hi hn
    exact (hQ (e i) (hGood i hi)).1 (hBad i hn)
  have hrow : ∀ i ∈ Good, (2 : ℝ)^a * x ≤
      src.gamma.law.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i hi
    exact hδscale.trans (hQ (e i) (hGood i hi)).2.2
  have hv : 0 < θ/4 := by linarith
  have hv1 : θ/4 ≤ 1 :=
    hsection.trans (streams.selectorStream.law.toFiniteLaw.prob_le_one _)
  have hδpos : 0 < δ := by
    have hp : 0 < (2 : ℝ)^a * x := mul_pos (by positivity) hx
    linarith
  have hεpos : 0 < conditioningEpsilonR 1024 (θ/4) (δ/2) :=
    conditioningEpsilonR_pos (by norm_num) hv (by linarith)
  have hεcap : conditioningEpsilonR 1024 (θ/4) (δ/2) ≤
      (2 : ℝ)^(-20 : ℤ) / 1024 * (θ/4)^((1 : ℝ)/256) := by
    unfold conditioningEpsilonR
    have h := min_le_right (δ/2)
      (((2 : ℝ)^(-(20 : ℝ))) / (1024 : ℕ) *
        (θ/4)^((4 : ℝ)/1024))
    convert h using 1; norm_num
  have hcond : (1/2 : ℝ) ≤
      streams.selectorStream.law.toFiniteLaw.prob (· ∈ K) /
        streams.selectorStream.law.toFiniteLaw.prob (· ∈ K) := by
    have hKpos : 0 < streams.selectorStream.law.toFiniteLaw.prob (· ∈ K) := by
      simpa only [K] using hv.trans_le hsection
    rw [div_self (ne_of_gt hKpos)]
    norm_num
  have hlower := ArbitraryPrefix.rareboost_canonical_sharp
    src.gamma.law ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
    (A src R₀) streams.selectorStream.law.toFiniteLaw
    (incomingDecode src streams) (incoming_fin_dwise src streams)
    Good Bad Rows K K H₁ a x (θ/4)
    (conditioningEpsilonR 1024 (θ/4) (δ/2))
    ha hd hx hscale hprofile hcount' houtside hrow
    hv hv1 hsection (Set.Subset.rfl) hcond hεpos hεcap
    (by simpa only [Bad, K] using hTV)
  let S : Set ((Fin w × Fin q₂) × src.gamma.Label) :=
    ArbitraryPrefix.rowRectangle Q (incomingRows src streams R b md)
  have hmap : Paper2.Compression.restrictionD
      (fun row sel => A src R₀ row.2 (incomingDecode src streams sel row.1))
      (ArbitraryPrefix.rowRectangle Good Rows) K ≤
      Paper2.Compression.restrictionD
        (fun row sel => A src R₀ row.2
          (src.inner.decode (streams.selectorStream.decode sel row.1.1)
            row.1.2)) S K := by
    let f : (Fin (w*q₂) × src.gamma.Label) →
        ((Fin w × Fin q₂) × src.gamma.Label) :=
      fun row => (e row.1, row.2)
    have hf : Set.MapsTo f
        (ArbitraryPrefix.rowRectangle Good Rows) S := by
      intro row hr
      change row.1 ∈ Good ∧ row.2 ∈ Rows row.1 at hr
      exact ⟨hGood row.1 hr.1, hr.2⟩
    have hh := Paper2.SourceProjection.restrictionD_map_le
      (fun row sel => A src R₀ row.2
        (src.inner.decode (streams.selectorStream.decode sel row.1.1)
          row.1.2)) f id S K
      (ArbitraryPrefix.rowRectangle Good Rows) K hf (fun _ h => h)
    simpa [f, incomingDecode, incomingCoord, e] using hh
  have hflag : ∀ z ∈ Q, streams.metadataStream.decode md z.1 =
      .inl (templateBin src streams md z.1) := by
    intro z hz
    exact (hQ z hz).2.1
  exact hlower.trans (hmap.trans
    (incoming_rectangle_cost_le_node src streams R b Ystar R₀
      activity ξ₀ md base Q hflag))

#print axioms incoming_section_cost

end CurrentAdditive.DeterministicIndexedMatrix.Sources
