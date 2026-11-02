import CurrentAdditive.V39IndexedIncomingLocal
import CurrentAdditive.V39IncomingDensity
import CurrentAdditive.IndexedTemplateGroup

/-! Actual diagonal receipt selection at the current cap-one conditioning
budget. Older two-family-free combinatorial helpers are reused through a
literal embedding that never inserts fixed-tail inputs into the matrix. -/

namespace CurrentAdditive.V39IncomingCapOne

open Paper2 Paper2.SourceMatrix
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

def embeddedRows (R : Set (Fin w × V38IndexedTwoTag.Column src)) :
    Set (Fin w × Sources.Column src) :=
  (fun pc => (pc.1,V38IndexedTwoTag.oldTag src pc.2)) '' R

theorem embedded_diagonal_iff
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (i : Fin w) (j : Fin q₂ × src.gamma.Label) :
    (i,Sources.Column.diagonal j) ∈ embeddedRows src R ↔ (i,Sum.inr j) ∈ R := by
  constructor
  · rintro ⟨⟨i',z⟩,hz,he⟩
    have hi : i' = i := congrArg Prod.fst he
    subst i'
    have htag := congrArg Prod.snd he
    cases z with
    | inl z => cases htag
    | inr j' =>
      have hj : j' = j := Sources.Column.diagonal.inj htag
      simpa only [hj] using hz
  · intro h
    exact ⟨(i,Sum.inr j),h,rfl⟩

theorem embedded_density
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (I₀ : Finset (Fin w)) (i : Fin w) :
    protectedDensity src w (embeddedRows src R) I₀ true i =
      V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀ i := by
  classical
  simp only [protectedDensity,V39IncomingDensity.density,ite_true]
  split_ifs
  · congr 1
    funext j
    exact propext (embedded_diagonal_iff src R i j)
  · rfl

theorem embedded_fibre
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (i : Fin w) (p : Fin s) (α : Fin q₂) :
    protectedFibre src w (embeddedRows src R) true i p α =
      {γ | (i,Sum.inr (α,γ)) ∈ R} := by
  ext γ
  simp only [protectedFibre,protectedImage,ite_true,Set.mem_setOf_eq]
  exact embedded_diagonal_iff src R i (α,γ)

/-- From one actual dyadic density class, choose complete streams first,
then the cap-one exceptional set, then K0/2+1 original good coordinates. -/
theorem select_cap_one_diagonal_blocks
    (κ : ℕ) (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (I₀ V : Finset (Fin w)) (δ θ : ℝ)
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (hκ : 1 ≤ κ) (hδ : 0 < δ) (hθ : 0 < θ)
    (hV : V.Nonempty) (hVI : V ⊆ I₀)
    (hrow : ∀ i ∈ V, δ/2 <
      V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀ i)
    (hsize : 256*(s : ℝ)*κ ≤ (V.card : ℝ)*δ)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : 2*((64 : ℝ)*V.card)^128 /
      (((255/256 : ℝ)-1/2)*V.card)^256 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂) :
    ∃ md : streams.metadataStream.Label,
      ∃ base : streams.baseStream.Label,
      ∃ hsection : θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
        (fun sel => (md,(base,sel)) ∈ Ystar),
      ∃ E Q : Finset (Fin w × Fin q₂),
        Q.card = s*κ*q₂+1 ∧
        (∀ z ∈ Q, z ∉ E ∧
          (∃ p : Fin s, streams.metadataStream.decode md z.1 = .inl p) ∧
          δ/4 ≤ src.gamma.law.toFiniteLaw.prob
            (fun γ => (z.1,Sum.inr (z.2,γ)) ∈ R)) ∧
        (∀ J : Finset (Fin (w*q₂)),
          J ⊆ Finset.univ \ E.image (incomingCoord (q₂ := q₂) (w := w)).symm →
          J.card ≤ 8 → projectionTV
            (condition streams.selectorStream.law.toFiniteLaw
              (fun sel => (md,(base,sel)) ∈ Ystar)
              (lt_of_lt_of_le (by linarith : 0 < θ/4) hsection))
            ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
            (incomingDecode src streams) J ≤ V38Moments.epsilon (θ/4) 1) := by
  classical
  obtain ⟨md,base,VG,hVG,hVGcard,hflag,hsection⟩ :=
    incoming_template_group_section src streams V Ystar θ hθ (by norm_num)
      hYstar hguard
  let K : Set streams.selectorStream.Label := fun sel => (md,(base,sel)) ∈ Ystar
  obtain ⟨Efin,hEfin,hTV⟩ := V38Moments.conditioning_outside_exception
    streams.selectorStream.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    (incomingDecode src streams) (incoming_fin_dwise src streams)
    K (θ/4) 1 (by linarith) (by norm_num) hsection
  let e : Fin (w*q₂) ≃ Fin w × Fin q₂ := incomingCoord
  let E := Efin.image e
  have hEcard : E.card ≤ s*q₂ := by
    rw [Finset.card_image_of_injective _ e.injective]
    exact hEfin.trans hException
  have hVGne : VG.Nonempty := by
    have hc : (0 : ℝ) < V.card := by exact_mod_cast Finset.card_pos.mpr hV
    have hc' : (0 : ℝ) < VG.card := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast hc')
  have hVGsize : 16*(s : ℝ)*κ ≤ (VG.card : ℝ)*δ := by
    have hh := mul_le_mul_of_nonneg_right hVGcard hδ.le
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by positivity)
      (show (0 : ℝ) ≤ κ by positivity)]
  let p := templateBin src streams md
  let Rold := embeddedRows src R
  have hmany : 2*s*κ*q₂ <
      (flatHeavyProtectedBlocks src w Rold VG true p δ).card := by
    rw [flatHeavyProtectedBlocks_card]
    apply heavy_protected_blocks_many src w s κ Rold I₀ VG true p δ
      (by norm_num) hVGne (hVG.trans hVI) hδ _ hVGsize
    intro i hi
    rw [embedded_density]
    exact hrow i (hVG hi)
  obtain ⟨Q,hQ,hQcard⟩ := select_flat_protected_blocks src w s κ
    Rold VG true p δ E hκ hEcard hmany
  refine ⟨md,base,hsection,E,Q,hQcard,?_,?_⟩
  · intro z hz
    have hz' := hQ hz
    have hm := (mem_flatHeavyProtectedBlocks src w Rold VG true p δ z.1 z.2).mp
      (Finset.mem_sdiff.mp hz').1
    refine ⟨(Finset.mem_sdiff.mp hz').2,
      ⟨p z.1,templateBin_eq_of_flag src streams md z.1 (hflag z.1 hm.1)⟩,?_⟩
    have hf := (mem_heavyProtectedBins src w Rold true z.1 (p z.1) δ z.2).mp hm.2
    simpa only [Rold,embedded_fibre] using hf
  · intro J hJ hcard
    have hEeq : E.image e.symm = Efin := by ext i; simp [E]
    change J ⊆ Finset.univ \ E.image e.symm at hJ
    rw [hEeq] at hJ
    exact hTV J hJ hcard

end CurrentAdditive.V39IncomingCapOne

#print axioms CurrentAdditive.V39IncomingCapOne.select_cap_one_diagonal_blocks
