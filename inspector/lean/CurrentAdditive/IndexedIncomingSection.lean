import CurrentAdditive.IndexedIncomingFin
import CurrentAdditive.ConditioningGeneralComplete

/-! The conditioning exception set is selected after the complete metadata
and base streams have been fixed.  All events remain on original indices. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

open Sources

theorem incoming_section_selected
    (κ : ℕ) (R : Set (Fin w × Column src))
    (I₀ V : Finset (Fin w)) (b : Bool) (δ : ℝ)
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (θ : ℝ)
    (hδ : 0 < δ) (hV : V.Nonempty) (hVI : V ⊆ I₀)
    (hrow : ∀ i ∈ V, δ / 2 < protectedDensity src w R I₀ b i)
    (hsize : 256 * (s : ℝ) * κ ≤ (V.card : ℝ) * δ)
    (hκ : 1 ≤ κ) (hθ : 0 < θ)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : 2 * ((64 : ℝ) * V.card) ^ 128 /
      (((255 / 256 : ℝ) - 1/2) * V.card) ^ 256 ≤ θ/4)
    (hException : conditioningExceptionCountR 1024 (θ/4) (δ/2) ≤ s*q₂) :
    ∃ md : streams.metadataStream.Label,
      ∃ base : streams.baseStream.Label,
      ∃ hsection : θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
          (fun sel => (md, (base, sel)) ∈ Ystar),
      ∃ E Q : Finset (Fin w × Fin q₂),
        E.card ≤ s*q₂ ∧ Q.card = s*κ*q₂+1 ∧
        (∀ z ∈ Q, z ∉ E ∧
          streams.metadataStream.decode md z.1 =
            .inl (templateBin src streams md z.1) ∧
          δ/4 ≤ src.gamma.law.toFiniteLaw.prob
            (fun γ => γ ∈ protectedFibre src w R b z.1
              (templateBin src streams md z.1) z.2)) ∧
        (∀ J : Finset (Fin (w*q₂)),
          J ⊆ Finset.univ \ E.image (incomingCoord (q₂ := q₂) (w := w)).symm →
          J.card ≤ 8 →
          projectionTV
            (condition streams.selectorStream.law.toFiniteLaw
              (fun sel => (md, (base, sel)) ∈ Ystar)
              (lt_of_lt_of_le (by linarith : 0 < θ/4) hsection))
            (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
            (incomingDecode src streams) J ≤
              conditioningEpsilonR 1024 (θ/4) (δ/2)) := by
  classical
  obtain ⟨md, base, VG, hVG, hVGcard, hflag, hsection⟩ :=
    incoming_template_group_section src streams V Ystar θ hθ
      (by norm_num) hYstar hguard
  let K : Set streams.selectorStream.Label :=
    fun sel => (md, (base, sel)) ∈ Ystar
  have hv : 0 < θ/4 := by linarith
  have hτ : 0 < δ/2 := by linarith
  obtain ⟨Efin, hEfin, hTV⟩ :=
    conditioning_exceptional_coordinates_R (R := 1024)
      (by norm_num) (by norm_num)
      streams.selectorStream.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      (incomingDecode src streams) (· ∈ K) (θ/4) (δ/2)
      hv hsection hτ (incoming_fin_dwise src streams)
  let E : Finset (Fin w × Fin q₂) :=
    Efin.image (incomingCoord (q₂ := q₂) (w := w))
  have hEcard : E.card ≤ s*q₂ := by
    rw [Finset.card_image_of_injective _
      (incomingCoord (q₂ := q₂) (w := w)).injective]
    exact hEfin.trans hException
  have hVGne : VG.Nonempty := by
    have hp : (0 : ℝ) < V.card := by
      exact_mod_cast Finset.card_pos.mpr hV
    have hp2 : (0 : ℝ) < VG.card := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast hp2)
  have hVGsize : 16 * (s : ℝ) * κ ≤ (VG.card : ℝ) * δ := by
    have hm := mul_le_mul_of_nonneg_right hVGcard hδ.le
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by positivity)
      (show (0 : ℝ) ≤ κ by positivity)]
  let p : Fin w → Fin s := templateBin src streams md
  have hmany : 2*s*κ*q₂ <
      (flatHeavyProtectedBlocks src w R VG b p δ).card := by
    rw [flatHeavyProtectedBlocks_card]
    exact heavy_protected_blocks_many src w s κ R I₀ VG b p δ
      (by omega) hVGne (hVG.trans hVI) hδ
      (fun i hi => hrow i (hVG hi)) hVGsize
  obtain ⟨Q, hQ, hQcard⟩ :=
    select_flat_protected_blocks src w s κ R VG b p δ E
      hκ hEcard hmany
  refine ⟨md, base, hsection, E, Q, hEcard, hQcard, ?_, ?_⟩
  · intro z hz
    have hz' := hQ hz
    have hblock := (Finset.mem_sdiff.mp hz').1
    have hnot := (Finset.mem_sdiff.mp hz').2
    have hmem := (mem_flatHeavyProtectedBlocks src w R VG b p δ z.1 z.2).mp hblock
    refine ⟨hnot, templateBin_eq_of_flag src streams md z.1
      (hflag z.1 hmem.1), ?_⟩
    exact (mem_heavyProtectedBins src w R b z.1 (p z.1) δ z.2).mp hmem.2
  · intro J hJ hcard
    have hEeq : E.image (incomingCoord (q₂ := q₂) (w := w)).symm = Efin := by
      ext a
      simp [E]
    rw [hEeq] at hJ
    simpa [K] using hTV J hJ hcard

#print axioms incoming_section_selected

end CurrentAdditive.DeterministicIndexedMatrix
