import CurrentAdditive.IndexedTemplateGroup

/-! Appendix I `det:incoming`: the positive section, heavy indexed fibres,
and original flattened coordinates after exception deletion. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

open Sources

/-- From an actual protected density group, keep the original selector
coordinates that survive conditioning.  The only outside inputs are the
public 256th-moment guard and the conditioning theorem's exceptional set. -/
theorem incoming_selected_blocks_of_group
    (r κ : ℕ) (R : Set (Fin w × Column src))
    (I₀ V : Finset (Fin w)) (b : Bool) (δ : ℝ)
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (θ : ℝ) (E : Finset (Fin w × Fin q₂))
    (hD : 8*256 ≤ D) (hδ : 0 < δ)
    (hV : V.Nonempty) (hVI : V ⊆ I₀)
    (hrow : ∀ i ∈ V, δ / 2 < protectedDensity src w R I₀ b i)
    (hsize : 256 * (s : ℝ) * κ ≤ (V.card : ℝ) * δ)
    (hκ : 1 ≤ κ) (hE : E.card ≤ s * q₂)
    (hθ : 0 < θ)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : 2 * ((64 : ℝ) * V.card) ^ 128 /
      (((255 / 256 : ℝ) - 1/2) * V.card) ^ 256 ≤ θ/4) :
    ∃ md : streams.metadataStream.Label,
      ∃ base : streams.baseStream.Label,
      ∃ VG : Finset (Fin w),
      ∃ Q : Finset (Fin w × Fin q₂),
        VG ⊆ V ∧
        (V.card : ℝ) / 2 ≤ VG.card ∧
        (∀ i ∈ VG, streams.metadataStream.decode md i =
          .inl (templateBin src streams md i)) ∧
        θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
          (fun sel => (md, (base, sel)) ∈ Ystar) ∧
        Q.card = s * κ * q₂ + 1 ∧
        (∀ z ∈ Q, z ∉ E ∧ z.1 ∈ VG ∧
          δ / 4 ≤ src.gamma.law.toFiniteLaw.prob
            (fun γ => γ ∈ protectedFibre src w R b z.1
              (templateBin src streams md z.1) z.2)) := by
  classical
  obtain ⟨md, base, VG, hVG, hVGcard, hVGflag, hsection⟩ :=
    incoming_template_group_section src streams V Ystar θ hθ hD hYstar hguard
  have hVcard : (0 : ℝ) < V.card := by
    exact_mod_cast Finset.card_pos.mpr hV
  have hVGpos : 0 < VG.card := by
    exact_mod_cast (show (0 : ℝ) < VG.card by linarith)
  have hVGne : VG.Nonempty := Finset.card_pos.mp hVGpos
  have hVGsize : 16 * (s : ℝ) * κ ≤ (VG.card : ℝ) * δ := by
    have hmul := mul_le_mul_of_nonneg_right hVGcard hδ.le
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by positivity)
      (show (0 : ℝ) ≤ κ by positivity)]
  let p : Fin w → Fin s := templateBin src streams md
  have hmany : 2 * s * κ * q₂ <
      (flatHeavyProtectedBlocks src w R VG b p δ).card := by
    rw [flatHeavyProtectedBlocks_card]
    exact heavy_protected_blocks_many src w s κ R I₀ VG b p δ
      (by omega) hVGne (hVG.trans hVI) hδ
      (fun i hi => hrow i (hVG hi)) hVGsize
  obtain ⟨Q, hQ, hQcard⟩ := select_flat_protected_blocks src w s κ
    R VG b p δ E hκ hE hmany
  refine ⟨md, base, VG, Q, hVG, hVGcard, ?_, hsection, hQcard, ?_⟩
  · intro i hi
    exact templateBin_eq_of_flag src streams md i (hVGflag i hi)
  · intro z hz
    have hz' := hQ hz
    have hblock := (Finset.mem_sdiff.mp hz').1
    have hnot := (Finset.mem_sdiff.mp hz').2
    have hmem := (mem_flatHeavyProtectedBlocks src w R VG b p δ z.1 z.2).mp hblock
    refine ⟨hnot, hmem.1, ?_⟩
    exact (mem_heavyProtectedBins src w R b z.1 (p z.1) δ z.2).mp hmem.2

#print axioms incoming_selected_blocks_of_group

end CurrentAdditive.DeterministicIndexedMatrix
