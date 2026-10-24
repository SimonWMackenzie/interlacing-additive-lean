import CurrentAdditive.IndexedIncomingSelected

/-! Appendix I `det:incoming`: protected receipt mass directly forces
enough original selector blocks, subject only to the public moment guard
and the explicit conditioning exception set. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.ProtectedDensityGroups

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

open Sources

/-- A failed `K_* κ` incoming bound at an actual Alice-prefix node yields
`sκq₂+1` genuine flattened selector coordinates after deleting every
conditioning exception.  It does not yet assert the node-cost contradiction. -/
theorem incoming_blocks_from_actual_receipts
    (r κ : ℕ) (R : Set (Fin w × Column src))
    (I₀ : Finset (Fin w))
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (θ : ℝ) (E : Finset (Fin w × Fin q₂))
    (hw : w = 2 ^ r) (hs : 0 < s) (hκ : 0 < κ)
    (hD : 8*256 ≤ D) (hθ : 0 < θ)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hE : E.card ≤ s * q₂)
    (hguard : ∀ m : ℕ,
      256 * (s : ℝ) * κ ≤ m →
      2 * ((64 : ℝ) * m) ^ 128 /
        (((255 / 256 : ℝ) - 1/2) * m) ^ 256 ≤ θ/4)
    (hmass : 1024 * (1 / 256 : ℝ) * (r + 2) * s * κ ≤
      ∑ i ∈ I₀, protectedReceipt src w R i) :
    ∃ b : Bool,
      ∃ δ : ℝ,
      ∃ md : streams.metadataStream.Label,
      ∃ base : streams.baseStream.Label,
      ∃ Q : Finset (Fin w × Fin q₂),
        0 < δ ∧
        θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
          (fun sel => (md, (base, sel)) ∈ Ystar) ∧
        Q.card = s * κ * q₂ + 1 ∧
        (∀ z ∈ Q, z ∉ E ∧
          streams.metadataStream.decode md z.1 =
            .inl (templateBin src streams md z.1) ∧
          δ / 4 ≤ src.gamma.law.toFiniteLaw.prob
            (fun γ => γ ∈ protectedFibre src w R b z.1
              (templateBin src streams md z.1) z.2)) := by
  classical
  obtain ⟨b, hlarge, j, hVI, hδpos, _hδone, _hδlow,
      hrow, hcount, hVcard⟩ :=
    incoming_density_group src w r κ R I₀ hw hs hκ hmass
  let δ : ℝ := (1 / 2 : ℝ) ^ j.val
  let V : Finset (Fin w) := dyadicGroup (protectedDensity src w R I₀ b)
    (∑ i, protectedDensity src w R I₀ b i) j
  have hVnon : V.Nonempty := by
    have hp : (0 : ℝ) < 256 * (s : ℝ) * κ := by positivity
    have hc : (0 : ℝ) < V.card := lt_of_lt_of_le hp hVcard
    exact Finset.card_pos.mp (Nat.cast_pos.mp hc)
  have hscaled : 256 * (s : ℝ) * κ ≤
      (∑ i, protectedDensity src w R I₀ b i) /
        (2 * (r + 2 : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r + 2 : ℝ))).2
    nlinarith [hlarge]
  have hsize : 256 * (s : ℝ) * κ ≤ (V.card : ℝ) * δ :=
    hscaled.trans hcount
  obtain ⟨md, base, VG, Q, _hVG, _hVGcard, hflag, hsection,
      hQcard, hQmem⟩ :=
    incoming_selected_blocks_of_group src streams r κ R I₀ V b δ
      Ystar θ E hD hδpos hVnon hVI (fun i hi => (hrow i hi).1)
      hsize hκ hE hθ hYstar
      (hguard V.card hVcard)
  refine ⟨b, δ, md, base, Q, hδpos, hsection, hQcard, ?_⟩
  intro z hz
  obtain ⟨hnot, hVG, hfibre⟩ := hQmem z hz
  exact ⟨hnot, hflag z.1 hVG, hfibre⟩

#print axioms incoming_blocks_from_actual_receipts

end CurrentAdditive.DeterministicIndexedMatrix
