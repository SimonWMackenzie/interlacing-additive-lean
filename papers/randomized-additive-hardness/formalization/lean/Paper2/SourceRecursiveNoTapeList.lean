import Paper2.SourceRecursiveNoSampling

/-!
# Literal fixed-length fair-bit inputs for the actual NO sampler

This only transports the checked capped-tape theorem along the existing
serialized-tape equivalence. It does not charge machine time or give a
malformed-list success probability.
-/

namespace Paper2.SourceRecursiveNoTapeList

open SourceMatrix SourceProfileParameters SourceDeficiency SourceSurvivingCollisions
  SourceRecursiveNoSampling Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Uniform literal bit lists of the public fixed length print the exact
NO-cost table with the same success margin as the checked capped tape. -/
theorem selected_tape_list_no_success
    {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
    (L : ℕ) (hL : 16 ≤ L)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
    (hcountSource : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity γ * outerWidth L / 16)
    (w r Q q : ℕ) [NeZero w] [NeZero Q]
    (hw : w = 2 ^ r) (hw2 : 2 ≤ w) (hQ : Q = 2 ^ q)
    (hquarter : 4 * ReferenceOwners.exceptionBudget
      (RestorationPublicCovers.e0 Q
        (deletionAllowance (V := V) (E := E) γ Δ (width L))) ≤ w)
    (hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)))
    (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
    (hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q
        (deletionAllowance (V := V) (E := E) γ Δ (width L))) ≤
      deletionAllowance (V := V) (E := E) γ Δ (width L) * w / 16)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (hsmallwx : (w : ℝ) * x L ≤ 1 / 10000)
    (hmargin : 2 * w * x L +
      deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1)
    (hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
      (deletionAllowance (V := V) (E := E) γ Δ (width L) /
        (16 * (w : ℝ))))
    (hsize : 2 * (Fintype.card V + width L - 3) ≤ outerWidth L)
    (ξ : SourceIteration.FixedTails L (width L) (width L - 2)
      (outerWidth L) w Q V)
    (sampleOrder : Fin (Fintype.card V) ≃ V) (k : ℕ) :
    1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
      (RecursiveSamplingMaterialization.tapeListLaw V (width L) (width L - 2)
        (outerWidth L) w Q (LookupSeed.width L) k
        (sourceRows L r q k) (sourceCols L r q k)).prob
        (fun bits => D (RecursiveSamplingMaterialization.materializeTapeList
          sampleOrder (SourceProfiles.width_ge_four L) (LookupSeed.width L)
          (by unfold LookupSeed.width; positivity)
          (SourceConstruction.activity order edge
            (by have := SourceProfiles.width_ge_four L; omega) rep hq)
          ξ k (sourceRows L r q k) (sourceCols L r q k) bits).matrix =
          sourceCost L r q k) := by
  let B := Nat.clog 2 (RecursiveSamplingExecution.alphabetCap (width L)
    (width L - 2) (outerWidth L) w Q (Fintype.card V) (LookupSeed.width L))
  let N := RecursiveSamplingExecution.drawCap (width L) (width L - 2)
    (outerWidth L) w Q (LookupSeed.width L) k
    (sourceRows L r q k) (sourceCols L r q k)
  let R := rejectionAttemptCap N
  have htape := selected_materialized_no_success L hL order edge loopless
    rep Δ hΔ hq hdegree γ hγ hE gap hinner houter hwide href hscale
    hcountSource w r Q q hw hw2 hQ hquarter hsmall hfirst hlast hKcheck
    hxsmall hstar hsmallwx hmargin hbridge hsize ξ sampleOrder k
  have hread := RecursiveSamplingTape.serializedTapeLaw_prob B R N
    (fun t => D (RecursiveSamplingMaterialization.materialize sampleOrder
      (SourceProfiles.width_ge_four L) (LookupSeed.width L)
      (by unfold LookupSeed.width; positivity)
      (SourceConstruction.activity order edge
        (by have := SourceProfiles.width_ge_four L; omega) rep hq)
      ξ k (sourceRows L r q k) (sourceCols L r q k) t).matrix =
      sourceCost L r q k)
  change _ ≤ _ at htape
  simpa only [RecursiveSamplingMaterialization.tapeListLaw,
    RecursiveSamplingMaterialization.materializeTapeList,
    RecursiveSamplingExecution.tapeLaw] using htape.trans_eq hread.symm

#print axioms selected_tape_list_no_success

end Paper2.SourceRecursiveNoTapeList
