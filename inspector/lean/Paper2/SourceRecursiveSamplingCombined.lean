import Paper2.SourceRecursiveNoTapeList
import Paper2.RecursiveSamplingIterationUpper

/-!
# One literal recursive sampler for all finite source cases

The same fixed-length input-list sampler and the same printed table satisfy
pointwise universal/YES bounds and a conditional NO success bound. The graph
gap appears only as an antecedent of the NO conclusion; no colouring or gap
selects the sampler.
-/

namespace Paper2.SourceRecursiveSamplingCombined

open SourceMatrix SourceProfileParameters SourceDeficiency SourceSurvivingCollisions
  SourceRecursiveNoSampling Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Exact finite source-bound guarantees for one public bit-list sampler.
The fourth conclusion is a list-length fact, not a machine-time bound. -/
theorem selected_combined_finite_guarantees
    {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
    (L : ℕ) (hL : 16 ≤ L)
    (itemOrder : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
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
    (vertexOrder : Fin (Fintype.card V) ≃ V) (k : ℕ) :
    let output := fun bits : RecursiveSamplingMaterialization.TapeList V
        (width L) (width L - 2) (outerWidth L) w Q
        (LookupSeed.width L) k (sourceRows L r q k) (sourceCols L r q k) =>
      RecursiveSamplingMaterialization.materializeTapeList vertexOrder
        (SourceProfiles.width_ge_four L) (LookupSeed.width L)
        (by unfold LookupSeed.width; positivity)
        (SourceConstruction.activity itemOrder edge
          (by have := SourceProfiles.width_ge_four L; omega) rep hq)
        ξ k (sourceRows L r q k) (sourceCols L r q k) bits
    (∀ bits, D (output bits).matrix ≤ sourceCost L r q k) ∧
    (∀ colour : V → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      ∀ bits, D (output bits).matrix ≤ sourceBudget L r q k) ∧
    ((∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) →
      1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
        (RecursiveSamplingMaterialization.tapeListLaw V (width L)
          (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
          (sourceRows L r q k) (sourceCols L r q k)).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k) ∧
      1 - (1 / 2 : ℝ) ^ 11 ≤
        (RecursiveSamplingMaterialization.tapeListLaw V (width L)
          (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
          (sourceRows L r q k) (sourceCols L r q k)).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k)) ∧
    (∀ bits, (output bits).bits.length =
      sourceRows L r q k * sourceCols L r q k) := by
  classical
  let hs := SourceProfiles.width_ge_four L
  let p := LookupSeed.width L
  let hp : 0 < p := by dsimp [p, LookupSeed.width]; positivity
  let act := SourceConstruction.activity itemOrder edge (by omega : 3 ≤ width L)
    rep hq
  let mX := sourceRows L r q k
  let mY := sourceCols L r q k
  let output := fun bits : RecursiveSamplingMaterialization.TapeList V
      (width L) (width L - 2) (outerWidth L) w Q p k mX mY =>
    RecursiveSamplingMaterialization.materializeTapeList vertexOrder hs p hp
      act ξ k mX mY bits
  change (∀ bits, D (output bits).matrix ≤ sourceCost L r q k) ∧
    (∀ colour : V → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      ∀ bits, D (output bits).matrix ≤ sourceBudget L r q k) ∧
    ((∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) →
      1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
        (RecursiveSamplingMaterialization.tapeListLaw V (width L)
          (width L - 2) (outerWidth L) w Q p k mX mY).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k) ∧
      1 - (1 / 2 : ℝ) ^ 11 ≤
        (RecursiveSamplingMaterialization.tapeListLaw V (width L)
          (width L - 2) (outerWidth L) w Q p k mX mY).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k)) ∧
    (∀ bits, (output bits).bits.length = mX * mY)
  have hbase : exponent L + exponent L + outerExponent L + r + q =
      exponent L + outerExponent L + exponent L + r + q := by omega
  have hmul : k * (exponent L + exponent L + outerExponent L + r + q) =
      k * (exponent L + outerExponent L + exponent L + r + q) :=
    congrArg (fun n : ℕ => k * n) hbase
  have hB : LookupSeed.exponent L + 1 +
      k * (exponent L + exponent L + outerExponent L + r + q) =
      sourceBudget L r q k := by dsimp [sourceBudget]; omega
  have hC : LookupSeed.exponent L + 1 +
      k * (exponent L + exponent L + outerExponent L + r + q) + k =
      sourceCost L r q k := by
    dsimp [sourceCost]
    have hadd : k *
        (exponent L + outerExponent L + exponent L + r + q + 1) =
        k * (exponent L + outerExponent L + exponent L + r + q) + k := by
      simpa only [Nat.mul_one] using Nat.mul_add k
        (exponent L + outerExponent L + exponent L + r + q) 1
    omega
  constructor
  · intro bits
    have hrun := RecursiveSamplingExecution.run_selected_iteration_bounds L
      vertexOrder itemOrder edge hs rep hq ξ
      (exponent L) (outerExponent L) r q
      (by have := SourceProfiles.width_ge_four L; omega) rfl rfl hw hQ
      hsize k mX mY (RecursiveSamplingTape.readTape _ _ _ bits)
    have hout := RecursiveSamplingMaterialization.materialize_D vertexOrder
      hs p hp act ξ k mX mY (RecursiveSamplingTape.readTape _ _ _ bits)
    change D (output bits).matrix = _ at hout
    rw [hout]
    exact hrun.1.trans_eq hC
  constructor
  · intro colour proper bits
    have hrun := RecursiveSamplingExecution.run_selected_iteration_bounds L
      vertexOrder itemOrder edge hs rep hq ξ
      (exponent L) (outerExponent L) r q
      (by have := SourceProfiles.width_ge_four L; omega) rfl rfl hw hQ
      hsize k mX mY (RecursiveSamplingTape.readTape _ _ _ bits)
    have hout := RecursiveSamplingMaterialization.materialize_D vertexOrder
      hs p hp act ξ k mX mY (RecursiveSamplingTape.readTape _ _ _ bits)
    change D (output bits).matrix = _ at hout
    rw [hout]
    exact (hrun.2 colour proper).trans_eq hB
  constructor
  · intro gap
    have hstrong := SourceRecursiveNoTapeList.selected_tape_list_no_success L hL
      itemOrder edge loopless rep Δ hΔ hq hdegree γ hγ hE gap
      hinner houter hwide href hscale hcountSource w r Q q hw hw2 hQ
      hquarter hsmall hfirst hlast hKcheck hxsmall hstar hsmallwx
      hmargin hbridge hsize ξ vertexOrder k
    constructor
    · exact hstrong
    · norm_num at hstrong ⊢
      linarith
  · intro bits
    exact RecursiveSamplingMaterialization.materializeTapeList_length
      vertexOrder hs p hp act ξ k mX mY bits

#print axioms selected_combined_finite_guarantees

end Paper2.SourceRecursiveSamplingCombined
