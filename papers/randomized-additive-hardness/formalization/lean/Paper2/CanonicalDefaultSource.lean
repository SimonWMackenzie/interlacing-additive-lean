import Paper2.RecursiveDefaults
import Paper2.ScannedSourceGuarantees

/-! A fully explicit canonical choice of recursive tails for the finite graph source.
The actual output constructor below uses no choice of tails or carrier order. -/

namespace Paper2.CanonicalDefaultSource

open SourceMatrix SourceProfileParameters SourceDeficiency SourceSurvivingCollisions
  SourceRecursiveNoSampling Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

/-- Public recursive defaults: the all-false seed row, seed column zero,
and the vertex-zero item in group zero. No promise or graph-dependent choice
enters this computable family. -/
def canonicalDefaultTails (L n w Q : ℕ)
    (hn : 0 < n) (hw : 0 < w) (hQ : 0 < Q) :
    SourceIteration.FixedTails L (width L) (width L - 2)
      (outerWidth L) w Q (Fin n) :=
  RecursiveEntries.defaultTails
    (fun _ : Fin (LookupSeed.width L) => false)
    (⟨0, by unfold LookupSeed.width; positivity⟩ : Fin (LookupSeed.width L))
    ((⟨0, by have := SourceProfiles.width_ge_four L; omega⟩,
      .inl ⟨0, hn⟩) : SourceConstruction.Items (width L) (Fin n))
    (by unfold outerWidth; positivity) hw hQ

/-- The actual canonical finite source on a correctly sized literal bit
list. The scan, coordinate/vertex orders and recursive tails are fixed
explicitly. This is not a parser for arbitrary raw byte strings. -/
def canonicalSourceOutput {n m : ℕ} (L : ℕ)
    (edge : Fin m → Bool → Fin n) (rep : ℕ)
    (hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) * rep)
    (w r Q q : ℕ) (hn : 0 < n) (hw : 0 < w) (hQ : 0 < Q)
    (k : ℕ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L) w Q
      (LookupSeed.width L) k (sourceRows L r q k) (sourceCols L r q k)) :=
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero w := ⟨Nat.ne_of_gt hw⟩
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  RecursiveSamplingMaterialization.materializeTapeList
    (finCongr (Fintype.card_fin n))
    (SourceProfiles.width_ge_four L) (LookupSeed.width L)
    (by unfold LookupSeed.width; positivity)
    (SourceActiveRank.scanAtCanonical edge (by
      have := SourceProfiles.width_ge_four L; omega) hq)
    (canonicalDefaultTails L n w Q hn hw hQ)
    k (sourceRows L r q k) (sourceCols L r q k) bits

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The canonical default-tail constructor satisfies the exact finite
source guarantees at every iteration, including iteration zero. The NO
premise is conditional on the displayed graph gap only; no colouring or
cost certificate is used to select the constructor. -/
theorem selected_canonical_default_finite_guarantees
    {n m : ℕ} [NeZero n]
    (L : ℕ) (hL : 16 ≤ L)
    (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) * rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < m)
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
        (deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L))) ≤ w)
    (hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)))
    (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) / 32)
    (hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q
        (deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L))) ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) * w / 16)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (hsmallwx : (w : ℝ) * x L ≤ 1 / 10000)
    (hmargin : 2 * w * x L +
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1)
    (hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
      (deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) /
        (16 * (w : ℝ))))
    (hsize : 2 * (n + width L - 3) ≤ outerWidth L)
    (k : ℕ) :
    let output := canonicalSourceOutput L edge rep hq w r Q q
      (NeZero.pos n) (NeZero.pos w) (NeZero.pos Q) k
    (∀ bits, D (output bits).matrix ≤ sourceCost L r q k) ∧
    (∀ colour : Fin n → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      ∀ bits, D (output bits).matrix ≤ sourceBudget L r q k) ∧
    ((∀ colour : Fin n → Fin 3, γ * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) →
      1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
          (sourceRows L r q k) (sourceCols L r q k)).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k) ∧
      1 - (1 / 2 : ℝ) ^ 11 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
          (sourceRows L r q k) (sourceCols L r q k)).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k)) ∧
    (∀ bits, (output bits).bits.length =
      sourceRows L r q k * sourceCols L r q k) := by
  exact ScannedSourceGuarantees.selected_scanned_combined_finite_guarantees
    L hL edge loopless rep Δ hΔ hq hdegree γ hγ hE
    hinner houter hwide href hscale hcountSource
    w r Q q hw hw2 hQ hquarter hsmall hfirst hlast hKcheck
    hxsmall hstar hsmallwx hmargin hbridge hsize
    (canonicalDefaultTails L n w Q (NeZero.pos n) (NeZero.pos w) (NeZero.pos Q)) k

end Paper2.CanonicalDefaultSource


