import Paper2.CanonicalDefaultSource
import Paper2.PublicScheduleSourceSize

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-! Literal public parameter choices for the finite canonical source. -/

namespace Paper2.ParameterizedCanonicalSource

open SourceProfileParameters SourceDeficiency SourceSurvivingCollisions
  SourceRecursiveNoSampling Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

/-- The actual scheduled parameters, with no existential choices. -/
def rep (L m : ℕ) : ℕ :=
  SourceRepetitionScratch.sourceRep L (Fin m)
def restorationWidth (L : ℕ) : ℕ :=
  RestorationWidthScheduleScratch.width L
def restorationDepth (L : ℕ) : ℕ :=
  RestorationWidthScheduleScratch.depth L
def coverWidth (n m L Δ : ℕ) (γ : ℚ) : ℕ :=
  SourceOverheadBounds.actualQ (V := Fin n) (E := Fin m) L γ Δ
def coverDepth (n m L Δ : ℕ) (γ : ℚ) : ℕ :=
  SourceOverheadBounds.q (V := Fin n) (E := Fin m) L γ Δ

private theorem coverWidth_pos (n m L Δ : ℕ) (γ : ℚ) :
    0 < coverWidth n m L Δ γ := by
  unfold coverWidth SourceOverheadBounds.actualQ
    SourceRationalScheduleScratch.publicQ
  exact RestorationPublicQScratch.publicQ_pos _ _

private theorem restorationWidth_pos (L : ℕ) :
    0 < restorationWidth L := by
  unfold restorationWidth RestorationWidthScheduleScratch.width
  positivity

local instance (L : ℕ) : NeZero (restorationWidth L) :=
  ⟨Nat.ne_of_gt (restorationWidth_pos L)⟩
local instance (n m L Δ : ℕ) (γ : ℚ) :
    NeZero (coverWidth n m L Δ γ) :=
  ⟨Nat.ne_of_gt (coverWidth_pos n m L Δ γ)⟩

private theorem cast_le {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  exact_mod_cast h

private theorem cast_lt {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) := by
  exact_mod_cast h

/-- The actual capped, scanned, default-tail source on a correctly-sized
literal bit list. The public check supplies only proof-irrelevant evidence
for the coordinate quotient; the data choices above do not depend on it. -/
def output {n m : ℕ} (L Δ : ℕ) (γ : ℚ)
    (edge : Fin m → Bool → Fin n)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ)
    (hn : 0 < n) (k : ℕ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ)
      (LookupSeed.width L) k
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k)) :=
  CanonicalDefaultSource.canonicalSourceOutput L edge (rep L m)
    (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
      L (Fin m) hc.1)
    (restorationWidth L) (restorationDepth L)
    (coverWidth n m L Δ γ) (coverDepth n m L Δ γ)
    hn (restorationWidth_pos L) (coverWidth_pos n m L Δ γ)
    k bits

/-- The four exact finite guarantees for the single scheduled output. -/
def Guarantees {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) : Prop :=
  let o := output L Δ γ edge hc (NeZero.pos n) k
  let r := restorationDepth L
  let q := coverDepth n m L Δ γ
  let w := restorationWidth L
  let Q := coverWidth n m L Δ γ
  (∀ bits, D (o bits).matrix ≤ sourceCost L r q k) ∧
  (∀ colour : Fin n → Fin 3,
    (∀ e, colour (edge e false) ≠ colour (edge e true)) →
    ∀ bits, D (o bits).matrix ≤ sourceBudget L r q k) ∧
  ((∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
    ((Finset.univ.filter (fun e => colour (edge e false) =
      colour (edge e true))).card : ℝ)) →
    1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
      (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
        (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
        (sourceRows L r q k) (sourceCols L r q k)).prob
        (fun bits => D (o bits).matrix = sourceCost L r q k) ∧
    1 - (1 / 2 : ℝ) ^ 11 ≤
      (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
        (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
        (sourceRows L r q k) (sourceCols L r q k)).prob
        (fun bits => D (o bits).matrix = sourceCost L r q k)) ∧
  (∀ bits, (o bits).bits.length =
    sourceRows L r q k * sourceCols L r q k)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The decidable public check is enough to discharge every numeric guard
of the actual finite canonical source. -/
theorem checked_finite_guarantees {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < m)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) :
    Guarantees L Δ γ edge hc k := by
  have hc' := hc
  rcases hc' with ⟨hcoord, hsize, hscaleQ, hinnerQ, houterQ,
    hrefQ, hsmallwxQ, hwideQ, hcountQ, _, _, hstar,
    hmarginQ, hsmallQ, hxsmallQ, hfirstQ, hlastQ,
    hquarterQ, hKcheckQ, _, hL, _⟩
  let w := restorationWidth L
  let r := restorationDepth L
  let Q := coverWidth n m L Δ γ
  let q := coverDepth n m L Δ γ
  let η := SourceRationalScheduleScratch.eta
    (V := Fin n) (E := Fin m) L γ Δ
  have hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) * rep L m :=
    SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
      L (Fin m) hcoord
  have hw : w = 2 ^ r := rfl
  have hQ : Q = 2 ^ q :=
    SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ
  have hw2 : 2 ≤ w := by
    have hell : 1 ≤ RestorationWidthScheduleScratch.ell L := by
      unfold RestorationWidthScheduleScratch.ell
      have h := Nat.clog_mono_right 2 (show 2 ≤ L + 1 by omega)
      norm_num at h ⊢
      exact h
    have hr : 1 ≤ r := by
      have hp : 0 < (RestorationWidthScheduleScratch.ell L) ^ 2 :=
        pow_pos (by omega) _
      dsimp [r, restorationDepth, RestorationWidthScheduleScratch.depth]
      omega
    have hpow : 2 ^ 1 ≤ 2 ^ r := pow_le_pow_right₀ (by omega) hr
    simpa only [hw, pow_one] using hpow
  have hγR : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast hγ
  have hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1 := by
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.rhoQ_cast]
      using cast_le hscaleQ
  have hinner : (width L : ℝ) * rho L ≤ 1 / 1000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.rhoQ_cast]
      using cast_le hinnerQ
  have houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.xQ_cast]
      using cast_le houterQ
  have href : (width L : ℝ) * x L ≤ 1 / 10000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.xQ_cast]
      using cast_le hrefQ
  have hsmallwx : (w : ℝ) * x L ≤ 1 / 10000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.xQ_cast,
      w, restorationWidth] using cast_le hsmallwxQ
  have hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096 := by
    simpa only [Rat.cast_le, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Nat.cast_mul] using cast_le hwideQ
  have hcount : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity (γ : ℝ) * outerWidth L / 16 := by
    rw [← SourceRationalScheduleScratch.witnessDensity_cast]
    exact_mod_cast hcountQ
  have hη : (η : ℝ) = deletionAllowance (V := Fin n) (E := Fin m)
      (γ : ℝ) Δ (width L) :=
    SourceRationalScheduleScratch.eta_cast L γ Δ
  have hmargin : 2 * w * x L +
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1 := by
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.xQ_cast,
      SourceRationalScheduleScratch.eta_cast,
      CompletePublicScheduleScratch.gQ, w, restorationWidth,
      Nat.cast_mul] using cast_lt hmarginQ
  have hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
        (16 * (127 / 128 : ℝ)) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.xQ_cast,
      SourceRationalScheduleScratch.eta_cast,
      CompletePublicScheduleScratch.gQ, w, restorationWidth,
      Nat.cast_mul] using cast_le hsmallQ
  have hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1 := by
    rw [← CompletePublicScheduleScratch.xQ_cast]
    exact_mod_cast hxsmallQ
  have hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) / 32 := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.xQ_cast,
      SourceRationalScheduleScratch.eta_cast,
      CompletePublicScheduleScratch.muQ, w, restorationWidth]
      using cast_le hfirstQ
  have hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) / 32 := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.muQ,
      SourceRationalScheduleScratch.eta_cast, w, restorationWidth]
      using cast_le hlastQ
  have hquarter : 4 * ReferenceOwners.exceptionBudget
      (RestorationPublicCovers.e0 Q
        (deletionAllowance (V := Fin n) (E := Fin m)
          (γ : ℝ) Δ (width L))) ≤ w := by
    exact (RationalCoverSchedule.source_quarterCheck_real
      (V := Fin n) (Edges := Fin m) L w Q γ Δ).1 hquarterQ
  have hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q
        (deletionAllowance (V := Fin n) (E := Fin m)
          (γ : ℝ) Δ (width L))) ≤
      deletionAllowance (V := Fin n) (E := Fin m)
        (γ : ℝ) Δ (width L) * w / 16 := by
    exact (RationalCoverSchedule.source_kCheck_real
      (V := Fin n) (Edges := Fin m) L r w Q γ Δ).1 hKcheckQ
  have hEcard : 0 < Fintype.card (Fin m) := by simpa using hE
  have hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
      (deletionAllowance (V := Fin n) (E := Fin m)
        (γ : ℝ) Δ (width L) / (16 * (w : ℝ))) := by
    have h := SourceRationalScheduleScratch.publicQ_meets_real
      (V := Fin n) (E := Fin m) L γ Δ hγ hΔ hEcard
    simpa only [Q, coverWidth, SourceOverheadBounds.actualQ,
      w, restorationWidth, SourceRationalScheduleScratch.restorationWidth,
      RestorationWidthScheduleScratch.width,
      RestorationWidthScheduleScratch.depth,
      RestorationWidthScheduleScratch.ell,
      Nat.cast_mul, Nat.cast_ofNat] using h
  have hstar' : 4 * RestorationCoverParameters.tStar Q ≤ w := hstar
  have hsize' : 2 * (n + width L - 3) ≤ outerWidth L := by
    simpa only [Fintype.card_fin] using hsize
  have hcore := CanonicalDefaultSource.selected_canonical_default_finite_guarantees
    L hL edge loopless (rep L m) Δ hΔ hq hdegree (γ : ℝ) hγR hE
    hinner houter hwide href hscale hcount
    w r Q q hw hw2 hQ hquarter hsmall hfirst hlast hKcheck
    hxsmall hstar' hsmallwx hmargin hbridge hsize' k
  exact hcore

/-- The public check obtained at the actual graph-size exponent once the
source size is above the explicit threshold. -/
def checksAtSize {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n) :
    CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ := by
  have hsize' : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤
      Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hsize
  have h := CompletePublicScheduleScratch.all_large_checks_at_graph
    (V := Fin n) (E := Fin m) edge Δ γ hγ hΔ hincident hdegree hsize'
  simpa only [Fintype.card_fin] using h

/-- The actual constructor at the graph-size exponent. The only bound
needed for its public arithmetic choices is the explicit source-size cutoff;
it does not consult a promise, colouring, optimum, or probability certificate. -/
def outputAtSize {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (k : ℕ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
      (outerWidth (Nat.clog 2 n))
      (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ)
      (LookupSeed.width (Nat.clog 2 n)) k
      (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)) :=
  output (Nat.clog 2 n) Δ γ edge
    (checksAtSize Δ γ edge hγ hΔ hincident hdegree hsize)
    (NeZero.pos n) k bits

/-- Finite canonical-source guarantees beyond the explicit source-size
threshold. This specializes `checked_finite_guarantees` at the actual dyadic
source exponent; all four conclusions are those of `Guarantees` for the
single `outputAtSize` constructor. -/
theorem large_finite_guarantees {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < m)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (k : ℕ) :
    Guarantees (Nat.clog 2 n) Δ γ edge
      (checksAtSize Δ γ edge hγ hΔ hincident hdegree hsize) k :=
  checked_finite_guarantees (Nat.clog 2 n) Δ γ edge
    loopless hdegree hγ hΔ hE
    (checksAtSize Δ γ edge hγ hΔ hincident hdegree hsize) k

/-- The four claims written literally for `outputAtSize`, rather than
through the checked-constructor abbreviation `Guarantees`. -/
def LargeGuarantees {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (k : ℕ) : Prop :=
  let L := Nat.clog 2 n
  let r := restorationDepth L
  let q := coverDepth n m L Δ γ
  let w := restorationWidth L
  let Q := coverWidth n m L Δ γ
  let o := outputAtSize Δ γ edge hγ hΔ hincident hdegree hsize k
  (∀ bits, D (o bits).matrix ≤ sourceCost L r q k) ∧
  (∀ colour : Fin n → Fin 3,
    (∀ e, colour (edge e false) ≠ colour (edge e true)) →
    ∀ bits, D (o bits).matrix ≤ sourceBudget L r q k) ∧
  ((∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
    ((Finset.univ.filter (fun e => colour (edge e false) =
      colour (edge e true))).card : ℝ)) →
    1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
      (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
        (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
        (sourceRows L r q k) (sourceCols L r q k)).prob
        (fun bits => D (o bits).matrix = sourceCost L r q k) ∧
    1 - (1 / 2 : ℝ) ^ 11 ≤
      (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
        (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
        (sourceRows L r q k) (sourceCols L r q k)).prob
        (fun bits => D (o bits).matrix = sourceCost L r q k)) ∧
  (∀ bits, (o bits).bits.length =
    sourceRows L r q k * sourceCols L r q k)

theorem large_output_finite_guarantees {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < m)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (k : ℕ) :
    LargeGuarantees Δ γ edge hγ hΔ hincident hdegree hsize k := by
  exact large_finite_guarantees Δ γ edge loopless hdegree hincident
    hγ hΔ hE hsize k

end Paper2.ParameterizedCanonicalSource


