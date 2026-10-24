import CurrentAdditive.QuarticSourceIterationLower
import Paper2.SourceRecursiveNoSampling

namespace Paper2.SourceRecursiveNoSampling

open SourceMatrix SourceProfileParameters SourceDeficiency SourceSurvivingCollisions
  Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

section SelectedSource

variable {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
variable (L : ℕ) (hL : 16 ≤ L)
variable (order : SourceConstruction.Items (width L) V ≃
  Fin (Fintype.card (SourceConstruction.Items (width L) V)))
variable (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
variable (rep Δ : ℕ) (hΔ : 0 < Δ)
variable (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * rep)
variable (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
variable (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
variable (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
  ((Finset.univ.filter (fun e => colour (edge e false) =
    colour (edge e true))).card : ℝ))
variable (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
variable (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
variable (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
variable (href : (width L : ℝ) * x L ≤ 1 / 10000)
variable (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
variable (hcountSource : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
  witnessDensity γ * outerWidth L / 16)
variable (w r Q q : ℕ) [NeZero w] [NeZero Q]
variable (hw : w = 2 ^ r) (hw2 : 2 ≤ w) (hQ : Q = 2 ^ q)
variable (ηq : ℚ)
variable (hηq : (ηq : ℝ) = deletionAllowance (V := V) (E := E) γ Δ (width L))
variable (hquarter : CurrentAdditive.QuarticSchedule.quarterCheck27Prop w Q ηq)
variable (hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
  deletionAllowance (V := V) (E := E) γ Δ (width L) /
    (16 * (127 / 128 : ℝ)))
variable (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
  deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
variable (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
  deletionAllowance (V := V) (E := E) γ Δ (width L) / 32)
variable (hKcheck :
  (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
    (r + 2) * width L) *
  CurrentAdditive.QuarticSchedule.E27 Q ηq ≤
  deletionAllowance (V := V) (E := E) γ Δ (width L) * w / 16)
variable (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
variable (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
variable (hsmallwx : (w : ℝ) * x L ≤ 1 / 10000)
variable (hmargin : 2 * w * x L +
  deletionAllowance (V := V) (E := E) γ Δ (width L) /
    (16 * (127 / 128 : ℝ)) < 1)
variable (hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
  (deletionAllowance (V := V) (E := E) γ Δ (width L) /
    (16 * (w : ℝ))))
variable (hsize : 2 * (Fintype.card V + width L - 3) ≤ outerWidth L)
variable (ξ : SourceIteration.FixedTails L (width L) (width L - 2)
  (outerWidth L) w Q V)

include hL loopless hΔ hdegree hγ hE gap hinner houter hwide href hscale
  hcountSource hw hw2 hQ hηq hquarter hsmall hfirst hlast hKcheck hxsmall
  hstar hsmallwx hmargin hbridge hsize

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Compression's failure event for the literal graph-source iteration and
the same rational laws used by the recursive sampler. -/
theorem selected_ideal_bad_le27 (k : ℕ) :
    (RecursiveSampling.sampleLaw (V := V)
      (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L)
      (w := w) (Q := Q) (SourceProfiles.width_ge_four L)
      (LookupSeed.rowLaw (LookupSeed.width L))
      (LookupSeed.columnLaw (LookupSeed.width L)
        (Nat.two_pow_pos (LookupSeed.exponent L)))
      k (sourceRows L r q k) (sourceCols L r q k)).toFiniteLaw.prob
      (fun z => D (sampleMatrix
        (SourceIteration.matrix (q₁ := width L - 2)
          L order edge (by have := SourceProfiles.width_ge_four L; omega)
          rep hq ξ k) z.2 z.1) < sourceCost L r q k) ≤
      (1 / 2 : ℝ) ^ 12 := by
  classical
  let Fk := SourceIteration.matrix (q₁ := width L - 2)
    L order edge (by have := SourceProfiles.width_ge_four L; omega) rep hq ξ k
  let μ₀ := LookupSeed.rowLaw (LookupSeed.width L)
  let ν₀ := LookupSeed.columnLaw (LookupSeed.width L)
    (Nat.two_pow_pos (LookupSeed.exponent L))
  let laws := RecursiveSampling.laws (V := V) (q₁ := width L - 2)
    (q₂ := outerWidth L) (s := width L) (w := w) (Q := Q)
    (SourceProfiles.width_ge_four L) μ₀ ν₀
  let H := sourceCost L r q k
  let R := sourceRank L r q k
  have hno := SourceIterationLower.selected_no_iteration27 L hL order edge
    loopless rep Δ hΔ hq hdegree γ hγ hE gap hinner houter hwide href
    hscale hcountSource w r Q q hw hw2 hQ ηq hηq hquarter hsmall hfirst hlast
    hKcheck hxsmall hstar hsmallwx hmargin hbridge ξ k
  have hbound := SourceIteration.selected_iteration_bounds L order edge
    (by have := SourceProfiles.width_ge_four L; omega) rep hq ξ
    (exponent L) (outerExponent L) r q (by
      have := SourceProfiles.width_ge_four L
      omega)
    rfl rfl hw hQ hsize k
  have hH : 1 ≤ H := by unfold H sourceCost; omega
  have hrank : (RankLeaves.realMatrix (Fk : _)).rank ≤ R := by
    calc
      _ ≤ 2 ^ (LookupSeed.exponent L + 1 +
          k * (exponent L + exponent L + outerExponent L + r + q) - 1) :=
        hbound.2.2
      _ = R := by
        change 2 ^ (LookupSeed.exponent L + 1 +
          k * (exponent L + exponent L + outerExponent L + r + q) - 1) =
          2 ^ (LookupSeed.exponent L + 1 +
            k * (exponent L + outerExponent L + exponent L + r + q) - 1)
        exact congrArg (fun n : ℕ => 2 ^ (LookupSeed.exponent L + 1 + k * n - 1))
          (by omega)
  have hrobust : ∀ U V, (1 / 2 : ℝ) ^ L ≤ (laws k).1.toFiniteLaw.prob
      (· ∈ U) → (3 / 5 : ℝ) ≤ (laws k).2.toFiniteLaw.prob (· ∈ V) →
      H ≤ Compression.restrictionD Fk U V := by
    intro U V hU hV
    have hp := hno.2 (0 : Fin 3) U V
      (by simpa only [SourceProfileParameters.rho] using hU)
      (by simpa using hV)
    change (H : ℤ) - (0 : ℤ) ≤
      (Compression.restrictionD Fk U V : ℤ) at hp
    exact_mod_cast (show (H : ℤ) ≤
      (Compression.restrictionD Fk U V : ℤ) by simpa using hp)
  have hc := Compression.two_sided_compression_failure Fk
    (laws k).1.toFiniteLaw (laws k).2.toFiniteLaw R H L hH
    (by omega) hrank hrobust
  simpa only [RecursiveSampling.sampleLaw,
    PositiveRationalLaw.toFiniteLaw_prod,
    PositiveRationalLaw.toFiniteLaw_iid] using hc

#print axioms selected_ideal_bad_le27

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The actual capped fair-bit sampler prints a table of exactly the NO
communication cost with the explicit finite success margin. This conclusion
concerns the literal row-major output, not a conditioned sampler. -/
theorem selected_materialized_no_success27
    (sampleOrder : Fin (Fintype.card V) ≃ V) (k : ℕ) :
    1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
      (RecursiveSamplingExecution.tapeLaw V (width L) (width L - 2)
        (outerWidth L) w Q (LookupSeed.width L) k
        (sourceRows L r q k) (sourceCols L r q k)).prob
        (fun t => D (RecursiveSamplingMaterialization.materialize sampleOrder
          (SourceProfiles.width_ge_four L) (LookupSeed.width L)
          (by unfold LookupSeed.width; positivity)
          (SourceConstruction.activity order edge
            (by have := SourceProfiles.width_ge_four L; omega) rep hq)
          ξ k (sourceRows L r q k) (sourceCols L r q k) t).matrix =
          sourceCost L r q k) := by
  classical
  let hs := SourceProfiles.width_ge_four L
  let p := LookupSeed.width L
  let hp : 0 < p := by dsimp [p, LookupSeed.width]; positivity
  let act := SourceConstruction.activity order edge (by omega : 3 ≤ width L)
    rep hq
  let mX := sourceRows L r q k
  let mY := sourceCols L r q k
  let H := sourceCost L r q k
  let Fk := SourceIteration.matrix (q₁ := width L - 2)
    L order edge (by omega : 3 ≤ width L) rep hq ξ k
  let idealLaw := RecursiveSampling.sampleLaw (V := V) (q₁ := width L - 2)
    (q₂ := outerWidth L) (s := width L) (w := w) (Q := Q) hs
    (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp) k mX mY
  let τ := RecursiveSamplingExecution.tapeLaw V (width L) (width L - 2)
    (outerWidth L) w Q p k mX mY
  let print (t : RecursiveSamplingExecution.Tape V (width L) (width L - 2)
      (outerWidth L) w Q p k mX mY) :=
    (RecursiveSamplingMaterialization.materialize sampleOrder hs p hp act ξ
      k mX mY t).matrix
  let ideal (z :
      (Fin mY → RecursiveEntries.Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items (width L) V) (width L) (width L - 2)
        (outerWidth L) w Q k) ×
      (Fin mX → RecursiveEntries.Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items (width L) V) (width L) (width L - 2)
        (outerWidth L) w Q k)) := sampleMatrix Fk z.2 z.1
  have hbound := SourceIteration.selected_iteration_bounds L order edge
    (by omega : 3 ≤ width L) rep hq ξ
    (exponent L) (outerExponent L) r q
    (by have := SourceProfiles.width_ge_four L; omega)
    rfl rfl hw hQ hsize k
  have hnum : LookupSeed.exponent L + 1 +
      k * (exponent L + exponent L + outerExponent L + r + q) + k ≤ H := by
    dsimp [H, sourceCost]
    have hbase : exponent L + exponent L + outerExponent L + r + q =
      exponent L + outerExponent L + exponent L + r + q := by omega
    have hmul : k * (exponent L + exponent L + outerExponent L + r + q) =
        k * (exponent L + outerExponent L + exponent L + r + q) :=
      congrArg (fun n : ℕ => k * n) hbase
    have hadd : k *
        (exponent L + outerExponent L + exponent L + r + q + 1) =
        k * (exponent L + outerExponent L + exponent L + r + q) + k := by
      simpa only [Nat.mul_one] using Nat.mul_add k
        (exponent L + outerExponent L + exponent L + r + q) 1
    omega
  have hupper : ∀ t, D (print t) ≤ H := by
    intro t
    have hm := RecursiveSamplingMaterialization.materialize_D_le sampleOrder hs
      p hp act ξ k mX mY t
    exact hm.trans (hbound.1.trans hnum)
  have hbad : idealLaw.toFiniteLaw.prob (fun z => D (ideal z) < H) ≤
      (1 / 2 : ℝ) ^ 12 := by
    exact selected_ideal_bad_le27 L hL order edge loopless rep Δ hΔ hq
      hdegree γ hγ hE gap hinner houter hwide href hscale hcountSource
      w r Q q hw hw2 hQ ηq hηq hquarter hsmall hfirst hlast hKcheck hxsmall
      hstar hsmallwx hmargin hbridge hsize ξ k
  have hcouple : |τ.prob (fun t => D (print t) < H) -
      idealLaw.toFiniteLaw.prob (fun z => D (ideal z) < H)| ≤
      (1 / 2 : ℝ) ^ 13 := by
    exact RecursiveSamplingMaterialization.materialize_matrix_event_error
      sampleOrder hs p hp act ξ k mX mY {M | D M < H}
  exact exact_cost_of_bad_event_bound τ idealLaw.toFiniteLaw print ideal
    D H ((1 / 2 : ℝ) ^ 12) ((1 / 2 : ℝ) ^ 13) hupper hbad hcouple

#print axioms selected_materialized_no_success27


end SelectedSource

end Paper2.SourceRecursiveNoSampling
