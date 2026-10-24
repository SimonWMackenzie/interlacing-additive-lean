import Paper2.RationalCoverSchedule
import Paper2.SourceSmallnessSchedule
import Paper2.SourceCoordinateSchedule
import Paper2.ParameterCutoff

/-!
Decidable arithmetic form of every frozen v12 Appendix C admissibility
comparison. The data are only public source carrier sizes and rational
source constants. No real-number comparison or protocol/colouring witness
occurs in the definition.
-/

namespace Paper2.CompletePublicScheduleScratch

open SourceProfileParameters

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

def rhoQ (L : ℕ) : ℚ := (1 / 2 : ℚ) ^ L
def xQ (L : ℕ) : ℚ := (1 / 2 : ℚ) ^ (10 * L)
def gQ : ℚ := 127 / 128
def muQ : ℚ := 1 / 256

/-- Literal comparisons of `eq:admissibility`, with `L≥16` and the seed
depth appended. `q₁=s-2`, `q₂=outerWidth L`, `w=2^(ell L)^2`,
`Q=publicQ L gamma Delta`, `eta` and `zeta` are the actual source values.
The three parts of the displayed `max` are listed separately. -/
def Checks (L Δ : ℕ) (γ : ℚ) : Prop :=
  let s := width L
  let q₂ := outerWidth L
  let w := RestorationWidthScheduleScratch.width L
  let Q := SourceOverheadBounds.actualQ (V := V) (E := E) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ
  SourceRepetitionScratch.coordinateAdmissible L E ∧
  2 * (Fintype.card V + s - 3) ≤ q₂ ∧
  (4 : ℚ) * s ^ 2 * rhoQ L ≤ 1 ∧
  (s : ℚ) * rhoQ L ≤ 1 / 1000 ∧
  (q₂ : ℚ) * xQ L ≤ 1 / 10000 ∧
  (s : ℚ) * xQ L ≤ 1 / 10000 ∧
  (w : ℚ) * xQ L ≤ 1 / 10000 ∧
  (10 * L : ℚ) ≤ (q₂ : ℚ) / 4096 ∧
  ((8 * s * (s - 2) : ℕ) : ℚ) ≤
    SourceRationalScheduleScratch.witnessDensity γ * q₂ / 16 ∧
  (2 : ℚ) * q₂ * xQ L ≤ 1 / 8 ∧
  (2 : ℚ) * s * xQ L ≤ 1 / 1000 ∧
  4 * RestorationCoverParameters.tStar Q ≤ w ∧
  (2 : ℚ) * w * xQ L + η / (16 * gQ) < 1 ∧
  (2 : ℚ) * w ^ 2 * xQ L ≤ η / (16 * gQ) ∧
  (w : ℚ) ^ 2 * q₂ * xQ L ≤ 1 ∧
  (4 : ℚ) * muQ * w * q₂ * xQ L ≤ η / 32 ∧
  (4 : ℚ) * muQ * w / q₂ ≤ η / 32 ∧
  RationalCoverSchedule.quarterCheck w Q η ∧
  RationalCoverSchedule.kCheck L (RestorationWidthScheduleScratch.depth L)
    w Q η ∧
  SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ ≤ 7 * L ∧
  16 ≤ L ∧
  LookupSeed.exponent L + 1 ≤ L

instance (L Δ : ℕ) (γ : ℚ) : Decidable (Checks (V := V) (E := E) L Δ γ) := by
  unfold Checks rhoQ xQ gQ muQ
  dsimp only
  letI : Decidable (SourceRepetitionScratch.coordinateAdmissible L E) := by
    unfold SourceRepetitionScratch.coordinateAdmissible
    infer_instance
  infer_instance

theorem rhoQ_cast (L : ℕ) : (rhoQ L : ℝ) = SourceProfileParameters.rho L := by
  simp [rhoQ, SourceProfileParameters.rho]

theorem xQ_cast (L : ℕ) : (xQ L : ℝ) = SourceProfileParameters.x L := by
  simp [xQ, SourceProfileParameters.x]


end Paper2.CompletePublicScheduleScratch

