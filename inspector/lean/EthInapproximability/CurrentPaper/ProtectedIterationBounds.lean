import EthInapproximability.CurrentPaper.ProtectedIterationDense
import EthInapproximability.CurrentPaper.ProtectedUpper

/-!
# Exact protected costs for the literal iteration

Source: frozen v8 `03-parameterized-construction.tex`,
`eq:paper-B-yes`, `eq:paper-B-no-exact`; `A-stage4-details.tex`,
`thm:paper-protected-stage4`. No protected-matrix cost is a premise.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedIterationBounds

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Parameters Construction
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem yes_upper (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hyes : G.SourceYES) :
    D (Iteration.protectedMatrix G c b y n M) ≤
      D M.entry + Iteration.baseOverhead G c b y n M := by
  let i := Iteration.parameters G c b y n M
  have hs : 4 ≤ bins i := Iteration.bins_ge_four G c b y n M
  have ha : 1 ≤ firstExponent i := by
    have := (ParameterGates.hard_seed_exponent_domains i).2.2.1
    omega
  have hL : 0 < Iteration.labels G c b y n M := PrimeSampler.size_pos _ _ _
  have hv : 0 < GraphVectors.vertexCount V (bins i) := by
    unfold GraphVectors.vertexCount
    exact Nat.mul_pos (by omega) G.card_vertex_pos
  have hb : 0 < GraphVectors.auxiliaryCount (bins i) := by
    unfold GraphVectors.auxiliaryCount
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨σ, hσ, _⟩ := GraphVectors.indexed_legal_of_sourceYES G hs hnoiso hyes
  have hu := ProtectedUpper.protected_yes_upper M.entry
    (a := firstExponent i) (b := binExponent i) (r := secondExponent i)
    ha hL hv hb (Iteration.secondFamily G c b y n M)
    (GraphVectors.itemOrder G (bins i)) (GraphVectors.vectors G (bins i))
    (GraphVectors.supportCap G (show 3 ≤ bins i by omega)) σ hσ
  simpa only [Iteration.baseOverhead, Iteration.a, Iteration.stepParameters, i,
    Nat.add_assoc] using hu

theorem any_upper (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix) :
    D (Iteration.protectedMatrix G c b y n M) ≤
      D M.entry + Iteration.baseOverhead G c b y n M + 1 := by
  let i := Iteration.parameters G c b y n M
  have hs : 4 ≤ bins i := Iteration.bins_ge_four G c b y n M
  have ha : 1 ≤ firstExponent i := by
    have := (ParameterGates.hard_seed_exponent_domains i).2.2.1
    omega
  have hL : 0 < Iteration.labels G c b y n M := PrimeSampler.size_pos _ _ _
  have hv : 0 < GraphVectors.vertexCount V (bins i) := by
    unfold GraphVectors.vertexCount
    exact Nat.mul_pos (by omega) G.card_vertex_pos
  have hb : 0 < GraphVectors.auxiliaryCount (bins i) := by
    unfold GraphVectors.auxiliaryCount
    exact Nat.mul_pos (by omega) (by omega)
  have hwidth : qOne (firstExponent i) + (2 ^ binExponent i + 1) ≤
      2 ^ (firstExponent i + 1) := by
    have hbins := bins_le_firstPower i
    have hqone := qOne_add_two (firstExponent i) ha
    change 2 ^ binExponent i ≤ 2 ^ firstExponent i at hbins
    rw [pow_succ]
    omega
  have hu := ProtectedUpper.protected_any_upper M.entry
    (a := firstExponent i) (b := binExponent i) (r := secondExponent i)
    hwidth hL hv hb
    (Iteration.secondFamily G c b y n M) (GraphVectors.itemOrder G (bins i))
    (GraphVectors.vectors G (bins i)) (GraphVectors.supportCap G (show 3 ≤ bins i by omega))
  simpa only [Iteration.baseOverhead, Iteration.a, Iteration.stepParameters, i,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu

theorem no_exact (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (hc : 0 < c) (ha : Accepted (Iteration.parameters G c b y n M))
    (hf : IsRobustAt M.entry b) (hcost : D M.entry = y + n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) :
    D (Iteration.protectedMatrix G c b y n M) =
      y + n + Iteration.baseOverhead G c b y n M + 1 := by
  classical
  apply le_antisymm
  · simpa only [hcost] using any_upper G c b y n M
  · have ht := ProtectedIterationDense.tolerance_bounds (Iteration.parameters G c b y n M) hc
    have hl := ProtectedIterationDense.subgame_lower G c b y n M hc ha hf hcost
      hΔ hγ hγone hcommon hno hsource Finset.univ Finset.univ
      (by rw [Finset.card_univ]; nlinarith [ht.1])
      (by rw [Finset.card_univ]; nlinarith [ht.2.2.1])
    exact hl.trans (D_mapNodes_le _ Subtype.val Subtype.val)

end EthInapproximability.CurrentPaper.ProtectedIterationBounds
