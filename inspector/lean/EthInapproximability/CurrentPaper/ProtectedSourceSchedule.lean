import EthInapproximability.CurrentPaper.ProtectedDeletionGates

/-!
# Source-item preparation at the explicit parameter schedule

Source: frozen v8 `A-stage4-details.tex`, `lem:paper-protected-preparation`,
the definition of `L_src` and physical graph-item assignment at lines 434--457;
`F-parameter-choices.tex`, `eq:paper-tail-graph`.

The accepted depth inequality proves the actual source-row threshold gates.
The graph's promise-independent source conditions and the public source
constant prove the physical deletion budgets. The final theorem applies
these results to one retained physical set and an arbitrary branch function,
returning one assignment and fixed row representatives for every retained
graph item. No protocol-prefix or communication lower bound is asserted.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedSourceSchedule

open Construction ProtectedGraphItems
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

universe u v w

/-- The paper's source-row fraction `2^(a+1-b₀)` with its signed exponent. -/
def sourceFraction (i : Parameters.Input) : ℝ :=
  (2 : ℝ) ^ (Parameters.firstExponent i + 1) * (2 : ℝ) ^ (-(i.incomingDepth : ℝ))

theorem sourceFraction_eq_rpow (i : Parameters.Input) :
    sourceFraction i =
      (2 : ℝ) ^ ((Parameters.firstExponent i : ℝ) + 1 - i.incomingDepth) := by
  unfold sourceFraction
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

theorem sourceFraction_pos (i : Parameters.Input) : 0 < sourceFraction i := by
  unfold sourceFraction
  positivity

/-- This is a consequence of the first integer acceptance test, not an
extra numerical assumption. -/
theorem sourceFraction_le (i : Parameters.Input) (ha : Parameters.Accepted i) :
    sourceFraction i ≤ 1 / (2 * (Parameters.bins i : ℝ)) := by
  have he : (Parameters.firstExponent i : ℝ) + 2 + Parameters.binExponent i ≤
      i.incomingDepth := by exact_mod_cast ha.2.2.1
  rw [sourceFraction_eq_rpow]
  calc
    _ ≤ (2 : ℝ) ^ (-((Parameters.binExponent i : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      simp [Parameters.bins, mul_comm]

/-- The ceiling threshold counts distinct original rows, not their copies. -/
def sourceThreshold (X : Type*) [Fintype X] (i : Parameters.Input) : ℕ :=
  ⌈sourceFraction i * Fintype.card X⌉₊

/-- The accepted schedule gives a positive threshold, the strict half-row
budget and the strict one-eighth defect threshold used in source preparation. -/
theorem threshold_gates {X : Type*} [Fintype X] [Nonempty X]
    (i : Parameters.Input) (ha : Parameters.Accepted i) :
    0 < sourceThreshold X i ∧
      2 * (Parameters.bins i * (sourceThreshold X i - 1)) < Fintype.card X ∧
      ((sourceThreshold X i - 1 : ℕ) : ℝ) < (Fintype.card X : ℝ) / 8 := by
  have h := source_threshold_half (Parameters.bins_pos i) (Fintype.card_pos (α := X))
    (sourceFraction_pos i) (sourceFraction_le i ha)
  change 0 < sourceThreshold X i ∧
    2 * (Parameters.bins i * (sourceThreshold X i - 1)) < Fintype.card X at h
  have hs : 64 ≤ Parameters.bins i :=
    Nat.le_of_dvd (Parameters.bins_pos i) (Parameters.sixtyfour_dvd_bins i)
  have hsmall : 8 * (sourceThreshold X i - 1) < Fintype.card X := by
    have hm := Nat.mul_le_mul_right (sourceThreshold X i - 1)
      (show 8 ≤ 2 * Parameters.bins i by omega)
    exact lt_of_le_of_lt (by simpa only [Nat.mul_assoc] using hm) h.2
  refine ⟨h.1, h.2, ?_⟩
  have hsmallR : 8 * ((sourceThreshold X i - 1 : ℕ) : ℝ) < Fintype.card X := by
    exact_mod_cast hsmall
  linarith

section Graph

variable {V : Type u} {E : Type v} {X : Type w}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype X] [Nonempty X]

open Classical in
/-- The public source assumptions provide both strict additional-copy deletion
budgets for one retained physical set. -/
theorem graph_deletion_gates (G : EndpointGraph V E) (i : Parameters.Input)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (L : ℕ) (hL : 0 < L)
    (B : Finset (ProtectedRows (Parameters.bins i) L
      (GraphVectors.vertexCount V (Parameters.bins i))
      (GraphVectors.auxiliaryCount (Parameters.bins i)) X))
    (hB : (1 - Parameters.columnTolerance i) * Fintype.card
      (ProtectedRows (Parameters.bins i) L
        (GraphVectors.vertexCount V (Parameters.bins i))
        (GraphVectors.auxiliaryCount (Parameters.bins i)) X) ≤ B.card) :
    2 * ((Finset.univ \ B).card : ℚ) <
      ((Parameters.bins i : ℚ) / 2 * (G.deltaV γ Δ * Fintype.card V)) *
        (Fintype.card X * vertexMultiplicity (X := X) (Parameters.bins i) L
          (GraphVectors.vertexCount V (Parameters.bins i))
          (GraphVectors.auxiliaryCount (Parameters.bins i)) : ℕ) ∧
    2 * ((Finset.univ \ B).card : ℚ) <
      ((Parameters.bins i : ℚ) / 2) *
        (Fintype.card X * auxiliaryMultiplicity (X := X) (Parameters.bins i) L
          (GraphVectors.vertexCount V (Parameters.bins i))
          (GraphVectors.auxiliaryCount (Parameters.bins i)) : ℕ) := by
  exact ProtectedDeletionGates.graph_deletion_gates_parameters i Δ γ (G.deltaV γ Δ)
    hΔ hγ hγone hsource (G.deltaStar_le_deltaV hγ hΔ hcommon)
    L (Fintype.card V) hL G.card_vertex_pos B hB

open Classical in
/-- The literal schedule and physical density produce the graph-witness
assignment and its fixed retained representatives. The branch function is
arbitrary; actual prefix semantics must be supplied separately by its caller. -/
theorem physical_witness_supply_parameters (G : EndpointGraph V E)
    (i : Parameters.Input) (ha : Parameters.Accepted i)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (L : ℕ) (hL : 0 < L)
    (B : Finset (ProtectedRows (Parameters.bins i) L
      (GraphVectors.vertexCount V (Parameters.bins i))
      (GraphVectors.auxiliaryCount (Parameters.bins i)) X))
    (branch : ProtectedRows (Parameters.bins i) L
      (GraphVectors.vertexCount V (Parameters.bins i))
      (GraphVectors.auxiliaryCount (Parameters.bins i)) X → Fin (Parameters.bins i))
    (hB : (1 - Parameters.columnTolerance i) * Fintype.card
      (ProtectedRows (Parameters.bins i) L
        (GraphVectors.vertexCount V (Parameters.bins i))
        (GraphVectors.auxiliaryCount (Parameters.bins i)) X) ≤ B.card) :
    let s := Parameters.bins i
    let t := sourceThreshold X i
    let badV := badItems (vertexEmbedding s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s)) B (s * (t - 1) + 1)
    let badB := badItems (auxiliaryEmbedding s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s)) B (s * (t - 1) + 1)
    let J := retainedIndices (GraphVectors.itemOrder G s) badV badB
    ∃ φ : Fin (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) → Fin s,
      (γ / 24) * (q2 G s : ℚ) ≤
        ((Wit (GraphVectors.vectors G s) J φ).card : ℚ) ∧
      (∀ j ∉ badV, HasRowRepresentatives
        (vertexEmbedding s L (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s))
        B branch t j (φ (vertexIndex (GraphVectors.itemOrder G s) j))) ∧
      (∀ j ∉ badB, HasRowRepresentatives
        (auxiliaryEmbedding s L (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s))
        B branch t j (φ (auxiliaryIndex (GraphVectors.itemOrder G s) j))) := by
  have ht := threshold_gates (X := X) i ha
  have hdel := graph_deletion_gates G i hΔ hγ hγone hcommon hsource L hL B hB
  have hs : 4 ≤ Parameters.bins i := by
    have hh := Nat.le_of_dvd (Parameters.bins_pos i) (Parameters.sixtyfour_dvd_bins i)
    omega
  exact physical_witness_supply G hs hΔ hγ hγone (fun v => (hcommon.2 v).2) hno
    L hL ht.1 ht.2.1.le B branch hdel.1 hdel.2

end Graph

end EthInapproximability.CurrentPaper.ProtectedSourceSchedule
