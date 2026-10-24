import EthInapproximability.CurrentPaper.ExactBinControl
import EthInapproximability.CurrentPaper.ExactSourceControl
import EthInapproximability.CurrentPaper.ExactSamplerSurvival

/-!
# The finite one-bit gap of the exact construction

Source: v8 `03-exact-hardness.tex`, the NO direction and exact gap, and
`G-exact-control.tex`. The matrix and both sampled families are literal
objects from `ExactConstruction`. The two one-copy bounds for `Qᵀ`, the
three coordinate restriction tests, and their scalar gates are exposed.
This module composes actual protocol prefixes and the five-copy source;
it does not assert that those remaining finite inputs, construction time,
or the NP-completeness endpoint have already been supplied.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ExactGap

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open Workspace.Types.Interlace NPCC
open ExactConstruction ExactBinControl ProtocolSeparation

/-- The template rows alone give the YES lower bound. Both one-copy inputs
are supplied at their actual real density; four-copy amplification is proved
by the current two-bound row ladder. -/
theorem matrix_lower_bound {a r N₁ N₂ n : ℕ} {h : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hh : 0 < h) (hrow : 4 * h ≤ 1)
    (h1 : a + 1 + r ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h (3 / 5)))
    (h2 : a + 1 + r - 1 ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h ((3 / 5) / 2)))
    (v : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    a + 1 + r + 2 ≤ D (matrix ha C₁ C₂ v cap) := by
  letI : Nonempty (Fin N₁) := ⟨⟨0, hN₁⟩⟩
  letI : Nonempty (Fin N₂) := ⟨⟨0, hN₂⟩⟩
  letI : Nonempty (Fin (2 ^ r)) := ⟨⟨0, by positivity⟩⟩
  let f := fun z x => secondMatrix ha C₁ C₂ x z
  have hfour := repeatedPowerOfTwo f (by omega) hh
    (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num : (3 / 5 : ℝ) ≤ 1)
    h1 h2 2 (by omega) (by norm_num; exact hrow)
  norm_num at hfour
  obtain ⟨RC, hRC⟩ := bracketGE.nonempty (X := Fin N₂)
    (Y := Fin (2 ^ r) × Fin N₁) 4 (4 * h) (9 / 25)
    hrow (by norm_num) (by simpa using hN₂)
  have hmember : Dfamily (interlaceFun f 4)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 4 (4 * h) (9 / 25)) ≤
      D (subgame (interlaceFun f 4) RC.1 RC.2) := by
    unfold Dfamily
    exact Nat.sInf_le ⟨RC, hRC, rfl⟩
  exact hfour.trans ((hmember.trans (D_subgame_le _ _ _)).trans
    (D_thirdMatrix_le_matrix ha C₁ C₂ v cap))

/-- A feasible source has exactly the YES cost on the same literal matrix. -/
theorem matrix_yes_cost {a r N₁ N₂ n : ℕ} {h : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hh : 0 < h) (hrow : 4 * h ≤ 1)
    (h1 : a + 1 + r ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h (3 / 5)))
    (h2 : a + 1 + r - 1 ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h ((3 / 5) / 2)))
    (v : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (σ : Fin n → Fin 4) (hf : Feasible v σ) :
    D (matrix ha C₁ C₂ v cap) = a + 1 + r + 2 := by
  have hlower := matrix_lower_bound ha C₁ C₂ hN₁ hN₂ hh hrow h1 h2 v cap
  have hupper := D_matrix_le_of_feasible ha C₁ C₂ v cap σ hf
  omega

/-- A source that defeats every four-bin partition defeats every protocol
at the YES budget. The partition is read from the original tree's first two
Alice queries; the subsequent Bob prefix preserves all its vector rows. -/
theorem no_short_protocol_of_badTriplet
    {a r N₁ N₂ n t₁ t₂ τ : ℕ} {h ε : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (hC₁ : IsBalancedFamily t₁ C₁ ε) (ht₁ : a + 2 ≤ t₁)
    (hC₂ : IsBalancedFamily t₂ C₂ ε) (ht₂ : 1 ≤ t₂)
    (hh : 0 < h) (hσ : 0 ≤ 1 - 8 * h)
    (h1 : a + 1 + r ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h (3 / 5)))
    (h2 : a + 1 + r - 1 ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h ((3 / 5) / 2)))
    (hbin : 4 * densityThreshold N₂ h < N₂)
    (hbinLoss : (3 : ℝ) * densityThreshold N₂ h ≤ 8 * h * N₂)
    (hsurvive : ((3 * densityThreshold N₂ h : ℕ) : ℝ) <
      (1 - ε) * (N₂ : ℝ) / (width a : ℝ))
    (hτ : 1 ≤ τ) (hgap : 2 ^ r * τ < N₁)
    (hBob : ∀ j, j < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j)) (rowThreshold N₁ j) ((1 - 8 * h) / 2) (a + 1 + (r - j)))
    (hAlice : ∀ j, j + 1 < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j - 1) + 1) (rowThreshold N₁ (j + 1)) (1 - 8 * h)
      (a + 1 + (r - j)))
    (hpair : BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      2 τ (1 - 8 * h) (a + 1 + 1))
    (hdensity : (1 + ε) * N₁ / 2 < ((N₁ - (2 ^ r - 1) * τ : ℕ) : ℝ))
    (v : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (hbad : ∀ σ : Fin n → Fin 4, ∃ (i j k : Fin n) (α : Fin (2 ^ r)),
      i ≠ j ∧ σ i = σ j ∧ σ i = σ k ∧
      v i α = true ∧ v j α = true ∧ v k α = false)
    (P : Protocol (Rows N₂ n) (Columns (2 ^ r) N₁) Bool)
    (hcost : P.cost ≤ a + 1 + r + 2)
    (hcomp : P.Computes (matrix ha C₁ C₂ v cap)) : False := by
  classical
  obtain ⟨hall, hnw⟩ := actual_bin_separation_of_oneCopy ha C₁ C₂ v cap
    (by positivity) hC₁.1 hC₂.1 (by omega) hh h1 h2 hbin P hcost hcomp
  let σ : Fin n → Fin 4 := fun i => Protocol.prefixCodeRaw 2 P (.inr i)
  obtain ⟨i, j, k, α, hij, hσij, hσik, hi, hj, hk⟩ := hbad σ
  let code := σ i
  obtain ⟨p, hScard, hSden, hSnonempty, _⟩ :=
    dominant_template_bin_density P hbin hbinLoss hnw code
  let S := templateLabels P code p
  have hsurv : ∀ β : Fin (2 ^ r), ∀ u : Fin (prefixLength a),
      ∃ z ∈ S, duplicateLabel a ha (C₂ z β) = u := by
    intro β u
    obtain ⟨z, hz, heq⟩ := ExactSamplerSurvival.second_family_survives
      C₂ hC₂ ht₂ S hScard hsurvive β (originalLabel a ha u)
    refine ⟨z, hz, ?_⟩
    rw [heq, duplicateLabel_original]
  let R : Finset (Rows N₂ n) := Finset.univ.filter
    (fun x => Protocol.prefixCodeRaw 2 P x = code)
  have hSR : ∀ z ∈ S, Sum.inl (p, z) ∈ R := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
  obtain ⟨hbudget, hagrees⟩ := actual_bin_suffix ha C₁ C₂ v cap P hall hcost hcomp code
  apply ExactSourceControl.no_source_triple_of_coordinate_tests ha C₁ C₂ v cap hC₁ ht₁
    hσ hτ hgap hBob hAlice hpair hdensity p S hSnonempty hSden hsurv R hSR
    (Protocol.rowSubtreeAtRaw 2 P code) hbudget
    (fun x hx c => hagrees x (Finset.mem_filter.mp hx).2 c) α i j k hij hi hj hk
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσij.symm⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσik.symm⟩

section GraphSource

variable {a r N₁ N₂ t₁ t₂ τ : ℕ} {h ε : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (hC₁ : IsBalancedFamily t₁ C₁ ε) (ht₁ : a + 2 ≤ t₁)
    (hC₂ : IsBalancedFamily t₂ C₂ ε) (ht₂ : 1 ≤ t₂)
    (hh : 0 < h) (hσ : 0 ≤ 1 - 8 * h)
    (h1 : a + 1 + r ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h (3 / 5)))
    (h2 : a + 1 + r - 1 ≤ Dfamily
      (interlaceFun (fun z x => secondMatrix ha C₁ C₂ x z) 1)
      (bracketGE (Fin N₂) (Fin (2 ^ r) × Fin N₁) 1 h ((3 / 5) / 2)))
    (hbin : 4 * densityThreshold N₂ h < N₂)
    (hbinLoss : (3 : ℝ) * densityThreshold N₂ h ≤ 8 * h * N₂)
    (hsurvive : ((3 * densityThreshold N₂ h : ℕ) : ℝ) <
      (1 - ε) * (N₂ : ℝ) / (width a : ℝ))
    (hτ : 1 ≤ τ) (hgap : 2 ^ r * τ < N₁)
    (hBob : ∀ j, j < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j)) (rowThreshold N₁ j) ((1 - 8 * h) / 2) (a + 1 + (r - j)))
    (hAlice : ∀ j, j + 1 < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j - 1) + 1) (rowThreshold N₁ (j + 1)) (1 - 8 * h)
      (a + 1 + (r - j)))
    (hpair : BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      2 τ (1 - 8 * h) (a + 1 + 1))
    (hdensity : (1 + ε) * N₁ / 2 < ((N₁ - (2 ^ r - 1) * τ : ℕ) : ℝ))

include hC₁ ht₁ hC₂ ht₂ hh hσ h1 h2 hbin hbinLoss hsurvive hτ hgap hBob hAlice hpair hdensity in
/-- The literal five-copy graph source has exactly the NO cost. This
includes the source contradiction, both actual sender prefixes, and the
unconditional upper bound on this same matrix. Profiles, tests and scalar
gates remain explicit rather than being packaged as a gap certificate. -/
theorem source_no_cost {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hD : 5 * d ≤ 2 ^ r) (hinj : ∀ α, Function.Injective (e α))
    (hbad : ∀ colour : Fin n → Fin 4,
      ∃ α : Fin d, colour (e α 0) = colour (e α 1)) :
    D (matrix ha C₁ C₂ (sourceVectors (2 ^ r) e) (sourceVectors_cap (2 ^ r) e)) =
      a + 1 + r + 3 := by
  let v := sourceVectors (2 ^ r) e
  let cap := sourceVectors_cap (2 ^ r) e
  have hlower : a + 1 + r + 3 ≤ D (matrix ha C₁ C₂ v cap) := by
    by_contra hn
    have hmem : D (matrix ha C₁ C₂ v cap) ∈ AchievableCosts (matrix ha C₁ C₂ v cap) :=
      Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty _)
    obtain ⟨P, hcost, hcomp⟩ := hmem
    exact no_short_protocol_of_badTriplet ha C₁ C₂ hC₁ ht₁ hC₂ ht₂ hh hσ h1 h2
      hbin hbinLoss hsurvive hτ hgap hBob hAlice hpair hdensity v cap
      (sourceVectors_badTriplet e hD hinj hbad) P (by omega) hcomp
  have hupper := D_matrix_le_unconditional ha C₁ C₂ v cap
  change D (matrix ha C₁ C₂ v cap) = a + 1 + r + 3
  omega

include hC₁ hC₂ hh hσ h1 h2 in
/-- On four-colourable inputs the identical five-copy construction has
exactly the YES cost. The source is computed from the graph; the supplied
colouring is used only to exhibit the protocol proving the upper bound. -/
theorem source_yes_cost {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (colour : Fin n → Fin 4)
    (hproper : ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) :
    D (matrix ha C₁ C₂ (sourceVectors (2 ^ r) e) (sourceVectors_cap (2 ^ r) e)) =
      a + 1 + r + 2 := by
  exact matrix_yes_cost ha C₁ C₂ hC₁.1 hC₂.1 hh (by linarith) h1 h2 _ _ _
    (sourceVectors_feasible (2 ^ r) e colour hproper)

end GraphSource

end EthInapproximability.CurrentPaper.ExactGap
