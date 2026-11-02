import EthInapproximability.CurrentPaper.ExactLowerBound
import EthInapproximability.CurrentPaper.ActualPrefix

/-!
# Actual coordinate branches of the exact construction

Source: v8 `G-exact-control.tex`, Bob's coordinate choice and the local
indexing problem. The tests here are the explicit lower-bound hypotheses
of the paper's generic first-message lemma, not assumed sender-control
conclusions. `ExactCoordinateSeparation` constructs these tests from
balancedness, the one-copy indexing bounds, and stopping.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ExactSourceControl

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open NPCC ExactConstruction ProtocolSeparation

/-- Coordinate separation on the actual unpruned suffix preserves every
row, including vector rows not used to prove the separation. The retained
labels describe actual joint diagonal columns, not separate projections. -/
theorem actual_coordinate_separation {a r N₁ N₂ n τ : ℕ} {h : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (hh : 0 ≤ h) (hτ : 1 ≤ τ) (hgap : 2 ^ r * τ < N₁)
    (hBob : ∀ j, j < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j)) (rowThreshold N₁ j) (h / 2) (a + 1 + (r - j)))
    (hAlice : ∀ j, j + 1 < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j - 1) + 1) (rowThreshold N₁ (j + 1)) h (a + 1 + (r - j)))
    (hpair : BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      2 τ h (a + 1 + 1))
    (p : Fin 4) (S : Finset (Fin N₂)) (hS : S.Nonempty)
    (hSden : h * (N₂ : ℝ) ≤ (S.card : ℝ))
    (P : Protocol (Rows N₂ n) (Columns (2 ^ r) N₁) Bool)
    (hcost : P.cost ≤ a + 1 + r)
    (hcomp : ∀ z ∈ S, ∀ α ℓ,
      P.eval (.inl (p, z)) (diagonal C₁ α ℓ) = secondMatrix ha C₁ C₂ (α, ℓ) z) :
    ActualPrefix.AllBob r P ∧
      ∀ α : Fin (2 ^ r), ∃ (code : Fin (2 ^ r)) (J : Finset (Fin N₁)),
        N₁ - (2 ^ r - 1) * τ ≤ J.card ∧
        ∀ ℓ ∈ J, Protocol.prefixCodeRaw r (Protocol.swap P) (diagonal C₁ α ℓ) = code := by
  classical
  let φ : Fin (2 ^ r) × Fin N₁ → Columns (2 ^ r) N₁ := fun x => diagonal C₁ x.1 x.2
  let ψ : Fin N₂ → Rows N₂ n := fun z => .inl (p, z)
  let P' := Protocol.pullback φ ψ (Protocol.swap P)
  have hcost' : P'.cost ≤ a + 1 + r := by
    simpa [P'] using hcost
  have hcomp' : ∀ x ∈ (Finset.univ : Finset (Fin (2 ^ r) × Fin N₁)),
      ∀ z ∈ S, P'.eval x z = secondMatrix ha C₁ C₂ x z := by
    intro x _ z hz
    simpa only [P', Protocol.pullback_eval, Protocol.eval_swap, φ, ψ] using hcomp z hz x.1 x.2
  have hrows : IsEquipartitionedGE (Finset.univ : Finset (Fin (2 ^ r) × Fin N₁))
      Finset.univ N₁ := by
    intro α _
    change N₁ ≤ ((Finset.univ : Finset (Fin (2 ^ r) × Fin N₁)).filter
      (fun x => x.1 = α)).card
    have heq : ((Finset.univ : Finset (Fin (2 ^ r) × Fin N₁)).filter
        (fun x => x.1 = α)) = ({α} : Finset (Fin (2 ^ r))) ×ˢ Finset.univ := by
      ext ⟨β, ℓ⟩
      simp [eq_comm]
    simp [heq]
  obtain ⟨hprefix, hNW, hcodes⟩ := twoTestRigidity r (a + 1) N₁ τ
    (secondMatrix ha C₁ C₂) Finset.univ h (by omega) hh
    hBob hAlice hpair hτ hgap Finset.univ S P' hS (Finset.subset_univ _)
    (by simpa using hSden) hrows hcost' hcomp'
  have hactual : ActualPrefix.AllBob r P :=
    ActualPrefix.allAlice_of_pullback_codes φ ψ Finset.univ S r (Protocol.swap P)
      hprefix hS hcodes
  refine ⟨hactual, ?_⟩
  intro α
  obtain ⟨code, hα⟩ := ExactLowerBound.dominantIndex_surjective (by positivity : 0 < 2 ^ r)
    (Protocol.prefixCodeRaw r P') hNW hgap α
  let J : Finset (Fin N₁) := Finset.univ.filter
    (fun ℓ => Protocol.prefixCodeRaw r P' (α, ℓ) = code)
  have hJcard : ((Finset.univ : Finset (Fin (2 ^ r) × Fin N₁)).filter
      (fun x => Protocol.prefixCodeRaw r P' x = code ∧ x.1 = α)).card = J.card := by
    apply Finset.card_bij (fun x _ => x.2)
    · intro x hx
      obtain ⟨_, hxcode, hxα⟩ := Finset.mem_filter.mp hx
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [← hxα] using hxcode
    · intro x hx y hy hxy
      exact Prod.ext ((Finset.mem_filter.mp hx).2.2.trans
        (Finset.mem_filter.mp hy).2.2.symm) hxy
    · intro ℓ hℓ
      exact ⟨(α, ℓ), by simpa [J] using hℓ, rfl⟩
  have hlarge := (Protocol.dominantIndex_spec Finset.univ Finset.univ
    (Protocol.prefixCodeRaw r P') hNW code).2.1
  rw [hα] at hlarge
  simp only [Finset.card_univ, Fintype.card_fin, hJcard] at hlarge
  refine ⟨code, J, hlarge, ?_⟩
  intro ℓ hℓ
  have hh := (Finset.mem_filter.mp hℓ).2
  simpa only [P', Protocol.prefixCodeRaw_pullback, φ] using hh

/-- A coordinate branch retains every ambient row. If it contains two active
vectors and one inactive vector, its actual unspent budget contradicts the
indexing lower bound on those same diagonal column labels. -/
theorem no_source_triple_in_bob_suffix {a r N₁ N₂ n t : ℕ} {ε : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (v : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (hC₁ : IsBalancedFamily t C₁ ε) (ht : a + 2 ≤ t)
    (R : Finset (Rows N₂ n)) (p : Fin 4) (α : Fin (2 ^ r))
    (J : Finset (Fin N₁)) (hJ : (1 + ε) * N₁ / 2 < (J.card : ℝ))
    (hprefix : ∀ u : Fin (prefixLength a), ∃ z : Fin N₂,
      Sum.inl (p, z) ∈ R ∧ duplicateLabel a ha (C₂ z α) = u)
    (P : Protocol (Rows N₂ n) (Columns (2 ^ r) N₁) Bool)
    (hall : ActualPrefix.AllBob r P) (hcost : P.cost ≤ a + 1 + r)
    (code : Fin (2 ^ r))
    (hcode : ∀ ℓ ∈ J, Protocol.prefixCodeRaw r (Protocol.swap P)
      (diagonal C₁ α ℓ) = code)
    (hcomp : ∀ x ∈ R, ∀ ℓ ∈ J,
      P.eval x (diagonal C₁ α ℓ) = matrix ha C₁ C₂ v cap x (diagonal C₁ α ℓ))
    (i j k : Fin n) (hij : i ≠ j)
    (hi : v i α = true) (hj : v j α = true) (hk : v k α = false)
    (hiR : Sum.inr i ∈ R) (hjR : Sum.inr j ∈ R) (hkR : Sum.inr k ∈ R) :
    False := by
  classical
  let C := J.image (diagonal C₁ α)
  let Q := ActualPrefix.colSubtree r P code
  have hbudget : Q.cost ≤ a + 1 := by
    have hb := hall.subtree_cost code
    change Q.cost + r ≤ P.cost at hb
    omega
  have hagrees : ∀ x ∈ R, ∀ c ∈ C,
      Q.eval x c = matrix ha C₁ C₂ v cap x c := by
    intro x hx c hc
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hc
    change (ActualPrefix.colSubtree r P code).eval x (diagonal C₁ α ℓ) = _
    rw [← hcode ℓ hℓ, hall.subtree_eval]
    exact hcomp x hx ℓ hℓ
  have hupper := restrictionCost_le_of_agrees (matrix ha C₁ C₂ v cap) R C Q hagrees
  have hlower := ExactLowerBound.local_indexing_lower_bound ha C₁ C₂ v cap
    hC₁ ht R C p α J hJ (fun ℓ hℓ => Finset.mem_image_of_mem _ hℓ)
    hprefix i j k hij hi hj hk hiR hjR hkR
  change a + 2 ≤ D (subgame (matrix ha C₁ C₂ v cap) R C) at hlower
  omega

/-- Coordinate rigidity and the local rank contradiction are connected on
the original protocol. The test hypotheses are those of the generic
separation theorem; the remaining sampler and numerical premises are
explicit, and no prescribed prefix or low-cost retained rectangle is assumed. -/
theorem no_source_triple_of_coordinate_tests
    {a r N₁ N₂ n t τ : ℕ} {h ε : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (v : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (hC₁ : IsBalancedFamily t C₁ ε) (ht : a + 2 ≤ t)
    (hh : 0 ≤ h) (hτ : 1 ≤ τ) (hgap : 2 ^ r * τ < N₁)
    (hBob : ∀ j, j < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j)) (rowThreshold N₁ j) (h / 2) (a + 1 + (r - j)))
    (hAlice : ∀ j, j + 1 < r → BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      (2 ^ (r - j - 1) + 1) (rowThreshold N₁ (j + 1)) h (a + 1 + (r - j)))
    (hpair : BlockLowerBound (secondMatrix ha C₁ C₂) Prod.fst Finset.univ
      2 τ h (a + 1 + 1))
    (hdensity : (1 + ε) * N₁ / 2 < ((N₁ - (2 ^ r - 1) * τ : ℕ) : ℝ))
    (p : Fin 4) (S : Finset (Fin N₂)) (hS : S.Nonempty)
    (hSden : h * (N₂ : ℝ) ≤ (S.card : ℝ))
    (hsurvives : ∀ α : Fin (2 ^ r), ∀ u : Fin (prefixLength a),
      ∃ z ∈ S, duplicateLabel a ha (C₂ z α) = u)
    (R : Finset (Rows N₂ n)) (hSR : ∀ z ∈ S, Sum.inl (p, z) ∈ R)
    (P : Protocol (Rows N₂ n) (Columns (2 ^ r) N₁) Bool)
    (hcost : P.cost ≤ a + 1 + r)
    (hcomp : ∀ x ∈ R, ∀ c, P.eval x c = matrix ha C₁ C₂ v cap x c)
    (α : Fin (2 ^ r)) (i j k : Fin n) (hij : i ≠ j)
    (hi : v i α = true) (hj : v j α = true) (hk : v k α = false)
    (hiR : Sum.inr i ∈ R) (hjR : Sum.inr j ∈ R) (hkR : Sum.inr k ∈ R) :
    False := by
  have htemplate : ∀ z ∈ S, ∀ β ℓ,
      P.eval (.inl (p, z)) (diagonal C₁ β ℓ) = secondMatrix ha C₁ C₂ (β, ℓ) z := by
    intro z hz β ℓ
    rw [hcomp _ (hSR z hz)]
    exact matrix_template_diagonal ha C₁ C₂ v cap p z β ℓ
  obtain ⟨hall, hbranches⟩ := actual_coordinate_separation ha C₁ C₂ hh hτ hgap
    hBob hAlice hpair p S hS hSden P hcost htemplate
  obtain ⟨code, J, hJcard, hcode⟩ := hbranches α
  have hJ : (1 + ε) * N₁ / 2 < (J.card : ℝ) :=
    hdensity.trans_le (by exact_mod_cast hJcard)
  have hprefix : ∀ u : Fin (prefixLength a), ∃ z : Fin N₂,
      Sum.inl (p, z) ∈ R ∧ duplicateLabel a ha (C₂ z α) = u := by
    intro u
    obtain ⟨z, hz, heq⟩ := hsurvives α u
    exact ⟨z, hSR z hz, heq⟩
  exact no_source_triple_in_bob_suffix ha C₁ C₂ v cap hC₁ ht R p α J hJ hprefix
    P hall hcost code hcode (fun x hx ℓ _ => hcomp x hx _)
    i j k hij hi hj hk hiR hjR hkR

end EthInapproximability.CurrentPaper.ExactSourceControl
