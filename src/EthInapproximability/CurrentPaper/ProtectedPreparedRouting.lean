import EthInapproximability.CurrentPaper.ProtectedRoutedBound
import EthInapproximability.CurrentPaper.ProtectedLocalCopies
import EthInapproximability.CurrentPaper.SelectorRegularity
import EthInapproximability.CurrentPaper.ActualPrefix

/-!
# Literal protected-matrix realization of the residual routing bound

Source: frozen v8 `A-stage4-details.tex`,
`lem:paper-protected-preparation`, `lem:paper-protected-routed-closure`.
The selected prefix branch, family labels, ordinary coordinates, and graph
witnesses are the output of the preparation argument. Here their actual
physical representatives are composed with the proved routing theorem.
-/

noncomputable section
open scoped Classical BigOperators
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity Workspace.Types.Interlace

namespace EthInapproximability.CurrentPaper.ProtectedPreparedRouting

open Construction JointTransfer ProtectedGraphItems ProtectedDefects ProtectedLocalCopies
open ProtectedRoutedBound ActualPrefix

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- The transpose of an actual prefix subtree agrees with the original
matrix on every retained input belonging to that same physical branch. -/
theorem actual_suffix_agrees {Row Col : Type*} {k : ℕ}
    (F : Col → Row → Bool) (B : Finset Row) (A : Finset Col)
    (P : Protocol Row Col Bool) (hpref : AllAlice k P)
    (hcomp : ∀ r ∈ B, ∀ c ∈ A, P.eval r c = F c r) (p : Fin (2 ^ k)) :
    ∀ r ∈ B, Protocol.prefixCodeRaw k P r = p → ∀ c ∈ A,
      (Protocol.swap (Protocol.rowSubtreeAtRaw k P p)).eval c r = F c r := by
  intro r hr hp c hc
  rw [Protocol.eval_swap, ← hp, hpref.subtree_eval]
  exact hcomp r hr c hc

/-- Charge every bit of the original, unpruned prefix after proving the
transposed subtree bound. -/
theorem actual_prefix_cost {Row Col : Type*} {k h : ℕ}
    (P : Protocol Row Col Bool) (hpref : AllAlice k P) (p : Fin (2 ^ k))
    (hlower : h ≤ (Protocol.swap (Protocol.rowSubtreeAtRaw k P p)).cost) :
    h + k ≤ P.cost := by
  have hs := hpref.subtree_cost p
  simp only [Protocol.cost_swap] at hlower
  omega

/-- The selected preparation branch gives a lower bound on an actual
physical protocol, not an abstract marker game. Its agreement hypothesis
is restricted to retained inputs on that same branch. -/
theorem physical_prepared_lower (base : X → Y → Bool)
    (a s m R L nv nb H b w : ℕ) (hs : 0 < s) (hL : 0 < L) (hqOne : 0 < qOne a)
    (family : SecondFamily a (2 ^ R * 2 ^ m) L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin (2 ^ R * 2 ^ m) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    {x h ε xcap : ℝ}
    (inputs : OrdinaryInputs (H := H) (Function.swap (firstMatrix base a s)) family x h ε)
    (hgraph : H + 1 ≤ Dfamily (interlaceFun base (qOne a + 3))
      (bracketGE X Y (qOne a + 3) xcap (1 / 2)))
    (B : Finset (ProtectedRows s L nv nb X))
    (A : Finset (ProtectedColumns a s (2 ^ R * 2 ^ m) Y))
    (branch : ProtectedRows s L nv nb X → Fin s) (p bin : Fin s)
    (K : Finset (Fin L)) (hKdensity : h * (L : ℝ) ≤ K.card)
    (hKphysical : ∀ ℓ ∈ K, ∃ copy : TemplateLabels s L nv nb X,
      templateEmbedding s L nv nb bin (ℓ, copy) ∈ B ∧
      branch (templateEmbedding s L nv nb bin (ℓ, copy)) = p)
    (ordinary witnesses : Finset (Fin (2 ^ R * 2 ^ m))) (hsub : witnesses ⊆ ordinary)
    (hordinary : 2 ^ R * 2 ^ m ≤ ordinary.card + b)
    (hwitnesses : w ≤ witnesses.card + b) (hexcess : 4 * b < w)
    (hgood : ∀ α ∈ ordinary,
      α ∉ ParameterizedNP.DenseSourceOwners.templateBadSet ⌈(Fintype.card X : ℝ) * xcap⌉₊
        (coordinateSupport family K) ∧ α ∉ diagonalDefects a s (2 ^ R * 2 ^ m) A)
    (hWit : ∀ α ∈ witnesses, ∃ i j k : Fin (nv + nb), i ≠ j ∧
      vectors i α = true ∧ vectors j α = true ∧ vectors k α = false ∧
      ItemRepresentatives (t := ⌈(Fintype.card X : ℝ) * xcap⌉₊) order B branch p i ∧
      ItemRepresentatives (t := ⌈(Fintype.card X : ℝ) * xcap⌉₊) order B branch p j ∧
      ItemRepresentatives (t := ⌈(Fintype.card X : ℝ) * xcap⌉₊) order B branch p k)
    (hscale : (2 : ℝ) ^ (R + m + 1) * x ≤ 1 / 4)
    (P : Protocol (ProtectedColumns a s (2 ^ R * 2 ^ m) Y) (ProtectedRows s L nv nb X) Bool)
    (hcomp : ∀ r ∈ B, branch r = p → ∀ c ∈ A,
      P.eval c r = protectedMatrix base a s (2 ^ R * 2 ^ m) L nv nb hs family order vectors cap c r) :
    H + (R + m) + 1 ≤ P.cost := by
  classical
  letI : Nonempty (Fin (qOne a)) := Fin.pos_iff_nonempty.mp hqOne
  have hq : 0 < 2 ^ R * 2 ^ m := by positivity
  letI : Nonempty (DiagonalLabels a s (2 ^ R * 2 ^ m) Y) :=
    Fintype.card_pos_iff.mp (diagonal_labels_pos a s _ hq)
  obtain ⟨templateSec, htemplateSec, htemplateVal⟩ :=
    indexed_template_section base a s (2 ^ R * 2 ^ m) L nv nb hs hL family order vectors
      cap B branch p bin K hKphysical
  have hKpos : 0 < K.card := by
    have hl : (0 : ℝ) < L := by exact_mod_cast hL
    exact_mod_cast (mul_pos inputs.density_pos hl).trans_le hKdensity
  obtain ⟨ell0, hell0⟩ := Finset.card_pos.mp hKpos
  let defaultRow := templateSec ⟨ell0, hell0⟩
  let rowMap : Fin L → ProtectedRows s L nv nb X := fun ell =>
    if hmem : ell ∈ K then templateSec ⟨ell, hmem⟩ else defaultRow
  let gammaSet (α : Fin (2 ^ R * 2 ^ m)) :=
    survivingRows (diagonalCoordinateEmbedding a s (2 ^ R * 2 ^ m)) A α
  have hrep : ∀ α : Fin (2 ^ R * 2 ^ m), ∃ rep : FirstColumns a s Y →
      DiagonalLabels a s (2 ^ R * 2 ^ m) Y,
      ∀ γ ∈ gammaSet α, diagonalEmbedding a s (2 ^ R * 2 ^ m) ((α, γ), rep γ) ∈ A := by
    intro α
    exact exists_row_representatives (diagonalCoordinateEmbedding a s (2 ^ R * 2 ^ m)) A α
  choose rep hrep using hrep
  let diag (α : Fin (2 ^ R * 2 ^ m)) (γ : FirstColumns a s Y) :=
    diagonalEmbedding a s (2 ^ R * 2 ^ m) ((α, γ), rep α γ)
  let support (α : Fin (2 ^ R * 2 ^ m)) := (gammaSet α).image (diag α)
  let π (_α : Fin (2 ^ R * 2 ^ m)) (c : ProtectedColumns a s (2 ^ R * 2 ^ m) Y) :=
    ((selectorTuple c) bin).2
  have hπ : ∀ α γ, π α (diag α γ) = γ := by
    intro α γ
    simp only [π, diag, selectorTuple_diagonal]
  have hdiagInj : ∀ α, Function.Injective (diag α) := by
    intro α γ γ' hh
    exact (hπ α γ).symm.trans ((congrArg (π α) hh).trans (hπ α γ'))
  have hinj : ∀ α ∈ ordinary, Set.InjOn (π α) ↑(support α) := by
    intro α _ c hc c' hc' hh
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hc'
    have heq : γ = γ' := by simpa only [hπ] using hh
    exact congrArg (diag α) heq
  have hmass : ∀ α ∈ ordinary,
      (3 / 4 : ℝ) * Fintype.card (FirstColumns a s Y) ≤ (support α).card := by
    intro α hα
    have hg := (hgood α hα).2
    have hcount : ⌈(3 / 4 : ℝ) * Fintype.card (FirstColumns a s Y)⌉₊ ≤ (gammaSet α).card := by
      apply Nat.le_of_not_gt
      intro hlt
      exact hg ((mem_badItems ..).mpr hlt)
    have hc : (support α).card = (gammaSet α).card :=
      Finset.card_image_of_injective _ (hdiagInj α)
    rw [hc]
    exact Nat.ceil_le.mp hcount
  have graphData : ∀ α : witnesses,
      ∃ e : Fin (qOne a + 3) ↪ Fin (firstLength a s),
      ∃ E : Finset (Fin (qOne a + 3) × X),
        IsEquipartitionedGE E Finset.univ ⌈(Fintype.card X : ℝ) * xcap⌉₊ ∧
        ∃ row : E → ProtectedRows s L nv nb X,
          (∀ r, row r ∈ B ∧ branch (row r) = p) ∧
          (∀ r (γ : FirstColumns a s Y) (d : DiagonalLabels a s (2 ^ R * 2 ^ m) Y),
            protectedMatrix base a s (2 ^ R * 2 ^ m) L nv nb hs family order vectors cap
              (diagonalEmbedding a s (2 ^ R * 2 ^ m) ((α.val, γ), d)) (row r) =
              base r.val.2 (γ (e r.val.1))) := by
    intro α
    obtain ⟨i, j, k, hij, hi, hj, hk, hri, hrj, hrk⟩ := hWit α.val α.property
    obtain ⟨E, hE, row, hrow, hvalue⟩ := physical_local_copies base a s (2 ^ R * 2 ^ m)
      L nv nb ⌈(Fintype.card X : ℝ) * xcap⌉₊ hs hL family order vectors cap B branch p bin
      K hKphysical α.val (hgood α.val (hsub α.property)).1 i j k hij hi hj hk hri hrj hrk
    exact ⟨localSelectors a vectors cap α.val i j hij hi hj, E, hE, row, hrow, hvalue⟩
  choose selector graphSet hgraphSet graphSec hgraphSec hgraphVal using graphData
  let graphRows (α : Fin (2 ^ R * 2 ^ m)) : Finset (Fin (qOne a + 3) × X) :=
    if hα : α ∈ witnesses then graphSet ⟨α, hα⟩ else ∅
  let graphMap (α : Fin (2 ^ R * 2 ^ m)) (r : Fin (qOne a + 3) × X) :
      ProtectedRows s L nv nb X :=
    if hα : α ∈ witnesses then
      if hr : r ∈ graphSet ⟨α, hα⟩ then graphSec ⟨α, hα⟩ ⟨r, hr⟩ else defaultRow
    else defaultRow
  let tuple (α : Fin (2 ^ R * 2 ^ m)) (γ : FirstColumns a s Y) : Fin (qOne a + 3) → Y :=
    if hα : α ∈ witnesses then SelectorRegularity.select (selector ⟨α, hα⟩) γ
    else fun _ => Classical.ofNonempty
  refine prepared_protocol_lower (Function.swap (firstMatrix base a s)) family inputs K hKdensity
    rowMap π ordinary witnesses hsub hordinary hwitnesses hexcess base graphRows graphMap tuple
    hgraph ?_ ?_ (SelectorRegularity.select_degree_pos (Y := Y)
      (n := firstLength a s) (k := qOne a + 3)) P support hinj hmass hscale ?_ ?_
  · intro α hα
    simpa only [graphRows, dif_pos hα] using hgraphSet ⟨α, hα⟩
  · intro α hα
    simpa only [tuple, dif_pos hα] using SelectorRegularity.select_regular (Y := Y) (selector ⟨α, hα⟩)
  · intro α hα c hc ell hell
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hc
    rw [show rowMap ell = templateSec ⟨ell, hell⟩ by simp only [rowMap, dif_pos hell]]
    rw [hcomp _ (htemplateSec ⟨ell, hell⟩).1 (htemplateSec ⟨ell, hell⟩).2 _ (hrep α γ hγ)]
    simpa only [diag, hπ, Function.swap] using htemplateVal ⟨ell, hell⟩ α γ (rep α γ)
  · intro α hα c hc r hr
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hc
    have hr' : r ∈ graphSet ⟨α, hα⟩ := by simpa only [graphRows, dif_pos hα] using hr
    rw [show graphMap α r = graphSec ⟨α, hα⟩ ⟨r, hr'⟩ by simp only [graphMap, dif_pos hα, dif_pos hr']]
    rw [hcomp _ (hgraphSec ⟨α, hα⟩ ⟨r, hr'⟩).1 (hgraphSec ⟨α, hα⟩ ⟨r, hr'⟩).2 _ (hrep α γ hγ)]
    simpa only [diag, hπ, tuple, dif_pos hα, interlaceFun, SelectorRegularity.select]
      using hgraphVal ⟨α, hα⟩ ⟨r, hr'⟩ γ (rep α γ)

end EthInapproximability.CurrentPaper.ProtectedPreparedRouting
