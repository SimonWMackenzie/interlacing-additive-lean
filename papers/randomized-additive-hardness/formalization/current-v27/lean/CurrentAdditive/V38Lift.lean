import CurrentAdditive.V37Lift

/-!
# Literal selected v38 alternating table: zero outside a selected edge

Source: `papers/randomized-additive-hardness/versions/v38/source/sections/alternation.tex`,
`def:alternating-table` and `yao:lift`. The old Paper2 constructor has an
extra array coordinate for nonincidences. Here that coordinate is fixed to
zero, while the original pattern law is requested only on the genuine
`Fin H × Fin K` array positions of v38.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Paper2.YaoLowerBound
open Workspace.Types.Protocol

/-- Reindex the v38 array into the older incidence-table representation.
The absent-vertex coordinate is a fixed zero and is never sampled. -/
noncomputable def v38WithZero {H K n : ℕ}
    (W : Fin n → Fin H × Fin K → Bool) :
    Fin n → Fin H × Fin (K + 1) → Bool :=
  fun ℓ p =>
    if h : ∃ i : Fin K, i.succ = p.2 then
      W ℓ (p.1, Classical.choose h)
    else false

@[simp] theorem v38WithZero_succ {H K n : ℕ}
    (W : Fin n → Fin H × Fin K → Bool)
    (ℓ : Fin n) (a : Fin H) (i : Fin K) :
    v38WithZero W ℓ (a, i.succ) = W ℓ (a, i) := by
  classical
  have h : ∃ j : Fin K, j.succ = i.succ := ⟨i, rfl⟩
  simp only [v38WithZero, dif_pos h]
  exact congrArg (fun j : Fin K => W ℓ (a, j))
    (Fin.succ_inj.mp (Classical.choose_spec h))

@[simp] theorem v38WithZero_zero {H K n : ℕ}
    (W : Fin n → Fin H × Fin K → Bool)
    (ℓ : Fin n) (a : Fin H) :
    v38WithZero W ℓ (a, 0) = false := by
  classical
  have h : ¬ ∃ i : Fin K, i.succ = (0 : Fin (K + 1)) := by
    rintro ⟨i, hi⟩
    exact Fin.succ_ne_zero i hi
  simp [v38WithZero]

/-- The literal v38 piecewise table. It has exactly `H × K` array positions;
off-edge and unused-edge entries are zero. -/
noncomputable def matrixV38 {V : Type*} {H K q labels n : ℕ}
    (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin labels → Fin q → Fin H)
    (W : Fin n → Fin H × Fin K → Bool) :
    (V × Fin labels) → (Fin q × Fin H × Fin n) → Bool :=
  matrix edges C (v38WithZero W)

theorem matrixV38_real_edge {V : Type*} {H K q labels n : ℕ}
    (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin labels → Fin q → Fin H)
    (W : Fin n → Fin H × Fin K → Bool)
    (α : Fin H) (e : Fin K ↪ V) (he : edges α = some e)
    (i : Fin K) (z : Fin labels) (g : Fin q) (ℓ : Fin n) :
    matrixV38 edges C W (e i, z) (g, α, ℓ) = W ℓ (C z g, i) := by
  simp [matrixV38, matrix_real_edge edges C (v38WithZero W) α e he]

theorem matrixV38_unused {V : Type*} {H K q labels n : ℕ}
    (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin labels → Fin q → Fin H)
    (W : Fin n → Fin H × Fin K → Bool)
    (α : Fin H) (he : edges α = none)
    (v : V) (z : Fin labels) (g : Fin q) (ℓ : Fin n) :
    matrixV38 edges C W (v, z) (g, α, ℓ) = false := by
  simp [matrixV38, matrix, position_unused edges α he]

private theorem v38_no_implies_old
    {V E : Type*} (t : ℕ)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c := by
  intro colour
  have hle : 2 ^ (2 ^ t - 1) ≤ 2 ^ (2 ^ t) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  let f : Fin (2 ^ (2 ^ t - 1)) ↪ Fin (2 ^ (2 ^ t)) := Fin.castLEEmb hle
  obtain ⟨e, c, hc⟩ := hno (fun v => f (colour v))
  let i0 : Fin (2 ^ t * 2 ^ t) := ⟨0, by positivity⟩
  refine ⟨e, colour (edges e i0), ?_⟩
  intro i
  exact f.injective ((hc i).trans (hc i0).symm)

/-- A source NO instance for the literal v38 table yields the v38 lookup
obstruction on the genuine `H×K` position set. This reuses the checked
dominant-class and projection calculations, but derives a real-position
restriction directly, never assuming a pattern law at the zero sentinel. -/
theorem lower_bound_matrixV38
    {V E : Type*} [Fintype V] {b t labels samples : ℕ}
    (ht : 4 ≤ t) (hlabels : 0 < labels)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin labels → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) labels C)
    (W : Fin samples → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) → Bool)
    (μ : Paper2.FiniteLaw (Fin samples))
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3)))) :
    (2 * b + 4 * t + 2) + 2 * t - 8 ≤
      Dalt .alice (matrixV38 (placeEdges edges index) C W) := by
  classical
  obtain ⟨P, hcost, hP⟩ := exists_optimal .alice
    (matrixV38 (placeEdges edges index) C W)
  by_contra h
  have hp : P.cost ≤ 2 * (b + 3 * t - 3) - 1 := by omega
  obtain ⟨e, σ, _, hσ, hsize⟩ :=
    LowerBound.exists_monochromatic_dominantClasses t P.toProtocol edges
      (v38_no_implies_old t edges hno)
  let Z : Fin (2 ^ t * 2 ^ t) → Finset (Fin labels) :=
    fun i => LowerBound.dominantClass t P.toProtocol (edges e i)
  have hproj (i : Fin (2 ^ t * 2 ^ t)) :
      (3 : ℝ) / (4 * (2 : ℝ) ^ (2 ^ t - 1)) ≤
        ∏ g, ((Restriction.addresses C g Z i).card : ℝ) / (2 : ℝ) ^ b := by
    simpa only [Restriction.addresses, Nat.cast_pow, Nat.cast_ofNat] using
      retained_projection_product (2 ^ (2 ^ t - 1)) (pow_pos (by decide) _)
        hlabels C hC (Z i) (hsize i)
  obtain ⟨g, hg⟩ := exists_large_projection t b ht
    (fun i g => (Restriction.addresses C g Z i).card) hproj
  let Q := Restriction.protocol (edges e) C g (index e) Z P
  let f : Restriction.Rows C g Z → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) :=
    fun p => (p.2.val, p.1)
  have hf : Function.Injective f := by
    intro p r he
    cases p with
    | mk i a =>
      cases r with
      | mk j c =>
        have hi : i = j := congrArg Prod.snd he
        have ha : a.val = c.val := congrArg Prod.fst he
        cases hi
        cases Subtype.ext ha
        rfl
  have hrow : 2 ^ ((b + 3 * t - 3) - t + 1) ≤
      (Finset.univ : Finset (Restriction.Rows C g Z)).card := by
    rw [Finset.card_univ, Restriction.row_card]
    exact (v37_payload_minimum b t ht).trans hg
  have hpatternRows : HasPatternBound μ (fun ℓ p => W ℓ (f p))
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3))) :=
    HasPatternBound.comp_injective μ W _ hpattern f hf
  have hQcost : Q.toProtocol.cost ≤ 2 * (b + 3 * t - 3) - 1 := by
    change (Restriction.protocol (edges e) C g (index e) Z P).cost ≤ _
    simpa only [Restriction.protocol_cost] using hp
  have hQstrategy : ∀ p,
      earlyStrategy t Q.toProtocol p = σ :=
    Restriction.protocol_earlyStrategy t (edges e) C g (index e) Z P σ hσ
  have hQlookup : ∀ p ℓ, Q.toProtocol.eval p ℓ = W ℓ (f p) := by
    intro p ℓ
    have hcompute := Restriction.protocol_computes
      (placeEdges edges index) C (v38WithZero W)
      (index e) (edges e) (placeEdges_real edges index e) g Z P
      (by simpa only [matrixV38] using hP)
    exact (hcompute p ℓ).trans (by
      simp [f, Restriction.payloadMap])
  exact no_short_lookup_v37 μ (fun ℓ p => W ℓ (f p))
    (b + 3 * t - 3) t (by omega) (by omega)
    (v37_log_guard b t ht) Finset.univ hrow _ (le_refl _)
    hpatternRows Q.toProtocol hQcost Q.alternates σ
    (by intro p _; exact hQstrategy p)
    (by intro p _ ℓ; exact hQlookup p ℓ)

/-- The inherited balanced-colouring protocol computes the very same v38
piecewise table; its outside slot is encoded by the zero sentinel. -/
theorem upper_bound_matrixV38
    {V E : Type*} [Fintype V] {b t labels samples : ℕ}
    (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (C : Fin labels → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (W : Fin samples → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) → Bool)
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤
      colourFiberCard (fun i => colour (edges e i)) c) :
    Dalt .alice (matrixV38 (placeEdges edges index) C W) ≤
      2 * b + 4 * t + 2 := by
  exact placed_balanced_budget t b (by omega) edges index colour hbalanced
    C (v38WithZero W)

/-- Both v38 promises use one explicitly named `H×K` array, one selector,
and one piecewise table. The source colouring only enters the corresponding
implication, never the table constructor. -/
theorem matrixV38_yes_no
    {V E : Type*} [Fintype V] {b t labels samples : ℕ}
    (ht : 4 ≤ t) (hlabels : 0 < labels)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (C : Fin labels → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) labels C)
    (W : Fin samples → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) → Bool)
    (μ : Paper2.FiniteLaw (Fin samples))
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3)))) :
    (∀ colour : V → Fin (2 ^ t),
      (∀ e c, 2 ^ t - 1 ≤
        colourFiberCard (fun i => colour (edges e i)) c) →
      Dalt .alice (matrixV38 (placeEdges edges index) C W) ≤
        2 * b + 4 * t + 2) ∧
    ((∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c) →
      (2 * b + 4 * t + 2) + 2 * t - 8 ≤
        Dalt .alice (matrixV38 (placeEdges edges index) C W)) := by
  constructor
  · intro colour hbalanced
    exact upper_bound_matrixV38 ht edges index C W colour hbalanced
  · intro hno
    exact lower_bound_matrixV38 ht hlabels edges index hno C hC W μ hpattern

/-- The selected source parameter `t=ceil(k/2)+4` gives the requested
fixed gap for the literal v38 table. -/
theorem matrixV38_fixed_gap
    {V E : Type*} [Fintype V] {b labels samples : ℕ}
    (k : ℕ) (hlabels : 0 < labels)
    (edges : E → Fin (2 ^ (v37GapParameter k) *
      2 ^ (v37GapParameter k)) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (C : Fin labels → Fin (2 ^ (v37GapParameter k - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (v37GapParameter k - 1)) (2 ^ b)
      (2 ^ (2 ^ (v37GapParameter k) - 1)) labels C)
    (W : Fin samples → Fin (2 ^ b) ×
      Fin (2 ^ (v37GapParameter k) * 2 ^ (v37GapParameter k)) → Bool)
    (μ : Paper2.FiniteLaw (Fin samples))
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * v37GapParameter k - 3)))) :
    (∀ colour : V → Fin (2 ^ (v37GapParameter k)),
      (∀ e c, 2 ^ (v37GapParameter k) - 1 ≤
        colourFiberCard (fun i => colour (edges e i)) c) →
      Dalt .alice (matrixV38 (placeEdges edges index) C W) ≤
        2 * b + 4 * v37GapParameter k + 2) ∧
    ((∀ colour : V → Fin (2 ^ (2 ^ (v37GapParameter k))),
      ∃ e c, ∀ i, colour (edges e i) = c) →
      (2 * b + 4 * v37GapParameter k + 2) + k ≤
        Dalt .alice (matrixV38 (placeEdges edges index) C W)) := by
  obtain ⟨hyes, hno⟩ := matrixV38_yes_no
    (v37GapParameter_ge_four k) hlabels edges index C hC W μ hpattern
  refine ⟨hyes, ?_⟩
  intro hn
  have hb := hno hn
  have hgap := v37GapParameter_gap k
  have hfour := v37GapParameter_ge_four k
  omega

#print axioms CurrentAdditive.SmallBias.lower_bound_matrixV38
#print axioms CurrentAdditive.SmallBias.matrixV38_yes_no
#print axioms CurrentAdditive.SmallBias.matrixV38_fixed_gap

end CurrentAdditive.SmallBias
