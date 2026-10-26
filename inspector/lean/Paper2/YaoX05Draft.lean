import Paper2.A4Definitions
import Paper2.YaoCloneSrc

/-! Unit 5 segment Y11 (lane a-yao-owner-1): the X05 / T33 contract record.

**DRAFT — NOT ADOPTED.**  The exact external contract for Guruswami--Lee
ECCC Theorem 1.1 (lock v12 YA:76-90, Y:71-75) is author decision AD-1; the
3-CNF language is D-A2.  This file records candidate FIELDS only.  It is not
an axiom, it is never instantiated here, and no statement below asserts that
such a record exists.  Every consequence is stated HYP-parametrically in a
record `G : GLSourceDraft t`.

Parameters fixed by YA:85-90 for `yao:source`: `Q = k = s = 2^t`, so the
edges have `Qk = 2^t*2^t` occurrences, `S = 2^(2^t-1)`, `ε = 1/(2S)`.
Fields: an all-input polynomial-time `BitMachine.Machine` from input words to
occurrence codes (the Yao-chosen DRAFT occurrence codec of `YaoCloneSrc`,
itself pending AD-1); completeness in GL's form (a `k`-colouring with at least
`Q-1` occurrences of every colour in every edge); soundness in GL's measure
form (a vertex probability measure under which every independent set has
measure `< ε`).  GL's additional clause "every such set induces a positive
fraction of the edges" is not recorded: YA:85-90 does not use it.

The derivation "no proper `S`-colouring" from the measure form (YA:86-87) is
proved locally (`draft_no_proper_colouring`), and composed with the checked
clone layer (`draft_clone_source_yes/no`). -/

namespace Paper2.YaoX05Draft

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2.YaoCloneSource
open Paper2.YaoLookup

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- `S = 2^(2^t-1)`, the forbidden colouring size (Y:77-90). -/
abbrev forbiddenColours (t : ℕ) : ℕ := 2 ^ (2 ^ t - 1)

/-- DRAFT (AD-1, D-A2): candidate fields of the external X05 contract.
NOT adopted; not an axiom; never instantiated in this lane. -/
structure GLSourceDraft (t : ℕ) where
  /-- D-A2 parameter: the language of satisfiable 3-CNF codes. -/
  L : BinaryLanguage
  /-- The fixed reduction machine (all inputs, malformed included). -/
  machine : BitMachine.Machine
  time : List Bool → ℕ
  output : List Bool → DraftOccSource t
  runs : ∀ input, machine.OutputsWithin input (draftOccEncode (output input)) (time input)
  poly : ∃ c d : ℕ, ∀ input, time input ≤ c * (input.length + 1) ^ d
  /-- GL completeness: a `k = 2^t` colouring with at least `Q-1 = 2^t-1`
  occurrences of each colour in every edge. -/
  complete : ∀ input, input ∈ L → ∃ colour : Fin (output input).1 → Fin (2 ^ t),
    ∀ i c, 2 ^ t - 1 ≤ colourFiberCard (fun j => colour ((output input).2.2 i j)) c
  /-- GL's vertex measure (soundness side). -/
  measure : ∀ input, Fin (output input).1 → ℝ
  measure_nonneg : ∀ input w, 0 ≤ measure input w
  measure_total : ∀ input, input ∉ L → ∑ w, measure input w = 1
  /-- GL soundness, measure form, `ε = 1/(2S)`: an independent set (containing
  no edge) has measure `< ε`. -/
  sound : ∀ input, input ∉ L → ∀ I : Finset (Fin (output input).1),
    (∀ i, ∃ j, (output input).2.2 i j ∉ I) →
      ∑ w ∈ I, measure input w < 1 / (2 * (forbiddenColours t : ℝ))

/-- YA:86-87, proved locally: a vertex probability measure, some colour
class has measure `≥ 1/S`. -/
theorem heavy_class {v S : ℕ} (hS : 0 < S) (μ : Fin v → ℝ) (htot : ∑ w, μ w = 1)
    (colour : Fin v → Fin S) :
    ∃ c : Fin S, 1 / (S : ℝ) ≤ ∑ w ∈ Finset.univ.filter (fun w => colour w = c), μ w := by
  have hne : (Finset.univ : Finset (Fin S)).Nonempty := ⟨⟨0, hS⟩, Finset.mem_univ _⟩
  have hsum : ∑ _c : Fin S, (1 / (S : ℝ)) ≤
      ∑ c : Fin S, ∑ w ∈ Finset.univ.filter (fun w => colour w = c), μ w := by
    rw [Finset.sum_fiberwise_of_maps_to (fun w _ => Finset.mem_univ (colour w)), htot]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
    field_simp
    exact le_refl _
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨c, hc⟩

/-- YA:86-87: the measure-form soundness gives no proper `S`-colouring. -/
theorem draft_no_proper_colouring {t : ℕ} (G : GLSourceDraft t) (input : List Bool)
    (hno : input ∉ G.L) :
    ∀ colour : Fin (G.output input).1 → Fin (forbiddenColours t),
      ∃ i c, ∀ j, colour ((G.output input).2.2 i j) = c := by
  intro colour
  have hS : 0 < forbiddenColours t := by positivity
  obtain ⟨c, hc⟩ := heavy_class hS (G.measure input) (G.measure_total input hno) colour
  by_contra hcon
  push Not at hcon
  have hind : ∀ i, ∃ j, (G.output input).2.2 i j ∉
      Finset.univ.filter (fun w => colour w = c) := by
    intro i
    obtain ⟨j, hj⟩ := hcon i c
    exact ⟨j, by simpa using hj⟩
  have hlt := G.sound input hno _ hind
  have hSpos : (0 : ℝ) < forbiddenColours t := by exact_mod_cast hS
  have : 1 / (2 * (forbiddenColours t : ℝ)) < 1 / (forbiddenColours t : ℝ) := by
    apply one_div_lt_one_div_of_lt hSpos
    linarith
  linarith

/-- HYP-parametric composition with the checked clone layer, YES side:
the clone source of a member carries a balanced `2^t`-colouring in the
banked `hbalanced` form. -/
theorem draft_clone_source_yes {t : ℕ} (G : GLSourceDraft t) (input : List Bool)
    (hyes : input ∈ G.L) :
    ∃ colour : Fin (cloneSource t (forbiddenColours t) (G.output input)).1 → Fin (2 ^ t),
      ∀ k c, 2 ^ t - 1 ≤ colourFiberCard
        (fun j => colour ((cloneSource t (forbiddenColours t) (G.output input)).2.2 k j)) c := by
  obtain ⟨colour, hbal⟩ := G.complete input hyes
  exact ⟨liftColour ⟨0, by positivity⟩ colour,
    clone_balanced ⟨0, by positivity⟩ colour (G.output input).2.2 hbal⟩

/-- HYP-parametric composition with the checked clone layer, NO side, in the
banked `hno` form of `materialize_fixed_gap_success`. -/
theorem draft_clone_source_no {t : ℕ} (G : GLSourceDraft t) (input : List Bool)
    (hno : input ∉ G.L) :
    ∀ colour : Fin (cloneSource t (forbiddenColours t) (G.output input)).1 →
        Fin (forbiddenColours t),
      ∃ k c, ∀ j, colour ((cloneSource t (forbiddenColours t) (G.output input)).2.2 k j) = c :=
  clone_no_proper_colouring (by positivity) (G.output input).2.2
    (draft_no_proper_colouring G input hno)

/-- The clone source always has a nonempty vertex set (YA:113). -/
theorem draft_clone_source_nonempty {t : ℕ} (G : GLSourceDraft t) (input : List Bool) :
    0 < (cloneSource t (forbiddenColours t) (G.output input)).1 :=
  cloneVertexCount_pos _ _ _

#print axioms heavy_class
#print axioms draft_no_proper_colouring
#print axioms draft_clone_source_yes
#print axioms draft_clone_source_no
#print axioms draft_clone_source_nonempty

end Paper2.YaoX05Draft
