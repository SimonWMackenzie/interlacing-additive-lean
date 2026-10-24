import EthInapproximability.ParameterizedNP.DenseStageFourOpening

/-!
# Parameterized NP route: the proof body of `lem:raw-low-profile`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/08-dense-stage4.tex`, **lines 218--256** -- the
  *proof* of `lem:raw-low-profile`, paragraph by paragraph:
  * `08:219--227`: "Fix `j in {0,1,2}`, take an arbitrary member of
    `<N,1,x_N,y/2^j>`, and transpose it.  First discard all protected selector
    and diagonal columns of `A`.  Since their total mass is `tau`, the uniform
    base-column copy retains density at least `(x_N - tau)/(1 - tau)
    >= h_2^raw >= h_j^raw`."  -> `§1`.
  * `08:229--239`: "Next discard the protected nonbase row reservoirs and all
    raw source rows. ... If `g_j` of the `s` Stage-3 blocks retain at least an
    `x_j` fraction of their rows, the elementary extremal bound
    `beta_j^raw <= (g_j + (s - g_j) x_j)/s` and `eq:raw-low-gates` imply
    `g_j >= p_j`."  -> `§2`.
  * `08:241--242`: "Project the retained base columns to any `p_j` such blocks.
    Projection cannot decrease their normalized density."  -> `§3`.
  * `08:242--251`: "The inherited General Hard Seed Lemma, instantiated at
    width `I_j`, therefore leaves a member of `<M_2^T, p_j, x_j, h_j^raw>` of
    complexity at least `D_2 + log_2 I_j = C - 1 - j`."  -> `§4` (the schedule
    identity) and `§5` (the inherited call, a **named hypothesis**).
  * `08:252--256`: "This proves `j + comp<N,1,x_N,y/2^j> >= C - 1`.  Taking
    the minimum over `j = 0,1,2` gives the claimed three-rung bound."
    -> `§6`, which supplies the composed `hrung` argument to the banked
    `DenseStageFourOpening.rawLowProfile` and applies it.
* **Supporting frozen anchors, opened and read for this tranche:**
  * `sections/09-first-wrapper.tex` `def:regular-finite-map` (label line 56,
    body lines 57--67) and `lem:regular-density-transfer` (label line 70,
    statement lines 71--88, proof lines 90--104), with its two displays
    `eq:fibre-bounded-density-transfer` (label 78) and
    `eq:regular-density-transfer` (label 84), and its closing sentence "The
    product of maps regular of degrees `d_1,d_2` is regular of degree
    `d_1 d_2`".  `09:53--55` names this as the property that makes the section's
    density comparisons valid, so it is the frozen justification of the
    one-sentence projection step `08:241--242`; `§3` transcribes it in full.
  * `sections/06-parameter-schedule.tex` `eq:hard-seed-width-gates` (label
    line 268, display 264--269) -- `k_T = log_2(s/4) >= m_HS`, `16 | (s/4)`,
    `log_2 s < b_T` -- with the frozen consequence sentence lines 271--274:
    "Consequently each `I_j = s/2^j`, `j = 0,1,2`, is a legal hard-seed width
    and satisfies `I_j < 2^{b_T}`."  This is where `§2`'s side condition
    `x_j < 1` comes from and where `§4`'s `log_2 I_j = log_2 s - j` is licensed.
  * `sections/06-parameter-schedule.tex` lines 900--913 -- the raw low-rung
    margins `eq:raw-low-rung-gates` and the frozen consequence display
    "`(beta_j^raw - x_j)/(1 - x_j) >= 9/(16 * 2^j)`, which is precisely the row
    density needed for the three raw lower rungs in `sec:dense-stage4`",
    together with `I_j = s/2^j`, `p_j = 9 I_j/16` (lines 912--913).  This is
    the exact hypothesis shape of `rawLow_gate_of_margin` in `§2` and the
    schedule tier used by the non-vacuity witness of `§7`.
  * `sections/08-dense-stage4.tex` `08:149--152` (`C = D_2 + log_2 s + 1`),
    consumed through the banked `cBlock` / `dTwoBlock`, never restated.
* **Reader counterparts** (`routes/parameterized-np/reader-facing/sections/`):
  the reader's statement of this conclusion is `eq:paper-protected-low`
  (`A-stage4-details.tex`, label line 227, display line 226,
  `Lambda_N(1,1/16,3/5) >= C-1`).  That item is **already assigned** -- to
  `rawLowProfile`, in the ledger row `STAGE4-PROTECTED-OPENING-001` -- and is
  **not** reclaimed here: this module supplies that theorem's `hrung`
  argument, not its statement.  The reader's own low-row *proof* content is
  `A-stage4-details.tex` lines 283--291 ("For `eq:paper-protected-low`,
  discard the two small protected column reservoirs and the protected nonbase
  row reservoirs.  At rung `j`, block balancing leaves `9(s/2^j)/16` Stage-3
  bins.  The inherited hard-seed estimate at width `s/2^j` gives complexity
  `C-1-j`."), which is proof **prose** and is never cited as a statement.
  Inside that same paragraph, lines 288--289 ("The same argument inside the
  base-column reservoir ... gives `eq:paper-reference-profile`") point at
  `cor:exact-protected-stage4` (`08:1327`), which the Alice-closure tranche
  declined; that pointer is **cited, not claimed**, and reader line 315
  onward (the `G_0` routing) is scale-alignment territory, out of scope here.
  Two reader items *are* claimed, both previously unclaimed, opened and
  re-read for this tranche (the line ranges were re-checked against the reader
  source in the repair round and corrected from the parked round's `308--314`):
  * `A-stage4-details.tex` lines 305--311, the fibre display ("every map used
    to transfer a normalized density between a protected reservoir and its
    quotient has equal positive fibre size.  If `phi : X -> Y` has fibres of
    size `d`, then for every `S subset X`, `|phi(S)|/|Y| >= |S|/|X|`")
    -> `regular_density_transfer`.  Opened: it states exactly the regular case
    of `eq:regular-density-transfer`, and no earlier ledger row cites those
    reader lines.
  * `A-stage4-details.tex` line 312, "Products of such maps again have equal
    fibres." -> `isFibreBounded_prod`.  This is the reader's counterpart of the
    frozen product clause `09:87--88`; it is a stated fact, not proof prose,
    and it is a **different** item from the display above, so no reader item is
    claimed twice.
  Everything else here -- `density_after_exact_mass_discard`,
  `rawLow_column_transport`, `extremal_block_bound`, `rawLow_block_count`,
  `rawLow_gate_of_margin`, `rowDensity_lt_one`, `rung_schedule_identity`,
  `widthI_eq_two_pow`, `rung_value_eq_log_width`, `RungSeedWitness`,
  `Dfamily_ge_of_seed_witnesses`, `rawLowProfile_body`, `J49Feasible` with its
  three certificate lemmas, `witness_bT_checked`, the aux battery, the poles
  and the non-vacuity witness
  -- claims **no** reader item: the reader compresses all of it into the four
  prose sentences quoted above.  No reader item is assigned twice, here or in
  any earlier row.

## What this module does, and what it deliberately does not

**Does.**  It proves, in the kernel and in full generality, the four steps of
`08:218--256` that are ordinary finite mathematics:

1. the column-discard density transport (`density_after_exact_mass_discard`),
   chained with the banked gate coverage into `rawLow_column_transport`;
2. the elementary extremal bound (`extremal_block_bound`) and its composition
   with the banked ceiling gate into a **count** of Stage-3 blocks
   (`rawLow_block_count`, `rawLow_block_count_of_block_densities`);
3. the projection step, i.e. `lem:regular-density-transfer` in full --
   fibre-bounded transfer, the regular corollary, and the product clause;
4. the schedule identity `D_2 + log_2 I_j = C - 1 - j`
   (`rung_schedule_identity`) with the real/natural width tie
   `widthI_eq_two_pow`;

and then composes them with the inherited call into the `hrung` argument that
the banked `rawLowProfile` demands (`rawLowProfile_body`).

**Does not.**  The inherited **General Hard Seed Lemma at width `I_j`** has no
vendored Lean declaration at this shape, so it is carried as an **explicit
named hypothesis** -- the predicate `RungSeedWitness`, a binder of
`rawLowProfile_body` -- never silently discharged, never an axiom, never a
field of a structure.  `Admissible`, `NoCert` and `LevelStep` remain explicit
propositional binders exactly as the banked opening leaves them, and `NoCert`
is nowhere inhabited here.

**Threading disclosure (read before consuming anything here).**  `§1`--`§3`
are **standalone** transcriptions of `08:220--242`, proved in full generality
and *not* consumed by `rawLowProfile_body`, which imports the legality of the
seed call wholesale through the named binder `hseed`; threading `§1`--`§3` into
that binder's discharge -- i.e. showing that the discard/projection steps put
the restriction into the rung bracket the inherited lemma is called on -- is
owed to the seed-facade successor tranche and is **not** claimed here.

**Nothing banked is restated.**  `rawLowGates`, `rawLowGates_cover_rungs`,
`block_count_of_extremal`, `betaRaw`, `rTail`, `rowDensity`, `widthI`,
`blockTarget`, `hRawSchedule`, `xN`, `xTdepth`, `tauR`, `sigmaR`, `cBlock`,
`dTwoBlock` and `rawLowProfile` are consumed **by pin** from
`DenseStageFourOpening`; `D_subgame_mono`, `Dfamily`, `bracketGE`, `subgame`,
`LambdaGE` and `interlaceFun` are consumed by pin from the vendored layer;
`PublicRecords.D_const` is consumed by pin.

## Mechanical-rule notes (frozen `sections/02-mechanical-contract.tex`)

* **M1/M4.**  The two new non-propositional definitions are `IsFibreBounded`,
  a purely finite counting predicate on a map, and `J49Feasible`, the frozen
  integer predicate `P_k(j)` of `06:89`.  Neither mentions a matrix, a
  protocol or a promise certificate, and neither carries a complexity or
  robustness conclusion.  `RungSeedWitness` is a *statement* about a pinned family,
  written as a `def : Prop` only so the same binder can be named once and
  reused; it is a hypothesis at every use site.
* **M3.**  No bundle field restates a derived telescope.  `IsFibreBounded`
  carries the two frozen inequalities of `def:regular-finite-map` and nothing
  else; the surjectivity that `09:64--65` *derives* is proved here as
  `IsFibreBounded.surjective`, not assumed.
* **M10 (weakening only).**  Where the frozen text writes a fraction the Lean
  uses the same real division; where it writes a ceiling the Lean uses
  `Nat.ceil`, inherited from the banked gate predicate, which is the side on
  which the ceiling makes the *hypothesis* harder, never easier.

## Axiom surface

Imports `DenseStageFourOpening` and, through it, `EthInapproximability.Prelude`,
hence `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
`LegacyNPCC.Stage12` is **not** imported anywhere in this chain, so the cited
AGHP balanced-family axiom is not in the closure of any declaration here.  No
new `axiom` is introduced and no opaque certificate carries a conclusion.
-/

namespace EthInapproximability.ParameterizedNP.RawLowProfileBody

open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.PublicRecords
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.StageTwoRelaxed
open EthInapproximability.ParameterizedNP.DenseStageFourOpening

/-! ## §1  The column-discard density transport (`08:220--227`)

"First discard all protected selector and diagonal columns of `A`.  Since
their total mass is `tau`, the uniform base-column copy retains density at
least `(x_N - tau)/(1 - tau) >= h_2^raw >= h_j^raw`."

Two separate things happen in that sentence.  The *density* claim is a general
finite-counting fact about discarding a set of **exactly** known mass -- the
frozen word is "Since their total mass is `tau`", and the banked
`protected_col_masses` proves that mass exactly, so the exact form is the
honest one: with only an upper bound on the discarded mass the denominator
would move the wrong way and the statement would be false.  The *chain* down
to `h_j^raw` is the banked `rawLowGates_cover_rungs`, consumed by pin. -/

/-- **The column-discard density transport (`08:222--225`), general.**

Let `P` be a set of columns of exact normalized mass `tau < 1` inside a
nonempty finite carrier, and let `S` be a retained set of normalized density at
least `x`.  After `P` is discarded, `S` still has normalized density at least
`(x - tau)/(1 - tau)` inside the surviving carrier.

General in the carrier, in `S`, in `P`, in `x` and in `tau`; no Section-8
constant appears. -/
theorem density_after_exact_mass_discard {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S P : Finset Ω) {x τ : ℝ} (hτ1 : τ < 1)
    (hΩ : 0 < Fintype.card Ω)
    (hP : (P.card : ℝ) = τ * (Fintype.card Ω : ℝ))
    (hS : x * (Fintype.card Ω : ℝ) ≤ (S.card : ℝ)) :
    (x - τ) / (1 - τ)
      ≤ ((S \ P).card : ℝ) / ((((Finset.univ : Finset Ω) \ P).card : ℕ) : ℝ) := by
  classical
  have hn : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
  have hPsub : P ⊆ (Finset.univ : Finset Ω) := Finset.subset_univ P
  have hPle : P.card ≤ Fintype.card Ω := by
    simpa using Finset.card_le_card hPsub
  have hden : ((((Finset.univ : Finset Ω) \ P).card : ℕ) : ℝ)
      = (1 - τ) * (Fintype.card Ω : ℝ) := by
    rw [Finset.card_sdiff, Finset.inter_univ]
    simp only [Finset.card_univ]
    rw [Nat.cast_sub hPle, hP]
    ring
  have hdenpos : (0 : ℝ) < ((((Finset.univ : Finset Ω) \ P).card : ℕ) : ℝ) := by
    rw [hden]; nlinarith
  have hnum : (x - τ) * (Fintype.card Ω : ℝ) ≤ (((S \ P).card : ℕ) : ℝ) := by
    have hsub : S ⊆ (S \ P) ∪ P := by
      intro a ha
      by_cases hp : a ∈ P
      · exact Finset.mem_union_right _ hp
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hp⟩)
    have hcard : S.card ≤ (S \ P).card + P.card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hcast : (S.card : ℝ) ≤ ((S \ P).card : ℝ) + (P.card : ℝ) := by
      exact_mod_cast hcard
    rw [hP] at hcast
    nlinarith
  rw [div_le_div_iff₀ (by linarith) hdenpos, hden]
  nlinarith

/-- **Aux 1 (round trip at zero discarded mass).**  With nothing discarded the
transport is the identity: `tau = 0` returns exactly the incoming density
bound.  This is a genuine unit test -- an encoding that divided by the *whole*
carrier instead of the surviving one would still pass here, but an encoding
that lost the numerator would not. -/
theorem density_after_exact_mass_discard_at_zero {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) {x : ℝ} (hΩ : 0 < Fintype.card Ω)
    (hS : x * (Fintype.card Ω : ℝ) ≤ (S.card : ℝ)) :
    x ≤ ((S \ (∅ : Finset Ω)).card : ℝ)
        / (((((Finset.univ : Finset Ω) \ (∅ : Finset Ω)).card : ℕ)) : ℝ) := by
  have h := density_after_exact_mass_discard (Ω := Ω) S ∅
    (x := x) (τ := 0) (by norm_num) hΩ (by simp) hS
  simpa using h

/-- **The frozen first paragraph of the proof (`08:220--227`), composed.**

At every rung `j <= 2`, under the banked gate predicate and the frozen
power-of-two floor `4 <= s`, the base-column copy surviving the discard of the
protected selector and diagonal columns has normalized density at least
`h_j^raw`.  The chain is literally the frozen one:
`h_j^raw <= h_2^raw <= (x_N - tau)/(1 - tau) <=` the surviving density.

`rawLowGates_cover_rungs` is consumed **by pin**: no part of the schedule is
recomputed here. -/
theorem rawLow_column_transport {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S P : Finset Ω) (hΩ : 0 < Fintype.card Ω)
    (hP : (P.card : ℝ) = tauR * (Fintype.card Ω : ℝ))
    (hS : xN * (Fintype.card Ω : ℝ) ≤ (S.card : ℝ))
    {s bT T₀ V₀ B₀ : ℕ} (hs : 4 ≤ s) {y : ℝ}
    (hgates : rawLowGates s bT T₀ V₀ B₀ y) {j : ℕ} (hj : j ≤ 2) :
    hRawSchedule (widthI s j)
      ≤ ((S \ P).card : ℝ) / ((((Finset.univ : Finset Ω) \ P).card : ℕ) : ℝ) :=
  le_trans (rawLowGates_cover_rungs hs hgates hj)
    (density_after_exact_mass_discard S P (by norm_num [tauR]) hΩ hP hS)

/-! ## §2  The row-discard extremal bound and the block count (`08:229--239`)

"If `g_j` of the `s` Stage-3 blocks retain at least an `x_j` fraction of their
rows, the elementary extremal bound `beta_j^raw <= (g_j + (s - g_j) x_j)/s` and
`eq:raw-low-gates` imply `g_j >= p_j`."

The **extremal bound** itself is proved here in general: a mean of `s` block
densities, each at most one, is at most the mean of the extremal profile in
which the good blocks are full and the rest sit at the threshold.  The
**implication to a count** is the banked `block_count_of_extremal`, consumed by
pin. -/

/-- **The elementary extremal bound (`08:234--237`), general.**

For any `s` block densities bounded by one, the average density is at most
`(g + (s - g) x)/s`, where `g` is the number of blocks whose density reaches
the threshold `x`.  This is the step at which the schedule turns a density
statement into a **count** of blocks.

General in `s`, in the densities and in the threshold: no Section-8 constant
appears, and it holds for every real `x`. -/
theorem extremal_block_bound {s : ℕ} (d : Fin s → ℝ) (x : ℝ)
    (hd1 : ∀ i, d i ≤ 1) :
    (∑ i, d i) / (s : ℝ)
      ≤ (((Finset.univ.filter fun i => x ≤ d i).card : ℝ)
          + ((s : ℝ) - ((Finset.univ.filter fun i => x ≤ d i).card : ℝ)) * x) / (s : ℝ) := by
  classical
  by_cases hs : s = 0
  · subst hs; simp
  have hspos : (0 : ℝ) < (s : ℝ) := by
    have : 0 < s := Nat.pos_of_ne_zero hs
    exact_mod_cast this
  set G : Finset (Fin s) := Finset.univ.filter fun i => x ≤ d i with hG
  have hsplit :
      (∑ i ∈ G, d i) + (∑ i ∈ Finset.univ.filter (fun i => ¬ x ≤ d i), d i) = ∑ i, d i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hgood : (∑ i ∈ G, d i) ≤ (G.card : ℝ) := by
    have := Finset.sum_le_card_nsmul G d 1 (fun i _ => hd1 i)
    simpa using this
  have hbad : (∑ i ∈ Finset.univ.filter (fun i => ¬ x ≤ d i), d i)
      ≤ ((Finset.univ.filter fun i => ¬ x ≤ d i).card : ℝ) * x := by
    have := Finset.sum_le_card_nsmul (Finset.univ.filter fun i => ¬ x ≤ d i) d x
      (fun i hi => le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2))
    simpa [nsmul_eq_mul] using this
  have hcards : G.card + (Finset.univ.filter fun i => ¬ x ≤ d i).card = s := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s))) (p := fun i => x ≤ d i)
    simpa [hG] using this
  have hcast : ((Finset.univ.filter fun i => ¬ x ≤ d i).card : ℝ) = (s : ℝ) - (G.card : ℝ) := by
    have hc : ((G.card + (Finset.univ.filter fun i => ¬ x ≤ d i).card : ℕ) : ℝ) = (s : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcards
    push_cast at hc
    linarith
  rw [div_le_div_iff_of_pos_right hspos, ← hsplit, ← hcast]
  linarith

/-- **Aux 2 (the extremal bound is tight).**  When every block is full the two
sides agree, so the bound is not a lossy over-estimate that would make the
banked ceiling gate unusable.  A unit test on the shape of the right-hand
side: an encoding that used `(g + (s-g))/s` or `(g + s x)/s` would fail here. -/
theorem extremal_block_bound_tight {s : ℕ} (x : ℝ) (hx : x ≤ 1) :
    (∑ _i : Fin s, (1 : ℝ)) / (s : ℝ)
      = (((Finset.univ.filter fun _i : Fin s => x ≤ (1 : ℝ)).card : ℝ)
          + ((s : ℝ) - ((Finset.univ.filter fun _i : Fin s => x ≤ (1 : ℝ)).card : ℝ)) * x)
        / (s : ℝ) := by
  classical
  have hfil : (Finset.univ.filter fun _i : Fin s => x ≤ (1 : ℝ))
      = (Finset.univ : Finset (Fin s)) := by
    ext i; simp [hx]
  rw [hfil]
  simp

/-- **The frozen implication `beta_j^raw <= ... => g_j >= p_j` (`08:237--239`).**

The banked `block_count_of_extremal` at the frozen rung data of `08:167--181`:
the threshold is `x_j = I_j x_T`, the density is `beta_j^raw`, the target is
`p_j = 9 I_j/16`, and the ceiling gate is the second clause of the banked
`rawLowGates`.  Nothing is recomputed; this is the pinned instance. -/
theorem rawLow_block_count {s bT T₀ V₀ B₀ : ℕ} (hs : 0 < s) {y : ℝ}
    (hgates : rawLowGates s bT T₀ V₀ B₀ y) {j : ℕ} (hj : j ≤ 2)
    (hx1 : rowDensity s j bT < 1) {g : ℕ}
    (hextremal : betaRaw (rTail y j) T₀ V₀ B₀
      ≤ ((g : ℝ) + ((s : ℝ) - (g : ℝ)) * rowDensity s j bT) / (s : ℝ)) :
    blockTarget s j ≤ (g : ℝ) :=
  block_count_of_extremal hs hx1 hextremal (hgates.2 j hj)

/-- **`08:229--239` end to end.**

Given the actual Stage-3 block densities -- with the frozen reading of
`beta_j^raw` as a lower bound for their average, which is what "the definition
of `beta_j^raw` then gives the remaining density among raw template rows"
asserts -- the extremal bound and the banked ceiling gate together produce the
frozen count: at least `p_j` of the `s` blocks retain an `x_j` fraction of
their rows.

The number of good blocks is not a parameter: it is the cardinality of the set
the frozen text names, so no count is assumed. -/
theorem rawLow_block_count_of_block_densities {s bT T₀ V₀ B₀ : ℕ} (hs : 0 < s) {y : ℝ}
    (hgates : rawLowGates s bT T₀ V₀ B₀ y) {j : ℕ} (hj : j ≤ 2)
    (hx1 : rowDensity s j bT < 1)
    (d : Fin s → ℝ) (hd1 : ∀ i, d i ≤ 1)
    (hbeta : betaRaw (rTail y j) T₀ V₀ B₀ ≤ (∑ i, d i) / (s : ℝ)) :
    blockTarget s j
      ≤ (((Finset.univ.filter fun i => rowDensity s j bT ≤ d i).card : ℕ) : ℝ) := by
  classical
  exact rawLow_block_count hs hgates hj hx1
    (le_trans hbeta (extremal_block_bound d (rowDensity s j bT) hd1))

/-- **Aux 3 (`06:271--273`: every rung threshold is a legal density).**  The
frozen consequence of `eq:hard-seed-width-gates` -- "each `I_j = s/2^j`,
`j = 0,1,2`, is a legal hard-seed width and satisfies `I_j < 2^{b_T}`" -- gives
the side condition `x_j < 1` that `block_count_of_extremal` needs.  General in
`s`, `j` and `b_T`. -/
theorem rowDensity_lt_one {s j bT : ℕ} (hs : (s : ℝ) < 2 ^ bT) :
    rowDensity s j bT < 1 := by
  have hpowj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hpowT : (0 : ℝ) < 2 ^ bT := by positivity
  have hnonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hw : widthI s j ≤ (s : ℝ) := by
    rw [widthI, div_le_iff₀ (by positivity)]
    nlinarith
  have hrw : rowDensity s j bT = widthI s j / 2 ^ bT := by
    simp [rowDensity, xTdepth, div_eq_mul_inv]
  rw [hrw, div_lt_one hpowT]
  linarith

/-- **The frozen margin display of `06:904--908`, turned into the gate.**

The schedule's rational margins are stated as
`(beta_j^raw - x_j)/(1 - x_j) >= 9/(16 * 2^j)`, "which is precisely the row
density needed for the three raw lower rungs".  Since `p_j = 9 I_j/16` and
`I_j = s/2^j`, that margin is exactly `p_j <= s (beta_j - x_j)/(1 - x_j)`, and
`Nat.le_ceil` promotes it to the ceiling form the banked `rawLowGates` uses.

General in every parameter, and stated so that the ceiling is only ever used on
the side that makes the gate easier to *establish* and harder to *use*. -/
theorem rawLow_gate_of_margin {s bT T₀ V₀ B₀ : ℕ} {y : ℝ} {j : ℕ}
    (hmargin : 9 / (16 * 2 ^ j)
      ≤ (betaRaw (rTail y j) T₀ V₀ B₀ - rowDensity s j bT) / (1 - rowDensity s j bT)) :
    blockTarget s j
      ≤ (⌈(s : ℝ) * (betaRaw (rTail y j) T₀ V₀ B₀ - rowDensity s j bT)
            / (1 - rowDensity s j bT)⌉₊ : ℝ) := by
  have hb : blockTarget s j = (s : ℝ) * (9 / (16 * 2 ^ j)) := by
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    simp only [blockTarget, widthI]
    field_simp
  have h1 : blockTarget s j
      ≤ (s : ℝ) * ((betaRaw (rTail y j) T₀ V₀ B₀ - rowDensity s j bT)
          / (1 - rowDensity s j bT)) := by
    rw [hb]
    exact mul_le_mul_of_nonneg_left hmargin (Nat.cast_nonneg s)
  refine le_trans h1 ?_
  rw [← mul_div_assoc]
  exact Nat.le_ceil _

/-- **Aux 4 (the block target is genuine content).**  `p_j > 0` at every legal
`s`, so `rawLow_block_count` asserts the existence of at least one good Stage-3
block and is not the vacuous `0 <= g`. -/
theorem blockTarget_pos {s j : ℕ} (hs : 0 < s) : 0 < blockTarget s j := by
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  simp only [blockTarget, widthI]
  positivity

/-! ## §3  The projection step (`08:241--242`) = `lem:regular-density-transfer`

"Project the retained base columns to any `p_j` such blocks.  Projection cannot
decrease their normalized density."

`09:53--55` says outright what licenses that sentence: "The proof below
repeatedly forgets uniform duplication labels.  We pin down the finite-map
property that makes the resulting density comparisons valid."  The property is
`def:regular-finite-map` (`09:56--67`) and the comparison is
`lem:regular-density-transfer` (`09:69--104`).  Both are transcribed here in
full, including the product clause. -/

/-- **`def:regular-finite-map` (`09:56--67`).**  `phi` is
`(d_-, d_+)`-fibre-bounded if `d_- <= |phi^{-1}(b)| <= d_+` for every `b`; a
*regular map of degree `d`* is the case `d_- = d_+ = d`, and the frozen text
says "throughout this section the word regular has only this meaning".

`M1`/`M4`: a purely finite counting predicate on a map -- no matrix, no
protocol, no promise certificate, no complexity conclusion.  `M3`: the
surjectivity that `09:64--65` derives is not a field; it is proved below. -/
def IsFibreBounded {A B : Type*} [Fintype A] [DecidableEq B]
    (φ : A → B) (dLo dHi : ℕ) : Prop :=
  ∀ b : B, dLo ≤ (Finset.univ.filter fun a => φ a = b).card
         ∧ (Finset.univ.filter fun a => φ a = b).card ≤ dHi

/-- **Aux 5 (`09:64--65`: a regular map is surjective).**  Derived, never
assumed: a positive lower fibre bound forces every point of the codomain to be
hit.  This is the `M3` check on `IsFibreBounded`. -/
theorem IsFibreBounded.surjective {A B : Type*} [Fintype A] [DecidableEq B]
    {φ : A → B} {dLo dHi : ℕ} (h : IsFibreBounded φ dLo dHi) (hd : 0 < dLo) :
    Function.Surjective φ := by
  intro b
  have hcard : 0 < (Finset.univ.filter fun a => φ a = b).card :=
    lt_of_lt_of_le hd (h b).1
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hcard
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

/-- **Aux 6 (monotone in the two bounds).**  Widening the fibre window
preserves fibre-boundedness.  A unit test that the two fields sit on the sides
the frozen definition puts them on: an encoding that swapped `d_-` and `d_+`
would not allow this direction. -/
theorem IsFibreBounded.mono {A B : Type*} [Fintype A] [DecidableEq B]
    {φ : A → B} {dLo dHi eLo eHi : ℕ} (h : IsFibreBounded φ dLo dHi)
    (hLo : eLo ≤ dLo) (hHi : dHi ≤ eHi) : IsFibreBounded φ eLo eHi :=
  fun b => ⟨le_trans hLo (h b).1, le_trans (h b).2 hHi⟩

/-- **`eq:fibre-bounded-density-transfer` (`09:73--78`).**

For a `(d_-, d_+)`-fibre-bounded `phi` with `d_- > 0`, and every `S`,
`|phi(S)|/|B| >= (d_- / d_+) |S|/|A|`.

The frozen proof is transcribed step for step: "Every element of `S` lies in a
fibre above `phi(S)`, so `|S| <= d_+ |phi(S)|`.  Summing the lower fibre bound
over `B` gives `d_- |B| <= |A|`."  General in both carriers and in `S`. -/
theorem fibreBounded_density_transfer {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {φ : A → B} {dLo dHi : ℕ} (h : IsFibreBounded φ dLo dHi) (hdLo : 0 < dLo)
    (hA : 0 < Fintype.card A) (S : Finset A) :
    (dLo : ℝ) / (dHi : ℝ) * ((S.card : ℝ) / (Fintype.card A : ℝ))
      ≤ ((S.image φ).card : ℝ) / (Fintype.card B : ℝ) := by
  classical
  obtain ⟨a0⟩ : Nonempty A := Fintype.card_pos_iff.mp hA
  have hdHi : 0 < dHi := lt_of_lt_of_le hdLo (le_trans (h (φ a0)).1 (h (φ a0)).2)
  have hB : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨φ a0⟩
  -- (1)  `|S| <= d_+ |phi(S)|`.
  have h1 : S.card ≤ dHi * (S.image φ).card := by
    have hsum : S.card = ∑ b ∈ S.image φ, (S.filter fun a => φ a = b).card :=
      Finset.card_eq_sum_card_image φ S
    calc S.card = ∑ b ∈ S.image φ, (S.filter fun a => φ a = b).card := hsum
      _ ≤ ∑ _b ∈ S.image φ, dHi := by
          refine Finset.sum_le_sum ?_
          intro b _
          refine le_trans (Finset.card_le_card ?_) (h b).2
          intro a ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩
      _ = (S.image φ).card * dHi := by simp [Finset.sum_const, mul_comm]
      _ = dHi * (S.image φ).card := by ring
  -- (2)  `d_- |B| <= |A|`.
  have h2 : dLo * Fintype.card B ≤ Fintype.card A := by
    have hsum : (Finset.univ : Finset A).card
        = ∑ b ∈ (Finset.univ : Finset B), ((Finset.univ : Finset A).filter fun a => φ a = b).card :=
      Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (φ a))
    calc dLo * Fintype.card B = ∑ _b ∈ (Finset.univ : Finset B), dLo := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ b ∈ (Finset.univ : Finset B),
            ((Finset.univ : Finset A).filter fun a => φ a = b).card :=
          Finset.sum_le_sum (fun b _ => (h b).1)
      _ = Fintype.card A := by simpa [Finset.card_univ] using hsum.symm
  have haR : (S.card : ℝ) ≤ (dHi : ℝ) * ((S.image φ).card : ℝ) := by exact_mod_cast h1
  have hbR : (dLo : ℝ) * (Fintype.card B : ℝ) ≤ (Fintype.card A : ℝ) := by exact_mod_cast h2
  have hdLoR : (0 : ℝ) < (dLo : ℝ) := by exact_mod_cast hdLo
  have hdHiR : (0 : ℝ) < (dHi : ℝ) := by exact_mod_cast hdHi
  have hnR : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hA
  have hmR : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast hB
  have hiR : (0 : ℝ) ≤ ((S.image φ).card : ℝ) := Nat.cast_nonneg _
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hmR]
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR hdLoR.le) hmR.le,
    mul_le_mul_of_nonneg_left hbR (mul_nonneg hdHiR.le hiR)]

/-- **`eq:regular-density-transfer` (`09:80--84`), the regular case.**

"Projection cannot decrease their normalized density" (`08:242`), in the exact
form the reader prints at `A-stage4-details.tex:305--311`: if every fibre of
`phi` has the same positive size, then `|phi(S)|/|B| >= |S|/|A|` for every
`S`. -/
theorem regular_density_transfer {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {φ : A → B} {d : ℕ} (h : IsFibreBounded φ d d) (hd : 0 < d)
    (hA : 0 < Fintype.card A) (S : Finset A) :
    (S.card : ℝ) / (Fintype.card A : ℝ) ≤ ((S.image φ).card : ℝ) / (Fintype.card B : ℝ) := by
  have hne : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    exact ne_of_gt this
  have := fibreBounded_density_transfer h hd hA S
  rwa [div_self hne, one_mul] at this

/-- **Aux 7 (inhabitation, degenerate end).**  The identity is regular of
degree one. -/
theorem isFibreBounded_id {A : Type*} [Fintype A] [DecidableEq A] :
    IsFibreBounded (id : A → A) 1 1 := by
  intro b
  have hfil : (Finset.univ.filter fun a : A => id a = b) = {b} := by
    ext a; simp [eq_comm]
  rw [hfil]; simp

/-- **Aux 8 (inhabitation, NONDEGENERATE).**  The first projection
`A x B -> A` is regular of degree `|B|`.  This is the shape the frozen text
actually uses -- forgetting a uniform duplication label -- and it is
non-injective with fibres of size `> 1` as soon as `|B| > 1`, so
`regular_density_transfer` is not inhabited only by bijections.  Together with
`regular_density_transfer_at_projection` below, the pair is a genuine
non-vacuity witness at legal values. -/
theorem isFibreBounded_fst {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] :
    IsFibreBounded (Prod.fst : A × B → A) (Fintype.card B) (Fintype.card B) := by
  intro b
  have hfil : (Finset.univ.filter fun a : A × B => a.1 = b)
      = ({b} : Finset A) ×ˢ (Finset.univ : Finset B) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [hfil]
  simp

/-- **Aux 9 (the nondegenerate witness really is nondegenerate).**  At
`A = Fin 2`, `B = Fin 3` the projection is regular of degree `3 > 1` and is not
injective, so the degree-one identity case is not the only inhabitant. -/
theorem isFibreBounded_fst_nondegenerate :
    IsFibreBounded (Prod.fst : Fin 2 × Fin 3 → Fin 2) 3 3
      ∧ 1 < 3
      ∧ ¬ Function.Injective (Prod.fst : Fin 2 × Fin 3 → Fin 2) := by
  refine ⟨?_, by norm_num, ?_⟩
  · have h := isFibreBounded_fst (A := Fin 2) (B := Fin 3)
    simpa using h
  · intro hinj
    have : ((0 : Fin 2), (0 : Fin 3)) = ((0 : Fin 2), (1 : Fin 3)) := hinj rfl
    simp at this

/-- **Aux 10 (the transfer really moves).**  At the nondegenerate witness of
Aux 8 the transfer is not an identity in disguise: forgetting a `Fin 3`-labelled
duplication takes a single labelled cell, of density `1/6` in `Fin 2 x Fin 3`,
to a cell of density `1/2` in `Fin 2`.  A unit test that the two carriers sit on
the sides the frozen display puts them on -- swapping numerator and denominator,
or dividing the image by `|A|`, would make this strict inequality false. -/
theorem regular_density_transfer_at_projection :
    (({((0 : Fin 2), (0 : Fin 3))} : Finset (Fin 2 × Fin 3)).image
        (Prod.fst : Fin 2 × Fin 3 → Fin 2)) = {(0 : Fin 2)}
      ∧ (1 : ℝ) / (Fintype.card (Fin 2 × Fin 3) : ℝ)
          < (1 : ℝ) / (Fintype.card (Fin 2) : ℝ) := by
  refine ⟨by simp, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num

/-- **Aux 11 (`09:87--88`, the product clause).**  "The product of maps regular
of degrees `d_1, d_2` is regular of degree `d_1 d_2`."  The frozen proof is
transcribed: "a fibre of `phi_1 x phi_2` is the Cartesian product of one fibre
of each factor and therefore has cardinality `d_1 d_2`." -/
theorem isFibreBounded_prod {A₁ B₁ A₂ B₂ : Type*} [Fintype A₁] [Fintype A₂]
    [DecidableEq B₁] [DecidableEq B₂]
    {φ₁ : A₁ → B₁} {φ₂ : A₂ → B₂} {d₁ d₂ : ℕ}
    (h₁ : IsFibreBounded φ₁ d₁ d₁) (h₂ : IsFibreBounded φ₂ d₂ d₂) :
    IsFibreBounded (Prod.map φ₁ φ₂) (d₁ * d₂) (d₁ * d₂) := by
  classical
  intro b
  have hfil : (Finset.univ.filter fun a : A₁ × A₂ => Prod.map φ₁ φ₂ a = b)
      = (Finset.univ.filter fun a₁ => φ₁ a₁ = b.1)
          ×ˢ (Finset.univ.filter fun a₂ => φ₂ a₂ = b.2) := by
    ext a
    simp [Finset.mem_product, Prod.ext_iff, Prod.map]
  rw [hfil, Finset.card_product]
  exact ⟨Nat.mul_le_mul (h₁ b.1).1 (h₂ b.2).1, Nat.mul_le_mul (h₁ b.1).2 (h₂ b.2).2⟩

/-! ## §4  The schedule identity `D_2 + log_2 I_j = C - 1 - j` (`08:245--251`)

The frozen chain closes with an identity of **public integers**:
`D_2 + log_2 I_j = C - 1 - j`.  With `I_j = s/2^j` (`06:912`) the left summand
is `log_2 s - j`, and `C = D_2 + log_2 s + 1` is the banked `cBlock` reading of
`08:149--152`.  Both facts are recorded here, the second one tying the natural
exponent to the real width the rest of the section uses. -/

/-- **`08:245--251`, the schedule identity.**  With `w_S = log_2 s` and
`log_2 I_j = w_S - j`, the frozen `D_2 + log_2 I_j = C - 1 - j` holds exactly,
and the rung readout `j + (D_2 + log_2 I_j) = C - 1` holds with no truncated
subtraction.  General in the four public integers. -/
theorem rung_schedule_identity (Dsrc a r₂ wS j : ℕ) (hj : j ≤ wS) :
    dTwoBlock Dsrc a r₂ + (wS - j) = cBlock Dsrc a r₂ wS - 1 - j
      ∧ j + (dTwoBlock Dsrc a r₂ + (wS - j)) = cBlock Dsrc a r₂ wS - 1 := by
  simp only [cBlock, dTwoBlock, dTwo, bCap]
  omega

/-- **Aux 12 (the natural exponent is the real width).**  At the frozen
power-of-two scale `s = 2^{w_S}` the width `I_j = s/2^j` of `06:912` is exactly
`2^{w_S - j}`, so writing `log_2 I_j = w_S - j` in `rung_schedule_identity` is
an identity and not a convention.  This is the tie that would break if the
natural subtraction were being used outside its legal range. -/
theorem widthI_eq_two_pow (wS j : ℕ) (hj : j ≤ wS) :
    widthI (2 ^ wS) j = 2 ^ (wS - j) := by
  have hsplit : (2 : ℝ) ^ wS = 2 ^ (wS - j) * 2 ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hj0 : (0 : ℝ) < 2 ^ j := by positivity
  rw [widthI]
  push_cast
  rw [hsplit]
  field_simp

/-- **Aux 12b (the rung value really is `D_2 + log_2 I_j`).**

At the frozen power-of-two scale `s = 2^{w_S}` the two halves of `08:245--251`
line up on the nose: the width is `I_j = 2^{w_S - j}`, so the natural exponent
`w_S - j` that `rawLowProfile_body` hands to the seed binder *is* `log_2 I_j`,
and the rung value `D_2 + (w_S - j)` *is* `C - 1 - j`.

This is what makes `hpow : s = 2 ^ w_S` load-bearing rather than decorative in
`§6`: with `s` and `w_S` unlinked, `cBlock Dsrc a r_2 w_S` need not be the
frozen `C = D_2 + log_2 s + 1` of `08:149--152` at all, and the conclusion
would be a statement about an unrelated integer. -/
theorem rung_value_eq_log_width (Dsrc a r₂ wS j : ℕ) (hj : j ≤ wS) :
    widthI (2 ^ wS) j = 2 ^ (wS - j)
      ∧ dTwoBlock Dsrc a r₂ + (wS - j) = cBlock Dsrc a r₂ wS - 1 - j :=
  ⟨widthI_eq_two_pow wS j hj, (rung_schedule_identity Dsrc a r₂ wS j hj).1⟩

/-! ## §5  The inherited General Hard Seed call at width `I_j` (`08:242--251`)

"The inherited General Hard Seed Lemma, instantiated at width `I_j`, therefore
leaves a member of `<M_2^T, p_j, x_j, h_j^raw>` of complexity at least
`D_2 + log_2 I_j`."

There is no vendored Lean declaration of that lemma at this shape, and the
banked `StageOneInterlace` precedent is binding: the inherited corollary enters
as an explicit **named binder** on the theorems that use it, never as a silent
axiom and never as a bundle field.  `RungSeedWitness` is that binder, written
once as a named proposition so that `§6` can quantify over the three rungs.

What the binder says is exactly the frozen output: *every* member of the rung's
bracket family contains, after the discard/projection steps of `§1`--`§3`, a
restriction whose complexity reaches the rung value.  What `§6` proves on top
of it is the transport -- restriction monotonicity and the passage to the
family infimum -- which is not part of the inherited statement. -/

/-- **The inherited rung output at width `I_j` (`08:242--251`), as a named
hypothesis.**

`M1`: this is a *statement about a pinned family*, not constructor data; it is
a hypothesis at every use site and is never inhabited inside this module.  The
existential is genuine: see `seed_witness_trivial_fails`, which shows the empty
restriction never satisfies it at a positive rung value. -/
def RungSeedWitness {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (n j : ℕ) (x y : ℝ) : Prop :=
  ∀ RC ∈ bracketGE Rw Cl 1 x (y / 2 ^ j),
    ∃ R' ⊆ RC.1, ∃ C' ⊆ RC.2, n ≤ D (subgame (interlaceFun Nmat 1) R' C')

/-- **Aux 13 (the empty restriction has complexity zero).**  A leaf protocol
computes a game on empty carriers, so `D` of the empty subgame is `0`.  Proved
through the banked `PublicRecords.D_const`, consumed by pin. -/
theorem D_subgame_empty {A B : Type*} (g : A → B → Bool) :
    D (subgame g (∅ : Finset A) (∅ : Finset B)) = 0 := by
  have h : subgame g (∅ : Finset A) (∅ : Finset B) = fun _ _ => false := by
    funext a c
    exact absurd a.2 (Finset.notMem_empty a.1)
  rw [h]
  exact D_const false

/-- **Statement pole for `RungSeedWitness` (the trivial witness fails).**

The existential in `RungSeedWitness` is not satisfiable by the trivial
restriction: taking `R' = C' = empty` gives complexity `0`, which misses every
positive rung value `D_2 + log_2 I_j`.  So the binder really does demand the
inherited hard-seed output and cannot be discharged by shrinking. -/
theorem seed_witness_trivial_fails {A B : Type*}
    (g : A → B → Bool) {n : ℕ} (hn : 0 < n) :
    ¬ (n ≤ D (subgame g (∅ : Finset A) (∅ : Finset B))) := by
  rw [D_subgame_empty]
  omega

/-- **Aux 14 (the seed binder is a pure lower-bound demand on the matrix).**

`RungSeedWitness` follows from a member-wise complexity lower bound, by taking
the improper restriction.  This is what makes the binder a *demand on `Nmat`*
and on nothing else: no clause about the schedule parameters, the gates or the
family shape can refute it, which is the shape check behind the consistency
probe below. -/
theorem RungSeedWitness_of_member_bound {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) {n j : ℕ} {x y : ℝ}
    (h : ∀ RC ∈ bracketGE Rw Cl 1 x (y / 2 ^ j),
      n ≤ D (subgame (interlaceFun Nmat 1) RC.1 RC.2)) :
    RungSeedWitness Nmat n j x y :=
  fun RC hRC => ⟨RC.1, subset_rfl, RC.2, subset_rfl, h RC hRC⟩

/-! ## §6  The composed `hrung` supply, and the banked opening applied
(`08:252--256`)

"This proves `j + comp<N,1,x_N,y/2^j> >= C - 1`.  Taking the minimum over
`j = 0,1,2` gives the claimed three-rung bound."

The passage from the per-member rung output to the family bound is proved here
(restriction monotonicity through the vendored `D_subgame_mono`, then the
family infimum).  The minimum over the three rungs is the banked
`rawLowProfile`, consumed by pin. -/

/-- **Per-member rung outputs give the family bound.**

`Dfamily` is a `Nat.sInf` and returns `0` on the empty family, so the
nonemptiness side condition is carried explicitly.  The restriction step is the
vendored `NPCC.D_subgame_mono`, consumed by pin: complexity cannot rise when a
game is restricted, so the sub-member's lower bound transports to the member.
General in the matrix, the densities and the rung index. -/
theorem Dfamily_ge_of_seed_witnesses {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) {n j : ℕ} {x y : ℝ}
    (hne : (bracketGE Rw Cl 1 x (y / 2 ^ j)).Nonempty)
    (h : RungSeedWitness Nmat n j x y) :
    n ≤ Dfamily (interlaceFun Nmat 1) (bracketGE Rw Cl 1 x (y / 2 ^ j)) := by
  classical
  obtain ⟨RC0, hRC0⟩ := hne
  have hset : {d : ℕ | ∃ RC ∈ bracketGE Rw Cl 1 x (y / 2 ^ j),
      d = D (subgame (interlaceFun Nmat 1) RC.1 RC.2)}.Nonempty := ⟨_, ⟨RC0, hRC0, rfl⟩⟩
  obtain ⟨RC, hRC, heq⟩ := Nat.sInf_mem hset
  obtain ⟨R', hR', C', hC', hbound⟩ := h RC hRC
  rw [Dfamily, heq]
  exact le_trans hbound (D_subgame_mono _ hR' hC')

/-- **`lem:raw-low-profile` (`08:193--216`), with its proof body supplied.**

The banked `rawLowProfile` reduces the lemma to a three-rung hypothesis.  This
theorem supplies that hypothesis from the inherited hard-seed call at width
`I_j` (the named binder `hseed`), the schedule identity of `§4`, and the
family transport of `Dfamily_ge_of_seed_witnesses` -- i.e. from the frozen
proof body `08:242--256`, with `§1`--`§3` proved above as the steps that make
the call legal.

`Admissible` and `NoCert` stay explicit propositional binders, and `hseed` is
gated behind both exactly as the frozen text gates the deeper rung outputs.

**The scale binder (`hpow`) is the substance of the statement, not decoration.**
`08:149--152` fixes `C = D_2 + log_2 s + 1`, and the banked `cBlock` is that
number *read off `w_S`*; so unless `w_S` is tied to `s` the conclusion is a
bound by an unrelated integer and `w_S - j` is not `log_2 I_j`.  The frozen
Stage-3 scale is a power of two, so the tie is the identity `s = 2^{w_S}`, and
`rung_value_eq_log_width` is the check that under it the rung value fed to
`hseed` is exactly `D_2 + log_2 I_j = C - 1 - j`.

**The two numeric side conditions are derived here, not assumed.**  `06:975`
("The penultimate comparison uses `64 | s`, hence `s >= 64`") is the frozen
divisibility of the source scale; with `hpow` it gives `2^6 | 2^{w_S}`, hence
`6 <= w_S`, which covers the schedule side condition `j <= log_2 s` for
`j <= 2`, and it gives `64 <= s`, hence the floor `4 <= s` that the banked
`rawLowProfile` demands.  Neither is a free binder. -/
theorem rawLowProfile_body {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (Dsrc a r₂ wS s bT T₀ V₀ B₀ : ℕ) (y : ℝ)
    (Admissible NoCert : Prop) (hAdm : Admissible) (hNo : NoCert)
    (hpow : s = 2 ^ wS) (hdiv : 64 ∣ s)
    (hgates : rawLowGates s bT T₀ V₀ B₀ y)
    (hne : ∀ j : ℕ, j ≤ 2 → (bracketGE Rw Cl 1 xN (y / 2 ^ j)).Nonempty)
    (hseed : Admissible → NoCert → ∀ j : ℕ, j ≤ 2 →
      RungSeedWitness Nmat (dTwoBlock Dsrc a r₂ + (wS - j)) j xN y) :
    cBlock Dsrc a r₂ wS - 1 ≤ LambdaGE Nmat 1 xN y := by
  have hspos : 0 < s := by rw [hpow]; positivity
  have h64 : 64 ≤ s := Nat.le_of_dvd hspos hdiv
  have hs : 4 ≤ s := le_trans (by norm_num) h64
  have hwS : 6 ≤ wS := by
    have hdvd : (2 : ℕ) ^ 6 ∣ 2 ^ wS := by
      rw [← hpow]; simpa using hdiv
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  refine rawLowProfile Nmat (cBlock Dsrc a r₂ wS) s bT T₀ V₀ B₀ y
    Admissible NoCert hAdm hNo hs hgates ?_
  intro hA hN j hj
  have hfam := Dfamily_ge_of_seed_witnesses Nmat (hne j hj) (hseed hA hN j hj)
  have hid := (rung_schedule_identity Dsrc a r₂ wS j (by omega)).2
  omega

/-! ## §7  Non-vacuity: the banked gate predicate is inhabited at a legal tier

The banked `rawLowProfile` and everything built on it is conditional on
`rawLowGates`, and a gate predicate that no legal schedule satisfies would make
the whole layer vacuous.  The witness below is at a **legal** tier of the
frozen schedule and is nondegenerate in every coordinate the frozen text
constrains.  Crucially `b_T` is **not a chosen numeral**: `06:239--242` forces
`b_T = 2^{j_49(k_T)}` from `k_T = log_2(s/4)`, so once `s` is fixed the value
of `b_T` is determined, and it is carried below as a **checked identity**
(`witness_bT_checked`) rather than as a free parameter.

* `s = 2^340` -- a power of two with `64 | s` (`06:975`) and `16 | (s/4)`
  (`eq:hard-seed-width-gates`), and `4 <= s`; so `w_S = log_2 s = 340`;
* `k_T = log_2(s/4) = 338`, hence `b_T = 2^{j_49(338)} = 2^9 = 512` -- the
  frozen finite search of `06:72--79` at `k_T`, verified in the
  search-certificate form of `eq:j49-search-data` (`06:91--97`): `j = 9` is a
  displayed feasible candidate `P_{338}(9)` and the maximality eliminator
  `P_{338}(j) -> j <= 9` holds, so `j_49(338) = 9` and no other `b_T` is legal
  at this `s`.  Then `log_2 s = 340 < 512 = b_T` is exactly the third clause of
  `eq:hard-seed-width-gates`, hence each `I_j < 2^{b_T}`, and the rung row
  densities are `x_j = I_j x_T = 2^{-172-j}`;
* `|T| = 2^346`, `|W_V| = |W_B| = 2^300` -- **nonempty** protected row
  reservoirs, so the `beta^raw` ceiling correction of `08:176--181` is
  genuinely active and the witness is not the degenerate `|W_V| = |W_B| = 0`
  case; and `|T| >= s`, as `08:22`'s `T = ⨆_{p in [s]} T_p` requires of a
  disjoint union of `s` nonempty template families;
* `y = 3/5` -- the reader's pinned value (`eq:paper-protected-low`).

The first gate is checked through the real-power schedule at `I_2 = 2^338`;
the three rung gates are checked through `rawLow_gate_of_margin`, i.e. through
the frozen margin display of `06:904--908`, against `x_j = 2^{-172-j}`. -/

/-- **`P_k(j)`, the frozen finite `j_49` predicate (`06:89`).**

`06:72--79` defines `j_49(k) = max {j >= 0 : 10000 j^2 <= 2401 k}`, and
`06:87--90` names the predicate `P_k(j) <-> 10000 j^2 <= 2401 k` "for later
mechanical uses".  Transcribed literally.

`M1`/`M4`: a pure integer predicate on two naturals -- no schedule constant, no
carrier, no matrix, no complexity or robustness conclusion. -/
def J49Feasible (k j : ℕ) : Prop := 10000 * j ^ 2 ≤ 2401 * k

/-- **Aux 15 (`06:93`, first clause: zero proves nonemptiness).**  `P_k(0)`
holds for every `k`, so the maximum defining `j_49(k)` is taken over a nonempty
set.  General in `k`. -/
theorem J49Feasible.zero (k : ℕ) : J49Feasible k 0 := by
  simp [J49Feasible]

/-- **Aux 16 (`06:94`: `k` is an explicit finite-support bound).**  The frozen
justification is "if `j > k`, then `10000 j^2 > 2401 k`, so no feasible
candidate exceeds `k`".  Derived, never assumed.  General in `k` and `j`. -/
theorem J49Feasible.le_index {k j : ℕ} (h : J49Feasible k j) : j ≤ k := by
  have hjj : j ≤ j ^ 2 := Nat.le_self_pow (by norm_num) j
  simp only [J49Feasible] at h
  omega

/-- **Aux 17 (the feasible set is an initial segment).**  `P_k` is downward
closed in `j`, which is what makes "the maximum" of `06:77--79` the same thing
as "the largest feasible candidate" that `eq:j49-search-data` certifies.  A
unit test on the direction of the inequality: an encoding that wrote
`2401 k <= 10000 j^2` would be *upward* closed and this would fail. -/
theorem J49Feasible.mono {k i j : ℕ} (h : J49Feasible k j) (hij : i ≤ j) :
    J49Feasible k i :=
  le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hij 2)) h

/-- **The witness tier's `b_T` is a CHECKED IDENTITY, not a chosen numeral.**

At `s = 2^340` the frozen chain of `06:239--242` is verified end to end in the
search-certificate form of `eq:j49-search-data`:

* `s/4 = 2^338`, so `k_T = log_2(s/4) = 338`;
* `P_{338}(9)` -- the displayed feasible candidate (`10000 * 81 = 810000 <=
  811538 = 2401 * 338`);
* `P_{338}(j) -> j <= 9` -- the maximality eliminator (at `j >= 10` the left
  side is at least `10^6`), so `j_49(338) = 9`;
* `b_T = 2^{j_49(k_T)} = 2^9 = 512`;
* `log_2 s = 340 < 512 = b_T`, the third clause of
  `eq:hard-seed-width-gates`.

So the numeral `512` fed to `rawLowGates` below is *forced* by `s`, and the
tier cannot be accused of picking a convenient depth. -/
theorem witness_bT_checked :
    (2 ^ 340 : ℕ) / 4 = 2 ^ 338
      ∧ J49Feasible 338 9
      ∧ (∀ j : ℕ, J49Feasible 338 j → j ≤ 9)
      ∧ (512 : ℕ) = 2 ^ 9
      ∧ (340 : ℕ) < 512 := by
  refine ⟨?_, by norm_num [J49Feasible], ?_, by norm_num, by norm_num⟩
  · rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, Nat.pow_div (by norm_num) (by norm_num)]
  intro j hj
  by_contra hcon
  have h10 : (10 : ℕ) ≤ j := by omega
  have hsq : 10 ^ 2 ≤ j ^ 2 := Nat.pow_le_pow_left h10 2
  simp only [J49Feasible] at hj
  omega

/-- **The ceiling-free lower bound on `beta_j^raw` (`08:176--181`).**

`beta_j^raw = (ceil(r_j(|T| + |W_V| + |W_B|)) - |W_V| - |W_B|)/|T|`, so dropping
the ceiling downwards gives
`beta_j^raw >= (r_j(|T| + |W_V| + |W_B|) - |W_V| - |W_B|)/|T|`.

**Exposed at `cc-t7r-r1`** (previously `private`).  It is the step the frozen
schedule sentence `06:902--906` needs -- "these rational margins imply
`(beta_j^raw - x_j)/(1 - x_j) >= 9/(16 . 2^j)`" -- because the margin's lower
bound on `beta_j^raw` has to be *derived* from the reservoir data rather than
assumed, and this is the only place the ceiling is discharged.  This exposure is
the only *declaration-level* delta this module carries in that round: no
statement and no proof term anywhere here changed, and the round's whole diff on
this file is this exposure plus one comment-only citation repair at `:385`
(`06:271--274` -> `06:271--273`).
General in the rung ratio and the three cardinalities, for a positive template
row total. -/
theorem betaRaw_lower {rj : ℝ} {T₀ V₀ B₀ : ℕ} (hT : 0 < T₀) :
    (rj * ((T₀ : ℝ) + (V₀ : ℝ) + (B₀ : ℝ)) - (V₀ : ℝ) - (B₀ : ℝ)) / (T₀ : ℝ)
      ≤ betaRaw rj T₀ V₀ B₀ := by
  have hT' : (0 : ℝ) < (T₀ : ℝ) := by exact_mod_cast hT
  have hceil := Nat.le_ceil (rj * ((T₀ : ℝ) + (V₀ : ℝ) + (B₀ : ℝ)))
  simp only [betaRaw]
  rw [div_le_div_iff₀ hT' hT']
  nlinarith [mul_le_mul_of_nonneg_right hceil hT'.le]

/-- A general step from a numeric gap to the frozen margin shape of
`06:904--908`: if the raw density beats the target by at least the discarded
row density, the margin `(beta - x)/(1 - x) >= c` follows. -/
private theorem margin_of_gap {β x c : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hc : 0 ≤ c)
    (h : c + x ≤ β) : c ≤ (β - x) / (1 - x) := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  rw [le_div_iff₀ h1]
  nlinarith

/-- **The first clause of `eq:raw-low-gates` at the witness tier.**
`h_2^raw <= (x_N - tau)/(1 - tau)` at `s = 2^340`, where `I_2 = 2^338` and the
real-power schedule gives `h_2^raw <= 2^{-8} = 1/256 <= 19/364`.  The estimate
`sqrt 338 >= 300/49` is deliberately crude -- the true value of `h_2^raw` here
is `2^{-515}` -- because a crude bound is all the gate needs and it keeps the
check kernel-cheap. -/
private theorem witness_column_gate :
    hRawSchedule (widthI (2 ^ 340) 2) ≤ (xN - tauR) / (1 - tauR) := by
  have hw : widthI (2 ^ 340 : ℕ) 2 = (2 : ℝ) ^ (338 : ℕ) := by
    rw [widthI_eq_two_pow 340 2 (by norm_num)]
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hself : Real.logb 2 2 = 1 := by
    rw [Real.logb, div_self hl2]
  have hlog : Real.logb 2 ((2 : ℝ) ^ (338 : ℕ)) = 338 := by
    rw [Real.logb_pow, hself]
    norm_num
  have hsqrt : (300 / 49 : ℝ) ≤ Real.sqrt 338 := by
    rw [show (300 / 49 : ℝ) = Real.sqrt ((300 / 49 : ℝ) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hexp : (3 : ℝ) ≤ (49 / 100 : ℝ) * Real.sqrt 338 := by linarith
  have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt 338) := by
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [← h8]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hfinal : hRawSchedule ((2 : ℝ) ^ (338 : ℕ)) ≤ 1 / 256 := by
    simp only [hRawSchedule, hlog]
    have hneg : -((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt 338)) ≤ -(8 : ℝ) := by linarith
    have hmono := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hneg
    have h256 : (2 : ℝ) ^ (-(8 : ℝ)) = 1 / 256 := by
      rw [Real.rpow_neg (by norm_num),
        show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h256] at hmono
    exact hmono
  rw [hw]
  refine le_trans hfinal ?_
  simp only [xN, tauR]
  norm_num

-- The three checks below are literal rational arithmetic at the tier's scale,
-- so the elaborator needs the dyadic literals up to `2^512`; the
-- `exponentiation.threshold` is raised for exactly this declaration and for
-- nothing else in this module.
set_option exponentiation.threshold 600 in
/-- The three numeric gaps behind the rung clauses, at the witness tier.  Each
is the frozen `beta_j^raw` lower bound of `08:176--181` (through `Nat.le_ceil`,
so the exact ceiling value is never needed) against `9/(16 * 2^j)` plus the
rung row density `x_j = 2^{-172-j}`. -/
private theorem witness_rung_gap {j : ℕ} (hj : j ≤ 2) :
    9 / (16 * 2 ^ j) + rowDensity (2 ^ 340) j 512
      ≤ betaRaw (rTail (3 / 5) j) (2 ^ 346) (2 ^ 300) (2 ^ 300) := by
  interval_cases j <;>
    · refine le_trans ?_
        (betaRaw_lower (T₀ := 2 ^ 346) (V₀ := 2 ^ 300) (B₀ := 2 ^ 300) (by positivity))
      simp only [rowDensity, widthI, xTdepth, rTail, sigmaR]
      push_cast
      norm_num

/-- **The three rung clauses of `eq:raw-low-gates` at the witness tier.** -/
private theorem witness_rung_gate {j : ℕ} (hj : j ≤ 2) :
    blockTarget (2 ^ 340) j
      ≤ (⌈((2 ^ 340 : ℕ) : ℝ) * (betaRaw (rTail (3 / 5) j) (2 ^ 346) (2 ^ 300) (2 ^ 300)
            - rowDensity (2 ^ 340) j 512) / (1 - rowDensity (2 ^ 340) j 512)⌉₊ : ℝ) := by
  refine rawLow_gate_of_margin ?_
  have hx0 : (0 : ℝ) ≤ rowDensity (2 ^ 340 : ℕ) j 512 := by
    simp only [rowDensity, widthI, xTdepth]
    positivity
  have hx1 : rowDensity (2 ^ 340 : ℕ) j 512 < 1 := by
    refine rowDensity_lt_one ?_
    have h : (2 : ℕ) ^ 340 < 2 ^ 512 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    exact_mod_cast h
  have hc : (0 : ℝ) ≤ 9 / (16 * 2 ^ j) := by positivity
  exact margin_of_gap hx0 hx1 hc (witness_rung_gap hj)

/-- **NON-VACUITY: the banked gate predicate is inhabited at a legal tier.**

`rawLowGates (2^340) 512 (2^346) (2^300) (2^300) (3/5)` holds.  Every
coordinate is at a legal schedule value: `s = 2^340` is a power of two with
`64 | s` and `16 | (s/4)`; `b_T = 512` is **forced** by `s` through
`witness_bT_checked` (`b_T = 2^{j_49(log_2(s/4))} = 2^{j_49(338)} = 2^9`), and
`log_2 s = 340 < b_T`; the protected row reservoirs `|W_V| = |W_B| = 2^300` are
nonempty and `|T| = 2^346 >= s` as `08:22` requires; `y = 3/5` is the reader's
pinned value.  So `rawLowProfile`, `rawLowProfile_body` and every gate consumer
above are conditional on a predicate that a legal schedule actually
satisfies. -/
theorem rawLowGates_inhabited :
    rawLowGates (2 ^ 340) 512 (2 ^ 346) (2 ^ 300) (2 ^ 300) (3 / 5) := by
  refine ⟨witness_column_gate, ?_⟩
  intro j hj
  exact witness_rung_gate hj

/-- **The witness is nondegenerate.**  The protected row reservoirs are
nonempty, the template reservoir is at least as large as the `s` blocks whose
disjoint union it is (`08:22`), `s` clears every frozen divisibility and window
constraint of `eq:hard-seed-width-gates` and `06:975`, and the rung target
`p_0` is positive -- so the inhabitation above is not obtained by collapsing a
carrier, and it is not at a cardinality-contradictory tier. -/
theorem rawLowGates_inhabited_nondegenerate :
    (0 : ℕ) < 2 ^ 300 ∧ (64 ∣ (2 ^ 340 : ℕ)) ∧ (16 ∣ ((2 ^ 340 : ℕ) / 4))
      ∧ ((2 ^ 340 : ℕ) : ℝ) < 2 ^ (512 : ℕ) ∧ 4 ≤ (2 ^ 340 : ℕ)
      ∧ (2 ^ 340 : ℕ) ≤ (2 ^ 346 : ℕ)
      ∧ 0 < blockTarget (2 ^ 340) 0 := by
  have hdiv64 : (64 : ℕ) ∣ 2 ^ 340 := by
    rw [show (64 : ℕ) = 2 ^ 6 from by norm_num]
    exact pow_dvd_pow 2 (by norm_num)
  have hquarter : (2 ^ 340 : ℕ) / 4 = 2 ^ 338 := witness_bT_checked.1
  have hfour : (4 : ℕ) ≤ 2 ^ 340 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 340 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  refine ⟨by positivity, hdiv64, ?_, ?_, hfour, ?_, blockTarget_pos (by positivity)⟩
  · rw [hquarter, show (16 : ℕ) = 2 ^ 4 from by norm_num]
    exact pow_dvd_pow 2 (by norm_num)
  · have h : (2 : ℕ) ^ 340 < 2 ^ 512 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    exact_mod_cast h
  · exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **Hypothesis-consistency probe for `rawLowProfile_body`.**

Every hypothesis of `rawLowProfile_body` other than the inherited seed binder
holds *simultaneously* at the witness tier over a concrete carrier: the scale
identity `s = 2^{w_S}` at `w_S = 340`, the frozen divisibility `64 | s`
(`06:975`), the banked gate predicate at exactly that `s` (with its `b_T`
forced by `witness_bT_checked`), and the three rung nonemptiness facts at the
frozen `x_N = 1/16` and the reader-pinned `y = 3/5`.  The two facts the theorem
*derives* rather than assumes -- the floor `4 <= s` and the schedule side
condition `6 <= w_S` -- are recorded alongside, so the derivation is visibly
consistent with the same tier.  In particular the theorem is not
green-because-vacuous: `hpow` and the gate predicate hold of one and the same
`s`, which is precisely the defect the unlinked-binder version had.

The remaining binder `hseed` is, by `RungSeedWitness_of_member_bound`, a pure
complexity lower bound on `Nmat`; nothing in the bundle above mentions `Nmat`'s
entries, and no clause bounds `D` from above, so no contradiction can be
assembled from the two together.  Discharging `hseed` itself is the inherited
General Hard Seed call, which is out of scope for this tranche by design.

**The carriers are chosen so that the excluded binder is not refuted by them.**
At `w_S = 340` the rung values `hseed` demands are `D_2 + (340 - j) >= 338`, so
a two- or four-element carrier would make `hseed` *false* and the probe would
be exhibiting a tier at which the omitted hypothesis cannot hold -- exactly the
degenerate reading this probe exists to rule out.  The carriers below therefore
have `Fintype.card = 2^340 = s`, which is cardinality-compatible with those
rung values; the last clause records that size. -/
theorem rawLowProfile_body_side_conditions_consistent :
    ((2 ^ 340 : ℕ) = 2 ^ (340 : ℕ) ∧ (64 ∣ (2 ^ 340 : ℕ))
        ∧ 4 ≤ (2 ^ 340 : ℕ) ∧ 6 ≤ (340 : ℕ))
      ∧ rawLowGates (2 ^ 340) 512 (2 ^ 346) (2 ^ 300) (2 ^ 300) (3 / 5)
      ∧ (∀ j : ℕ, j ≤ 2 →
          (bracketGE (Fin (2 ^ 340)) (Fin (2 ^ 340)) 1 xN
            ((3 / 5 : ℝ) / 2 ^ j)).Nonempty)
      ∧ Fintype.card (Fin (2 ^ 340)) = (2 ^ 340 : ℕ) := by
  refine ⟨⟨rfl, rawLowGates_inhabited_nondegenerate.2.1,
      rawLowGates_inhabited_nondegenerate.2.2.2.2.1, by norm_num⟩,
    rawLowGates_inhabited, ?_, Fintype.card_fin _⟩
  intro j hj
  refine bracketGE.nonempty (X := Fin (2 ^ 340)) (Y := Fin (2 ^ 340)) 1 xN
    ((3 / 5 : ℝ) / 2 ^ j) (by norm_num [xN]) ?_ ?_
  · have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [div_le_one (by positivity)]
    linarith
  · rw [Fintype.card_fin]
    exact Nat.one_le_two_pow

end EthInapproximability.ParameterizedNP.RawLowProfileBody
