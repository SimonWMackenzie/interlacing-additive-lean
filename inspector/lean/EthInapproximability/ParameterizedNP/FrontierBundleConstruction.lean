import EthInapproximability.ParameterizedNP.SelectEmbedComposition

/-!
# Parameterized NP route: branch (i)'s frontier bundle, `09:1269--1276`, CONSTRUCTED

Branch (i) proper is the single sentence `09:1269--1276`; the supply displays it
consumes (`09:1280--1296`) are printed inside branch (ii) and are read here as
branch-INDEPENDENT facts.  See the anchor list below.

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:1233--1236`**, the initial retention `A_r = q A_0` and "Start one
      clean reference certificate in every coordinate outside `E_0`", entering
      as the banked `hR` binder at the paper's own `A_0`.
    * **`09:1238--1248`**, the routing rule and the weight bookkeeping; the
      banked `RoutingDynamics` dynamics, the source of the row supply below.
    * **`09:1250--1252`**, the two stopping rules and the exposure rule -- the
      banked `FrontierIndexing.canonicalSystem.firstBob`, from which `hbob` is
      **derived** here rather than assumed.
    * **`09:1253--1258`**, `d_v` with the display **`09:1255`**,
      `kappa_v = 2^{r-d_v}`, and `W_v` at `09:1257`.  Consumed by pin as the
      banked `TranscriptLevelConstruction.kappaAt` -- the prerequisite
      **`WDFW-F10`**, already executed, never re-reified here.
    * **`09:1268`**, `vartheta = 9/16` (the banked `vartheta`), and the branch
      selector "We first close any first-Bob node satisfying `W_v >= vartheta
      kappa_v`" -- which is why the headline below is a **dichotomy** and not an
      implication out of a hoisted `hheavy`.
    * **`09:1269--1276`, branch (i)** -- the single sentence "When
      `kappa_v >= t_ref`, follow the denser Bob child and invoke the
      certified-scale reference stopping lemma on `G` with ...", whose display
      **`09:1271--1274`** fixes exactly **two** parameters:
      `r' = kappa_v/t_ref` at `09:1272` and `a^sharp = 1` at `09:1273`.  The
      others are *not* fixed here -- `09:1275` reads "The other parameters are
      those of `sec:wrapper-low-rungs`", and that is where `t = t_ref`
      (**`09:319`**) and `h = theta` (**`09:322`**) are fixed.  This is the index
      tuple every statement below is written at.
    * **`09:316--327`**, the `sec:wrapper-low-rungs` substitution block that
      `09:1275` imports: `t = t_ref` at **`09:319`**, `h = theta` at
      **`09:322`**, and at **`09:325--327`** the sentence "The equality
      `eq:reference-all-columns` verifies the orientation; the reference
      restriction is a full product, so its balancedness error is exactly zero;
      and `q/4 >= t_ref` makes all three values of `r'` legal."
    * **`09:1276--1278`** opens **branch (ii)** ("... When
      `2 <= kappa_v < t_ref`, write `ell_v = log_2 kappa_v`").  The three
      displays listed next therefore sit **textually inside branch (ii)**; they
      are read here, and proved in the banked chain, as **branch-INDEPENDENT**
      facts about a frontier node, and **no statement below attributes them to
      branch (i)**.
    * **`09:1280--1283`**, the census `ceil(W_v) >= ceil(9 kappa_v/16) >=
      u_{kappa_v}`, consumed by pin (it supplies `hblocks`).  Branch-independent
      per the previous bullet.
    * **`09:1287--1290`**, the projection form of the parent column density
      (`rho = 2y^2` at `09:1290`).  **GAP-EXPOSED**, verbatim as the banked layer
      records it; nothing here narrows it, and `hdens` is carried as an explicit
      binder for exactly that reason -- see the five-clause table below.
      Branch-independent per the bullet above.
    * **`09:1291--1296`**: "Each selected certificate has at least
      `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows, so trim it
      to the row density `kappa_v x_T`" -- the row supply, discharged through
      the banked `TranscriptLevelSuccessors.exists_frontier_routedTriple_at_paper_schedule`.
      Branch-independent per the bullet above.
    * **`09:1297--1300`** and **`09:1310--1313`** (`eq:wrapper-first-bob-light`)
      are **not** proved here; the left disjunct of the headline is the frozen
      light conclusion as a *case*, never as a theorem.
  * `08-dense-stage4.tex`
    (SHA-256 `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`):
    `08:166`, `x_T = 2^{-b_T}`, the banked `DenseStageFourOpening.xTdepth`.
    This is the density every statement below substitutes; it is never a free
    real.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    **`A:111--112`** ("Let `M` be a nonempty Boolean matrix with `m` rows, ...
    and let `0 < x <= 1`"), **`A:117--118`** ("let `t >= t_cert` be a power of
    two divisible by `16`"), and **`A:125`** ("Let `r, r'` be positive powers of
    two ... and put `q = r t`").  These three are the ambient guards the
    `hpos` discharge of section 1 runs on, and `A:138--141` is the three-clause
    supply the built restriction reads back.
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `eq:tref-search` (`06:558--572`), the defining display of `k_ref`, consumed
    only through the banked `WrapperReferenceConstruction.tRef`; and
    `06:237--243`, which makes `b_T` a **DEFINED** schedule quantity.
* **Reader counterpart: none claimable, searched first-hand this tranche.**
  `routes/parameterized-np/reader-facing/sections/` was searched for `frontier`,
  `trim`, `row density`, `nonempty` and `positive`.  The only hits touching this
  material are `A-stage4-details.tex:315--319` ("Near the full row set, ordinary
  reference copies control the protocol until a terminal frontier; labelled
  protected copies from other outer coordinates are routed to that frontier"),
  `:371--373` and `:387`, all of which are **unnumbered connective proof prose**
  about the terminal two-stream argument, not about the branch-(i) supply
  bundle.  The predecessor `TranscriptLevelConstruction` already records
  `:315--319` once at module level and assigns it to no declaration; this module
  does the same and **no declaration below claims a reader counterpart**.
  Assigning prose to a theorem, or the same prose to two declarations, is what
  the reader-counterpart rule forbids.

## What this module is

The named real blocker of residue `L1`: the **construction** of the branch-(i)
frontier bundle of `09:1269--1276` -- branch (i) proper, the single sentence
whose display is `09:1271--1274` and whose other parameters `09:1275` imports
from `09:316--327` -- fed by the **branch-independent** supply displays of
`09:1280--1296`, at the paper's own index tuple and the paper's own row
schedule, *conditionally on the paper's own hypotheses* --
with every clause of the bundle either derived or named as one of the paper's
own hypotheses at its exact anchor.  Nothing is hoisted.

### The five clauses, and where each one now comes from

* **`hheavy`, `09:1268` -- derived by case split.**  `09:1268` says "We first
  close any first-Bob node satisfying `W_v >= vartheta kappa_v`", i.e. the heavy
  condition *selects a branch*; the headline therefore concludes a
  **disjunction** whose left half is the frozen light case, and the caller
  supplies nothing whatever about `W_v`.
* **`hblocks`, `09:1271--1274` with `09:1280--1283` -- discharged** upstream by
  `TranscriptLevelConstruction.frontierBlockCount_le_heavy_ceiling`, consumed
  by pin.  The census display is printed inside branch (ii) and is read
  branch-independently; see the anchor list.
* **`hpos`, `A:111--112`/`A:117--118`/`A:125` -- derived here**, in section 1,
  from the ambient guards of the invoked theorem: `08:166`'s `x_T = 2^{-b_T}`
  is positive, `A:111`'s row carrier is nonempty, and `09:1255`'s `kappa_v` is
  at least `1`.
* **`hA`, `09:1291--1296` with `09:1238--1239` -- discharged** upstream by
  `TranscriptLevelConstruction.certificate_rows_meet_trim_demand` through the
  banked `exists_frontier_routedTriple_at_paper_schedule`; the row set is the
  certificate's own `rowsAt P (R i) v.val`.  The trim display is printed inside
  branch (ii) and is read branch-independently.
* **`hdens`, `09:1287--1290` -- the paper's own hypothesis, GAP-EXPOSED.**  The
  frozen sentence is about the *projection* `projSet J`, which has no Lean
  form; the column-set analogue is the form `A:141` consumes.  It is therefore
  an explicit named binder, at its anchor, and this module neither closes nor
  narrows the projection form.  Printed inside branch (ii), read
  branch-independently.

So of the five, three are derived or discharged, one is derived by the case
split the frozen text itself performs, and exactly one remains a binder --
declared as such, at the anchor that makes it GAP-EXPOSED.

### The two banked interfaces this tranche wires into genuine consumption

* `WrapperDenseFrontierWiring.exists_frontier_routedTriple` was consumed only by
  callers that **re-carried its bundle as binders** of their own
  (`exists_frontier_routedTriple_at_paper_indices`, then
  `..._at_paper_schedule`), each discharging one more clause and passing the
  rest along.  It is fired here with nothing passed along: `hbob` comes from
  `firstBob_spec`, `hheavy` from the case split, `hpos` from section 1.
* `WrapperDenseFrontierWiring.frontierRoutedRestriction`, and its banked wrapper
  `TranscriptLevelConstruction.paperFrontierRestriction`, had **never been
  applied to a triple the routing produces**: the only two call sites in `src/`
  (`paperFrontierRestriction` itself and `paperFrontierRestriction_selCard`)
  take the triple `htr` as a *binder*, so nothing checked that the object they
  build is reachable at all.  Section 4 builds it from the triple section 3
  constructs, and reads its `A:138--141` census quantities back off the built
  object.

### The four `cc-t5i` drops, re-landed WITH consumers

Tranche `cc-t5i` round `r1` deleted five declarations from
`TranscriptLevelSuccessors`.  One of them,
`exists_trimmed_reference_rows_in_the_positive_regime` (later
`trim_of_unbundled_positivity`), was a **duplicate** of the banked
`exists_trimmed_reference_rows` and is **deliberately not restored** -- restoring
it would re-earn exactly the `L1-F9` finding that removed it.  The other four
were dropped only because they had become unconsumed bytes, and re-landing them
unconsumed would re-earn the `F2` finding.  Each therefore returns here **with a
consumer inside this module**:

* `hpos_at_a_node_iff_positive_density` -- consumed by `hpos_at_paper_schedule`
  and by `hpos_needs_a_nonempty_row_carrier`;
* `hpos_at_paper_schedule` -- consumed by both headlines.  This is also the
  successor **`L1-F10`** of `TRANSCRIPT-LEVEL-SUCCESSORS-001` ("turning that
  supply into a declaration of its own"), **DISCHARGED here** and no longer
  open;
* `certifiedRowFloor_pos_at_paper_schedule` -- consumed by
  `frontier_trim_needs_the_schedule_density` and by the restriction headline's
  positive-fibre readout;
* `trim_unobtainable_at_zero_density` -- consumed by
  `frontier_trim_needs_the_schedule_density`.

## Why the trivial witness fails, for each existential deliverable

* `frontier_bundle_or_light_at_paper_schedule`: the right disjunct demands
  `S.card = r' p_t`, which is **positive** at the frozen guards
  (`paper_blockCount_is_positive`), so `S = empty` is refuted; and it demands
  `T.Nonempty` with `T.card` at least `ceil(r' t x_T m_G)`, which
  `certifiedRowFloor_pos_at_paper_schedule` puts at `1` or above, so `T = empty`
  is refuted.  The left disjunct is a strict inequality between two named
  quantities of the routing and is refutable: the banked
  `TranscriptLevelJoin.splitAudit_is_not_light` exhibits a routed system where it
  is false, so the disjunction is not carried by its left half.
* `frontier_restriction_or_light_at_paper_schedule`: same, plus the produced
  datum's `selCard` is pinned to the frozen `p_{kappa_v}`, which no degenerate
  rectangle attains.

## CANONICAL INHABITATION -- REGISTERED and DEFERRED, not discharged

The paper's own instance of this construction is the routing of the **alleged**
`(C+r-1)`-bit protocol of `09:1188--1193`.  No such protocol exists -- that is
the conclusion of the whole argument -- so the paper never exhibits a bundle;
its object at `09:1268` is a function of the assumed protocol, and the honest
Lean form is the conditional dichotomy below.  The canonical-inhabitation
obligation is therefore **REGISTERED and DEFERRED** in the ledger row
`FRONTIER-BUNDLE-CONSTRUCTION-001`, discharged only when an unconditional
`eq:wrapper-first-bob-light` closes the alleged protocol out.

Section 5 fires the **section 4** headline at the banked `splitAudit` routed
system -- and thereby section 3's, which section 4 consumes.  That instance is
**NON-FIDELITY / BEYOND-PAPER** and inherits every disclosure the banked module
carries: `k_ref = 4` meets every gate in `src/` but `A:117` with `A:26` forces
`t_ref >= t_cert = 2^{2^20}`, so it visits a point the paper never does.  It is a
smoke probe that the constructor is usable end to end; it does **not** satisfy
the deferred obligation and must never be cited as doing so.

**Why there is no separate section-3 live-fire probe.**  Firing section 3 alone
at `splitAudit` yields the proposition `exists (S,T,b), S subseteq ... and
T subseteq ... and RoutedTriple ...` -- which is, symbol for symbol, the banked
`TranscriptLevelSuccessors.splitAudit_yields_paper_indexed_triple`.  A theorem's
content is its statement, so such a declaration would record only a **new proof
route**, not new evidence, and would re-earn the `L1-F9` / `cc-t5i`
rename-not-dedup finding in the other direction.  The banked lemma is therefore
consumed by pin wherever that proposition is wanted, and the live-fire evidence
for section 3 is carried -- independently and with strictly more content -- by
`splitAudit_frontier_restriction_reads_back_the_frozen_census`, whose statement
does record something the banked tree does not: the census `= 9` and the fibre
readouts off the **built** `RestrictionDatum`.

## Residues this module does NOT close (named, not implied)

* `09:1287--1290` stays **GAP-EXPOSED** in its projection form; only the
  column-set analogue is supplied, exactly as the banked layer records.
* `eq:wrapper-first-bob-light` (`09:1310--1313`) is **not proved**: the left
  disjunct is a case, not a conclusion.  Proving it runs through
  `thm:certified-localized-extension` and `lem:certified-row-ladder`, neither of
  which is invoked here.
* `lem:final-reference-uniqueness` (`09:1315--1344`) is untouched;
  `eq:wrapper-initial-survival` (`09:1224--1232`) is still the banked `hR`
  binder rather than a derived gate; `hDenseRung` is neither discharged nor fed;
  `eq:wrapper-u-dense` is asserted nowhere; `thm:first-wrapper` is not proved.
  **No route completion is claimed and none may be inferred.**

## Named successors this module registers

* **`FBC-F1`** -- the `hdens` supply.  When the projection form of
  `09:1287--1290` lands, `hdens` stops being a binder and the headline becomes
  unconditional in the column side.  That is a new declaration in the module
  that lands the projection, not an edit here.
* **`FBC-F2`** -- a joint-satisfiability probe on branch (ii).  Section 5 fires
  at `kappa_v = t_ref`, the boundary `09:1269` assigns to branch (i).  A probe
  strictly inside `09:1277`'s `2 <= kappa_v < t_ref` would exercise the other
  branch's entry; the banked `TranscriptLevelJoin.interiorAudit` is the routed
  system to fire it at.

## Axioms and imports

The sole import is `SelectEmbedComposition`, whose transitive closure is the
`WrapperDenseFrontierWiring` chain; `LegacyNPCC.Stage12`, which reaches the
cited AGHP balanced-family axiom, is **not** imported, directly or
transitively.  `EXPANDER-001` occurs in no hypothesis of any declaration below.
No `axiom`, no opaque certificate, no unproved obligation marker.

## DEFINED-VS-FREE ledger for this tranche

| quantity | status | how it is obtained here |
| --- | --- | --- |
| `kappa_v` | DEFINED, `09:1255` | the banked `kappaAt`, consumed by pin |
| `r'` at `09:1272` | DEFINED | the banked `frontierCopies` |
| `t = t_ref`, `09:319` | DEFINED, `eq:tref-search` | the banked `tRef k_ref` at `4 <= k_ref` |
| `a^sharp` at `09:1273` | DEFINED | the literal `1` of the display |
| `p_t` | DEFINED, `A:120` | the banked `certifiedPt`, evaluated |
| `A_0` | DEFINED, `09:1219` | the banked `initialRefRows (xTdepth b_T) (Fintype.card X)` |
| `x_T` | DEFINED, `08:166` with `06:243` | the banked `xTdepth` at `b_T` |
| `b_T` | DEFINED, `06:239--241` | a binder in sections 1--4; assigned only in the section 5 probe |
| `m_G` | DEFINED, `09:113--116` | read at the row carrier, `Fintype.card X`, never a free natural |
| `theta` | binder | `09:1287--1290` GAP-EXPOSED; `h = theta` (`09:322`) left open |
| `k_ref`, `r` | binders | never assigned outside the labelled section 5 probe |

The `t` row is anchored at `09:319`, reached through `09:1275`'s "The other
parameters are those of `sec:wrapper-low-rungs`".  It is **not** `09:1272`: that
display fixes `r'` and `a^sharp` and nothing else.  The `theta` row's `h = theta`
sits in the same imported block, at `09:322`.

Every numeral in sections 1--4 is a frozen literal of a cited display (`0`, `1`,
`2`, `4`) or an evaluation.  Self-chosen values occur **only** in section 5,
which claims no legality and says so in its own docstring.
-/

namespace EthInapproximability.ParameterizedNP.FrontierBundleConstruction

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
open EthInapproximability.ParameterizedNP.TranscriptLevelConstruction
open EthInapproximability.ParameterizedNP.TranscriptLevelSuccessors

/-! ## §1  `hpos` DISCHARGED from the ambient guards `A:111--112`/`A:117--118`/`A:125`

The row clause of the frontier bundle is `hpos : 0 < r' t x m`.  The banked layer
records (`WrapperDenseFrontierWiring.trim_positivity_iff_factors_positive`) that
this is exactly the conjunction of four positivity facts, and that those four are
*entailed by* what `thm:certified-localized-extension` already fixes before any
restriction is spoken of: `r'` a positive power of two (`A:125`), `t` a power of
two divisible by `16` (`A:117--118`), `m` the row count of a **nonempty** matrix
(`A:111`), and `0 < x <= 1` (`A:112`).

At a frontier node two of the four stop being free, and that is what this
section is: `r' t` collapses to `kappa_v = 2^{r-d_v}` (`09:1255`), which
`one_le_kappaAt` puts at `1` or above, and the density is the schedule's own
`x_T = 2^{-b_T}` (`08:166`), which `xTdepth_pos` puts above `0`.  What is left is
the row carrier's nonemptiness, and nothing else.

The three declarations here were dropped as unconsumed bytes by tranche `cc-t5i`;
each returns with its consumers named in the header and exercised below. -/

section Positivity

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **Aux 1 (identity: at a node the bundle's row clause is EXACTLY positive
density over a nonempty carrier).**

The banked `trim_positivity_iff_factors_positive` reads the clause at four free
quantities, all of which can vanish.  At a frontier node two of them are not
free: `r' t` is `kappa_v = 2^{r-d_v}` (`09:1255`), at least `1` by the banked
`one_le_kappaAt`, so the capacity drops out of the equivalence entirely and what
remains is precisely `0 < x` together with `Rows(G)` nonempty (`09:113--116`
with `A:111`).

This is the statement-pole check for the discharge below: the clause carries
**no** hidden strength beyond the two facts the frozen schedule already fixes at
every node -- in particular it does not secretly constrain the capacity, the
depth, or the protocol.

General in `P`, `Coord`, `R`, `A_0`, `r`, the node and the density `x`; the
density is deliberately *not* specialised to `xTdepth` here, so the equivalence
is available before the schedule is substituted. -/
theorem hpos_at_a_node_iff_positive_density (P : Protocol X Y Z)
    (R : Coord → Finset X) (A0 r : ℕ) (v : FrontierNode P R A0 r) {x : ℝ} :
    0 < ((kappaAt P R A0 r v : ℕ) : ℝ) * x * ((Fintype.card X : ℕ) : ℝ)
      ↔ (0 < x ∧ 0 < Fintype.card X) := by
  have hκ : (0 : ℝ) < ((kappaAt P R A0 r v : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_kappaAt P R A0 r v)
  constructor
  · intro h
    have hX : 0 < Fintype.card X := by
      rcases Nat.eq_zero_or_pos (Fintype.card X) with hzero | hpos
      · rw [hzero] at h; simp at h
      · exact hpos
    have hXR : (0 : ℝ) < ((Fintype.card X : ℕ) : ℝ) := by exact_mod_cast hX
    refine ⟨?_, hX⟩
    by_contra hx0
    have hxle : x ≤ 0 := not_lt.mp hx0
    nlinarith [mul_nonneg (mul_pos hκ hXR).le (neg_nonneg.mpr hxle)]
  · rintro ⟨hx, hX⟩
    have hXR : (0 : ℝ) < ((Fintype.card X : ℕ) : ℝ) := by exact_mod_cast hX
    exact mul_pos (mul_pos hκ hx) hXR

/-- **Aux 2: the bundle's row clause is DISCHARGED at the paper's own schedule.**

At the paper's own row density `x_T = 2^{-b_T}` (`08:166`, the banked `xTdepth`,
with `b_T` DEFINED by `06:239--241` and left a binder here) over a nonempty row
carrier -- which `A:111` fixes for the invoked lemma's matrix, and which
`09:113--116` reads at `m_G = abs(Rows(G))` -- the clause holds at **every**
frontier node with no further hypothesis.

This is what makes the headline's `hpos` a derivation rather than a binder: the
caller supplies `A:111`'s carrier nonemptiness, which is a hypothesis of the
invoked theorem itself, and the rest is evaluation.  Read it against the banked
`TranscriptLevelSuccessors.hone_can_fail_at_legal_positive_xT`, which exhibits
legal schedule values at which the *retired* `hone` is false: a clause the
schedule always supplies has replaced one it does not.

General in `P`, `Coord`, `R`, `A_0`, `r`, the node and `b_T`; the row carrier
enters only through its cardinality, and no numeral is assigned anywhere. -/
theorem hpos_at_paper_schedule (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r bT : ℕ) (v : FrontierNode P R A0 r) (hX : 0 < Fintype.card X) :
    0 < ((kappaAt P R A0 r v : ℕ) : ℝ) * xTdepth bT * ((Fintype.card X : ℕ) : ℝ) :=
  (hpos_at_a_node_iff_positive_density P R A0 r v).mpr ⟨xTdepth_pos bT, hX⟩

/-- **Aux 3, a STATEMENT POLE: `A:111`'s carrier nonemptiness is load-bearing.**

The discharge above consumes exactly one hypothesis, and here is the point at
which dropping it destroys the clause rather than merely the proof: over an
empty row carrier the bundle's row clause is **false**, at every node, at every
capacity, and at every density whatever -- including the paper's own `x_T`.

So `A:111`'s "nonempty Boolean matrix" is not decoration inherited from the
statement of `thm:certified-localized-extension`; it is the whole residual
content of `hpos` once the schedule is substituted.

General in `P`, `Coord`, `R`, `A_0`, `r`, the node and the density; no numeral is
assigned, and the hypothesis is a cardinality equation rather than a chosen
carrier. -/
theorem hpos_needs_a_nonempty_row_carrier (P : Protocol X Y Z) (R : Coord → Finset X)
    (A0 r : ℕ) (v : FrontierNode P R A0 r) (hX : Fintype.card X = 0) {x : ℝ} :
    ¬ (0 < ((kappaAt P R A0 r v : ℕ) : ℝ) * x * ((Fintype.card X : ℕ) : ℝ)) := by
  intro h
  have := ((hpos_at_a_node_iff_positive_density P R A0 r v).mp h).2
  omega

end Positivity

/-! ## §2  The trim target at the paper's schedule, and the pole that separates it

`09:1296` trims "to the row density `kappa_v x_T`", and `A:139--140` fixes the
target `ceil(r' t x m)`.  Two facts about that target are needed by the
construction and are recorded here: it is positive along the paper's own row
densities, so the `T.Nonempty` clause the banked supply delivers is never
vacuously satisfied; and it is *not* positive at `x = 0`, where the existential
deliverable is unobtainable outright.

Both declarations were dropped by `cc-t5i` as unconsumed; the two-sided
statement below is their consumer, and the restriction headline of section 3
consumes the first again. -/

section TrimTarget

/-- **Aux 4 (the conclusion's own nonemptiness clause is live at the schedule).**

`A:139--140`'s floor `ceil(r' t x m)` is what `09:1291--1296` trims to, and the
banked `certifiedRowFloor_pos_iff_trim_positive` makes its positivity equivalent
to the bundle's row clause.  Substituting the paper's own `x = x_T = 2^{-b_T}`
(`08:166`) turns that equivalence into an unconditional fact about the schedule:
at any positive widths over a nonempty carrier the trim demanded is at least one
row.

Both banked lemmas are consumed by pin and neither is restated.  General in `r'`,
`t`, `m` and `b_T`; no numeral is assigned. -/
theorem certifiedRowFloor_pos_at_paper_schedule {r' t m bT : ℕ}
    (hr' : 0 < r') (ht : 0 < t) (hm : 0 < m) :
    0 < RestrictionDatum.certifiedRowFloor r' t (xTdepth bT) m :=
  certifiedRowFloor_pos_iff_trim_positive.mpr
    (trim_positivity_iff_factors_positive.mpr ⟨hr', ht, hm, xTdepth_pos bT⟩)

/-- **Aux 5, a STATEMENT POLE: at zero row density the trim deliverable is
unobtainable.**

Not merely unproved -- unobtainable: at `x = 0` **no** subset whatever meets the
conjunction "card equal to the floor" and "nonempty", for any row carrier and any
`A`.  The row supply is no obstacle there, since `2 (r' t . 0 . m) = 0 <= abs(A)`
holds for every `A` including the empty one, so it is the density clause alone
that is refuted.

This is the machine-checked form of the "why the trivial witness fails" note
carried by every trim statement in this arc, and it is about the **existential
deliverable** rather than about the floor's value.

**Not a duplicate of its sibling, and the difference is the point.**  The banked
`TranscriptLevelConstruction.trim_nonemptiness_needs_a_row_density_clause`
evaluates the *floor* to `0` at `x = 0` and negates the two clause forms there;
the statement below says that the pair "card equal to the floor" and "nonempty"
is **unsatisfiable**.  Neither implies the other by rewriting: a zero floor is
compatible with a nonempty set, and only the conjunction is refuted.

General in the row carrier, in `A`, and in both widths. -/
theorem trim_unobtainable_at_zero_density {Row : Type*} {r' t m : ℕ}
    {A : Finset Row} :
    ¬ ∃ T ⊆ A, T.card = RestrictionDatum.certifiedRowFloor r' t 0 m ∧ T.Nonempty := by
  rintro ⟨T, -, hcard, hne⟩
  have hzero : RestrictionDatum.certifiedRowFloor r' t 0 m = 0 := by
    simp [RestrictionDatum.certifiedRowFloor]
  have hpos : 0 < T.card := Finset.card_pos.mpr hne
  rw [hzero] at hcard
  omega

/-- **The two sides together, at the paper's own index tuple: the schedule
density is what makes `09:1291--1296` executable.**

At the frontier substitution `r' = kappa_v/t_ref`, `t = t_ref` (`09:1272`) over a
nonempty row carrier, and at the paper's own `x_T = 2^{-b_T}` (`08:166`):

* the trim target is positive and the trimmed set exists inside the certificate's
  rows, so the row side of the bundle is genuinely produced; while
* at `x = 0` -- the one point outside the schedule's range -- the same deliverable
  is refuted for **every** `A`, the row supply notwithstanding.

The two halves are not restatements of one another: the first is an existence
claim under a supply hypothesis, the second a refutation with no hypothesis at
all.  Together they are why the headline's density is the banked `xTdepth` and
never a free real.

*Why the trivial witness fails.*  `T = empty` has card `0` while the first
conjunct puts the demanded card at `1` or above.

General in the row carrier, in `A`, in `r`, `d_v`, `k_ref` and `b_T`; no numeral
is assigned. -/
theorem frontier_trim_needs_the_schedule_density {Row : Type*} [Fintype Row]
    {r d kref bT : ℕ} (hm : 0 < Fintype.card Row) {A : Finset Row}
    (hA : 2 * (((frontierCopies r d kref * tRef kref : ℕ) : ℝ) * xTdepth bT
        * ((Fintype.card Row : ℕ) : ℝ)) ≤ (A.card : ℝ)) :
    (0 < RestrictionDatum.certifiedRowFloor (frontierCopies r d kref) (tRef kref)
          (xTdepth bT) (Fintype.card Row)
        ∧ ∃ T ⊆ A, T.card = RestrictionDatum.certifiedRowFloor (frontierCopies r d kref)
            (tRef kref) (xTdepth bT) (Fintype.card Row) ∧ T.Nonempty)
      ∧ ¬ ∃ T ⊆ A, T.card = RestrictionDatum.certifiedRowFloor (frontierCopies r d kref)
          (tRef kref) 0 (Fintype.card Row) ∧ T.Nonempty := by
  have ht : 0 < tRef kref := by rw [tRef_eq]; exact pow_pos (by norm_num) kref
  have hfloor := certifiedRowFloor_pos_at_paper_schedule (bT := bT)
    (frontierCopies_pos r d kref) ht hm
  have hpos : 0 < ((frontierCopies r d kref * tRef kref : ℕ) : ℝ) * xTdepth bT
      * ((Fintype.card Row : ℕ) : ℝ) :=
    trim_positivity_iff_factors_positive.mpr
      ⟨frontierCopies_pos r d kref, ht, hm, xTdepth_pos bT⟩
  exact ⟨⟨hfloor, exists_trimmed_reference_rows hpos hA⟩, trim_unobtainable_at_zero_density⟩

end TrimTarget

/-! ## §3  The headline: the frontier bundle, CONSTRUCTED

`09:1268` reads "We first close any first-Bob node satisfying
`W_v >= vartheta kappa_v`".  The heavy condition is therefore a *branch
selector*, and the honest Lean form of "the construction of branch (i),
`09:1269--1276`" is a dichotomy at an arbitrary first-Bob node of the canonical
routed system: either the node is light -- the frozen
`eq:wrapper-first-bob-light` conclusion, carried here as a **case** and never
as a proved statement -- or the branch-(i) supply is produced at the paper's
own index tuple.

The three supply displays this section consumes (`09:1280--1283`,
`09:1287--1290`, `09:1291--1296`) are printed *after* `09:1276--1278` opens
branch (ii), so they sit textually in branch (ii).  They are read here -- and
proved in the banked chain -- as **branch-INDEPENDENT** facts about a frontier
node, and nothing below attributes them to branch (i)'s text.

Nothing about `W_v` is assumed.  `hbob` is read off the exposure rule
`09:1250--1252` through `firstBob_spec`; `hblocks` and `hA` are discharged by the
banked chain; `hpos` is section 1.  The single remaining binder is `hdens`, and
it is the paper's own `09:1287--1290`, GAP-EXPOSED. -/

section Bundle

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord]

/-- **Branch (i), `09:1269--1276`, at the paper's index tuple and row schedule,
fed by the branch-independent supply displays `09:1280--1296`: the bundle is
CONSTRUCTED, conditionally on the paper's own hypotheses.**

At a first-Bob node `v` of the canonical routed system
(`FrontierIndexing.canonicalSystem`, the frozen `09:1250--1259` routing), lying
on coordinate `i`'s route, with the retention `09:1233--1235` at the paper's own
`A_0 = ceil(2 x_T m_G)` (`09:1219`, `m_G` read at the row carrier per
`09:113--116`):

**either** `W_v < vartheta kappa_v` -- the light case `09:1268` sends past the
closure, whose universal form is `eq:wrapper-first-bob-light` and is **not**
proved here -- **or** the routed triple `(S,T,K)` of `09:1270--1274` exists at
`r' = kappa_v/t_ref` (`09:1272`) and `a^sharp = 1` (`09:1273`), the two
parameters that display fixes, together with `t = t_ref` (`09:319`, imported by
`09:1275`'s "The other parameters are those of `sec:wrapper-low-rungs`"), with
`S` inside the node's own census and `T` inside the certificate's own rows at
that address.

**What is derived, and what remains the paper's own hypothesis.**  `hheavy` is
gone: it is the case split, taken here rather than demanded of the caller.
`hbob` is gone: `09:1250--1252`'s exposure rule gives it through
`firstBob_spec`.  `hblocks` and `hA` were already discharged by the banked chain
(`frontierBlockCount_le_heavy_ceiling` and `certificate_rows_meet_trim_demand`).
`hpos` is discharged by `hpos_at_paper_schedule` from `hX`, which is `A:111`'s
own nonemptiness hypothesis.  What is left is `hdens`, the parent column density
of `09:1287--1290` (printed inside branch (ii), read branch-independently),
whose *projection* form has no Lean statement: it is
GAP-EXPOSED in the banked layer and is carried here as an explicit named binder,
never as a bundle field and never as an axiom.

`hk : 4 <= k_ref` is `A:117--118`'s divisibility in exponent form and
`hcap : k_ref <= r - d_v` is `09:1269`'s branch guard; both are load-bearing, and
the banked `frontierBlockCount_needs_the_kref_floor` and
`frontierCopies_needs_the_branch_guard` are their rejection probes.

*Why the trivial witness fails.*  The right disjunct demands
`S.card = r' p_t`, positive at the frozen guards
(`paper_blockCount_is_positive`), so `S = empty` fails; and `T.Nonempty` with
`T.card` at least `ceil(r' t x_T m_G)`, positive by
`certifiedRowFloor_pos_at_paper_schedule`, so `T = empty` fails.  The left
disjunct is refutable -- the banked `splitAudit_is_not_light` exhibits a routed
system where it is false -- so the disjunction is not carried by its left half.

General in the three protocol carriers, in `Coord`, in `P`, `R`, `r`, the
coordinate, the node, `k_ref`, `b_T` and `theta`. -/
theorem frontier_bundle_or_light_at_paper_schedule (P : Protocol X Y Z)
    (R : Coord → Finset X) {r bT kref : ℕ} {θ : ℝ} (i : Coord)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
    (Sc : Finset Y) (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length)
    (hX : 0 < Fintype.card X) (hY : 0 < Fintype.card Y)
    (hdens : θ ≤ ((retainedCols P Sc v.val).card : ℝ) / (Fintype.card Y : ℝ)) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
          < vartheta
            * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
      ∨ ∃ (S : Finset Coord) (T : Finset X) (b : Bool),
          S ⊆ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v ∧
            T ⊆ rowsAt P (R i) v.val ∧
            RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
              (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
              (retainedCols P Sc (v.val ++ [b])) := by
  by_cases hheavy : vartheta
      * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
    ≤ frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
  · exact Or.inr (exists_frontier_routedTriple_at_paper_schedule P R r i (hR i) v hroute Sc
      hk hcap hY ((canonicalSystem hcomp hR).firstBob_spec v hv).2.1 hheavy
      (hpos_at_paper_schedule P R _ r bT v hX) hdens)
  · exact Or.inl (TranscriptLevelJoin.light_iff_not_heavy.mpr hheavy)

end Bundle

/-! ## §4  The restriction the bundle builds, and its four `A:138--141` readouts

`WrapperDenseFrontierWiring.frontierRoutedRestriction` -- the `a^sharp = 1` datum
of `09:1270--1274`, built as an explicit full product -- and its banked wrapper
`TranscriptLevelConstruction.paperFrontierRestriction` were, until now, only ever
applied to a triple carried as a **binder**: both existing call sites in `src/`
quantify over `htr`, so nothing checked that the object they build is reachable
from the routing at all.  It is fired here at the triple section 3 constructs,
and the `A:138--141` census quantities are read back off the built object rather
than assumed of it. -/

section Restriction

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- **`09:1270--1274`'s restriction, produced from the routing.**

The same dichotomy as `frontier_bundle_or_light_at_paper_schedule`, with the
right disjunct carrying the built `RestrictionDatum` and its census:

* `A:138`'s block census reads back the frozen `p_{kappa_v} = 9 kappa_v/16` of
  `09:1280--1283` -- so the object really is indexed by the capacity the frontier
  derives, not by a free width;
* `A:139--140`'s common fibre size is exactly `abs(T)`, the trimmed row set's
  own cardinality -- which is `09:325--327`'s "the reference restriction is a
  full product, so its balancedness error is exactly zero" read at the routing's
  own rows;
* that fibre is **positive**, by `certifiedRowFloor_pos_at_paper_schedule` at the
  paper's own `x_T`, so `A:139--140` is not vacuously met;
* `A:141`'s density is the denser Bob child's retained column density.

`S.Nonempty`, which `A:139--140`'s readout needs, is **derived** from
`paper_blockCount_is_positive` rather than assumed: the frozen count is positive
at the guards, so the selection cannot be empty.

The two additional binders `0 < theta <= 1` are `A:128`'s `h in (0,1]`, carried
by the banked constructor and by `RestrictionDatum` itself.

*Why the trivial witness fails.*  Inherited from section 3, and sharpened: the
datum's own `selCard` is pinned to the frozen positive `p_{kappa_v}`, and its
common fibre is pinned to a positive cardinality, so no degenerate rectangle
satisfies the right disjunct.

General in the three protocol carriers, in `Coord`, in `P`, `R`, `r`, the
coordinate, the node, `k_ref`, `b_T` and `theta`. -/
theorem frontier_restriction_or_light_at_paper_schedule (P : Protocol X Y Z)
    (R : Coord → Finset X) {r bT kref : ℕ} {θ : ℝ} (i : Coord)
    (hcomp : CompletedNoBob P r)
    (hR : ∀ j, refRowFloor (initialRefRows (xTdepth bT) (Fintype.card X)) r ≤ (R j).card)
    (v : FrontierNode P R (initialRefRows (xTdepth bT) (Fintype.card X)) r)
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hroute : v.val ∈ coordRoutes P R (initialRefRows (xTdepth bT) (Fintype.card X)) r i)
    (Sc : Finset Y) (hk : 4 ≤ kref) (hcap : kref ≤ r - v.val.length)
    (hX : 0 < Fintype.card X) (hY : 0 < Fintype.card Y)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hdens : θ ≤ ((retainedCols P Sc v.val).card : ℝ) / (Fintype.card Y : ℝ)) :
    frontierWeight P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v
          < vartheta
            * ((kappaAt P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v : ℕ) : ℝ)
      ∨ ∃ (S : Finset Coord) (T : Finset X) (b : Bool)
          (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
            (frontierCopies r v.val.length kref) (tRef kref) 1 (xTdepth bT) θ S T
            (retainedCols P Sc (v.val ++ [b]))),
          S ⊆ representedCoords P R (initialRefRows (xTdepth bT) (Fintype.card X)) r v ∧
            T ⊆ rowsAt P (R i) v.val ∧
            (paperFrontierRestriction htr hθ0 hθ1).selCard
                = RestrictionDatum.certifiedPt (kappaFrontier r v.val.length) ∧
            (paperFrontierRestriction htr hθ0 hθ1).rowsPerBlock = T.card ∧
            0 < T.card ∧
            (paperFrontierRestriction htr hθ0 hθ1).colDens
                = ((retainedCols P Sc (v.val ++ [b])).card : ℝ) / (Fintype.card Y : ℝ) := by
  rcases frontier_bundle_or_light_at_paper_schedule P R i hcomp hR v hv hroute Sc hk hcap
      hX hY hdens with hlight | ⟨S, T, b, hSsub, hTsub, htr⟩
  · exact Or.inl hlight
  refine Or.inr ⟨S, T, b, htr, hSsub, hTsub, ?_, ?_, ?_, ?_⟩
  · exact paperFrontierRestriction_selCard htr hθ0 hθ1 hk hcap
  · have hS : S.Nonempty := by
      refine Finset.card_pos.mp ?_
      rw [routedTriple_blockCount htr]
      exact paper_blockCount_is_positive hk hcap
    rw [paperFrontierRestriction, frontierRoutedRestriction]
    exact routedRestriction_rowsPerBlock htr hθ0 hθ1 (le_refl 1) hS
  · have ht : 0 < tRef kref := by rw [tRef_eq]; exact pow_pos (by norm_num) kref
    have hfloor := certifiedRowFloor_pos_at_paper_schedule (bT := bT)
      (frontierCopies_pos r v.val.length kref) ht hX
    exact Nat.lt_of_lt_of_le hfloor htr.2.2.1
  · rw [paperFrontierRestriction, frontierRoutedRestriction]
    exact routedRestriction_colDens htr hθ0 hθ1 (le_refl 1)

end Restriction

/-! ## §5  A smoke probe at the banked split instance

**NON-FIDELITY / BEYOND-PAPER.**  Everything in this section audits *our*
encoding at a point the frozen paper never visits, and it claims no legality.
Every disclosure the banked `TranscriptLevelSuccessors.splitAudit` carries is
inherited verbatim:

* `k_ref = 4` satisfies every gate carried in `src/` (`A:117--118`'s
  `16 | t_ref`), but `A:117` with `A:26` forces `t_ref >= t_cert = 2^{2^20}`, so
  the paper's own `k_ref` is astronomically larger.  This is the clause that
  makes the instance an audit rather than the paper's instance;
* the alphabets `Fin 32` and `Bool`, the Alice predicate, the coordinate count
  `18` and the wrapper exponent `r = 5` are **ours**; the frozen text fixes none
  of them.  The depth `b_T = 9` is a weaker case and is stated separately for
  that reason: `06:241` fixes `b_T = 2^{j_{49}(k_T)}` as a **function** of the
  schedule (through `k_T = log_2(s/4)`, `06:239`), so `b_T` is DEFINED -- as the
  header table records -- and what this audit chooses is a point the schedule is
  never instantiated at.  The numeral is ours; the quantity is not free;
* the column parameter `theta = rhoSmall = 18/25` is **ours at this node**, and
  its pedigree is disclosed here rather than claimed.  `09:434--436` reads "For
  the small-capacity calls put" and then prints `rho = 2y^2 = 18/25` at
  `09:436` -- "the small-capacity calls" being branch (ii)'s
  `2 <= kappa_v < t_ref` -- whereas this probe sits at `kappa_v = t_ref = 16`,
  the boundary `09:1269` assigns to **branch (i)**, whose column parameter is
  `h = theta` at `09:322` (imported by `09:1275`) and is left open there.  So
  `rhoSmall` is a legal `A:128` value **borrowed from branch (ii)**, not a value
  the frozen text fixes at this node; `probe_rhoSmall_pos` and
  `probe_rhoSmall_le_one` below claim exactly the `A:128` legality `0 < h <= 1`
  and nothing more.

What is **not** ours, and is evaluated rather than assigned: `x_T = 2^{-b_T}`
(`08:166`, the banked `splitAuditXT`), `A_0 = ceil(2 x_T m_G)` (`09:1219`, the
banked `splitAuditA0`), `kappa_v = 2^{r-d_v} = 16` and `W_v = 9` (`09:1255`,
`09:1257`).

The probe establishes exactly one thing: that the constructor of section 4 --
and hence section 3's, which it consumes -- is usable end to end, fired at a
routed system with the light disjunct eliminated by the banked
`splitAudit_is_not_light`.  There is deliberately **no** separate section-3
live-fire declaration: its proposition would be the banked
`TranscriptLevelSuccessors.splitAudit_yields_paper_indexed_triple` symbol for
symbol, which is the header's rename-not-dedup boundary; that lemma is consumed
by pin wherever the bare triple is wanted.  **This probe does not discharge the
canonical-inhabitation obligation**, which stays REGISTERED and DEFERRED per the
header. -/

section SmokeProbe

/-- **`A:120` EVALUATED at the probe node.**  `p_{kappa_v} = 9 . 16/16 = 9` at
`kappa_v = 2^{5-1}`, so the census the built restriction reads back is the frozen
count and not a symbol.  A numeral evaluation inside the BEYOND-PAPER section.

Routed entirely through banked names: `09:1255`'s capacity is evaluated by the
banked `TranscriptLevelConstruction.kappaFrontier_eq`, and `A:120`'s count at
that capacity is the banked `RestrictionDatum.certifiedPt_sixteen`.  Neither
`certifiedPt` nor `kappaFrontier` nor `stoppingCapacity` is unfolded here; the
only arithmetic performed locally is `2 ^ (5 - 1) = 16`. -/
theorem probe_certifiedPt_kappa :
    RestrictionDatum.certifiedPt (kappaFrontier 5 1) = 9 := by
  have hκ : kappaFrontier 5 1 = 16 := by rw [kappaFrontier_eq]; norm_num
  rw [hκ]
  exact RestrictionDatum.certifiedPt_sixteen

/-- **`09:436`'s `rho = 2y^2` is a legal `A:128` column parameter, left half.**
Consumed by the restriction probe below, where `A:128`'s `h in (0,1]` is what the
built datum demands.  A readout of the banked `rhoSmall`, not a chosen value. -/
theorem probe_rhoSmall_pos : (0 : ℝ) < rhoSmall := by norm_num [rhoSmall]

/-- **`09:436`'s `rho = 2y^2` is a legal `A:128` column parameter, right half.** -/
theorem probe_rhoSmall_le_one : rhoSmall ≤ 1 := by norm_num [rhoSmall]

/-- **The constructor of section 4, fired: the `09:1270--1274` restriction is
built at the banked split instance, and its census reads back `9`.**

The restriction dichotomy at `splitAuditNode`, light disjunct eliminated as
above.  What survives is an actual `RestrictionDatum` at
`r' = kappa_v/t_ref = 1`, `t = t_ref = 16`, `a^sharp = 1`, whose `A:138` census
is the frozen `p_{kappa_v} = 9` of `09:1280--1283` (`probe_certifiedPt_kappa`),
whose `A:139--140` common fibre is the trimmed row set itself, and whose fibre is
positive.  This is the first place in `src/` where
`WrapperDenseFrontierWiring.frontierRoutedRestriction` is applied to an object
produced by the routing rather than merely typed.

**NON-FIDELITY**, per the section label. -/
theorem splitAudit_frontier_restriction_reads_back_the_frozen_census :
    ∃ (S : Finset (Fin 18)) (T : Finset (Fin 32)) (b : Bool)
      (htr : RoutedTriple (Blk := Fin 18) (Row := Fin 32) (Col := Bool)
        (frontierCopies 5 splitAuditNode.val.length 4) (tRef 4) 1 splitAuditXT rhoSmall S T
        (retainedCols splitAudit (Finset.univ : Finset Bool)
          (splitAuditNode.val ++ [b]))),
      (paperFrontierRestriction htr probe_rhoSmall_pos probe_rhoSmall_le_one).selCard = 9
        ∧ (paperFrontierRestriction htr probe_rhoSmall_pos
            probe_rhoSmall_le_one).rowsPerBlock = T.card
        ∧ 0 < T.card := by
  obtain ⟨-, hcap, -, hY, -, -, -, hdens⟩ :=
    heavy_bundle_jointly_satisfiable_at_positive_depth
  rcases frontier_restriction_or_light_at_paper_schedule splitAudit splitAuditRows
      (bT := 9) (kref := 4) (0 : Fin 18) TranscriptLevelJoin.splitAudit_completedNoBob
      splitAudit_hR splitAuditNode TranscriptLevelJoin.splitAudit_firstBob_true
      (splitAudit_node_mem_coordRoutes 0) Finset.univ (by norm_num) hcap
      (by norm_num) hY probe_rhoSmall_pos probe_rhoSmall_le_one hdens
    with hlight | ⟨S, T, b, htr, -, -, hsel, hrows, hcard, -⟩
  · exact absurd hlight TranscriptLevelJoin.splitAudit_is_not_light
  · exact ⟨S, T, b, htr, hsel.trans probe_certifiedPt_kappa, hrows, hcard⟩

end SmokeProbe

end EthInapproximability.ParameterizedNP.FrontierBundleConstruction
