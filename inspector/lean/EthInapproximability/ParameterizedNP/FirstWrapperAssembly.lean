import EthInapproximability.ParameterizedNP.LargeCapacityBranch

/-!
# Parameterized NP route: the first-wrapper assembly of `eq:wrapper-first-bob-light`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`)
  together with `sections/A-certified-stopping.tex`
  (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`).
  Both hashes were recomputed first-hand this tranche.
* **The exact frozen lines traced here**, in print order:
  * `09:1217--1221`, the row schedule `A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0`.
  * `09:1238--1239`, "At remaining selector capacity `2^k`, a certificate
    consists of at least `A_k` reference rows in one outer coordinate."
  * `09:1268--1269`, the shared heavy condition and `vartheta = 9/16`.
  * `09:1269--1276`, the large-capacity branch (banked, consumed by pin).
  * `09:1277--1306`, the small-capacity branch (banked, consumed by pin), of
    which `09:1291--1296` ("each selected certificate has at least
    `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows, so trim it to
    the row density `kappa_v x_T`") is the row bookkeeping §2 uses.
  * **`09:1306--1313`, this tranche's target `(T1)`**: the join sentence "Its
    lower bound is one more bit than the remaining child budget in the alleged
    protocol.  Therefore" and the displayed conclusion
    `eq:wrapper-first-bob-light`, `W_v < vartheta kappa_v` at every first-Bob
    node `v`.
  * **`A:138--141`, this tranche's target `(T2)`**: "every restriction of
    `Mhat` with exactly `r' p_t` represented outer blocks, **at least
    `ceil(r' t x m)` rows in each represented block**, and column density at
    least `h 2^{-a^sharp}`, has communication complexity at least `H + log_2(r't)`".
    The middle clause is `LARGE-CAPACITY-BRANCH-001` GAP-EXPOSED item **(18)**.
* **Cross-anchors opened first-hand this tranche:** `09:105` (`q = 2^r`),
  `09:327` (`q/4 >= t_ref`, exponent gate `k + 2 <= r`), `09:315--324` (the
  `y_* = 3/5` substitution of the certified-scale stopping lemma), `09:1287--1296`
  (the selection/projection/trim step that stays inside `hselect`),
  `A:109--146` (`thm:certified-localized-extension`), `A:148--162`
  (`lem:certified-row-ladder`), and `06:558--572` (`eq:tref-search`,
  `t_ref = 2^{k_ref}`) in `sections/06-parameter-schedule.tex`
  (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`).

## Reader counterpart: NONE claimable, re-verified first-hand this round

`routes/parameterized-np/reader-facing/sections/` was searched again for
`vartheta`, `9/16`, `first Bob`, `first-Bob`, `row floor`, `represented block`,
`Localized Extension` and `localized extension`; every hit was opened.  Three
near misses, all declined:

* `02-preliminaries.tex:512--526`, `cor:paper-localized-extension`, is the
  **uncertified** Localized Extension -- no `t >= t_cert`, no `h_t`, no
  `eq:certified-E1`/`E2`.  It is the closest reader sentence to §2 because it
  *does* print an equipartition clause (`ceil(r' x_seed m)`-equipartitioned,
  `02-preliminaries.tex:518--522`), but that clause governs the reader's own
  uncertified endpoint, is stated over `x_seed` rather than the wrapper's
  `x_T`, and names no `A_k`; and the corollary as a whole is already declined
  for the certified endpoint in the banked `WRAPPER-LOW-RUNGS-001` and
  `LARGE-CAPACITY-BRANCH-001` rows.  Citing it here would be a false counterpart.
* `A-stage4-details.tex:390--392` ("Its small-capacity and final-node closures
  use the certified row ladder ...; they do not require a new odd-copy theorem")
  is unnumbered prose and is already assigned to `TERMINAL-TWO-STREAM-001`.
* `02-preliminaries.tex:301` ("not stable under the first Bob bit") is prose
  about Stage-2 stability, not about a frontier node.
* `A-stage4-details.tex:363` ("Localized Extension applied to
  `eq:paper-reference-profile` yields ...") -- found by the repair round's own
  re-sweep, which the parked generation's list omitted.  Declined on two
  independent grounds: it is unnumbered prose *inside a proof body*, and it is
  the **low-rungs** application at rung `j` (hard-seed fraction
  `9(q/2^j)/16`, output `C + r_q - 1 - j`), not the first-Bob frontier and not
  the per-block row floor.  It belongs to the banked `WRAPPER-LOW-RUNGS-001`
  neighbourhood, and citing prose as a statement is barred in any case.

The reader artifact contains no `vartheta`, no `eq:wrapper-first-bob-light`, no
first-Bob frontier weight, no capacity dichotomy, and no `A_k` row schedule.
No reader item is claimed, and no reader item is assigned twice.

## What this tranche does

### `(T1)` The assembly of `09:1306--1313` (§1)

`firstBobLight_assembled` is the join.  It consumes the banked
`LargeCapacityBranch.canonical_firstBobLight_largeCapacity`
(`LargeCapacityBranch.lean`, SHA-256
`0EEE471B93C6871199BC4DE55550A391ACA062D212018DBC1011A93466E629F5`) by pin and
**discharges that theorem's `hsmall` binder** against the banked small-capacity
machinery pinned in `SplitFirstBobInstance.lean` (SHA-256
`A84D9ACA58C3E7E671485D78EDF13A64362AFBBF4F20B2EF86915929C0E5297C`) -- namely
`DenseWrapperFrontier.capacity_row_density_legal` (`09:1302--1304`) and
`DenseWrapperFrontier.smallCapacity_child_bound` (`09:1296--1306`), which are
exactly the two lemmas `SplitFirstBobInstance.canonical_firstBobLight_smallCapacity`
itself uses.  Nothing is re-proved.

**The surviving binder list, recorded precisely.**  After the join,
`firstBobLight_assembled` carries exactly these hypotheses, and no others:

1. **Construction inputs** (banked, not assumptions about the mathematics):
   `hcomp : CompletedNoBob P r` and `hR` (the `A_r = q A_0` retention), which
   *are* `FrontierIndexing.canonicalSystem`'s own two inputs; and `hv`, the
   first-Bob flag.
2. **Frozen schedule guards:** `hC : 3 <= C` (`09:240`), `hk : 4 <= k`
   (`A:117--118` in exponent form), `hq4 : k + 2 <= r` (`09:327`),
   `hgate : 2^r x_T <= 4/25025` (`eq:wrapper-low-simple-gate`, `09:305`).
3. **Parameter guards:** `hxT0`, `hxT1`, `hθ0`, `hθ1`, `hy0`, `hy1`,
   `hGrow`, `hGcol` (the carriers of `G` nonempty).
4. **Budget:** `hbudget : B + (d_v + 1) <= C + r - 1`, the alleged
   `(C+r-1)`-bit protocol's remaining budget below the selected Bob child
   (`09:1306--1308`).
5. **Two base certificates at one `G`, deliberately *not* identified:**
   `hbase : C - 1 <= LambdaGE Gmat 1 x_T (3/5)` is `lem:wrapper-reference`
   (`09:151--162`) read at the certified-scale stopping lemma's **fixed**
   `y_* = 3/5` (`09:314--315`), which is what the *large* branch needs; and
   `hbaseY : C - 1 <= LambdaGE Gmat 1 x_T y` is the same frozen display read at
   the wrapper's own `y`, which is what `09:1299`'s `z = y` ladder call needs.
   `09:1290`'s parent density `rho = 2y^2` is stated in that same `y`, so the
   two symbols are kept apart; **this module does not assert `y = 3/5`.**
6. **Schedule-owned endpoint inputs, left named:** `htcert` (`A:117`),
   `hE1`, `hE2` (`eq:certified-E1`, `eq:certified-E2`), `hcol` (`A:141` at
   `a^sharp = 1`), all discharged by `eq:tref-search` in `06`, not here.
7. **The two genuinely unproved steps, both named hypotheses and never axioms:**
   `hLocEx`, the certified-scale reference stopping lemma
   `thm:certified-localized-extension` (`A:109--146`), where `EXPANDER-001`
   would enter; and `hselect`, the selection/projection step `09:1287--1296`
   (GAP-EXPOSED item 15, owned by `SPLIT-FIRST-BOB-INSTANCE-001`, untouched by
   this tranche).

### `(T2)` The `hLocEx` narrowing, begun (§2)

GAP-EXPOSED item **(18)** records that `hLocEx` carries `A:138`'s block count
and `A:141`'s column density but **not** `A:139--140`'s per-block row floor, so
the assumed implication fires without that clause being checked.

§2 begins the narrowing by *modelling* the clause rather than carrying the
sharpened note.  `perBlockRowFloor_le_refRowFloor` proves, generally, that the
wrapper's own row schedule meets it: `ceil(kappa_v x_T m_G) <= A_{ell_v}` at
`kappa_v = 2^{ell_v}`, `A_0 = ceil(2 x_T m_G)`.  The narrowed endpoint
`largeCapacityExtension_rowFloor` then carries `A:139--140` as an explicit
antecedent of `hLocEx`, in `A:138--141` print order, and **discharges** it from
one new named binder `hrows` -- the routing's own row bookkeeping of
`09:1238--1239` at the node's capacity.  `canonical_firstBobLight_largeCapacity_rowFloor`
and `firstBobLight_assembled_rowFloor` thread it to the frontier and to the join.

**`m` is DEFINED, and the three narrowed declarations pin it.**  `A:111` reads
"Let `M` be a nonempty Boolean matrix with `m` rows", so `m` is not a parameter
of the endpoint but the row count of the matrix it is invoked on; `09:1270`
invokes it **on `G`** and `09:1291--1294` writes that row count as `m_G` in the
very display the floor is discharged from.  Hence `m = m_G = |Rows(G)|`, which in
this development is `Fintype.card Rw` for `Gmat : Rw -> Cl -> Bool`, and the
three `*_rowFloor` declarations form the floor at that value rather than at a
free natural.  Together with `A:111`'s own nonemptiness -- carried here as
`hGne`/`hGrow : 1 <= Fintype.card Rw` -- this makes `A:139--140` a demand that
holds at **every** legal instantiation.  The general schedule lemmas of §2
(`perBlockRowFloor_le_refRowFloor`, `_mono`, `_at_zero`, `_at_firstBob`) stay
universally quantified in `m_G`: they are properties of the row schedule *as a
schedule*, not encodings of `A:139--140`, and their generality is what supplies
the pinned instance.

**What is and is not gained, stated exactly.**  The narrowed `hLocEx` is a
*weaker* demand on the unproved endpoint (one more antecedent to be granted),
bought at the price of one new binder `hrows` naming the routing invariant.  So
the two statements are not comparable by mere hypothesis strength; what improves
is **fidelity**: `A:139--140` is now present in the interface and supplied from
the frozen row schedule, instead of being silently absorbed.  Item (18) is
therefore **advanced, not discharged** -- the banked `largeCapacityExtension`
and `canonical_firstBobLight_largeCapacity` are untouched and still carry the
un-narrowed shape, and this module supersedes rather than replaces them.
`perBlockRowFloor_is_not_free` is the rejection probe showing the new antecedent
is a real demand and not automatic.

### `(T3)` `hselect` -- NOT attempted

Per the recorded scope decision the deferred items are not worked.  `hselect`
(GAP-EXPOSED item 15, owned by `SPLIT-FIRST-BOB-INSTANCE-001`, `09:1287--1296`)
stays exactly the binder the banked
`canonical_firstBobLight_smallCapacity` carries: the column projection at a
protocol node is still unmodelled, so nothing identifies the ladder's certified
restriction inside the selected Bob child.  No antecedent is added to it here.
Adding a *provable* antecedent would have been a vacuous narrowing (an implication
is unchanged by an antecedent that is a theorem), and that is deliberately not
done.

## What is *not* claimed

* Neither `firstBobLight_assembled` nor `firstBobLight_assembled_rowFloor`
  proves `eq:wrapper-first-bob-light`.  Both **conclude** it under the named
  binders enumerated above; `hLocEx` and `hselect` remain unproved.
* `thm:certified-localized-extension` is not proved and is not an axiom.
  `EXPANDER-001` has no Lean declaration by design and appears in no hypothesis
  of this module.
* `hDenseRung` is neither discharged nor fed; `eq:wrapper-u-dense` is asserted
  nowhere; `sec:wrapper-mass-redistribution` (`09:1512--1781`) stays DEFERRED in
  full under `WRAPPER-MASS-REDISTRIBUTION-001` and is the **next** segment, whose
  opening cut is `09:1512`.
* No route completion is claimed.

## Canonical inhabitation

This module introduces **no `structure`, no `inductive` and no `def`**, so it
opens no new canonical-inhabitation obligation.  The frontier apparatus is the
banked `FrontierIndexing.canonicalSystem` with its existing parametric legality
statement `FrontierIndexing.canonicalSystem_legal_instance`; the row schedule is
the banked `DenseWrapperFrontier.refRowFloor`/`initialRefRows`.

The paper's own instance of the assembled join is the full wrapper argument at
the schedule's parameters, inside the `(C+r-1)`-bit contradiction frame of
`09:1188--1313`.  It is instantiated at no numeral, and `eq:tref-search` forces
`k_ref >= 2^19`, so no legal instance is computable by `decide`; the banked
`LargeCapacityBranch.largeBranch_never_reaches_the_audit_instance` records
first-hand that the large branch cannot even be reached at the `r = 2` audit
instances.  The canonical-inhabitation obligation for the join is therefore
**inherited from `LARGE-CAPACITY-BRANCH-001`, still ledger-registered and
deferred**, discharged only when the schedule-level construction lands and never
by a probe.  The two interim consistency declarations in §4 carry the mandatory
**BEYOND-PAPER AUDIT** label, claim no legality for their numerals, and are
strictly weaker evidence than the paper's application point.

## Repair record (round r1 of this module)

This module was **parked** at its first judged round on a REVISE covering three
of its twelve declarations; the parked bytes are preserved on
`wip/cc-t4l-first-wrapper-assembly` (SHA-256
`DA856699D1ACB9538B21A35746754A2930587D68D1CF94980791CD996F3CDF41`, 771 lines).
This generation restores those bytes and applies the prescribed repairs, with
one disclosed exception: a fifth reader near-miss bullet (`A-stage4-details.tex:363`)
was added from this round's own re-sweep, which the parked generation's list had
omitted.  It is a further *declination*, not a claim, and is itemised in the
reader-counterpart section above.  Otherwise no other change:

1. **The missing-hypothesis defect (three declarations).**  `mG : ℕ` was an
   implicit binder constrained by nothing in `largeCapacityExtension_rowFloor`,
   `canonical_firstBobLight_largeCapacity_rowFloor` and
   `firstBobLight_assembled_rowFloor`, so the new `A:139--140` clause was
   evacuable at the legal, type-correct instantiation `m_G := 0` -- at which the
   whole narrowing collapsed to the banked theorem plus a no-op antecedent.
   `mG` is removed from all three binder lists and every occurrence of the floor
   is now formed at the DEFINED value `Fintype.card Rw` (`A:111` under
   `09:1270`'s `M = G`).  **Proof terms are unaffected**: the discharge is still
   `perBlockRowFloor_le_refRowFloor` composed with `hrows`, now at the pinned
   row count.
2. **The audit instance's `m_G`.**  `assembled_arithmetic_binders_consistent`
   asserted the numeral `1`.  It now names a carrier `Rw := Fin 1` and writes
   `Fintype.card (Fin 1)`, so the value is *evaluated* from the definitional
   chain instead of assigned -- the same DEFINED-vs-FREE discipline one layer
   down.  The proof term is unchanged (§2's lemma is general in `m_G`).
3. **Record repairs, all citation-level.**  The `A-stage4-details.tex` sentence
   spans `390--392`, not `389--391`; `perBlockRowFloor_mono`'s attribution is
   split, since `09:1239--1244` halves the **row count** while the capacity
   halving is `09:1255`; GAP-EXPOSED item 15 now names its owning row
   `SPLIT-FIRST-BOB-INSTANCE-001`; and the BEYOND-PAPER list of
   `assembled_arithmetic_binders_consistent` now discloses `x_T`, DEFINED at
   `06:243` and pinned here at the BEYOND-PAPER value `2^{-22}`.
4. **Registered, not repaired.**  `colDens` is a free real constrained by no
   other binder (`hcol : theta/2^1 <= colDens` is met by `colDens := theta` and
   pins no real column density).  That is the **banked**
   `LARGE-CAPACITY-BRANCH-001` interface, passed through here byte-identically;
   it is the same species as (1) and is registered on that row's GAP-EXPOSED
   list rather than repaired inside this module, which would mutate a banked pin
   outside its own tranche.  **`rowsPerBlock` is the same species again, and is
   registered here as GAP-EXPOSED item (21)** on this module's own row: it is a
   free `ℕ` occurring only in `hrows` and in the new `A:139--140` antecedent, so
   that antecedent is discharged unconditionally from `hrows` at every
   instantiation and constrains nothing at the point of use -- at
   `rowsPerBlock := refRowFloor (initialRefRows xT (Fintype.card Rw)) ell` it is
   literally a theorem.  It is **not** repairable inside this tranche: nothing in
   the development models the restriction fed to
   `thm:certified-localized-extension`, and that absence *is* the remaining
   content of GAP-EXPOSED item (18), which this module advances but does not
   discharge.

The nine declarations judged CLEAR keep their statements and proof terms
unchanged; only the two citation-level docstring repairs above and the audit
instance's carrier evaluation touch them.  No declaration is added or removed,
`hselect` is untouched, and no new mathematics is introduced.

## Verify-seat record-only corrections (`cc-t4l-r1`, 10 August 2026)

Applied by the verify seat after all twelve per-declaration verdicts came back
CLEAR.  **No statement, hypothesis, conclusion, binder or proof term is touched
by any of them**; they are citation and prose repairs plus one ledger
registration, and the module's Lean content is byte-unchanged in every
declaration body.

* **A regression introduced by round r1 is reverted.**  The reader corollary
  `cor:paper-localized-extension` ends at `02-preliminaries.tex:526`
  (`\end{corollary}`); `527` is blank.  The parked generation's `512--526` was
  correct, and r1's prescription to change it to `527` was itself off by one.
  Re-read first-hand at the frozen bytes and restored to `512--526`.
* `perBlockRowFloor_mono`'s row-halving sentence spans `09:1239--1244`, not
  `09:1240--1243` (the sentence opens at the end of `1239` and closes at the
  start of `1244`); corrected in both the docstring and the repair record.
* The `A:138--141` "print order" claim on `largeCapacityExtension_rowFloor` is
  qualified: the realised antecedent order is `A:141`, `A:138`, `A:139--140`,
  since the column-density clause is inherited from the banked list.
* `firstBobLight_assembled_rowFloor`'s "can never be evacuated" is scoped to the
  `m := 0` route and cross-referenced to item (21).
* The "no other change" wording now carries its one-clause exception.
* This module had **no ledger row at all**; the row `FIRST-WRAPPER-ASSEMBLY-001`
  is added in the same change, carrying item (21).

## Proof status

Every declaration is either a **general** property of the frozen row schedule,
of the banked frontier readouts, or of the endpoint interface; or a **statement
pole** / **BEYOND-PAPER AUDIT** consistency check at self-chosen numerals,
carrying that label in its own docstring.  No mathematics is added: every
inequality of the paper used here is consumed from a banked, already-proved
declaration by pin.
-/

namespace EthInapproximability.ParameterizedNP.FirstWrapperAssembly

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.LargeCapacityBranch

/-! ## §1  `(T1)` The assembly of `09:1306--1313`

"Its lower bound is one more bit than the remaining child budget in the alleged
protocol.  Therefore `W_v < vartheta kappa_v` at every first-Bob node `v`."

The banked `canonical_firstBobLight_largeCapacity` already discharges the large
branch and leaves the small branch as the binder `hsmall`.  This section
discharges `hsmall` too, from the banked small-capacity machinery, so that the
frozen conclusion is reached at **every** first-Bob node of the canonical routed
system with no branch left conditional. -/

section Assembly

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`eq:wrapper-first-bob-light` (`09:1306--1313`), assembled across both
capacity branches.**

At a first-Bob node `v` of `FrontierIndexing.canonicalSystem`, the frozen
conclusion `W_v < vartheta kappa_v` holds.  Both branches of the closure of
`09:1268--1306` are discharged rather than assumed:

* the **large** branch `09:1269--1276` (`kappa_v >= t_ref`, exponent form
  `k <= ell_v`) is the banked `canonical_firstBobLight_largeCapacity`, consumed
  by pin;
* the **small** branch `09:1277--1306` (`kappa_v < t_ref`, exponent form
  `ell_v < k`) is discharged here, exactly as the banked
  `canonical_firstBobLight_smallCapacity` discharges it: `capacity_row_density_legal`
  is `09:1302--1304` ("`kappa_v x_T <= t_ref x_T <= 1` verifies legality"), and
  `smallCapacity_child_bound` is the `lem:certified-row-ladder` call of
  `09:1296--1306` at `M = G`, `H = C-1`, `x = x_T`, `z = y`, `ell = ell_v`, with
  `hbaseY` the second clause of `lem:wrapper-reference` and `C >= 3` supplying
  `H >= 2`.

The strict branch guard `ell_v < k` supplied by the banked branch-wise dichotomy
is weakened to `ell_v <= k` before `capacity_row_density_legal` is called, which
is legitimate in that direction and is how the banked small-capacity theorem
already reads it; the boundary `kappa_v = t_ref` is handled by the **large**
branch, exactly as `09:1269` (non-strict) against `09:1277` (strict) assigns it.

**Two base certificates at one `G`, kept apart.**  `hbase` is
`lem:wrapper-reference` at the stopping lemma's fixed `y_* = 3/5` (`09:314--315`),
`hbaseY` the same display at the wrapper's own `y`, in which `09:1290`'s
`rho = 2y^2` and `09:1299`'s `z = y` are stated.  Nothing here asserts `y = 3/5`.

**Still conditional, and named:** `hLocEx` (`thm:certified-localized-extension`,
`A:109--146`, where `EXPANDER-001` would enter) and `hselect` (`09:1287--1296`,
GAP-EXPOSED item 15, owned by `SPLIT-FIRST-BOB-INSTANCE-001`).  Both are
hypotheses, never axioms.  The full surviving
binder list is enumerated in the module header.

General in the source carriers, in `P`, `Coord`, `R`, `A_0`, `r`, `C`, `k`, the
residual budget `B` and the real parameters `x_T`, `theta`, `colDens`, `y`. -/
theorem firstBobLight_assembled {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B k tcert : ℕ} {xT θ colDens y : ℝ}
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hGrow : 1 ≤ Fintype.card Rw) (hGcol : 1 ≤ Fintype.card Cl)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (hbaseY : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) →
      (C - 1) + (r - v.val.length) ≤ B)
    (hselect : smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
        ≤ (representedCoords P R A0 r v).card →
        LambdaGE Gmat (2 ^ (r - v.val.length - 1) + 1)
          ((2 : ℝ) ^ (r - v.val.length) * xT) (y ^ 2) ≤ B) :
    frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  refine canonical_firstBobLight_largeCapacity Gmat hcomp hR hv hC hk hq4 hxT0 hxT1 hθ0 hθ1
    hGrow hgate hbase htcert hE1 hE2 hcol hbudget hLocEx ?_
  intro hbranch hcover
  have hlt : v.val.length < r := ((canonicalSystem hcomp hR).firstBob_spec v hv).2.2
  have hlegal : ((2 : ℝ) ^ (r - v.val.length)) * xT ≤ 1 :=
    capacity_row_density_legal (le_of_lt hxT0) (le_of_lt hbranch) hq4 hgate
  have hladder := smallCapacity_child_bound Gmat (ℓ := r - v.val.length) hGrow hGcol hC hxT0
    hy0 hy1 hbaseY (by omega) hlegal
  exact le_trans hladder (hselect hcover)

end Assembly

/-! ## §2  `(T2)` The `A:139--140` per-block row floor, and the narrowed `hLocEx`

`A:138--141` demands three things of the restriction fed to
`thm:certified-localized-extension`:

1. exactly `r' p_t` represented outer blocks (`A:138--139`);
2. **at least `ceil(r' t x m)` rows in each represented block** (`A:139--140`);
3. column density at least `h 2^{-a^sharp}` (`A:141`).

The banked `largeCapacityExtension` carries (1) and (3) and leaves (2) inside
`hLocEx`'s restriction data -- GAP-EXPOSED item (18).  At the `09:1272`
substitution `r' t = kappa_v = 2^{ell_v}`, `x = x_T`, `m = m_G`, clause (2) reads
`ceil(kappa_v x_T m_G)`, and the wrapper's own row schedule already meets it:
`09:1238--1239` gives every certificate at least `A_{ell_v}` rows, and
`09:1219--1221` makes `A_{ell_v} = 2^{ell_v} ceil(2 x_T m_G)`. -/

section RowFloor

/-- **`A:139--140` is met by the frozen row schedule of `09:1219--1221`.**

`ceil(kappa x_T m_G) <= A_ell` at `kappa = 2^ell`, `A_0 = ceil(2 x_T m_G)`,
`A_ell = 2^ell A_0`.

This is the per-block row floor `A:139--140` demands, read at the `09:1272`
substitution `r' t = kappa_v`, `x = x_T`, `m = m_G`.  The proof is the banked
`refRowFloor_meets_row_demand` (`09:1291--1296`, "`A_{ell_v} = kappa_v A_0 >=
2 kappa_v x_T m_G`") plus one ceiling step: the schedule gives **twice** the
demanded real quantity, and a natural number bounding a nonnegative real bounds
its ceiling.  The factor two is exactly the slack `09:1219`'s `A_0 = ceil(2 x_T
m_G)` was built to carry, so no new arithmetic is introduced.

General in `ell`, `m_G` and `x_T >= 0`. -/
theorem perBlockRowFloor_le_refRowFloor (ℓ mG : ℕ) {xT : ℝ} (hxT0 : 0 ≤ xT) :
    ⌈(2 : ℝ) ^ ℓ * xT * (mG : ℝ)⌉₊ ≤ refRowFloor (initialRefRows xT mG) ℓ := by
  refine Nat.ceil_le.2 ?_
  have hdemand := refRowFloor_meets_row_demand ℓ mG xT
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ ℓ * xT * (mG : ℝ) := by positivity
  linarith

/-- **Aux A1 (monotonicity).**  The per-block row floor of `A:139--140` grows
with the capacity exponent, which is what lets the frozen routing rule restore
the invariant one level down.

**Attribution, split (the two halvings are different objects).**  The rule of
`09:1239--1244` -- "At an Alice query, route it to a child containing at least
`ceil(A_k/2) >= A_{k-1}` of those rows" (the sentence opens at the end of
`1239` and closes at the start of `1244`; the display itself is `1241--1243`)
-- halves the **row count**, not the capacity.  The
capacity halving is the depth relation `kappa_v = 2^{r-d_v}` of `09:1255`, one
Alice query deeper being one exponent lower.  This lemma is monotonicity in the
**capacity** exponent `ell_v = r - d_v`, so `09:1255` is its motivating anchor
and `09:1240--1243` is the row-side companion that keeps `A_{ell}` above the
floor as the routing descends.

General in `ell <= ell'`, `m_G` and `x_T >= 0`. -/
theorem perBlockRowFloor_mono {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') (mG : ℕ) {xT : ℝ}
    (hxT0 : 0 ≤ xT) :
    ⌈(2 : ℝ) ^ ℓ * xT * (mG : ℝ)⌉₊ ≤ ⌈(2 : ℝ) ^ ℓ' * xT * (mG : ℝ)⌉₊ := by
  refine Nat.ceil_le_ceil ?_
  have hpow : (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ ℓ' := pow_le_pow_right₀ (by norm_num) hℓ
  have hnn : (0 : ℝ) ≤ xT * (mG : ℝ) := by positivity
  nlinarith

/-- **Aux A2 (the base of the schedule, `ell = 0`).**  At capacity one the
per-block floor is `ceil(x_T m_G)` and the schedule supplies `A_0 = ceil(2 x_T
m_G)`, so the frozen factor two is visibly the slack.  Both halves are recorded:
the floor is met, and `A_0` is what `09:1219` says it is.  General. -/
theorem perBlockRowFloor_at_zero (mG : ℕ) {xT : ℝ} (hxT0 : 0 ≤ xT) :
    ⌈(2 : ℝ) ^ (0 : ℕ) * xT * (mG : ℝ)⌉₊ ≤ refRowFloor (initialRefRows xT mG) 0
      ∧ refRowFloor (initialRefRows xT mG) 0 = ⌈2 * xT * (mG : ℝ)⌉₊ := by
  refine ⟨perBlockRowFloor_le_refRowFloor 0 mG hxT0, ?_⟩
  simp [refRowFloor, initialRefRows]

/-- **`A:139--140` at the derived capacity of a first-Bob node.**

The same floor, but read at `kappa_v` as the routing *derives* it rather than at
an abstract exponent: the banked `firstBob_capacity_dyadic` puts the node's
capacity in the dyadic form `2^{ell}` with `ell >= 1` (`09:1250--1259`, "every
first-Bob node has `kappa_v >= 2`"), and the floor is met at that `ell`.

General in `P`, `Coord`, `R`, `A_0`, `r` and the node; the wrapper's `A_0` is
not assumed to be `initialRefRows`, which is why the schedule instance is the one
carrying the floor. -/
theorem perBlockRowFloor_at_firstBob {X Y Z : Type*} {Coord ι V : Type*}
    {P : Protocol X Y Z} {r A0 : ℕ} (S : RoutedSystem P Coord ι V r A0) {v : V}
    (hv : S.firstBob v = true) (mG : ℕ) {xT : ℝ} (hxT0 : 0 ≤ xT) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ S.toWrapperFrontier.capacity v = 2 ^ ℓ ∧
      ⌈(2 : ℝ) ^ ℓ * xT * (mG : ℝ)⌉₊ ≤ refRowFloor (initialRefRows xT mG) ℓ := by
  obtain ⟨ℓ, hℓ, hcap⟩ := firstBob_capacity_dyadic S hv
  exact ⟨ℓ, hℓ, hcap, perBlockRowFloor_le_refRowFloor ℓ mG hxT0⟩

/-- **The endpoint call of `09:1269--1276` with `A:139--140` present -- item (18)
narrowed.**

Identical to the banked `LargeCapacityBranch.largeCapacityExtension` except that
`hLocEx` now carries `A:139--140`, "at least `ceil(r' t x m)` rows in each
represented block", placed immediately after `A:138`'s block count.  (The
antecedent chain as a whole does **not** reproduce `A:138--141`'s print order:
the column-density clause `A:141` is inherited from the banked antecedent list
and stands earlier, so the realised order is `A:141`, `A:138`, `A:139--140`.
Antecedent order is mathematically immaterial; the claim is only about where
the new clause sits relative to the block count.)  At the `09:1272`
substitution `r' t = 2^ell`, `x = x_T`, `m = m_G` the clause reads
`ceil(2^ell x_T m_G) <= rowsPerBlock`.

That antecedent is **discharged**, not assumed, from the single new binder
`hrows` -- `09:1238--1239`, "at remaining selector capacity `2^k`, a certificate
consists of at least `A_k` reference rows in one outer coordinate" -- composed
with `perBlockRowFloor_le_refRowFloor`.

**What this does and does not buy, recorded.**  The narrowed `hLocEx` is a
weaker demand on the unproved endpoint, paid for with the new binder `hrows`, so
the narrowed and banked statements are not comparable by hypothesis strength
alone; what improves is fidelity to `A:138--141`.  The banked
`largeCapacityExtension` is untouched and still proves what it proved: this
supersedes rather than deletes.  Item (18) is **advanced, not discharged** --
`selCard` is still a plain census, and nothing here forces the *counted* blocks
to be the *same* blocks `hrows` speaks about; that identification is part of the
unmodelled restriction data.

**`m` is source-DEFINED and is pinned here, not a free binder.**  `A:111` reads
"Let `M` be a nonempty Boolean matrix with `m` rows", so `m` is the row count of
the matrix the endpoint is invoked on; `09:1270` invokes it **on `G`**
("follow the denser Bob child and invoke the certified-scale reference stopping
lemma on `G`"), and `09:1291--1294` writes that row count as `m_G` in the very
display this floor is discharged from (`A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T
m_G`).  Hence `m = m_G = |Rows(G)| = Fintype.card Rw`, and every occurrence of
the floor below is formed at `Fintype.card Rw` rather than at an unconstrained
natural.  With `hGne : 1 <= Fintype.card Rw` -- itself `A:111`'s nonemptiness --
the `A:139--140` clause is then a genuine demand at **every** legal
instantiation, rather than one a caller could evacuate by choosing `m = 0`.

General in the member type, its cost, `C`, `r`, `k`, `ell`, the row count
and the real parameters `x_T`, `theta`, `colDens`; the row-floor parameter `m`
is **not** general -- it is the row carrier of `Gmat`. -/
theorem largeCapacityExtension_rowFloor {Mem : Type*} (memCost : Mem → ℕ) (mem : Mem)
    {C r k ℓ tcert selCard rowsPerBlock : ℕ} {xT θ colDens : ℝ}
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Gmat : Rw → Cl → Bool)
    (hk : 4 ≤ k) (hkl : k ≤ ℓ) (hℓr : ℓ ≤ r) (hq4 : k + 2 ≤ r) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hcount : 9 * (((2 : ℕ) ^ ℓ : ℕ) : ℝ) / 16 ≤ (selCard : ℝ))
    -- `09:1238--1239` with `09:1219--1221`: the routing's own row bookkeeping,
    -- at the source-DEFINED `m = m_G = Fintype.card Rw` (`A:111` with `09:1270`)
    (hrows : refRowFloor (initialRefRows xT (Fintype.card Rw)) ℓ ≤ rowsPerBlock)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ (ℓ - k) →
      (2 : ℕ) ^ (ℓ - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ (ℓ - k) * 2 ^ k = 2 ^ ℓ →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      -- `A:138--139`, exactly `r' p_t` represented outer blocks, and enough of them
      2 ^ (ℓ - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ ℓ / 16 →
      9 * (((2 : ℕ) ^ ℓ : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
      -- `A:139--140`, at least `ceil(r' t x m)` rows in each represented block,
      -- with `m` at its defining value `m_G = Fintype.card Rw` (`A:111`, `09:1270`)
      ⌈(2 : ℝ) ^ ℓ * xT * ((Fintype.card Rw : ℕ) : ℝ)⌉₊ ≤ rowsPerBlock →
      (C - 1) + ℓ ≤ memCost mem) :
    C + ℓ ≤ 1 + memCost mem := by
  have hfloor : ⌈(2 : ℝ) ^ ℓ * xT * ((Fintype.card Rw : ℕ) : ℝ)⌉₊ ≤ rowsPerBlock :=
    le_trans (perBlockRowFloor_le_refRowFloor ℓ (Fintype.card Rw) (le_of_lt hxT0)) hrows
  exact largeCapacityExtension memCost mem Gmat hk hkl hℓr hq4 hC hxT0 hxT1 hθ0 hθ1 hGne
    hgate hcount hbase htcert hE1 hE2 hcol
    (fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 =>
      hLocEx h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hfloor)

end RowFloor

/-! ## §3  The narrowed branch and the narrowed join

The narrowed endpoint is threaded to the frontier apparatus and then to the join,
mirroring the banked `canonical_firstBobLight_largeCapacity` and §1's
`firstBobLight_assembled` step for step.  Nothing else changes: the small branch,
the budget, and the `hselect` binder are exactly as they were. -/

section NarrowedFrontier

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **The large-capacity branch of `09:1269--1276` at the frontier, with
`A:139--140` supplied.**

The banked `canonical_firstBobLight_largeCapacity` with the narrowed endpoint
substituted for the banked one, and the new binder `hrows` threaded.  The block
count is still the banked `heavy_blockCount_le_card_representedCoords`
(`09:1268--1269` with `09:1279--1281`), the dichotomy still the banked
`canonical_firstBobLight_branchwise`.

**The `m` pin is inherited, at this layer too.**  `m_G` is not a free binder
here either: exactly as `selCard` is instantiated at this layer to the real
quantity `(representedCoords P R A0 r v).card`, the row floor is formed at the
real row count `Fintype.card Rw` of `Gmat` -- `A:111`'s `m` under `09:1270`'s
substitution `M = G`.  The row-floor clause is therefore tied to a real row
count at every layer of the module, and to none that a caller may choose.

General in the source carriers, `C`, `r`, `k`, the residual budget and the
real parameters `x_T`, `theta`, `colDens`; `m` is the row carrier of `Gmat`. -/
theorem canonical_firstBobLight_largeCapacity_rowFloor {Rw Cl : Type*} [Fintype Rw]
    [Fintype Cl] (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B k tcert rowsPerBlock : ℕ} {xT θ colDens : ℝ}
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hrows : refRowFloor (initialRefRows xT (Fintype.card Rw)) (r - v.val.length)
      ≤ rowsPerBlock)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xT * ((Fintype.card Rw : ℕ) : ℝ)⌉₊
        ≤ rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ B)
    (hsmall : r - v.val.length < k →
      smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
        ≤ (representedCoords P R A0 r v).card →
      C + (r - v.val.length) - 1 ≤ B) :
    frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  refine canonical_firstBobLight_branchwise hcomp hR hv hC hbudget ?_ hsmall
  intro hbranch hheavy
  have hcap : (canonicalSystem hcomp hR).toWrapperFrontier.capacity v
      = 2 ^ (r - v.val.length) := rfl
  have hcount : 9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
      ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) := by
    refine heavy_blockCount_le_card_representedCoords P R A0 r v ?_
    rw [← hcap]
    exact hheavy
  have hend : C + (r - v.val.length) ≤ 1 + B :=
    largeCapacityExtension_rowFloor (Mem := ℕ) (fun n => n) B Gmat hk hbranch
      (Nat.sub_le _ _) hq4 hC hxT0 hxT1 hθ0 hθ1 hGne hgate hcount hrows hbase htcert hE1 hE2
      hcol hLocEx
  omega

/-- **`eq:wrapper-first-bob-light` (`09:1306--1313`), assembled with
`A:139--140` supplied.**

`firstBobLight_assembled` with the narrowed large branch.  The small branch is
discharged exactly as in §1 -- `capacity_row_density_legal` (`09:1302--1304`)
then `smallCapacity_child_bound` (`09:1296--1306`) -- and `hselect`
(`09:1287--1296`, GAP-EXPOSED item 15, owned by
`SPLIT-FIRST-BOB-INSTANCE-001`) is untouched.

The surviving binder list is §1's, with one addition and one weakening:
`hrows` is new (`09:1238--1239`), and `hLocEx` now grants `A:139--140`.  Nothing
else moves.

**The `m` pin, at the headline product.**  As in the two layers below, the
`A:139--140` floor is formed at the source-DEFINED `m = m_G = Fintype.card Rw`
(`A:111` under `09:1270`'s `M = G`), never at a caller-chosen natural; `hGrow`
is `A:111`'s nonemptiness for that same carrier, so `m_G >= 1` holds wherever
this theorem is applied and the new clause cannot be evacuated **by the
`m := 0` route**, exactly as the parallel sentence in
`largeCapacityExtension_rowFloor` scopes it.  That is the whole of the claim:
`rowsPerBlock` remains a free natural tied to no real represented block, so the
new clause is still discharged from `hrows` at every instantiation and
constrains nothing at the point of use -- GAP-EXPOSED item **(21)** on this
module's ledger row, the same species as the registered free `colDens`.

General in the source carriers, `P`, `Coord`, `R`, `A_0`, `r`, `C`, `k`,
the residual budget and the real parameters `x_T`, `theta`, `colDens`, `y`;
`m` is the row carrier of `Gmat`. -/
theorem firstBobLight_assembled_rowFloor {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B k tcert rowsPerBlock : ℕ} {xT θ colDens y : ℝ}
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hGrow : 1 ≤ Fintype.card Rw) (hGcol : 1 ≤ Fintype.card Cl)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hrows : refRowFloor (initialRefRows xT (Fintype.card Rw)) (r - v.val.length)
      ≤ rowsPerBlock)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (hbaseY : C - 1 ≤ LambdaGE Gmat 1 xT y)
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) →
      ⌈(2 : ℝ) ^ (r - v.val.length) * xT * ((Fintype.card Rw : ℕ) : ℝ)⌉₊
        ≤ rowsPerBlock →
      (C - 1) + (r - v.val.length) ≤ B)
    (hselect : smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
        ≤ (representedCoords P R A0 r v).card →
        LambdaGE Gmat (2 ^ (r - v.val.length - 1) + 1)
          ((2 : ℝ) ^ (r - v.val.length) * xT) (y ^ 2) ≤ B) :
    frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  refine canonical_firstBobLight_largeCapacity_rowFloor Gmat hcomp hR hv hC hk hq4 hxT0 hxT1
    hθ0 hθ1 hGrow hgate hrows hbase htcert hE1 hE2 hcol hbudget hLocEx ?_
  intro hbranch hcover
  have hlt : v.val.length < r := ((canonicalSystem hcomp hR).firstBob_spec v hv).2.2
  have hlegal : ((2 : ℝ) ^ (r - v.val.length)) * xT ≤ 1 :=
    capacity_row_density_legal (le_of_lt hxT0) (le_of_lt hbranch) hq4 hgate
  have hladder := smallCapacity_child_bound Gmat (ℓ := r - v.val.length) hGrow hGcol hC hxT0
    hy0 hy1 hbaseY (by omega) hlegal
  exact le_trans hladder (hselect hcover)

end NarrowedFrontier

/-! ## §4  Aux battery, statement poles and hypothesis consistency

One general readout of the assembled conclusion, two poles, and one
BEYOND-PAPER consistency check; the three general properties of the new
`A:139--140` clause are §2's `perBlockRowFloor_mono`, `perBlockRowFloor_at_zero`
and `perBlockRowFloor_at_firstBob`.  A green build sees none of these. -/

section Poles

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **Aux A4 (readout of the assembled conclusion at the frozen numerals).**

`eq:wrapper-first-bob-light` is `W_v < vartheta kappa_v` with `vartheta = 9/16`
(`09:1268`) and `kappa_v = 2^{ell_v}`, `ell_v >= 1` (`09:1255`, `09:1259`).  This
lemma reads the conclusion of `firstBobLight_assembled` in exactly those frozen
terms: the capacity is exhibited in its dyadic form and the threshold as `9/16`.

A round-trip check on the encoding rather than new mathematics: the dyadic form
is the banked `firstBob_capacity_dyadic` and the threshold the banked
`vartheta_val`.  If either pin drifted, this lemma would stop compiling.

General in `P`, `Coord`, `R`, `A_0`, `r` and the node. -/
theorem assembled_conclusion_readout {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r}
    (hv : (canonicalSystem hcomp hR).firstBob v = true)
    (hlight : frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ)) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ (canonicalSystem hcomp hR).toWrapperFrontier.capacity v = 2 ^ ℓ
      ∧ frontierWeight P R A0 r v < 9 * (2 : ℝ) ^ ℓ / 16 := by
  obtain ⟨ℓ, hℓ, hcap⟩ := firstBob_capacity_dyadic (canonicalSystem hcomp hR) hv
  refine ⟨ℓ, hℓ, hcap, ?_⟩
  rw [hcap] at hlight
  have hcast : (((2 : ℕ) ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by push_cast; ring
  rw [hcast, vartheta_val] at hlight
  linarith

/-- **Statement pole: `A:139--140` is a real demand, not a free antecedent.**

Were `ceil(2^ell x_T m_G) <= rowsPerBlock` automatic, the narrowing of §2 would
be decoration.  It is not: at `ell = 1`, `x_T = 1/2`, `m_G = 4` the floor is
`ceil(2 . (1/2) . 4) = 4`, which a block carrying only `3` rows fails, while the
schedule's own `A_1 = 2 . ceil(2 . (1/2) . 4) = 8` meets it with room to spare.

**Rejection probe, claiming no legality.**  The numerals `ell = 1`, `x_T = 1/2`,
`m_G = 4` are ours and are not legal schedule values -- `eq:wrapper-low-simple-gate`
alone forces `x_T` far below `1/2`.  Their only role is to show a guard fires. -/
theorem perBlockRowFloor_is_not_free :
    ⌈(2 : ℝ) ^ (1 : ℕ) * (1 / 2 : ℝ) * ((4 : ℕ) : ℝ)⌉₊ = 4
      ∧ ¬ (⌈(2 : ℝ) ^ (1 : ℕ) * (1 / 2 : ℝ) * ((4 : ℕ) : ℝ)⌉₊ ≤ 3)
      ∧ refRowFloor (initialRefRows (1 / 2 : ℝ) 4) 1 = 8 := by
  have h4 : (2 : ℝ) ^ (1 : ℕ) * (1 / 2 : ℝ) * ((4 : ℕ) : ℝ) = 4 := by norm_num
  have hceil : ⌈(2 : ℝ) ^ (1 : ℕ) * (1 / 2 : ℝ) * ((4 : ℕ) : ℝ)⌉₊ = 4 := by
    rw [h4]; simp
  refine ⟨hceil, by rw [hceil]; norm_num, ?_⟩
  have hinit : initialRefRows (1 / 2 : ℝ) 4 = 4 := by
    simp only [initialRefRows]
    norm_num
  simp only [refRowFloor, hinit]
  norm_num

/-- **Statement pole: the join of `09:1306--1308` is a one-bit margin, and the
closure output is not free.**

"Its lower bound is one more bit than the remaining child budget in the alleged
protocol."  Written subtraction-free with `d_v + ell_v = r`: the suffix below the
selected Bob child has at most `C + ell_v - 2` bits available, and either branch
gives the child `C + ell_v - 1`.  The margin is exactly one, so the contradiction
of `09:1306--1308` fires and nothing weaker would do.

The **first clause is general and is the non-vacuity statement that matters**:
at *every* tuple satisfying the frozen side conditions -- `C >= 3`,
`d_v + ell_v = r`, `ell_v >= 1` (`09:1259`), and the budget relation of
`09:1306--1308` -- the closure output `C + ell_v - 1` strictly exceeds the
residual budget `B`.  So the contradiction fires everywhere the assembled join
is applied, and `firstBobLight_assembled` is nowhere vacuous for want of a
margin.  The subsequent clauses instantiate it at the frozen minimum `C = 3`
with `ell_v = 4`, `d_v = 2`, `r = 6`, `B = 5`, and record that at `B = 6` -- one
bit more -- the budget relation itself fails.  Those numerals are
**BEYOND-PAPER**, claim no legality, and only illustrate the general clause; the
underlying contradiction is the banked
`DenseWrapperFrontier.firstBob_budget_contradiction`. -/
theorem assembled_join_margin_is_one_bit :
    (∀ C r d ℓ B : ℕ, 3 ≤ C → d + ℓ = r → 1 ≤ ℓ → B + (d + 1) ≤ C + r - 1 →
        B + 1 ≤ C + ℓ - 1)
      ∧ (5 : ℕ) + (2 + 1) ≤ 3 + 6 - 1
      ∧ ¬ ((3 : ℕ) + 4 - 1 ≤ 5)
      ∧ (3 : ℕ) + 4 - 1 = 5 + 1
      ∧ ¬ ((6 : ℕ) + (2 + 1) ≤ 3 + 6 - 1) := by
  refine ⟨fun C r d ℓ B hC hdℓ hℓ hbudget => by omega, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- **Hypothesis consistency for the assembled join (BEYOND-PAPER AUDIT).**

Per the `HYPOTHESIS-CONSISTENCY` discipline, the assembled theorem's binder
bundle is checked for joint satisfiability rather than assumed consistent.

**Coverage, stated precisely, and it is partial.**  What is exhibited below is
the **arithmetic and gate** group of `firstBobLight_assembled` -- `hk`, `hq4`,
`hC`, `hxT0`, `hxT1`, `hgate`, `hbudget`, and `1 <= ell_v` -- jointly satisfiable
at `C = 3`, `r = 6`, `k = 4`, `d_v = 2`, `ell_v = 4`, `B = 5`, with `x_T` taken
as the banked closed-form accessor `WrapperLowRungs.wrapperLowRungGates_legal_instance`
at `(k, r) = (4, 6)` rather than as a numeral, together with the branch-side row
floor `ceil(2^{ell_v} x_T m_G) <= A_{ell_v}` at that same `x_T`, which is the new
§2 clause evaluated inside the bundle.

**`m_G` is evaluated from a carrier, not asserted as a numeral.**  `A:111` makes
`m` the row count of the matrix, and `09:1270` substitutes `M = G`, so `m_G` is
never an independently choosable number: it is whatever `Fintype.card Rw` is for
the row carrier in play.  The audit instance therefore *names a carrier*,
`Rw := Fin 1`, and writes the floor at `Fintype.card (Fin 1)`, evaluating the
definitional chain rather than short-circuiting it with the numeral `1`.  The
choice of the carrier is ours and is BEYOND-PAPER (see the label below); the
value of `m_G` given that carrier is not ours, and this instance does not assert
it.  `Fin 1` is a legal row carrier in the sense that matters here -- it is
nonempty, so `hGrow : 1 <= Fintype.card Rw` holds of it -- while no claim is made
that any `G` of the schedule has one row.

The **analytic** binders `hbase`, `hbaseY`, `hy0`, `hy1`, `hGrow`, `hGcol` are
inherited unchanged from the banked `smallCapacity_child_bound` and
`largeCapacityExtension`, and are **not** instantiated jointly with the
arithmetic ones: no `Gmat` is exhibited at the pinned `x_T`.  The endpoint
binders `hE1`, `hE2`, `hcol`, `htcert` are likewise **declined** -- `hE1`/`hE2`
are in fact unsatisfiable at small `k`, which is exactly why `eq:tref-search`
forces `k_ref >= 2^19` and why `k` stays universally quantified.  So full-bundle
satisfiability is *inferred from the groups*, not exhibited, and a joint instance
would additionally need the unmodelled `hLocEx` and `hselect`.

The last clause is the join: the closure output `C + ell_v - 1 = 6` exceeds the
residual budget `B = 5`, so the frozen contradiction of `09:1306--1308` genuinely
fires and the bundle is **not** vacuously consistent with its own conclusion.

**BEYOND-PAPER AUDIT.**  `r` is DEFINED by `06:515` with `09:105`, `k = k_ref` by
`06:558--569`, `C` by the wrapper schedule, and `x_T` by `06:243`
(`x_T = 2^{-b_T}` with `b_T = 2^{j_{49}(k_T)}` at `06:241`).  The values `r = 6`,
`k = 4`, `C = 3`, `B = 5`, `d_v = 2`, the carrier `Rw := Fin 1` (hence `m_G = 1`
by evaluation), **and the resulting `x_T = 1/(2^6 . 65536) = 2^{-22}`** are
**ours**, and no legality is claimed for any of them.  `x_T` is disclosed here
explicitly: although it enters through the banked closed-form accessor
`wrapperLowRungGates_legal_instance 4 6` as an *expression* rather than a numeral
-- which is the required discipline, since `06:243` DEFINES it -- the accessor is
evaluated at BEYOND-PAPER arguments, so the pinned value is a BEYOND-PAPER value
and is named as one.  These clauses audit *our* encoding at a point the paper
never visits, and are strictly weaker evidence than the paper's application
point. -/
theorem assembled_arithmetic_binders_consistent :
    (4 : ℕ) ≤ 4 ∧ (4 : ℕ) + 2 ≤ 6 ∧ (3 : ℕ) ≤ 3
      ∧ (0 : ℝ) < 1 / ((2 : ℝ) ^ 6 * 65536)
      ∧ (1 : ℝ) / ((2 : ℝ) ^ 6 * 65536) ≤ 1
      ∧ ((2 : ℝ) ^ (6 : ℕ)) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 4 / 25025
      ∧ (5 : ℕ) + (2 + 1) ≤ 3 + 6 - 1
      ∧ 1 ≤ (6 - 2 : ℕ)
      ∧ ⌈(2 : ℝ) ^ (6 - 2 : ℕ) * (1 / ((2 : ℝ) ^ 6 * 65536))
            * ((Fintype.card (Fin 1) : ℕ) : ℝ)⌉₊
          ≤ refRowFloor (initialRefRows (1 / ((2 : ℝ) ^ 6 * 65536))
              (Fintype.card (Fin 1))) (6 - 2)
      ∧ ¬ ((3 : ℕ) + (6 - 2) - 1 ≤ 5) := by
  obtain ⟨-, hpos, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, hpos, ?_, ?_, by norm_num, by norm_num,
    perBlockRowFloor_le_refRowFloor _ _ (le_of_lt hpos), by norm_num⟩
  · rw [div_le_one (by positivity)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 6]
  · rw [hval]; norm_num

end Poles

end EthInapproximability.ParameterizedNP.FirstWrapperAssembly
