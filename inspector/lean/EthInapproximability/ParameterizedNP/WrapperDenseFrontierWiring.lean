import EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
import EthInapproximability.ParameterizedNP.FirstWrapperAssembly

/-!
# Parameterized NP route: the dense-frontier wiring of the routed triple `(S,T,K)`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand
  this tranche.
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:311--313`**, "Project the retained outer column set to any
      `9 kappa_j/16` such coordinates.  Its normalized density remains at least
      `theta`, by specified-coordinate projection." -- the block side of the
      routed triple at the low-rung site.
    * **`09:313--323`, the substitution display**, and **`09:325--327`, the
      legality paragraph** ("the reference restriction is a full product, so its
      balancedness error is exactly zero"); both consumed by pin from
      `WrapperReferenceConstruction`, never restated.
    * **`sec:wrapper-projection-covers` (label `09:336`)** with
      `lem:product-projection-cover` (label `09:343`, statement `09:342--353`,
      proof `09:355--362`), and `E_0`, `e_0 = |E_0|` at `09:448--451`.  The
      cover itself is the banked `WrapperProjectionCovers.productProjectionCover`
      and is consumed by pin.
    * **`sec:dense-wrapper-frontier` (label `09:1185`), the frozen frame of
      `09:1184--1366`**: the completed no-Bob prefix `09:1196--1215`;
      `A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0` at `09:1219--1222`; the routing
      rule `09:1238--1248`; `kappa_v = 2^{r - d_v}`, `W_v` at `09:1253--1258`;
      `eq:wrapper-frontier-conservation` at `09:1261--1266`; `vartheta = 9/16`
      at `09:1268` (record fix F6: the line is `09:1268`, not `09:1267`,
      which is blank).
    * **`09:1268--1276`, THE DENSE-FRONTIER CERTIFIED CALL.**  "We first close
      any first-Bob node satisfying `W_v >= vartheta kappa_v`.  When
      `kappa_v >= t_ref`, follow the denser Bob child and invoke the
      certified-scale reference stopping lemma on `G` with
      `r' = kappa_v/t_ref`, `a^sharp = 1`.  The other parameters are those of
      `sec:wrapper-low-rungs`."  This is the **`a^sharp = 1`** site; §3 below
      builds its restriction as an explicit full product for the first time.
    * **`09:1277--1290`**, "the number of represented coordinates is at least
      `ceil(W_v)`", "`ceil(W_v) >= ceil(9 kappa_v/16) >= u_{kappa_v}`", "the
      parent projection to any selected `u_{kappa_v}` of them has density at
      least `rho = 2y^2`.  The denser Bob child retains density at least `y^2`"
      -- the frozen sentence that *is* the `a^sharp = 1` of `09:1273`, and the
      reason §3's column clause is `theta/2` and not `theta`.
    * **`09:1291--1296`**, "Each selected certificate has at least
      `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` reference rows, so trim it
      to the row density `kappa_v x_T`" -- the row side of the routed triple,
      and the exact source of §3's factor `2`.
    * **`09:1746--1749`, the poor-`u_don` projection cover.**  "Apply the
      poor-`u_don` projection cover to the donors feeding `T_*`.  By
      `eq:wrapper-terminal-donor-gate`, it leaves `u_don` donors whose joint
      outer projection has density at least `rho_0`."  §5 folds exactly this
      sentence, and nothing after it.
    * **`09:1780--1781`**, "We have proved `eq:wrapper-u-dense`" -- the target
      this module **does not reach**; see the residue paragraph below.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    `A:138--141` (the restriction bundle: `r' p_t` represented outer blocks,
    `ceil(r' t x m)` rows per represented block, column density at least
    `h 2^{-a^sharp}`) and `A:128--129` (`h in (0,1]`, `a^sharp in {0,1}`).  The
    whole interface is the banked `RestrictionDatum.RestrictionDatum` and the
    banked `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall`; nothing
    below restates a clause of either.
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `eq:tref-search` (`06:557--572`) whose closing clause `06:568--569` defines
    `t_ref = 2^{k_ref}`, and `eq:cover-bounds` (`06:640--654`) which owns
    `B_ref`, `B_sing`, `B_pair` and `e_0^max`.  Both are banked
    (`WrapperReferenceConstruction.tRef`, `WrapperProjectionCovers.e0Max`,
    `ParameterSchedule`) and are consumed by pin; no numeral is put in their
    place.
  * `08-dense-stage4.tex`
    (SHA-256 `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`),
    `08:166`, the defining display `x_T = 2^{-b_T}`, banked as
    `DenseStageFourOpening.xTdepth` and consumed by pin.
* **Cited external interfaces.**  `EXPANDER-001` (`lem:cited-expander-family`)
  has **no** Lean declaration by design and occurs in no hypothesis here: the
  `A:126--128` family clause enters only through the `eps` legality disjunction,
  and both sites wired below sit on its *other* branch -- the exact full product
  -- which is why every restriction constructed here is a rectangle and its
  balancedness error is literally `0`.  `LegacyNPCC.Stage12`, whose closure
  reaches the cited AGHP balanced-family axiom, is **not** imported, directly or
  transitively.  No new `axiom`, no opaque certificate, no unproved placeholder.

## What this tranche is

The convergence point of the two arcs.  `WrapperReferenceConstruction` (banked)
built the certified reference call's restriction *as a function of a routed
triple* `(S, T, K)` and recorded, in its own words, that "the **routing** is not
built ... the *selection* of which outer coordinates and which reference rows the
frontier routing hands the call at a given member ... is the content of
`sec:wrapper-dense-frontier` and after, and enters here only as the data
arguments `S`, `T`, `K` and as the still-open `hrung` binder of §6".

This module names that routing supply and builds the restrictions it determines,
from the banked frontier apparatus, so that the waiting restriction-side
declarations are read at a triple the frontier produces rather than at an
assumed one.

**What it does not do, said once at the top.**  It does **not** discharge the
`hrung` binder, in whole or in part.  §4 is a shell -- named as such, proved by
`shell_signature_forall_to_exists`, with `routedSupply_gives_only_inhabitation`
proving that the routing's entire contribution to `hrung` is datum inhabitation,
which `WrapperReferenceConstruction.referenceRestriction_nonempty` already banks.
The parked generation of this module claimed the opposite; that claim is
withdrawn here, and the `hrung` deferral of
`WRAPPER-REFERENCE-CONSTRUCTION-001` stands **unchanged**, with the endpoint
(`A:285--329`) as its residue.

## This generation: `L1-F6`, the `hone` retirement (licensed opening)

The one change over the banked generation, and it is confined to §3's row side:
the binder `hone : kappa_v x_T m_G >= 1` is **retired** from
`exists_trimmed_reference_rows` and from its consumer
`exists_frontier_routedTriple`, replaced in both by
`hpos : r' t x m > 0`.  The registration is `L1-F6` of
`TRANSCRIPT-LEVEL-SUCCESSORS-001` (tranche `cc-t5c`), whose
`exists_trimmed_reference_rows_in_the_positive_regime` proved the retired binder
dischargeable in the legal regime.  (That declaration became a duplicate of the
interface it produced and was deleted by `L1-F9` in tranche `cc-t5i`, with no
declaration of the same type left behind under another name; its single consumer
now fires this module's `exists_trimmed_reference_rows` directly, converting the
four unbundled positivity facts through `trim_positivity_iff_factors_positive`
at the call site.)

* **Why it is redundant.**  The frozen `09:1291--1296` states only the row count
  `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G`; the product `x_Tm_G` occurs in
  `09-first-wrapper.tex` at `09:1219`, `09:1294` and `09:1327` only, and none of
  the three is a `>= 1` display.  The proof consumes nothing beyond
  `r' t x m > 0`, and that positivity is **entailed by** (not equal to) the
  ambient guards the invoked theorem already fixes: `A:111--112`'s nonempty
  matrix with `0 < x <= 1`, `A:117--118`'s `t >= t_cert` a power of two divisible
  by `16`, and `A:125`'s positive powers of two.  The guards are strictly
  stronger than the positivity; only the entailment direction is used.
* **What does not move.**  The conclusion is byte-identical:
  `T.card = RestrictionDatum.certifiedRowFloor r' t x m` with
  `certifiedRowFloor = ceil(r' t x m)` (`RestrictionDatum.lean:247`), i.e.
  `A:140` verbatim, plus `T.Nonempty`.  Both theorems become strictly stronger;
  no statement is weakened and no obligation is transferred.
* **Call sites.**  The one `src/` consumer outside this file,
  `TranscriptLevelConstruction.exists_frontier_routedTriple_at_paper_indices`,
  is updated in the same change *at its proof only* -- its own signature, and
  therefore everything downstream of it, is untouched: it still carries the
  paper-shaped `hone` and now derives `hpos` from it in one step.  Retiring that
  binder too is the **successor `WDFW-F13`**, deliberately not taken here, since
  it would move the statements of two further modules and so fall outside this
  opening.  (It was taken in tranche `cc-t5i`; see the successor list below.)
* **Hypothesis consistency is inherited, not re-argued.**  The only clause that
  moved was replaced by a strictly weaker one
  (`retired_hone_binder_is_strictly_stronger`, first conjunct), so every model of
  the pre-retirement bundle is a model of this one: the change can create no
  inconsistency, and no LANE-GATE 3 obligation is created by it.  Nor is one
  discharged -- the bundle's inhabitation at a *heavy* frontier node stays
  DEFERRED against residue `L1` exactly as before.
* **Scope.**  Nothing else in this module changes: no anchor is re-cited, no
  deferral is discharged, `WDFW-F10`--`WDFW-F12` stand, and the LANE-GATE 3
  deferral of the frontier premise bundle against residue `L1` is unchanged.
* **Successors this generation registers.**
  * **`WDFW-F13` -- DISCHARGED in tranche `cc-t5i`**: retire the paper-shaped
    `hone` from
    `TranscriptLevelConstruction.exists_frontier_routedTriple_at_paper_indices`
    and its own consumers (see "Call sites" above); an interface change across
    two further modules, therefore its own tranche.  Both statements now carry
    `hpos` in the same binder position with their conclusions byte-identical, so
    both became strictly stronger, and the audit witnesses in those modules keep
    the retired, stronger clause and weaken it at the call.  **Consequence for
    this module, recorded and ruled on at the declaration itself:**
    `exists_trimmed_reference_rows_of_one`, the compatibility corollary that
    served the `hone`-carrying callers, has no consumer left.  It is KEPT as a
    labelled dead endpoint rather than deleted -- it is strictly weaker than the
    theorem it fires, not a duplicate of it, and it is the machine-checked
    evidence that the retired binder was never the paper's.  No successor is
    registered to revive it.
  * **`WDFW-F14` -- DISCHARGED in tranche `cc-t5i`** (see the next section):
    rename `trim_positivity_iff_ambient_guards`.  The `iff` is
    with the four **positivity** facts the guards entail, not with the guards of
    `A:111--112`/`A:117--118`/`A:125` themselves, which additionally demand
    "power of two", "divisible by `16`", "`>= t_cert`" and "`x <= 1`".  Nothing
    false is proved and only the entailment direction is consumed, but the name
    invites the inverted reading; `trim_positivity_iff_factors_positive` is the
    prescribed name.  A rename is an interface change, hence a successor.
  * **`WDFW-F15` -- DISCHARGED in tranche `cc-t5i`** (see the next section):
    replace the deprecated `push_neg at hxle` inside
    `trim_positivity_iff_factors_positive` with `push Not at hxle`.  The build is
    GREEN; this was the one deprecation warning the `L1-F6` generation
    introduced, and it is a proof-tactic edit, which the verify seat's
    record-only boundary does not cover.

## This generation: `WDFW-F14` + `WDFW-F15` (licensed opening, tranche `cc-t5i`)

Two registered successors of the `L1-F6` generation above, taken together
because both touch the same declaration and neither touches a statement.

* **`WDFW-F15`, the tactic swap.**  Inside the proof only, `push_neg at hxle`
  becomes `push Not at hxle`.  `Mathlib/Tactic/Push.lean:276--283` deprecates
  `push_neg` and expands it to exactly `push <cfg> Not <loc>`, so the swap is
  token-for-token the tactic the deprecation names and the elaborated proof term
  is unchanged.  **The theorem's statement bytes do not move**, and the module's
  one deprecation warning is gone.
* **`WDFW-F14`, the rename.**  `trim_positivity_iff_ambient_guards` becomes
  `trim_positivity_iff_factors_positive`, the name prescribed when the successor
  was registered.  The old name is **not** retained as an alias: an alias would
  keep the misleading reading reachable, which is the whole defect the successor
  names.  The rename is safe because the declaration is **unconsumed** -- after
  the edit its identifier occurs in comment-stripped `src/` exactly once, at its
  own head -- so no proof term anywhere depends on the old identifier.
* **Statement bytes, both declarations.**  Nothing but the identifier changes:
  the binders `{r' t m : ℕ} {x : ℝ}`, the left side
  `0 < ((r' * t : ℕ) : ℝ) * x * (m : ℝ)` and the right side
  `0 < r' /\ 0 < t /\ 0 < m /\ 0 < x` are byte-identical to the banked ones.  No
  hypothesis is added, weakened or reordered, so no LANE-GATE 3 obligation is
  created and none is discharged.
* **The companion rename, in the other module.**  `L1-F9`'s rename half is taken
  in the same tranche: `TranscriptLevelSuccessors`'s
  `positive_regime_trim_is_strictly_stronger` becomes
  `positive_regime_trim_holds_where_hone_fails`, which is what its three
  conjuncts actually prove now that `L1-F6` has made it and the banked lemma
  logically equivalent.  `L1-F9`'s **deduplication** half is *not* taken here --
  it would move statements in a third module.
* **Scope.**  No anchor is re-cited, no deferral is discharged, no declaration is
  added or removed, `WDFW-F10`--`WDFW-F13` stand, and the LANE-GATE 3 deferral of
  the frontier premise bundle against residue `L1` is unchanged.  `tools/AxiomAudit.lean`
  is repointed at the two new identifiers; the audit count is unchanged at `38`.

## What is consumed by pin, and what is authored

**Consumed by pin, never restated:**

* `WrapperReferenceConstruction.productRestriction`, `.referenceRestriction`,
  `.representedBlocks_product`, `.productRestriction_selCard`,
  `.productRestriction_rowsPerBlock`, `.productRestriction_colDens`,
  `.referenceRowFloor_at_mG`, `.refBlockCount_eq_certifiedPt_kappa`,
  `.productRestriction_rejects_empty_rows`, `.referenceRestriction_nonempty`,
  `.wrapperLowRungs_at_referenceConstruction`, `.tRef`, `.refRungCopies` -- the
  ten restriction-side declarations this tranche wires, plus the headline they
  feed and the two width reifications they are indexed by.
* `LargeCapacityBranch.heavy_blockCount_le_card_representedCoords` -- `09:1268--1269`
  with `09:1280--1281`.
* `SplitFirstBobInstance.representedCoords`,
  `.representedCoords_nonempty` -- the frontier's own census, `09:1278--1281`.
* `RoutedCertificateSystem.exists_denser_bob_child`, `.retainedCols`,
  `.card_bobCols_children_add` -- `09:1287--1290`.
* `FrontierIndexing.frontierWeight`, `.FrontierNode`;
  `DenseWrapperFrontier.vartheta`, `.vartheta_val` -- `09:1268` (the `vartheta`
  display; `09:1253--1258` is the `kappa_v`/`W_v` display it sits after).
* `WrapperProjectionCovers.productProjectionCover`, `.PoorProjection`,
  `.projSet` -- `lem:product-projection-cover`.
* `WrapperMassRedistribution.donors_survive_cover` -- the counting step of
  `09:1746--1749`.
* `RestrictionDatum.RestrictionDatum`, `.certifiedPt`, `.certifiedRowFloor`,
  `.certifiedColFloor`, `.representedBlocks`, `.certifiedPt_pos`,
  `.sixteen_dvd_two_pow`.
* `DenseStageFourOpening.xTdepth`, `.cBlock`; `WrapperLowRungs.kappaLow`;
  `CertifiedLocalizedExtension.CanonicalReferenceStoppingCall`, `.tCert`,
  `.clog_two_tCert`.

**Authored here** (and nowhere else in `src/`):

1. `RoutedTriple`, the four-clause *supply* the routing hands the certified call
   at one node: a nonempty row side, the `A:138` block count, the `A:139--140`
   row floor, the `A:141` column floor.  It is a `Prop`-valued `def`, not a
   structure, so it creates no new bundle-inhabitation obligation and restates no
   derived telescope: its four clauses are literally the four data hypotheses of
   the banked `productRestriction`, and nothing else.
2. `routedRestriction` and its four readouts -- the banked full-product
   constructor fired at a supply, with `A:138`, `A:139--140` and `A:141` read
   back off the built object.
3. `lowRungRoutedRestriction` and its two frozen readouts -- the same at the
   `09:313--323` indices (`a^sharp = 0`), where the block count is the frozen
   `9 kappa_j/16` and the row floor is read at `m_G`.
4. **The frontier supply itself** (§3): the three sides of the triple produced
   from the routed system at a heavy first-Bob node --
   `exists_selected_blocks_at_heavy_node` (`09:1268--1269` + `09:1280--1281`),
   `exists_trimmed_reference_rows` (`09:1291--1296`),
   `exists_denser_child_colFloor` (`09:1287--1290`) -- and
   `exists_frontier_routedTriple`, which assembles them into a `RoutedTriple` at
   `a^sharp = 1`.  **Branch attribution, recorded (F2).**  `09:1268--1300` is a
   dichotomy: branch (i), `kappa_v >= t_ref` (`09:1269--1275`), is the
   reference-stopping call at `a^sharp = 1`; branch (ii), `2 <= kappa_v < t_ref`
   (`09:1276--1300`), defines `ell_v = log_2 kappa_v`, runs the
   represented-coordinate census with `u_{kappa_v}`, the `rho = 2y^2` parent
   projection and the trim, and then applies **`lem:certified-row-ladder`**, not
   the reference stopping lemma.  The assembled `a^sharp = 1` supply is a branch-(i)
   object, but two of its three ingredients are read outside branch (i)'s own
   paragraph: the represented-coordinate census `09:1280--1281` with
   `09:1287--1290`, and the reference-row trim `09:1291--1296`.  Each is derivable
   at branch (i) as well -- the census bound
   `LargeCapacityBranch.heavy_blockCount_le_card_representedCoords` depends only on
   `09:1268`'s heavy condition, not on the `kappa_v` split -- and the Lean
   statements are branch-neutral generalisations, which is why they are not false;
   but the attribution is recorded here rather than left implicit.
5. **The `hrung` binder, named and left open** (§4): `ReferenceStoppingEndpoint`
   names `thm:certified-localized-extension` at the `09:313--323` substitution
   once, tied to `\widehat M`'s `[q]`; `shell_signature_forall_to_exists` isolates
   the inference that makes any `hrung`-shaped deliverable a shell;
   `routedSupply_gives_only_inhabitation` proves that the routing contributes
   exactly datum inhabitation to it and nothing else; and
   `rung_of_referenceEndpoint` states the shell in the open and is proved by the
   shell lemma.  **No discharge is claimed**: the `hrung` deferral of
   `WRAPPER-REFERENCE-CONSTRUCTION-001` is unchanged by this tranche, because its
   residue is the endpoint (`A:285--329`) and not the routing.
6. **The poor-`u_don` cover folded** (§5): `exists_dense_donor_subset` runs the
   banked cover at `k = u_don`, `rho = rho_0`, `B = B_theta` and closes it with
   the banked `donors_survive_cover` arithmetic, producing exactly the frozen
   `09:1748--1749` sentence -- `u_don` surviving donors whose joint outer
   projection is not poor.

## Why `a^sharp = 1` at the frontier site, and `a^sharp = 0` at the low-rung site

This is the one place where the two certified calls of Section 9 visibly differ,
and the difference is *derived* here rather than transcribed.  At `09:322` the
low-rung call carries `a^sharp = 0`: its restriction is taken at the member
itself, whose column density is `theta` by the bracket.  At `09:1273` the
frontier call carries `a^sharp = 1`, and `09:1289--1290` says why -- "The denser
Bob child retains density at least `y^2`", half of the parent's `rho = 2y^2`.
`exists_denser_child_colFloor` proves that halving from the banked exact Bob mass
balance, so `RestrictionDatum.certifiedColFloor theta 1 = theta/2` is met at the
child by construction.  A single Bob step is exactly one factor of two, which is
exactly `a^sharp = 1`.

The halving is landed in the **column-set** form -- which is the form `A:141` and
`RestrictionDatum.colDens` are written in, and therefore the form the certified
call consumes -- and *not* in the projection form the frozen sentence is phrased
in.  That gap is GAP-EXPOSED item 7 of `ROUTED-CERTIFICATE-SYSTEM-001`, is
inherited here unchanged, and is neither closed nor narrowed by this tranche; no
declaration below is cited as discharging `09:1287--1290`.

## What is NOT done here, stated exactly

* **`eq:wrapper-u-dense` is not proved, and no route completion is claimed.**  No
  declaration below has `comp <U, 1, 1-delta_U, theta> >= C + r` -- in Lean,
  `FirstWrapperClose.DenseRung` -- as a conclusion, and none mentions `Dfamily`
  at the `1 - delta_U` bracket.
* **`hDenseRung` is FED, not discharged, and it falls only through the banked
  bridge at its pin.**  The bridge is
  `WrapperMassRedistribution.denseRung_of_no_shallow_member` (re-exported as
  `FirstWrapperClose.denseRung_of_no_shallow_member`), whose one open input is
  the per-member refutation `hmember`.  This module is **not** an instance of
  that bridge and deliberately does not restate it: consuming a banked interface
  means firing it where its input is available, and `hmember` is not available.
  What this module feeds toward it is the routing supply and the two certified
  restrictions the refutation needs at `09:1270--1274` and `09:311--327`.  The
  two residues that keep `hmember` out of reach are named, and neither is
  narrowed by anything below:
  * **the L1 construction** -- producing, from an arbitrary member of the bracket
    family and an arbitrary shallow protocol on it, a
    `RoutedCertificateSystem.RoutedSystem` with its protected-mass family.  Every
    theorem of §3 *begins* with a routed system already in hand, exactly as
    `OwnerFamilyToPigeonhole` records; this module inherits that residue
    unchanged and does not pretend to shorten it.
  * **the terminal lemma's proof** -- `TERMINAL-TWO-STREAM-001`, which is stated
    and not proved upstream.  §5 stops at the frozen `09:1749` sentence and does
    not enter `09:1750--1779`, whose close runs through that lemma and through
    the inherited Localized Extension corollary of Appendix D.
* **The one shell in the module is §4's, and it is NAMED rather than disguised.**
  `rung_of_referenceEndpoint`'s hypothesis bundle is at least as strong as its
  conclusion; it is proved by `shell_signature_forall_to_exists` and its docstring
  says outright that it discharges nothing.  Every §1--§3 and §5 deliverable is,
  by contrast, an existential produced from strictly weaker frozen data by an
  actual proof term.  The parked generation of this module asserted "no
  conditional shell" while carrying exactly one; that assertion is withdrawn and
  replaced by this paragraph and by the shell-signature gate.
* **The endpoint implication is the whole residue of §4, and the routing does not
  narrow it.**  `ReferenceStoppingEndpoint` is
  `thm:certified-localized-extension` at the `09:313--323` substitution; it is a
  binder here, is not proved anywhere in `src/`, and its canonical-inhabitation
  obligation stays REGISTERED and DEFERRED against
  `CERTIFIED-LOCALIZED-EXTENSION-001` with its proof the `A:285--329` residue.
  §4 removes **neither** half of the `hrung` deferral:
  `routedSupply_gives_only_inhabitation` proves that what the routing supplies to
  `hrung` is datum inhabitation, which
  `WrapperReferenceConstruction.referenceRestriction_nonempty` already banks.
* **The general form of the frozen theorem is not expressible in `src/`
  (successor `WDFW-F12`).**  Stating `thm:certified-localized-extension`
  universally over the ambient data `A:111--137` at a fixed readout is unsound in
  this encoding: `A:117`'s `t_cert <= t` with `t = 2^{k_t}` forces `2^20 <= k_t`,
  so `eq:certified-E3` demands `val >= 2 + 2^20` uniformly and demands more as the
  free `H` grows, while **no antecedent of `CertifiedExtensionEndpoint` mentions
  `val`**.  The cause is the banked `RestrictionDatum` abstraction -- a datum
  records its rectangle and its three `A:138--141` readouts, not the matrix it
  restricts -- so "the communication complexity of this restriction" has no Lean
  spelling and `val` must stay pinned at the call site.  This is a fact about
  `RESTRICTION-DATUM-001`'s interface, carried as a successor and not charged
  here.
* **`e_0` is not compared to the schedule here**, and the `09:455--457`
  asymptotic display is orientation-only by its own disclaimer at `09:458--459`;
  neither is formalized.
* **`R5` is not leaned on.**  The `r5_seven_binders_live` /
  `r5_eighth_binder_fails_here` audit pair of `MassLeavesOwner` is a NON-FIDELITY
  probe whose eighth item is provably false at that point; no declaration below
  consumes it, mentions it, or treats it as an inhabitant.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/A-stage4-details.tex`
(SHA-256 `5B6E9BA0E271D67BF2B0525BD6D59D90C150A8170BDCE29DC74DA55AB39019C6`),
opened first-hand this tranche.  **No reader item is claimed here**, and the
survey that establishes that is:

* the display at line `394`, `D_U(1; 1-delta_U, theta) >= C + r_q`, is precisely
  `eq:wrapper-u-dense`, which this module does **not** close; claiming it would
  be false, and `DenseWrapperFrontier` already records the same declination on
  the same ground;
* lines `370--399` are the reader's rung outline, every sentence of which sits
  inside the proof of `thm:paper-adapted-stage4-interface` and is therefore
  prose, which the reader-counterpart rule bars from carrying a statement.  Lines
  `371--373` ("the all-column reference follows every Bob query and its
  one-bit-down certificate prevents an early cheap termination") are the nearest
  sentences to §3 and are prose; lines `390--391` are **already assigned** to
  `TerminalTwoStream`;
* lines `361--368`, the reader's rung display, are the counterpart of
  `eq:wrapper-u-low` and are **already assigned** to
  `WrapperLowRungs.wrapperLowRungs`; §4 fires that statement rather than
  restating it, so reclaiming those lines would be a double assignment;
* the reader prints no `A_0`, no `A_k`, no `kappa_v`, no `W_v`, no `vartheta`, no
  `E_0`, no `u_don`, no restriction datum, no block count, no projection cover
  and no full-product clause at all.

Every declaration below therefore carries its autoformalization anchor alone.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the supply predicate, general (5): `routedTriple_rows_nonempty`,
  `routedTriple_blockCount`, `routedTriple_colFloor`,
  `routedTriple_mono_cols`, `routedTriple_weaken_aSharp`.
* `B` the built restriction, general (4): `routedRestriction_representedBlocks`,
  `routedRestriction_selCard`, `routedRestriction_rowsPerBlock`,
  `routedRestriction_colDens`.
* `C` the low-rung site, general (2): `lowRungRoutedRestriction_blockCount_frozen`,
  `lowRungRoutedRestriction_rowFloor_at_mG`.
* `D` the frontier supply, general (9): `exists_selected_blocks_at_heavy_node`,
  `exists_trimmed_reference_rows`, `exists_denser_child_colFloor`,
  `exists_frontier_routedTriple`; plus the `L1-F6` retirement battery
  `trim_positivity_iff_factors_positive` (the replacement binder is equivalent to
  the four **positivity facts entailed by** the ambient guards of
  `A:111--112`/`A:117--118`/`A:125` -- NOT to those guards themselves, which are
  strictly stronger; `WDFW-F14` renamed it to say so),
  `certifiedRowFloor_pos_iff_trim_positive` (it is necessary, not
  just sufficient), `certifiedRowFloor_mono_in_row_density`,
  `exists_trimmed_reference_rows_of_one` (the retired statement recovered
  verbatim as a corollary; **dead since `WDFW-F13`**, and kept deliberately as a
  labelled endpoint -- see its own docstring for the ruling)
  and `retired_hone_binder_is_strictly_stronger` (a
  rejection probe showing the weakening is strict).
* `E` the `hrung` binder and the SHELL-SIGNATURE gate, general (3):
  `shell_signature_forall_to_exists`, `routedSupply_gives_only_inhabitation`,
  `rung_of_referenceEndpoint`; plus the re-fired banked headline
  `wrapperLowRungs_of_referenceEndpoint`, which lands no content over the
  headline it fires and says so.
* `F` the poor-`u_don` cover fold, general (1): `exists_dense_donor_subset`.
* `G` statement poles and rejection probes (3):
  `routedTriple_colFloor_is_not_free`, `frontier_blockCount_needs_the_heavy_node`,
  `live_firstBob_node_is_not_heavy`.
* `H` LANE-GATE 3 non-vacuity at paper-derived values (5):
  `routedTriple_nondegenerate_at_legal_widths`,
  `frontier_blockCount_matches_heavy_ceiling` (NON-FIDELITY, see below),
  `routedSupply_shape_is_satisfiable`,
  `routedSupply_and_gate_set_jointly_satisfiable`,
  `endpoint_side_conditions_are_satisfiable`.

That is **32 battery entries proved**, with `0` unproved, of which four are
statement poles or rejection probes and five are non-vacuity results -- the last
two the hypothesis-consistency check for the routing supply, run at the frozen
carriers `[q]` and `[L]`, first over the *range* of legal widths and then at the
paper's own closed-form tested endpoint (`eq:kref-tested-endpoint`,
`06:588--589`), where the routing supply and the whole banked gate set are shown
to hold simultaneously for all three rungs; the fifth settles the two decidable
side conditions §4 adds and says outright that the third, `hendpoint`, is not
settled and cannot be here.

## Canonical inhabitation, and the two LANE-GATE 3 deferrals

`RoutedTriple` is a `Prop`, not a structure, so no new structure-inhabitation
obligation is created.  The obligations that *are* created are the inhabitation
of the predicate and of the frontier premise bundle, and both are handled as the
canonical-inhabitation rule demands -- one by the paper's own construction, one
by an explicit registered deferral:

* `routedSupply_shape_is_satisfiable` and
  `routedSupply_and_gate_set_jointly_satisfiable` inhabit the `09:313--323`
  supply at the paper's own tested widths, stated over the range rather than at a
  numeral because `t_ref` and `kappa` are quantities the frozen schedule defines.
  `routedTriple_nondegenerate_at_legal_widths` does the same for the `a^sharp = 1`
  index shape, with all three sides nonempty and both floors positive.
* `exists_frontier_routedTriple` is **not** labelled the paper's own instance
  (record fix F3).  It is an implication with `r'` and `t` free, whereas the
  paper's instance fixes `r' = kappa_v/t_ref` and `t = t_ref` (`09:1272`);
  `tRef` is banked and expressible, but `kappa_v = 2^{r-d_v}` (`09:1255`) has **no
  reification in `src/`** -- the nearest `def` is `WrapperLowRungs.kappaLow`, which
  reifies the *low-rung* `kappa_j = q/2^j` of `09:277--283` at the rung index `j`,
  a different index from the frontier depth `d_v`, and conflating them would be a
  DEFINED-vs-FREE defect.  So the canonical-inhabitation obligation for
  `RoutedTriple` **at the paper's own index tuple** is REGISTERED and DEFERRED,
  and the `kappa_v` reification is carried as successor `WDFW-F10`.
* The five-clause premise bundle of `exists_frontier_routedTriple` (`hheavy`,
  `hblocks`, `hpos`, `hA`, `hdens`) has its own LANE-GATE 3 obligation, and it is
  **DEFERRED against residue L1**: `hheavy` at a node's own defined `kappa_v`
  needs a routed system with a *heavy* first-Bob node, and
  `live_firstBob_node_is_not_heavy` shows by evaluation that neither banked live
  instance supplies one (`W_v = 1 < 9/8 = vartheta kappa_v` at the
  `FirstBobFrontierInstance` node, and `W_v = 1/2` at the `SplitFirstBobInstance`
  node at the same `kappa_v = 2`).  `frontier_blockCount_matches_heavy_ceiling`
  exhibits `hblocks` alone and is labelled **NON-FIDELITY** accordingly; it is not
  a substitute for the deferred obligation and its docstring says so.
* §3b's two deliverables are **unconsumed** in `src/` (successor `WDFW-F11`): the
  `a^sharp = 1` datum they build has an index shape no
  `CanonicalReferenceStoppingCall` accepts, that wrapper being pinned at
  `a^sharp = 0` (`CertifiedLocalizedExtension.lean:967`), and wiring them waits on
  branch (ii)'s `lem:certified-row-ladder`.  Nothing below over-claims on that
  account.

## Proof status and axiom surface

New (the routing supply and the frontier construction) over adapted pins.
Imports: `WrapperReferenceConstruction` and `FirstWrapperAssembly` only, whose
closures carry every pin listed above.  `#print axioms` on every declaration
below is recorded in `tools/AxiomAudit.lean`; the surface is `propext`,
`Classical.choice`, `Quot.sound` only.

## HYPOTHESIS-CONSISTENCY note

`wrapperLowRungs_of_referenceEndpoint` conjoins the hypotheses of the banked
`wrapperLowRungs_at_referenceConstruction` -- machine-checked jointly satisfiable
at the paper's own tested endpoint by the banked
`referenceCall_full_gate_set_is_satisfiable` -- with exactly three additions,
`hBlk`, `hinh` and `hendpoint`.

`hBlk` is `A:138`'s "of `\widehat M`" read through `def:relaxed-interlace`
(`03:295--304`) and is satisfied by the frozen block carrier `[q] = Fin (2^{k_q})`
itself; `hinh` is satisfiable at legal widths by
`routedTriple_nondegenerate_at_legal_widths` and at the `09:313--323` indices by
`routedSupply_shape_is_satisfiable` together with
`routedSupply_gives_only_inhabitation`, and is in any case banked as
`WrapperReferenceConstruction.referenceRestriction_nonempty`.

**`hendpoint`'s consistency is exactly the open question, and is not asserted
here (record fix F1).**  It is `thm:certified-localized-extension` at the
`09:313--323` substitution; its truth is the frozen appendix proof `A:285--329`,
the registered residue.  What *is* checked is that it is not vacuously
false for a shape reason: the readout it bounds is the member's own
`D (subgame ...)`, pinned at the call site rather than universally quantified,
which is precisely the pinning `WDFW-F12` above records as unavoidable.  A form
of the endpoint that quantified over the ambient data `A:111--137` at a fixed
readout would be refutable outright, since `A:117` forces `2^20 <= k_t` and hence
`val >= 2 + 2^20` uniformly; that form is therefore **not** used.

Nothing below conjoins a `YES` clause with a `NO` clause, and nothing conjoins
two branches of the terminal dispatch.
-/

namespace EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring

open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.HardSeedFacade
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.CertifiedLocalizedExtension
open EthInapproximability.ParameterizedNP.WrapperLowRungAssembly
open EthInapproximability.ParameterizedNP.WrapperReferenceConstruction
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance
open EthInapproximability.ParameterizedNP.LargeCapacityBranch
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers

/-! ## §1  The routing supply `(S, T, K)` (`A:138--141` as the routing hands it)

`WrapperReferenceConstruction.productRestriction` takes three Finsets and four
facts about them.  This section names that package once, so that the frontier can
*produce* it and the certified call can *consume* it without either side quoting
the other's clause list.

It is a `Prop`-valued `def` and not a structure: nothing is bundled that is not
already a hypothesis of the banked constructor, and no derived telescope is
restated. -/

section Supply

variable {Blk Row Col : Type*} [Fintype Row] [Fintype Col]

/-- **The routed triple's four clauses (`A:138--141` at one node), named.**

`S` is the selected outer coordinate set, `T` the retained (trimmed) reference
rows, `K` the retained columns.  The four clauses are, in the frozen order:

* `T` is nonempty -- without it the rectangle `S x T` represents no block at all
  (the banked `WrapperReferenceConstruction.productRestriction_rejects_empty_rows`,
  consumed by pin -- record fix F4);
* `A:138--139`: exactly `r' p_t` represented outer blocks;
* `A:139--140`: at least `ceil(r' t x m)` rows in each represented block, with
  `m = |Row|` read at the carrier and never at a free natural;
* `A:141`: column density at least `h 2^{-a^sharp}`.

General in the three carriers and in `r'`, `t`, `a^sharp`, `x`, `h`; the two
frozen sites -- `09:313--323` at `a^sharp = 0` and `09:1270--1274` at
`a^sharp = 1` -- are substitutions of this one predicate. -/
def RoutedTriple (r' t aSharp : ℕ) (x h : ℝ)
    (S : Finset Blk) (T : Finset Row) (K : Finset Col) : Prop :=
  T.Nonempty
    ∧ S.card = r' * RestrictionDatum.certifiedPt t
    ∧ RestrictionDatum.certifiedRowFloor r' t x (Fintype.card Row) ≤ T.card
    ∧ RestrictionDatum.certifiedColFloor h aSharp
        ≤ (K.card : ℝ) / (Fintype.card Col : ℝ)

/-- **Aux A1 (the row side of a supply is nonempty).**  General. -/
theorem routedTriple_rows_nonempty {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K) :
    T.Nonempty := htr.1

/-- **Aux A2 (`A:138`'s census readout of a supply).**  General. -/
theorem routedTriple_blockCount {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K) :
    S.card = r' * RestrictionDatum.certifiedPt t := htr.2.1

/-- **Aux A3 (`A:141`'s density readout of a supply).**  General. -/
theorem routedTriple_colFloor {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K) :
    RestrictionDatum.certifiedColFloor h aSharp
      ≤ (K.card : ℝ) / (Fintype.card Col : ℝ) := htr.2.2.2

/-- **Aux A4 (monotonicity in the retained column set).**

Enlarging the retained columns can only help `A:141`, so a supply survives any
enlargement of `K`.  This is the direction the frozen argument uses when it
passes from a node to its *parent* and asserts the parent projection is at least
as dense.  General. -/
theorem routedTriple_mono_cols {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K K' : Finset Col} (hKK : K ⊆ K')
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K) :
    RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K' := by
  refine ⟨htr.1, htr.2.1, htr.2.2.1, le_trans htr.2.2.2 ?_⟩
  have hcard : (K.card : ℝ) ≤ (K'.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hKK
  have hden : (0 : ℝ) ≤ (Fintype.card Col : ℝ) := Nat.cast_nonneg _
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hden)

/-- **Aux A5 (`A:129`'s `a^sharp` is a weakening direction).**

A supply at `a^sharp = 0` is a supply at `a^sharp = 1`, because `h/2 <= h/1`
whenever `h >= 0`.  This records the *direction* of the frozen difference between
the two certified calls: `09:1273`'s `a^sharp = 1` is strictly weaker on the
column side than `09:322`'s `a^sharp = 0`, which is why the denser-Bob-child
halving of `09:1289--1290` suffices for it.  General. -/
theorem routedTriple_weaken_aSharp {r' t : ℕ} {x h : ℝ} (hh : 0 ≤ h)
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t 0 x h S T K) :
    RoutedTriple (Blk := Blk) (Col := Col) r' t 1 x h S T K := by
  refine ⟨htr.1, htr.2.1, htr.2.2.1, le_trans ?_ htr.2.2.2⟩
  rw [RestrictionDatum.certifiedColFloor, RestrictionDatum.certifiedColFloor]
  norm_num
  linarith

end Supply

/-! ## §2  The restriction the supply builds (`09:326`, `A:138--141`)

The banked full-product constructor, fired at a supply.  Every clause of
`A:138--141` becomes a *proved* readout of the built object rather than a second
hypothesis. -/

section Built

variable {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]

/-- **The routed restriction, BUILT.**

`WrapperReferenceConstruction.productRestriction` at a supply.  Nothing is chosen
here: `S`, `T`, `K` come from the routing and the three legality facts come from
`RoutedTriple`.  General in the carriers and in every index. -/
def routedRestriction {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) :
    RestrictionDatum.RestrictionDatum Blk Row Col r' t aSharp x h :=
  productRestriction S T K htr.1 htr.2.1 htr.2.2.1 htr.2.2.2 hh0 hh1 ha

/-- **Aux B1 (`A:138`'s represented blocks of the routed restriction).**

The rectangle represents exactly the selected outer coordinates -- the banked
`representedBlocks_product` at the supply.  General. -/
theorem routedRestriction_representedBlocks {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) :
    RestrictionDatum.representedBlocks (routedRestriction htr hh0 hh1 ha).rowSet = S :=
  representedBlocks_product htr.1

/-- **Aux B2 (`A:138`'s census returns the frozen count).**  General. -/
theorem routedRestriction_selCard {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) :
    (routedRestriction htr hh0 hh1 ha).selCard = r' * RestrictionDatum.certifiedPt t :=
  productRestriction_selCard S T K htr.1 htr.2.1 htr.2.2.1 htr.2.2.2 hh0 hh1 ha

/-- **Aux B3 (`A:139--140`, and why the balancedness error is exactly `0`).**

Every represented block holds the *same* row set, so the minimum fibre size is
the common value `|T|`.  That equality is the Lean content of `09:326`'s "the
reference restriction is a full product, so its balancedness error is exactly
zero", now read at the routing's own `T`.  General; the hypothesis is that at
least one outer coordinate is selected. -/
theorem routedRestriction_rowsPerBlock {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) (hS : S.Nonempty) :
    (routedRestriction htr hh0 hh1 ha).rowsPerBlock = T.card :=
  productRestriction_rowsPerBlock S T K htr.1 htr.2.1 htr.2.2.1 htr.2.2.2 hh0 hh1 ha hS

/-- **Aux B4 (`A:141`'s density readout).**  General. -/
theorem routedRestriction_colDens {r' t aSharp : ℕ} {x h : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col) r' t aSharp x h S T K)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (ha : aSharp ≤ 1) :
    (routedRestriction htr hh0 hh1 ha).colDens
      = (K.card : ℝ) / (Fintype.card Col : ℝ) :=
  productRestriction_colDens S T K htr.1 htr.2.1 htr.2.2.1 htr.2.2.2 hh0 hh1 ha

end Built

/-! ## §3a  The low-rung site (`09:311--327`), at the routing's own triple

The banked `referenceRestriction` fired at a supply, so that the object the
certified call of `09:313--323` is made at is now produced by the routing rather
than assumed to exist. -/

section LowRungSite

variable {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]

/-- **The `09:313--323` restriction at the routing's triple, BUILT.**

`WrapperReferenceConstruction.referenceRestriction` fired at a supply indexed by
the substitution display's own widths, `r' = kappa_j/t_ref` and `t = t_ref`, at
`a^sharp = 0` (`09:322`).  General in the carriers and in `k_q`, `k_ref`, `j`,
`x_T`, `theta`. -/
def lowRungRoutedRestriction (kq kref j : ℕ) {xT θ : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col)
      (refRungCopies kq kref j) (tRef kref) 0 xT θ S T K)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    RestrictionDatum.RestrictionDatum Blk Row Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ :=
  referenceRestriction kq kref j S T K htr.1 htr.2.1 htr.2.2.1
    (by
      have hden : RestrictionDatum.certifiedColFloor θ 0 = θ := by
        rw [RestrictionDatum.certifiedColFloor]; norm_num
      have := htr.2.2.2
      rwa [hden] at this)
    hθ0 hθ1

end LowRungSite

section LowRungReadouts

variable {Blk Row Col : Type*} [Fintype Row] [Fintype Col]

/-- **`09:311--312` at the routing's triple, PROVED.**

The number of outer coordinates the routing must select is not a number chosen
here: it is the frozen `9 kappa_j/16` of `09:311`, reached by evaluating the
substitution through the banked `refBlockCount_eq_certifiedPt_kappa`.  General at
the frozen ranges. -/
theorem lowRungRoutedRestriction_blockCount_frozen {kq kref j : ℕ} {xT θ : ℝ}
    {S : Finset Blk} {T : Finset Row} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col)
      (refRungCopies kq kref j) (tRef kref) 0 xT θ S T K)
    (hk : 4 ≤ kref) (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) :
    S.card = RestrictionDatum.certifiedPt (kappaLow kq j) := by
  rw [htr.2.1]
  exact refBlockCount_eq_certifiedPt_kappa hk hj hq4

/-- **`A:139--140`'s row floor of the routing's triple is read at `m_G`, PROVED.**

At the reference construction the endpoint's `m` is `m_G = |Omega| w_0` (`09:113`
with `09:116`), so the row count the routing must retain in each selected
coordinate is the frozen `ceil(kappa_j x_T m_G)` -- the banked
`referenceRowFloor_at_mG` read at the supply.  General in the reservoir carrier,
the base multiplicity, and every schedule parameter. -/
theorem lowRungRoutedRestriction_rowFloor_at_mG (Om : Type*) [Fintype Om] (w₀ : ℕ)
    {Col : Type*} [Fintype Col] {kq kref j : ℕ} {xT θ : ℝ}
    {S : Finset Blk} {T : Finset (Om × Fin w₀)} {K : Finset Col}
    (htr : RoutedTriple (Blk := Blk) (Col := Col)
      (refRungCopies kq kref j) (tRef kref) 0 xT θ S T K)
    (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq) :
    ⌈((kappaLow kq j : ℕ) : ℝ) * xT * ((Fintype.card Om * w₀ : ℕ) : ℝ)⌉₊ ≤ T.card := by
  have hfloor := htr.2.2.1
  rwa [referenceRowFloor_at_mG Om w₀ hj hq4] at hfloor

end LowRungReadouts

/-! ## §3b  The frontier supply itself (`09:1268--1296`)

This is the routing.  At a heavy first-Bob node of a routed certificate system,
the three sides of the triple are produced:

* the block side from the frozen census `09:1278--1281`;
* the row side from the frozen trim `09:1291--1296`;
* the column side from the frozen denser-Bob-child halving `09:1287--1290`,
  which is exactly the `a^sharp = 1` of `09:1273`.

Every input below is a frozen fact about the routed system; nothing is a
`RestrictionDatum` in disguise, and no conclusion is assumed on either side. -/

section FrontierSupply

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1268--1269` with `09:1280--1281`: the block side of the triple, SELECTED.**

"We first close any first-Bob node satisfying `W_v >= vartheta kappa_v`" together
with "the number of represented coordinates is at least `ceil(W_v)`" gives at
least `9 kappa_v/16` represented coordinates, and `09:1268` then *selects*
exactly the number `A:138` demands.  The selection is a genuine
`Finset.exists_subset_card_eq` inside the census, not a fresh set: every selected
coordinate is one the routing actually represents at `v`.

The banked `heavy_blockCount_le_card_representedCoords` supplies the census
bound; what is added is the selection and its comparison with `A:138`'s demand.

*Why the trivial witness fails.*  `S = empty` has card `0`, and the demanded
count `r' p_t` is positive throughout the frozen range (`A:125` makes `r'` a
positive power of two, and `A:117` with `A:120` jointly make `p_t > 0` --
`A:117` fixes `t >= t_cert` a power of two divisible by `16` and `A:120` is the
`p_t = 9t/16` display), so the empty selection is
refuted outright -- see `frontier_blockCount_needs_the_heavy_node`.

General in `P`, `Coord`, `R`, `A_0`, `r`, the node, and the two widths. -/
theorem exists_selected_blocks_at_heavy_node (P : Workspace.Types.Protocol.Protocol X Y Z)
    (R : Coord → Finset X) (A0 r : ℕ) (v : FrontierNode P R A0 r) {κ : ℝ} {r' t : ℕ}
    (hheavy : vartheta * κ ≤ frontierWeight P R A0 r v)
    (hblocks : ((r' * RestrictionDatum.certifiedPt t : ℕ) : ℝ) ≤ 9 * κ / 16) :
    ∃ S ⊆ representedCoords P R A0 r v,
      S.card = r' * RestrictionDatum.certifiedPt t := by
  have hcensus := heavy_blockCount_le_card_representedCoords P R A0 r v hheavy
  have hle : r' * RestrictionDatum.certifiedPt t
      ≤ (representedCoords P R A0 r v).card := by
    exact_mod_cast le_trans hblocks hcensus
  exact Finset.exists_subset_card_eq hle

/-- **`09:1291--1296`: the row side of the triple, TRIMMED.**

"Each selected certificate has at least `A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T
m_G` reference rows, so trim it to the row density `kappa_v x_T`."  The frozen
factor `2` is the whole content: it is what makes the trim to the exact floor
`ceil(r' t x m)` possible inside the certificate, and it is carried here as the
hypothesis `hA` rather than assumed away.

**`L1-F6`, DISCHARGED here: the `hone` binder is retired.**  The parked
signature carried `hone : kappa_v x_T m_G >= 1` and its docstring called that
"the frozen regime".  It is not one.  `09:1291--1296` states only the
`A_{ell_v} = kappa_v A_0 >= 2 kappa_v x_T m_G` row count, and a first-hand search
of the frozen `09-first-wrapper.tex` finds the product `x_Tm_G` at exactly three
lines -- `09:1219`, `09:1294`, `09:1327` -- none of them a `>= 1` display.  What
the proof actually consumes is `r' t x m > 0`, and *that* is **entailed by** the
ambient guards of the theorem being invoked: `A:111--112`'s "let `M` be a
**nonempty** Boolean matrix with `m` rows" together with `0 < x <= 1`,
`A:117--118`'s `t >= t_cert` a power of two divisible by `16`, and `A:125`'s "let
`r, r'` be positive powers of two".  So the binder below is paper-supplied where
the retired one was not.  The entailment is one-way and only that direction is
used: positivity does not give back "power of two", "divisible by `16`",
"`>= t_cert`" or "`x <= 1`".

The weakening is **minimal, not merely convenient**:
`trim_positivity_iff_factors_positive` proves `hpos` equivalent to the four
*positivity facts* those guards entail (not to the guards themselves), and
`certifiedRowFloor_pos_iff_trim_positive` proves it
*necessary* -- drop it and the conclusion's own nonemptiness clause becomes false,
not merely unprovable.  Nothing in the conclusion moves: it is still
`RestrictionDatum.certifiedRowFloor r' t x m`, i.e. `ceil(r' t x m)`
(`RestrictionDatum.lean:247`), which is `A:140` verbatim.  Every pre-retirement
caller was served unchanged by `exists_trimmed_reference_rows_of_one` -- and
since `WDFW-F13` (tranche `cc-t5i`) retired the paper-shaped binder from the two
downstream statements as well, there is no such caller left and that corollary is
a deliberately kept dead endpoint rather than a live compatibility shim; and
`retired_hone_binder_is_strictly_stronger` exhibits a point where the retired
binder fails while this one holds, so the retirement is a strict weakening rather
than a rename.

*Why the trivial witness fails.*  The deliverable asks for a subset of the
certificate's own rows whose card is **exactly** the floor; the empty set has
card `0`, which the conclusion's second clause refutes because `hpos` forces the
floor to be at least `1` (`certifiedRowFloor_pos_iff_trim_positive`).

General in the row carrier and in all four numerals. -/
theorem exists_trimmed_reference_rows {Row : Type*}
    {r' t m : ℕ} {x : ℝ} {A : Finset Row}
    (hpos : 0 < ((r' * t : ℕ) : ℝ) * x * (m : ℝ))
    (hA : 2 * (((r' * t : ℕ) : ℝ) * x * (m : ℝ)) ≤ (A.card : ℝ)) :
    ∃ T ⊆ A, T.card = RestrictionDatum.certifiedRowFloor r' t x m ∧ T.Nonempty := by
  set z : ℝ := ((r' * t : ℕ) : ℝ) * x * (m : ℝ) with hz
  have hzpos : (0 : ℝ) < z := hpos
  have hzle : z ≤ (A.card : ℝ) := by linarith
  have hceil : RestrictionDatum.certifiedRowFloor r' t x m ≤ A.card := by
    rw [RestrictionDatum.certifiedRowFloor]
    exact Nat.ceil_le.mpr hzle
  obtain ⟨T, hTA, hTcard⟩ := Finset.exists_subset_card_eq hceil
  refine ⟨T, hTA, hTcard, ?_⟩
  rw [← Finset.card_pos, hTcard, RestrictionDatum.certifiedRowFloor]
  exact Nat.ceil_pos.mpr hzpos

/-- **Aux D5 (`A:111--112`, `A:117--118`, `A:125`: the retirement's replacement
binder is exactly the POSITIVITY those ambient guards entail).**

`hpos` is not a fifth hypothesis smuggled in where `hone` left: it is the
conjunction of the four positivity facts *entailed by* what the invoked theorem
already fixes before any restriction is spoken of -- `r'` a positive power of two
(`A:125`), `t` a power of two divisible by `16` and at least `t_cert`
(`A:117--118`), `m` the row count of a **nonempty** matrix (`A:111`), and
`0 < x <= 1` (`A:112`).

**Read the `iff` exactly.**  The right-hand side is `0 < r' /\ 0 < t /\ 0 < m /\
0 < x`, i.e. the four *positivity* facts -- **not** the guards themselves, which
are strictly stronger.  Positivity does not return "power of two", "divisible by
`16`", "`>= t_cert`" or "`x <= 1`".  Only the guards-give-`hpos` direction is
consumed by the retirement argument; the converse recorded here says merely that
`hpos` cannot hold with any factor vanishing, because `r' t` and `m` enter as
`Nat` casts and therefore cannot be negative.

**`WDFW-F14`, DISCHARGED (tranche `cc-t5i`): the name now says this.**  The
banked name was `trim_positivity_iff_ambient_guards`, which invited the inverted
reading just refused above -- the `iff` is with the four *factor positivities*,
never with the ambient guards.  The banked name is **not** kept as an alias, and
the statement bytes below are byte-identical to the banked ones: only the
identifier moved.

General in all four quantities; no numeral is assigned to any of them. -/
theorem trim_positivity_iff_factors_positive {r' t m : ℕ} {x : ℝ} :
    0 < ((r' * t : ℕ) : ℝ) * x * (m : ℝ) ↔ (0 < r' ∧ 0 < t ∧ 0 < m ∧ 0 < x) := by
  constructor
  · intro h
    have hrt0 : r' * t ≠ 0 := by
      intro hzero
      rw [hzero] at h
      simp at h
    have hm0 : m ≠ 0 := by
      intro hzero
      rw [hzero] at h
      simp at h
    have hrt' : 0 < r' * t := Nat.pos_of_ne_zero hrt0
    have hrtR : (0 : ℝ) < ((r' * t : ℕ) : ℝ) := by exact_mod_cast hrt'
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hx : 0 < x := by
      by_contra hxle
      push Not at hxle
      nlinarith [mul_nonneg (mul_pos hrtR hmR).le (neg_nonneg.mpr hxle)]
    exact ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hrt'),
      Nat.pos_of_ne_zero (by rintro rfl; simp at hrt'),
      Nat.pos_of_ne_zero hm0, hx⟩
  · rintro ⟨hr, ht, hm, hx⟩
    have hrtR : (0 : ℝ) < ((r' * t : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hr ht
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    exact mul_pos (mul_pos hrtR hx) hmR

/-- **Aux D6 (`A:140`: the replacement binder is NECESSARY, not just sufficient).**

The floor `ceil(r' t x m)` of `A:139--140` is positive **iff** `r' t x m` is, so
the retained binder is precisely the condition under which the conclusion's own
`T.Nonempty` clause can hold at all: weakening it any further would make the
deliverable false rather than unprovable.  This is what makes `L1-F6` a
retirement of a redundant hypothesis and not a loosening of the statement.

General in all four quantities. -/
theorem certifiedRowFloor_pos_iff_trim_positive {r' t m : ℕ} {x : ℝ} :
    0 < RestrictionDatum.certifiedRowFloor r' t x m
      ↔ 0 < ((r' * t : ℕ) : ℝ) * x * (m : ℝ) := by
  rw [RestrictionDatum.certifiedRowFloor]
  exact Nat.ceil_pos

/-- **Aux D7 (`A:140` is monotone in the row density).**

A larger `x` never demands fewer rows per represented block.  The frozen call
substitutes `x = x_T` (`08:166`) and `09:1291--1296` trims "to the row density
`kappa_v x_T`", so this is the sense in which the trim tracks the density it is
named after.  It needs no positivity: `r' t` and `m` are `Nat` casts.

General in `r'`, `t`, `m` and both densities. -/
theorem certifiedRowFloor_mono_in_row_density {r' t m : ℕ} {x y : ℝ} (h : x ≤ y) :
    RestrictionDatum.certifiedRowFloor r' t x m
      ≤ RestrictionDatum.certifiedRowFloor r' t y m := by
  rw [RestrictionDatum.certifiedRowFloor, RestrictionDatum.certifiedRowFloor]
  refine Nat.ceil_mono ?_
  have h1 : (0 : ℝ) ≤ ((r' * t : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (mul_nonneg h1 h2) (sub_nonneg.mpr h)]

/-- **Aux D8 (the retired form, recovered verbatim as a corollary).**

The pre-`L1-F6` statement of `exists_trimmed_reference_rows`, byte-for-byte in
its hypothesis `hone` and in its conclusion, obtained from the retired-binder
form in one step.  This is the machine-checked content of "call sites lose
nothing": any consumer that had `kappa_v x_T m_G >= 1` in hand still gets the
identical trim, because `1 <= z` forces `0 < z`.

**DISPOSITION after `WDFW-F13` (tranche `cc-t5i`): this corollary is now DEAD,
and is KEPT deliberately as a labelled endpoint.**  It was introduced to serve
the callers that still carried the paper-shaped `hone` when `L1-F6` retired that
binder from the theorem above.  `WDFW-F13` has since retired `hone` from
`TranscriptLevelConstruction.exists_frontier_routedTriple_at_paper_indices` and
from `TranscriptLevelSuccessors.exists_frontier_routedTriple_at_paper_schedule`,
so **no such caller remains**: a first-hand census of `src/` taken in that
tranche finds this identifier only at its own head and in prose.  The two
possible dispositions were weighed and the ruling is recorded here rather than
left implicit.

* **Not deleted, because it is not a duplicate.**  The deletion `L1-F9` performed
  in the same tranche removed a statement *logically equivalent* to a banked one,
  where a second name splits one interface in two.  This corollary is instead
  **strictly weaker** than the theorem above -- its hypothesis is strictly
  stronger, as `retired_hone_binder_is_strictly_stronger` exhibits at an explicit
  point -- so it creates no competing interface: a consumer that pinned it would
  get less than the bank, never something divergent from it.
* **Kept, because it is the retirement's own evidence.**  It is the pre-`L1-F6`
  statement preserved byte-for-byte, and it is the machine-checked answer to the
  question a later reader will ask -- was the paper-shaped binder *discarded* or
  *discharged*?  The frozen `09:1291--1296` states only the row count
  `A_{ell_v} >= 2 kappa_v x_T m_G` and never a `>= 1` display, so the honest
  record is that the binder was never the paper's; this corollary is where that
  is checked rather than asserted.  Retired material in this repository is
  preserved with its witness, not removed to make a census tidy.
* **What "dead" therefore means here.**  Zero proof consumers, by design and not
  by oversight, and no successor is registered to give it one.  Anything that
  needs the trim consumes `exists_trimmed_reference_rows` directly.

*Why the trivial witness fails.*  The same pole as the theorem it fires:
`T = empty` has card `0` while the demanded card is `ceil(r' t x m)`, which
`hone` puts at `1` or above through
`certifiedRowFloor_pos_iff_trim_positive`.

General in the row carrier and in all four quantities. -/
theorem exists_trimmed_reference_rows_of_one {Row : Type*}
    {r' t m : ℕ} {x : ℝ} {A : Finset Row}
    (hone : 1 ≤ ((r' * t : ℕ) : ℝ) * x * (m : ℝ))
    (hA : 2 * (((r' * t : ℕ) : ℝ) * x * (m : ℝ)) ≤ (A.card : ℝ)) :
    ∃ T ⊆ A, T.card = RestrictionDatum.certifiedRowFloor r' t x m ∧ T.Nonempty :=
  exists_trimmed_reference_rows (lt_of_lt_of_le zero_lt_one hone) hA

/-- **Aux D9, a REJECTION PROBE: the retirement is a STRICT weakening.**

Two facts.  First, in general, the retired binder implies the retained one, which
is the direction Aux D8 consumes.  Second, at `r' = 1`, `t = 2^4`, `m = 16` and
`x = xTdepth 10 = 2^{-10}` (`08:166`) the product is `16 . 2^{-10} . 16 = 1/4`:
the retained binder holds and the retired one **fails**.  So `L1-F6` removes a
hypothesis that genuinely constrained the statement; it is not a rename, and
`exists_trimmed_reference_rows` is strictly stronger than the statement it
replaces.

**Self-chosen values, claiming NO legality.**  `b_T = 10`, `m = 16`, `t = 2^4`
and `r' = 1` are ours.  This is a rejection probe: `A:117` with `A:26` forces
`t >= t_cert` far above `2^4`, so the tuple is illegal by design, which is
exactly what a probe exhibiting the failure of a hypothesis is allowed -- and
required -- to be.  It is **not** an instance of the theorem and discharges no
inhabitation obligation. -/
theorem retired_hone_binder_is_strictly_stronger :
    (∀ {r' t m : ℕ} {x : ℝ}, 1 ≤ ((r' * t : ℕ) : ℝ) * x * (m : ℝ) →
        0 < ((r' * t : ℕ) : ℝ) * x * (m : ℝ))
      ∧ 0 < (((1 * 2 ^ 4 : ℕ)) : ℝ) * xTdepth 10 * ((16 : ℕ) : ℝ)
      ∧ ¬ (1 ≤ (((1 * 2 ^ 4 : ℕ)) : ℝ) * xTdepth 10 * ((16 : ℕ) : ℝ)) := by
  refine ⟨fun h => lt_of_lt_of_le zero_lt_one h, ?_, ?_⟩
  · norm_num [xTdepth]
  · norm_num [xTdepth]

end FrontierSupply

section FrontierCols

variable {X Y Z : Type*} [Fintype Y] [DecidableEq Y]

/-- **`09:1287--1290` in its COLUMN-SET form: the column side of the triple at
`a^sharp = 1`.**

"The denser Bob child retains density at least `y^2`" -- half of the parent's
`rho = 2y^2`.  At a Bob query the two children split the retained column set
*exactly* (the banked `card_bobCols_children_add`), so one of them keeps at least
half; `RestrictionDatum.certifiedColFloor theta 1 = theta/2` is therefore met at
that child by construction.  Here `theta` stands for the parent's density; at the
frozen call it is instantiated at `rho = 2y^2` and the conclusion is the frozen
`y^2`.

This is what `a^sharp = 1` measures at `09:1273`, against `09:322`'s
`a^sharp = 0`: one Bob step is exactly one factor of two.  The value is not
transcribed here, it is produced.

**Scope, inherited verbatim from the banked `exists_denser_bob_child`
(GAP-EXPOSED item 7 of `ROUTED-CERTIFICATE-SYSTEM-001`).**  The frozen sentence
at `09:1287--1290` is about the *projection* `projSet J` of the retained column
set, not about the column set itself.  This is the column-set analogue that
argument runs on -- which is also the form `A:141` and
`RestrictionDatum.colDens` are written in, so it is the form the certified call
consumes -- but it must **not** be cited as discharging `09:1287--1290`.  The
projection form remains unlanded, exactly as the banked module records; this
tranche neither closes it nor narrows it.

*Why the trivial witness fails.*  Neither bit is a uniform witness -- a Bob
predicate may send every column to one child -- so the existential genuinely
quantifies; the banked `denserChild_needs_the_right_bit` exhibits a query at
which `false` fails outright.

General in the three carriers, in the ambient column family and in `theta`. -/
theorem exists_denser_child_colFloor {P : Workspace.Types.Protocol.Protocol X Y Z}
    {p : List Bool} (h : DenseWeightedCount.IsBobNode (DenseWeightedCount.descend P p))
    (Sc : Finset Y) {θ : ℝ} (hY : 0 < Fintype.card Y)
    (hdens : θ ≤ ((retainedCols P Sc p).card : ℝ) / (Fintype.card Y : ℝ)) :
    ∃ b : Bool, RestrictionDatum.certifiedColFloor θ 1
      ≤ (((retainedCols P Sc (p ++ [b])).card : ℝ) / (Fintype.card Y : ℝ)) := by
  obtain ⟨b, hb⟩ := exists_denser_bob_child h Sc
  refine ⟨b, ?_⟩
  have hbR : ((retainedCols P Sc p).card : ℝ)
      ≤ 2 * ((retainedCols P Sc (p ++ [b])).card : ℝ) := by
    have := hb
    simp only [retainedCols]
    exact_mod_cast this
  have hYR : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hpar : θ * (Fintype.card Y : ℝ) ≤ ((retainedCols P Sc p).card : ℝ) :=
    (le_div_iff₀ hYR).mp hdens
  have hchain : θ * (Fintype.card Y : ℝ)
      ≤ 2 * ((retainedCols P Sc (p ++ [b])).card : ℝ) := le_trans hpar hbR
  rw [RestrictionDatum.certifiedColFloor, pow_one, le_div_iff₀ hYR]
  have hcomm : θ / 2 * (Fintype.card Y : ℝ) = θ * (Fintype.card Y : ℝ) / 2 := by ring
  rw [hcomm]
  linarith [hchain]

end FrontierCols

section FrontierTriple

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {Coord : Type} [Fintype Coord]

/-- **`09:1268--1296`: the routed triple of the dense frontier, BUILT.**

The three sides of the previous three theorems, assembled into one
`RoutedTriple` at `a^sharp = 1` -- i.e. at the `09:1270--1274` certified call
"follow the denser Bob child and invoke the certified-scale reference
stopping lemma on `G` with `r' = kappa_v/t_ref`, `a^sharp = 1`".

It is produced from frozen data alone: the heavy condition of `09:1268--1269`,
the reference-row count of `09:1291--1296`, and the parent column density of
`09:1287--1290`.  The selected coordinates are a subset of the node's actual
census, and the retained rows a subset of the certificate's actual rows -- neither
is a synthetic Finset.

**This is NOT labelled the paper's own instance (record fix F3).**  It is an
implication with `r'` and `t` free, whereas the paper's instance fixes
`r' = kappa_v/t_ref` and `t = t_ref` (`09:1272`).  `tRef` is banked and
expressible, but `kappa_v = 2^{r-d_v}` (`09:1255`) has no reification in `src/` --
`WrapperLowRungs.kappaLow` reifies the *low-rung* `kappa_j = q/2^j` of
`09:277--283`, at the rung index `j`, not at the frontier depth `d_v`.  So the
canonical-inhabitation obligation at the paper's own index tuple is REGISTERED
and DEFERRED, and the `kappa_v` reification is successor `WDFW-F10`.  `kappa`
appearing here as a free real is the convention inherited verbatim from the
banked `LargeCapacityBranch.heavy_blockCount_le_card_representedCoords`.

**Branch attribution (record fix F2).**  The assembled object is branch (i)'s
(`09:1269--1275`, `kappa_v >= t_ref`, `a^sharp = 1`); the census ingredient
`09:1280--1281` with `09:1287--1290` and the trim ingredient `09:1291--1296` are
printed in branch (ii)'s paragraph (`09:1276--1300`, `2 <= kappa_v < t_ref`),
whose own close is `lem:certified-row-ladder` rather than the reference stopping
lemma.  Each ingredient is derivable at branch (i) too -- the census bound
depends only on `09:1268`'s heavy condition, not on the `kappa_v` split -- so the
branch-neutral statement below is not thereby false; the reading outside the
frozen paragraph is recorded rather than left implicit.

What it is still conditional on is the routed system `P`, `R`, `v` being in hand,
which is the registered residue L1 (the transcript-level construction from an
arbitrary shallow protocol on an arbitrary bracket member) and is not narrowed
here.  Its column clause is supplied in the column-set form (see
`exists_denser_child_colFloor`'s scope paragraph); the projection form of
`09:1287--1290` stays GAP-EXPOSED.  Its five-clause premise bundle carries its own
LANE-GATE 3 obligation, DEFERRED against L1 -- see
`frontier_blockCount_matches_heavy_ceiling` and
`live_firstBob_node_is_not_heavy`.

**`L1-F6` at the consumer.**  The row clause of the bundle is now `hpos`, the
`r' t x m > 0` that `A:111--112`/`A:117--118`/`A:125` entail, where the parked
generation demanded
`hone : kappa_v x_T m_G >= 1` -- a display the frozen `09-first-wrapper.tex` does
not contain.  The conclusion is untouched; the theorem is strictly stronger; and
any caller holding the retired binder still applies it, since `1 <= z` gives
`0 < z`.  See `exists_trimmed_reference_rows` for the retirement and Aux D5--D9
for its minimality, necessity and strictness.

*Why the trivial witness fails.*  Every clause is a lower bound on a card or a
density that the degenerate choices (`S = empty`, `T = empty`, `K = empty`) all
violate at the frozen positive counts -- see the poles of §6 and the banked
`WrapperReferenceConstruction.productRestriction_rejects_empty_rows`.

General in the three protocol carriers, in `Coord`, in the routed system, in the
node and in every schedule quantity. -/
theorem exists_frontier_routedTriple (P : Workspace.Types.Protocol.Protocol X Y Z)
    (R : Coord → Finset X) (A0 r : ℕ) (v : FrontierNode P R A0 r)
    (Sc : Finset Y) (Arows : Finset X) {κ : ℝ} {r' t : ℕ} {x θ : ℝ}
    (hY : 0 < Fintype.card Y)
    (hbob : DenseWeightedCount.IsBobNode (DenseWeightedCount.descend P v.val))
    (hheavy : vartheta * κ ≤ frontierWeight P R A0 r v)
    (hblocks : ((r' * RestrictionDatum.certifiedPt t : ℕ) : ℝ) ≤ 9 * κ / 16)
    (hpos : 0 < ((r' * t : ℕ) : ℝ) * x * ((Fintype.card X : ℕ) : ℝ))
    (hA : 2 * (((r' * t : ℕ) : ℝ) * x * ((Fintype.card X : ℕ) : ℝ)) ≤ (Arows.card : ℝ))
    (hdens : θ ≤ ((retainedCols P Sc v.val).card : ℝ) / (Fintype.card Y : ℝ)) :
    ∃ (S : Finset Coord) (T : Finset X) (b : Bool),
      S ⊆ representedCoords P R A0 r v ∧ T ⊆ Arows ∧
        RoutedTriple (Blk := Coord) (Row := X) (Col := Y)
          r' t 1 x θ S T (retainedCols P Sc (v.val ++ [b])) := by
  obtain ⟨S, hSsub, hScard⟩ :=
    exists_selected_blocks_at_heavy_node P R A0 r v hheavy hblocks
  obtain ⟨T, hTsub, hTcard, hTne⟩ :=
    exists_trimmed_reference_rows (Row := X) (r' := r') (t := t)
      (m := Fintype.card X) (x := x) (A := Arows) hpos hA
  obtain ⟨b, hb⟩ := exists_denser_child_colFloor hbob Sc hY hdens
  exact ⟨S, T, b, hSsub, hTsub, hTne, hScard, le_of_eq hTcard.symm, hb⟩

/-- **The `09:1270--1274` restriction, BUILT as an explicit full product.**

The `a^sharp = 1` datum of the dense frontier, produced from the routed triple.
Until this tranche the only Lean witness at these indices was the banked
existence statement
`RestrictionDatum.datum_consistent_with_frozen_side_conditions`; this is the
object itself, as the rectangle `S x T` inside `[q] x Rows(G)` together with the
denser child's retained columns.  General. -/
def frontierRoutedRestriction [DecidableEq Coord] {r' t : ℕ} {x θ : ℝ}
    {S : Finset Coord} {T : Finset X} {K : Finset Y}
    (htr : RoutedTriple (Blk := Coord) (Row := X) (Col := Y) r' t 1 x θ S T K)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    RestrictionDatum.RestrictionDatum Coord X Y r' t 1 x θ :=
  routedRestriction htr hθ0 hθ1 (le_refl 1)

end FrontierTriple

/-! ## §4  The `hrung` binder, and why the routing does not discharge it

`WrapperReferenceConstruction.wrapperLowRungs_at_referenceConstruction` carries a
binder `hrung` -- "at each member of `<U,1,y/2^j,theta>` the construction retains
the reference rows, projects to `9 kappa_j/16` outer coordinates, and applies the
certified-scale reference stopping lemma".  The parked generation of this module
claimed to discharge its routing half from `hroute`.  **That claim was false**,
and this section records the correct position instead, in machine-checked form.

**Why, exactly.**  The banked
`CertifiedLocalizedExtension.CertifiedExtensionEndpoint`'s conclusion is
`CertifiedE3 H (kr' + kt) val`, which does not mention the datum, and its three
datum-mentioning antecedents are discharged for *every* datum by the banked
`certifiedE3_of_datum`.  So `CanonicalReferenceStoppingCall ... Dat val` is, under
the ambient guards, the same `Prop` for every `Dat`, and `hrung`'s existential
follows from the endpoint together with **any** inhabitant of the datum type --
an inhabitation already banked as
`WrapperReferenceConstruction.referenceRestriction_nonempty`.
`shell_signature_forall_to_exists` isolates that inference as one general fact,
`routedSupply_gives_only_inhabitation` proves that inhabitation is *all* the
routing contributes here, and `rung_of_referenceEndpoint` is then stated in
exactly that shape and proved *by* the shell lemma, so the shell is named rather
than disguised.

**The general form of `thm:certified-localized-extension` is not expressible in
`src/`, and this is the round's substantive finding.**  Taking the endpoint as
the frozen theorem universally quantified over the ambient data of `A:111--137`
would make `H`, `t` and their exponents free while the readout `val` stays fixed
at the member's own complexity; but `A:117`'s `t_cert <= t` with `t = 2^{k_t}`
forces `2^20 <= k_t`, so `eq:certified-E3` demands `val >= 2 + 2^20` *uniformly*,
for every instance and every restriction, and demands more still as the free `H`
grows.  No antecedent of `CertifiedExtensionEndpoint` mentions `val`, so nothing
bounds that growth.  The obstruction is the banked `RestrictionDatum`
abstraction: a datum records its retained rectangle and its three `A:138--141`
readouts, **not the matrix it restricts**, so "the communication complexity of
this restriction" -- which is what `A:141--145` measures -- has no Lean spelling,
and `val` must stay a parameter pinned at the call site.  Carried as successor
`WDFW-F12`; it is a fact about `RESTRICTION-DATUM-001`'s interface, not about
this tranche.

So the endpoint stays a binder at the paper's own `09:313--323` substitution,
named once as `ReferenceStoppingEndpoint` and there narrowed to restrictions
**of `\widehat M`**; its proof is the registered `A:285--329` residue of
`CERTIFIED-LOCALIZED-EXTENSION-001`, unchanged and unnarrowed here.  Nothing
below is presented as landing the routing half of `hrung`, and the `hrung`
deferral recorded by `WRAPPER-REFERENCE-CONSTRUCTION-001` is **unchanged by this
tranche**, because the residue is the endpoint and not the routing. -/

universe u v

section Wiring

variable {Rw Cl Rw₂ Cl₂ : Type u} [Fintype Rw] [Fintype Cl] [Fintype Rw₂] [Fintype Cl₂]
  {Blk Col : Type v} [DecidableEq Blk] [Fintype Blk] [Fintype Col]

/-- **`thm:certified-localized-extension` at the `09:313--323` substitution, per
member, as ONE named binder tied to `\widehat M`.**

`09:314--323` applies the frozen theorem "using its fixed `y_* = 3/5` and the
substitutions `M = G`, `H = C-1`, `x = x_T`, `t = t_ref`, `r = q/t_ref`,
`r' = kappa_j/t_ref`, `eps = 0`, `h = theta`, `a^sharp = 0`", at each member of
the bracket family and at the member's own complexity readout.  That is exactly
what this `def` names: the banked
`CertifiedLocalizedExtension.CanonicalReferenceStoppingCall` is the substitution,
consumed by pin and not restated, and the ambient guards `A:111--137` are its own
antecedents inside that banked `def`.

**Binder only.**  Nothing in this repository proves it, and nothing below
pretends to.  Its proof is the frozen appendix proof `A:285--329`, the
registered residue of `CERTIFIED-LOCALIZED-EXTENSION-001`, whose
canonical-inhabitation obligation stays REGISTERED and DEFERRED
(`CONDITIONAL-STATUS`).

**The tie to `\widehat M`, authored here.**  `A:138` reads "Then every
restriction **of** `\widehat M` ...", and by `def:relaxed-interlace`
(`03:295--304`) the relaxed `q`-copy interlace has row set `[q] x X` and column
set `[L]`.  So an `A:138` restriction's outer-block carrier is `\widehat M`'s own
`[q]`, which at this call is `q = 2^{k_q}` (`09:105`); `Fintype.card Blk = 2^kq`
is that identification, and it is the **first** antecedent here.  The parked
generation left the block carrier abstract, at arbitrary cardinality, which is a
strictly larger `forall` than the frozen theorem supplies; adding the clause
narrows the binder, so what is assumed is weaker.

What the tie does **not** encode: the *entries* of `\widehat M`.  The banked
`RestrictionDatum` records a restriction by its rectangle and its three
`A:138--141` readouts, not by the matrix it restricts; that abstraction is
inherited from `RESTRICTION-DATUM-001`, is the same obstruction as `WDFW-F12`
above, and is neither closed nor narrowed here.

General in the carriers, in `N`, `G`, and in every schedule quantity. -/
def ReferenceStoppingEndpoint (Nmat Gmat : Rw → Cl → Bool)
    (C kq kref bT : ℕ) (θ y : ℝ) (Blk Col : Type v)
    [DecidableEq Blk] [Fintype Blk] [Fintype Col] : Prop :=
  Fintype.card Blk = 2 ^ kq →
  ∀ j : ℕ, j ≤ 2 →
    ∀ RC ∈ bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ,
      ∀ Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
          (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ,
        CanonicalReferenceStoppingCall Gmat C kq kref j (xTdepth bT) θ Dat
          (D (subgame (interlaceFun (wrapperU Nmat kq) 1) RC.1 RC.2))

/-- **The SHELL SIGNATURE, general -- the gate this repair installs.**

The defect the parked generation carried, isolated as one general fact: whenever
a hypothesis is `forall a, P a` and the type is inhabited, the existential
`exists a, P a` follows with the witness *discarded*.  So a declaration whose
hypothesis bundle contains `forall a, P a` and whose conclusion is `exists a, P a`
discharges nothing at all, however elaborate the witness it happens to plug in --
and no green build can see it, because the proof term typechecks perfectly.

The shape to test for at every wiring declaration is therefore: **a `forall Dat`
hypothesis whose body does not mention `Dat` in its conclusion**.  The banked
`CertifiedLocalizedExtension.CertifiedExtensionEndpoint` has exactly that shape
(`CertifiedE3 H (kr'+kt) val` is datum-free, and `certifiedE3_of_datum`
discharges its three datum-mentioning antecedents for every datum), so every
`hrung`-shaped deliverable built from it is a shell.  `rung_of_referenceEndpoint`
below is therefore proved *by this lemma*, which is the honest form: the shell is
named, its consequence is stated, and no discharge is claimed.

*Why the trivial witness fails.*  Nothing here is claimed to be hard -- the
content is that it is **easy**, which is the entire point.  General in the sort
and the predicate. -/
theorem shell_signature_forall_to_exists {α : Sort*} {P : α → Prop}
    (hne : Nonempty α) (hall : ∀ a, P a) : ∃ a, P a :=
  hne.elim fun a => ⟨a, hall a⟩

omit [Fintype Blk] in
/-- **What the routing actually contributes to `hrung`: inhabitation, and nothing
more.  PROVED.**

The judge's D20 diagnosis, made machine-checkable.  A routing supply at the
`09:313--323` indices yields an inhabitant of the datum type at those indices --
its own `lowRungRoutedRestriction` -- and by the shell signature above that
inhabitant is the *only* thing `hrung` needs from it, since the endpoint supplies
the call at every datum alike.

**And that inhabitation is already banked**, as
`WrapperReferenceConstruction.referenceRestriction_nonempty`
(`WrapperReferenceConstruction.lean:1149`, consumed at `:1303` inside
`referenceCall_full_gate_set_is_satisfiable`).  So the routing does not narrow
the `hrung` deferral by one symbol, and this tranche does not claim it does.  The
`09:311--327` content the routing *does* carry -- the frozen block count and the
row floor read at `m_G` -- is landed in §3a, where it is a readout of a built
object rather than a re-assumption.

*Why the trivial witness fails.*  The conclusion is `Nonempty` of a structure
whose three fields are `A:138--141`; an arbitrary rectangle does not inhabit it,
which is why the supply predicate has to be supplied at all.

General in the carriers and in every schedule quantity. -/
theorem routedSupply_gives_only_inhabitation {kq kref bT j : ℕ} {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hroute : ∃ (S : Finset Blk) (T : Finset Rw) (K : Finset Col),
      RoutedTriple (Blk := Blk) (Row := Rw) (Col := Col)
        (refRungCopies kq kref j) (tRef kref) 0 (xTdepth bT) θ S T K) :
    Nonempty (RestrictionDatum.RestrictionDatum Blk Rw Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ) := by
  obtain ⟨S, T, K, htr⟩ := hroute
  exact ⟨lowRungRoutedRestriction kq kref j htr hθ0 hθ1⟩

/-- **`hrung` from the endpoint and datum inhabitation -- the shell, NAMED.**

The banked headline's `hrung` binder, obtained from `ReferenceStoppingEndpoint`
together with per-rung inhabitation of the datum type.  The proof is one
application of `shell_signature_forall_to_exists`, which is the point: **this
declaration discharges nothing.**  Its hypothesis bundle is at least as strong as
its conclusion, the routing appears nowhere in it, and it is recorded only so
that the inference the parked generation dressed up as a wiring is stated in the
open.

The `hrung` deferral of `WRAPPER-REFERENCE-CONSTRUCTION-001` is **unchanged by
this tranche**: its residue is the endpoint (`A:285--329`), not the routing.
`hinh` is supplied in practice by the banked
`WrapperReferenceConstruction.referenceRestriction_nonempty`, and
`routedSupply_gives_only_inhabitation` records that the frontier routing supplies
the same thing and no more.

*Why the trivial witness fails.*  It does not fail, and the declaration says so:
`shell_signature_forall_to_exists` is the whole proof.  What *would* be a real
discharge is a statement whose conclusion pins the datum to the routing, and that
is not available while the endpoint's readout `val` is untied (`WDFW-F12`).

General in the carriers, in `N`, `G`, and in every schedule quantity. -/
theorem rung_of_referenceEndpoint (Nmat Gmat : Rw → Cl → Bool)
    {C kq kref bT : ℕ} {θ y : ℝ}
    (hBlk : Fintype.card Blk = 2 ^ kq)
    (hinh : ∀ j : ℕ, j ≤ 2 →
      Nonempty (RestrictionDatum.RestrictionDatum Blk Rw Col
        (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ))
    (hendpoint : ReferenceStoppingEndpoint Nmat Gmat C kq kref bT θ y Blk Col) :
    ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ,
        ∃ Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
            (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ,
          CanonicalReferenceStoppingCall Gmat C kq kref j (xTdepth bT) θ Dat
            (D (subgame (interlaceFun (wrapperU Nmat kq) 1) RC.1 RC.2)) := by
  intro j hj RC hRC
  exact shell_signature_forall_to_exists (hinh j hj) (hendpoint hBlk j hj RC hRC)

/-- **The banked `eq:wrapper-u-low` headline re-fired through the named endpoint.**

`WrapperReferenceConstruction.wrapperLowRungs_at_referenceConstruction` with its
`hrung` binder supplied by `rung_of_referenceEndpoint`.  Every banked hypothesis
is passed unchanged and narrowed nowhere; `hBlk`, `hinh` and `hendpoint` are
added.

**This declaration does NOT advance `eq:wrapper-u-low` (`09:264--266`), and must
not be recorded as doing so.**  Since `hinh ∧ hendpoint ⟹ hrung` while
`hrung ⇏ hendpoint`, it is *strictly weaker* than the banked headline it re-fires
and lands no mathematical content over it.  It is kept because the parked
generation's version must be re-derived through the repaired form rather than
left standing, and because naming the endpoint once, tied to `\widehat M`, is a
narrowing of what the banked tranche left abstract.

*Why the trivial witness fails.*  The deliverable is a lower bound on a
`Nat.sInf`, and at the constant matrix that infimum is `0` while the demanded
value `C + k_q - 1 - j` is at least `2`; the banked
`WrapperLowRungs.wrapperLowRungs_not_automatic` exhibits exactly that member.

General in the carriers, in `N`, `G`, `M_2^T`, and in every schedule integer and
real. -/
theorem wrapperLowRungs_of_referenceEndpoint
    (Nmat Gmat : Rw → Cl → Bool) (M2T : Rw₂ → Cl₂ → Bool)
    {Dsrc a r₂ wS bT kq kref jcand : ℕ} {θ Lθ y : ℝ}
    (hq4 : kref + 2 ≤ kq) (hC : 3 ≤ cBlock Dsrc a r₂ wS)
    (hfloor : Nat.clog 2 tCert ≤ kref)
    (hgate : ((2 : ℝ) ^ kq) * xTdepth bT ≤ 4 / 25025)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hwS : mHS.{u} + 2 ≤ wS) (hwSbT : wS ≤ bT)
    (hD2 : dTwoBlock Dsrc a r₂ = D M2T)
    (hrob : IsRobust M2T (1 / 10 : ℝ) ((bT : ℕ) : ℝ))
    (hD3 : 3 ≤ D M2T)
    (hland : ∀ jr : ℕ, jr ≤ 2 →
      RungLanding Gmat M2T wS jr bT (xTdepth bT) yStar)
    (hcand : RawLowProfileBody.J49Feasible kref jcand)
    (hsched1 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kq : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (kref - 1))
    (hsched2 : ((cBlock Dsrc a r₂ wS - 1 : ℕ) : ℝ) + (kref : ℝ) + Lθ
      ≤ (2 : ℝ) ^ (jcand : ℕ))
    (hθL : (2 : ℝ) ^ (-Lθ) ≤ θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hBlk : Fintype.card Blk = 2 ^ kq)
    (hinh : ∀ j : ℕ, j ≤ 2 →
      Nonempty (RestrictionDatum.RestrictionDatum Blk Rw Col
        (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ))
    (hendpoint : ReferenceStoppingEndpoint Nmat Gmat (cBlock Dsrc a r₂ wS) kq kref bT θ y
      Blk Col) :
    ∀ j : ℕ, j ≤ 2 →
      cBlock Dsrc a r₂ wS + kq ≤ j + 1 + Dfamily (interlaceFun (wrapperU Nmat kq) 1)
        (bracketGE (Fin (2 ^ kq) × Rw) (Fin (2 ^ kq) → Cl) 1 (y / 2 ^ j) θ) :=
  wrapperLowRungs_at_referenceConstruction (Blk := Blk) (Col := Col)
    Nmat Gmat M2T hq4 hC hfloor hgate hRw hCl hwS hwSbT hD2 hrob hD3 hland hcand
    hsched1 hsched2 hθL hne
    (rung_of_referenceEndpoint Nmat Gmat hBlk hinh hendpoint)

end Wiring

/-! ## §5  The poor-`u_don` projection cover, folded (`09:1746--1749`)

"Apply the poor-`u_don` projection cover to the donors feeding `T_*`.  By
`eq:wrapper-terminal-donor-gate`, it leaves `u_don` donors whose joint outer
projection has density at least `rho_0`."

Both halves are banked -- `lem:product-projection-cover` as
`WrapperProjectionCovers.productProjectionCover`, and the counting step as
`WrapperMassRedistribution.donors_survive_cover` -- and this section is the fold
that produces the frozen sentence's actual conclusion from them.  It stops
there: `09:1750` onward is `lem:template-coordinate-extraction` and the row-(iv)
inherited endpoint, neither of which is entered. -/

section CoverFold

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {q : ℕ}

/-- **`09:1748--1749`, PROVED: the cover leaves `u_don` dense donors.**

From a retained outer column set `S` of density at least `theta`, a donor index
set `Jgood` with more than `u_don B_theta` members, and the frozen cover
parameters, there is a `u_don`-subset of the donors whose joint projection is
**not** poor -- i.e. has density at least `rho_0`, which is the exact conclusion
the frozen sentence draws.

The proof is the frozen one: the banked cover produces an exceptional set `E`
with `|E| <= u_don (B_theta - 1)`; the banked `donors_survive_cover` turns
`u_don B_theta < |Jgood|` into `u_don <= |Jgood| - |E|`, so `Jgood \ E` still has
`u_don` members; any such subset misses `E` entirely, and by the cover's defining
property a `u_don`-set missing `E` cannot be poor.

*Why the trivial witness fails.*  The deliverable is not merely a `u_don`-subset
of `Jgood` -- those exist as soon as `Jgood` is big enough -- but one whose
projection meets the density floor.  The banked
`WrapperProjectionCovers.productProjectionCover_witness_is_nonempty` shows the
cover is genuinely nonempty at legal instances, so the `Jgood \ E` step is not
vacuous and an arbitrary `u_don`-subset of `Jgood` will not do.

General in the alphabet, in `q`, in the donor set and in all four numerals. -/
theorem exists_dense_donor_subset (S : Finset (Fin q → Y)) (Jgood : Finset (Fin q))
    {uDon Bθ : ℕ} {ρ₀ θ : ℝ}
    (hY : 0 < Fintype.card Y) (hu : 1 ≤ uDon) (hB : 1 ≤ Bθ)
    (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1) (hBρ : ρ₀ ^ Bθ < θ)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hdonors : (uDon : ℝ) * (Bθ : ℝ) < (Jgood.card : ℝ)) :
    ∃ J ⊆ Jgood, J.card = uDon
      ∧ ρ₀ * (Fintype.card Y : ℝ) ^ uDon ≤ ((projSet J S).card : ℝ) := by
  classical
  obtain ⟨E, hEcard, hEmeets⟩ :=
    productProjectionCover S (k := uDon) (B := Bθ) hY hu hB hρ0 hρ1 hBρ hS
  -- `donors_survive_cover` at `coverSize = |E|`, `donors = |Jgood|`, `Bt = B_theta`
  have hcover : ((E.card : ℝ)) ≤ (uDon : ℝ) * ((Bθ : ℝ) - 1) := by
    have hnat : (E.card : ℝ) ≤ ((uDon * (Bθ - 1) : ℕ) : ℝ) := by exact_mod_cast hEcard
    have hsub : ((uDon * (Bθ - 1) : ℕ) : ℝ) = (uDon : ℝ) * ((Bθ : ℝ) - 1) := by
      have hBn : ((Bθ - 1 : ℕ) : ℝ) = (Bθ : ℝ) - 1 := by
        have : (1 : ℕ) ≤ Bθ := hB
        push_cast [Nat.cast_sub this]
        ring
      push_cast
      rw [hBn]
    linarith [hnat, hsub.le, hsub.ge]
  have hsurv : (uDon : ℝ) ≤ (Jgood.card : ℝ) - (E.card : ℝ) :=
    WrapperMassRedistribution.donors_survive_cover hcover hdonors
  have hdiff : uDon ≤ (Jgood \ E).card := by
    have hcard : (Jgood.card : ℝ) - (E.card : ℝ) ≤ ((Jgood \ E).card : ℝ) := by
      have hle : Jgood.card ≤ (Jgood \ E).card + E.card :=
        Finset.card_le_card_sdiff_add_card
      have : (Jgood.card : ℝ) ≤ ((Jgood \ E).card : ℝ) + (E.card : ℝ) := by
        exact_mod_cast hle
      linarith
    have : (uDon : ℝ) ≤ ((Jgood \ E).card : ℝ) := le_trans hsurv hcard
    exact_mod_cast this
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hdiff
  have hJgood : J ⊆ Jgood := Finset.Subset.trans hJsub Finset.sdiff_subset
  have hJdisj : (E ∩ J) = ∅ := by
    ext i
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hiE hiJ
    have := hJsub hiJ
    rw [Finset.mem_sdiff] at this
    exact this.2 hiE
  have hnotpoor : ¬ PoorProjection ρ₀ J S := by
    intro hpoor
    obtain ⟨i, hi⟩ := hEmeets J hJcard hpoor
    rw [hJdisj] at hi
    exact absurd hi (by simp)
  refine ⟨J, hJgood, hJcard, ?_⟩
  have := not_lt.mp hnotpoor
  rwa [hJcard] at this

end CoverFold

/-! ## §6  Statement poles and LANE-GATE 3 non-vacuity

A green build sees none of the three failure modes guarded against here: a supply
met by a degenerate triple, a column clause that holds for free, and a block
selection that would exist without the frozen heavy condition. -/

section Poles

/-! **Empty-row-side pole, F4:** the parked generation carried a re-export of the
banked `WrapperReferenceConstruction.productRestriction_rejects_empty_rows` under
a local name.  That is a restatement of a banked pin, which the fixed-interface
discipline bars, so the local copy is **dropped**: `RoutedTriple`'s first clause
is guarded by the banked declaration, consumed by pin at
`WrapperReferenceConstruction.lean:1076--1079` and cited by its owning module's
name wherever the empty-row refutation is needed -- §1's `RoutedTriple`
docstring, §3b's `exists_frontier_routedTriple`, and §6's
`endpoint_side_conditions_are_satisfiable`.  Nothing is lost: the same theorem,
at the same statement, under its owning module's name. -/

/-- **Statement pole (`A:141` at `a^sharp = 1` is not satisfied for free).**

`exists_denser_child_colFloor` concludes `theta/2 <= |K|/|Y|`, and the worry is
that this could hold whatever the routing does.  It cannot: at `K = empty` the
readout is `0`, so the clause **forces** `theta <= 0`, which `A:128`'s
`0 < theta` refutes.  So the column clause comes from the Bob mass balance and
not from the shape of the statement.

*Why the trivial witness fails.*  There is no witness to find: the statement is
the forcing direction, and the empty retained set is exactly what it excludes.
General in `theta` at `A:128`'s floor. -/
theorem routedTriple_colFloor_is_not_free {Col : Type*} [Fintype Col] {θ : ℝ}
    (hθ0 : 0 < θ)
    (h : RestrictionDatum.certifiedColFloor θ 1
      ≤ (((∅ : Finset Col).card : ℝ) / (Fintype.card Col : ℝ))) : False := by
  rw [RestrictionDatum.certifiedColFloor] at h
  simp only [Finset.card_empty, Nat.cast_zero, zero_div] at h
  norm_num at h
  linarith

/-- **Statement pole (the block selection needs the frozen heavy node).**

`exists_selected_blocks_at_heavy_node` selects `r' p_t` coordinates *inside* the
node's census.  Dropping the heavy condition breaks it: a node whose census is
empty represents nothing, and there the frozen positive demand cannot be met at
all.  So the selection is a consequence of `09:1268--1269`, not of the ambient
finiteness of `Coord`.

*Why the trivial witness fails.*  The existential asks for a subset of the census
of the demanded size; at an empty census only the empty set is available, and its
card is `0`, which the demand refutes. -/
theorem frontier_blockCount_needs_the_heavy_node {Coord : Type*}
    {r' t : ℕ} (hpos : 0 < r' * RestrictionDatum.certifiedPt t)
    (h : ∃ S ⊆ (∅ : Finset Coord), S.card = r' * RestrictionDatum.certifiedPt t) :
    False := by
  obtain ⟨S, hSsub, hScard⟩ := h
  rw [Finset.subset_empty] at hSsub
  rw [hSsub, Finset.card_empty] at hScard
  omega

/-- **REJECTION PROBE (no legality claimed): `09:1268`'s heavy condition FAILS at
the only routed systems `src/` has.**

`09:1268--1269` closes "any first-Bob node satisfying `W_v >= vartheta kappa_v`".
Both quantities are DEFINED by the frozen source and both are already *evaluated*
in banked declarations at the live audit instance: `kappa_v = 2^{r - d_v} = 2`
(`09:1255`, banked `FirstBobFrontierInstance.live_kappa_attained`) and `W_v = 1`
(`09:1257`, banked `FirstBobFrontierInstance.live_frontierWeight_bobNode`).
Neither is chosen here -- both are read off the banked evaluations -- and
`vartheta = 9/16` is the banked `DenseWrapperFrontier.vartheta`.  The heavy
condition reads `9/8 <= 1`, which is false.

**Why this is the right kind of evidence.**  It is a *rejection* probe: it claims
no legality and exhibits no instance.  What it establishes is that `hheavy` is
not a clause that holds for free at any routed system currently in `src/` -- the
split instance is strictly worse (`W_v = 1/2` at the same `kappa_v = 2`) -- so
the LANE-GATE 3 deferral recorded on `frontier_blockCount_matches_heavy_ceiling`
is forced by the missing L1 machinery rather than chosen for convenience.  It
also supplies the "why the trivial witness fails" side of `hheavy`: the clause is
refutable, hence not vacuous.

`kappa_v` itself is still unreified in `src/` (successor `WDFW-F10`); this probe
consumes the banked *evaluation* at the audit instance and does not stand in for
that reification. -/
theorem live_firstBob_node_is_not_heavy :
    ¬ (vartheta * ((FirstBobFrontierInstance.liveSystem.toWrapperFrontier.capacity
          FirstBobFrontierInstance.liveBobNode : ℕ) : ℝ)
        ≤ frontierWeight FirstBobFrontierInstance.liveProtocol
            FirstBobFrontierInstance.liveRows 1 2 FirstBobFrontierInstance.liveBobNode) := by
  rw [FirstBobFrontierInstance.live_kappa_attained,
    FirstBobFrontierInstance.live_frontierWeight_bobNode, vartheta_val]
  norm_num

end Poles

section NonVacuity

/-- **LANE-GATE 3 (the supply is inhabited nondegenerately at legal widths),
PROVED.**

At any pair of frozen legal widths -- `4 <= k_ref` (which `A:117`'s divisibility
and `06:561--563`'s floor both force) and `k_ref <= l` -- the supply predicate is
inhabited at the `09:1272` index tuple `r' = 2^{l - k_ref}`, `t = 2^{k_ref}`,
`a^sharp = 1`, with **all three sides nonempty**: the block side has the frozen
positive count `9 . 2^{l-4}`, the row side is the whole carrier, and the column
side is the whole indexed column carrier.

Stated over the *range* of legal widths rather than at a numeral, because `t_ref`
and `kappa` are quantities the frozen schedule defines and assigning either a
numeral would be assigning a value to a defined quantity.

*Why this is not the canonical inhabitation.*  It is not.  The paper's own
instantiation of the supply is the frontier routing of `09:1268--1296` at the
index tuple `r' = kappa_v/t_ref`, `t = t_ref` (`09:1272`), which is **not**
expressible while `kappa_v` is unreified (successor `WDFW-F10`); that obligation
is REGISTERED and DEFERRED, and `exists_frontier_routedTriple` is the
branch-neutral generalisation of it, not a substitute.  What is below is the
shape audit -- it shows the four clauses can hold together nondegenerately at
legal widths, which a supply demanding more than the paper could not. -/
theorem routedTriple_nondegenerate_at_legal_widths {k ℓ L : ℕ} {x θ : ℝ}
    (hk : 4 ≤ k) (hkℓ : k ≤ ℓ) (hL : 1 ≤ L)
    (hx0 : 0 < x) (hgate : ((2 : ℝ) ^ ℓ) * x ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ (S : Finset (Fin (9 * 2 ^ (ℓ - 4)))) (T : Finset (Fin L)) (K : Finset (Fin L)),
      S.Nonempty ∧ T.Nonempty ∧ K.Nonempty
        ∧ 0 < RestrictionDatum.certifiedRowFloor (2 ^ (ℓ - k)) (2 ^ k) x L
        ∧ 0 < RestrictionDatum.certifiedColFloor θ 1
        ∧ RoutedTriple (Blk := Fin (9 * 2 ^ (ℓ - 4))) (Row := Fin L) (Col := Fin L)
            (2 ^ (ℓ - k)) (2 ^ k) 1 x θ S T K := by
  classical
  have hLpos : 0 < L := hL
  have hPt : RestrictionDatum.certifiedPt ((2 : ℕ) ^ k) = 9 * 2 ^ (k - 4) := by
    have hP : 16 * RestrictionDatum.certifiedPt ((2 : ℕ) ^ k) = 9 * 2 ^ k :=
      RestrictionDatum.sixteen_mul_certifiedPt (RestrictionDatum.sixteen_dvd_two_pow hk)
    have hsplit : (2 : ℕ) ^ k = 16 * 2 ^ (k - 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  have hexp : (2 : ℕ) ^ (ℓ - k) * 2 ^ (k - 4) = 2 ^ (ℓ - 4) := by
    rw [← pow_add]
    congr 1
    omega
  have hcount : (2 : ℕ) ^ (ℓ - k) * RestrictionDatum.certifiedPt ((2 : ℕ) ^ k)
      = 9 * 2 ^ (ℓ - 4) := by
    rw [hPt, ← hexp]; ring
  have hmul : (2 : ℕ) ^ (ℓ - k) * 2 ^ k = 2 ^ ℓ := by
    rw [← pow_add]; congr 1; omega
  have hcast : (((2 ^ (ℓ - k) * 2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ ℓ := by
    rw [hmul]; push_cast; ring
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  refine ⟨Finset.univ, Finset.univ, Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by positivity⟩⟩
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hLpos⟩⟩
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hLpos⟩⟩
  · -- `A:112`'s `0 < x` makes the row demand a positive number
    rw [RestrictionDatum.certifiedRowFloor]
    refine Nat.ceil_pos.mpr ?_
    rw [hcast]
    positivity
  · -- `A:128`'s `0 < theta` makes the column demand a positive number
    rw [RestrictionDatum.certifiedColFloor]
    positivity
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hLpos⟩⟩
  · rw [Finset.card_univ, Fintype.card_fin, hcount]
  · -- the row floor is legal at `2^l x <= 1`
    refine le_trans (RestrictionDatum.certifiedRowFloor_le ?_) ?_
    · rw [hcast]; exact hgate
    · rw [Finset.card_univ, Fintype.card_fin]
  · rw [Finset.card_univ, Fintype.card_fin, RestrictionDatum.certifiedColFloor]
    rw [div_self (ne_of_gt hLR), pow_one]
    linarith

/-- **The block-count identity behind `hblocks`, at `kappa = 2^l`. NON-FIDELITY.**

**What this proves, exactly.**  Two arithmetic facts about the frozen census
demand `r' p_t` at `r' = 2^{l-k}`, `t = 2^k`: it does not exceed `9 . 2^l/16`
(with **equality**, since `p_{2^k} = 9 . 2^{k-4}`), and it is positive.  Both are
evaluations of `RestrictionDatum.certifiedPt` through the banked
`sixteen_mul_certifiedPt`; no numeral is assigned to a source-DEFINED quantity,
and the statement is over the *range* `4 <= k <= l` because `t_ref` and `kappa`
are quantities the frozen schedule defines.

**What this does NOT prove, exactly (the parked generation's D27 defect).**  It is
**not** a non-vacuity result for `exists_frontier_routedTriple`.  That theorem
carries a *five*-clause premise bundle -- `hheavy`, `hblocks`, `hpos`, `hA`,
`hdens` -- and only `hblocks` is exhibited here: no frontier node, no routed
system, no certificate weight, no reference-row supply and no parent column
density appears anywhere below.  Its earlier name asserted the opposite and has
been withdrawn.

**The LANE-GATE 3 obligation for that five-clause bundle is DEFERRED against
residue L1**, registered in
`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, and is
discharged only when the transcript-level construction lands: exhibiting
`hheavy` at the node's own defined `kappa_v = 2^{r-d_v}` (`09:1255`) needs a
routed system with a **heavy** first-Bob node, and
`live_firstBob_node_is_not_heavy` shows -- by evaluating both sides at the only
routed systems `src/` currently has -- that neither banked instance supplies one.
The deferral is therefore a fact about the available machinery, not a
convenience.

*Why the trivial witness fails.*  The first clause is an equality at the frozen
count, so it pins the comparison rather than leaving it slack; the second
excludes the degenerate empty selection.  General in `k` and `l` at the frozen
range. -/
theorem frontier_blockCount_matches_heavy_ceiling {k ℓ : ℕ} (hk : 4 ≤ k) (hkℓ : k ≤ ℓ) :
    ((((2 : ℕ) ^ (ℓ - k) * RestrictionDatum.certifiedPt ((2 : ℕ) ^ k) : ℕ)) : ℝ)
        ≤ 9 * ((2 : ℝ) ^ ℓ) / 16
      ∧ 0 < (2 : ℕ) ^ (ℓ - k) * RestrictionDatum.certifiedPt ((2 : ℕ) ^ k) := by
  have hPt : RestrictionDatum.certifiedPt ((2 : ℕ) ^ k) = 9 * 2 ^ (k - 4) := by
    have hP : 16 * RestrictionDatum.certifiedPt ((2 : ℕ) ^ k) = 9 * 2 ^ k :=
      RestrictionDatum.sixteen_mul_certifiedPt (RestrictionDatum.sixteen_dvd_two_pow hk)
    have hsplit : (2 : ℕ) ^ k = 16 * 2 ^ (k - 4) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  have hexp : (2 : ℕ) ^ (ℓ - k) * 2 ^ (k - 4) = 2 ^ (ℓ - 4) := by
    rw [← pow_add]; congr 1; omega
  have hcount : (2 : ℕ) ^ (ℓ - k) * RestrictionDatum.certifiedPt ((2 : ℕ) ^ k)
      = 9 * 2 ^ (ℓ - 4) := by
    rw [hPt, ← hexp]; ring
  constructor
  · rw [hcount]
    have hsplitℓ : (2 : ℝ) ^ ℓ = 16 * 2 ^ (ℓ - 4) := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    push_cast
    rw [hsplitℓ]
    ring_nf
    norm_num
  · rw [hcount]
    positivity

/-- **LANE-GATE 3 / HYPOTHESIS CONSISTENCY: the routing supply's shape is
satisfiable at the frozen carriers, PROVED.**

`RoutedTriple` at the `09:313--323` index tuple is the supply the whole module is
about, and the worry a green build cannot see is that it might be unsatisfiable at
the carriers the frozen text fixes -- which would make every §2, §3a and §4
statement that consumes it vacuous however well it typechecks.  (Via
`routedSupply_gives_only_inhabitation` it is also what supplies §4's `hinh`.)

It is not.  At `A:125`'s block carrier `[q] = Fin (2^{k_q})` (whose
identification with `09:105`'s scale-alignment width is forced by the
substitution `q = r t_ref`), at a general row carrier (`A:111`'s `m` is an input,
not a size the clause bundle fixes) and at `03:297--299`'s indexed column carrier
`[L]` kept general in `1 <= L`, a supply exists at the `09:313--323` index tuple
with **all three sides nonempty**, under exactly the frozen gates:
`06:561--563`'s floor term, `09:277--278`'s rung range, `09:327`'s legality,
`eq:wrapper-low-simple-gate` and `A:128`'s `0 < theta <= 1`.

The block side is a genuine selection inside `[q]`, not the whole carrier: its
card is the frozen `9 kappa_j/16`, which is strictly smaller than `2^{k_q}`.

*Why the trivial witness fails.*  The empty triple fails all three nonemptiness
clauses and the positive block count; that is precisely what the poles of §6
record. -/
theorem routedSupply_shape_is_satisfiable {Row : Type*} [Fintype Row]
    {kq kref j L : ℕ} {xT θ : ℝ}
    (hfloor : Nat.clog 2 tCert ≤ kref) (hj : j ≤ 2) (hq4 : kref + 2 ≤ kq)
    (hRow : 1 ≤ Fintype.card Row) (hL : 1 ≤ L)
    (hxT0 : 0 < xT) (hgate : ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ (S : Finset (Fin (2 ^ kq))) (T : Finset Row) (K : Finset (Fin L)),
      S.Nonempty ∧ T.Nonempty ∧ K.Nonempty
        ∧ 0 < RestrictionDatum.certifiedColFloor θ 0
        ∧ RoutedTriple (Blk := Fin (2 ^ kq)) (Row := Row) (Col := Fin L)
            (refRungCopies kq kref j) (tRef kref) 0 xT θ S T K := by
  classical
  have hk4 : 4 ≤ kref := by
    have h20 : (2 : ℕ) ^ 20 ≤ kref := clog_two_tCert ▸ hfloor
    have hsmall : (4 : ℕ) ≤ 2 ^ 20 := by norm_num
    omega
  have hcount : refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref)
      = RestrictionDatum.certifiedPt (kappaLow kq j) :=
    refBlockCount_eq_certifiedPt_kappa hk4 hj hq4
  have hpos : 0 < refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref) := by
    rw [hcount, kappaLow_def]
    exact RestrictionDatum.certifiedPt_pos
      (RestrictionDatum.sixteen_dvd_two_pow (by omega)) (pow_pos (by norm_num) _)
  -- the block side fits inside `[q]`
  have hfit : refRungCopies kq kref j * RestrictionDatum.certifiedPt (tRef kref)
      ≤ Fintype.card (Fin (2 ^ kq)) := by
    have hPtK : RestrictionDatum.certifiedPt (kappaLow kq j) ≤ 2 ^ (kq - j) := by
      have hP : 16 * RestrictionDatum.certifiedPt (kappaLow kq j) = 9 * 2 ^ (kq - j) := by
        rw [kappaLow_def]
        exact RestrictionDatum.sixteen_mul_certifiedPt
          (RestrictionDatum.sixteen_dvd_two_pow (by omega))
      omega
    have hfin : (2 : ℕ) ^ (kq - j) ≤ 2 ^ kq := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Fintype.card_fin, hcount]
    exact le_trans hPtK hfin
  obtain ⟨S, -, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 ^ kq))))
      (by simpa using hfit)
  -- the row side: `09:327`'s legality makes the whole carrier admissible
  have hmul : (2 : ℕ) ^ (kq - j - kref) * 2 ^ kref = 2 ^ (kq - j) := by
    rw [← pow_add]; congr 1; omega
  have hcast : (((refRungCopies kq kref j * tRef kref : ℕ)) : ℝ) = (2 : ℝ) ^ (kq - j) := by
    rw [refRungCopies_eq, tRef_eq, hmul]; push_cast; ring
  have hpowle : ((2 : ℝ) ^ (kq - j)) ≤ (2 : ℝ) ^ kq :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hrowgate : (((refRungCopies kq kref j * tRef kref : ℕ)) : ℝ) * xT ≤ 1 := by
    rw [hcast]; nlinarith [le_of_lt hxT0]
  have hLpos : 0 < L := hL
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  refine ⟨S, Finset.univ, Finset.univ, ?_, ?_, ?_, ?_, ?_, hScard, ?_, ?_⟩
  · rw [← Finset.card_pos, hScard]; exact hpos
  · rw [← Finset.card_pos, Finset.card_univ]; exact hRow
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hLpos⟩⟩
  · -- `A:128`'s `0 < theta` makes the column demand a positive number
    rw [RestrictionDatum.certifiedColFloor]
    positivity
  · rw [← Finset.card_pos, Finset.card_univ]; exact hRow
  · rw [Finset.card_univ]
    exact RestrictionDatum.certifiedRowFloor_le hrowgate
  · rw [Finset.card_univ, Fintype.card_fin, RestrictionDatum.certifiedColFloor,
      div_self (ne_of_gt hLR)]
    simpa using hθ1

/-- **HYPOTHESIS CONSISTENCY, machine-checked: the added `hroute` shape and the
banked gate set hold TOGETHER at the paper's own tested endpoint.**

The cc-t1p rule asks, for every new headline, that the full hypothesis bundle be
tested for joint satisfiability rather than merely typechecked.  Here that test
is run outright: the banked
`WrapperReferenceConstruction.referenceCall_full_gate_set_is_satisfiable`
produces a legal width tuple at the paper's own closed-form tested endpoint
(`eq:kref-tested-endpoint`, `06:586--590`: `k_ref^* = 100 L_P^2`,
`j_ref^* = 4 L_P`) satisfying `06:561--563`'s floor term, `09:327`'s legality,
`A:112`'s `0 < x_T`, `eq:wrapper-low-simple-gate` and both `eq:tref-search` side
clauses, and `routedSupply_shape_is_satisfiable` then produces the routing supply
at those very widths, for all three rungs at once.

So the banked gate set is not inconsistent with the routing supply, and its
conclusion is not reached vacuously for want of a supply.  Nothing here claims a
concrete legal *schedule* tuple; the widths are the paper's own, obtained from
the banked endpoint rather than assigned.

*Why the trivial witness fails.*  The deliverable is not "some tuple" but a tuple
at which every listed gate and the supply hold simultaneously; dropping any one
of the frozen gates would make it a different and weaker statement, and the three
nonemptiness clauses exclude the degenerate supply outright. -/
theorem routedSupply_and_gate_set_jointly_satisfiable (Ccert : ℕ)
    {Row : Type} [Fintype Row] (hRow : 1 ≤ Fintype.card Row)
    {L : ℕ} (hL : 1 ≤ L) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ kref kq jcand Lθ xT,
      Nat.clog 2 tCert ≤ kref ∧ kref + 2 ≤ kq
        ∧ RawLowProfileBody.J49Feasible kref jcand
        ∧ 0 < xT ∧ ((2 : ℝ) ^ kq) * xT ≤ 4 / 25025
        ∧ ((2 : ℝ) ^ (-(Lθ : ℝ)) ≤ θ)
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kq : ℝ) + (Lθ : ℝ) ≤ (2 : ℝ) ^ (kref - 1))
        ∧ (((Ccert - 1 : ℕ) : ℝ) + (kref : ℝ) + (Lθ : ℝ) ≤ (2 : ℝ) ^ (jcand : ℕ))
        ∧ ∀ j : ℕ, j ≤ 2 →
            ∃ (S : Finset (Fin (2 ^ kq))) (T : Finset Row) (K : Finset (Fin L)),
              S.Nonempty ∧ T.Nonempty ∧ K.Nonempty
                ∧ RoutedTriple (Blk := Fin (2 ^ kq)) (Row := Row) (Col := Fin L)
                    (refRungCopies kq kref j) (tRef kref) 0 xT θ S T K := by
  obtain ⟨kref, kq, jcand, Lθ, xT, hfloor, hq4, -, -, hcand, hxT0, hgate, -,
    hθL, hs1, hs2, -⟩ :=
    referenceCall_full_gate_set_is_satisfiable Ccert (Row := Row) hRow hL hθ0 hθ1
  refine ⟨kref, kq, jcand, Lθ, xT, hfloor, hq4, hcand, hxT0, hgate, hθL, hs1, hs2, ?_⟩
  intro j hj
  obtain ⟨S, T, K, hS, hT, hK, -, htr⟩ :=
    routedSupply_shape_is_satisfiable (Row := Row) (j := j) (L := L)
      hfloor hj hq4 hRow hL hxT0 hgate hθ0 hθ1
  exact ⟨S, T, K, hS, hT, hK, htr⟩

/-- **LANE-GATE 3 for §4's two decidable side conditions, PROVED.**

`rung_of_referenceEndpoint` adds three hypotheses to the banked headline's own
bundle: `hBlk`, `hinh` and `hendpoint`.  Two of the three are settled outright
here, at the frozen carriers and under the frozen gates:

* `hBlk` -- `A:138`'s "of `\widehat M`" read through `def:relaxed-interlace`
  (`03:295--304`): the outer-block carrier of a restriction of the relaxed
  `q`-copy interlace is `[q]`, which at this call is `Fin (2^{k_q})` by `09:105`.
  So the tie is met by the frozen carrier itself and constrains nothing that the
  frozen text does not already fix.
* `hinh` -- datum inhabitation at all three rungs, obtained by routing the supply
  of `routedSupply_shape_is_satisfiable` through
  `routedSupply_gives_only_inhabitation`; the same inhabitation is banked
  independently as `WrapperReferenceConstruction.referenceRestriction_nonempty`.

The third, `hendpoint`, is **not** settled and cannot be: its truth is
`thm:certified-localized-extension`, whose proof is the registered
`A:285--329` residue.  Recording that split honestly is the point of this declaration -- the
parked generation asserted that neither addition could conflict with the rest,
which was true of two of them and unknown of the third (record fix F1).

*Why the trivial witness fails.*  The second clause is `Nonempty` of a structure
whose three fields are `A:138--141`, at index tuples fixed by the frozen
schedule; it is not met by an arbitrary rectangle, which is what
`WrapperReferenceConstruction.productRestriction_rejects_empty_rows` and
`routedTriple_colFloor_is_not_free` rule out.

General in the row carrier, in `L`, and in every schedule quantity. -/
theorem endpoint_side_conditions_are_satisfiable {Row : Type} [Fintype Row]
    {kq kref bT L : ℕ} {θ : ℝ}
    (hfloor : Nat.clog 2 tCert ≤ kref) (hq4 : kref + 2 ≤ kq)
    (hRow : 1 ≤ Fintype.card Row) (hL : 1 ≤ L)
    (hgate : ((2 : ℝ) ^ kq) * xTdepth bT ≤ 4 / 25025)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    Fintype.card (Fin (2 ^ kq)) = 2 ^ kq
      ∧ ∀ j : ℕ, j ≤ 2 →
          Nonempty (RestrictionDatum.RestrictionDatum (Fin (2 ^ kq)) Row (Fin L)
            (2 ^ (kq - j - kref)) (2 ^ kref) 0 (xTdepth bT) θ) := by
  refine ⟨Fintype.card_fin _, fun j hj => ?_⟩
  obtain ⟨S, T, K, -, -, -, -, htr⟩ :=
    routedSupply_shape_is_satisfiable (Row := Row) (j := j) (L := L)
      hfloor hj hq4 hRow hL (xTdepth_mem bT).1 hgate hθ0 hθ1
  exact routedSupply_gives_only_inhabitation (Blk := Fin (2 ^ kq)) (Rw := Row)
    (Col := Fin L) (kref := kref) hθ0 hθ1 ⟨S, T, K, htr⟩

end NonVacuity

end EthInapproximability.ParameterizedNP.WrapperDenseFrontierWiring
