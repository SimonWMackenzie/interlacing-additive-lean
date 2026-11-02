import EthInapproximability.ParameterizedNP.DenseWrapperFrontier

/-!
# Parameterized NP route: the no-early-stop block of the first wrapper

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 1367--1511** --
  the subsubsection `sec:wrapper-protected-early`, "Protected mass cannot stop
  early", opening at `09:1367--1368` immediately after `sec:dense-wrapper-frontier`
  (whose last line `09:1366` the predecessor module `DenseWrapperFrontier`
  discharges) and stopping immediately before `sec:wrapper-mass-redistribution`
  (`09:1512`).  The anchors traced here, in the order the frozen block prints
  them:
  * `09:1370--1376`, the reservoir masses and the donor functional: "Each outer
    coordinate contains two protected row reservoirs, each of mass
    `mu_P = 1/184` relative to the `m` rows of one copy of `N`.  For a first-Bob
    node `v` and a donor set `J_0 subseteq [q]`, let `P_v(J_0)` denote,
    normalized by `m`, the protected mass from those donors reaching `v`";
  * `09:1378--1384`, the four block constants `rho_0 = 99/100`,
    `rho_1 = rho_0/2`, `B_theta = min{B >= 1 : rho_0^B < theta}`,
    `L_q = ceil(log_2(2q)) + 1`;
  * `09:1386`: "We use one more elementary extraction fact";
  * `lem:template-coordinate-extraction` (label `09:1389`, statement
    `09:1388--1399`): "Let `P subseteq Y^u` have density at least `rho`, where
    `u` is divisible by four, and let `Y_T subseteq Y` have density `lambda_T`
    with `1 - lambda_T <= rho/8`.  Some set of `u/2` coordinates has an
    all-template projection of density at least `rho 2^{-u-1}` inside
    `Y_T^{u/2}`";
  * its frozen proof (`09:1401--1416`): "For a uniformly chosen tuple of `P`,
    the expected number of nontemplate coordinates is at most
    `u(1-lambda_T)/rho <= u/8`.  Markov's inequality shows that at least half
    the tuples have at least `3u/4` template coordinates.  Average the
    `u/2`-subsets of those template positions.  The elementary ratio
    `binom(3u/4, u/2)/binom(u, u/2) >= 2^{-u}` shows that one coordinate set
    receives at least a `2^{-u-1}` fraction of all tuples of `P`.  Dividing by
    the at most `|Y|^{u/2}` completions of one projected pattern gives at least
    `rho 2^{-u-1} |Y|^{u/2}` distinct patterns.  Since
    `|Y_T|^{u/2} <= |Y|^{u/2}`, their density inside `Y_T^{u/2}` is at least the
    claimed value";
  * `lem:early-protected-closure` (label `09:1419`, statement `09:1418--1430`)
    with `eq:protected-early-threshold` (label `09:1424`, display
    `09:1421--1425`): "Let `v` be a first-Bob node and put `kappa = kappa_v >= 2`.
    If `P_v(J_0) >= 128 mu_P B_theta L_q s kappa`, then one child of `v` has
    communication complexity at least `C + log_2 kappa - 1`";
  * its frozen proof `09:1432--1509`, whose steps are, in order:
    `09:1433--1440` ("One of the two protected reservoir types contributes at
    least half"; `D_mass = sum_j d_j >= 64 B_theta L_q s kappa`);
    `09:1441--1448` (discard donors with `d_j < D_mass/(2q)`, "their total
    contribution is below `D_mass/2`"; at most `L_q` dyadic classes
    `d_cls/2 < d_j <= d_cls`; some class `V` has
    `|V| d_cls >= D_mass/(2 L_q)`);
    `09:1449--1456` and `eq:protected-dyadic-class` (label `09:1455`): "`u` the
    least power of two at least `8 s kappa/d_cls`.  Then
    `8 s kappa <= u d_cls < 16 s kappa`, `|V| >= u B_theta`";
    `09:1458--1464` (poor `u`-sets, `lem:product-projection-cover`, the cover of
    size at most `u(B_theta - 1)`, the surviving `u`-set of density at least
    `rho_0`, and "after Bob's query, one child has density at least `rho_1`");
    `09:1466--1471` ("The schedule gives `1 - lambda_T <= 1/100 <= rho_1/8`, so
    `lem:template-coordinate-extraction` applies.  It leaves `u/2` donors whose
    projected all-template set has density at least `rho_1 2^{-u-1}` in
    `Y_T^{u/2}`.  Averaging over the equal template bins, fix one Stage-3 bin in
    each donor without reducing this relative density");
    `09:1473--1483` (the protected-reservoir fibre average, `d_cls q_2/4`
    Stage-2 coordinates per donor at surviving `C_1`-density `d_cls/4`, and
    `K_int = s kappa q_2` represented Stage-2 outer blocks);
    `eq:protected-delta-min` (label `09:1489`, display `09:1486--1490`):
    `d_cls >= 64 B_theta L_q s/q =: delta_min`;
    `09:1491--1497` (the ambient product width `(u/2) q_2`, at least
    `4 K_int`, so `r' = K_int/t_2` "lies in the literal range of Localized
    Extension");
    `09:1499--1508` (select exactly `9 K_int/16` blocks; "This is call (iii) in
    `sec:extension-call-ledger`"; the endpoint
    `B_cap + log_2 K_int = C + log_2 kappa - 1`).
* **Cross-anchors opened first-hand for this tranche:**
  * `06-parameter-schedule.tex:1102--1167`, `sec:extension-call-ledger`, the
    Localized Extension call table: the common binders
    `eq:extension-common-binders` (`06:1107--1114`), the ambient/represented
    binders `r = q_amb/t_2`, `r' = K/t_2` (`06:1122--1125`), the exact output
    size `|Q_s| = r' p_seed = 9K/16` (`06:1128--1130`), row **(iii)** "Early
    protected-mass stop (`lem:early-protected-closure`)" (`06:1147--1153`) with
    `v = u/2`, `K = K_int = s kappa q_2`, `h = rho_1 2^{-u-1}`, `a^sharp = 0`
    and "per-block row density at least `d_cls/4`, which the structural gates
    make at least `K 2^{-b_1}`", and the uniform closing sentence
    `06:1161--1167` ("`K` is a multiple of `t_2`, `1 <= r' <= r`, and the
    selected block count is exactly `9K/16`");
  * `09:1777--1778`, the frozen budget identity `C = B_cap + log_2 q_2 +
    log_2 s + 1`, which is the banked `TerminalTwoStream.terminalTarget` at the
    frozen exponents, and is what makes `B_cap + log_2 K_int` equal
    `C + log_2 kappa - 1`;
  * `08-dense-stage4.tex:123--134`, where `1/184` is printed: `08:123--127`
    gives "the base, selector, and diagonal **column** masses of `A` are exactly
    `91/92, 1/184, 1/184`", and `08:134` abbreviates
    `mu_Sigma = mu_D = 1/184`.  Since the wrapper's `N` is `A^T`, those column
    masses of `A` are exactly the **row** reservoir masses of `N` that
    `09:1370--1373` speaks of; the round-`r1` anchor `08:196--198` (which is
    inside `lem:raw-low-profile`) was wrong and is corrected here by a
    first-hand frozen-source lookup.

  * `A-certified-stopping.tex:109--146`, `thm:certified-localized-extension`, the
    inherited endpoint, read antecedent by antecedent: `A:111` (`M` a nonempty
    Boolean matrix, `H >= 2`), `A:112` (`0 < x <= 1`), `A:113--116`
    (`eq:certified-base`), `A:117--118` (`t >= t_cert`, a power of two divisible
    by `16`, `t x <= 1`), `A:125` (`r, r'` positive powers of two with
    `r' <= r`, `q = r t`), `A:126--128` (the `(q,t,eps)`-balanced family with
    `0 < eps < 1`, or the exact full product at `eps = 0`), `A:128--129`
    (`h in (0,1]`, `a^sharp in {0,1}`), `eq:certified-E1`/`eq:certified-E2`, and
    the `A:138--141` restriction data (exactly `r' p_t` represented outer blocks,
    at least `ceil(r' t x m)` rows in each, column density at least
    `h 2^{-a^sharp}`), concluding `H + log_2(r' t)` at `eq:certified-E3`;
  * `D-inherited-contracts.tex:746--764`, `eq:contract-extension-exponents`: "At
    every active call ... the call record must exhibit natural numbers
    `T, R, R_loc` satisfying `t_2 = 2^T`, `q_amb = 2^{R+T}`, `K = 2^{R_loc+T}`,
    `R_loc <= R`", with the closing warning "Recording only `t_2 | q_amb` and
    `t_2 | K` does not discharge `eq:contract-extension-exponents`" and the
    sentence "The product counts `1, 2, u/2, u_don/2` are likewise powers of two
    at their call sites";
  * `06:851--857`, `eq:epsilon-product`, `eps_prod = max{(1+eps_2)^{t_2}-1,
    1-(1-eps_2)^{t_2}} < 1/50`, and `06:937--950`, `eq:all-extension-gates`:
    "Every product-family application has ambient width at most `v_max q_2`,
    inverse row density at most `2^{L_h}`, and balancedness error at most
    `eps_prod`.  It is therefore enough to verify ..." -- the uniformity that
    makes the two column-loss gates quantifiable over reached widths;
  * `06:529--539`, `eq:Q-theta-choice`: `Q_0 = max{8 b_out/(delta delta_U),
    8/delta, 16}` (`06:529--531`), `Q` the least power of two at least `Q_0`
    (`06:532`), `theta = c_theta/(2Q) = delta/(16Q)` (`06:533`) with
    `1/theta = 160Q` an integer at `delta = 1/10` (`06:539`);
  * `06:547`, the finite gate "We also impose the finite gate
    `delta_U <= 1/200`", and `05:39--40`, "`b_0, b_out in N` are positive
    incoming and requested outgoing robustness depths" (the sentence wraps, and
    the citation is given as the straddle it is).  Together with `delta = 1/10`
    these evaluate the **first** branch of the `Q_0` maximum:
    `8 b_out/(delta delta_U) >= 8 . 1 . 10 . 200 = 16000`, so `Q >= 2^14`
    (`06:532`) and every threshold the schedule hands this block satisfies
    `theta = 1/(160Q) <= 1/2621440`.  Round `r2` read only the `16` branch of
    that maximum and recorded `theta <= 1/2560`; see the round-`r3` section
    below.

## Round `r2`: the two-fix repair

Round `r1` was **parked, not banked**: the build was green and every repository
gate passed, but the round-`r1` statement gate returned REVISE on two substantive
findings, both confirmed independently by the verify seat.  This round repairs
both under *restore-don't-rederive*: the 85 declarations round `r1` carried
CLEAR -- including the `r1`-completed call row `ExtensionCallThree`, the restored
`A:109--146` antecedent of `hLocEx`, the frozen threshold form of
`earlyProtectedClosure`, and the `B_theta` cover bracket -- are carried
forward unchanged, and only the two defective surfaces move.

**REVISE-A (the column-density chain was inert).**  `selectedColumnDensity` was
provable with **none** of its hypotheses: its deliverable existentially
quantified a bare `P` with no tie to `S`, so `P := Finset.univ` made the
right-hand side `|Y_T|^{u/2}` and `callThreeH_le_one` closed it; and its `hQuery`
binder asked only that two counts dominate the parent's projection count, which
`P_0 := univ`, `P_1 := empty` discharges for every `S` and every `J`, since
nothing tied `P_0`, `P_1` to `projSet J S`.  The whole of `09:1458--1471` -- poor
cover, `rho_0 -> rho_1`, template extraction -- was therefore inert, exactly as
round `r0` had charged.  The repair is two clauses, both frozen content:

* `hQuery` now asks for a genuine **partition** of the relabelled parent
  `ambientRelabel J eJ S` (`Disjoint P_0 P_1` and `P_0 union P_1 = iota(projSet
  J S)`), which is what "after Bob's query" means -- a query splits the columns
  it acts on -- and it supplies the frozen relabelling `iota : [u] -> J`
  explicitly rather than leaving it implicit;
* the deliverable now carries the produced child's **provenance**: the returned
  `P` satisfies `P subseteq iota(projSet J S)` and carries the frozen `rho_1`
  density, alongside the selected `u`-set's membership `J subseteq V`, its size,
  and its non-poorness.

Both round-`r1` seat countermodels are preserved as **regression probes** and are
now refuted against the repaired clauses:
`selectedColumnDensity_univ_child_pole` (the `P := univ` pole) and
`bobQuery_trivial_split_fails` (the `P_0 := univ`, `P_1 := empty` pole), with
`selectedColumnDensity_poles_are_live` exhibiting a concrete instance at which
their hypothesis holds.  `bobQuery_partition_is_satisfiable` shows the
strengthened binder is still satisfiable **without any protocol**, so the repair
adds faithfulness and not an existence burden.

**REVISE-B (the whole witness family stood at a forbidden scale).**  Every
round-`r1` non-vacuity witness ran at `r_3 = 0`, i.e. `s = 1`, which the frozen
source forbids: `04:389` (`def:guarded-source-constructor`), `04:460`
(`lem:guarded-source-active-slot`), `04:481` (`def:guarded-source-retention`),
`04:504` (`thm:guarded-source`) and `04:619` all require `s >= 4` a power of two,
so `r_3 >= 2`.  That is also the loosest possible operand for the very
inequalities the witnesses exercise.  In addition,
`earlyProtectedClosure_block_bundle_is_consistent` ran at `r_2 = 4` (`q_2 = 16`)
with `k_2 = 4` (`t_2 = 16`) against `eq:stage2-structural-gates` (`06:835`)
`4 t_2 <= q_2`.  All five witnesses are re-instantiated at `r_3 = 2` (`s = 4`)
and the block bundle additionally at `r_2 = 6` (`q_2 = 64`), where
`4 t_2 = 64 <= 64 = q_2`; both floor-tier anchors are carried as **checked
identities** (`witness_family_floorTier_anchors`, renamed from round `r2`'s
`witness_family_schedule_legality` by the round-`r3` repair, and two extra
conjuncts of the
block bundle) so that the family cannot drift back silently.

## Round `r3`: the `theta`/`s` legality repair

Rounds `r0`--`r2` all located their non-vacuity by *searching the constraints
they could see locally* for a `theta` and an `s`, and then calling the result
legal.  That is the defect this round repairs, and it is a defect of
**provenance**, not of arithmetic: every inequality rounds `r1`/`r2` proved is
still true, and every one of them is carried forward unchanged.  What is
withdrawn is the claim that the points at which they were proved are points the
frozen schedule reaches.

Three numerals were assigned to quantities the frozen source **defines**:

* **`theta = 1/20480`.**  Round `r2` justified it as `eq:Q-theta-choice` at
  `Q = 2^7 = 128`, on the strength of the `16` branch of the `Q_0` maximum
  (`theta <= 1/2560`, "so `1/20480` is under the ceiling").  That is a
  non-sequitur twice over: an upper bound on legal `theta` legalizes nothing
  under it, and the maximum has a **larger** branch.  Reading
  `06:529--531` in full against `05:39--40` (`b_out >= 1`), `06:539`
  (`delta = 1/10`) and `06:547` (`delta_U <= 1/200`) gives `Q_0 >= 16000`, hence
  `Q >= 2^14 = 16384` and `theta <= 1/2621440`.  `Q = 128` is **refuted**.
* **`s = 4`.**  `04:389`, `04:460`, `04:481`, `04:504` and `04:619` require
  `s >= 4` a power of two -- that is a *floor*, and the round-`r2` witnesses met
  it.  The value of `s` is fixed elsewhere: `eq:s-choice` (`06:112--120`) reads
  `A_pre = max{16, b_out, B_pub, z_R, clog_2(|E|+2)}`,
  `u = clog_2(clog_2(A_pre + 16))`, `s = 2^{ceil(B_s u^2)}`, with `B_s` a
  *positive* integer of the universal configuration field (`06:56--62`).  Then
  `A_pre >= 16`, `clog_2(32) = 5`, `clog_2(5) = 3`, so `u >= 3` and
  `s >= 2^9 = 512`; `06:394--395` adds `64 | s`.  `s = 4` is a floor value the
  defining display cannot produce.  The chain is *already reified and proved*,
  in the banked `ParameterSchedule.Apre`/`.uAux`/`.sScale` with
  `three_le_uAux` and `sScale_floor` -- but `ParameterSchedule` **imports this
  module**, so those results cannot be consumed here.  That import direction is
  why the `s` half is carried below as the two derived binders `512 <= s` and
  `64 | s` rather than through the schedule constructor.
* **`q = 2^24`.**  `eq:q-deltaU` (`06:514--518`) fixes `q = 2^{A_wrap L_P^2}`
  with `L_P = clog_2(P_0)` (`06:471`) and `P_0 >= 16` (`06:467`), so the
  reachable exponents are the multiples `A_wrap L_P^2` with `L_P >= 4`; `24` is
  not one of them.  `A_wrap` itself is genuinely free -- `06:520--522` says only
  that it "is fixed universally below ... chosen large enough to dominate every
  protocol-independent exceptional-set bound" -- so the legal instances below
  quantify over it existentially rather than pinning a numeral.

The repair, declaration by declaration:

1. **Re-derived at legal values.**  `Q0_route_floor`, `Qwidth_route_floor`,
   `scheduleTheta_pos`, `scheduleTheta_le_rhoZero`, `scheduleTheta_route_le`,
   `Btheta_ge_two_at_scheduleTheta`, `Btheta_le_tested_at_scheduleTheta` and
   `Btheta_bracket_at_scheduleTheta` evaluate the defining chain in dependency
   order, consuming `EntryGates.Q0`, `.Qwidth`, `.rQ`, `.deltaFixed`,
   `Q0_le_Qwidth` and `Qwidth_eq_two_pow` **by pin**.  No numeral is assigned to
   `theta`: the bracket is stated at the schedule's own `theta = 1/(160 Q)`,
   uniformly in `Q`.  The lower half `B_theta >= 2` holds at every threshold the
   chain produces; the upper half is the `eq:cover-tested-endpoint` discipline
   of `06:657--693` at base `rho_0`, and is a *function of* `Q` rather than a
   constant, because a smaller `theta` forces a larger least search.  (The
   downstream `ParameterSchedule.Bpair_le_tested` is the same estimate at the
   banked `theta Q`; the import direction again forbids consuming it, and the
   local proof is recorded here as a forced duplication, not as a second
   interface.)
2. **Demoted to floor-tier probes, legality withdrawn.**
   `Btheta_floorTier_ge_two`, `Btheta_floorTier_le`,
   `witness_family_floorTier_anchors`, `extensionCallThree_floorTier_instance`,
   `extensionCallThree_of_width_floorTier_instance`,
   `reachableWidth_floorTier_instance` and
   `earlyProtectedClosure_block_bundle_is_consistent` keep the round-`r2`
   arithmetic verbatim and lose the word "legal".  Each is now labelled
   **FLOOR-TIER / BEYOND-PAPER**: it audits *our encoding* at a point the paper
   never visits, it satisfies the Section-4 floors and the Stage-2 structural
   gates but **not** `eq:s-choice`, `eq:Q-theta-choice` or `eq:q-deltaU`, and no
   parameter value may be read out of it.
3. **New legal-value non-vacuity.**  `reachableWidth_at_scheduleTheta` and
   `earlyProtectedClosure_block_bundle_at_scheduleTheta` inhabit the same two
   predicates at the schedule's own `theta = 1/(160 Q)`, at any `s = 2^{r_3}`
   meeting the `eq:s-choice` floor, at `kappa = 2^{ell} >= 2` (`09:1420`), and
   at a wrapper width `q = 2^{A_wrap L_P^2}` of the `eq:q-deltaU` shape whose
   `A_wrap` is produced by `exists_wrapper_exponent`.  That last step is the
   only place where `06:520--522`'s "chosen large enough" is discharged rather
   than assumed, and `mul_succ_le_two_pow` is its arithmetic core.
4. **The separation itself is checked, not asserted.**
   `floorTier_values_are_refuted_by_the_schedule` proves in the kernel that the
   route's own threshold is *strictly below* `1/20480`, that `s = 4` is strictly
   below the `eq:s-choice` floor `512`, and (through
   `wrapper_exponent_ne_twentyfour`) that `24` is not an `eq:q-deltaU` exponent.
   `scheduleTier_hypotheses_are_satisfiable` discharges the schedule tier's
   premise bundle at a concrete tuple, so neither schedule-tier inhabitant is
   vacuously true of an inconsistent hypothesis set.  `Btheta_antitone` and
   `Btheta_mono_in_scheduleWidth` record why no constant can cap the least
   search over the legal family, which is the structural reason the round-`r2`
   bound `B_theta <= 1100` was never a statement about the schedule.

**What is registered rather than discharged.**  Two obligations stay open and
are recorded in `OBLIGATION_LEDGER.md` under `WRAPPER-PROTECTED-EARLY-001`:

* the `s` half of the chain is consumed as the derived binders `512 <= s`,
  `64 | s` instead of through `ParameterSchedule.sScale`, because that module
  imports this one.  A module importing **both** is where the two can be
  composed; this one cannot be it;
* `ExtensionCallThree` still has **no** inhabitant at a full schedule point.
  Its `b_1`, `r_2` and `k_2` are Stage-1/Stage-2 quantities whose defining
  displays are outside `sec:wrapper-protected-early`, so the legal instance
  would have to be built where those land.  `extensionCallThree_floorTier_-`
  `instance` is the interim probe and is labelled NON-FIDELITY accordingly; it
  does **not** discharge the canonical-inhabitation obligation.

Finally, the round-`r2` prose in the route ledger row repeated the refuted
claims verbatim; it is corrected in the same change as this module.

## Round `r4`: the `hLocEx` re-shape (the `A:138` restriction datum restored)

Round `r3` was banked, and its 85+ CLEAR declarations are carried forward
unchanged.  What round `r4` repairs is a **shape** defect that no gate in this
module could see, because seeing it needs an *upper* bound on a child's cost and
no such bound occurs here.  The defect was proved downstream, in the banked
`MassRedistributionEntry.constructionPath_composition_is_refuted_at_a_reachable_-`
`width`: conjoin the round-`r3` `hLocEx` with `09:1520--1523`'s first-Bob budget
("the conclusion of the lemma would exceed its remaining child budget", the words
being on `09:1523`) and one
reachable width, and `False` follows -- **without** `eq:protected-early-threshold`
ever being used.  That refutation is a theorem, not a charge, and it is preserved
as a regression pole (protocol-free, in Section 11 below, as
`oldShapeLocEx_forces_an_untied_object` and
`oldShapeLocEx_and_a_child_budget_are_inconsistent`).

*What was actually missing, read off the frozen theorem.*  `A:138--143` reads
"every restriction of `Mhat` with exactly `r' p_t` represented outer blocks, at
least `ceil(r'txm)` rows in each represented block, and column density at least
`h 2^{-a^sharp}`, has communication complexity at least `H + log_2(r't)`" -- the
clause list runs `A:138--141` and the endpoint display `H+log_2(r't)` sits at
`A:142--144` with the numeral on `A:143`, which is why the in-code comments cite
those two ranges separately.  The
**subject** of that quantifier is the restriction.  Round `r3` encoded `A:138--141`
as three inequalities on the outer parameters `selCard`, `rowsPerBlock`,
`colDens`, and concluded about a `child : Mem` fixed *outside* the quantifier;
nothing tied the two, so the assumed implication was strictly stronger than the
inherited corollary -- it bounded objects the antecedent never mentions.
`09:1503--1504` is explicit about the intended subject: "Localized Extension gives
the **selected** Bob child complexity".

*The repair, and it is an addition, never a weakening.*  Every round-`r3`
antecedent of `hLocEx` survives verbatim and in the frozen `A:110--146` order.
Three things are added, all frozen content:

* an explicit restriction-datum parameter `isRestr : Mem -> N -> N -> R -> Prop`
  of the two closure theorems, reading "`w` is a restriction of the relaxed
  `q`-copy interlace `Mhat` with the given represented-block count, per-block row
  count and column density".  This module models no matrix restriction (`Mem` is
  an abstract cost carrier), so the datum is GAP-EXPOSED and abstract here; its
  concrete realization is the banked `RestrictionDatum.RestrictionDatum`, which
  **imports this module** and therefore cannot be consumed here.  A forward
  obligation to compose the two is registered in `OBLIGATION_LEDGER.md`;
* the `A:138` clauses `isRestr w blocks rowsEach colDens` and
  `blocks = 2^{R_loc}(9 t_2/16)` -- the second being `A:138`'s **exactly** `r' p_t`
  at `p_t = 9t/16` (`eq:certified-pt-ht`), which round `r3` had only as the supply
  inequality `9 . 2^{R_loc+k_2}/16 <= selCard`.  The supply inequality is kept
  (`09:1499` selects exactly `9K_int/16` blocks *out of* a supply of at least
  `K_int`), so the two counts are the frozen pair and not a substitution;
* the concluded object `w`, its block count `blocks` and its per-block row count
  `rowsEach` are bound **inside** the quantifier, so `A:139--140`'s row count is
  read off the same restriction the conclusion speaks about.

*Where the restriction comes from.*  `09:1499--1504` produces it inside the proof
of `lem:early-protected-closure`, after the extraction chain has run -- which
needs the protected mass.  So the new binder `hSelect` is **gated on `D_mass`**
(on `eq:protected-early-threshold` itself in `earlyProtectedClosure`), and a
bundle that drops the threshold can no longer reach the endpoint.  That is
exactly the property the round-`r3` shape lacked.

*And it is gated on the extraction as well (the `r2` re-gate).*  `D_mass` alone
is not where `09:1499` stands.  The frozen selection is reached only after
`09:1458--1464` (poor-`u`-set cover, denser child at `rho_1`) and `09:1466--1471`
(the schedule gap, `lem:template-coordinate-extraction`, the `u/2` donors at
`rho_1 2^{-u-1}`), so `hSelect` takes that block's **output** as a second
antecedent: a child `P` of the relabelled parent, a coordinate set `J'` of the
frozen half width `u/2`, and the entering column density attained on `J'` in
`Y_T^{u/2}`.  `earlyProtectedClosureFromDmass` discharges it from
`selectedColumnDensity` and from `hYT0`, so the six density-chain hypotheses are
load-bearing for the endpoint rather than decorative.  The conclusion, the
`hLocEx` antecedent list, and the singular density slot are all unchanged by this
gate: it only makes the assumed selection harder to trigger, never the assumed
endpoint easier to reach.

*Both directions are kernel-checked, not asserted.*  Section 11 proves the old
shape forces a bound on an untied object (hence is inconsistent with any child
budget), and proves the new shape satisfiable at **both** the empty and the total
restriction datum -- so the repair neither keeps the over-reach nor buys
consistency by making the hypothesis unsatisfiable.
`MassRedistributionEntry.reshapedBinder_and_firstBob_budget_stand_together`
exhibits the repaired binder's *shape*, at the empty datum, coexisting with
`09:1520--1523`'s budget; at the empty datum the binder conjunct is a tautology,
so **nothing about the binder's content** is exhibited there.  The content is
exhibited one theorem further on, at a **non-degenerate** restriction datum, by
`MassRedistributionEntry.narrowedSelection_locEx_and_budget_stand_together_-`
`at_a_nondegenerate_datum` -- which also exhibits `hSelect` itself -- and
`MassRedistributionEntry.reshapedBinder_through_the_gate_returns_the_frozen_-`
`collision` compiles the complementary fact that with the selection's output in
hand the frozen collision returns, so the repair routed the contradiction through
`eq:protected-early-threshold` rather than deleting it.

*The selection binder is singular, not universal.*  `hSelect` asserts the
restriction at **one** column density, the `A:141` floor `h 2^{-a^sharp}` at
`a^sharp = 0`, i.e. at `callThreeH e / 2 ^ (0 : N)`.  `09:1501--1502` records
"the entering column density" -- one restriction at one density -- and `A:141`
reads the density slot as a **lower bound**, so the predicate is antitone there
(`MassRedistributionEntry.datumRestr_antitone_in_density` compiles this).  A
binder universally quantified over every density above the floor would therefore
be strictly stronger than its own manuscript reference and satisfiable only at
degenerate data; the narrowed form is the frozen one.

*Consumers re-derived in the same tranche.*  `EarlyClosureBlockSelection.`
`earlyProtectedClosure_at_builtPv`, `ProtectedEarlyClosure.firstBob_protectedMass_-`
`lt_of_earlyClosure` and its two aggregations, and the canonical-system chain
through `BobHeavyDonorCount`, `WrapperExceptionalCount`, `WrapperLossTable`,
`WrapperProjectionCoverTail`, `WrapperUDenseOpening` and the four `Terminal*`
modules all carry `isRestr` and the gated `hSelect`; **no conclusion anywhere
changed**.

*What this does not do.*  It does not discharge `hLocEx`, and it does not build
the restriction: `isRestr` is a binder, `hSelect` is a binder, and both are
GAP-EXPOSED.  `sec:wrapper-mass-redistribution` remains GAP-EXPOSED in full and
no route completion is claimed.

## Round `r2` of the re-shape: the extraction re-gate (and the `r1` incident)

*The incident of record.*  Round `r1` narrowed `hSelect` to the single entering
column density -- which is right, and is kept -- but discharged the resulting
proof obligation by building the call record's `column_density` field from
`le_refl _` and then **discarding** the step that showed the density is attained.
The consequence was invisible to every gate: the build was green, the arithmetic
checks passed, the registry verified, and the statement was still true; yet
`hQuery`, `hS`, `hYT`, `hgap`, `hY`, `hYT0` and the carriers `Y`, `S`, `YT`,
`lamT` had all become dead for the conclusion, so the whole of `09:1458--1471`
no longer gated the endpoint in the principal deliverable.  That is the same
inertness pattern an earlier round had repaired one level down, re-instated one
level up, and the module's own "Proved outright" item 8 was falsified by the
proof printed below it.  The round was **parked, not banked**.

*The repair.*  `hSelect` now takes `ExtractionOutput S YT e` as an antecedent:
the child of the relabelled parent, the frozen half width `u/2`, and the entering
column density attained on it -- exactly what `09:1466--1471` leaves on the table
for `09:1499` to select from.  `earlyProtectedClosureFromDmass` discharges it
from `extractionOutput_of_selectedColumnDensity`, the frozen extraction itself.
Nothing else in either closure theorem moves: the `hLocEx` antecedent list is
unchanged and still the frozen `A:110--146` order, the conclusion is unchanged,
the density slot stays singular, and the two shape poles and the consistency
readout of Section 11 are untouched.  Adding an antecedent to an assumed
implication only makes the assumption weaker, so the theorem is strictly stronger
than the parked one -- the repair buys nothing by weakening a bound.

*How it is checked, since a green build cannot see it.*  Each of the six
hypotheses was deleted in a scratch copy and the module re-elaborated; all six
deletions break the proof.  Symmetrically, the parked shape was re-elaborated
with the extraction block and all six hypotheses removed, and it still compiles
-- which is the incident, reproduced rather than asserted.

## What round `r1` had already repaired, and which stands

The round-`r0` shape of this block was barred at the statement gate on three
load-bearing declarations.  All three repairs are carried forward here unchanged,
and they are mathematical, not cosmetic:

1. **`ExtensionCallThree` now records the whole of row (iii).**  `r0` omitted the
   entering column density `h = rho_1 2^{-u-1}` and `a^sharp = 0` (`06:1150`),
   and recorded only `t_2 | K_int`, which `D:762--764` explicitly says does not
   discharge the exponent contract.  The record is now indexed by the three
   named exponents `T, R, R_loc` of `eq:contract-extension-exponents`, carries
   `u = 2^e` (so `D:761--762`'s power-of-two product count `u/2 = 2^{e-1}`
   holds), carries the ambient-width clause, and carries the `A:141` column
   density at `a^sharp = 0`.  `h in (0,1]` is **not** a field, because
   `callThreeH_pos` and `callThreeH_le_one` prove it outright and a field
   restating a derived fact is dead weight.  The whole record is *constructed* by
   `extensionCallThree_of_width` from schedule data, never assumed.
2. **`earlyProtectedClosure` now assumes exactly `thm:certified-localized-
   extension` and starts at the lemma's own threshold.**  `r0`'s `hLocEx` had an
   antecedent strictly weaker than `A:109--146`, so the *assumed* implication was
   stronger than the inherited corollary; the antecedent list is now the frozen
   one in the order `A:110--146` prints it.  Because call (iii) has `v = u/2 > 1`,
   `06:1119--1120` puts it on the **product** branch of `A:126--128`, so the
   `eps_prod` clause is live and appears as the two explicit binders `heps0`,
   `heps1` -- and `EXPANDER-001` still has **no** Lean declaration.  The statement
   is now hypothesized at `eq:protected-early-threshold` (`09:1421--1425`) on
   `P_v(J_0)` itself rather than at the derived `D_mass` of `09:1436--1439`;
   `protected_reservoir_halving` performs `09:1433--1435` and is where `mu_P` is
   load-bearing.  The density chain is wired: `exists_dense_uset_in_class`,
   `denserChild_rhoOne`, `templateCoordinateExtraction` and
   `representedBlocks_ge` are all consumed, by `selectedColumnDensity` and by
   `earlyProtectedClosureFromDmass`, and they are what *produce* the `A:141`
   column density the endpoint now demands.  The dyadic-class family is re-sited
   to `Fin q` so that it composes with the cover family.
3. **Non-vacuity left the degenerate `theta = 1` corner.**  `r0`'s only
   certificate ran at `theta = 1`, where `B_theta = 1` and the poor-`u`-set
   cover `u(B_theta - 1)` is the empty cover -- the exact corner in which the
   frozen argument has no content.  Round `r2` moved the certificate to
   `theta = 1/20480` and proved `2 <= B_theta <= 1100` there without evaluating
   the least search: `two_le_Btheta` from `theta <= rho_0`, and the tested
   endpoint `rho_0^{1100} < 1/20480` through the banked `coverExponent_le`,
   which is `06:657--693`'s own `eq:cover-tested-endpoint` discipline.  Both
   inequalities stand and are carried forward -- but round `r2`'s further claim
   that `1/20480` is a *legal* threshold does not, and is withdrawn above: the
   two theorems are now the floor-tier probes `Btheta_floorTier_ge_two` and
   `Btheta_floorTier_le`, and the legal-value bracket is
   `Btheta_bracket_at_scheduleTheta`.

## What this module lands, and what it deliberately does not

**Proved outright.**

1. The four block constants of `09:1378--1384` at their frozen values, with
   `B_theta` **consumed by pin** as `WrapperProjectionCovers.coverExponent` at
   base `rho_0` -- the frozen least-search is one definition, and re-rolling it
   here would be a restatement.
2. `lem:template-coordinate-extraction` **in full**, statement and proof: the
   ambient nontemplate count, the Markov threshold, the `u/2`-subset average
   through the frozen elementary ratio, and the completion-count division.  The
   fibre-completion step is the banked
   `WrapperProjectionCovers.card_le_prod_projSet_mul` at the one-element family
   `{J}`, consumed by pin, and the deliverable is the banked
   `WrapperProjectionCovers.projSet`.
3. The whole **extraction chain** of `09:1441--1497`: the light-donor discard,
   the dyadic classification and its pigeonhole, the least-dyadic `u` with the
   frozen two-sided bound `8 s kappa <= u d_cls < 16 s kappa`, the class-size
   bound `|V| >= u B_theta`, `eq:protected-delta-min`, the reverse-Markov fibre
   count that produces the represented Stage-2 blocks, the frozen block count
   `K_int = s kappa q_2`, and the ambient-width inequality `4 K_int <= (u/2)q_2`.
4. The cover step of `09:1458--1462`: a class of size at least `u B_theta`
   contains a `u`-set that is **not** poor, over the banked
   `WrapperProjectionCovers.productProjectionCover` and `PoorProjection`.
5. The endpoint arithmetic: `B_cap + log_2 K_int = C + log_2 kappa - 1` at the
   frozen exponents, over the banked `TerminalTwoStream.terminalTarget`.

6. The ambient-width inequality of `09:1491--1495` and the exact output-size
   equation `|Q_s| = r' p_seed = 9K/16` of `06:1128--1130` at the frozen dyadic
   widths (`ambient_width_ge`, `ExtensionCallThree.selected_count`), plus the
   whole exponent contract `eq:contract-extension-exponents` of `D:749--755`
   (`extensionCallThree_of_width`), so that row (iii) of the call table is
   **constructed** by `earlyProtectedClosureFromDmass` rather than assumed.
7. The reservoir halving of `09:1433--1439` (`protected_reservoir_halving`): the
   passage from `eq:protected-early-threshold` on the `mu_P`-weighted `P_v(J_0)`
   to `D_mass >= 64 B_theta L_q s kappa` on one reservoir type.  This is the step
   that makes `mu_P` load-bearing rather than decorative.
8. The composition of `09:1458--1471` into the entering column density
   `h = rho_1 2^{-u-1}` of row (iii) (`selectedColumnDensity`): the poor-`u`-set
   cover, the denser Bob child, and the template extraction, wired in that order,
   with the selected `u`-set transported into the `Y^u` ambient by the frozen
   relabelling `ambientRelabel`.  **Round `r2` of the density narrowing** makes
   that wiring load-bearing *inside `selectedColumnDensity`*: the query is a
   partition of the relabelled parent and the produced child carries its
   provenance and its `rho_1` density, so none of the three steps can be bypassed
   (`selectedColumnDensity_univ_child_pole`, `bobQuery_trivial_split_fails`).

   *This item previously over-claimed, and the over-claim is the incident of
   record.*  Making the chain load-bearing inside `selectedColumnDensity` did
   **not** make it load-bearing for the two closure theorems: the round-`r1`
   narrowing built the call record's `column_density` field from `le_refl _` and
   discarded the attained-density step, after which `hQuery`, `hS`, `hYT`,
   `hgap`, `hY`, `hYT0` (and the carriers `Y`, `S`, `YT`, `lamT`) were dead for
   the endpoint, exactly the inertness pattern one level up.  The **extraction
   re-gate** of this round repairs it at the only place that can: `hSelect` now
   takes the extraction's own output -- the child `P` with its provenance, the
   half-width `J'`, and the entering column density attained on it -- as an
   antecedent, and `earlyProtectedClosureFromDmass` supplies it from
   `selectedColumnDensity`.  The `09:1499` selection therefore consumes
   `09:1466--1471`, which is the frozen order, and deleting any one of the six
   hypotheses now breaks the proof rather than leaving it untouched.
9. `two_le_Btheta` and `Btheta_bracket_at_scheduleTheta`: at every threshold the
   frozen chain produces -- `theta = 1/(160 Q)` with `Q` the `06:532` least
   power of two above `Q_0 >= 16000` -- `B_theta >= 2`, so the poor-`u`-set
   cover `u(B_theta - 1)` is never the empty cover, and the
   `eq:cover-tested-endpoint` bound `B_theta <= 100 clog_2(160 Q)` caps the
   least search without evaluating it.  The round-`r2` pair at
   `theta = 1/20480` survives as the floor-tier probes
   `Btheta_floorTier_ge_two`, `Btheta_floorTier_le`, which claim no legality.
10. `ExtractionOutput` and its battery: the `09:1466--1471` deliverable named as
   the input of the `09:1499` selection, with **canonical inhabitation by the
   paper's own instance** (`extractionOutput_of_selectedColumnDensity` -- the
   frozen extraction produces it, nothing synthetic stands in for it),
   monotonicity in the retained parent (`extractionOutput_mono`), the content
   lemma that it forces a nonempty retained parent
   (`extractionOutput_forces_nonempty_parent`), and two poles:
   `extractionOutput_at_the_empty_parent_fails` and
   `extractionOutput_needs_a_template`, the latter proving in the kernel that the
   gate is **unsatisfiable** at an empty template alphabet, which is why `hYT0`
   is a hypothesis of both closure theorems rather than a convenience.

**Stated, not proved (named hypotheses, never axioms).**  The frozen block's
external contacts are all explicit binders of `earlyProtectedClosure`; none is an
`axiom`:

* `hLocEx`, the inherited `thm:certified-localized-extension` (`A:109--146`) at
  the `06:1147--1153` substitution, with its antecedents in the order the frozen
  theorem prints them;
* the `06`-owned analytic side of that endpoint -- `hbase` (`eq:certified-base`),
  `htcert` (`A:117`), `hE1`, `hE2` (`eq:certified-E1`, `eq:certified-E2`),
  `hrows` (`A:139--140`), `hx0`/`hx1`/`htx` (`A:112`, `A:118`) -- which
  `eq:tref-search` and `eq:all-extension-gates` discharge, not this block;
* `heps0`, `heps1`, the `A:126--128` product-branch balancedness error.  Call
  (iii) has `v = u/2 > 1`, so `06:1119--1120` places it on the product branch at
  `eps_prod` (`eq:epsilon-product`) rather than at the exact-full-product
  `eps = 0`.  **`EXPANDER-001` has no Lean declaration by design**: the cited
  balanced family reaches this module only through those two explicit binders and
  is never a silent axiom.  A ledger note is owed for this contact and is
  recorded in `OBLIGATION_LEDGER.md`;
* `hGate`, the structural-gate comparison of `06:1151--1152`, stated against
  `delta_min` (`eq:protected-delta-min`) rather than against `d_cls`;
* `hQuery` and `hBlocks`, the two GAP-EXPOSED protocol/geometry contacts named
  below;
* **round `r4`:** `hSelect`, the `09:1499--1504` selection -- that under `D_mass`
  the extraction produces exactly `9 K_int/16` represented blocks and the
  restriction they cut out of `Mhat` is realized at a child of `v` -- together
  with the abstract restriction datum `isRestr` it is stated against.  Both are
  GAP-EXPOSED; neither is an `axiom`, and `hSelect` is gated on the threshold
  **and on the `09:1466--1471` extraction output** (`ExtractionOutput`, added by
  round `r2`), so that neither a mass-free bundle nor a mass-plus-width-only
  bundle can reach the endpoint.

**Hypothesis consistency, discharged constructively at two tiers.**  Every gate
in this pipeline can pass while the principal deliverable is vacuous, so the
block-owned half of `earlyProtectedClosure`'s bundle is exhibited with models at
two clearly separated tiers.

*At the schedule's own values.*
`earlyProtectedClosure_block_bundle_at_scheduleTheta` and
`reachableWidth_at_scheduleTheta` satisfy the `B_theta` bracket, the
`eq:protected-delta-min` comparison, the structural gate and the Stage-2
comparison at `theta = 1/(160 Q)` for the `06:532` `Q` of the route
(`Q_0 >= 16000`, so `Q >= 2^14`), at every `s = 2^{r_3}` meeting the
`eq:s-choice` floor `512 <= s` with `64 | s`, at `kappa = 2^{ell} >= 2`
(`09:1420`), and at a wrapper width of the `eq:q-deltaU` shape
`q = 2^{A_wrap L_P^2}` whose `A_wrap` is produced rather than picked.  Nothing
in either is a numeral standing for a defined quantity.

*At the floor tier.*  `earlyProtectedClosure_block_bundle_is_consistent` and
`reachableWidth_floorTier_instance` keep the round-`r2` arithmetic at
`theta = 1/20480`, `q = 2^24`, `s = 4` (`r_3 = 2`), `kappa = 2`, `q_2 = 64`
(`r_2 = 6`), `k_2 = 4` (`t_2 = 16`, so `4 t_2 <= q_2` at `06:835`), `b_1 = 24`.
Those values meet the Section-4 floors and the Stage-2 structural gates and
**nothing else**: `eq:s-choice`, `eq:Q-theta-choice` and `eq:q-deltaU` all
refute them, so the two probes are BEYOND-PAPER audits of our encoding and no
parameter value may be read out of them.

Following the banked
`WrapperLowRungs.wrapperLowExtension_fires_at_legal_tier`, neither tier exhibits
an inhabitant of `hLocEx`, `hbase`, `hE1` or `hE2`, and the floor tier could
not: at small `k_2` those gates are unsatisfiable, which is exactly why
`eq:tref-search` (`06:558--572`) forces `k_ref >= 2^19`, hence a certified width
`t_ref = 2^{k_ref}`.  That
the whole shape is not merely non-contradictory but *right* is the separate
burden of the constructed call record: an earlier shape assumed row (iii)
uniformly in `(u, d_cls)`, and that bundle is **unsatisfiable** at legal widths,
because a large `d_cls` admits `u = 2` and then `4 K_int <= (u/2) q_2` fails.

**GAP-EXPOSED, recorded rather than papered over.**  Inside `09:1367--1511` the
following are *not* modelled and no declaration asserts them:
* the protocol object itself -- there is no Bob query, no child node, and no
  `first-Bob node v`.  `09:1463--1464` ("after Bob's query, one child has density
  at least `rho_1`") enters as `hQuery`, which after the round-`r2` repair
  supplies the frozen relabelling `iota : [u] -> J` of the selected donors as the
  coordinates of `Y^u` together with a genuine **partition** of the relabelled
  parent `iota(projSet J S)` into two children; the halving to `rho_1` is then
  the banked `DenseWrapperFrontier.denserChild_density` at `y = sqrt(rho_1)`.
  That `hQuery` still smuggles nothing in is
  `bobQuery_partition_is_satisfiable`: the degenerate query that sends every
  column to one child meets it at every `S`, `J` with `|J| = u`, so the binder
  asserts geometry and not existence.  What it no longer permits is the
  round-`r1` pair `P_0 := univ`, `P_1 := empty`, which met the old count-only
  form for **every** `S` (`bobQuery_trivial_split_fails`);
* the Stage-4 entry-map geometry of `09:1474--1476` ("in a protected reservoir,
  all rows carrying a fixed Stage-2 coordinate have the same Stage-4 entry
  map"), which is Section-8 reservoir structure: only its *counting* consequence
  is used, through the general reverse-Markov lemma `card_ge_of_sum_ge` and the
  block count `representedBlocks_ge`, with the availability of the counted
  blocks entering as `hBlocks`;
* the reservoir *structure* behind `09:1370--1373`: that there are exactly two
  protected row reservoirs per outer coordinate, each of mass `mu_P`, is an input
  of `protected_reservoir_halving` (the two density functions and the weighted
  threshold), not a conclusion;
* **round `r4`:** the relaxed `q`-copy interlace `Mhat` of `A:126--128` and its
  restrictions.  `Mem` here is an abstract cost carrier, so `A:138`'s "restriction
  of `Mhat`" is carried as the abstract predicate parameter `isRestr` and the
  `09:1499--1504` selection that produces one is the binder `hSelect`.  The
  concrete datum -- represented blocks, per-block rows, column density, with the
  `A:138--141` readouts -- is the banked `RestrictionDatum.RestrictionDatum`,
  which imports this module; composing the two is a registered forward
  obligation, not a claim made here.

`sec:wrapper-mass-redistribution` (`09:1512--1781`) remains GAP-EXPOSED in full.
No route completion is claimed.

## Reader counterpart

Searched first-hand in the frozen reader artifact
`routes/parameterized-np/reader-facing/sections/`: `rho_0`, `99/100`,
"template-coordinate", `K_int`, `B_theta`, `L_q`, `delta_min` and `d_cls` occur
**nowhere**.  The reader's only account of this block is prose inside the proof
of `thm:paper-adapted-stage4-interface`, at `A-stage4-details.tex:374--377`
("The fixed masses and the certified cover bounds ensure that either an early
protected reservoir already gives a hard restriction or one terminal owner
receives enough protected mass from a donor"), and reader line `374` is already
recorded by `WrapperProjectionCovers` as *unclaimed prose*; citing prose as a
statement is barred.  The one frozen constant with a reader locus is
`mu_P = 1/184`, at `A-stage4-details.tex:197`, opened first-hand this round:
"the base, selector, and diagonal column masses are exactly
`91/92, 1/184, 1/184`" -- the same **column** masses of the protected matrix that
the frozen `08:123--127` prints, and reader lines 196--199 are **already
assigned** to
`DenseStageFourOpening.protected_row_masses`; `muP` therefore *cites* that locus
and does **not** reclaim it.  **This module claims no reader item**, and
recording the absence is a finding about the reader artifact rather than an
omission.

## Axiom surface

`LegacyNPCC.Stage12` is **not** imported, directly or transitively through
`DenseWrapperFrontier`; the AGHP balanced-family axiom is not reached.  Every
declaration below is `Classical`-only.
-/

namespace EthInapproximability.ParameterizedNP.WrapperProtectedEarly

open Finset
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers

/-! ## Section 1  The block constants (`09:1370--1384`) -/

/-- **`09:1370--1373`.**  "Each outer coordinate contains two protected row
reservoirs, each of mass `mu_P = 1/184` relative to the `m` rows of one copy of
`N`."  The value is the frozen selector/diagonal **column** mass of the protected
matrix `A` printed at `08:123--127` and abbreviated `mu_Sigma = mu_D = 1/184` at
`08:134`, banked as `DenseStageFourOpening.protected_col_masses`; because the
wrapper's `N` is `A^T`, a column mass of `A` *is* a row-reservoir mass of `N`,
which is why `09:1370--1373` calls it a row reservoir.  It is *cited* here as the
numeral the wrapper block reuses, not re-derived. -/
noncomputable def muP : ℝ := 1 / 184

/-- **`09:1379`.**  `rho_0 = 99/100`, the poor-projection threshold of the donor
cover.  It is the same numeral as the banked
`WrapperProjectionCovers.rhoPair`, but a *different frozen constant* -- `09:380`
prints `rho_pair` for the pair cover of `sec:wrapper-projection-covers` (`09:376`
is `tau_0 = 2 s x_T`, a different display line; the round-`r1` citation of `376`
here was wrong and is corrected), and
`09:1379` prints `rho_0` for the `u`-set donor cover -- so it is named
separately and `rhoZero_eq_rhoPair` records the coincidence of values. -/
noncomputable def rhoZero : ℝ := 99 / 100

/-- **`09:1379`.**  `rho_1 = rho_0/2`, the density retained by the denser Bob
child. -/
noncomputable def rhoOne : ℝ := rhoZero / 2

/-- **`09:1378--1383`.**  `B_theta = min{B >= 1 : rho_0^B < theta}`.  Consumed by
pin from the banked least-search `WrapperProjectionCovers.coverExponent`, which
`09:408--410` and `09:1380` print in the same least-search form: `09:408--410`
prints only `B_*` and `B_pair`, and the third frozen search `B_theta` is the one
on `09:1380` (the round-`r1` reading of `09:408--410` as covering all three is
corrected here).  Nothing new is rolled. -/
noncomputable def Btheta (θ : ℝ) : ℕ := coverExponent rhoZero θ

/-- **`09:1382`.**  `L_q = ceil(log_2(2q)) + 1`, the number of dyadic donor
classes.  `Nat.clog 2` is the frozen `ceil(log_2 .)` on the naturals. -/
def Lq (q : ℕ) : ℕ := Nat.clog 2 (2 * q) + 1

/-- **Aux 1.1.**  `mu_P` is a genuine mass: strictly between `0` and `1`.
General (no hypotheses). -/
theorem muP_pos : 0 < muP := by norm_num [muP]

theorem muP_lt_one : muP < 1 := by norm_num [muP]

/-- **Aux 1.2.**  The frozen coincidence of numerals: `rho_0` and the banked
`rho_pair` are the same real, and recording the identity is what keeps the two
frozen names from being silently merged. -/
theorem rhoZero_eq_rhoPair : rhoZero = rhoPair := by norm_num [rhoZero, rhoPair]

theorem rhoZero_pos : 0 < rhoZero := by norm_num [rhoZero]

theorem rhoZero_lt_one : rhoZero < 1 := by norm_num [rhoZero]

/-- **Aux 1.3.**  `rho_1 = 99/200`, the frozen halving. -/
theorem rhoOne_eq : rhoOne = 99 / 200 := by norm_num [rhoOne, rhoZero]

theorem rhoOne_pos : 0 < rhoOne := by norm_num [rhoOne, rhoZero]

theorem rhoOne_lt_one : rhoOne < 1 := by norm_num [rhoOne, rhoZero]

/-- **`09:1466`, the schedule comparison.**  "The schedule gives
`1 - lambda_T <= 1/100 <= rho_1/8`."  The right-hand comparison is exact
arithmetic at the frozen numerals (`rho_1/8 = 99/1600`). -/
theorem one_hundredth_le_rhoOne_div_eight : (1 : ℝ) / 100 ≤ rhoOne / 8 := by
  norm_num [rhoOne, rhoZero]

/-- **`09:1466` composed with `eq:wrapper-template-gates`.**  The banked template
gates supply `lambda_T >= 99/100`, hence `1 - lambda_T <= 1/100 <= rho_1/8`,
which is exactly the hypothesis `lem:template-coordinate-extraction` needs at
`rho = rho_1`.  The gate predicate is consumed by pin; no clause is restated. -/
theorem templateGap_of_wrapperTemplateGates {mT : ℕ} {lamT eps2 tau0 : ℝ}
    (h : wrapperTemplateGates mT lamT eps2 tau0) : 1 - lamT ≤ rhoOne / 8 := by
  have hlam : (99 : ℝ) / 100 ≤ lamT := h.1
  have := one_hundredth_le_rhoOne_div_eight
  linarith

/-- **Aux 1.4 (`09:1378--1383` by pin).**  `B_theta >= 1` and
`rho_0^{B_theta} < theta` at every positive retained-column density `theta`.
Both come from the banked `coverExponent_spec`; `0 <= rho_0 < 1` is discharged
at the frozen numeral. -/
theorem Btheta_spec {θ : ℝ} (hθ : 0 < θ) :
    1 ≤ Btheta θ ∧ rhoZero ^ Btheta θ < θ :=
  coverExponent_spec (le_of_lt rhoZero_pos) rhoZero_lt_one hθ

theorem one_le_Btheta {θ : ℝ} (hθ : 0 < θ) : 1 ≤ Btheta θ := (Btheta_spec hθ).1

/-- **Aux 1.4b (`09:1378--1383` below the cover base).**  `B_theta >= 2`
whenever `theta <= rho_0`.  At `B_theta = 1` the search condition would read
`rho_0 < theta`, so the degenerate corner `B_theta = 1` -- where the poor-`u`-set
cover `u(B_theta - 1)` collapses to the empty cover and the frozen argument has
no content -- is reached only above the cover base.  General in `theta`: the
hypothesis is the comparison against `rho_0` and nothing schedule-specific, and
`Btheta_ge_two_at_scheduleTheta` is what feeds it the schedule's own threshold.
This lemma is what a non-vacuity certificate must invoke instead of evaluating
the least search. -/
theorem two_le_Btheta {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ rhoZero) : 2 ≤ Btheta θ := by
  by_contra hcon
  push Not at hcon
  have h1 : 1 ≤ Btheta θ := one_le_Btheta hθ0
  have hB : Btheta θ = 1 := by omega
  have hspec := (Btheta_spec hθ0).2
  rw [hB, pow_one] at hspec
  linarith

/-! ### The schedule's own row threshold (`eq:Q-theta-choice`, round `r3`)

`06:539` prints the threshold `eq:Q-theta-choice` hands this block in closed
form: `1/theta = 160 Q`, i.e. `theta = 1/(160 Q)`.  The five declarations below
evaluate the display's *defining chain* in dependency order rather than picking
a numeral under a locally visible ceiling, which is the round-`r3` repair.

`Q_0` and `Q` are **not** re-rolled here.  `EntryGates.Q0` transcribes the
maximum `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}` and
`EntryGates.Qwidth = 2 ^ EntryGates.rQ` is the least power of two at least
`Q_0`; both are consumed by pin, together with `EntryGates.Q0_le_Qwidth` and
`EntryGates.Qwidth_eq_two_pow`.  The banked module cites those from
`10-direct-bridge.tex:47--51`, which prints the display **byte for byte** as
`06:529--532` does -- opened first-hand this round on both sides, and recorded
downstream as the checked identity `ParameterSchedule.schedule_Q0_eq_entry_Q0`.
So `eq:Q-theta-choice`'s `Q_0` and `Q` reach this block through one interface,
not two. -/

/-- **Aux 1.4c (`06:529--531` evaluated at its first branch).**

`Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}`.  Round `r2` read only the
`16` branch.  The first branch is larger under the frozen side conditions:

* `b_out >= 1`.  `10-direct-bridge.tex:41`, inside
  `thm:direct-robustification` -- the very theorem whose display
  `EntryGates.Q0` transcribes -- reads "Fix an integer `b_out >= 1`", and
  `05:39--40` says the same of the public record ("`b_0, b_out in N` are
  positive incoming and requested outgoing / robustness depths"; the sentence
  wraps across the two lines and is cited as the straddle it is);
* `delta = 1/10`, `06:539` (and `10-direct-bridge.tex:37`), entering as the
  banked `EntryGates.deltaFixed` so that the numeral is not restated here;
* `0 < delta_U`, `10-direct-bridge.tex:38` ("let `0 < delta_U < 1`"), which
  `06:517`'s `delta_U = eta_R/(16q)` supplies at positive `eta_R` and `q`
  (banked downstream as `ParameterSchedule.deltaU_pos`);
* `delta_U <= 1/200`, `06:547`: "We also impose the finite gate
  `delta_U <= 1/200`."  On the route this gate is discharged by the downstream
  `ParameterSchedule.deltaU_le_gates` at the same `delta_U = eta_R/(16q)`; that
  module imports this one, so the gate enters here as a binder.

Hence `8 b_out/(delta delta_U) >= 8 . 1 . 10 . 200 = 16000`.  General in
`b_out` and `delta_U` over exactly those frozen conditions and nothing more. -/
theorem Q0_route_floor {bout : ℕ} {δU : ℝ} (hb : 1 ≤ bout) (hδ0 : 0 < δU)
    (hδ : δU ≤ 1 / 200) : (16000 : ℝ) ≤ EntryGates.Q0 bout δU := by
  have hbR : (1 : ℝ) ≤ (bout : ℝ) := by exact_mod_cast hb
  have hbranch : (16000 : ℝ) ≤ 8 * (bout : ℝ) / (EntryGates.deltaFixed * δU) := by
    rw [EntryGates.deltaFixed_eq, le_div_iff₀ (by positivity)]
    nlinarith [hbR, hδ0, hδ]
  refine le_trans hbranch ?_
  rw [EntryGates.Q0]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

/-- **Aux 1.4d (`06:532`, the least power of two above the floor).**

`Q` is a power of two, so a floor of `16000` on `Q_0` is a floor of
`2^14 = 16384` on `Q`: were `Q < 2^14` then `Q = 2^{r_Q} <= 2^13 = 8192 < 16000`,
contradicting `Q_0 <= Q`.  This is where `06:532`'s *least power of two*
accessor does work that no inequality on `Q_0` alone could do, and it is the
step round `r2` skipped when it read `Q = 2^7 = 128` off a ceiling. -/
theorem Qwidth_route_floor {bout : ℕ} {δU : ℝ} (hb : 1 ≤ bout) (hδ0 : 0 < δU)
    (hδ : δU ≤ 1 / 200) : 16384 ≤ EntryGates.Qwidth bout δU := by
  have h16000 := Q0_route_floor hb hδ0 hδ
  have hle := EntryGates.Q0_le_Qwidth bout δU
  have hpow : EntryGates.Qwidth bout δU = 2 ^ EntryGates.rQ bout δU :=
    EntryGates.Qwidth_eq_two_pow bout δU
  by_contra hcon
  have hlt : (2 : ℕ) ^ EntryGates.rQ bout δU < 2 ^ 14 := by
    rw [← hpow]; omega
  have hr : EntryGates.rQ bout δU < 14 :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hsmall : EntryGates.Qwidth bout δU ≤ 8192 := by
    rw [hpow]
    calc (2 : ℕ) ^ EntryGates.rQ bout δU ≤ 2 ^ 13 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8192 := by norm_num
  have : ((EntryGates.Qwidth bout δU : ℕ) : ℝ) ≤ 8192 := by exact_mod_cast hsmall
  linarith

/-- **Aux 1.4e (`06:539`).**  The schedule threshold `theta = 1/(160 Q)` is
positive at every positive width.  Written in `06:539`'s own closed form so that
no numeral stands in for `theta`. -/
theorem scheduleTheta_pos {Q : ℕ} (hQ : 0 < Q) : 0 < 1 / (160 * (Q : ℝ)) := by
  have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  positivity

/-- **Aux 1.4f (`06:539` against `09:1379`).**  Every schedule threshold lies
below the cover base `rho_0 = 99/100`: already at `Q = 1` the display gives
`theta = 1/160`.  This is the hypothesis `two_le_Btheta` consumes, and unlike
the round-`r2` argument it needs no ceiling on `theta` at all. -/
theorem scheduleTheta_le_rhoZero {Q : ℕ} (hQ : 0 < Q) :
    1 / (160 * (Q : ℝ)) ≤ rhoZero := by
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  rw [rhoZero, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- **Aux 1.4g (the route's threshold ceiling, fully collected).**

Composing `Qwidth_route_floor` with `06:539` gives
`theta = 1/(160 Q) <= 1/(160 . 16384) = 1/2621440` at every parameter setting the
route reaches.  Round `r2` recorded `1/2560` here, from the `16` branch of the
`Q_0` maximum alone.  The ceiling is *recorded*, never used to legalize a value
under it -- that inference is the defect this round repairs. -/
theorem scheduleTheta_route_le {bout : ℕ} {δU : ℝ} (hb : 1 ≤ bout) (hδ0 : 0 < δU)
    (hδ : δU ≤ 1 / 200) :
    1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)) ≤ 1 / 2621440 := by
  have hQ := Qwidth_route_floor hb hδ0 hδ
  have hQR : (16384 : ℝ) ≤ ((EntryGates.Qwidth bout δU : ℕ) : ℝ) := by
    exact_mod_cast hQ
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Aux 1.4h (`09:1378--1383` at the schedule's own threshold).**

`B_theta >= 2` at `theta = 1/(160 Q)` for every positive `Q`, hence at every
threshold `eq:Q-theta-choice` produces.  Nothing here is pinned: the statement
is uniform in `Q`, so the poor-`u`-set cover `u(B_theta - 1)` is non-empty at
every schedule point rather than at one exhibited numeral. -/
theorem Btheta_ge_two_at_scheduleTheta {Q : ℕ} (hQ : 0 < Q) :
    2 ≤ Btheta (1 / (160 * (Q : ℝ))) :=
  two_le_Btheta (scheduleTheta_pos hQ) (scheduleTheta_le_rhoZero hQ)

/-- **Aux 1.4i (`eq:cover-tested-endpoint`, `06:657--693`, at base `rho_0`).**

`B_theta <= 100 clog_2(160 Q)` at the schedule threshold `theta = 1/(160 Q)`.
The frozen discipline is to bound the least search by exhibiting *one* tested
exponent rather than evaluating the search: `rho_0^{100} < 1/2` gives
`rho_0^{100 r} < 2^{-r}`, and `2^{clog_2(160Q)} >= 160 Q` makes `2^{-r}` at
most `theta` at `r = clog_2(160 Q)`.

*Why `clog_2(160 Q)` is the frozen `bl`.*  `eq:cover-tested-endpoint` stores
`B^*_pair = 100 bl(den theta)` with `bl(v) = clog_2(v + 1)` (`06:665`,
`06:689--690`), so the frozen endpoint is `100 clog_2(160 Q + 1)`.  The two
agree here: `den theta = 160 Q = 5 * 2^{r_Q + 5}` always carries the odd factor
`5`, so it is never a power of two, and `clog_2(n) = clog_2(n + 1)` at every
non-power-of-two `n`.  The form stated below is therefore the frozen endpoint,
written without the `+ 1`.

The bound is a **function of** `Q`, and it has to be: a larger `Q` is a smaller
`theta` and forces a larger least search, so no constant caps `B_theta` over the
whole legal family.  That is the structural reason the round-`r2` constant
`1100` could only ever have been a statement about one pinned numeral.

*Forced duplication, recorded.*  The downstream `ParameterSchedule.Bpair_le_-`
`tested` proves the same estimate at the banked `ParameterSchedule.theta Q`
through `cover_tested_endpoint`.  `ParameterSchedule` **imports this module**,
so it cannot be consumed here; this is a local re-derivation of a banked
estimate across an import boundary that cannot be crossed, not a second
interface. -/
theorem Btheta_le_tested_at_scheduleTheta {Q : ℕ} (hQ : 0 < Q) :
    Btheta (1 / (160 * (Q : ℝ))) ≤ 100 * Nat.clog 2 (160 * Q) := by
  set r := Nat.clog 2 (160 * Q) with hr
  have hrpos : 0 < r := Nat.clog_pos (by norm_num) (by omega)
  refine coverExponent_le (by omega) ?_
  have hsplit : rhoZero ^ (100 * r) = (rhoZero ^ 100) ^ r := by rw [pow_mul]
  have h100 : rhoZero ^ 100 < 1 / 2 := by norm_num [rhoZero]
  have hnn : (0 : ℝ) ≤ rhoZero ^ 100 := by
    have := rhoZero_pos; positivity
  have hlt : (rhoZero ^ 100) ^ r < ((1 : ℝ) / 2) ^ r :=
    pow_lt_pow_left₀ h100 hnn (by omega)
  have hclog : (160 * Q : ℕ) ≤ 2 ^ r := Nat.le_pow_clog (by norm_num) _
  have hclogR : ((160 * Q : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hclog
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hhalf : ((1 : ℝ) / 2) ^ r ≤ 1 / (160 * (Q : ℝ)) := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast at hclogR
    linarith
  rw [hsplit]
  linarith

/-- **Aux 1.4j (the bracket the block consumes, at the schedule's threshold).**

`2 <= B_theta <= 100 clog_2(160 Q)` at `theta = 1/(160 Q)`.  This is the
round-`r3` replacement for the round-`r2` pair at `theta = 1/20480`: same two
facts, now uniform in the schedule width instead of pinned at a value
`eq:Q-theta-choice` cannot produce. -/
theorem Btheta_bracket_at_scheduleTheta {Q : ℕ} (hQ : 0 < Q) :
    2 ≤ Btheta (1 / (160 * (Q : ℝ))) ∧
      Btheta (1 / (160 * (Q : ℝ))) ≤ 100 * Nat.clog 2 (160 * Q) :=
  ⟨Btheta_ge_two_at_scheduleTheta hQ, Btheta_le_tested_at_scheduleTheta hQ⟩

/-! ### Floor-tier probes at `theta = 1/20480` (BEYOND-PAPER, round `r3`)

The two theorems below are the round-`r2` pair with the word "legal" withdrawn.
Round `r2` presented `theta = 1/20480` as `eq:Q-theta-choice` at `Q = 2^7 = 128`
and called it legal; `Q0_route_floor` and `Qwidth_route_floor` **refute** that
reading, since the route forces `Q >= 2^14`.  The arithmetic is untouched and
still true -- these are honest statements about the least search at one
particular density -- but they audit our encoding at a point the frozen
schedule never visits, so they carry no legality claim and no parameter value
may be read out of them.  Nothing below them depends on their being legal:
every consumer is itself a floor-tier probe. -/

/-- **FLOOR-TIER PROBE (BEYOND-PAPER; no legality claimed).**  `B_theta >= 2` at
the audit density `theta = 1/20480`, by `two_le_Btheta` from
`1/20480 <= rho_0`.  The density is **not** a schedule threshold: `06:529--531`
with `06:547` and `05:39--40` force `Q >= 2^14`, hence `theta <= 1/2621440`. -/
theorem Btheta_floorTier_ge_two : 2 ≤ Btheta (1 / 20480) :=
  two_le_Btheta (by norm_num) (by norm_num [rhoZero])

/-- **FLOOR-TIER PROBE (BEYOND-PAPER; no legality claimed).**  At the same audit
density the least search is at most `1100`, certified by `coverExponent_le` from
the tested endpoint `rho_0^{1100} < 1/20480` -- the `eq:cover-tested-endpoint`
discipline of `06:657--693` applied at a non-schedule point.  The endpoint is
checked in two stages (`rho_0^{100} < 37/100`, then eleventh powers) so no
`1100`-fold rational exponentiation is demanded of the kernel in one step.  The
legal-value counterpart is `Btheta_le_tested_at_scheduleTheta`, which is a
function of `Q` rather than a constant. -/
theorem Btheta_floorTier_le : Btheta (1 / 20480) ≤ 1100 := by
  refine coverExponent_le (by norm_num) ?_
  have hbase : (0 : ℝ) ≤ rhoZero ^ 100 := by
    have := rhoZero_pos
    positivity
  have h100 : rhoZero ^ 100 < 37 / 100 := by norm_num [rhoZero]
  have heq : rhoZero ^ 1100 = (rhoZero ^ 100) ^ 11 := by rw [← pow_mul]
  have hpow : (rhoZero ^ 100) ^ 11 < ((37 : ℝ) / 100) ^ 11 := by
    exact pow_lt_pow_left₀ h100 hbase (by norm_num)
  rw [heq]
  refine lt_of_lt_of_le hpow ?_
  norm_num

/-- **`06:1150`, the entering column density of call (iii).**  `h = rho_1 2^{-u-1}`
at the frozen width `u = 2^e` (`09:1449--1450`: `u` is the least *power of two*
at least `8 s kappa/d_cls`).  Written with a natural-number denominator so that
no negative exponent enters. -/
noncomputable def callThreeH (e : ℕ) : ℝ := rhoOne / 2 ^ (2 ^ e + 1)

/-- **Aux 1.4d (`A:128--129`).**  `h in (0,1]`, the frozen guard on the entering
density.  Both halves are proved outright, so neither is a field of the call
record. -/
theorem callThreeH_pos (e : ℕ) : 0 < callThreeH e :=
  div_pos rhoOne_pos (by positivity)

theorem callThreeH_le_one (e : ℕ) : callThreeH e ≤ 1 := by
  unfold callThreeH
  rw [div_le_one (by positivity)]
  have h1 : rhoOne ≤ 1 := le_of_lt rhoOne_lt_one
  have h2 : (1 : ℝ) ≤ 2 ^ (2 ^ e + 1) := one_le_pow₀ (by norm_num)
  linarith

/-- **Aux 1.5.**  `L_q >= 1`; the dyadic partition is never empty. -/
theorem one_le_Lq (q : ℕ) : 1 ≤ Lq q := Nat.le_add_left 1 _

theorem Lq_pos (q : ℕ) : 0 < Lq q := one_le_Lq q

/-- **Aux 1.6 (what `L_q` is for).**  `2q <= 2^{L_q}`: the frozen
`ceil(log_2(2q)) + 1` is large enough to index every dyadic class of a donor
weight lying in `(1/(2q), 1]`.  This is the only property of `L_q` the frozen
proof uses, and it is the one `exists_heavy_dyadic_class` consumes. -/
theorem two_mul_le_two_pow_Lq (q : ℕ) : 2 * q ≤ 2 ^ Lq q := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (2 * q)
  exact h.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))

/-! ## Section 2  `lem:template-coordinate-extraction` (`09:1388--1416`)

The frozen statement is about `P subseteq Y^u` for `u` divisible by four; the
Lean carrier is `Fin u -> Y` with the zero-based slot convention
(`conv:finite-slots`).  Everything in this section is general in `Y`, `u`, `P`,
`Y_T`, `rho` and `lambda_T`. -/

section TemplateExtraction

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {u : ℕ}

/-- **`09:1402--1403`.**  "the number of nontemplate coordinates" of one tuple. -/
def nonTemplateCount (YT : Finset Y) (f : Fin u → Y) : ℕ :=
  (Finset.univ.filter (fun i => f i ∉ YT)).card

/-- **`09:1404--1405`.**  The set of template coordinates of one tuple. -/
def templateSet (YT : Finset Y) (f : Fin u → Y) : Finset (Fin u) :=
  Finset.univ.filter (fun i => f i ∈ YT)

omit [Fintype Y] in
/-- **Aux 2.1.**  Template and nontemplate coordinates partition the `u`
coordinates.  General. -/
theorem templateSet_add_nonTemplateCount (YT : Finset Y) (f : Fin u → Y) :
    (templateSet YT f).card + nonTemplateCount YT f = u := by
  classical
  simpa [templateSet, nonTemplateCount, Finset.card_univ] using
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin u))) (p := fun i => f i ∈ YT)

/-- **Aux 2.2 (the ambient fibre count).**  Exactly `(|Y| - |Y_T|)|Y|^{u-1}` of
the `|Y|^u` tuples are nontemplate at a fixed coordinate.  This is the exact
count the frozen expectation `u(1-lambda_T)/rho` is computed from.  General. -/
theorem card_filter_nonTemplate_coord (YT : Finset Y) (i : Fin u) :
    (Finset.univ.filter (fun f : Fin u → Y => f i ∉ YT)).card
      = (Fintype.card Y - YT.card) * (Fintype.card Y) ^ (u - 1) := by
  classical
  have hset : (Finset.univ.filter (fun f : Fin u → Y => f i ∉ YT))
      = Fintype.piFinset (fun j => if j = i then YTᶜ else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj; simpa using h
      · simp [hj]
    · intro h
      have := h i
      simpa using this
  rw [hset, Fintype.card_piFinset]
  rw [Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i)]
  have hrest : ∀ j ∈ (Finset.univ : Finset (Fin u)) \ {i},
      (if j = i then (YTᶜ : Finset Y) else Finset.univ).card = Fintype.card Y := by
    intro j hj
    have : j ≠ i := by simpa using (Finset.mem_sdiff.mp hj).2
    simp [this]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const]
  have hcard : ((Finset.univ : Finset (Fin u)) \ {i}).card = u - 1 := by
    simp [Finset.card_sdiff, Finset.card_univ]
  rw [hcard]
  simp [Finset.card_compl]
  ring

/-- **Aux 2.3.**  Summing Aux 2.2 over the `u` coordinates: the total nontemplate
count over the whole ambient cube.  General. -/
theorem sum_nonTemplateCount_univ (YT : Finset Y) :
    ∑ f : Fin u → Y, nonTemplateCount YT f
      = u * ((Fintype.card Y - YT.card) * (Fintype.card Y) ^ (u - 1)) := by
  classical
  have hswap : ∑ f : Fin u → Y, nonTemplateCount YT f
      = ∑ i : Fin u, (Finset.univ.filter (fun f : Fin u → Y => f i ∉ YT)).card := by
    simp only [nonTemplateCount, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  simp [card_filter_nonTemplate_coord, Finset.card_univ]

omit [Fintype Y] [DecidableEq Y] in
/-- **`09:1405--1410`, the `u/2`-subset average.**

"Average the `u/2`-subsets of those template positions.  The elementary ratio
`binom(3u/4, u/2)/binom(u, u/2) >= 2^{-u}` shows that one coordinate set receives
at least a `2^{-u-1}` fraction of all tuples."

The frozen ratio is used here in its two elementary halves -- `binom(n, k) >= 1`
whenever `k <= n`, and `binom(u, k) <= 2^u` -- which is exactly the bound the
frozen sentence asserts, and which is why no hypothesis about `3u/4` beyond
`k <= |T f|` appears.  General in the ambient index type's size `u`, in the
family `T`, and in `k`. -/
theorem exists_subset_of_average {ι : Type*}
    (P : Finset ι) (T : ι → Finset (Fin u)) (k : ℕ)
    (hk : k ≤ u) (hT : ∀ f ∈ P, k ≤ (T f).card) :
    ∃ J : Finset (Fin u), J.card = k ∧
      P.card ≤ 2 ^ u * (P.filter (fun f => J ⊆ T f)).card := by
  classical
  set A : Finset (Finset (Fin u)) := Finset.powersetCard k Finset.univ with hA
  have hAne : A.Nonempty := by
    rw [hA, ← Finset.card_pos, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact Nat.choose_pos hk
  have hswap : ∑ J ∈ A, (P.filter (fun f => J ⊆ T f)).card
      = ∑ f ∈ P, (Finset.powersetCard k (T f)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro f _
    rw [← Finset.card_filter]
    congr 1
    ext J
    simp [hA, Finset.mem_powersetCard]
    tauto
  have hlow : P.card ≤ ∑ J ∈ A, (P.filter (fun f => J ⊆ T f)).card := by
    rw [hswap]
    calc P.card = ∑ _f ∈ P, 1 := by simp
      _ ≤ ∑ f ∈ P, (Finset.powersetCard k (T f)).card := by
          refine Finset.sum_le_sum ?_
          intro f hf
          rw [Finset.card_powersetCard]
          exact Nat.choose_pos (hT f hf)
  obtain ⟨J, hJA, hJmax⟩ := Finset.exists_max_image A
    (fun J => (P.filter (fun f => J ⊆ T f)).card) hAne
  refine ⟨J, ?_, ?_⟩
  · exact (Finset.mem_powersetCard.mp (by rw [← hA]; exact hJA)).2
  · calc P.card ≤ ∑ J' ∈ A, (P.filter (fun f => J' ⊆ T f)).card := hlow
      _ ≤ ∑ _J' ∈ A, (P.filter (fun f => J ⊆ T f)).card :=
          Finset.sum_le_sum (fun J' hJ' => hJmax J' hJ')
      _ = A.card * (P.filter (fun f => J ⊆ T f)).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ u * (P.filter (fun f => J ⊆ T f)).card := by
          refine Nat.mul_le_mul_right _ ?_
          rw [hA, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          exact Nat.choose_le_two_pow u k

/-- **`lem:template-coordinate-extraction` (`09:1388--1416`), proved.**

"Let `P subseteq Y^u` have density at least `rho`, where `u` is divisible by
four, and let `Y_T subseteq Y` have density `lambda_T` with
`1 - lambda_T <= rho/8`.  Some set of `u/2` coordinates has an all-template
projection of density at least `rho 2^{-u-1}` inside `Y_T^{u/2}`."

Both densities are written multiplicatively against the frozen denominators --
`rho |Y|^u <= |P|` on the way in and `rho |Y_T|^{u/2} <= 2^{u+1} |proj|` on the
way out -- so that no division is taken and the empty-alphabet case is not
silently excluded; `0 < |Y|` is carried explicitly, exactly as the banked
`productProjectionCover` carries it.  The deliverable is the banked
`WrapperProjectionCovers.projSet` of the all-template subfamily, so nothing is
re-defined.

The existential is not satisfied by a trivial witness: at
`templateCoordinateExtraction_trivial_witness_fails` the empty projection makes
the right-hand side `0` while the left-hand side is positive. -/
theorem templateCoordinateExtraction (P : Finset (Fin u → Y)) (YT : Finset Y)
    {ρ lamT : ℝ}
    (hu : 4 ∣ u) (hu0 : 0 < u) (hY : 0 < Fintype.card Y)
    (hρ0 : 0 < ρ)
    (hP : ρ * (Fintype.card Y : ℝ) ^ u ≤ (P.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ ρ / 8) :
    ∃ J : Finset (Fin u), J.card = u / 2 ∧
      ρ * (YT.card : ℝ) ^ (u / 2)
        ≤ 2 ^ (u + 1) *
          ((projSet J (P.filter (fun f => ∀ i ∈ J, f i ∈ YT))).card : ℝ) := by
  classical
  have hYTle : YT.card ≤ Fintype.card Y := Finset.card_le_univ YT
  -- `09:1402--1403`: the ambient nontemplate expectation, in exact counts.
  have hsum : ((∑ f ∈ P, nonTemplateCount YT f : ℕ) : ℝ) ≤ (u : ℝ) * (P.card : ℝ) / 8 := by
    have h1 : (∑ f ∈ P, nonTemplateCount YT f) ≤ ∑ f : Fin u → Y, nonTemplateCount YT f :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ P)
    rw [sum_nonTemplateCount_univ] at h1
    have h2 : ((∑ f ∈ P, nonTemplateCount YT f : ℕ) : ℝ)
        ≤ (u : ℝ) * (((Fintype.card Y - YT.card : ℕ) : ℝ)
            * ((Fintype.card Y : ℝ)) ^ (u - 1)) := by
      exact_mod_cast h1
    have h3 : ((Fintype.card Y - YT.card : ℕ) : ℝ) ≤ (ρ / 8) * (Fintype.card Y : ℝ) := by
      rw [Nat.cast_sub hYTle]
      have hstep : (Fintype.card Y : ℝ) - (YT.card : ℝ)
          ≤ (Fintype.card Y : ℝ) - lamT * (Fintype.card Y : ℝ) := by linarith
      have hcard : (0:ℝ) ≤ (Fintype.card Y : ℝ) := by positivity
      nlinarith [hstep]
    have hpow : (0:ℝ) ≤ ((Fintype.card Y : ℝ)) ^ (u - 1) := by positivity
    have h4 : ((∑ f ∈ P, nonTemplateCount YT f : ℕ) : ℝ)
        ≤ (u : ℝ) * ((ρ / 8) * (Fintype.card Y : ℝ) * ((Fintype.card Y : ℝ)) ^ (u - 1)) := by
      refine h2.trans ?_
      gcongr
    have hpowu : (Fintype.card Y : ℝ) * ((Fintype.card Y : ℝ)) ^ (u - 1)
        = ((Fintype.card Y : ℝ)) ^ u := by
      rw [← pow_succ']
      congr 1
      omega
    rw [show (u : ℝ) * ((ρ / 8) * (Fintype.card Y : ℝ) * ((Fintype.card Y : ℝ)) ^ (u - 1))
        = (u : ℝ) * (ρ / 8) * ((Fintype.card Y : ℝ) * ((Fintype.card Y : ℝ)) ^ (u - 1)) by ring,
      hpowu] at h4
    refine h4.trans ?_
    have hun : (0:ℝ) ≤ (u:ℝ) := by positivity
    have hlast : (u : ℝ) * (ρ / 8) * ((Fintype.card Y : ℝ)) ^ u
        ≤ (u : ℝ) * (P.card : ℝ) / 8 := by
      nlinarith [hP, hun]
    linarith [hlast]
  -- `09:1403--1405`: Markov's inequality at the frozen threshold `3u/4`.
  set Good : Finset (Fin u → Y) :=
    P.filter (fun f => 3 * u ≤ 4 * (templateSet YT f).card) with hGood
  have hMarkov : (P.card : ℝ) ≤ 2 * (Good.card : ℝ) := by
    set Bad : Finset (Fin u → Y) :=
      P.filter (fun f => ¬ (3 * u ≤ 4 * (templateSet YT f).card)) with hBad
    have hsplit : Good.card + Bad.card = P.card := by
      rw [hGood, hBad]
      exact Finset.card_filter_add_card_filter_not _
    have hbadpt : ∀ f ∈ Bad, u ≤ 4 * nonTemplateCount YT f := by
      intro f hf
      have hmem := Finset.mem_filter.mp (by rw [← hBad]; exact hf)
      have := templateSet_add_nonTemplateCount YT f
      omega
    have hbadsum : (u : ℕ) * Bad.card ≤ 4 * ∑ f ∈ P, nonTemplateCount YT f := by
      calc (u : ℕ) * Bad.card = ∑ _f ∈ Bad, u := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ f ∈ Bad, 4 * nonTemplateCount YT f := Finset.sum_le_sum hbadpt
        _ = 4 * ∑ f ∈ Bad, nonTemplateCount YT f := by rw [Finset.mul_sum]
        _ ≤ 4 * ∑ f ∈ P, nonTemplateCount YT f := by
            refine Nat.mul_le_mul_left _ ?_
            exact Finset.sum_le_sum_of_subset (by rw [hBad]; exact Finset.filter_subset _ _)
    have hbadR : (u : ℝ) * (Bad.card : ℝ)
        ≤ 4 * (((∑ f ∈ P, nonTemplateCount YT f : ℕ)) : ℝ) := by
      exact_mod_cast hbadsum
    have hu0R : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu0
    have hbad2 : (Bad.card : ℝ) ≤ (P.card : ℝ) / 2 := by
      have hmul : (u : ℝ) * (Bad.card : ℝ) ≤ (u : ℝ) * ((P.card : ℝ) / 2) := by
        calc (u : ℝ) * (Bad.card : ℝ)
            ≤ 4 * (((∑ f ∈ P, nonTemplateCount YT f : ℕ)) : ℝ) := hbadR
          _ ≤ 4 * ((u : ℝ) * (P.card : ℝ) / 8) := by linarith [hsum]
          _ = (u : ℝ) * ((P.card : ℝ) / 2) := by ring
      exact le_of_mul_le_mul_left hmul hu0R
    have hsplitR : (Good.card : ℝ) + (Bad.card : ℝ) = (P.card : ℝ) := by exact_mod_cast hsplit
    linarith
  -- `09:1405--1410`: the `u/2`-subset average.
  have hk : u / 2 ≤ u := Nat.div_le_self u 2
  have hT : ∀ f ∈ Good, u / 2 ≤ (templateSet YT f).card := by
    intro f hf
    have hmem := Finset.mem_filter.mp (by rw [← hGood]; exact hf)
    obtain ⟨c, hc⟩ := hu
    have := templateSet_add_nonTemplateCount YT f
    omega
  obtain ⟨J, hJcard, hJmany⟩ := exists_subset_of_average Good (templateSet YT) (u / 2) hk hT
  refine ⟨J, hJcard, ?_⟩
  set SJ : Finset (Fin u → Y) := Good.filter (fun f => J ⊆ templateSet YT f) with hSJ
  set Sfull : Finset (Fin u → Y) := P.filter (fun f => ∀ i ∈ J, f i ∈ YT) with hSfull
  have hsub : SJ ⊆ Sfull := by
    intro f hf
    have hmem := Finset.mem_filter.mp (by rw [← hSJ]; exact hf)
    have hfP : f ∈ P := (Finset.mem_filter.mp (by rw [← hGood]; exact hmem.1)).1
    rw [hSfull, Finset.mem_filter]
    refine ⟨hfP, ?_⟩
    intro i hi
    have := hmem.2 hi
    simpa [templateSet] using this
  have hproj : (projSet J SJ).card ≤ (projSet J Sfull).card :=
    Finset.card_le_card (projSet_mono hsub)
  have hcompl : (Jᶜ : Finset (Fin u)).card = u / 2 := by
    rw [Finset.card_compl, hJcard, Fintype.card_fin]
    omega
  -- `09:1410--1412`: dividing by the completions of one projected pattern,
  -- through the banked one-element-family projection bound.
  have hfibre : SJ.card ≤ (projSet J SJ).card * Fintype.card Y ^ (u / 2) := by
    have := card_le_prod_projSet_mul SJ {J}
    simpa [hcompl] using this
  have hYR : (0:ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hsplitpow : ((Fintype.card Y : ℝ)) ^ u
      = ((Fintype.card Y : ℝ)) ^ (u / 2) * ((Fintype.card Y : ℝ)) ^ (u / 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hGoodR : (Good.card : ℝ) ≤ 2 ^ u * (SJ.card : ℝ) := by
    have hnat : (Good.card : ℕ) ≤ 2 ^ u * SJ.card := hJmany
    exact_mod_cast hnat
  have hfibreR : (SJ.card : ℝ)
      ≤ ((projSet J SJ).card : ℝ) * ((Fintype.card Y : ℝ)) ^ (u / 2) := by
    exact_mod_cast hfibre
  have hprojR : ((projSet J SJ).card : ℝ) ≤ ((projSet J Sfull).card : ℝ) := by
    exact_mod_cast hproj
  have hpowpos : (0:ℝ) < ((Fintype.card Y : ℝ)) ^ (u / 2) := by positivity
  have hchain : ρ * ((Fintype.card Y : ℝ)) ^ (u / 2) * ((Fintype.card Y : ℝ)) ^ (u / 2)
      ≤ 2 ^ (u + 1) * ((projSet J Sfull).card : ℝ) * ((Fintype.card Y : ℝ)) ^ (u / 2) := by
    calc ρ * ((Fintype.card Y : ℝ)) ^ (u / 2) * ((Fintype.card Y : ℝ)) ^ (u / 2)
        = ρ * ((Fintype.card Y : ℝ)) ^ u := by rw [hsplitpow]; ring
      _ ≤ (P.card : ℝ) := hP
      _ ≤ 2 * (Good.card : ℝ) := hMarkov
      _ ≤ 2 * (2 ^ u * (SJ.card : ℝ)) := by linarith
      _ ≤ 2 * (2 ^ u * (((projSet J SJ).card : ℝ) * ((Fintype.card Y : ℝ)) ^ (u / 2))) := by
          gcongr
      _ ≤ 2 * (2 ^ u * (((projSet J Sfull).card : ℝ)
            * ((Fintype.card Y : ℝ)) ^ (u / 2))) := by gcongr
      _ = 2 ^ (u + 1) * ((projSet J Sfull).card : ℝ) * ((Fintype.card Y : ℝ)) ^ (u / 2) := by
          rw [pow_succ]; ring
  have hdiv : ρ * ((Fintype.card Y : ℝ)) ^ (u / 2)
      ≤ 2 ^ (u + 1) * ((projSet J Sfull).card : ℝ) :=
    le_of_mul_le_mul_right (by linarith [hchain]) hpowpos
  have hYTle' : (YT.card : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hYTle
  have hYTpow : ((YT.card : ℝ)) ^ (u / 2) ≤ ((Fintype.card Y : ℝ)) ^ (u / 2) := by gcongr
  calc ρ * ((YT.card : ℝ)) ^ (u / 2) ≤ ρ * ((Fintype.card Y : ℝ)) ^ (u / 2) := by gcongr
    _ ≤ 2 ^ (u + 1) * ((projSet J Sfull).card : ℝ) := hdiv

omit [Fintype Y] in
/-- **Aux 2.4 (the deliverable really is all-template).**  Every pattern counted
by `templateCoordinateExtraction` lands inside `Y_T^{|J|}`, which is what
"all-template projection ... inside `Y_T^{u/2}`" asserts.  General. -/
theorem projSet_filter_mem_template (P : Finset (Fin u → Y)) (YT : Finset Y)
    (J : Finset (Fin u)) :
    ∀ g ∈ projSet J (P.filter (fun f => ∀ i ∈ J, f i ∈ YT)), ∀ i : ↥J, g i ∈ YT := by
  classical
  intro g hg i
  rw [projSet, Finset.mem_image] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  exact (Finset.mem_filter.mp hf).2 i.1 i.2

end TemplateExtraction

/-! ## Section 2b  The reservoir halving and `eq:protected-early-threshold`
(`09:1370--1376`, `09:1433--1439`) -/

/-- **`09:1370--1376` composed with `09:1433--1439`, the reservoir halving,
proved.**

"Each outer coordinate contains two protected row reservoirs, each of mass
`mu_P = 1/184` relative to the `m` rows of one copy of `N`.  For a first-Bob node
`v` and a donor set `J_0 subseteq [q]`, let `P_v(J_0)` denote, normalized by `m`,
the protected mass from those donors reaching `v`" (`09:1370--1376`); and "One of
the two protected reservoir types contributes at least half of
`eq:protected-early-threshold`.  Let `d_j in [0,1]` be the retained relative
density of this type from donor `j`, and write `D_mass = sum_j d_j`.  Then
`D_mass >= 64 B_theta L_q s kappa`" (`09:1433--1439`).

`P_v(J_0)` is modelled as the `mu_P`-weighted total of the two type sums -- that
is exactly what the frozen normalization "relative to the `m` rows" says, and it
is what makes the two frozen constants match: the `128 mu_P B_theta L_q s kappa`
of `eq:protected-early-threshold` (`09:1421--1425`) becomes
`64 B_theta L_q s kappa` on the `D_mass` side once `mu_P` cancels.  This is the
step at which `mu_P` is load-bearing, and it is why `earlyProtectedClosure` may
be stated at the lemma's own threshold rather than at the derived `D_mass` form.

No reservoir *structure* is asserted: which rows lie in which reservoir, and the
fact that there are exactly two types, are inputs (the two functions `d_0`,
`d_1`), not conclusions.  General in the donor index type and in the four
constants. -/
theorem protected_reservoir_halving {ι : Type*} (J₀ : Finset ι) (d₀ d₁ : ι → ℝ)
    {B L : ℕ} {s κ : ℝ}
    (hthr : 128 * muP * (B : ℝ) * (L : ℝ) * s * κ
        ≤ muP * ((∑ j ∈ J₀, d₀ j) + (∑ j ∈ J₀, d₁ j))) :
    64 * (B : ℝ) * (L : ℝ) * s * κ ≤ ∑ j ∈ J₀, d₀ j ∨
      64 * (B : ℝ) * (L : ℝ) * s * κ ≤ ∑ j ∈ J₀, d₁ j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hμ : 0 < muP := muP_pos
  have hsum : (∑ j ∈ J₀, d₀ j) + (∑ j ∈ J₀, d₁ j) < 128 * (B : ℝ) * (L : ℝ) * s * κ := by
    linarith
  have hmul := mul_lt_mul_of_pos_left hsum hμ
  nlinarith [hmul, hthr]

/-- **Aux 2b.1 (the halving is not vacuous).**  At a donor set carrying the
frozen threshold with the two types equal, both branches of
`protected_reservoir_halving` fire.  This records that the disjunction is
reachable rather than being satisfied only by an unsatisfiable antecedent. -/
theorem protected_reservoir_halving_is_live :
    128 * muP * (1 : ℝ) * (1 : ℝ) * 1 * 1 ≤ muP * ((64 : ℝ) + 64) := by
  have hμ : 0 < muP := muP_pos
  nlinarith [hμ]

/-! ## Section 3  The dyadic donor classes (`09:1441--1448`) -/

/-- **`09:1443--1444`.**  The dyadic class index of a donor weight `d`: the
unique `k` with `2^{-(k+1)} < d <= 2^{-k}`. -/
noncomputable def classIndex (d : ℝ) : ℕ := Nat.log 2 ⌊1 / d⌋₊

/-- **`09:1443--1444`.**  The class representative `d_cls = 2^{-k}`, written as
`1/2^k` so that no negative exponent enters. -/
noncomputable def classWidth (k : ℕ) : ℝ := 1 / 2 ^ k

theorem classWidth_pos (k : ℕ) : 0 < classWidth k := by
  unfold classWidth; positivity

theorem classWidth_le_one (k : ℕ) : classWidth k ≤ 1 := by
  unfold classWidth
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

/-- **Aux 3.1 (the defining property of the class index).**  For
`0 < d <= 1`, `d <= d_cls` and `d_cls < 2d` at `d_cls = classWidth (classIndex d)`,
i.e. exactly the frozen `d_cls/2 < d_j <= d_cls`.  General. -/
theorem classIndex_spec {d : ℝ} (h0 : 0 < d) (h1 : d ≤ 1) :
    d ≤ classWidth (classIndex d) ∧ classWidth (classIndex d) < 2 * d := by
  have hinv : (1:ℝ) ≤ 1 / d := by
    rw [le_div_iff₀ h0]; linarith
  have hfl : 1 ≤ ⌊1 / d⌋₊ := Nat.le_floor (by exact_mod_cast hinv)
  have hne : ⌊1 / d⌋₊ ≠ 0 := by omega
  set k := classIndex d with hk
  have hlow : (2 : ℕ) ^ k ≤ ⌊1 / d⌋₊ := by
    rw [hk, classIndex]
    exact Nat.pow_log_le_self 2 hne
  have hhigh : ⌊1 / d⌋₊ < 2 ^ (k + 1) := by
    rw [hk, classIndex]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hlowR : ((2 : ℝ)) ^ k ≤ 1 / d := by
    have h1' : ((2 : ℕ) ^ k : ℝ) ≤ (⌊1 / d⌋₊ : ℝ) := by exact_mod_cast hlow
    have h2' : ((⌊1 / d⌋₊ : ℕ) : ℝ) ≤ 1 / d := Nat.floor_le (by positivity)
    push_cast at h1'
    linarith
  have hhighR : 1 / d < ((2 : ℝ)) ^ (k + 1) := by
    have hlt : (⌊1 / d⌋₊ : ℝ) + 1 > 1 / d := Nat.lt_floor_add_one (1 / d)
    have hle : ((⌊1 / d⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) ^ (k + 1) : ℝ) := by
      exact_mod_cast hhigh
    push_cast at hle
    linarith
  have hpk : (0:ℝ) < ((2:ℝ)) ^ k := by positivity
  have hmul1 : ((2:ℝ)) ^ k * d ≤ 1 := by
    have hstep := mul_le_mul_of_nonneg_right hlowR (le_of_lt h0)
    rwa [div_mul_cancel₀ _ (ne_of_gt h0)] at hstep
  have hmul2 : 1 < 2 * ((2:ℝ)) ^ k * d := by
    have hstep : 1 / d < 2 * ((2:ℝ)) ^ k := by
      rw [pow_succ] at hhighR; linarith
    have hstep2 := mul_lt_mul_of_pos_right hstep h0
    rwa [div_mul_cancel₀ _ (ne_of_gt h0)] at hstep2
  constructor
  · rw [classWidth, le_div_iff₀ hpk]
    linarith [hmul1]
  · rw [classWidth, div_lt_iff₀ hpk]
    linarith [hmul2]

/-- **Aux 3.2 (only `L_q` classes are needed).**  A donor weight in
`(delta, 1]` with `1/delta <= 2^L` has class index below `L`.  This is the sole
use the frozen proof makes of `L_q`.  General. -/
theorem classIndex_lt {d δ : ℝ} {L : ℕ} (hδ : 0 < δ) (hd : δ < d) (hd1 : d ≤ 1)
    (hL : 1 / δ ≤ (2 : ℝ) ^ L) : classIndex d < L := by
  have h0 : 0 < d := lt_trans hδ hd
  have hspec := classIndex_spec h0 hd1
  set k := classIndex d with hk
  have hlow : d ≤ classWidth k := hspec.1
  have hpow : ((2:ℝ)) ^ k * d ≤ 1 := by
    rw [classWidth, le_div_iff₀ (by positivity : (0:ℝ) < ((2:ℝ)) ^ k)] at hlow
    linarith
  have hstrict : ((2:ℝ)) ^ k < (2 : ℝ) ^ L := by
    have h1 : ((2:ℝ)) ^ k ≤ 1 / d := by
      rw [le_div_iff₀ h0]; linarith
    have h2 : (1:ℝ) / d < 1 / δ := by
      exact one_div_lt_one_div_of_lt hδ hd
    linarith
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hstrict

/-- **`09:1441--1443`, the light-donor discard.**  "Discard donors with
`d_j < D_mass/(2q)`.  Their total contribution is below `D_mass/2`."  Written
non-strictly (`<=` on both sides), which is the direction the frozen proof
consumes, and subtraction-free.  General. -/
theorem sum_light_le_half {ι : Type*} (J : Finset ι) (d : ι → ℝ)
    {D : ℝ} {q : ℕ} (hq : 0 < q) (hJ : J.card ≤ q) (hD : 0 ≤ D) :
    ∑ j ∈ J.filter (fun j => d j ≤ D / (2 * q)), d j ≤ D / 2 := by
  classical
  have hqR : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  calc ∑ j ∈ J.filter (fun j => d j ≤ D / (2 * q)), d j
      ≤ ∑ _j ∈ J.filter (fun j => d j ≤ D / (2 * q)), D / (2 * q) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact (Finset.mem_filter.mp hj).2
    _ = (J.filter (fun j => d j ≤ D / (2 * q))).card * (D / (2 * q)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) * (D / (2 * q)) := by
        have hcard : ((J.filter (fun j => d j ≤ D / (2 * q))).card : ℝ) ≤ (q : ℝ) := by
          have : (J.filter (fun j => d j ≤ D / (2 * q))).card ≤ q :=
            le_trans (Finset.card_filter_le _ _) hJ
          exact_mod_cast this
        have hpos : (0:ℝ) ≤ D / (2 * q) := by positivity
        exact mul_le_mul_of_nonneg_right hcard hpos
    _ = D / 2 := by field_simp

/-- **`09:1443--1448`, the dyadic pigeonhole.**  "Partition the others into at
most `L_q` dyadic classes `d_cls/2 < d_j <= d_cls`.  Some class `V` satisfies
`|V| d_cls >= D_mass/(2 L_q)`."

The class index is `classIndex`, its representative `classWidth`, and the
pigeonhole is over the `L_q` fibres of `classIndex` on the surviving donors.
General in the index type, in `d`, and in `D`. -/
theorem exists_heavy_dyadic_class {ι : Type*} (J : Finset ι) (d : ι → ℝ)
    {D : ℝ} {q : ℕ} (hq : 0 < q) (hJ : J.card ≤ q)
    (_hd0 : ∀ j ∈ J, 0 ≤ d j) (hd1 : ∀ j ∈ J, d j ≤ 1)
    (hD1 : 1 ≤ D) (hDsum : D ≤ ∑ j ∈ J, d j) :
    ∃ (k : ℕ) (V : Finset ι), V ⊆ J ∧
      (∀ j ∈ V, classWidth k < 2 * d j ∧ d j ≤ classWidth k) ∧
      D / (2 * Lq q) ≤ (V.card : ℝ) * classWidth k ∧
      D / (2 * q) ≤ classWidth k := by
  classical
  have hD0 : (0:ℝ) ≤ D := by linarith
  have hqR : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  set δ : ℝ := D / (2 * q) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]; positivity
  set H : Finset ι := J.filter (fun j => ¬ (d j ≤ δ)) with hH
  have hheavy : D / 2 ≤ ∑ j ∈ H, d j := by
    have hlight : ∑ j ∈ J.filter (fun j => d j ≤ δ), d j ≤ D / 2 := by
      rw [hδdef]; exact sum_light_le_half J d hq hJ hD0
    have hsplit : (∑ j ∈ J.filter (fun j => d j ≤ δ), d j) + (∑ j ∈ H, d j)
        = ∑ j ∈ J, d j := by
      rw [hH]
      exact Finset.sum_filter_add_sum_filter_not _ _ _
    linarith [hlight, hDsum, hsplit]
  -- every surviving donor has class index below `L_q`
  have hclslt : ∀ j ∈ H, classIndex (d j) < Lq q := by
    intro j hj
    have hmem := Finset.mem_filter.mp (by rw [← hH]; exact hj)
    have hlt : δ < d j := lt_of_not_ge hmem.2
    have hd1' : d j ≤ 1 := hd1 j hmem.1
    have hLq : 1 / δ ≤ (2 : ℝ) ^ Lq q := by
      have hinv : 1 / δ ≤ 2 * (q : ℝ) := by
        rw [div_le_iff₀ hδ0]
        have hone : (1:ℝ) ≤ δ * (2 * q) := by
          rw [hδdef]; field_simp; linarith
        linarith
      have hpow : (2 : ℝ) * (q : ℝ) ≤ (2 : ℝ) ^ Lq q := by
        have hnat : 2 * q ≤ 2 ^ Lq q := two_mul_le_two_pow_Lq q
        have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
        push_cast at hcast
        linarith
      linarith
    exact classIndex_lt hδ0 hlt hd1' hLq
  -- pigeonhole over the at most `L_q` classes
  have hfib : ∑ k ∈ Finset.range (Lq q), ∑ j ∈ H.filter (fun j => classIndex (d j) = k), d j
      = ∑ j ∈ H, d j := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun j => classIndex (d j))]
    intro j hj
    exact Finset.mem_range.mpr (hclslt j hj)
  have hLpos : 0 < Lq q := Lq_pos q
  have hexists : ∃ k ∈ Finset.range (Lq q),
      (∑ j ∈ H, d j) / (Lq q) ≤ ∑ j ∈ H.filter (fun j => classIndex (d j) = k), d j := by
    by_contra hcon
    push Not at hcon
    have hlt : ∑ k ∈ Finset.range (Lq q),
        ∑ j ∈ H.filter (fun j => classIndex (d j) = k), d j
        < ∑ k ∈ Finset.range (Lq q), (∑ j ∈ H, d j) / (Lq q) := by
      refine Finset.sum_lt_sum_of_nonempty ?_ ?_
      · exact ⟨0, Finset.mem_range.mpr hLpos⟩
      · intro k hk; exact hcon k hk
    rw [hfib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
    have hLR : (0:ℝ) < (Lq q : ℝ) := by exact_mod_cast hLpos
    rw [mul_div_cancel₀ _ (ne_of_gt hLR)] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨k, hkmem, hklow⟩ := hexists
  refine ⟨k, H.filter (fun j => classIndex (d j) = k), ?_, ?_, ?_, ?_⟩
  · exact (Finset.filter_subset _ _).trans (by rw [hH]; exact Finset.filter_subset _ _)
  · intro j hj
    have hmem := Finset.mem_filter.mp hj
    have hjH := Finset.mem_filter.mp (by rw [← hH]; exact hmem.1)
    have hlt : δ < d j := lt_of_not_ge hjH.2
    have h0 : 0 < d j := lt_trans hδ0 hlt
    have hspec := classIndex_spec h0 (hd1 j hjH.1)
    rw [hmem.2] at hspec
    exact ⟨hspec.2, hspec.1⟩
  · have hbound : ∑ j ∈ H.filter (fun j => classIndex (d j) = k), d j
        ≤ ((H.filter (fun j => classIndex (d j) = k)).card : ℝ) * classWidth k := by
      calc ∑ j ∈ H.filter (fun j => classIndex (d j) = k), d j
          ≤ ∑ _j ∈ H.filter (fun j => classIndex (d j) = k), classWidth k := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hmem := Finset.mem_filter.mp hj
            have hjH := Finset.mem_filter.mp (by rw [← hH]; exact hmem.1)
            have hlt : δ < d j := lt_of_not_ge hjH.2
            have h0 : 0 < d j := lt_trans hδ0 hlt
            have hspec := classIndex_spec h0 (hd1 j hjH.1)
            rw [hmem.2] at hspec
            exact hspec.1
        _ = ((H.filter (fun j => classIndex (d j) = k)).card : ℝ) * classWidth k := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hLR : (0:ℝ) < (Lq q : ℝ) := by exact_mod_cast hLpos
    have hhalf : D / (2 * (Lq q : ℝ)) ≤ (∑ j ∈ H, d j) / (Lq q) := by
      rw [div_le_div_iff₀ (by positivity) hLR]
      nlinarith [hheavy, hLR]
    calc D / (2 * (Lq q : ℝ)) ≤ (∑ j ∈ H, d j) / (Lq q) := hhalf
      _ ≤ ∑ j ∈ H.filter (fun j => classIndex (d j) = k), d j := hklow
      _ ≤ ((H.filter (fun j => classIndex (d j) = k)).card : ℝ) * classWidth k := hbound
  · -- `eq:protected-delta-min` in its raw form: `d_cls >= D/(2q)`
    by_cases hne : (H.filter (fun j => classIndex (d j) = k)).Nonempty
    · obtain ⟨j, hj⟩ := hne
      have hmem := Finset.mem_filter.mp hj
      have hjH := Finset.mem_filter.mp (by rw [← hH]; exact hmem.1)
      have hlt : δ < d j := lt_of_not_ge hjH.2
      have h0 : 0 < d j := lt_trans hδ0 hlt
      have hspec := classIndex_spec h0 (hd1 j hjH.1)
      rw [hmem.2] at hspec
      rw [hδdef] at hlt
      linarith [hspec.1]
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hLR : (0:ℝ) < (Lq q : ℝ) := by exact_mod_cast hLpos
      have := hklow
      rw [hne, Finset.sum_empty] at this
      have hhalf : (0:ℝ) < (∑ j ∈ H, d j) / (Lq q) := by
        have : (0:ℝ) < ∑ j ∈ H, d j := by linarith [hheavy]
        positivity
      linarith

/-! ## Section 4  The width `u` (`09:1449--1456`) -/

/-- **`09:1449--1450`.**  "Let `u` be the least power of two at least
`8 s kappa/d_cls`", as the exponent of that least power. -/
noncomputable def dyadicCeilExp (x : ℝ) : ℕ := sInf {k : ℕ | x ≤ (2 : ℝ) ^ k}

theorem dyadicCeilExp_setNonempty (x : ℝ) : {k : ℕ | x ≤ (2 : ℝ) ^ k}.Nonempty := by
  obtain ⟨n, hn⟩ := exists_nat_gt x
  refine ⟨n, ?_⟩
  simp only [Set.mem_setOf_eq]
  have hnat : n < 2 ^ n := Nat.lt_two_pow_self
  have hcast := (Nat.cast_le (α := ℝ)).mpr (le_of_lt hnat)
  push_cast at hcast
  linarith

/-- **Aux 4.1.**  `x <= 2^{dyadicCeilExp x}`: the chosen power really is at least
`x`.  General. -/
theorem le_two_pow_dyadicCeilExp (x : ℝ) : x ≤ (2 : ℝ) ^ dyadicCeilExp x :=
  Nat.sInf_mem (dyadicCeilExp_setNonempty x)

/-- **Aux 4.2 (minimality).**  For `1/2 < x`, `2^{dyadicCeilExp x} < 2x` -- the
frozen strict upper half of `8 s kappa <= u d_cls < 16 s kappa`.  The guard
`1/2 < x` is genuine: at `x <= 1/2` the least power of two at least `x` is `1`
and `1 < 2x` fails.  General. -/
theorem two_pow_dyadicCeilExp_lt (x : ℝ) (hx : 1 / 2 < x) :
    (2 : ℝ) ^ dyadicCeilExp x < 2 * x := by
  rcases Nat.eq_zero_or_pos (dyadicCeilExp x) with h0 | hpos
  · rw [h0]; norm_num; linarith
  · obtain ⟨k, hk⟩ : ∃ k, dyadicCeilExp x = k + 1 := ⟨dyadicCeilExp x - 1, by omega⟩
    have hnot : k ∉ {k : ℕ | x ≤ (2 : ℝ) ^ k} := by
      intro hmem
      have := Nat.sInf_le hmem
      rw [← dyadicCeilExp] at this
      omega
    have hlt : (2 : ℝ) ^ k < x := lt_of_not_ge hnot
    rw [hk, pow_succ]
    linarith

/-! ## Section 5  The donor cover (`09:1458--1464`) -/

section Cover

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {q : ℕ}

/-- **`09:1458--1463`, proved over the banked cover lemma.**

"Call a `u`-set of donors poor if its projection of the retained outer column set
has density below `rho_0`.  By `lem:product-projection-cover`, the union of a
maximal disjoint family of poor `u`-sets has size at most `u(B_theta - 1)`.
Hence `eq:protected-dyadic-class` leaves a `u`-set of donors outside that cover.
Its projection has density at least `rho_0`."

`lem:product-projection-cover` is consumed by pin as
`WrapperProjectionCovers.productProjectionCover`, and poorness is the banked
`WrapperProjectionCovers.PoorProjection`; the only new content is the counting
step `|V| >= u B_theta` and `|E| <= u(B_theta - 1)` leaving `u` donors. -/
theorem exists_dense_uset_in_class (S : Finset (Fin q → Y)) {u : ℕ} {θ : ℝ}
    (V : Finset (Fin q)) (hY : 0 < Fintype.card Y) (hu : 1 ≤ u) (hθ : 0 < θ)
    (hV : u * Btheta θ ≤ V.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ)) :
    ∃ J : Finset (Fin q), J ⊆ V ∧ J.card = u ∧ ¬ PoorProjection rhoZero J S := by
  classical
  obtain ⟨hB1, hBρ⟩ := Btheta_spec hθ
  obtain ⟨E, hEcard, hEmeet⟩ :=
    productProjectionCover (q := q) (Y := Y) S hY hu hB1 rhoZero_pos rhoZero_lt_one hBρ hS
  have hbig : u ≤ (V \ E).card := by
    have h1 : V.card ≤ (V \ E).card + E.card := by
      have := Finset.card_le_card_sdiff_add_card (s := V) (t := E)
      omega
    have h2 : E.card ≤ u * (Btheta θ - 1) := hEcard
    have h3 : u * (Btheta θ - 1) + u = u * Btheta θ := by
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hB1
      rw [hc]
      have : 1 + c - 1 = c := by omega
      rw [this, Nat.mul_add, Nat.mul_one]
      omega
    omega
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hbig
  refine ⟨J, ?_, hJcard, ?_⟩
  · exact hJsub.trans (Finset.sdiff_subset)
  · intro hpoor
    obtain ⟨x, hx⟩ := hEmeet J hJcard hpoor
    have hxE : x ∈ E := (Finset.mem_inter.mp hx).1
    have hxJ : x ∈ J := (Finset.mem_inter.mp hx).2
    have : x ∈ V \ E := hJsub hxJ
    exact (Finset.mem_sdiff.mp this).2 hxE

end Cover

/-- **`09:1463--1464`, by pin.**  "after Bob's query, one child has density at
least `rho_1`."  The two Bob children partition the parent's columns, so their
densities sum to at least the parent's; the banked
`DenseWrapperFrontier.denserChild_density` at `y = sqrt(rho_1)` then gives the
denser child `rho_1 = rho_0/2`.  General in the two child densities. -/
theorem denserChild_rhoOne {d₀ d₁ : ℝ} (h : rhoZero ≤ d₀ + d₁) :
    rhoOne ≤ max d₀ d₁ := by
  have hy : Real.sqrt rhoOne ^ 2 = rhoOne := Real.sq_sqrt (le_of_lt rhoOne_pos)
  have hsum : 2 * Real.sqrt rhoOne ^ 2 ≤ d₀ + d₁ := by
    rw [hy, rhoOne]
    linarith [h]
  have := DenseWrapperFrontier.denserChild_density (y := Real.sqrt rhoOne) hsum
  rwa [hy] at this

/-! ### Section 5b  The frozen relabelling and Bob's query (`09:1463--1464`)

`09:1463--1464` reads "Its projection has density at least `rho_0`; after Bob's
query, one child has density at least `rho_1`."  Two distinct things happen in
that sentence, and the round-`r1` shape of this module collapsed both into a
content-free binder:

1. the selected `u`-set of donors is **relabelled** as the coordinates of the
   ambient `Y^u`, so that `lem:template-coordinate-extraction` -- which is stated
   on `Y^u` -- can be applied to the parent's projection.  That relabelling is a
   bijection `[u] -> J`, and it is `ambientRelabel` below;
2. Bob's query **splits** the relabelled parent into its two children.  A query
   partitions the columns it acts on; it does not merely produce two arbitrary
   sets whose counts happen to dominate the parent's.  The partition is what
   makes the passage from `rho_0` to `rho_1` a halving of *the parent's own*
   density rather than a statement about unrelated data, and it is what forces
   the produced child to be a subset of the relabelled parent.

Neither the protocol nor the query is modelled; both remain GAP-EXPOSED.  What is
modelled is exactly the two clauses above, and
`bobQuery_partition_is_satisfiable` shows they are satisfiable without any
protocol, so nothing is smuggled in. -/

section BobQuery

variable {Y : Type*} [DecidableEq Y] {q u : ℕ}

/-- **`09:1463`, the frozen relabelling, named.**  The projection of the retained
outer column set to the selected `u`-set of donors, transported along a
relabelling `eJ : [u] -> J` of those donors as the coordinates of `Y^u`.  The
deliverable is the banked `WrapperProjectionCovers.projSet`; only the transport
is new. -/
def ambientRelabel (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J) (S : Finset (Fin q → Y)) :
    Finset (Fin u → Y) :=
  (projSet J S).image (fun g i => g (eJ i))

omit [DecidableEq Y] in
/-- **Aux 5b.1.**  Relabelling along a bijection of coordinate sets is injective.
General in the alphabet, in `q`, in `u`, in `J` and in `eJ`. -/
theorem relabel_injective (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J) :
    Function.Injective (fun (g : ↥J → Y) (i : Fin u) => g (eJ i)) := by
  intro g₁ g₂ h
  funext j
  have hj := congrFun h (eJ.symm j)
  simpa using hj

/-- **Aux 5b.2 (identity).**  The relabelling changes no count: it is the frozen
`Y^u` presentation of the *same* projection, which is why the `rho_0` density of
`09:1463` transports unchanged.  General. -/
theorem card_ambientRelabel (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J)
    (S : Finset (Fin q → Y)) :
    (ambientRelabel J eJ S).card = (projSet J S).card :=
  Finset.card_image_of_injective _ (relabel_injective J eJ)

/-- **Aux 5b.3 (monotonicity).**  A larger retained column set relabels to a
larger ambient family.  General. -/
theorem ambientRelabel_mono (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J)
    {S S' : Finset (Fin q → Y)} (h : S ⊆ S') :
    ambientRelabel J eJ S ⊆ ambientRelabel J eJ S' :=
  Finset.image_subset_image (projSet_mono h)

/-- **Aux 5b.4 (degeneracy).**  Nothing is created by the transport: the empty
retained set relabels to the empty ambient family.  General. -/
theorem ambientRelabel_empty (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J) :
    ambientRelabel J eJ (∅ : Finset (Fin q → Y)) = ∅ := by
  simp [ambientRelabel, projSet]

/-- **Aux 5b.5 (inhabitation with the hardest field: the repaired query binder is
satisfiable without the protocol).**

The repaired `hQuery` demands a genuine **partition** of the relabelled parent
`ambientRelabel J eJ S`, not two arbitrary families dominating its count.  It is
nonetheless satisfiable at every `S`, `J` and `u` with `|J| = u`, by the
degenerate query that sends every column to one child: `P_0` the whole relabelled
parent and `P_1` empty.  So the strengthened binder adds no existence burden and
in particular does **not** assert that Bob's query exists -- the protocol stays
GAP-EXPOSED.  The relabelling itself is produced from `|J| = u` alone, through
`Finset.equivFin`.  General. -/
theorem bobQuery_partition_is_satisfiable (S : Finset (Fin q → Y))
    (J : Finset (Fin q)) (hJ : J.card = u) :
    ∃ (eJ : Fin u ≃ ↥J) (P₀ P₁ : Finset (Fin u → Y)),
      Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ S := by
  classical
  obtain ⟨eJ⟩ : Nonempty (Fin u ≃ ↥J) := ⟨(J.equivFin.trans (finCongr hJ)).symm⟩
  exact ⟨eJ, ambientRelabel J eJ S, ∅, Finset.disjoint_empty_right _, Finset.union_empty _⟩

end BobQuery

/-- **`09:1458--1471`, the entering column density of call (iii), proved.**

The frozen chain from the dyadic class to the `h` of row (iii), in the order the
proof prints it:

* `09:1458--1462`, the poor-`u`-set cover: "Call a `u`-set of donors poor if its
  projection of the retained outer column set has density below `rho_0`.  By
  `lem:product-projection-cover`, the union of a maximal disjoint family of poor
  `u`-sets has size at most `u(B_theta - 1)`.  Hence
  `eq:protected-dyadic-class` leaves a `u`-set of donors outside that cover" --
  `exists_dense_uset_in_class`;
* `09:1463--1464`, "Its projection has density at least `rho_0`; after Bob's
  query, one child has density at least `rho_1`" -- `denserChild_rhoOne`;
* `09:1466--1469`, "The schedule gives `1 - lambda_T <= 1/100 <= rho_1/8`, so
  `lem:template-coordinate-extraction` applies.  It leaves `u/2` donors whose
  projected all-template set has density at least `rho_1 2^{-u-1}` in
  `Y_T^{u/2}`" -- `templateCoordinateExtraction` at `rho = rho_1`.

`rho_1 2^{-u-1}` at the frozen width `u = 2^e` is exactly `callThreeH e`, the
entering density `h` of row (iii) at `06:1150`.  So this theorem is what
*produces* the `A:141` column density the inherited endpoint consumes; it is the
step whose absence let an earlier shape of this block bypass the whole chain.

**Round `r2` repair (REVISE-A).**  The round-`r1` shape of this statement was
*provable with none of its hypotheses*: its deliverable existentially quantified
a bare `P` with no tie to `S`, so `P := Finset.univ` made the right-hand side
`|Y_T|^{u/2}` and `callThreeH_le_one` closed it; and its `hQuery` binder asked
only that two counts dominate the parent's, which `P_0 := univ`, `P_1 := empty`
discharges for every `S` and every `J`.  The whole chain -- poor cover,
`rho_0 -> rho_1`, template extraction -- was therefore inert.  Two clauses repair
it, and both are frozen content rather than Lean convenience:

* `hQuery` now asks for a genuine **partition** of the relabelled parent
  `ambientRelabel J eJ S`, which is what "Bob's query" means: a query splits the
  columns it acts on.  `P_0 := univ`, `P_1 := empty` no longer satisfies it as
  soon as the parent projection is proper
  (`bobQuery_trivial_split_fails`), while
  `bobQuery_partition_is_satisfiable` shows the binder stays satisfiable without
  any protocol;
* the deliverable now carries the produced child's **provenance**: `P` is a
  subset of the relabelled parent and carries the frozen `rho_1` density.  So
  `P := Finset.univ` no longer discharges the conclusion whenever the projection
  is proper (`selectedColumnDensity_univ_child_pole`), and the `rho_0`-density
  of the selected `u`-set, the halving to `rho_1`, and the extraction are all
  load-bearing.

**GAP-EXPOSED, as explicit binders rather than assertions.**  The protocol object
is still not modelled: there is no Bob, no node, no child.  What `hQuery`
supplies is the relabelling of the selected donors as the coordinates of `Y^u`
together with a two-part split of the relabelled parent; that both exist is
*assumed*, never derived, and the assumption is a genuine one only about the
geometry of a query, not about its conclusion.

General in the alphabet, in `q`, in `e`, and in the two densities. -/
theorem selectedColumnDensity {Y : Type*} [Fintype Y] [DecidableEq Y] {q e : ℕ}
    (S : Finset (Fin q → Y)) (YT : Finset Y) (V : Finset (Fin q))
    {θ lamT : ℝ}
    (hY : 0 < Fintype.card Y) (hθ : 0 < θ) (he : 2 ≤ e)
    (hV : 2 ^ e * Btheta θ ≤ V.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ J : Finset (Fin q), J ⊆ V → J.card = 2 ^ e →
        ∃ (eJ : Fin (2 ^ e) ≃ ↥J) (P₀ P₁ : Finset (Fin (2 ^ e) → Y)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ S) :
    ∃ (J : Finset (Fin q)) (eJ : Fin (2 ^ e) ≃ ↥J)
      (P : Finset (Fin (2 ^ e) → Y)) (J' : Finset (Fin (2 ^ e))),
      J ⊆ V ∧ J.card = 2 ^ e ∧ ¬ PoorProjection rhoZero J S ∧
      P ⊆ ambientRelabel J eJ S ∧
      rhoOne * (Fintype.card Y : ℝ) ^ (2 ^ e) ≤ (P.card : ℝ) ∧
      J'.card = 2 ^ e / 2 ∧
      callThreeH e * (YT.card : ℝ) ^ (2 ^ e / 2)
        ≤ ((projSet J' (P.filter (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) := by
  classical
  have hYR : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  obtain ⟨J, hJV, hJcard, hJpoor⟩ :=
    exists_dense_uset_in_class (u := 2 ^ e) (θ := θ) S V hY Nat.one_le_two_pow hθ hV hS
  -- `09:1463`: the selected `u`-set is not poor, i.e. its projection is
  -- `rho_0`-dense.
  have hdense : rhoZero * (Fintype.card Y : ℝ) ^ (2 ^ e) ≤ ((projSet J S).card : ℝ) := by
    have h := hJpoor
    simp only [PoorProjection, hJcard, not_lt] at h
    exact h
  obtain ⟨eJ, P₀, P₁, hdisj, hunion⟩ := hQuery J hJV hJcard
  -- the split is a partition, so the two children's counts sum to the parent's
  -- exactly -- and the relabelling changes no count.
  have hsplit : ((projSet J S).card : ℝ) = (P₀.card : ℝ) + (P₁.card : ℝ) := by
    have hnat : (projSet J S).card = P₀.card + P₁.card := by
      rw [← card_ambientRelabel J eJ S, ← hunion, Finset.card_union_of_disjoint hdisj]
    exact_mod_cast hnat
  set N : ℝ := (Fintype.card Y : ℝ) ^ (2 ^ e) with hN
  have hNpos : 0 < N := by rw [hN]; exact pow_pos hYR _
  -- `09:1463--1464`: the denser Bob child retains `rho_1`.
  have hsum : rhoZero ≤ (P₀.card : ℝ) / N + (P₁.card : ℝ) / N := by
    rw [← add_div, le_div_iff₀ hNpos]
    linarith [hdense, hsplit]
  have hmax := denserChild_rhoOne hsum
  have hchild : ∃ P : Finset (Fin (2 ^ e) → Y),
      P ⊆ ambientRelabel J eJ S ∧ rhoOne * N ≤ (P.card : ℝ) := by
    rcases le_total ((P₀.card : ℝ) / N) ((P₁.card : ℝ) / N) with hcase | hcase
    · refine ⟨P₁, ?_, ?_⟩
      · rw [← hunion]; exact Finset.subset_union_right
      · rw [max_eq_right hcase, le_div_iff₀ hNpos] at hmax
        exact hmax
    · refine ⟨P₀, ?_, ?_⟩
      · rw [← hunion]; exact Finset.subset_union_left
      · rw [max_eq_left hcase, le_div_iff₀ hNpos] at hmax
        exact hmax
  obtain ⟨P, hPsub, hPdense⟩ := hchild
  -- `09:1466--1469`: `lem:template-coordinate-extraction` at `rho = rho_1`.
  have h4 : (4 : ℕ) ∣ 2 ^ e := by
    have h : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h]
    exact pow_dvd_pow 2 he
  obtain ⟨J', hJ'card, hJ'dense⟩ :=
    templateCoordinateExtraction (u := 2 ^ e) P YT h4 (by positivity) hY rhoOne_pos
      hPdense hYT hgap
  refine ⟨J, eJ, P, J', hJV, hJcard, hJpoor, hPsub, hPdense, hJ'card, ?_⟩
  -- `06:1150`: dividing the frozen `rho_1 2^{-u-1}` by its denominator.
  have hpow : (0 : ℝ) < 2 ^ (2 ^ e + 1) := by positivity
  have hcomm :
      ((projSet J' (P.filter (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) * 2 ^ (2 ^ e + 1)
        = 2 ^ (2 ^ e + 1)
            * ((projSet J' (P.filter (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) := by ring
  rw [callThreeH, div_mul_eq_mul_div, div_le_iff₀ hpow, hcomm]
  exact hJ'dense

/-! ### The extraction's output, as the input of the `09:1499` selection -/

/-- **`09:1466--1471` read as what `09:1499` consumes.**

The frozen proof reaches the selection only after the extraction has run:
`09:1458--1464` produces a `u`-set outside the poor cover whose projection is
`rho_0`-dense and a Bob child at `rho_1`, and `09:1466--1471` then applies
`lem:template-coordinate-extraction`, leaving `u/2` donors "whose projected
all-template set has density at least `rho_1 2^{-u-1}` in `Y_T^{u/2}`".  Only
then does `09:1499` say "Select exactly `9K_int/16` of these represented Stage-2
blocks", and `09:1501--1502` records "the entering column density" of that call.

This predicate names exactly that output at the frozen width `u = 2^e`: a child
`P` of the relabelled parent (`ambientRelabel`, `09:1463`), a coordinate set `J'`
of the frozen half width `u/2`, and the **entering column density** attained on
`J'` in `Y_T^{u/2}` -- the `A:141` slot `h 2^{-a^sharp}` at `a^sharp = 0`, with
`h = rho_1 2^{-u-1} = callThreeH e` (`06:1150`), written as a density, i.e. with
the frozen denominator `|Y_T|^{u/2}` divided out.

*Why the density form rather than the cleared product.*  `09:1501` names a
**density**, and `A:141` reads its slot as a lower bound on a density; the
cleared product `h |Y_T|^{u/2} <= |proj|` is equivalent to it exactly when
`|Y_T| > 0`, and that non-degeneracy is itself frozen content
(`eq:wrapper-template-gates`, `09:389`, forces `lambda_T >= 99/100`, so the
template alphabet is never empty).  Keeping the division makes the dependence
visible in the kernel: `extractionOutput_needs_a_template` below proves the
predicate is **unsatisfiable** at `Y_T = empty`.

It is scaffolding for no one: this is the antecedent the `09:1499` selection
binder of both closure theorems takes, and `extractionOutput_of_selected-`
`ColumnDensity` is the paper's own instance of it.  General in the alphabet, in
`q`, in the parent, in the template set and in `e`. -/
def ExtractionOutput {Y : Type*} [DecidableEq Y] {q : ℕ}
    (S : Finset (Fin q → Y)) (YT : Finset Y) (e : ℕ) : Prop :=
  ∃ (J : Finset (Fin q)) (eJ : Fin (2 ^ e) ≃ ↥J) (P : Finset (Fin (2 ^ e) → Y))
    (J' : Finset (Fin (2 ^ e))),
    P ⊆ ambientRelabel J eJ S ∧ J'.card = 2 ^ e / 2 ∧
    callThreeH e / 2 ^ (0 : ℕ)
      ≤ ((projSet J' (P.filter (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ)
          / (YT.card : ℝ) ^ (2 ^ e / 2)

/-- **CANONICAL INHABITATION (`09:1458--1471`): the paper's own instance.**

The extraction output is not postulated anywhere: at the frozen hypotheses of
`09:1458--1471` -- a dyadic class `V` of size at least `u B_theta`
(`eq:protected-dyadic-class`), the retained column set at density `theta`, the
template gate `1 - lambda_T <= rho_1/8` (`09:1466`) and Bob's query as a
partition -- `selectedColumnDensity` produces it, and `hYT0` turns its cleared
product into the entering **density**.  So the antecedent that gates the
`09:1499` selection is exactly the deliverable of the block that precedes it in
the frozen proof, and this lemma is the canonical-inhabitation discharge for
`ExtractionOutput`: no synthetic probe stands in for it.  General. -/
theorem extractionOutput_of_selectedColumnDensity {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q e : ℕ} (S : Finset (Fin q → Y)) (YT : Finset Y) (V : Finset (Fin q))
    {θ lamT : ℝ}
    (hY : 0 < Fintype.card Y) (hθ : 0 < θ) (he : 2 ≤ e) (hYT0 : 0 < YT.card)
    (hV : 2 ^ e * Btheta θ ≤ V.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ J : Finset (Fin q), J ⊆ V → J.card = 2 ^ e →
        ∃ (eJ : Fin (2 ^ e) ≃ ↥J) (P₀ P₁ : Finset (Fin (2 ^ e) → Y)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ S) :
    ExtractionOutput S YT e := by
  obtain ⟨J, eJ, P, J', -, -, -, hPsub, -, hJ'card, hJ'dense⟩ :=
    selectedColumnDensity S YT V hY hθ he hV hS hYT hgap hQuery
  have hYTR : (0 : ℝ) < (YT.card : ℝ) := by exact_mod_cast hYT0
  refine ⟨J, eJ, P, J', hPsub, hJ'card, ?_⟩
  rw [pow_zero, div_one, le_div_iff₀ (by positivity)]
  exact hJ'dense

/-- **Aux 5c.1 (monotonicity in the retained parent).**  A larger retained outer
column set can only make the extraction easier: the produced child stays a subset
of the larger relabelled parent, and no density changes.  This is the transport
that `ambientRelabel_mono` supplies, lifted to the gate.  General. -/
theorem extractionOutput_mono {Y : Type*} [DecidableEq Y] {q e : ℕ}
    {S S' : Finset (Fin q → Y)} (YT : Finset Y) (h : S ⊆ S') :
    ExtractionOutput S YT e → ExtractionOutput S' YT e := by
  rintro ⟨J, eJ, P, J', hPsub, hJ'card, hdens⟩
  exact ⟨J, eJ, P, J', hPsub.trans (ambientRelabel_mono J eJ h), hJ'card, hdens⟩

/-- **Aux 5c.2 (the gate has content): it forces a nonempty retained parent.**

`h = rho_1 2^{-u-1}` is strictly positive (`callThreeH_pos`), so a witness must
carry a nonempty projection, hence a nonempty child, hence a nonempty relabelled
parent -- and `ambientRelabel` is an image of `projSet J S`, so `S` itself is
nonempty.  A binder that could be met with no columns at all would be exactly the
inert gate this round removes.  General. -/
theorem extractionOutput_forces_nonempty_parent {Y : Type*} [DecidableEq Y] {q e : ℕ}
    {S : Finset (Fin q → Y)} {YT : Finset Y} (hYT0 : 0 < YT.card)
    (h : ExtractionOutput S YT e) : S.Nonempty := by
  obtain ⟨J, eJ, P, J', hPsub, -, hdens⟩ := h
  have hYTR : (0 : ℝ) < (YT.card : ℝ) := by exact_mod_cast hYT0
  have hden : (0 : ℝ) < (YT.card : ℝ) ^ (2 ^ e / 2) := by positivity
  rw [pow_zero, div_one, le_div_iff₀ hden] at hdens
  have hpos : (0 : ℝ) < ((projSet J' (P.filter (fun f => ∀ i ∈ J', f i ∈ YT))).card : ℝ) :=
    lt_of_lt_of_le (mul_pos (callThreeH_pos e) hden) hdens
  have hne : (projSet J' (P.filter (fun f => ∀ i ∈ J', f i ∈ YT))).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hpos
  have hPne : P.Nonempty := by
    obtain ⟨g, hg⟩ := (Finset.image_nonempty).1 hne
    exact ⟨g, (Finset.mem_filter.1 hg).1⟩
  obtain ⟨f, hf⟩ := hPne
  have hfmem : f ∈ ambientRelabel J eJ S := hPsub hf
  obtain ⟨g, hg, -⟩ := Finset.mem_image.1 hfmem
  obtain ⟨s, hs, -⟩ := Finset.mem_image.1 hg
  exact ⟨s, hs⟩

/-- **POLE 5c.3 (the trivial parent fails).**  The empty retained outer column set
does not satisfy the gate.  So `hSelect`'s new antecedent is not a formality that
any bundle discharges: it demands columns that survive the cover step.  General. -/
theorem extractionOutput_at_the_empty_parent_fails {Y : Type*} [DecidableEq Y] {q e : ℕ}
    {YT : Finset Y} (hYT0 : 0 < YT.card) :
    ¬ ExtractionOutput (∅ : Finset (Fin q → Y)) YT e := by
  intro h
  exact absurd (extractionOutput_forces_nonempty_parent hYT0 h) (by simp)

/-- **POLE 5c.4 (`hYT0` is load-bearing, in the kernel).**

At an empty template alphabet the frozen denominator `|Y_T|^{u/2}` vanishes
(`u/2 >= 1` at `e >= 1`), the density slot collapses to `0`, and the frozen
entering density `h = rho_1 2^{-u-1} > 0` cannot be attained.  So the gate is
**unsatisfiable** there, which is why the closure theorems keep `hYT0` as a
hypothesis rather than deriving the cleared product form and dropping it: the
division is frozen content (`09:1501` names a density), not presentation.
General. -/
theorem extractionOutput_needs_a_template {Y : Type*} [DecidableEq Y] {q e : ℕ}
    (he : 1 ≤ e) (S : Finset (Fin q → Y)) :
    ¬ ExtractionOutput S (∅ : Finset Y) e := by
  rintro ⟨J, eJ, P, J', -, -, hdens⟩
  have hhalf : (2 : ℕ) ^ e / 2 ≠ 0 := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have hzero : (((∅ : Finset Y).card : ℝ)) ^ (2 ^ e / 2) = 0 := by
    rw [Finset.card_empty, Nat.cast_zero, zero_pow hhalf]
  rw [hzero, div_zero, pow_zero, div_one] at hdens
  exact absurd hdens (not_le.2 (callThreeH_pos e))

/-! ## Section 6  The represented Stage-2 blocks (`09:1473--1495`) -/

/-- **`09:1476--1479`, the reverse-Markov fibre count.**  "Averaging these `q_2`
coordinate fibres therefore supplies more than `d_cls q_2/4` Stage-2 coordinates
whose surviving `C_1`-density is at least `d_cls/4`."

The general fact: if `n` bounded-by-one fibres carry total mass at least `a n`,
then more than `(a - b) n` of them individually carry at least `b`.  This is the
*counting* content of the frozen sentence; the reservoir geometry of
`09:1474--1476` that makes the fibres equal is Section-8 structure and is not
modelled here.  General. -/
theorem card_ge_of_sum_ge {ι : Type*} (T : Finset ι) (f : ι → ℝ)
    {a b : ℝ} (hb : 0 ≤ b) (hf1 : ∀ i ∈ T, f i ≤ 1)
    (hsum : a * T.card ≤ ∑ i ∈ T, f i) :
    (a - b) * T.card ≤ ((T.filter (fun i => b ≤ f i)).card : ℝ) := by
  classical
  set G : Finset ι := T.filter (fun i => b ≤ f i) with hG
  set B : Finset ι := T.filter (fun i => ¬ (b ≤ f i)) with hB
  have hsplit : G.card + B.card = T.card := by
    rw [hG, hB]; exact Finset.card_filter_add_card_filter_not _
  have hGB : ∑ i ∈ T, f i ≤ (G.card : ℝ) + b * (B.card : ℝ) := by
    have hdec : (∑ i ∈ G, f i) + (∑ i ∈ B, f i) = ∑ i ∈ T, f i := by
      rw [hG, hB]; exact Finset.sum_filter_add_sum_filter_not _ _ _
    have hG1 : ∑ i ∈ G, f i ≤ (G.card : ℝ) := by
      calc ∑ i ∈ G, f i ≤ ∑ _i ∈ G, (1:ℝ) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hmemi : i ∈ T := by
              rw [hG, Finset.mem_filter] at hi
              exact hi.1
            exact hf1 i hmemi
        _ = (G.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hB1 : ∑ i ∈ B, f i ≤ b * (B.card : ℝ) := by
      calc ∑ i ∈ B, f i ≤ ∑ _i ∈ B, b := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hnot : ¬ (b ≤ f i) := by
              rw [hB, Finset.mem_filter] at hi
              exact hi.2
            exact le_of_lt (lt_of_not_ge hnot)
        _ = b * (B.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    linarith
  have hcards : (G.card : ℝ) + (B.card : ℝ) = (T.card : ℝ) := by exact_mod_cast hsplit
  have hBle : (B.card : ℝ) ≤ (T.card : ℝ) := by
    have hle : B.card ≤ T.card := by omega
    exact_mod_cast hle
  nlinarith [hsum, hGB, hcards, hBle, hb]

/-- **`09:1481--1483`.**  The frozen represented-block count
`K_int = s kappa q_2`. -/
def Kint (s κ q₂ : ℕ) : ℕ := s * κ * q₂

/-- **Aux 6.1 (`09:1479--1483`, the block total).**  Each of the `u/2` selected
donors contributes more than `d_cls q_2/4` blocks, and `8 s kappa <= u d_cls`
turns that into `K_int = s kappa q_2` blocks in total:
`(u/2)(d_cls q_2/4) = (u d_cls) q_2/8 >= s kappa q_2`.  General in all five
quantities. -/
theorem representedBlocks_ge {s κ q₂ u : ℕ} {dcls perDonor : ℝ}
    (hu : (2 : ℕ) ∣ u)
    (hud : 8 * ((s : ℝ) * κ) ≤ (u : ℝ) * dcls)
    (hper : dcls * q₂ / 4 ≤ perDonor) :
    (Kint s κ q₂ : ℝ) ≤ ((u / 2 : ℕ) : ℝ) * perDonor := by
  have hq₂ : (0:ℝ) ≤ (q₂ : ℝ) := by positivity
  have hhalf : ((u / 2 : ℕ) : ℝ) * 2 = (u : ℝ) := by
    obtain ⟨c, hc⟩ := hu
    subst hc
    have hc2 : 2 * c / 2 = c := by omega
    rw [hc2]
    push_cast
    ring
  have hstep : ((u / 2 : ℕ) : ℝ) * (dcls * q₂ / 4) = ((u : ℝ) * dcls) * (q₂ : ℝ) / 8 := by
    rw [← hhalf]; ring
  have hmul : ((u / 2 : ℕ) : ℝ) * (dcls * q₂ / 4) ≤ ((u / 2 : ℕ) : ℝ) * perDonor := by
    have hnn : (0:ℝ) ≤ ((u / 2 : ℕ) : ℝ) := by positivity
    nlinarith [hper]
  have hlow : (Kint s κ q₂ : ℝ) ≤ ((u : ℝ) * dcls) * (q₂ : ℝ) / 8 := by
    rw [Kint]
    push_cast
    nlinarith [hud, hq₂]
  linarith [hstep, hmul, hlow]

/-! ## Section 7  Localized Extension call (iii) and the block endpoint -/

/-- **`06:1147--1153` with `06:1107--1130`, `06:1161--1162` and
`eq:contract-extension-exponents` (`D:746--764`), transcribed in full.**

Row (iii) of `sec:extension-call-ledger`, "Early protected-mass stop
(`lem:early-protected-closure`)": `v = u/2`, `K = K_int = s kappa q_2`,
`h = rho_1 2^{-u-1}`, `a^sharp = 0`, and "The dyadic-class estimate supplies
per-block row density at least `d_cls/4`, which the structural gates make at
least `K 2^{-b_1}`."  The common binders are `06:1107--1113`
(`M = M_1^T`, `H = B_cap`, `x = 2^{-b_1}`, `y = 3/5`, `t = t_2`,
`p_seed = 9t_2/16`) and the remaining integer binders `r = q_amb/t_2`,
`r' = K/t_2` are `06:1122--1125`.

`D:746--764` additionally demands that the call record **exhibit** natural
numbers `T, R, R_loc` with
`t_2 = 2^T`, `q_amb = 2^{R+T}`, `K = 2^{R_loc+T}`, `R_loc <= R`, and closes with
the explicit warning that "Recording only `t_2 | q_amb` and `t_2 | K` does not
discharge `eq:contract-extension-exponents`".  The three exponents are therefore
index parameters of this record and the three equalities are fields.  The frozen
`u` is carried as `2^e` (`09:1449--1450`: `u` is the least **power of two** at
least `8 s kappa/d_cls`), so `D:761--762`'s "the product counts `1,2,u/2,
u_don/2` are likewise powers of two at their call sites" holds here with
`u/2 = 2^{e-1}` and `q_amb = 2^{e-1} q_2`.

The frozen dyadic facts of `eq:protected-dyadic-class` (`09:1451--1454`) are the
first two clauses, so the row's `u` is the frozen one.  `h in (0,1]` is **not** a
field: `callThreeH_pos` and `callThreeH_le_one` prove it outright, and a field
restating a derived fact would be dead weight.

This is a **record of the call's binders**, not a claim that Localized Extension
holds: the corollary itself enters `earlyProtectedClosure` as the separate named
hypothesis `hLocEx`, whose antecedent list is the whole of `A:109--146`. -/
structure ExtensionCallThree (T R Rloc b₁ e r₂ r₃ ℓ : ℕ) (dcls colDens : ℝ) : Prop where
  /-- `09:1451--1452`, lower half of `eq:protected-dyadic-class`, at
  `s = 2^{r_3}`, `kappa = 2^{ell}`, `u = 2^e`. -/
  uWidth_lower : 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * dcls
  /-- `09:1451--1452`, upper half; strict, exactly as frozen. -/
  uWidth_upper : (2 : ℝ) ^ e * dcls < 16 * ((2 : ℝ) ^ (r₃ + ℓ))
  /-- `09:1449--1450` and `D:761--762`: `u = 2^e` with `16 | u`, hence `4 | u`
  (which `lem:template-coordinate-extraction` needs) and `u/2 = 2^{e-1}`. -/
  four_le_e : 4 ≤ e
  /-- `A:117`: `t = t_2 = 2^T` is divisible by `16`. -/
  four_le_T : 4 ≤ T
  /-- `D:751`: `q_amb = (u/2) q_2 = 2^{R+T}`, the ambient product width of
  `06:1117--1118` at `v = u/2`. -/
  ambient_exponent : R + T = (e - 1) + r₂
  /-- `D:752`: `K = K_int = s kappa q_2 = 2^{R_loc+T}`. -/
  capacity_exponent : Rloc + T = r₃ + ℓ + r₂
  /-- `D:753`: `R_loc <= R`, i.e. `A:125`'s `r' <= r`. -/
  rloc_le_r : Rloc ≤ R
  /-- `09:1491--1495`: the ambient product width is at least `4 K_int`, so
  "`r' = K_int/t_2` lies in the literal range of Localized Extension". -/
  ambient_width : 4 * Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) ≤ 2 ^ (e - 1) * 2 ^ r₂
  /-- `06:1151--1152`: the structural-gate comparison `d_cls/4 >= K 2^{-b_1}`,
  with `x = 2^{-b_1}` from `eq:extension-common-binders`. -/
  row_density_gate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁ ≤ dcls / 4
  /-- `06:1150` and `A:141` at `a^sharp = 0`: the entering column density is
  `h = rho_1 2^{-u-1}` and the selected child retains at least
  `h 2^{-a^sharp} = h`. -/
  column_density : callThreeH e / 2 ^ (0 : ℕ) ≤ colDens

/-- **Aux 7.1 (`A:125` and `06:1162`).**  `1 <= r' <= r` at `r' = 2^{R_loc}`,
`r = 2^R`: both halves follow from the exponent record, so the ledger's uniform
clause is a consequence of `D:753` and not an extra assumption. -/
theorem ExtensionCallThree.one_le_r' {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (_h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    1 ≤ (2 : ℕ) ^ Rloc := Nat.one_le_two_pow

theorem ExtensionCallThree.r'_le_r {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    (2 : ℕ) ^ Rloc ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) h.rloc_le_r

/-- **Aux 7.2 (`D:756`).**  "both `q_amb/t_2` and `K/t_2` must be powers of two
with named exponents": `q = r t` and `K = r' t` at the recorded exponents. -/
theorem ExtensionCallThree.ambient_eq {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    (2 : ℕ) ^ R * 2 ^ T = 2 ^ (e - 1) * 2 ^ r₂ := by
  rw [← pow_add, h.ambient_exponent, pow_add]

theorem ExtensionCallThree.capacity_eq {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    (2 : ℕ) ^ Rloc * 2 ^ T = Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) := by
  rw [← pow_add, h.capacity_exponent, Kint, ← pow_add, ← pow_add]

theorem ExtensionCallThree.capacity_dvd {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    (2 : ℕ) ^ T ∣ Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) := by
  rw [← h.capacity_eq]
  exact dvd_mul_left _ _

/-- **Aux 7.3 (`06:1128--1130` and `A:138`).**  The exact output-size equation
`|Q_s| = r' p_seed = 9K/16`, at the recorded exponents and without truncation:
`16 | t_2` is what makes both sides integral. -/
theorem ExtensionCallThree.selected_count {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    (2 : ℕ) ^ Rloc * (9 * 2 ^ T / 16) = 9 * 2 ^ (Rloc + T) / 16 := by
  obtain ⟨c, hc⟩ : ∃ c, T = c + 4 := ⟨T - 4, by have := h.four_le_T; omega⟩
  subst hc
  have h1 : (9 : ℕ) * 2 ^ (c + 4) / 16 = 9 * 2 ^ c := by
    have hx : (9 : ℕ) * 2 ^ (c + 4) = (9 * 2 ^ c) * 16 := by rw [pow_add]; ring
    rw [hx, Nat.mul_div_cancel _ (by norm_num)]
  have h2 : (9 : ℕ) * 2 ^ (Rloc + (c + 4)) / 16 = 9 * 2 ^ (Rloc + c) := by
    have hx : (9 : ℕ) * 2 ^ (Rloc + (c + 4)) = (9 * 2 ^ (Rloc + c)) * 16 := by
      rw [show Rloc + (c + 4) = (Rloc + c) + 4 by omega, pow_add]; ring
    rw [hx, Nat.mul_div_cancel _ (by norm_num)]
  rw [h1, h2, pow_add]
  ring

/-- **Aux 7.4 (`lem:template-coordinate-extraction`'s width guard).**  `4 | u` at
`u = 2^e`, which is the divisibility the extraction lemma demands and which the
record supplies through `four_le_e`. -/
theorem ExtensionCallThree.four_dvd_u {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    (4 : ℕ) ∣ 2 ^ e := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact pow_dvd_pow 2 (by have := h.four_le_e; omega)

/-- **`09:1505--1507`, the endpoint identity, proved.**

"`B_cap + log_2 K_int = C + log_2 kappa - 1`", at the frozen dyadic exponents
`s = 2^{r_3}`, `q_2 = 2^{r_2}`, `kappa = 2^{ell}` and the banked
`C = TerminalTwoStream.terminalTarget b_cap r_2 r_3 = D_2 + log_2 s + 1`
(`09:1777--1778`).  Written subtraction-free, so that the frozen `-1` never
becomes a truncated natural subtraction. -/
theorem endpoint_identity (bcap r₂ r₃ ℓ : ℕ) :
    DenseBranchSelection.Dtwo bcap r₂ + (r₃ + ℓ) + 1
      = TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ := by
  simp [TerminalTwoStream.terminalTarget, DenseBranchSelection.Dtwo]
  omega

/-- **`09:1499--1508`, the frozen log-count of `K_int`.**  At the frozen dyadic
widths `s = 2^{r_3}`, `kappa = 2^{ell}`, `q_2 = 2^{r_2}` the represented capacity
is `K_int = 2^{r_3 + ell + r_2}`, which is what makes `log_2 K_int` the frozen
sum of exponents. -/
theorem Kint_dyadic (r₂ r₃ ℓ : ℕ) :
    Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) = 2 ^ (r₃ + ℓ + r₂) := by
  rw [Kint, ← pow_add, ← pow_add]

/-! ## Section 8  The extraction chain and `lem:early-protected-closure` -/

/-- **`09:1441--1497`, the extraction chain, proved.**

From the frozen donor-mass threshold in the form `09:1439` reaches it --
`D_mass >= 64 B_theta L_q s kappa` -- the frozen proof produces the dyadic class
`V`, its representative `d_cls`, and the width `u`, satisfying
`eq:protected-dyadic-class` (`8 s kappa <= u d_cls < 16 s kappa` and
`|V| >= u B_theta`) and `eq:protected-delta-min` (`d_cls >= 64 B_theta L_q s/q`,
using `kappa >= 2`).

The conclusion is exactly the data `lem:product-projection-cover` and Localized
Extension call (iii) consume; nothing about the protocol, the reservoirs, or the
Stage-4 entry maps is asserted. -/
theorem exists_protected_dyadic_class {ι : Type*} (J₀ : Finset ι) (d : ι → ℝ)
    {q s κ : ℕ} {θ : ℝ}
    (hq : 0 < q) (hs : 1 ≤ s) (hκ : 2 ≤ κ) (hθ : 0 < θ)
    (hJ : J₀.card ≤ q)
    (hd0 : ∀ j ∈ J₀, 0 ≤ d j) (hd1 : ∀ j ∈ J₀, d j ≤ 1)
    (hmass : 64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s * κ ≤ ∑ j ∈ J₀, d j) :
    ∃ (k : ℕ) (V : Finset ι),
      V ⊆ J₀ ∧
      (∀ j ∈ V, classWidth k < 2 * d j ∧ d j ≤ classWidth k) ∧
      32 * (Btheta θ : ℝ) * s * κ ≤ (V.card : ℝ) * classWidth k ∧
      64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s / q ≤ classWidth k := by
  classical
  set D : ℝ := 64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s * κ with hDdef
  have hB1 : 1 ≤ Btheta θ := one_le_Btheta hθ
  have hBR : (1:ℝ) ≤ (Btheta θ : ℝ) := by exact_mod_cast hB1
  have hLR : (1:ℝ) ≤ (Lq q : ℝ) := by exact_mod_cast one_le_Lq q
  have hsR : (1:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hκR : (2:ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  have hBL : (1:ℝ) ≤ (Btheta θ : ℝ) * (Lq q : ℝ) := by nlinarith [hBR, hLR]
  have hBLs : (1:ℝ) ≤ (Btheta θ : ℝ) * (Lq q : ℝ) * s := by nlinarith [hBL, hsR]
  have hBLsk : (2:ℝ) ≤ (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * κ := by nlinarith [hBLs, hκR]
  have hD1 : 1 ≤ D := by
    rw [hDdef]; nlinarith [hBLsk]
  obtain ⟨k, V, hVsub, hVspec, hVheavy, hVdelta⟩ :=
    exists_heavy_dyadic_class J₀ d hq hJ hd0 hd1 hD1 (by rw [hDdef]; exact hmass)
  have hLR0 : (0:ℝ) < (Lq q : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  have hqR : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  refine ⟨k, V, hVsub, hVspec, ?_, ?_⟩
  · have heq : D / (2 * (Lq q : ℝ)) = 32 * (Btheta θ : ℝ) * s * κ := by
      rw [hDdef]; field_simp; ring
    rw [heq] at hVheavy
    exact hVheavy
  · have hstep : 64 * (Btheta θ : ℝ) * (Lq q : ℝ) * s / q ≤ D / (2 * q) := by
      rw [hDdef, div_le_div_iff₀ hqR (by positivity)]
      have hpos : (0:ℝ) ≤ (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * (q : ℝ) := by positivity
      nlinarith [hpos, hκR]
    linarith [hVdelta, hstep]

/-- **`09:1449--1456`, the width `u`, proved.**

"Let `u` be the least power of two at least `8 s kappa/d_cls`.  Then
`8 s kappa <= u d_cls < 16 s kappa`, `|V| >= u B_theta`."

Both halves are proved from `dyadicCeilExp`'s two properties; the class-size
bound uses the class-heaviness `|V| d_cls >= 32 B_theta s kappa` produced by
`exists_protected_dyadic_class`, and in fact delivers the stronger
`2 u B_theta <= |V|`.

The width is returned **as its exponent**, `u = 2^e`.  That is not cosmetic:
`D:761--762` requires the product count `u/2` at a call site to be a power of
two with a named exponent, and `eq:contract-extension-exponents` (`D:749--755`)
is not discharged by divisibility alone.  An earlier shape of this lemma returned
only `2 | u` and then had no exponent to record. -/
theorem exists_width_u {B s κ : ℕ} {dcls Vcard : ℝ}
    (hdcls0 : 0 < dcls) (hdcls1 : dcls ≤ 1) (hs : 1 ≤ s) (hκ : 2 ≤ κ) (hB : 1 ≤ B)
    (hheavy : 32 * (B : ℝ) * s * κ ≤ Vcard * dcls) :
    ∃ e : ℕ, 1 ≤ e ∧
      8 * ((s : ℝ) * κ) ≤ (2 : ℝ) ^ e * dcls ∧
      (2 : ℝ) ^ e * dcls < 16 * ((s : ℝ) * κ) ∧
      2 * ((2 : ℝ) ^ e * B) ≤ Vcard := by
  classical
  have hsR : (1:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hκR : (2:ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  have hBR : (1:ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  set x : ℝ := 8 * ((s : ℝ) * κ) / dcls with hxdef
  have hx16 : 16 ≤ x := by
    rw [hxdef, le_div_iff₀ hdcls0]
    nlinarith [hsR, hκR, hdcls1, hdcls0]
  have hxhalf : 1 / 2 < x := by linarith
  set e : ℕ := dyadicCeilExp x with hedef
  have hlow : x ≤ (2 : ℝ) ^ e := le_two_pow_dyadicCeilExp x
  have hhigh : (2 : ℝ) ^ e < 2 * x := two_pow_dyadicCeilExp_lt x hxhalf
  have hepos : 1 ≤ e := by
    by_contra hcon
    push Not at hcon
    interval_cases e
    · simp at hlow; linarith
  have hxd : 2 * x * dcls = 16 * ((s : ℝ) * κ) := by
    rw [hxdef]; field_simp; ring
  have hupper : (2 : ℝ) ^ e * dcls < 16 * ((s : ℝ) * κ) := by
    have hx : (2 : ℝ) ^ e * dcls < 2 * x * dcls := mul_lt_mul_of_pos_right hhigh hdcls0
    linarith
  refine ⟨e, hepos, ?_, hupper, ?_⟩
  · have hxl : x * dcls ≤ (2 : ℝ) ^ e * dcls := mul_le_mul_of_nonneg_right hlow (le_of_lt hdcls0)
    have hxe : x * dcls = 8 * ((s : ℝ) * κ) := by
      rw [hxdef]; field_simp
    linarith
  · nlinarith [hheavy, hupper, hBR, hdcls0]

/-- **`09:1491--1495`, the ambient-width inequality, proved.**

"The ambient product width is `(u/2)q_2`.  Since `d_cls <= 1` and
`eq:protected-dyadic-class` gives `u d_cls >= 8 s kappa`, this width is at least
`4 K_int`."

`d_cls <= 1` is genuinely load-bearing: without it the width `u` may be as small
as `2` at a large `d_cls`, and `4 K_int <= (u/2) q_2` fails.  General. -/
theorem ambient_width_ge {s κ q₂ u : ℕ} {dcls : ℝ}
    (hu : 2 ∣ u) (hdcls1 : dcls ≤ 1)
    (hud : 8 * ((s : ℝ) * κ) ≤ (u : ℝ) * dcls) :
    4 * Kint s κ q₂ ≤ (u / 2) * q₂ := by
  have hunat : 8 * (s * κ) ≤ u := by
    have hstep : 8 * ((s : ℝ) * κ) ≤ (u : ℝ) := by
      have hup : (u : ℝ) * dcls ≤ (u : ℝ) := by
        have : (0:ℝ) ≤ (u : ℝ) := by positivity
        nlinarith [hdcls1]
      linarith
    have hcast : ((8 * (s * κ) : ℕ) : ℝ) ≤ ((u : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  have hhalf : 4 * (s * κ) ≤ u / 2 := by omega
  calc 4 * Kint s κ q₂ = (4 * (s * κ)) * q₂ := by rw [Kint]; ring
    _ ≤ (u / 2) * q₂ := Nat.mul_le_mul_right _ hhalf

/-- **`06:1161--1162` and `09:1499`, the integrality clauses, proved at the frozen
dyadic widths.**

`K_int = 2^{r_3 + ell + r_2}` and `t_2 = 2^{k_2}` with `16 | t_2` and
`k_2 <= r_3 + ell + r_2` (the frozen Stage-2 comparison that makes `r' >= 1`);
then `t_2 | K_int`, `t_2 <= K_int`, and `16 | 9 K_int`, so the ledger's exact
output size `9K/16` is an integer.  General in the four exponents. -/
theorem dyadic_call_integrality {k₂ r₂ r₃ ℓ : ℕ} (hk₂ : 4 ≤ k₂) (hle : k₂ ≤ r₃ + ℓ + r₂) :
    (2 ^ k₂ : ℕ) ∣ Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) ∧
      (2 ^ k₂ : ℕ) ≤ Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) ∧
      16 ∣ 9 * Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) := by
  rw [Kint_dyadic]
  refine ⟨pow_dvd_pow 2 hle, Nat.pow_le_pow_right (by norm_num) hle, ?_⟩
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) 9

/-- **Aux 8.1 (`09:1451--1452` forces the width exponent).**

`u d_cls >= 8 s kappa` together with `d_cls <= 1` gives
`2^e >= 8 . 2^{r_3+ell} = 2^{r_3+ell+3}`, i.e. `e >= r_3 + ell + 3`.  This is
where `4 | u` -- the divisibility `lem:template-coordinate-extraction` demands --
and `D:761--762`'s power-of-two product count `u/2 = 2^{e-1}` both come from, and
it is why the exponent record `eq:contract-extension-exponents` can be
*constructed* rather than assumed.  General. -/
theorem width_exponent_ge {e r₃ ℓ : ℕ} {dcls : ℝ} (hdcls1 : dcls ≤ 1)
    (hlow : 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * dcls) : r₃ + ℓ + 3 ≤ e := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have h1 : (2 : ℝ) ^ e * dcls ≤ (2 : ℝ) ^ e := by nlinarith [hdcls1, hp]
  have h2 : (2 : ℝ) ^ (r₃ + ℓ + 3) = 8 * ((2 : ℝ) ^ (r₃ + ℓ)) := by
    have hpa := pow_add (2 : ℝ) (r₃ + ℓ) 3
    rw [hpa]; ring
  have hpow : (2 : ℝ) ^ (r₃ + ℓ + 3) ≤ (2 : ℝ) ^ e := by linarith
  by_contra hcon
  push Not at hcon
  have hnat : (2 : ℕ) ^ e < 2 ^ (r₃ + ℓ + 3) := Nat.pow_lt_pow_right (by norm_num) hcon
  have hc := (Nat.cast_lt (α := ℝ)).mpr hnat
  push_cast at hc
  linarith

/-- **The reachable width/class window (`09:1449--1456` with
`eq:protected-delta-min`).**

`(e, d_cls)` is *reachable* at these schedule values when it satisfies the two
frozen bounds of `eq:protected-dyadic-class` at `u = 2^e`, lies in the donor
range `(0,1]`, and is at least the frozen `delta_min` of
`eq:protected-delta-min` (`09:1486--1490`).  These are exactly the constraints
the extraction chain of `09:1441--1490` imposes on the pair it produces.

The point of naming the window is `bounded_of_reachableWidth`: it pins `2^e` to a
bounded range, which is what lets the schedule-owned uniform gates of
`eq:all-extension-gates` (`06:937--950`) be quantified over reachable widths
without becoming unsatisfiable.  `06:938--940` states exactly this uniformity --
"Every product-family application has ambient width at most `v_max q_2` ...  It is
therefore enough to verify ..." -- so the quantified shape is the frozen one and
not a Lean convenience. -/
def ReachableWidth (q r₃ ℓ : ℕ) (θ : ℝ) (e : ℕ) (dcls : ℝ) : Prop :=
  8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * dcls ∧
    (2 : ℝ) ^ e * dcls < 16 * ((2 : ℝ) ^ (r₃ + ℓ)) ∧
    0 < dcls ∧ dcls ≤ 1 ∧
    64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q ≤ dcls

/-- **Aux 8.2 (`06:938--940`, the reachable window is bounded).**

`2^e <= 2^ell q` at every reachable pair: `2^e d_cls < 16 . 2^{r_3+ell}` and
`d_cls >= delta_min = 64 B_theta L_q 2^{r_3}/q` give
`2^e < 2^ell q/(4 B_theta L_q) <= 2^ell q`, using `B_theta >= 1` and `L_q >= 1`.
This is the frozen `v_max` bound in the form this block needs, and it is the
evidence that the uniformly-quantified schedule gates below are not vacuous. -/
theorem bounded_of_reachableWidth {q r₃ ℓ e : ℕ} {θ dcls : ℝ} (hq : 0 < q) (hθ : 0 < θ)
    (h : ReachableWidth q r₃ ℓ θ e dcls) :
    (2 : ℝ) ^ e ≤ ((2 ^ ℓ : ℕ) : ℝ) * q := by
  obtain ⟨-, hupper, -, -, hdelta⟩ := h
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hBR : (1 : ℝ) ≤ (Btheta θ : ℝ) := by exact_mod_cast one_le_Btheta hθ
  have hLR : (1 : ℝ) ≤ (Lq q : ℝ) := by exact_mod_cast one_le_Lq q
  have hsR : (0 : ℝ) < ((2 ^ r₃ : ℕ) : ℝ) := by positivity
  have hepos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hkR : ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by push_cast; ring
  have hprod : (2 : ℝ) ^ (r₃ + ℓ) = ((2 ^ r₃ : ℕ) : ℝ) * (2 : ℝ) ^ ℓ := by
    push_cast; rw [pow_add]
  rw [div_le_iff₀ hqR] at hdelta
  have hBL : (1 : ℝ) ≤ (Btheta θ : ℝ) * (Lq q : ℝ) := by nlinarith [hBR, hLR]
  have hBLs : (0 : ℝ) ≤ ((Btheta θ : ℝ) * (Lq q : ℝ) - 1) * ((2 ^ r₃ : ℕ) : ℝ) :=
    mul_nonneg (by linarith [hBL]) (le_of_lt hsR)
  have hlow : 64 * ((2 ^ r₃ : ℕ) : ℝ) ≤ dcls * q := by nlinarith [hdelta, hBLs]
  have h1 : (2 : ℝ) ^ e * (64 * ((2 ^ r₃ : ℕ) : ℝ)) ≤ (2 : ℝ) ^ e * (dcls * q) :=
    mul_le_mul_of_nonneg_left hlow (le_of_lt hepos)
  have h2 : ((2 : ℝ) ^ e * dcls) * q < (16 * ((2 : ℝ) ^ (r₃ + ℓ))) * q :=
    mul_lt_mul_of_pos_right hupper hqR
  rw [hprod] at h2
  have hcomb : ((2 ^ r₃ : ℕ) : ℝ) * (64 * (2 : ℝ) ^ e)
      < ((2 ^ r₃ : ℕ) : ℝ) * (16 * ((2 : ℝ) ^ ℓ * q)) := by nlinarith [h1, h2]
  have hfinal : 64 * (2 : ℝ) ^ e < 16 * ((2 : ℝ) ^ ℓ * q) :=
    lt_of_mul_lt_mul_left hcomb (le_of_lt hsR)
  rw [hkR]
  linarith [hfinal, hepos]

/-- **The call-(iii) record is constructed, not assumed.**

From the frozen width data of `eq:protected-dyadic-class` at `u = 2^e`, together
with the schedule's `16 | t_2` (`4 <= T`) and the Stage-2 comparison
`k_2 <= r_3 + ell + r_2` that makes `r' >= 1`, the exponent contract
`eq:contract-extension-exponents` (`D:749--755`) is **derived**:
`R := (e-1) + r_2 - T` and `R_loc := r_3 + ell + r_2 - T`, and `R_loc <= R`
follows from `width_exponent_ge`.  The ambient-width clause is the banked
`ambient_width_ge` at `u = 2^e`.

That the record is constructed is what makes the whole shape sound: an earlier
version of this block *assumed* row (iii) uniformly in `(u, d_cls)`, and that
bundle is unsatisfiable at legal widths, because a large `d_cls` admits `u = 2`
and then `4 K_int <= (u/2) q_2` fails. -/
theorem extensionCallThree_of_width {T b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (hT : 4 ≤ T) (hTle : T ≤ r₃ + ℓ + r₂) (hℓ : 1 ≤ ℓ)
    (hdcls1 : dcls ≤ 1)
    (hlow : 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * dcls)
    (hhigh : (2 : ℝ) ^ e * dcls < 16 * ((2 : ℝ) ^ (r₃ + ℓ)))
    (hgate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁ ≤ dcls / 4)
    (hcol : callThreeH e / 2 ^ (0 : ℕ) ≤ colDens) :
    ExtensionCallThree T ((e - 1) + r₂ - T) (r₃ + ℓ + r₂ - T) b₁ e r₂ r₃ ℓ dcls colDens := by
  have he : r₃ + ℓ + 3 ≤ e := width_exponent_ge hdcls1 hlow
  have hud : 8 * (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)) ≤ (((2 ^ e : ℕ)) : ℝ) * dcls := by
    have hc : (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)) = (2 : ℝ) ^ (r₃ + ℓ) := by
      push_cast; rw [pow_add]
    have hu : (((2 ^ e : ℕ)) : ℝ) = (2 : ℝ) ^ e := by push_cast; ring
    rw [hc, hu]; exact hlow
  have hamb : 4 * Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) ≤ (2 ^ e / 2) * 2 ^ r₂ :=
    ambient_width_ge (dvd_pow_self 2 (by omega)) hdcls1 hud
  have hhalf : (2 : ℕ) ^ e / 2 = 2 ^ (e - 1) := by
    obtain ⟨c, hc⟩ : ∃ c, e = c + 1 := ⟨e - 1, by omega⟩
    subst hc
    simp [pow_succ]
  rw [hhalf] at hamb
  exact
    { uWidth_lower := hlow
      uWidth_upper := hhigh
      four_le_e := by omega
      four_le_T := hT
      ambient_exponent := by omega
      capacity_exponent := by omega
      rloc_le_r := by omega
      ambient_width := hamb
      row_density_gate := hgate
      column_density := hcol }

/-- **`lem:early-protected-closure` (`09:1418--1509`) entered at `D_mass`.**

This is the frozen proof from `09:1441` onward: the extraction chain, the width
`u = 2^e`, the poor-`u`-set cover, the denser Bob child, the template
extraction, the represented Stage-2 blocks, the call-(iii) record, and the
endpoint arithmetic.  `earlyProtectedClosure` below enters one step earlier, at
`eq:protected-early-threshold` itself, through `protected_reservoir_halving`.

**Everything in row (iii) is constructed here.**  The width `u = 2^e` and its two
dyadic bounds, the exponent contract `eq:contract-extension-exponents`, the
ambient-width inequality, the represented-block count `K_int`, and the entering
column density `h = rho_1 2^{-u-1}` are all produced from schedule data; only
the following remain as named binders, and none is an `axiom`:

* `hLocEx`, the inherited `thm:certified-localized-extension` (`A:109--146`), in
  the exact implication shape the frozen theorem has, with its antecedents in the
  order `A:110--146` prints them at the `06:1147--1153` substitution
  `M = M_1^T`, `H = B_cap`, `x = 2^{-b_1}`, `y_* = 3/5`, `t = t_2 = 2^{k_2}`,
  `r = 2^R`, `r' = 2^{R_loc}`, `eps = eps_prod`, `h = rho_1 2^{-u-1}`,
  `a^sharp = 0`.  Call (iii) has `v = u/2 > 1`, so `06:1119--1120` puts it on the
  **product** branch of `A:126--128` and its balancedness error is
  `eps_prod` of `eq:epsilon-product` (`06:851--857`), not `0`; `heps0`/`heps1`
  are that branch's `0 < eps < 1`.  **`EXPANDER-001` has no Lean declaration by
  design**: the cited balanced family reaches this module only through those two
  explicit binders, never as a silent axiom.
* `hbase` (`eq:certified-base`, `A:113--116`), `htcert` (`A:117`), `hE1`, `hE2`
  (`eq:certified-E1`, `eq:certified-E2`) and `hrows` (`A:139--140`), which belong
  to `06`, not to this block.  The two gates are quantified over
  `ReachableWidth` rather than over all widths, which is `06:937--950`'s own
  uniformity and is what keeps them satisfiable.
* `hQuery` (`09:1463--1464`, the printed Bob-query sentence "after Bob's query,
  one child has density at least `rho_1`"), together with the relabelling of the
  selected donors as the coordinates of `Y^u` -- that relabelling has no printed
  anchor and is an **encoding convention**, carried explicitly by the `Fin u ≃ ↥J`
  binder rather than cited; and `hBlocks` (`09:1473--1479`),
  the Stage-4 reservoir geometry behind the `q_2`-fibre average.  Both are
  GAP-EXPOSED and neither is asserted.
* `hGate`, the structural-gate comparison of `06:1151--1152`, stated against
  `delta_min` (`eq:protected-delta-min`) rather than against `d_cls` -- which is
  what makes `eq:protected-delta-min` load-bearing: the schedule cannot see the
  class the argument happens to select, so the gate must hold at the frozen lower
  bound and be transported upward.

The conclusion is the frozen `C + log_2 kappa - 1` at the banked
`TerminalTwoStream.terminalTarget`, written subtraction-free. -/
theorem earlyProtectedClosureFromDmass
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    {Mem : Type*} (memCost : Mem → ℕ) (child : Mem)
    (isRestr : Mem → ℕ → ℕ → ℝ → Prop)
    {q k₂ b₁ r₂ r₃ ℓ bcap tcert selCard rowsPerBlock : ℕ}
    {θ lamT x epsProd : ℝ}
    (S : Finset (Fin q → Y)) (YT : Finset Y) (J₀ : Finset (Fin q)) (d : Fin q → ℝ)
    (hq : 0 < q) (hℓ : 1 ≤ ℓ) (hθ0 : 0 < θ)
    (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂) (hbcap : 2 ≤ bcap)
    (hJ : J₀.card ≤ q) (hd0 : ∀ j ∈ J₀, 0 ≤ d j) (hd1 : ∀ j ∈ J₀, d j ≤ 1)
    -- `09:1436--1439`, `D_mass`
    (hDmass : 64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)
        ≤ ∑ j ∈ J₀, d j)
    -- `06:1151--1152` at `delta_min`
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    -- the column-density chain of `09:1458--1471`
    (hY : 0 < Fintype.card Y) (hYT0 : 0 < YT.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    -- `09:1463--1464`, the relabelling and Bob's query, as a genuine partition
    (hQuery : ∀ (u : ℕ) (J : Finset (Fin q)), J.card = u →
        ∃ (eJ : Fin u ≃ ↥J) (P₀ P₁ : Finset (Fin u → Y)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ S)
    -- `09:1473--1483`, the represented Stage-2 blocks
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    -- `A:112`, `A:113--117`, `06:558--572`
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rw)
    (hbase : bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5))
    (htcert : tcert ≤ 2 ^ k₂)
    -- `A:126--128` on the product branch, at `eps_prod` of `eq:epsilon-product`
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    -- `eq:certified-E1`, `eq:certified-E2` uniformly over `eq:all-extension-gates`
    (hE1 : ∀ (e R : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls → R + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd))
    (hE2 : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    -- `A:139--140`, at least `ceil(r' t x m)` rows in each represented block
    (hrows : ⌈((2 : ℝ) ^ (r₃ + ℓ + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsPerBlock)
    -- `09:1499--1504`, the selection: **under the frozen `D_mass` threshold** the
    -- extraction chain selects exactly `9 K_int/16` represented blocks and the
    -- restriction they cut out of `Mhat` is realized at a child of `v` ("Localized
    -- Extension gives the **selected** Bob child complexity", `09:1503--1504`).
    -- GAP-EXPOSED: this module models no protocol, so the selection enters as a
    -- binder -- but it is gated on `D_mass`, because the frozen selection exists
    -- only inside the proof of `lem:early-protected-closure`.
    -- The frozen selection is **singular**: `09:1501--1502` records "the entering
    -- column density" -- one restriction at one entering density -- so the datum is
    -- asserted at that density itself, the `A:141` floor `h 2^{-a^sharp}` at
    -- `a^sharp = 0`, and never at an unbounded family of densities.
    -- Round `r2` of the re-shape adds the **extraction gate**: in the frozen text
    -- the selection of `09:1499` is downstream of `09:1466--1471`, so the binder
    -- fires only once the extraction of `09:1458--1471` has actually produced its
    -- output -- a child `P` of the relabelled parent, a half-width coordinate set
    -- `J'`, and the entering column density attained on it.  That output is
    -- exactly what `selectedColumnDensity` delivers, so `hQuery`, `hS`, `hYT`,
    -- `hgap`, `hY` and `hYT0` are load-bearing for the endpoint and no
    -- mass-plus-width-only bundle reaches it.
    (hSelect : 64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)
          ≤ ∑ j ∈ J₀, d j →
        ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
          ExtractionOutput S YT e →
          isRestr child ((2 : ℕ) ^ (r₃ + ℓ + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock
            (callThreeH e / 2 ^ (0 : ℕ)))
    (hLocEx : ∀ (e R Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ) (w : Mem),
        -- the call record of `06:1147--1153` and `D:746--764`
        ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
        -- `A:111`, `M` nonempty and `H >= 2`
        1 ≤ Fintype.card Rw → 2 ≤ bcap →
        -- `A:112`, `0 < x <= 1`, strict on the left exactly as frozen
        0 < x → x ≤ 1 →
        -- `A:113--116`, `eq:certified-base`
        bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
        -- `A:117--118`, `t >= t_cert`, a power of two divisible by `16`, `t x <= 1`
        tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
        -- `A:125`, `r, r'` positive powers of two with `r' <= r`, `q = r t`
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R → (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
        -- `A:126--128`, the `(q,t,eps)`-balanced product branch: `0 < eps < 1`
        0 < epsProd → epsProd < 1 →
        -- `A:128--129`, `h in (0,1]` at `h = rho_1 2^{-u-1}`
        0 < callThreeH e → callThreeH e ≤ 1 →
        -- `eq:certified-E1`, `eq:certified-E2`
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        -- `A:138`, first half: the endpoint speaks about a **restriction of
        -- `Mhat`**, so the object whose cost is concluded is the one carrying the
        -- restriction data, bound here inside the quantifier together with them
        isRestr w blocks rowsEach colDens →
        -- `A:138`, second half: **exactly** `r' p_t` represented outer blocks,
        -- with `p_t = 9t/16` of `eq:certified-pt-ht` integral at `16 | t`, and the
        -- `09:1499` supply out of which exactly that many are selected
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        -- `A:139--140`, the per-block row count, read off the same restriction
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsEach →
        -- `A:141` at `a^sharp = 0`, column density at least `h 2^{-a^sharp}`
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        -- `A:142--144`, the conclusion `H + log_2(r' t)`, about that restriction
        bcap + (Rloc + k₂) ≤ memCost w) :
    TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ ≤ memCost child + 1 := by
  classical
  have hs1 : 1 ≤ (2 ^ r₃ : ℕ) := Nat.one_le_two_pow
  have hκ2 : 2 ≤ (2 ^ ℓ : ℕ) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hcast : (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)) = (2 : ℝ) ^ (r₃ + ℓ) := by
    push_cast; rw [pow_add]
  have hcastu : ∀ n : ℕ, (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by
    intro n; push_cast; ring
  -- `09:1441--1490`: the dyadic class, its representative, and `delta_min`
  obtain ⟨kcls, V, -, -, hVheavy, hVdelta⟩ :=
    exists_protected_dyadic_class J₀ d hq hs1 hκ2 hθ0 hJ hd0 hd1 hDmass
  -- `09:1449--1456`: the width `u = 2^e`
  obtain ⟨e, he1, hulow0, huhigh0, hVcard⟩ :=
    exists_width_u (B := Btheta θ) (s := 2 ^ r₃) (κ := 2 ^ ℓ)
      (classWidth_pos kcls) (classWidth_le_one kcls) hs1 hκ2 (one_le_Btheta hθ0) hVheavy
  have hulow : 8 * ((2 : ℝ) ^ (r₃ + ℓ)) ≤ (2 : ℝ) ^ e * classWidth kcls := by
    rw [← hcast]; exact hulow0
  have huhigh : (2 : ℝ) ^ e * classWidth kcls < 16 * ((2 : ℝ) ^ (r₃ + ℓ)) := by
    rw [← hcast]; exact huhigh0
  have he3 : r₃ + ℓ + 3 ≤ e := width_exponent_ge (classWidth_le_one kcls) hulow
  have hreach : ReachableWidth q r₃ ℓ θ e (classWidth kcls) :=
    ⟨hulow, huhigh, classWidth_pos kcls, classWidth_le_one kcls, hVdelta⟩
  -- `09:1458--1471`: the entering column density `h = rho_1 2^{-u-1}`
  have hVnat : 2 ^ e * Btheta θ ≤ V.card := by
    have hpow : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
    have hBnn : (0 : ℝ) ≤ ((Btheta θ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : ((2 ^ e * Btheta θ : ℕ) : ℝ) ≤ (V.card : ℝ) := by
      push_cast
      nlinarith [hVcard, mul_nonneg (le_of_lt hpow) hBnn]
    exact_mod_cast hstep
  -- `09:1458--1471`: the extraction runs, and its output -- the child of the
  -- relabelled parent, the frozen half width `u/2`, and the entering column
  -- density `h = rho_1 2^{-u-1}` attained on it -- is produced here, from
  -- `hQuery`, `hS`, `hYT`, `hgap`, `hY` and `hYT0`.  Round `r1` computed this and
  -- then discarded it; round `r2` makes it the **input** of the `09:1499`
  -- selection, which is the order the frozen proof has.
  have hext : ExtractionOutput S YT e :=
    extractionOutput_of_selectedColumnDensity (θ := θ) (lamT := lamT) S YT V hY hθ0
      (by omega) hYT0 hVnat hS hYT hgap (fun J _ hJc => hQuery (2 ^ e) J hJc)
  -- `06:1151--1152` transported to the selected class through `eq:protected-delta-min`
  have hGate' : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁ ≤ classWidth kcls / 4 :=
    le_trans hGate (by linarith [hVdelta])
  -- `06:1147--1153` and `D:746--764`: the call record, constructed
  have hcall :
      ExtensionCallThree k₂ ((e - 1) + r₂ - k₂) (r₃ + ℓ + r₂ - k₂) b₁ e r₂ r₃ ℓ
        (classWidth kcls) (callThreeH e / 2 ^ (0 : ℕ)) :=
    extensionCallThree_of_width hk₂ hk₂le hℓ (classWidth_le_one kcls) hulow huhigh hGate'
      (le_refl _)
  -- `09:1473--1483`: the represented Stage-2 blocks
  have hK : (Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) : ℝ) ≤ (selCard : ℝ) := by
    have hud : 8 * (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ))
        ≤ (((2 ^ e : ℕ)) : ℝ) * classWidth kcls := by
      rw [hcastu e]; exact hulow0
    have hb := representedBlocks_ge (s := 2 ^ r₃) (κ := 2 ^ ℓ) (q₂ := 2 ^ r₂) (u := 2 ^ e)
      (dcls := classWidth kcls) (perDonor := classWidth kcls * ((2 ^ r₂ : ℕ) : ℝ) / 4)
      (dvd_pow_self 2 (by omega)) hud (le_refl _)
    exact le_trans hb (hBlocks e (classWidth kcls) hreach)
  have hKnn : (0 : ℝ) ≤ (Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) : ℝ) := by positivity
  have hKd : Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) = 2 ^ (r₃ + ℓ + r₂) := Kint_dyadic r₂ r₃ ℓ
  have hcount : 9 * ((2 ^ ((r₃ + ℓ + r₂ - k₂) + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) := by
    have hexp : (r₃ + ℓ + r₂ - k₂) + k₂ = r₃ + ℓ + r₂ := by omega
    rw [hexp, ← hKd]
    linarith [hK, hKnn]
  -- `09:1499--1504`: the selected blocks, and the restriction they cut out, at the
  -- single entering density `h 2^{-a^sharp}` the call row records.  The selection
  -- is fed the extraction's own output, so it stands strictly downstream of
  -- `09:1466--1471`, as it does in the frozen proof.
  have hsel := hSelect hDmass e (classWidth kcls) hreach hext
  -- the inherited endpoint at call (iii), applied to that restriction
  have hend := hLocEx e ((e - 1) + r₂ - k₂) (r₃ + ℓ + r₂ - k₂)
    ((2 : ℕ) ^ (r₃ + ℓ + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock (classWidth kcls)
    (callThreeH e / 2 ^ (0 : ℕ)) child
    hcall hMne hbcap hx0 hx1 hbase htcert hk₂ htx
    Nat.one_le_two_pow hcall.r'_le_r (pow_add 2 _ k₂).symm heps0 heps1
    (callThreeH_pos e) (callThreeH_le_one e)
    (hE1 e ((e - 1) + r₂ - k₂) (classWidth kcls) hreach hcall.ambient_exponent)
    (hE2 e (classWidth kcls) hreach)
    hsel hcall.selected_count rfl hcount hrows hcall.column_density
  have hcap : (r₃ + ℓ + r₂ - k₂) + k₂ = r₃ + ℓ + r₂ := hcall.capacity_exponent
  have hid := endpoint_identity bcap r₂ r₃ ℓ
  simp only [DenseBranchSelection.Dtwo] at hid
  omega

/-- **`lem:early-protected-closure` (`09:1418--1509`), at its own threshold.**

"Let `v` be a first-Bob node and put `kappa = kappa_v >= 2`.  If
`P_v(J_0) >= 128 mu_P B_theta L_q s kappa` (`eq:protected-early-threshold`), then
one child of `v` has communication complexity at least `C + log_2 kappa - 1`."

The hypothesis is the frozen `eq:protected-early-threshold` itself, on the
`mu_P`-weighted protected mass `P_v(J_0)` of `09:1374--1376`, with the two
protected reservoir types carried as the two density functions `d_0`, `d_1`.
`protected_reservoir_halving` performs `09:1433--1439` -- "One of the two
protected reservoir types contributes at least half" -- and
`earlyProtectedClosureFromDmass` runs the rest of the frozen proof on whichever
type survives.  This is why `mu_P` is defined here at all: it is the
normalization that turns the `128 mu_P` of the threshold into the `64` of
`D_mass`.

`kappa = kappa_v >= 2` is `hl : 1 <= ell` at `kappa = 2^ell`, and `09:1253`
already makes `kappa_v = 2^{r-d_v}` a power of two, so the dyadic form is not a
narrowing.  The conclusion is `C + log_2 kappa - 1 <= comp(child)` at the banked
`TerminalTwoStream.terminalTarget`, written subtraction-free.

No route completion is claimed: `sec:wrapper-mass-redistribution`
(`09:1512--1781`) remains GAP-EXPOSED in full. -/
theorem earlyProtectedClosure
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    {Mem : Type*} (memCost : Mem → ℕ) (child : Mem)
    (isRestr : Mem → ℕ → ℕ → ℝ → Prop)
    {q k₂ b₁ r₂ r₃ ℓ bcap tcert selCard rowsPerBlock : ℕ}
    {θ lamT x epsProd : ℝ}
    (S : Finset (Fin q → Y)) (YT : Finset Y) (J₀ : Finset (Fin q)) (d₀ d₁ : Fin q → ℝ)
    (hq : 0 < q) (hℓ : 1 ≤ ℓ) (hθ0 : 0 < θ)
    (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂) (hbcap : 2 ≤ bcap)
    (hJ : J₀.card ≤ q)
    (hd₀0 : ∀ j ∈ J₀, 0 ≤ d₀ j) (hd₀1 : ∀ j ∈ J₀, d₀ j ≤ 1)
    (hd₁0 : ∀ j ∈ J₀, 0 ≤ d₁ j) (hd₁1 : ∀ j ∈ J₀, d₁ j ≤ 1)
    -- `eq:protected-early-threshold` (`09:1421--1425`), on `P_v(J_0)` itself
    (hthr : 128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)
        ≤ muP * ((∑ j ∈ J₀, d₀ j) + (∑ j ∈ J₀, d₁ j)))
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hY : 0 < Fintype.card Y) (hYT0 : 0 < YT.card)
    (hS : θ * (Fintype.card Y : ℝ) ^ q ≤ (S.card : ℝ))
    (hYT : lamT * (Fintype.card Y : ℝ) ≤ (YT.card : ℝ))
    (hgap : 1 - lamT ≤ rhoOne / 8)
    (hQuery : ∀ (u : ℕ) (J : Finset (Fin q)), J.card = u →
        ∃ (eJ : Fin u ≃ ↥J) (P₀ P₁ : Finset (Fin u → Y)),
          Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = ambientRelabel J eJ S)
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rw)
    (hbase : bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5))
    (htcert : tcert ≤ 2 ^ k₂)
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    (hE1 : ∀ (e R : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls → R + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd))
    (hE2 : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    (hrows : ⌈((2 : ℝ) ^ (r₃ + ℓ + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsPerBlock)
    -- `09:1499--1504`, gated on `eq:protected-early-threshold` itself
    -- The frozen selection is **singular**: `09:1501--1502` records "the entering
    -- column density" -- one restriction at one entering density -- so the datum is
    -- asserted at that density itself, the `A:141` floor `h 2^{-a^sharp}` at
    -- `a^sharp = 0`, and never at an unbounded family of densities.
    -- Round `r2` of the re-shape additionally gates it on the **output of the
    -- extraction** of `09:1458--1471`, which is where the frozen proof stands when
    -- it reaches `09:1499`.
    (hSelect : 128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ)
          * ((2 ^ ℓ : ℕ) : ℝ)
          ≤ muP * ((∑ j ∈ J₀, d₀ j) + (∑ j ∈ J₀, d₁ j)) →
        ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
          ExtractionOutput S YT e →
          isRestr child ((2 : ℕ) ^ (r₃ + ℓ + r₂ - k₂) * (9 * 2 ^ k₂ / 16)) rowsPerBlock
            (callThreeH e / 2 ^ (0 : ℕ)))
    (hLocEx : ∀ (e R Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ) (w : Mem),
        ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
        1 ≤ Fintype.card Rw → 2 ≤ bcap →
        0 < x → x ≤ 1 →
        bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
        tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R → (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callThreeH e → callThreeH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        isRestr w blocks rowsEach colDens →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsEach →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ memCost w) :
    TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ ≤ memCost child + 1 := by
  rcases protected_reservoir_halving J₀ d₀ d₁ hthr with h | h
  · exact earlyProtectedClosureFromDmass Mmat memCost child isRestr S YT J₀ d₀ hq hℓ hθ0
      hk₂ hk₂le hbcap hJ hd₀0 hd₀1 h hGate hY hYT0 hS hYT hgap hQuery hBlocks hx0 hx1 htx
      hMne hbase htcert heps0 heps1 hE1 hE2 hrows (fun _ => hSelect hthr) hLocEx
  · exact earlyProtectedClosureFromDmass Mmat memCost child isRestr S YT J₀ d₁ hq hℓ hθ0
      hk₂ hk₂le hbcap hJ hd₁0 hd₁1 h hGate hY hYT0 hS hYT hgap hQuery hBlocks hx0 hx1 htx
      hMne hbase htcert heps0 heps1 hE1 hE2 hrows (fun _ => hSelect hthr) hLocEx

/-! ## Section 9  Non-vacuity at two tiers, and statement poles

Every new predicate is inhabited and every existential deliverable is shown to
fail on its trivial witness.  A green build sees none of this.

Round `r3` splits the inhabitants into two **explicitly labelled tiers**, and
the labels are load-bearing:

* **schedule tier.**  `reachableWidth_at_scheduleTheta` and
  `earlyProtectedClosure_block_bundle_at_scheduleTheta` stand at values the
  frozen defining displays produce: `theta = 1/(160 Q)` with `Q` the `06:532`
  least power of two above `Q_0`, `s = 2^{r_3}` at the `eq:s-choice` floor
  `512 <= s` with `64 | s`, `kappa = 2^{ell} >= 2`, and a width
  `q = 2^{A_wrap L_P^2}` of the `eq:q-deltaU` shape;
* **floor tier (BEYOND-PAPER).**  The five `floorTier` probes and
  `earlyProtectedClosure_block_bundle_is_consistent` keep the round-`r2`
  numerals `theta = 1/20480`, `s = 4`, `q = 2^24`.  Those meet the Section-4
  floors and the Stage-2 structural gates and nothing else -- `eq:s-choice`
  gives `s >= 512`, `eq:Q-theta-choice` gives `theta <= 1/2621440`, and
  `eq:q-deltaU` has no exponent `24` -- so they audit *our encoding* at points
  the paper never visits.  They claim no legality, and no parameter value may be
  read out of them. -/

/-- **FLOOR-TIER PROBE (BEYOND-PAPER; NON-FIDELITY).  `ExtensionCallThree` is
satisfiable at nondegenerate widths.**

The record's ten fields are exercised at `r_2 = 13` (`q_2 = 8192`),
`T = k_2 = 5` (`t_2 = 32`, so `4 t_2 = 128 <= 8192 = q_2`), `b_1 = 40`,
`r_3 = 2` (`s = 4`), `ell = 1` (`kappa = 2`, the `09:1420` floor), `e = 7`
(`u = 128`), `d_cls = 1/2`, and `colDens = h` exactly.

It is not degenerate as an inhabitant: `8 s kappa = 64 = 2^7 . (1/2) = u d_cls`
attains the lower dyadic bound while the upper one is strict
(`64 < 128 = 16 s kappa`); `e = 7 >= r_3 + ell + 3 = 6`; `R_loc + T = 16` and
`R + T = 19` give `R_loc = 11 <= 14 = R`, the exponent contract
`eq:contract-extension-exponents` with all three named exponents;
`4 K_int = 262144 <= 524288 = 2^{e-1} q_2`; the row gate is
`2^{16}/2^{40} = 2^{-24} <= 1/8 = d_cls/4`; and the column density is the frozen
`h = rho_1 2^{-129}`, which is positive, so the record does **not** hold for the
degenerate `h = 0`.

**What it is not.**  `s = 4` meets the Section-4 floor (`04:389`
`def:guarded-source-constructor`, `04:460` `lem:guarded-source-active-slot`,
`04:481` `def:guarded-source-retention`, `04:504` `thm:guarded-source`,
`04:619`) but **not** `eq:s-choice` (`06:112--120`), which forces `s >= 512`
with `64 | s` (`06:394--395`).  Round `r2` called this tuple "legal"; that
claim is withdrawn.  `ExtensionCallThree` has no schedule-tier inhabitant here,
because its `b_1`, `r_2` and `k_2` are Stage-1/Stage-2 quantities defined
outside `sec:wrapper-protected-early`; the canonical-inhabitation obligation is
registered in `OBLIGATION_LEDGER.md` and is **not** discharged by this probe. -/
theorem extensionCallThree_floorTier_instance :
    ExtensionCallThree 5 14 11 40 7 13 2 1 (1 / 2) (callThreeH 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [Kint]
  · norm_num
  · rw [pow_zero, div_one]

/-- **FLOOR-TIER ANCHORS of the probe family, as checked identities (round
`r3`; the name and the claim are both weaker than round `r2`'s).**

Two things the probe tuple above really does satisfy, carried as literal
arithmetic so that it cannot drift: the Section-4 guarded-source **floor**
`s >= 4` a power of two (`04:389`, `04:460`, `04:481`, `04:504`, `04:619`) at
`s = 2^{r_3} = 4`, and `eq:stage2-structural-gates` (`06:835`) `4 t_2 <= q_2` at
`t_2 = 2^{k_2} = 32`, `q_2 = 2^{r_2} = 8192`.  The round-`r1` family violated
both (it ran at `s = 1`, and at `r_2 = 4` with `t_2 = 16`), so the guard is
still worth having.

Round `r2` named this theorem `witness_family_schedule_legality` and read it as
certifying that the tuple is a *schedule* point.  It does not and cannot: a
floor is not a defining display, and `eq:s-choice` (`06:112--120`, with
`06:394--395`) forces `s >= 512` with `64 | s`.  The legality claim is
withdrawn; what remains is exactly the two inequalities named. -/
theorem witness_family_floorTier_anchors :
    4 ≤ (2 ^ 2 : ℕ) ∧ (2 : ℕ) ^ 2 = 4 ∧ 4 * (2 ^ 5 : ℕ) ≤ 2 ^ 13 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **FLOOR-TIER PROBE (BEYOND-PAPER): the call record is reachable from the
width data.**

The same tuple as `extensionCallThree_floorTier_instance`, obtained through
`extensionCallThree_of_width` rather than by hand: the exponent contract is
*derived*, not asserted.  This is the statement-pole check for
`extensionCallThree_of_width` -- had the constructor's arithmetic been wrong, no
width at all would produce a record.  The tier label is inherited from the tuple
and, like it, claims no schedule legality. -/
theorem extensionCallThree_of_width_floorTier_instance :
    ExtensionCallThree 5 ((7 - 1) + 13 - 5) (2 + 1 + 13 - 5) 40 7 13 2 1
      (1 / 2) (callThreeH 7) :=
  extensionCallThree_of_width (T := 5) (b₁ := 40) (e := 7) (r₂ := 13) (r₃ := 2) (ℓ := 1)
    (dcls := 1 / 2) (colDens := callThreeH 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [pow_zero, div_one])

/-- **FLOOR-TIER PROBE (BEYOND-PAPER): `ReachableWidth` is inhabited.**

At the audit density `theta = 1/20480` the window `ReachableWidth` is inhabited
at `q = 2^24`, `r_3 = 2` (`s = 4`), `ell = 1`, `e = 6`, `d_cls = 1`: the two
dyadic bounds are `64 <= 64 < 128`, the class width is in `(0,1]`, and
`delta_min = 64 B_theta L_q . 4/2^24 <= 1` because `B_theta <= 1100` and
`L_q = 26` (`64 . 1100 . 26 . 4 = 7321600 <= 16777216`).

Round `r2` called all three of `theta`, `s` and `q` legal here.  None is:
`eq:Q-theta-choice` with `06:547` and `05:39--40` gives `theta <= 1/2621440`
(`scheduleTheta_route_le`), `eq:s-choice` gives `s >= 512`, and `eq:q-deltaU`
has no reachable exponent `24` (`q = 2^{A_wrap L_P^2}` with `L_P >= 4`).  The
schedule-tier statement -- the one that actually shows the uniformly-quantified
gates `hE1`, `hE2`, `hBlocks` range over a nonempty set at parameter values the
paper produces -- is `reachableWidth_at_scheduleTheta`; this probe is retained
only because it is the concrete arithmetic that `bounded_of_reachableWidth` was
first exercised against. -/
theorem reachableWidth_floorTier_instance :
    ReachableWidth (2 ^ 24) 2 1 (1 / 20480) 6 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_refl _, ?_⟩
  have hB : (Btheta (1 / 20480) : ℝ) ≤ 1100 := by exact_mod_cast Btheta_floorTier_le
  have hL : (Lq (2 ^ 24) : ℝ) = 26 := by
    have : Lq (2 ^ 24) = 26 := by
      unfold Lq
      rw [show 2 * 2 ^ 24 = 2 ^ 25 by ring, Nat.clog_pow 2 25 (by norm_num)]
    rw [this]; norm_num
  have hBnn : (0 : ℝ) ≤ (Btheta (1 / 20480) : ℝ) := Nat.cast_nonneg _
  rw [hL, div_le_one (by positivity)]
  push_cast
  linarith [hB, hBnn]

/-- **FLOOR-TIER CONSISTENCY PROBE (BEYOND-PAPER): the block-owned premise
bundle is not self-contradictory.**

Every gate in this pipeline can pass while the principal deliverable is vacuous,
so the block-owned half of `earlyProtectedClosure`'s bundle is discharged
constructively.  The instantiation is the audit density `theta = 1/20480`,
`q = 2^24`, `r_3 = 2` (`s = 4`), `ell = 1` (`kappa = 2`, the `09:1420` floor),
`r_2 = 6` (`q_2 = 64`), `k_2 = 4` (`t_2 = 16`), `b_1 = 24`, donor densities
identically `1`.  Then `L_q = 26`, `2 <= B_theta <= 1100`
(`Btheta_floorTier_ge_two`, `Btheta_floorTier_le`) -- in particular
`B_theta >= 2`, so the poor-`u`-set cover `u(B_theta - 1)` is **not** the empty
cover, which is the degenerate corner the round-`r0` `theta = 1` witness sat in
-- and:

* the Section-4 guarded-source floor and the Stage-2 structural gate are carried
  as checked identities rather than left implicit: `s = 4 >= 4` a power of two
  (`04:389`, `04:460`, `04:481`, `04:504`, `04:619`) and `4 t_2 = 64 <= 64 = q_2`
  (`eq:stage2-structural-gates`, `06:835`).  The round-`r1` witness ran at
  `s = 1` and at `r_2 = 4` with `t_2 = 16`, i.e. `4 t_2 = 64 > 16 = q_2`, and so
  violated both;
* `eq:protected-early-threshold` at `mu_P`: `128 mu_P B_theta L_q s kappa
  = mu_P . 26624 B_theta <= mu_P . 2 . 2^24` because `B_theta <= 1100`;
* `D_mass` after halving: `64 B_theta . 26 . 4 . 2 = 13312 B_theta <= 2^24`;
* the structural gate `06:1151--1152`:
  `2^{r_3+ell+r_2}/2^{b_1} = 2^9/2^{24} <= (64 B_theta . 26 . 4/2^24)/4`, which
  needs `B_theta >= 1` and, at `b_1 = 20`, would have needed `B_theta >= 5`; the
  bracket `2 <= B_theta <= 1100` is what supplies it, and the degenerate
  `theta = 1` corner is excluded by `two_le_Btheta`.

**Tier, explicitly.**  Round `r2` titled this "at a LEGAL retained density" and
read `theta = 1/20480` as `eq:Q-theta-choice` at `Q = 2^7 = 128`.  That reading
is refuted by `Qwidth_route_floor`: the route forces `Q >= 2^14`, hence
`theta <= 1/2621440`.  Together with `s = 4` against `eq:s-choice` and `q = 2^24`
against `eq:q-deltaU`, all three numerals here are BEYOND-PAPER audit points, so
this is a consistency certificate for the block-owned binders and **no parameter
value may be read out of it**.  The schedule-tier statement is
`earlyProtectedClosure_block_bundle_at_scheduleTheta`.

Following the banked
`WrapperLowRungs.wrapperLowExtension_fires_at_legal_tier`, it exhibits **no**
inhabitant of `hLocEx`, `hbase`, `hE1` or `hE2`, and could not: at small `k_2`
those gates are unsatisfiable, which is precisely why `eq:tref-search`
(`06:558--572`) forces `k_ref >= 2^19`, hence a certified width
`t_ref = 2^{k_ref}`. -/
theorem earlyProtectedClosure_block_bundle_is_consistent :
    2 ≤ Btheta (1 / 20480) ∧
      Btheta (1 / 20480) ≤ 1100 ∧
      Lq (2 ^ 24) = 26 ∧
      4 ≤ (2 ^ 2 : ℕ) ∧
      4 * (2 ^ 4 : ℕ) ≤ 2 ^ 6 ∧
      64 * (Btheta (1 / 20480) : ℝ) * (Lq (2 ^ 24) : ℝ) * ((2 ^ 2 : ℕ) : ℝ)
          * ((2 ^ 1 : ℕ) : ℝ) ≤ ((2 ^ 24 : ℕ) : ℝ) ∧
      ((2 : ℝ) ^ (2 + 1 + 6)) / 2 ^ 24
          ≤ (64 * (Btheta (1 / 20480) : ℝ) * (Lq (2 ^ 24) : ℝ) * ((2 ^ 2 : ℕ) : ℝ)
              / ((2 ^ 24 : ℕ) : ℝ)) / 4 := by
  have hL : Lq (2 ^ 24) = 26 := by
    unfold Lq
    rw [show 2 * 2 ^ 24 = 2 ^ 25 by ring, Nat.clog_pow 2 25 (by norm_num)]
  have hge : 2 ≤ Btheta (1 / 20480) := Btheta_floorTier_ge_two
  have hle : Btheta (1 / 20480) ≤ 1100 := Btheta_floorTier_le
  have hgeR : (2 : ℝ) ≤ (Btheta (1 / 20480) : ℝ) := by exact_mod_cast hge
  have hleR : (Btheta (1 / 20480) : ℝ) ≤ 1100 := by exact_mod_cast hle
  have hLR : (Lq (2 ^ 24) : ℝ) = 26 := by rw [hL]; norm_num
  refine ⟨hge, hle, hL, by norm_num, by norm_num, ?_, ?_⟩
  · rw [hLR]; push_cast; linarith [hleR]
  · rw [hLR]; push_cast; rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith [hgeR]

/-! ### Schedule-tier non-vacuity (round `r3`)

The two inhabitants below stand at values the frozen defining displays produce,
and every one of them is *evaluated* rather than chosen:

* `theta = 1/(160 Q)` is `eq:Q-theta-choice` at `06:539`, with `Q` the banked
  `EntryGates.Qwidth` -- `06:532`'s least power of two at least `Q_0` -- so the
  threshold is never a numeral;
* `s = 2^{r_3}` is constrained by `eq:s-choice` (`06:112--120`) and
  `06:394--395` to `512 <= s` with `64 | s`, and those two consequences enter as
  the binder `9 <= r_3` and are *checked* in the deliverable.  The defining
  display itself is the banked `ParameterSchedule.sScale` with
  `ParameterSchedule.sScale_floor`; that module imports this one, so the chain
  is consumed here as its two derived consequences and the composition is a
  registered ledger obligation;
* `kappa = 2^{ell}` is at the `09:1420` floor `kappa >= 2`, also checked;
* `q = 2^{A_wrap L_P^2}` is the `eq:q-deltaU` shape (`06:514--518`).  `A_wrap` is
  the one genuinely **free** input in sight -- `06:520--522` fixes only that it
  "is chosen large enough to dominate every protocol-independent
  exceptional-set bound" -- so it is *produced* by `exists_wrapper_exponent`
  from the frozen requirement, never picked. -/

/-- **Aux 9.1 (`09:1382` at a power-of-two width).**  `L_q = clog_2(2q) + 1`
evaluates to `n + 2` at `q = 2^n`.  General in `n`; this is the identity that
makes the `eq:protected-delta-min` comparison a statement about the exponent. -/
theorem Lq_two_pow (n : ℕ) : Lq (2 ^ n) = n + 2 := by
  unfold Lq
  rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring, Nat.clog_pow 2 (n + 1) (by norm_num)]

/-- **Aux 9.2 (the arithmetic core of "chosen large enough", `06:520--522`).**

`M (n + 2) <= 2^n` for every `n >= 2M + 5`.  General in `M >= 1` and `n`: a
linear-in-`n` demand is eventually dominated by `2^n`, and the threshold is
explicit so that the width can be exhibited rather than merely asserted to
exist.

Base case: `2^{2M+5} = 32 (2^M)^2 > 32 M^2 >= 9 M^2 >= M(2M + 7)`.  Step: the
demand grows by `M` while the bound doubles, and `M <= n < 2^n`. -/
theorem mul_succ_le_two_pow {M : ℕ} (hM : 1 ≤ M) :
    ∀ n, 2 * M + 5 ≤ n → M * (n + 2) ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hp : M < 2 ^ M := Nat.lt_two_pow_self
      have hpow : (2 : ℕ) ^ (2 * M + 5) = 2 ^ M * 2 ^ M * 32 := by
        rw [show 2 * M + 5 = M + M + 5 by ring, pow_add, pow_add]
        norm_num
      rw [hpow]
      nlinarith [hp, Nat.one_le_two_pow (n := M)]
  | succ n hn ih =>
      have hnp : n < 2 ^ n := Nat.lt_two_pow_self
      have hpow : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      rw [hpow]
      have : M * (n + 1 + 2) = M * (n + 2) + M := by ring
      omega

/-- **Aux 9.3 (`eq:q-deltaU` at a width large enough for
`eq:protected-delta-min`).**

`06:515` fixes the wrapper width to `q = 2^{A_wrap L_P^2}` and `06:520--522`
leaves `A_wrap` free, fixing only that it is "chosen large enough to dominate
every protocol-independent exceptional-set bound".  This lemma discharges that
stipulation for the one demand this block makes on `q`: given the required
multiple `M` and the schedule's `L_P`, some positive `A_wrap` makes
`M . L_q(q) <= q` at `q = 2^{A_wrap L_P^2}`, since `L_q(2^n) = n + 2`.

`A_wrap := 2M + 5` works because `L_P >= 1` makes the exponent at least
`2M + 5`.  Nothing is searched and nothing is pinned: the returned width is a
closed form in the demand it has to meet. -/
theorem exists_wrapper_exponent (M LP : ℕ) (hM : 1 ≤ M) (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, 1 ≤ Awrap ∧ M * (Awrap * LP ^ 2 + 2) ≤ 2 ^ (Awrap * LP ^ 2) := by
  refine ⟨2 * M + 5, by omega, ?_⟩
  exact mul_succ_le_two_pow hM _ (Nat.le_mul_of_pos_right _ (pow_pos (by omega) 2))

/-- **Aux 9.4 (the width demand of this block, as one multiple).**

`exists_wrapper_exponent` specialized at `M = 128 B_theta s kappa`, the largest
multiple of `L_q` that either schedule-tier inhabitant below has to dominate:
`ReachableWidth` at `d_cls = 1/2` needs `128 B_theta L_q s <= q`, and the block
bundle's `eq:protected-delta-min` comparison needs `64 B_theta L_q s kappa <= q`.
Both are implied by `M L_q <= q`. -/
theorem exists_wrapper_width {θ : ℝ} (hθ : 0 < θ) (r₃ ℓ LP : ℕ) (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, 1 ≤ Awrap ∧
      128 * Btheta θ * 2 ^ r₃ * 2 ^ ℓ * (Awrap * LP ^ 2 + 2)
        ≤ 2 ^ (Awrap * LP ^ 2) := by
  have hB1 : 1 ≤ Btheta θ := one_le_Btheta hθ
  have hM1 : 1 ≤ 128 * Btheta θ * 2 ^ r₃ * 2 ^ ℓ :=
    Nat.mul_pos (Nat.mul_pos (by omega) (Nat.two_pow_pos r₃)) (Nat.two_pow_pos ℓ)
  exact exists_wrapper_exponent _ LP hM1 hLP

/-- **SCHEDULE-TIER NON-VACUITY 1: `ReachableWidth` is inhabited at the
schedule's own threshold, scale and width.**

The window `(e, d_cls) = (r_3 + ell + 4, 1/2)` is reachable at
`theta = 1/(160 Q)` -- `eq:Q-theta-choice` in the `06:539` closed form, at the
banked `Q = EntryGates.Qwidth bout deltaU` of `06:532` -- for every scale
`s = 2^{r_3}` meeting the `eq:s-choice` floor and every `kappa = 2^{ell} >= 2`,
at a width `q = 2^{A_wrap L_P^2}` of the `eq:q-deltaU` shape.

*Every value is evaluated, none is chosen.*  `theta` is the display, not a
numeral.  `r_3 >= 9` is `eq:s-choice`'s `s >= 512` (`06:112--120` at
`A_pre >= 16`, `u >= 3`, `B_s >= 1`), and `512 <= s` together with `64 | s`
(`06:394--395`) is *returned* as part of the deliverable rather than assumed
downstream.  `ell >= 1` is `09:1420`'s `kappa >= 2`, likewise returned.
`A_wrap` is produced by `exists_wrapper_exponent` from `06:520--522`.

`L_P` carries only `1 <= L_P` here; the frozen `L_P = clog_2(P_0) >= 4`
(`06:467`, `06:471`) is stronger, so the statement covers every legal `L_P` and
assumes less than the schedule provides.

*Nondegeneracy.*  `d_cls = 1/2` is interior to the frozen donor range `(0,1]`,
and the lower dyadic bound of `eq:protected-dyadic-class` is attained exactly
(`2^{r_3+ell+4} . (1/2) = 8 . 2^{r_3+ell}`) while the upper one is strict, so the
inhabitant sits on the boundary the frozen `u`-choice actually produces rather
than in the interior of both bounds.  `B_theta >= 2` at this `theta`
(`Btheta_ge_two_at_scheduleTheta`) so the poor-`u`-set cover `u(B_theta - 1)` is
non-empty.

This is the statement the round-`r2` `reachableWidth_legal_instance` claimed to
be and was not. -/
theorem reachableWidth_at_scheduleTheta {bout : ℕ} {δU : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 200)
    {r₃ ℓ LP : ℕ} (hr₃ : 9 ≤ r₃) (hℓ : 1 ≤ ℓ) (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, 1 ≤ Awrap ∧
      512 ≤ (2 ^ r₃ : ℕ) ∧ (64 : ℕ) ∣ 2 ^ r₃ ∧ 2 ≤ (2 ^ ℓ : ℕ) ∧
      2 ≤ Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) ∧
      ReachableWidth (2 ^ (Awrap * LP ^ 2)) r₃ ℓ
        (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) (r₃ + ℓ + 4) (1 / 2) := by
  have hQ : 0 < EthInapproximability.ParameterizedNP.EntryGates.Qwidth bout δU := by
    have := Qwidth_route_floor hb hδ0 hδ
    omega
  have hθ : 0 < 1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)) := scheduleTheta_pos hQ
  obtain ⟨Awrap, hA1, hAle⟩ := exists_wrapper_width hθ r₃ ℓ LP hLP
  refine ⟨Awrap, hA1, ?_, ?_, ?_, Btheta_ge_two_at_scheduleTheta hQ, ?_, ?_,
    by norm_num, by norm_num, ?_⟩
  · calc (512 : ℕ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ r₃ := Nat.pow_le_pow_right (by norm_num) hr₃
  · exact ⟨2 ^ (r₃ - 6), by rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; omega⟩
  · calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  · have heq : (2 : ℝ) ^ (r₃ + ℓ + 4) * (1 / 2) = 8 * (2 : ℝ) ^ (r₃ + ℓ) := by
      rw [show r₃ + ℓ + 4 = (r₃ + ℓ) + 4 by ring, pow_add]; ring
    rw [heq]
  · have heq : (2 : ℝ) ^ (r₃ + ℓ + 4) * (1 / 2) = 8 * (2 : ℝ) ^ (r₃ + ℓ) := by
      rw [show r₃ + ℓ + 4 = (r₃ + ℓ) + 4 by ring, pow_add]; ring
    rw [heq]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (r₃ + ℓ) := by positivity
    linarith
  · rw [Lq_two_pow (Awrap * LP ^ 2)]
    have hR : ((128 * Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)))
          * 2 ^ r₃ * 2 ^ ℓ * (Awrap * LP ^ 2 + 2) : ℕ) : ℝ)
        ≤ ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ) := by exact_mod_cast hAle
    have hqpos : (0 : ℝ) < ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hqpos]
    push_cast at hR ⊢
    have h2l : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
    have hnn : (0 : ℝ) ≤ 128
        * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ) * 2 ^ r₃
        * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2) := by positivity
    have hmono : (128
          * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ) * 2 ^ r₃
          * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2)) * 1
        ≤ (128
          * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ) * 2 ^ r₃
          * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2)) * (2 : ℝ) ^ ℓ :=
      mul_le_mul_of_nonneg_left h2l hnn
    linarith

/-- **SCHEDULE-TIER NON-VACUITY 2: the block-owned premise bundle is satisfiable
at the schedule's own threshold, scale, secondary width and wrapper width.**

The same seven-clause bundle as
`earlyProtectedClosure_block_bundle_is_consistent`, now at parameter values the
frozen displays produce.  Read in order, the conjuncts are: the
`eq:s-choice` floor `512 <= s` with `64 | s`; the `09:1420` floor `kappa >= 2`;
the `B_theta` bracket at the schedule threshold (`Btheta_bracket_at_-`
`scheduleTheta`, whose upper half is the `eq:cover-tested-endpoint` estimate and
is a function of `Q`, not a constant); the `09:1382` evaluation
`L_q(2^n) = n + 2`; `eq:stage2-structural-gates` (`06:835`) `4 t_2 <= q_2`; the
`eq:protected-delta-min` comparison `64 B_theta L_q s kappa <= q`; and the
`06:1151--1152` structural gate.

*What is free and what is evaluated.*  `bout` and `delta_U` are the public
record's own inputs and only their frozen side conditions are used
(`05:39--40`, `06:547`); `theta` is then *computed* through `EntryGates.Q0` and
`EntryGates.Qwidth`.  `r_3`, `ell`, `r_2` and `k_2` are carried as binders at
their frozen floors and gates, never as numerals.  `A_wrap` and `b_1` are
produced: `A_wrap` by `exists_wrapper_exponent` from `06:520--522`, and
`b_1 = r_3 + ell + r_2 + A_wrap L_P^2` as *a sufficient* Stage-1 row exponent for
the `06:1151--1152` gate, exhibited in closed form.  It is deliberately not
claimed to be the least such exponent: at this `b_1` the gate reduces to
`1 <= 16 B_theta L_q 2^{r_3}`, whose right side is at least `32` under
`B_theta >= 1`, `L_q >= 2`, so the exponent carries at least five bits of slack.
`b_1` is existentially bound, so nothing in the statement depends on the choice.

The frozen `q_2 >= 6144` of `eq:stage2-structural-gates` is *not* imposed here:
the bundle needs only `4 t_2 <= q_2`, and assuming more than the display the
clause comes from would be an over-strong hypothesis.  For the same reason `L_P`
carries only `1 <= L_P` where the schedule gives `>= 4`. -/
theorem earlyProtectedClosure_block_bundle_at_scheduleTheta {bout : ℕ} {δU : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 200)
    {r₃ ℓ r₂ k₂ LP : ℕ} (hr₃ : 9 ≤ r₃) (hℓ : 1 ≤ ℓ) (hLP : 1 ≤ LP)
    (hgate : k₂ + 2 ≤ r₂) :
    ∃ Awrap b₁ : ℕ, 1 ≤ Awrap ∧
      512 ≤ (2 ^ r₃ : ℕ) ∧ (64 : ℕ) ∣ 2 ^ r₃ ∧ 2 ≤ (2 ^ ℓ : ℕ) ∧
      2 ≤ Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) ∧
      Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)))
          ≤ 100 * Nat.clog 2 (160 * EntryGates.Qwidth bout δU) ∧
      Lq (2 ^ (Awrap * LP ^ 2)) = Awrap * LP ^ 2 + 2 ∧
      4 * (2 ^ k₂ : ℕ) ≤ 2 ^ r₂ ∧
      64 * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
          * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)
          ≤ ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ) ∧
      ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
            * (Lq (2 ^ (Awrap * LP ^ 2)) : ℝ) * ((2 ^ r₃ : ℕ) : ℝ)
            / ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ)) / 4 := by
  have hQ : 0 < EthInapproximability.ParameterizedNP.EntryGates.Qwidth bout δU := by
    have := Qwidth_route_floor hb hδ0 hδ
    omega
  have hθ : 0 < 1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)) := scheduleTheta_pos hQ
  obtain ⟨Awrap, hA1, hAle⟩ := exists_wrapper_width hθ r₃ ℓ LP hLP
  have hBR : (1 : ℝ) ≤ (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ) := by
    exact_mod_cast one_le_Btheta hθ
  refine ⟨Awrap, r₃ + ℓ + r₂ + Awrap * LP ^ 2, hA1, ?_, ?_, ?_,
    Btheta_ge_two_at_scheduleTheta hQ, Btheta_le_tested_at_scheduleTheta hQ,
    Lq_two_pow _, ?_, ?_, ?_⟩
  · calc (512 : ℕ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ r₃ := Nat.pow_le_pow_right (by norm_num) hr₃
  · exact ⟨2 ^ (r₃ - 6), by rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; omega⟩
  · calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  · calc 4 * (2 ^ k₂ : ℕ) = 2 ^ (k₂ + 2) := by ring
      _ ≤ 2 ^ r₂ := Nat.pow_le_pow_right (by norm_num) hgate
  · rw [Lq_two_pow]
    have hR : ((128 * Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)))
          * 2 ^ r₃ * 2 ^ ℓ * (Awrap * LP ^ 2 + 2) : ℕ) : ℝ)
        ≤ ((2 ^ (Awrap * LP ^ 2) : ℕ) : ℝ) := by exact_mod_cast hAle
    push_cast at hR ⊢
    have hkey : (128
          * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
          * 2 ^ r₃ * 2 ^ ℓ * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2))
        = 2 * (64 * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
            * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2) * 2 ^ r₃ * 2 ^ ℓ) := by ring
    rw [hkey] at hR
    have hX : (0 : ℝ) ≤ 64
        * (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
        * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2) * 2 ^ r₃ * 2 ^ ℓ := by positivity
    linarith
  · rw [Lq_two_pow]
    have hlhs : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ (r₃ + ℓ + r₂ + Awrap * LP ^ 2)
        = 1 / (2 : ℝ) ^ (Awrap * LP ^ 2) := by
      rw [pow_add (2 : ℝ) (r₃ + ℓ + r₂) (Awrap * LP ^ 2), div_mul_eq_div_div,
        div_self (by positivity : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) ≠ 0)]
    rw [hlhs]
    have hqpos : (0 : ℝ) < (2 : ℝ) ^ (Awrap * LP ^ 2) := by positivity
    push_cast
    rw [div_div, div_le_div_iff₀ hqpos (by positivity)]
    have hsr : (1 : ℝ) ≤ (2 : ℝ) ^ r₃ := one_le_pow₀ (by norm_num)
    have hA0 : (0 : ℝ) ≤ (Awrap : ℝ) * (LP : ℝ) ^ 2 := by positivity
    have hn2 : (2 : ℝ) ≤ (Awrap : ℝ) * (LP : ℝ) ^ 2 + 2 := by linarith
    have step1 : (1 : ℝ) * 2
        ≤ (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
          * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2) :=
      mul_le_mul hBR hn2 (by norm_num) (by linarith)
    have step2 : ((Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
          * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2)) * 1
        ≤ ((Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
          * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2)) * 2 ^ r₃ :=
      mul_le_mul_of_nonneg_left hsr (by positivity)
    have hprod : (2 : ℝ)
        ≤ (Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
          * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2) * 2 ^ r₃ := by linarith
    have hfin : (2 : ℝ) * (2 : ℝ) ^ (Awrap * LP ^ 2)
        ≤ ((Btheta (1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ))) : ℝ)
            * ((Awrap : ℝ) * (LP : ℝ) ^ 2 + 2) * 2 ^ r₃) * (2 : ℝ) ^ (Awrap * LP ^ 2) :=
      mul_le_mul_of_nonneg_right hprod (le_of_lt hqpos)
    linarith

/-! ### Round-`r3` aux battery and tier separation

Five general sanity results about the machinery added this round, plus the
theorem that makes the tier separation itself kernel-visible. -/

/-- **Aux battery 1 (`09:1378--1383`, general monotonicity of the least
search).**  The cover exponent is antitone in the retained density: a *smaller*
`theta` forces a *larger* `B_theta`, because `rho_0^{B} < theta_1 <= theta_2`
makes every exponent admissible for `theta_1` admissible for `theta_2`.

This is the structural fact behind `Btheta_le_tested_at_scheduleTheta` being a
function of `Q` rather than a constant, and hence behind the round-`r2` upper
bound `B_theta <= 1100` being a statement about one density only.  General: no
schedule data enters. -/
theorem Btheta_antitone {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h : θ₁ ≤ θ₂) :
    Btheta θ₂ ≤ Btheta θ₁ :=
  coverExponent_le (one_le_Btheta h1) (lt_of_lt_of_le (Btheta_spec h1).2 h)

/-- **Aux battery 2 (the same monotonicity in the schedule width).**  A wider
bridge interlace `Q` is a smaller threshold `theta = 1/(160 Q)` and so a larger
`B_theta`.  Composing `Btheta_antitone` with the closed form of `06:539`. -/
theorem Btheta_mono_in_scheduleWidth {Q₁ Q₂ : ℕ} (h1 : 0 < Q₁) (h : Q₁ ≤ Q₂) :
    Btheta (1 / (160 * (Q₁ : ℝ))) ≤ Btheta (1 / (160 * (Q₂ : ℝ))) := by
  have h1R : (0 : ℝ) < (Q₁ : ℝ) := by exact_mod_cast h1
  have hR : (Q₁ : ℝ) ≤ (Q₂ : ℝ) := by exact_mod_cast h
  have h2R : (0 : ℝ) < (Q₂ : ℝ) := lt_of_lt_of_le h1R hR
  refine Btheta_antitone (scheduleTheta_pos (Q := Q₂) (by omega)) ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- **Aux battery 3 (`Lq_two_pow` is not vacuous at the widths this block
uses).**  `L_q >= 2` at every power-of-two width, so the dyadic-class count the
extraction chain divides by is never `0` or `1`.  General in `n`. -/
theorem two_le_Lq_two_pow (n : ℕ) : 2 ≤ Lq (2 ^ n) := by
  rw [Lq_two_pow]; omega

/-- **Statement pole (the width threshold of `mul_succ_le_two_pow` is real).**

The conclusion is false at `n = 0` for every `M >= 1`, so the hypothesis
`2M + 5 <= n` is doing work and the lemma is not a disguised triviality.  This
is also why `exists_wrapper_exponent` must *produce* an `A_wrap` rather than
return the trivial one. -/
theorem mul_succ_le_two_pow_fails_at_zero {M : ℕ} (hM : 1 ≤ M) :
    ¬ (M * (0 + 2) ≤ 2 ^ 0) := by
  simp only [pow_zero]
  omega

/-- **Statement pole (`exists_wrapper_exponent`'s deliverable is not met by the
trivial witness).**

`A_wrap := 0` -- the degenerate "width" `q = 2^0 = 1` -- refutes the produced
inequality for every `M >= 1`, since it asks `2M <= 1`.  So the existential
genuinely selects a width, and `06:520--522`'s "chosen large enough" is
discharged rather than trivially satisfied. -/
theorem exists_wrapper_exponent_fails_at_zero {M LP : ℕ} (hM : 1 ≤ M) :
    ¬ (M * (0 * LP ^ 2 + 2) ≤ 2 ^ (0 * LP ^ 2)) := by
  simp only [Nat.zero_mul, pow_zero]
  omega

/-- **`24` is not a wrapper exponent (`eq:q-deltaU`, `06:467`, `06:471`).**

`q = 2^{A_wrap L_P^2}` with `L_P = clog_2(P_0)` and `P_0 >= 16`, so `L_P >= 4`
and, since `05:411` requires `A_wrap > 0`, the reachable exponents are
`A_wrap L_P^2 in {16, 25, 32, 36, ...}`.
`24` is not among them: at `L_P = 4` it would need `16 A_wrap = 24`, and at
`L_P >= 5` every positive multiple already exceeds `24`.

This is the third of the three round-`r2` numerals, refuted in the kernel. -/
theorem wrapper_exponent_ne_twentyfour {Awrap LP : ℕ} (hLP : 4 ≤ LP) :
    Awrap * LP ^ 2 ≠ 24 := by
  intro h
  rcases Nat.lt_or_ge LP 5 with h5 | h5
  · have hLP4 : LP = 4 := by omega
    subst hLP4
    norm_num at h
    omega
  · have hsq : 25 ≤ LP ^ 2 := by nlinarith
    rcases Nat.eq_zero_or_pos Awrap with h0 | h0
    · subst h0; simp at h
    · have : 25 ≤ Awrap * LP ^ 2 :=
        le_trans hsq (Nat.le_mul_of_pos_left _ h0)
      omega

/-- **TIER SEPARATION (the round-`r3` finding, made kernel-visible).**

The three numerals rounds `r1`/`r2` called legal are refuted by the defining
displays, not merely unsupported by them:

* `theta`: the route's own threshold `1/(160 Q)` is **strictly below** the audit
  density `1/20480`, because `Q0_route_floor` and `Qwidth_route_floor` force
  `Q >= 2^14` and hence `theta <= 1/2621440`.  In particular the floor-tier
  probes `Btheta_floorTier_ge_two`, `Btheta_floorTier_le`,
  `reachableWidth_floorTier_instance` and
  `earlyProtectedClosure_block_bundle_is_consistent` stand at a density the
  schedule never produces;
* `s`: the probe scale `s = 2^2 = 4` is strictly below the `eq:s-choice` floor
  `512` (`06:112--120` with `06:394--395`);
* `q`: the exponent `24` is refuted by `wrapper_exponent_ne_twentyfour`.

A separation theorem is the right shape here: it cannot be satisfied by
weakening a bound, and it fails immediately if a future round moves the route
floor back down. -/
theorem floorTier_values_are_refuted_by_the_schedule {bout : ℕ} {δU : ℝ}
    (hb : 1 ≤ bout) (hδ0 : 0 < δU) (hδ : δU ≤ 1 / 200) :
    1 / (160 * ((EntryGates.Qwidth bout δU : ℕ) : ℝ)) < 1 / 20480 ∧
      (2 ^ 2 : ℕ) < 512 ∧
      ∀ Awrap LP : ℕ, 4 ≤ LP → Awrap * LP ^ 2 ≠ 24 := by
  refine ⟨?_, by norm_num, fun _ _ h => wrapper_exponent_ne_twentyfour h⟩
  have := scheduleTheta_route_le hb hδ0 hδ
  have hlt : (1 : ℝ) / 2621440 < 1 / 20480 := by norm_num
  linarith

/-- **HYPOTHESIS CONSISTENCY of the schedule tier.**

The premise bundle of `reachableWidth_at_scheduleTheta` and
`earlyProtectedClosure_block_bundle_at_scheduleTheta` -- `b_out >= 1`
(`05:39--40`), `0 < delta_U <= 1/200` (`06:547`), `r_3 >= 9`
(`eq:s-choice`), `ell >= 1` (`09:1420`), `L_P >= 1` (`06:471`), and
`k_2 + 2 <= r_2` (`eq:stage2-structural-gates`) -- is discharged at a concrete
tuple, so the two schedule-tier inhabitants are not vacuously true of an
inconsistent hypothesis set.  The tuple used is `b_out = 1`,
`delta_U = 1/200`, `r_3 = 9` (`s = 512`, the `eq:s-choice` floor), `ell = 1`
(`kappa = 2`), `L_P = 4` (`P_0 = 16`, the `06:467` floor), `k_2 = 4`
(`16 | t_2`), `r_2 = 6`.

It reads no schedule parameter out of that tuple: the returned `theta`, `q` and
`A_wrap` remain the evaluated ones. -/
theorem scheduleTier_hypotheses_are_satisfiable :
    ∃ Awrap : ℕ, 1 ≤ Awrap ∧
      512 ≤ (2 ^ 9 : ℕ) ∧ (64 : ℕ) ∣ 2 ^ 9 ∧ 2 ≤ (2 ^ 1 : ℕ) ∧
      2 ≤ Btheta (1 / (160 * ((EntryGates.Qwidth 1 (1 / 200) : ℕ) : ℝ))) ∧
      ReachableWidth (2 ^ (Awrap * 4 ^ 2)) 9 1
        (1 / (160 * ((EntryGates.Qwidth 1 (1 / 200) : ℕ) : ℝ))) (9 + 1 + 4) (1 / 2) :=
  reachableWidth_at_scheduleTheta (bout := 1) (δU := 1 / 200) (by norm_num)
    (by norm_num) (by norm_num) (r₃ := 9) (ℓ := 1) (LP := 4)
    (by norm_num) (by norm_num) (by norm_num)

/-- **Statement pole 1 (`templateCoordinateExtraction`'s deliverable is not the
trivial witness).**  The frozen conclusion is existential in the coordinate set
`J`, and the trivial candidate -- an empty all-template projection -- fails it:
with `rho > 0` and `|Y_T| > 0` the left-hand side is strictly positive while an
empty projection makes the right-hand side `0`.  So the lemma genuinely produces
patterns and is not satisfied by vacuous data. -/
theorem templateCoordinateExtraction_trivial_witness_fails
    {u : ℕ} {ρ : ℝ} {c : ℕ} (hρ : 0 < ρ) (hc : 0 < c) :
    ¬ (ρ * (c : ℝ) ^ (u / 2) ≤ 2 ^ (u + 1) * ((0 : ℕ) : ℝ)) := by
  have hcR : (0:ℝ) < (c : ℝ) := by exact_mod_cast hc
  have : (0:ℝ) < ρ * (c : ℝ) ^ (u / 2) := by positivity
  simp only [Nat.cast_zero, mul_zero]
  linarith

/-- **Statement pole 2 (`selectedColumnDensity` does not allow the empty
witness).**  Its deliverable is the entering density `h = rho_1 2^{-u-1}` of row
(iii), which is **strictly positive** at every width; so a selected restriction
with an empty all-template projection refutes the conclusion, and the theorem
genuinely produces columns.  This is also why `column_density` is a live field of
`ExtensionCallThree`: the degenerate `h = 0` is excluded. -/
theorem selectedColumnDensity_trivial_witness_fails {e c : ℕ} (hc : 0 < c) :
    ¬ (callThreeH e * (c : ℝ) ^ (2 ^ e / 2) ≤ ((0 : ℕ) : ℝ)) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hpos : (0 : ℝ) < callThreeH e * (c : ℝ) ^ (2 ^ e / 2) := by
    have := callThreeH_pos e
    positivity
  simp only [Nat.cast_zero]
  linarith

/-! ### Round-`r2` REVISE-A regression probes

Both round-`r1` seat countermodels are preserved here as kernel-visible probes:
each is the exact witness that discharged a round-`r1` clause, and each is now
*refuted* against the repaired clause.  If a future round loosens either clause
back, these two theorems become unprovable. -/

/-- **Regression probe A0 (the counting core of both seat countermodels).**

The relabelled parent `ambientRelabel J eJ S` never has more elements than `S`
itself -- it is an image of an image.  So whenever `S` is smaller than the whole
ambient cube, the full cube is **not** contained in it.  General in the alphabet,
in `q`, in `u`, in `S`, in `J` and in the relabelling. -/
theorem ambientRelabel_card_le {Y : Type*} [DecidableEq Y] {q u : ℕ}
    (S : Finset (Fin q → Y)) (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J) :
    (ambientRelabel J eJ S).card ≤ S.card := by
  classical
  refine le_trans (Finset.card_image_le) ?_
  exact Finset.card_image_le

/-- **Regression probe A1 (the round-`r1` `P := Finset.univ` countermodel, now
refuted).**

The round-`r1` deliverable existentially quantified a bare `P` with no tie to
`S`, and `P := Finset.univ` discharged it: the all-template projection of the
whole cube on any `J'` is all of `Y_T^{J'}`, whose count meets
`callThreeH e |Y_T|^{u/2}` because `callThreeH e <= 1`.  The repaired deliverable
carries the child's provenance `P subseteq ambientRelabel J eJ S`, and `univ`
fails it at every retained set smaller than the ambient cube -- which is the
generic case, since `09:1463`'s parent has density `rho_0 < 1`. -/
theorem selectedColumnDensity_univ_child_pole {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q u : ℕ} (S : Finset (Fin q → Y)) (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J)
    (hS : S.card < Fintype.card (Fin u → Y)) :
    ¬ ((Finset.univ : Finset (Fin u → Y)) ⊆ ambientRelabel J eJ S) := by
  intro hsub
  have h1 : (Finset.univ : Finset (Fin u → Y)).card ≤ (ambientRelabel J eJ S).card :=
    Finset.card_le_card hsub
  rw [Finset.card_univ] at h1
  have h2 : (ambientRelabel J eJ S).card ≤ S.card := ambientRelabel_card_le S J eJ
  omega

/-- **Regression probe A2 (the round-`r1` `P_0 := univ`, `P_1 := empty`
countermodel for `hQuery`, now refuted).**

The round-`r1` `hQuery` asked only that two counts dominate the parent's
projection count, and `P_0 := Finset.univ`, `P_1 := empty` discharged it for
**every** `S` and every `J`, so nothing tied the two families to
`projSet J S` and the `rho_0 -> rho_1` halving was a statement about unrelated
data.  The repaired binder asks for a partition of the relabelled parent, and
that same pair fails it at every retained set smaller than the ambient cube. -/
theorem bobQuery_trivial_split_fails {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q u : ℕ} (S : Finset (Fin q → Y)) (J : Finset (Fin q)) (eJ : Fin u ≃ ↥J)
    (hS : S.card < Fintype.card (Fin u → Y)) :
    ¬ ((Finset.univ : Finset (Fin u → Y)) ∪ (∅ : Finset (Fin u → Y))
        = ambientRelabel J eJ S) := by
  intro hEq
  refine selectedColumnDensity_univ_child_pole S J eJ hS ?_
  rw [← hEq]
  exact Finset.subset_union_left

/-- **Regression probe A3 (the two probes bite at a concrete instance).**

Probes A1 and A2 are only informative if their hypothesis
`|S| < |Y|^u` is met somewhere the block actually reaches.  It is met at the
smallest nondegenerate instance: a two-letter alphabet, `u = 4` (the least width
`lem:template-coordinate-extraction` admits, since `4 | u`), and a singleton
retained set.  `1 < 16`, so both probes fire. -/
theorem selectedColumnDensity_poles_are_live :
    ({(fun _ => true : Fin 4 → Bool)} : Finset (Fin 4 → Bool)).card
      < Fintype.card (Fin 4 → Bool) := by
  rw [Fintype.card_fun]
  simp

/-- **Statement pole 3 (the endpoint is not the empty bound).**  The frozen
conclusion `C + log_2 kappa - 1 <= comp(child)` is nontrivial: the target
`C + log_2 kappa` is at least `2` at every legal `ell >= 1`, so a `child` of
complexity `0` refutes it.  Any restatement that let the target collapse to `0`
would be exactly this triviality. -/
theorem earlyProtectedClosure_is_not_trivial (bcap r₂ r₃ ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ¬ (TerminalTwoStream.terminalTarget bcap r₂ r₃ + ℓ ≤ 0 + 1) := by
  have := TerminalTwoStream.terminalTarget_pos bcap r₂ r₃
  omega

/-- **Statement pole 4 (`exists_width_u` needs the class heaviness).**  Dropping
`hheavy` makes the last conclusion false: at `V_card = 0` no `e` satisfies
`2 . 2^e B <= 0` for `B >= 1`, so the class-size output is genuinely carried by
the dyadic-class estimate and not by the width construction alone. -/
theorem width_u_needs_heaviness {e B : ℕ} (hB : 1 ≤ B) :
    ¬ (2 * ((2 : ℝ) ^ e * B) ≤ 0) := by
  have hpow : (0:ℝ) < (2:ℝ) ^ e := by positivity
  have hBR : (1:ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  nlinarith

/-- **Statement pole 5 (`2 L_q` really is needed).**  `L_q` is not cosmetic: the
pigeonhole in `exists_heavy_dyadic_class` divides by `L_q`, and the frozen
`ceil(log_2(2q)) + 1` is exactly large enough for the surviving donors' class
indices.  Recorded here as the inequality the proof consumes, at a small
concrete `q`: this is an arithmetic probe of the frozen formula, and `q = 5` is
not a schedule width (`eq:q-deltaU` gives `q = 2^{A_wrap L_P^2}`). -/
theorem Lq_bound_is_live : 2 * 5 ≤ 2 ^ Lq 5 ∧ Lq 5 = 5 := by
  constructor
  · exact two_mul_le_two_pow_Lq 5
  · rfl

/-- **Statement pole 6 (the halving is where `mu_P` lives).**  Dropping `mu_P`
from `eq:protected-early-threshold` would leave `D_mass` short by the factor
`128 mu_P` and the whole chain would enter at the wrong constant.  Recorded as
the exact arithmetic identity the halving uses: `128 mu_P / (2 mu_P) = 64`. -/
theorem muP_cancels_in_halving : 128 * muP / (2 * muP) = 64 := by
  have h : muP ≠ 0 := ne_of_gt muP_pos
  field_simp
  norm_num

/-- **Non-vacuity 5 (the dyadic class is not empty of content).**  The class
specification `d_cls/2 < d_j <= d_cls` is satisfiable at a donor weight inside
the frozen `(0,1]` range,
and it pins `d_j` to a genuine dyadic window rather than to a point or to the
empty range. -/
theorem classIndex_nondegenerate :
    classWidth (classIndex ((3:ℝ) / 4)) = 1 ∧
      classWidth (classIndex ((3:ℝ) / 8)) = 1 / 2 := by
  constructor
  · have h : classIndex ((3:ℝ) / 4) = 0 := by
      rw [classIndex]
      norm_num
    rw [h, classWidth]; norm_num
  · have h : classIndex ((3:ℝ) / 8) = 1 := by
      rw [classIndex]
      norm_num
    rw [h, classWidth]; norm_num

/-! ## Section 10  The aux-lemma battery

General sanity properties of the new definitions, proved. -/

/-- **Aux battery 1 (inhabitation with the hardest field).**  `ExtensionCallThree`
is inhabited *and* its two hardest fields -- the structural-gate row comparison
`K 2^{-b_1} <= d_cls/4` and the strictly positive entering density `h` -- are
genuinely satisfied there, not vacuous.

FLOOR TIER: the values are `extensionCallThree_floorTier_instance`'s, i.e. the
`04:389` scale **floor** `s = 2^2 = 4` rather than the forbidden `s = 1`, and
`eq:s-choice` (`06:112--120`) refutes them as schedule values.  No legality is
claimed; what is claimed is that the two fields are not vacuous. -/
theorem extensionCallThree_row_gate_is_live :
    (Kint (2 ^ 2) 2 (2 ^ 13) : ℝ) / 2 ^ 40 ≤ (1 / 2 : ℝ) / 4 ∧ 0 < callThreeH 7 := by
  refine ⟨?_, callThreeH_pos 7⟩
  rw [Kint]; norm_num

/-- **Aux battery 2 (monotonicity of the dyadic-class count).**  `L_q` is monotone
in `q`: a wider outer interlace never needs fewer dyadic classes.  General. -/
theorem Lq_mono {q q' : ℕ} (h : q ≤ q') : Lq q ≤ Lq q' := by
  unfold Lq
  exact Nat.succ_le_succ (Nat.clog_mono_right 2 (by omega))

/-- **Aux battery 3 (round trip on the class index).**  For every dyadic weight
`2^{-k}` the class index recovers `k` exactly, so `classWidth` and `classIndex`
are inverse on the frozen representatives.  General. -/
theorem classIndex_classWidth (k : ℕ) : classIndex (classWidth k) = k := by
  rw [classIndex, classWidth]
  have h : (1 : ℝ) / (1 / 2 ^ k) = 2 ^ k := by
    field_simp
  rw [h]
  have hfloor : ⌊(2 : ℝ) ^ k⌋₊ = 2 ^ k := by
    rw [show ((2 : ℝ)) ^ k = ((2 ^ k : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  rw [hfloor]
  exact Nat.log_pow (by norm_num) k

/-- **Aux battery 4 (identity on the frozen block count).**  `K_int` is
multiplicative in its three widths and positive at positive widths, so the frozen
`K_int = s kappa q_2` never degenerates to `0`.  General. -/
theorem Kint_pos {s κ q₂ : ℕ} (hs : 0 < s) (hκ : 0 < κ) (hq₂ : 0 < q₂) :
    0 < Kint s κ q₂ := by
  rw [Kint]; positivity

/-- **Aux battery 5 (monotonicity of the reverse-Markov count).**  Raising the
per-fibre threshold `b` can only shrink the counted set, which is the direction
`09:1476--1479` uses when it trades `d_cls/2` for `d_cls/4`.  General. -/
theorem card_ge_of_sum_ge_mono {ι : Type*} (T : Finset ι) (f : ι → ℝ)
    {b b' : ℝ} (h : b ≤ b') :
    (T.filter (fun i => b' ≤ f i)).card ≤ (T.filter (fun i => b ≤ f i)).card := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  have hmem := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hmem.1, le_trans h hmem.2⟩

/-- **Aux battery 6 (the template extraction really uses `4 | u`).**  At `4 | u`
the two frozen widths agree: `u/2` template coordinates are exactly half of `u`,
and `u - u/2 = u/2` is what makes the completion count `|Y|^{u/2}`.  General. -/
theorem u_half_split {u : ℕ} (hu : 4 ∣ u) : u / 2 + u / 2 = u ∧ u - u / 2 = u / 2 := by
  obtain ⟨c, hc⟩ := hu
  subst hc
  omega

/-- **Aux battery 7 (`h` is antitone in the width).**  `h = rho_1 2^{-u-1}` shrinks
as the width `u = 2^e` grows, which is why `eq:all-extension-gates` must be
verified at the *largest* reached width and why `bounded_of_reachableWidth` is
what makes the uniformly-quantified gates meaningful.  General. -/
theorem callThreeH_antitone {e e' : ℕ} (h : e ≤ e') : callThreeH e' ≤ callThreeH e := by
  unfold callThreeH
  have hpow : (2 : ℝ) ^ (2 ^ e + 1) ≤ (2 : ℝ) ^ (2 ^ e' + 1) := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    have : (2 : ℕ) ^ e ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) h
    omega
  have h0 : (0 : ℝ) < (2 : ℝ) ^ (2 ^ e + 1) := by positivity
  exact div_le_div_of_nonneg_left (le_of_lt rhoOne_pos) h0 hpow

/-! ## Section 11  Round `r4`: the `hLocEx` shape separation, kernel-checked

The round-`r4` repair is a change of *shape*, and a green build sees no shape.
What follows makes the separation itself checkable: the round-`r3` shape is
**refuted** (it bounds an object nothing in its antecedent mentions), and the
round-`r4` shape is **satisfiable** at both an empty and a total restriction
datum, so the repair neither keeps the over-reach nor buys consistency by
becoming vacuous.

The refutation is the direction record of the banked
`MassRedistributionEntry.constructionPath_composition_is_refuted_at_a_reachable_-`
`width`, restated here **protocol-free**: no `RoutedSystem`, no first-Bob node
and no `Protocol.cost` occur, so what is exhibited is a property of the binder
alone and not of the wrapper's protocol layer. -/

section ShapeSeparation

/-- **REGRESSION POLE (the round-`r3` shape, refuted).**

*What is proved.*  Assume the round-`r3` `hLocEx` -- whose `A:138--141` clauses
were three inequalities on the outer parameters `selCard`, `rowsPerBlock`,
`colDens`, with the concluded object `child` fixed **outside** the quantifier --
together with the mass-free binders of the closure (`hGate`, `hBlocks`, `hrows`,
the analytic side of the endpoint) and one reachable width.  Then
`B_cap + log_2 K_int <= memCost child` for a `child` that no antecedent mentions:
`extensionCallThree_of_width` builds the call record from the width alone, so the
binder fires without the protected-mass threshold ever being used.

*Why that is a defect and not a feature.*  `A:138` says "every restriction of
`Mhat` with exactly `r' p_t` represented outer blocks ... has communication
complexity at least `H + log_2(r't)`".  The subject of the frozen quantifier is
the restriction; the round-`r3` binder replaced it by an object supplied by the
caller, so the *assumed* implication was stronger than the inherited corollary.
`09:1503--1504` is explicit that the endpoint is delivered at "the **selected**
Bob child", i.e. at an object the selection produces.

General in the matrix carriers, the cost carrier, the width and every schedule
parameter. -/
theorem oldShapeLocEx_forces_an_untied_object
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    {Mem : Type*} (memCost : Mem → ℕ) (child : Mem)
    {q k₂ b₁ r₂ r₃ ℓ bcap tcert selCard rowsPerBlock e : ℕ}
    {θ x epsProd dcls : ℝ}
    (hℓ : 1 ≤ ℓ) (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂) (hbcap : 2 ≤ bcap)
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hreach : ReachableWidth q r₃ ℓ θ e dcls)
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rw)
    (hbase : bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5))
    (htcert : tcert ≤ 2 ^ k₂)
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    (hE1 : ∀ (e R : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls → R + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd))
    (hE2 : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    (hrows : ⌈((2 : ℝ) ^ (r₃ + ℓ + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsPerBlock)
    (hLocExOld : ∀ (e R Rloc : ℕ) (dcls colDens : ℝ),
        ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
        1 ≤ Fintype.card Rw → 2 ≤ bcap →
        0 < x → x ≤ 1 →
        bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
        tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R → (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callThreeH e → callThreeH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsPerBlock →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ memCost child) :
    bcap + (r₃ + ℓ + r₂) ≤ memCost child := by
  obtain ⟨hlow, hhigh, hdpos, hd1, hdmin⟩ := hreach
  have hGate' : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁ ≤ dcls / 4 :=
    le_trans hGate (by linarith [hdmin])
  have hcol : callThreeH e / 2 ^ (0 : ℕ) ≤ callThreeH e := by rw [pow_zero, div_one]
  have hcall := extensionCallThree_of_width (T := k₂) (b₁ := b₁) (e := e) (r₂ := r₂)
    (r₃ := r₃) (ℓ := ℓ) (dcls := dcls) (colDens := callThreeH e)
    hk₂ hk₂le hℓ hd1 hlow hhigh hGate' hcol
  have he4 : 4 ≤ e := hcall.four_le_e
  have hcastu : (((2 ^ e : ℕ)) : ℝ) = (2 : ℝ) ^ e := by push_cast; ring
  have hud : 8 * (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)) ≤ (((2 ^ e : ℕ)) : ℝ) * dcls := by
    have hc : (((2 ^ r₃ : ℕ) : ℝ) * ((2 ^ ℓ : ℕ) : ℝ)) = (2 : ℝ) ^ (r₃ + ℓ) := by
      push_cast; rw [pow_add]
    rw [hc, hcastu]
    exact hlow
  have hK : ((Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) : ℕ) : ℝ) ≤ (selCard : ℝ) := by
    have hb := representedBlocks_ge (s := 2 ^ r₃) (κ := 2 ^ ℓ) (q₂ := 2 ^ r₂)
      (u := 2 ^ e) (dcls := dcls) (perDonor := dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4)
      (dvd_pow_self 2 (by omega)) hud (le_refl _)
    exact le_trans hb (hBlocks e dcls ⟨hlow, hhigh, hdpos, hd1, hdmin⟩)
  have hKd : Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) = 2 ^ (r₃ + ℓ + r₂) := Kint_dyadic r₂ r₃ ℓ
  have hKnn : (0 : ℝ) ≤ ((Kint (2 ^ r₃) (2 ^ ℓ) (2 ^ r₂) : ℕ) : ℝ) := by positivity
  have hcount : 9 * ((2 ^ ((r₃ + ℓ + r₂ - k₂) + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) := by
    have hexp : (r₃ + ℓ + r₂ - k₂) + k₂ = r₃ + ℓ + r₂ := by omega
    rw [hexp, ← hKd]
    linarith [hK, hKnn]
  have hend := hLocExOld e ((e - 1) + r₂ - k₂) (r₃ + ℓ + r₂ - k₂) dcls (callThreeH e)
    hcall hMne hbcap hx0 hx1 hbase htcert hk₂ htx
    Nat.one_le_two_pow hcall.r'_le_r (pow_add 2 _ k₂).symm heps0 heps1
    (callThreeH_pos e) (callThreeH_le_one e)
    (hE1 e ((e - 1) + r₂ - k₂) dcls ⟨hlow, hhigh, hdpos, hd1, hdmin⟩ hcall.ambient_exponent)
    (hE2 e dcls ⟨hlow, hhigh, hdpos, hd1, hdmin⟩)
    hcall.selected_count hcount hrows hcall.column_density
  have hcap : (r₃ + ℓ + r₂ - k₂) + k₂ = r₃ + ℓ + r₂ := hcall.capacity_exponent
  omega

/-- **REGRESSION POLE, the inconsistency itself.**

The immediate corollary of the previous theorem: the round-`r3` binder, conjoined
with **any** budget on the very object it silently bounds, is inconsistent -- and
the protected-mass threshold `eq:protected-early-threshold` never enters.  This
is the protocol-free core of the banked `MassRedistributionEntry` refutation, and
it is what the round-`r4` shape must, and does, escape. -/
theorem oldShapeLocEx_and_a_child_budget_are_inconsistent
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    {Mem : Type*} (memCost : Mem → ℕ) (child : Mem)
    {q k₂ b₁ r₂ r₃ ℓ bcap tcert selCard rowsPerBlock e : ℕ}
    {θ x epsProd dcls : ℝ}
    (hℓ : 1 ≤ ℓ) (hk₂ : 4 ≤ k₂) (hk₂le : k₂ ≤ r₃ + ℓ + r₂) (hbcap : 2 ≤ bcap)
    (hGate : ((2 : ℝ) ^ (r₃ + ℓ + r₂)) / 2 ^ b₁
        ≤ (64 * (Btheta θ : ℝ) * (Lq q : ℝ) * ((2 ^ r₃ : ℕ) : ℝ) / q) / 4)
    (hreach : ReachableWidth q r₃ ℓ θ e dcls)
    (hBlocks : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        ((2 ^ e / 2 : ℕ) : ℝ) * (dcls * ((2 ^ r₂ : ℕ) : ℝ) / 4) ≤ (selCard : ℝ))
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : ((2 : ℝ) ^ k₂) * x ≤ 1)
    (hMne : 1 ≤ Fintype.card Rw)
    (hbase : bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5))
    (htcert : tcert ≤ 2 ^ k₂)
    (heps0 : 0 < epsProd) (heps1 : epsProd < 1)
    (hE1 : ∀ (e R : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls → R + k₂ = (e - 1) + r₂ →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd))
    (hE2 : ∀ (e : ℕ) (dcls : ℝ), ReachableWidth q r₃ ℓ θ e dcls →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd))
    (hrows : ⌈((2 : ℝ) ^ (r₃ + ℓ + r₂ - k₂)) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsPerBlock)
    (hLocExOld : ∀ (e R Rloc : ℕ) (dcls colDens : ℝ),
        ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
        1 ≤ Fintype.card Rw → 2 ≤ bcap →
        0 < x → x ≤ 1 →
        bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
        tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
        0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R → (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
        0 < epsProd → epsProd < 1 →
        0 < callThreeH e → callThreeH e ≤ 1 →
        (3 / 5 : ℝ) ^ (2 ^ k₂)
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
        HardSeedFacade.hardSeedColumnDensity k₂
          ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
        (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
        9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
        ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsPerBlock →
        callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
        bcap + (Rloc + k₂) ≤ memCost child)
    (hbudget : memCost child < bcap + (r₃ + ℓ + r₂)) : False := by
  have := oldShapeLocEx_forces_an_untied_object Mmat memCost child hℓ hk₂ hk₂le hbcap
    hGate hreach hBlocks hx0 hx1 htx hMne hbase htcert heps0 heps1 hE1 hE2 hrows hLocExOld
  omega

/-- **The round-`r4` shape escapes the pole: satisfiable at the empty datum.**

At the restriction datum that holds of nothing, the re-shaped binder is
**provable outright, at every cost function** -- in particular at a `memCost`
below the endpoint, which the previous two theorems show the round-`r3` binder
can never tolerate.  So the added `A:138` antecedent is exactly what removed the
over-reach: the binder now says nothing whatever about objects that are not
restrictions of `Mhat`.

This is a statement pole and claims **no legality**: `fun _ _ _ _ => False` is
not the frozen datum, and no parameter value may be read out of it.  What it
certifies is a property of the *shape*.

General in the matrix carriers, the cost carrier, the cost function and every
schedule parameter. -/
theorem reshapedLocEx_at_the_empty_datum
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    {Mem : Type*} (memCost : Mem → ℕ)
    {k₂ b₁ r₂ r₃ ℓ bcap tcert selCard : ℕ} {x epsProd : ℝ} :
    ∀ (e R Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ) (w : Mem),
      ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
      1 ≤ Fintype.card Rw → 2 ≤ bcap →
      0 < x → x ≤ 1 →
      bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
      tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
      0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R → (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
      0 < epsProd → epsProd < 1 →
      0 < callThreeH e → callThreeH e ≤ 1 →
      (3 / 5 : ℝ) ^ (2 ^ k₂)
        ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
      HardSeedFacade.hardSeedColumnDensity k₂
        ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
      (fun (_ : Mem) (_ _ : ℕ) (_ : ℝ) => False) w blocks rowsEach colDens →
      (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
      blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
      9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
      ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsEach →
      callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
      bcap + (Rloc + k₂) ≤ memCost w := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdatum _ _ _ _ _
  exact hdatum.elim

/-- **And satisfiable at the total datum, so the escape is not vacuity.**

At the datum that holds of everything -- the *worst* case for the repair, since
then the added `A:138` antecedent excludes nothing -- the re-shaped binder is
still inhabited, at the cost function pinned by the call record itself: the
record's `capacity_exponent` (`D:752`) forces `R_loc + T = r_3 + ell + r_2`, so
the frozen endpoint `B_cap + log_2 K_int` is a *fixed* number and
`memCost = fun _ => B_cap + (r_3 + ell + r_2)` meets it.

Together with `reshapedLocEx_at_the_empty_datum` this is the non-vacuity half of
the separation: the round-`r4` binder is satisfiable whether or not the datum is
inhabited, so the repair did not buy consistency by making the hypothesis
unsatisfiable.  BEYOND-PAPER: both datum choices audit our encoding, not the
frozen `Mhat`. -/
theorem reshapedLocEx_at_the_total_datum
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Mmat : Rw → Cl → Bool)
    {Mem : Type*} {k₂ b₁ r₂ r₃ ℓ bcap tcert selCard : ℕ} {x epsProd : ℝ} :
    ∀ (e R Rloc blocks rowsEach : ℕ) (dcls colDens : ℝ) (w : Mem),
      ExtensionCallThree k₂ R Rloc b₁ e r₂ r₃ ℓ dcls colDens →
      1 ≤ Fintype.card Rw → 2 ≤ bcap →
      0 < x → x ≤ 1 →
      bcap ≤ NPCC.LambdaGE Mmat 1 x (3 / 5) →
      tcert ≤ 2 ^ k₂ → 4 ≤ k₂ → ((2 : ℝ) ^ k₂) * x ≤ 1 →
      0 < (2 : ℕ) ^ Rloc → (2 : ℕ) ^ Rloc ≤ 2 ^ R → (2 : ℕ) ^ R * 2 ^ k₂ = 2 ^ (R + k₂) →
      0 < epsProd → epsProd < 1 →
      0 < callThreeH e → callThreeH e ≤ 1 →
      (3 / 5 : ℝ) ^ (2 ^ k₂)
        ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + ((R : ℝ) + k₂)))) / (1 + epsProd) →
      HardSeedFacade.hardSeedColumnDensity k₂
        ≤ (callThreeH e * (2 : ℝ) ^ (-((bcap : ℝ) + k₂))) / (1 + epsProd) →
      (fun (_ : Mem) (_ _ : ℕ) (_ : ℝ) => True) w blocks rowsEach colDens →
      (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) = 9 * 2 ^ (Rloc + k₂) / 16 →
      blocks = (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) →
      9 * ((2 ^ (Rloc + k₂) : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
      ⌈((2 : ℝ) ^ Rloc) * 2 ^ k₂ * x * (Fintype.card Rw)⌉₊ ≤ rowsEach →
      callThreeH e / 2 ^ (0 : ℕ) ≤ colDens →
      bcap + (Rloc + k₂) ≤ (fun _ : Mem => bcap + (r₃ + ℓ + r₂)) w := by
  intro _ _ Rloc _ _ _ _ _ hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hcap : Rloc + k₂ = r₃ + ℓ + r₂ := hcall.capacity_exponent
  have hgoal : bcap + (Rloc + k₂) = bcap + (r₃ + ℓ + r₂) := by omega
  exact le_of_eq hgoal

/-- **Aux (the frozen selected count is nondegenerate).**

`r' p_t = 2^{R_loc}(9 t_2/16)` is positive whenever `16 | t_2`, so the block
count the re-shaped binder demands of the restriction is never the empty
selection -- the added `A:138` clause is a real constraint and not a vacuous
`0 = 0`.  This is the `eq:certified-pt-ht` integrality of `p_t = 9t/16` in the
form the round-`r4` clause needs.  General. -/
theorem selectedBlocks_pos {Rloc k₂ : ℕ} (hk₂ : 4 ≤ k₂) :
    0 < (2 : ℕ) ^ Rloc * (9 * 2 ^ k₂ / 16) := by
  obtain ⟨c, hc⟩ : ∃ c, k₂ = c + 4 := ⟨k₂ - 4, by omega⟩
  subst hc
  have hx : (9 : ℕ) * 2 ^ (c + 4) / 16 = 9 * 2 ^ c := by
    have h : (9 : ℕ) * 2 ^ (c + 4) = (9 * 2 ^ c) * 16 := by rw [pow_add]; ring
    rw [h, Nat.mul_div_cancel _ (by norm_num)]
  rw [hx]
  positivity

/-- **Aux (the frozen selected count is exactly the record's own count).**

`r' p_t` and the `06:1128--1130` output size `9K/16` agree at the recorded
exponents, so the round-`r4` exactness clause `blocks = r' p_t` and the
round-`r3` supply clause speak about the same number and the shape change adds no
second notion of "how many blocks".  General over any call record. -/
theorem selectedBlocks_eq_output_size {T R Rloc b₁ e r₂ r₃ ℓ : ℕ} {dcls colDens : ℝ}
    (h : ExtensionCallThree T R Rloc b₁ e r₂ r₃ ℓ dcls colDens) :
    (2 : ℕ) ^ Rloc * (9 * 2 ^ T / 16) = 9 * 2 ^ (r₃ + ℓ + r₂) / 16 := by
  rw [h.selected_count, h.capacity_exponent]

end ShapeSeparation

end EthInapproximability.ParameterizedNP.WrapperProtectedEarly
