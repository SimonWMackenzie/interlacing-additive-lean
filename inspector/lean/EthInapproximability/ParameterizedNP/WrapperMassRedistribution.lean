import EthInapproximability.ParameterizedNP.ParameterSchedule

/-!
# Parameterized NP route: mass redistribution and completion of scale alignment

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 1512--1781**,
  the subsubsection `sec:wrapper-mass-redistribution`, "Mass redistribution and
  completion of scale alignment", opening at `09:1512--1513` immediately after
  `sec:wrapper-protected-early` (whose last line `09:1511` the predecessor module
  `WrapperProtectedEarly` discharges) and closing at `09:1781`, the last line of
  the frozen dense-rung argument, immediately before the closing
  `\begin{proof}[Proof of \Cref{thm:first-wrapper}]` at `09:1783`.  This is the
  **final** Section-9 print-order block of the `hDenseRung` range: with it the
  five-block range `09:335--1781` is covered end to end.

  The anchors traced here, in the order the frozen block prints them:
  * `09:1515--1517`, the no-omitted-early-leaf remark: "By
    `lem:wrapper-no-bob-completion`, every retained protected row from every
    donor reaches exactly one first-Bob node or one final Alice-frontier node.
    Thus the mass decomposition below has no omitted early-leaf term";
  * `09:1519--1525`, the clean coordinate set `J_clean` and the contrapositive
    call: "Apply the contrapositive of `lem:early-protected-closure` at every
    first-Bob node, with `J_0 = J_clean`.  Such a node has `kappa_v >= 2`, and the
    conclusion of the lemma would exceed its remaining child budget";
  * `eq:wrapper-total-early-mass` (label `09:1533`, display `09:1526--1534`):
    `P_B < 128 mu_P B_theta L_q s K_B <= 128 mu_P B_theta L_q s e_0/(1-vartheta)`;
  * `09:1535--1540`, the Bob-heavy definition: a clean donor `j` is Bob-heavy if
    `sum over first-Bob frontier nodes v of P_v({j}) > eta_R/4`, "where mass is
    normalized by `m`, as in the definition of `P_v`";
  * `eq:wrapper-bob-heavy-count` (label `09:1546`, display `09:1542--1547`):
    `e_B <= 512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)`;
  * `09:1548`, `J_good` is the set of the other clean donors;
  * `09:1550--1552`, owners: "Every clean reference certificate has a unique final
    node, its *owner*.  Distinct clean donors have distinct owners because a final
    node contains at most one clean certificate.  Let `n_T` be the total number of
    final nodes";
  * `eq:wrapper-exceptional-count` (label `09:1562`, display `09:1555--1564`):
    `e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`, with the
    frozen justification `09:1564` "Here we used `K_B + n_T <= q` and
    `eq:wrapper-clean-count`";
  * `09:1566--1584`, the four-category loss table for the rows of a good donor
    missing from its owner: initially deleted rows at most `eta_R m/16`; base rows
    lost along the unique clean route less than `eta_R m/16`; protected rows
    stopped at first-Bob nodes at most `eta_R m/4`; protected rows sent to other
    final nodes, "the remaining loss";
  * `09:1585--1598`, the three justifications: the first line from
    `delta_U q <= eta_R/16`; the second from the clean-route geometric sum
    `sum_{h=0}^{r-1} A_h = A_0 sum 2^h = (q-1)A_0 < q A_0` with the schedule gate
    `q A_0 <= eta_R m/16`; the third line "is the definition of not being
    Bob-heavy";
  * `09:1600--1610`, the contrapositive: "If the last line were at most
    `eta_R m/2`, then the owner would retain more than
    `1 - (1/16 + 1/16 + 1/4 + 1/2) eta_R = 1 - 7 eta_R/8 > 1 - eta_R` of all rows
    of its copy of `N`.  Its coordinate lies outside the singleton cover, so its
    outer column projection has density at least `1 - eta_C`.  The
    deletion-stable Stage-4 theorem would make the owner `C`-hard, impossible
    under the alleged shallow protocol";
  * `eq:wrapper-mass-leaves-owner` (label `09:1614`, display `09:1611--1615`):
    `sum_{T != own(j)} m_{j,T} > eta_R/2` for `j in J_good`;
  * `eq:wrapper-owner-threshold` (label `09:1624`, display `09:1620--1625`):
    `lambda_0 = q_2 2^{1-b_1}`, `delta_i = lambda_0 + 5 eps_i + 2/q_2`, with
    `eps_i` "the fraction of its ordinary baseline missing at `own(i)`"
    (`09:1617--1619`);
  * `eq:wrapper-baseline-deficit-sum` (label `09:1630`, display `09:1627--1631`):
    `sum_{i in J_good} eps_i <= eta_R/(8g)`, with its frozen derivation
    `09:1632--1642`;
  * `09:1643--1646`: "If a different donor `j` sent protected mass at least
    `2 mu_P delta_i` to `own(i)`, one of the two reservoir types would arrive
    there at relative density at least `delta_i`.  Such a transfer is possible
    only when `delta_i <= 1`";
  * `09:1648--1679`, the terminal-state application: the retained ordinary
    reference rows at physical density `1 - eps_i`, the joint ordinary Stage-3
    column set, the `tau_0 = 2 s x_T` quotient row density, the `a_min` typed pair
    density, the `eq:wrapper-template-gates` margin `>= 49/64`, hypotheses
    (a)--(c) of `lem:terminal-state-realization`, `delta_i = lambda_0 + 5 eps_i +
    2/q_2` with `q_2 >= 16` and `lambda_0 <= 1/8`, the two seed certificates,
    `log_2 s < b_T`, Extension call (ii), and `lem:terminal-two-stream` making
    the restriction and hence the owner `C`-hard, "Therefore every such transfer
    is strictly below `2 mu_P delta_i`";
  * `eq:wrapper-owner-gates` (label `09:1688`, display `09:1682--1689`):
    `2 mu_P q lambda_0 <= eta_R/16`, `mu_P <= g/20`, `q_2 >= 64 mu_P q/eta_R`;
  * `eq:wrapper-good-to-good` (label `09:1698`, display `09:1692--1699`):
    `2 mu_P sum_i delta_i <= 2 mu_P (q lambda_0 + 5 eta_R/(8g) + 2q/q_2)
    <= 3 eta_R/16 < eta_R/4`;
  * `09:1700--1702`: "every good donor sends more than `eta_R/4` protected mass to
    exceptional final nodes.  If `e_T = 0`, this is already a contradiction";
  * `09:1704--1709`, the double pigeonhole: an exceptional node per good donor
    receiving more than `eta_R/(4 e_T)`, a node `T_*` chosen by at least
    `|J_good|/e_T` donors, and one common reservoir type for at least half of
    those donors;
  * `eq:wrapper-terminal-density` (label `09:1712`, display `09:1710--1713`):
    `delta_0 = eta_R/(8 e_T mu_P)`;
  * `09:1715--1731`, the schedule bounds `e_T <= E_T` and
    `u_don <= u_term`, the derived `|J_good| = c - e_B >= q - E_T`, and the
    legality of dividing by `E_T` ("`theta <= 1/160 < 18/25`, so `B_ref >= 2`;
    since `t_ref >= 4`, `eq:cover-bounds` and `eq:terminal-uniform-bounds` give
    `e_0^max >= 1` and `E_T >= 1`");
  * `eq:wrapper-terminal-donor-gate` (label `09:1740`, display `09:1736--1741`):
    `|J_good| > q/2` and `q/(4 E_T) > u_don B_theta`, from the first two gates of
    `eq:terminal-wrapper-gates`;
  * `09:1742--1744`: "If `delta_0 >= 1`, the strict pigeonhole conclusion
    preceding `eq:wrapper-terminal-density` is itself impossible.  We may
    therefore assume `delta_0 < 1`, and hence `u_don >= 8s`";
  * `09:1746--1759`, the poor-`u_don` projection cover leaving `u_don` donors at
    joint density `rho_0`, `lem:template-coordinate-extraction` on the resulting
    `u_don/2` donors at retained density `rho_0 2^{-u_don-1}`, and the Stage-2
    partition average giving at least `delta_0 q_2/2` represented blocks per donor
    at surviving `C_1`-density at least `delta_0/2`;
  * `eq:wrapper-terminal-block-supply` (label `09:1763`, display
    `09:1761--1765`): `u_don delta_0 q_2/4 >= 2 s q_2`;
  * `09:1767--1781`: `kappa = 2 s q_2`, exactly `9 kappa/16` selected blocks, the
    ambient width `(u_don/2) q_2 >= 2 kappa` making `r' = kappa/t_2` legal, call
    (iv) of `sec:extension-call-ledger` verified uniformly for every `e_T <= E_T`
    and `u_don <= u_term`, and the endpoint
    `B_cap + log_2 kappa = B_cap + log_2 q_2 + log_2 s + 1 = C`, contradicting
    the shallow protocol and proving `eq:wrapper-u-dense`.
* **Cross-anchors opened first-hand for this tranche:**
  * `06:1102--1167`, `sec:extension-call-ledger`: the common binders
    `eq:extension-common-binders` (`06:1107--1113`), the ambient/represented
    binders `r = q_amb/t_2`, `r' = K/t_2` (`06:1122--1125`), the exact output size
    `|Q_s| = r' p_seed = 9K/16` (`06:1128--1130`), and row **(iv)** "Exceptional
    terminal recipient (the final application in
    `sec:wrapper-mass-redistribution`)" (`06:1154--1159`) with
    `v = u_don/2`, `K = 2 s q_2`, `h = rho_0 2^{-u_don-1}`, `a^sharp = 0`, "The
    donor average supplies per-block row density at least `delta_0/2`, again at
    least `K 2^{-b_1}` by the structural gates", closed by the uniform sentence
    `06:1161--1167`;
  * `06:715--731`, `eq:terminal-uniform-bounds`: `vartheta = 9/16`,
    `B_theta = B_pair`, `L_q = ceil(log_2(2q)) + 1`,
    `E_B = ceil(512 mu_P B_theta L_q s e_0^max/((1-vartheta) eta_R))`,
    `E_T = ceil(e_0^max/(1-vartheta)) + E_B`,
    `delta_term = eta_R/(8 mu_P max{1, E_T})`, and `u_term` the least power of two
    with `u_term delta_term >= 8s`, together with `06:732--735` ("at most `E_B`
    Bob-heavy clean sources and at most `E_T` exceptional terminal recipients.
    Every terminal many-donor application has density at least `delta_term` and
    donor width at most `u_term`") and `06:745--747` ("no parameter in
    `eq:terminal-uniform-bounds` depends on which terminal state a protocol
    happens to reach");
  * `06:738--743`, `eq:terminal-wrapper-gates`:
    `q >= 8 max{1, E_T}`, `q > 4 E_T u_term B_theta`, `q/4 >= t_ref`;
  * `06:639--653`, `eq:cover-bounds`, for `B_ref = min{B >= 1 : (18/25)^B <
    theta}` and
    `e_0^max = (B_ref - 1)(t_ref/2 + log_2 t_ref - 2) + (B_sing - 1) + 2(B_pair -
    1)`, which is what `09:1727--1731` uses to get `e_0^max >= 1`;
  * `06:514--518`, `eq:q-deltaU`: `q = 2^{A_wrap L_P^2}` and
    `delta_U = eta_R/(16q)`, i.e. the frozen identity `delta_U q = eta_R/16` that
    `09:1585` and `09:1641` both invoke;
  * `06:875--884`, `eq:parameter-wrapper-survival-gates`, the schedule-side
    spelling of `eq:wrapper-initial-survival`: `q A_0/m <= eta_R/16`,
    `q A_0 + delta_U q m <= m_G`, `q(q-1)A_0/m_G <= eta_R/(16g)` -- the third row
    is the "last inequality" of `09:1641--1642`;
  * `06:1213--1218`, which lists `eq:wrapper-owner-gates` among the finite
    parameter conditions the effective cutoff discharges, so this block *uses*
    those three gates and does not prove them;
  * `09:238--272`, `thm:first-wrapper`, whose `09:256--258` explicitly assumes
    `eq:wrapper-owner-gates`, "whose clauses are verified by
    `eq:stage2-structural-gates` and the fixed duplication masses";
  * `09:1224--1232`, `eq:wrapper-initial-survival`, and `09:1217--1222`,
    `A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0` -- the reference-row floors the
    clean-route loss sums;
  * `09:386--395`, `eq:wrapper-template-gates`, and `09:373--384` for
    `tau_0 = 2 s x_T`, `rho_pair = 99/100` and `a_min`;
  * `09:1777--1778`, the frozen budget identity
    `C = B_cap + log_2 q_2 + log_2 s + 1`, banked as
    `TerminalTwoStream.terminalTarget`.

## What this module lands, and what it deliberately does not

**Proved outright.**

1. `09:1515--1517`, the no-omitted-early-leaf fact, as a statement about the
   banked `DenseWrapperFrontier.WrapperFrontier`: the first-Bob nodes and the
   final Alice nodes **exhaust** the frontier (`frontier_no_early_leaf`), so the
   two-term protected-mass decomposition `protectedMass_two_term` has no third
   summand.  The banked `sum_bobNodes_add_sum_finalNodes` is consumed by pin and
   restated nowhere.
2. `eq:wrapper-total-early-mass` in full (`wrapperTotalEarlyMass`), from the
   per-node contrapositive form `firstBob_protectedMass_lt` -- itself the frozen
   `09:1521--1523` budget contradiction over the banked
   `DenseWrapperFrontier.firstBob_budget_contradiction` -- and the banked
   `eq:wrapper-clean-count` bound `K_B <= e_0/(1-vartheta)`.
3. `eq:wrapper-bob-heavy-count` (`wrapperBobHeavyCount`), over the general
   counting lemma `card_le_of_lower_bounds`.
4. `eq:wrapper-exceptional-count` (`wrapperExceptionalCount`), including the
   owner-injectivity step of `09:1550--1552` (`owner_injOn_of_unique_clean`,
   whose input is the banked `lem:final-reference-uniqueness` in counting form).
5. `eq:wrapper-mass-leaves-owner` (`wrapperMassLeavesOwner`) with the frozen
   four-category arithmetic `1/16 + 1/16 + 1/4 + 1/2 = 7/8` and the strict margin
   `1 - 7 eta_R/8 > 1 - eta_R`, plus the clean-route geometric sum
   `cleanRouteLoss_eq` / `cleanRouteLoss_lt` over the banked
   `DenseWrapperFrontier.refRowFloor`.
6. `eq:wrapper-owner-threshold` and `eq:wrapper-baseline-deficit-sum`
   (`ownerThreshold`, `wrapperBaselineDeficitSum`), over the **banked**
   `DenseBranchSelection.lambdaZero` -- the frozen paper has exactly one
   `lambda_0` (`09:1621`, `08:796`) and this module defines no second copy, so
   `ownerThreshold` is syntactically the left-hand side of the third clause of
   the banked `TerminalTwoStream.terminalEntry`.  `lambdaZero_le_eighth` proves
   the frozen `lambda_0 <= 1/8` from the structural gate `16 q_2 <= 2^{b_1}`,
   and `structuralReadout` obtains the same readout the way `09:1670--1671`
   does, by pin from `TerminalTwoStream.terminalEntry_of_stageTwoWidths`.
   `terminalEntry_of_ownerThreshold` is the bridge from the owner threshold to
   `eq:terminal-entry`, and `ownerHard_of_ownerThreshold` is the frozen join:
   the owner-threshold half composed with the terminal-lemma half, so that the
   two halves of this block demonstrably compose rather than merely coexisting.
7. `eq:wrapper-owner-gates` as the predicate `wrapperOwnerGates` and
   `eq:wrapper-good-to-good` **proved** from it (`wrapperGoodToGood`), including
   the exact frozen constant `3 eta_R/16`; the middle gate `mu_P <= g/20` is a
   *checked identity* at the frozen `mu_P = 1/184` and `g = 91/92`
   (`muP_le_g_div_twenty`).
8. The pigeonhole layer of `09:1700--1713`: the residual mass to exceptional
   nodes (`goodDonor_to_exceptional_gt`), the `e_T = 0` contradiction
   (`exceptional_nonempty_of_positive_mass`), the fibre pigeonhole
   (`exists_heavy_fibre`), the reservoir halving, and
   `eq:wrapper-terminal-density` (`deltaZero`, `deltaZero_of_pigeonhole`).
9. The schedule layer of `09:1715--1744`: `E_B`, `E_T`, `delta_term` and
   `u_term` are **consumed by pin** from the banked
   `EthInapproximability.ParameterizedNP.ParameterSchedule` (module
   `SCHEDULE-001`) at their `eq:terminal-uniform-bounds` values and are defined
   nowhere here; what this module adds is `E_T >= 1`
   (`one_le_ET_of_e0Max_pos`), `|J_good| >= q - E_T`
   (`goodDonorCount_ge`), both clauses of `eq:wrapper-terminal-donor-gate`
   (`wrapperTerminalDonorGate`), the impossibility of `delta_0 >= 1`
   (`deltaZero_lt_one_of_density`), and `u_don >= 8s`
   (`uDon_ge_eight_s`).
10. The final-call layer of `09:1746--1781`: the surviving donor count against
    the poor-`u_don` cover (`donors_survive_cover`) over the banked
    `WrapperProjectionCovers.productProjectionCover`, the entering column density
    `h = rho_0 2^{-u_don-1}` (`callFourH`) with its two range facts,
    `eq:wrapper-terminal-block-supply` (`terminalBlockSupply`), the frozen
    capacity `kappa = 2 s q_2` (`terminalCapacity`), the ambient-width inequality
    `(u_don/2) q_2 >= 2 kappa` (`terminal_ambient_width_ge`), row (iv) of the
    call ledger as the record `ExtensionCallFour` **constructed** from schedule
    data by `extensionCallFour_of_width`, the exact output size `9K/16`, and the
    endpoint identity `B_cap + log_2 kappa = C` (`terminalEndpoint_identity`)
    over the banked `TerminalTwoStream.terminalTarget`.
11. The **conditional scheduled point** of Section 13: the block's own gate
    system stated over quantities that are *evaluated through the banked
    Section-6 definitional chain* rather than assigned.  `theta`, `t_ref`,
    `t_2`, `e_0^max`, `E_B`, `E_T`, `delta_term` and `u_term` are universally
    quantified under the schedule's own search clauses
    (`ParameterSchedule.KrefPred`, `ParameterSchedule.K2Pred`,
    `ParameterSchedule.terminalWrapperGates`), and non-vacuity is discharged by
    **exponent arithmetic at large `A_wrap`** against
    `ParameterSchedule.terminalWrapperGates_at_scheduled_point`.  **No
    declaration in this module claims a concrete legal schedule tuple**, and no
    numeral is assigned to any quantity `sec:parameters` fixes; see the scope
    paragraph at the head of Section 13.
12. The **assembly bridge** `le_D_of_no_shallow_protocol` and
    `denseRung_of_no_shallow_member`: the passage from the frozen
    `09:1192--1193` shape ("suppose for contradiction that a protocol `P` of cost
    at most `C+r-1` computes `U'`") to the deferred binder `hDenseRung` of
    `ScaleAlignOpening.firstWrapper`, over the vendored
    `Workspace.UpperBound.AchievableCosts_nonempty` and
    `EthBridge.le_Dfamily`.  This is a *bridge*, not a discharge: see below.

**Stated, not proved (named hypotheses, never axioms).**

* `hTerminalTwoStream`, the banked `TerminalTwoStream.TerminalTwoStream` at the
  `09:1661--1677` substitution, consumed **by pin at its recorded statement**
  through `ownerHard_of_terminalTwoStream`, which supplies the eight antecedents
  of that `def` as explicit binders and returns its conclusion.  The banked
  terminal lemma is itself *stated and not proved*
  (`TERMINAL-TWO-STREAM-001`), so this is a **conditional citation only** and
  nothing here strengthens it;
* `hCleanCount`, the banked `eq:wrapper-clean-count` bound, entering as the real
  inequality `K_B + ell <= e_0/(1-vartheta)` it is;
* `hHard`, the deletion-stable Stage-4 hardness of `09:1609--1610`, and
  `hExtension`, the Localized Extension call (iv) endpoint of `09:1771--1778`:
  both enter as implications into a residual-complexity bound, never as
  assertions;
* the three clauses of `eq:wrapper-owner-gates`, which `06:1213--1218` assigns to
  the effective cutoff and `09:256--258` assumes in `thm:first-wrapper`.

**GAP-EXPOSED, recorded rather than papered over.**  Inside `09:1512--1781` the
following are *not* modelled and no declaration asserts them:

* **GAP-EXPOSED M1 (the protocol and its routed certificate system).**  There is
  no protocol object, no Bob query, no owner rectangle and no per-node column
  projection.  Every contact with them is an explicit binder.  In particular the
  frozen phrases "the deletion-stable Stage-4 theorem would make the owner
  `C`-hard" (`09:1609`) and "This again contradicts the shallow protocol"
  (`09:1780`) enter as `hHard` and `hExtension`.
* **GAP-EXPOSED M2 (`lem:terminal-state-realization` binder-shape mismatch,
  reported and not forced).**  `09:1661--1669` says the Stage-4 template-row
  entry map supplies hypotheses (a)--(c) of `lem:terminal-state-realization`
  "with ... ordinary deficit `eps_i`, and foreign density `delta_i`".  The banked
  `TerminalStateRealization.terminalStateRealization` takes its foreign density
  as `hForDensity : delta' <= (streamRows XZ j Rf).card / Rf.card`, a *ratio of
  physical row counts at a realized rectangle*, and its ordinary deficit as
  `hOrdDensity : 1 - eps <= (streamRows XZ i RG).card / RG.card`.  The block's
  `eps_i` and `delta_i` are, respectively, a normalized baseline deficit
  (`09:1618--1619`) and the *threshold* `lambda_0 + 5 eps_i + 2/q_2`
  (`eq:wrapper-owner-threshold`); identifying them with those two ratios needs
  exactly the owner rectangle and its stream row sets, which is GAP-EXPOSED M1.
  The realization pin is therefore **cited and not applied**: this module
  consumes `TerminalTwoStream.TerminalTwoStream`, whose own `hstate` argument is
  the `TwoStreamState` the realization would produce, and carries that argument
  as a binder.  Forcing the identification would have meant inventing the row
  counts, which the full-paper mandate forbids.
* **GAP-EXPOSED M3 (the two reservoir types).**  "One of the two reservoir types
  would arrive there at relative density at least `delta_i`" (`09:1644--1646`)
  and "One common reservoir type accounts for at least half of those donors"
  (`09:1707--1708`) are Section-8 reservoir structure.  Only their *counting*
  consequence is used, through the general `reservoir_halving_of_pair` and the
  banked `WrapperProtectedEarly.protected_reservoir_halving`.
* **GAP-EXPOSED M4 (`hDenseRung` is bridged, not discharged).**  The frozen dense
  rung is a statement about **every** member of the one-copy bracket family, and
  the contradiction engine of this block runs inside a *fixed* alleged protocol
  on a *fixed* member, through the routed certificate system of GAP-EXPOSED M1.
  `denseRung_of_no_shallow_member` reduces `hDenseRung` to exactly that per-member
  statement and no further; the per-member statement itself remains a binder.
  **No route completion is claimed, and `eq:wrapper-u-dense` is asserted
  nowhere.**
* **The `wrapperCleanCount` debt of `DenseWrapperFrontier` is NOT resolved here.**
  That module's GAP-EXPOSED 4 is `eq:wrapper-frontier-conservation`'s first
  clause `sum_v W_v >= q - e_0`, whose routing dynamics are printed at
  `09:1259--1266` -- inside `sec:dense-wrapper-frontier`, **not** inside
  `09:1512--1781`.  Opened first-hand: the present block never re-derives that
  inequality; it *consumes* `eq:wrapper-clean-count` at `09:1531`, `09:1560` and
  `09:1720`.  The debt therefore stays with the routing block and is recorded
  here as unresolved rather than silently re-homed.

## Reader counterpart

Searched first-hand in the frozen reader artifact
`routes/parameterized-np/reader-facing/sections/`: `J_good`, `J_clean`,
"Bob-heavy", `e_B`, `e_T`, `E_T`, `u_don`, `u_term`, `lambda_0`, `delta_0`,
"redistribution" and "owner" occur **nowhere**.  The reader's only account of
this block is the unnumbered prose inside the proof of
`thm:paper-adapted-stage4-interface` at `A-stage4-details.tex:374--377` ("The
fixed masses and the certified cover bounds ensure that either an early protected
reservoir already gives a hard restriction or one terminal owner receives enough
protected mass from a donor"), whose line `374` is already recorded by
`WrapperProjectionCovers` as *unclaimed prose* and whose content
`WrapperProtectedEarly` already declined to claim; citing prose as a statement is
barred, and re-citing an assigned reader item is barred.  Opened first-hand this
tranche, the two remaining candidates in range are both barred for the same
reason: `A-stage4-details.tex:396--399` ("The complete owner--donor count is
finite: it uses only the fixed reservoir masses above, the two source deletion
tolerances, and the exact cover and ceiling inequalities certified by the
parameter compiler.  It is expanded line by line in the ultra-explicit
companion") is the reader's *nearest* account of this block and is unnumbered
prose inside the proof of `thm:paper-adapted-stage4-interface`; and the one
numbered display in range, `A-stage4-details.tex:394`, is
`D_U(1; 1-delta_U, theta) >= C + r_q`, i.e. `eq:wrapper-u-dense` itself, which
this module does **not** close and therefore must not claim.  Reader lines
`390--391` are already assigned to `TERMINAL-TWO-STREAM-001`.  **This module
claims no reader item**, and recording the absence is a finding about the reader
artifact rather than an omission here.

The search was repeated first-hand for the scheduled-record clauses that
Section 13 reads.  `64 | s`, the `b_1` power-of-two clause and
the accessor list of `05:417--422` occur **nowhere** in
`routes/parameterized-np/reader-facing/sections/`; the reader's only
power-of-two records in range are `03-parameterized-construction.tex:72`
(`q_2, t_2` are powers of two) and `:309` (`q, t` powers of two, with `t <= 2^b`
at depth `b_1`), and neither states any divisibility floor on `s`.  So the
scheduled-record clauses have **no** reader counterpart and none is cited.

## The banked schedule is consumed by pin, never restated

Section 6 is already reified as
`EthInapproximability.ParameterizedNP.ParameterSchedule` (`SCHEDULE-001`).
Every Section-6 quantity this block reads is therefore taken from that module
by name, and this module defines **no** second copy of any of them:

* `eq:q-deltaU` (`06:514--518`): `ParameterSchedule.qWrap`, `.deltaU`.
* `eq:Q-theta-choice` (`06:526--537`): `EntryGates.Q0`, `EntryGates.Qwidth`
  and `ParameterSchedule.theta`.
* `eq:eta-choice` (`06:203--218`): `ParameterSchedule.etaC`, `.etaR`.
* `eq:cover-bounds` (`06:639--653`): `ParameterSchedule.e0maxSched`.
* `eq:terminal-uniform-bounds` (`06:715--730`):
  `ParameterSchedule.vartheta`, `.EB`, `.ET`, `.deltaTerm`, `.uTerm`.
* `eq:terminal-wrapper-gates` (`06:738--743`):
  `ParameterSchedule.terminalWrapperGates`, all **three** rows.
* `eq:tref-search` (`06:557--571`): `ParameterSchedule.krefFloor`,
  `.KrefPred`, `.kref`, `.tref`.
* `eq:t2-search` (`06:763--772`) with `eq:Hmax` (`06:754--761`):
  `ParameterSchedule.K2Pred`, `.k2`, `.t2`, `.HmaxSched`, `.LhSched`.
* the least-power-of-two accessor (`06:1253--1268`):
  `ParameterSchedule.leastPowTwoGe`.

The banked `DenseWrapperFrontier.vartheta` and `ParameterSchedule.vartheta` are
the *same* frozen `9/16` and `vartheta_pin` below records that as a checked
equation, so the `eq:wrapper-clean-count` side of the block and the
`eq:terminal-uniform-bounds` side cannot drift apart.

## Axiom surface

`LegacyNPCC.Stage12` is **not** imported, directly or transitively through
`WrapperProtectedEarly` or `ParameterSchedule`; the AGHP balanced-family axiom
is not reached.
`EXPANDER-001` has no Lean declaration and appears in no hypothesis of this
module: call (iv) has `v = u_don/2 > 1`, so `06:1119--1120` places it on the
product branch of `A:126--128`, but this module records the call's *binders* and
never invokes the inherited corollary, whose endpoint enters as the named
implication `hExtension`.  Every declaration below is `Classical`-only.
-/

namespace EthInapproximability.ParameterizedNP.WrapperMassRedistribution

open Finset
open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly

/-! ## Section 1  `09:1515--1517`: the decomposition has no early-leaf term -/

/-- **`09:1515--1517`.**

"By `lem:wrapper-no-bob-completion`, every retained protected row from every donor
reaches exactly one first-Bob node or one final Alice-frontier node.  Thus the
mass decomposition below has no omitted early-leaf term."

The frozen content, at the banked routed frontier: the first-Bob nodes and the
final Alice nodes **exhaust** the frontier.  This is the fact that licenses a
two-term decomposition; the banked `bobNodes_disjoint_finalNodes` supplies the
"exactly one" half and is not restated.  General in `r` and in the node type. -/
theorem frontier_no_early_leaf {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : WrapperFrontier r V) :
    F.bobNodes ∪ F.finalNodes = (Finset.univ : Finset V) := by
  ext v
  simp only [WrapperFrontier.bobNodes, WrapperFrontier.finalNodes, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_univ, iff_true]
  cases hb : F.firstBob v with
  | false => exact Or.inr rfl
  | true => exact Or.inl rfl

/-- **`09:1515--1517`, the decomposition itself.**

With no early-leaf term, the total protected mass over the frontier is the sum of
its first-Bob part and its final-Alice part, and in particular the first-Bob part
is the total minus the final part.  The additive split is the banked
`sum_bobNodes_add_sum_finalNodes`, consumed by pin; what is stated here is the
frozen *consequence* the block uses at `09:1526`. -/
theorem protectedMass_two_term {r : ℕ} {V : Type*} [Fintype V]
    (F : WrapperFrontier r V) (P : V → ℝ) :
    ∑ v ∈ F.bobNodes, P v = (∑ v, P v) - ∑ v ∈ F.finalNodes, P v := by
  have h := F.sum_bobNodes_add_sum_finalNodes P
  linarith

/-! ## Section 2  `eq:wrapper-total-early-mass` (`09:1519--1534`) -/

/-- **`09:1526--1529`.**  The frozen early-mass coefficient
`128 mu_P B_theta L_q s`, at the banked constants `mu_P = 1/184`,
`B_theta = coverExponent rho_0 theta` and `L_q = ceil(log_2(2q)) + 1`, all
consumed by pin from `WrapperProtectedEarly` and re-rolled nowhere. -/
noncomputable def earlyMassCoeff (θ : ℝ) (q s : ℕ) : ℝ :=
  128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ)

/-- **Aux 2.1.**  The early-mass coefficient is positive at every legal `theta`
and every positive Stage-3 width; `B_theta >= 1` is the banked
`one_le_Btheta` and `L_q >= 1` the banked `one_le_Lq`. -/
theorem earlyMassCoeff_pos {θ : ℝ} (hθ : 0 < θ) {q s : ℕ} (hs : 1 ≤ s) :
    0 < earlyMassCoeff θ q s := by
  have hB : (1 : ℝ) ≤ (Btheta θ : ℝ) := by exact_mod_cast one_le_Btheta hθ
  have hL : (1 : ℝ) ≤ (Lq q : ℝ) := by exact_mod_cast one_le_Lq q
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have := muP_pos
  unfold earlyMassCoeff
  positivity

/-- **Aux 2.2.**  The coefficient of `eq:protected-early-threshold` is exactly
`earlyMassCoeff theta q s` times the node's capacity: the frozen threshold of
`09:1421--1425` reads `128 mu_P B_theta L_q s kappa`, so summing it over
first-Bob nodes is summing `earlyMassCoeff` against `kappa_v`.  A checked
identity, not a new constant. -/
theorem earlyMassCoeff_threshold (θ : ℝ) (q s : ℕ) (κ : ℝ) :
    earlyMassCoeff θ q s * κ = 128 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * κ := by
  unfold earlyMassCoeff; ring

/-- **`09:1519--1525`, the contrapositive call, in its budget form.**

"Apply the contrapositive of `lem:early-protected-closure` at every first-Bob
node, with `J_0 = J_clean`.  Such a node has `kappa_v >= 2`, and the conclusion of
the lemma would exceed its remaining child budget."

`hclosure` is `lem:early-protected-closure` at this node -- the banked
`WrapperProtectedEarly.earlyProtectedClosure`, whose conclusion is a child of
complexity at least `C + log_2 kappa - 1`; the budget arithmetic is the banked
`DenseWrapperFrontier.firstBob_budget_contradiction`, re-proved nowhere.  The
frozen `kappa_v >= 2` appears as `1 <= ell`, i.e. `kappa_v = 2^{ell} >= 2`.
General in `C`, `r`, the depth `d`, the exponent `ell`, the residual budget and
the mass. -/
theorem firstBob_protectedMass_lt {C r d ℓ B : ℕ} {Pv thr : ℝ} (hC : 3 ≤ C)
    (hdℓ : d + ℓ = r) (hℓ : 1 ≤ ℓ) (hbudget : B + (d + 1) ≤ C + r - 1)
    (hclosure : thr ≤ Pv → C + ℓ - 1 ≤ B) :
    Pv < thr := by
  by_contra hcon
  exact firstBob_budget_contradiction hC hdℓ hℓ hbudget (hclosure (not_lt.mp hcon))

/-- **`eq:wrapper-total-early-mass` (`09:1526--1534`), proved.**

"Therefore the total protected mass from clean donors that stops at first-Bob
nodes is strictly less than `P_B < 128 mu_P B_theta L_q s K_B <=
128 mu_P B_theta L_q s e_0/(1 - vartheta)`."

Both lines.  The first is the strict per-node bound of `firstBob_protectedMass_lt`
summed over the first-Bob nodes; the second replaces `K_B` by the banked
`eq:wrapper-clean-count` bound `K_B <= e_0/(1-vartheta)` (`09:1355`,
`DenseWrapperFrontier.wrapperCleanCount`, consumed as the real inequality
`hKB`).  The nonemptiness binder is not decoration: see
`totalEarlyMass_needs_a_first_bob_node`.  General in the node index type. -/
theorem wrapperTotalEarlyMass {ι : Type*} (B : Finset ι) (Pv κv : ι → ℝ)
    {cf e0 : ℝ} (hne : B.Nonempty) (hcf : 0 < cf)
    (hlt : ∀ v ∈ B, Pv v < cf * κv v)
    (hKB : ∑ v ∈ B, κv v ≤ e0 / (1 - vartheta)) :
    ∑ v ∈ B, Pv v < cf * (e0 / (1 - vartheta)) := by
  have hstep : ∑ v ∈ B, Pv v < ∑ v ∈ B, cf * κv v :=
    Finset.sum_lt_sum_of_nonempty hne hlt
  have hmul : ∑ v ∈ B, cf * κv v = cf * ∑ v ∈ B, κv v := by
    rw [Finset.mul_sum]
  have hle : cf * (∑ v ∈ B, κv v) ≤ cf * (e0 / (1 - vartheta)) :=
    mul_le_mul_of_nonneg_left hKB (le_of_lt hcf)
  linarith [hstep, hmul ▸ hstep]

/-- **`eq:wrapper-total-early-mass` at the frozen coefficient.**

The same statement with `cf` instantiated at `earlyMassCoeff theta q s`, so the
frozen display is available verbatim rather than through an abstract
coefficient. -/
theorem wrapperTotalEarlyMass_frozen {ι : Type*} (B : Finset ι) (Pv κv : ι → ℝ)
    {θ : ℝ} {q s : ℕ} {e0 : ℝ} (hθ : 0 < θ) (hs : 1 ≤ s) (hne : B.Nonempty)
    (hlt : ∀ v ∈ B, Pv v < earlyMassCoeff θ q s * κv v)
    (hKB : ∑ v ∈ B, κv v ≤ e0 / (1 - vartheta)) :
    ∑ v ∈ B, Pv v < earlyMassCoeff θ q s * (e0 / (1 - vartheta)) :=
  wrapperTotalEarlyMass B Pv κv hne (earlyMassCoeff_pos hθ hs) hlt hKB

/-! ## Section 3  `eq:wrapper-bob-heavy-count` (`09:1535--1547`) -/

/-- **`09:1535--1539`.**  "Call a clean donor `j` *Bob-heavy* if
`sum over first-Bob frontier nodes v of P_v({j}) > eta_R/4`, where mass is
normalized by `m`."  The frozen threshold, as a predicate on the per-donor
first-Bob mass. -/
def BobHeavy (etaR : ℝ) (mass : ℝ) : Prop := etaR / 4 < mass

theorem bobHeavy_iff (etaR mass : ℝ) : BobHeavy etaR mass ↔ etaR / 4 < mass := Iff.rfl

/-- **Aux 3.1, the general counting step behind `eq:wrapper-bob-heavy-count`.**

If every member of a subset `H` of `J` carries more than the positive threshold
`t`, the other members of `J` carry nothing negative, and the total over `J` is at
most `M`, then `|H| <= M/t`.  This is the *only* counting content of
`09:1541--1547`.  General. -/
theorem card_le_of_lower_bounds {ι : Type*} (J H : Finset ι) (f : ι → ℝ)
    {t M : ℝ} (ht : 0 < t) (hHJ : H ⊆ J) (hnonneg : ∀ j ∈ J, 0 ≤ f j)
    (hheavy : ∀ j ∈ H, t < f j) (htot : ∑ j ∈ J, f j ≤ M) :
    (H.card : ℝ) ≤ M / t := by
  classical
  have hHsum : t * (H.card : ℝ) ≤ ∑ j ∈ H, f j := by
    have : ∑ _j ∈ H, t ≤ ∑ j ∈ H, f j :=
      Finset.sum_le_sum fun j hj => le_of_lt (hheavy j hj)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  have hsub : ∑ j ∈ H, f j ≤ ∑ j ∈ J, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg hHJ fun j hj _ => hnonneg j hj
  have hfin : t * (H.card : ℝ) ≤ M := by linarith
  rw [le_div_iff₀ ht]
  linarith

/-- **`eq:wrapper-bob-heavy-count` (`09:1542--1547`), proved.**

"Their number `e_B` satisfies
`e_B <= 512 mu_P B_theta L_q s e_0/((1-vartheta) eta_R)`."

From `eq:wrapper-total-early-mass` and the Bob-heavy threshold `eta_R/4`: the
counting lemma gives
`e_B <= (128 mu_P B_theta L_q s e_0/(1-vartheta))/(eta_R/4)`, and the division by
a quarter is the frozen factor four that turns `128` into `512`.  General in the
donor index type.  Legality of `theta` and `s` is deliberately **not** a binder:
the frozen counting step needs only `eta_R > 0`, and adding the schedule
conditions would make the statement demand more than `09:1541--1547` does. -/
theorem wrapperBobHeavyCount {ι : Type*} (J H : Finset ι) (mass : ι → ℝ)
    {θ : ℝ} {q s : ℕ} {e0 etaR : ℝ} (hetaR : 0 < etaR)
    (hHJ : H ⊆ J) (hnonneg : ∀ j ∈ J, 0 ≤ mass j)
    (hheavy : ∀ j ∈ H, BobHeavy etaR (mass j))
    (htot : ∑ j ∈ J, mass j ≤ earlyMassCoeff θ q s * (e0 / (1 - vartheta))) :
    (H.card : ℝ)
      ≤ 512 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * e0
          / ((1 - vartheta) * etaR) := by
  have hq : (0 : ℝ) < etaR / 4 := by linarith
  have hcount := card_le_of_lower_bounds J H mass hq hHJ hnonneg hheavy htot
  have hv : (1 : ℝ) - vartheta = 7 / 16 := one_sub_vartheta
  have hrewrite :
      earlyMassCoeff θ q s * (e0 / (1 - vartheta)) / (etaR / 4)
        = 512 * muP * (Btheta θ : ℝ) * (Lq q : ℝ) * (s : ℝ) * e0
            / ((1 - vartheta) * etaR) := by
    rw [hv]
    unfold earlyMassCoeff
    field_simp
    ring
  rwa [hrewrite] at hcount

/-! ## Section 4  Owners and `eq:wrapper-exceptional-count` (`09:1550--1564`) -/

/-- **`09:1550--1552`, owner injectivity.**

"Every clean reference certificate has a unique final node, its *owner*.  Distinct
clean donors have distinct owners because a final node contains at most one clean
certificate."

The input is the banked `lem:final-reference-uniqueness` in its counting form: no
final node carries two clean certificates, i.e. every owner fibre inside the clean
donor set has at most one element.  The conclusion is injectivity on that set.
General in both index types. -/
theorem owner_injOn_of_unique_clean {ι V : Type*} [DecidableEq V]
    (Jclean : Finset ι) (own : ι → V)
    (huniq : ∀ v : V, (Jclean.filter fun j => own j = v).card ≤ 1) :
    ∀ i ∈ Jclean, ∀ j ∈ Jclean, own i = own j → i = j := by
  classical
  intro i hi j hj hij
  by_contra hne
  have hsub : ({i, j} : Finset ι) ⊆ Jclean.filter fun k => own k = own i := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hj, hij.symm⟩
  have hcard : (2 : ℕ) ≤ (Jclean.filter fun k => own k = own i).card := by
    have hpair : ({i, j} : Finset ι).card = 2 := Finset.card_pair hne
    calc (2 : ℕ) = ({i, j} : Finset ι).card := hpair.symm
      _ ≤ _ := Finset.card_le_card hsub
  have := huniq (own i)
  omega

/-- **`eq:wrapper-exceptional-count` (`09:1555--1564`), proved.**

"`e_T = n_T - |J_good| <= q - c + e_B <= e_0/(1-vartheta) + e_B`.  Here we used
`K_B + n_T <= q` and `eq:wrapper-clean-count`."

Both inequalities, over the reals, exactly as printed: `|J_good| = c - e_B`
(`09:1548`, the good donors are the non-Bob-heavy clean ones), `K_B + n_T <= q`
with `K_B >= 0`, and `c >= q - e_0/(1-vartheta)`.  `K_B >= 0` is genuinely
load-bearing -- see `exceptionalCount_needs_nonneg_KB`.  General. -/
theorem wrapperExceptionalCount {nT jgood c eB KB q e0 : ℝ}
    (hjgood : jgood = c - eB) (hKB0 : 0 ≤ KB) (hkraft : KB + nT ≤ q)
    (hclean : q - e0 / (1 - vartheta) ≤ c) :
    nT - jgood ≤ q - c + eB ∧ q - c + eB ≤ e0 / (1 - vartheta) + eB := by
  constructor
  · rw [hjgood]; linarith
  · linarith

/-! ## Section 5  The four-category table and `eq:wrapper-mass-leaves-owner`
(`09:1566--1615`) -/

/-- **`09:1593--1595`, the clean-route geometric sum.**

"`sum_{h=0}^{r-1} A_h = A_0 sum_{h=0}^{r-1} 2^h = (q-1) A_0 < q A_0`", at
`q = 2^r` and the banked reference-row floors `A_h = 2^h A_0`
(`DenseWrapperFrontier.refRowFloor`, consumed by pin).  The identity, exactly as
printed and with `q = 2^r` substituted.  General in `A_0` and `r`. -/
theorem cleanRouteLoss_eq (A0 r : ℕ) :
    ∑ h ∈ Finset.range r, refRowFloor A0 h = (2 ^ r - 1) * A0 := by
  induction r with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, refRowFloor]
      have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ^ (n + 1) - 1 = (2 ^ n - 1) + 2 ^ n := by
        rw [pow_succ]; omega
      rw [h2, Nat.add_mul]

/-- **`09:1595`, the strict frozen form.**  `(q-1) A_0 < q A_0` at `q = 2^r`,
which needs `A_0 >= 1` -- the frozen `A_0 = ceil(2 x_T m_G)` is positive at every
legal scale.  General. -/
theorem cleanRouteLoss_lt {A0 r : ℕ} (hA0 : 1 ≤ A0) :
    ∑ h ∈ Finset.range r, refRowFloor A0 h < 2 ^ r * A0 := by
  rw [cleanRouteLoss_eq]
  have h1 : (1 : ℕ) ≤ 2 ^ r := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h1
  have hstep : (2 ^ r - 1) * A0 + A0 = 2 ^ r * A0 := by
    rw [hk, Nat.add_sub_cancel_left, Nat.add_mul, Nat.one_mul]
    omega
  omega

/-- **`09:1596--1597`, the second table line.**  "The schedule requires
`q A_0 <= eta_R m/16`, proving the second line": the clean route's total loss is
strictly below `eta_R m/16`.  This composes `cleanRouteLoss_lt` with the first
row of `eq:wrapper-initial-survival` (`09:1226`), carried as the binder it is.
General. -/
theorem cleanRouteLoss_lt_budget {A0 r m : ℕ} {etaR : ℝ} (hA0 : 1 ≤ A0)
    (hgate : ((2 ^ r * A0 : ℕ) : ℝ) ≤ etaR * m / 16) :
    ((∑ h ∈ Finset.range r, refRowFloor A0 h : ℕ) : ℝ) < etaR * m / 16 := by
  have hlt := cleanRouteLoss_lt (A0 := A0) (r := r) hA0
  have : ((∑ h ∈ Finset.range r, refRowFloor A0 h : ℕ) : ℝ) < ((2 ^ r * A0 : ℕ) : ℝ) := by
    exact_mod_cast hlt
  linarith

/-- **`09:1600--1606`, the frozen retention arithmetic.**

"`1 - (1/16 + 1/16 + 1/4 + 1/2) eta_R = 1 - 7 eta_R/8 > 1 - eta_R`."  Both the
exact sum of the four table coefficients and the strict final margin, the latter
using `eta_R > 0`.  A checked identity. -/
theorem fourCategory_coefficients {etaR : ℝ} (hetaR : 0 < etaR) :
    (1 : ℝ) - (1 / 16 + 1 / 16 + 1 / 4 + 1 / 2) * etaR = 1 - 7 * etaR / 8
      ∧ 1 - 7 * etaR / 8 > 1 - etaR := by
  constructor
  · ring
  · linarith

/-- **`eq:wrapper-mass-leaves-owner` (`09:1600--1615`), proved.**

"If the last line were at most `eta_R m/2`, then the owner would retain more than
`1 - 7 eta_R/8 > 1 - eta_R` of all rows of its copy of `N`. ... The
deletion-stable Stage-4 theorem would make the owner `C`-hard, impossible under
the alleged shallow protocol.  We have proved
`sum_{T != own(j)} m_{j,T} > eta_R/2`."

The frozen contrapositive.  `L1`, `L2`, `L3` are the first three table lines at
their frozen budgets (`09:1575`, `09:1577`, `09:1579`), `hret` says the retained
fraction is at least one minus the total loss, and `hHard` is the frozen
hardness contradiction of `09:1609--1610`, carried as the implication it is
(GAP-EXPOSED M1).  General in all six reals. -/
theorem wrapperMassLeavesOwner {etaR L1 L2 L3 L4 retained : ℝ}
    (hetaR : 0 < etaR) (h1 : L1 ≤ etaR / 16) (h2 : L2 < etaR / 16)
    (h3 : L3 ≤ etaR / 4)
    (hret : 1 - (L1 + L2 + L3 + L4) ≤ retained)
    (hHard : ¬ (1 - etaR < retained)) :
    etaR / 2 < L4 := by
  by_contra hcon
  push Not at hcon
  exact hHard (by linarith)

/-! ## Section 6  `eq:wrapper-owner-threshold` and
`eq:wrapper-baseline-deficit-sum` (`09:1617--1642`) -/

/-- **`eq:wrapper-owner-threshold`, first half (`09:1621`), consumed BY PIN.**

`lambda_0 = q_2 2^{1-b_1}`.  The frozen paper has exactly ONE `lambda_0`, and it
is already banked as `DenseBranchSelection.lambdaZero q_2 b_1 = 2 q_2/2^{b_1}`
(`08:796`, `DenseBranchSelection.lean:693`) -- the same constant the banked
`TerminalTwoStream.terminalEntry` (`09:838--844`) is stated over.  **No local
copy is defined here**: a second definition with the factors in the other order
is propositionally but not definitionally equal, so the owner-threshold half and
the terminal-lemma half would compile green without composing.  Everything below
speaks about the banked constant. -/
theorem lambdaZero_eq_frozen_display (q₂ b₁ : ℕ) :
    DenseBranchSelection.lambdaZero q₂ b₁ = (q₂ : ℝ) * 2 / 2 ^ b₁ := by
  rw [DenseBranchSelection.lambdaZero]; ring

/-- **`eq:wrapper-owner-threshold`, second half (`09:1623`).**
`delta_i = lambda_0 + 5 eps_i + 2/q_2`, over the banked `lambda_0`.  The body is
*syntactically* the left-hand side of the third clause of
`TerminalTwoStream.terminalEntry` (`TerminalTwoStream.lean:590--591`), which is
what makes `terminalEntry_of_ownerThreshold` below a definitional bridge rather
than a re-derivation. -/
noncomputable def ownerThreshold (q₂ b₁ : ℕ) (epsI : ℝ) : ℝ :=
  DenseBranchSelection.lambdaZero q₂ b₁ + 5 * epsI + 2 / (q₂ : ℝ)

theorem lambdaZero_pos {q₂ b₁ : ℕ} (hq₂ : 0 < q₂) :
    0 < DenseBranchSelection.lambdaZero q₂ b₁ := by
  have : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂
  unfold DenseBranchSelection.lambdaZero; positivity

/-- **`09:1671`, the frozen structural readout, general form.**  "the structural
gates give `q_2 >= 16` and `lambda_0 <= 1/8`."  The second half, from the frozen
`16 q_2 <= 2^{b_1}`: `lambda_0 = 2 q_2/2^{b_1} <= 2/16 = 1/8`, over the banked
constant.  General in the two widths. -/
theorem lambdaZero_le_eighth {q₂ b₁ : ℕ} (hgate : 16 * q₂ ≤ 2 ^ b₁) :
    DenseBranchSelection.lambdaZero q₂ b₁ ≤ 1 / 8 := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
  have hgateR : (16 : ℝ) * (q₂ : ℝ) ≤ (2 : ℝ) ^ b₁ := by exact_mod_cast hgate
  unfold DenseBranchSelection.lambdaZero
  rw [div_le_div_iff₀ hpow (by norm_num)]
  linarith

/-- **`09:1670--1671`, the structural readout AS THE PAPER SUPPLIES IT.**

The frozen sentence does not posit `16 q_2 <= 2^{b_1}` locally: it says the
*structural gates* give `q_2 >= 16` and `lambda_0 <= 1/8`.  Those two facts are
already discharged from the banked Stage-2 width record by
`TerminalTwoStream.terminalEntry_of_stageTwoWidths` (`TerminalTwoStream.lean:632`),
so they are consumed by pin here rather than re-proved.  This is the declaration
`terminalEntry_of_ownerThreshold` uses at the join. -/
theorem structuralReadout (W : StageTwoRelaxed.StageTwoWidths) :
    16 ≤ W.q₂ ∧ DenseBranchSelection.lambdaZero W.q₂ W.b₁ ≤ 1 / 8 :=
  TerminalTwoStream.terminalEntry_of_stageTwoWidths W

/-- **THE BRIDGE (`09:1670--1671`).**

"`delta_i = lambda_0 + 5 eps_i + 2/q_2`, and the structural gates give
`q_2 >= 16` and `lambda_0 <= 1/8`" -- i.e. the owner threshold of
`eq:wrapper-owner-threshold` is exactly what `eq:terminal-entry` demands.  Given
the two structural clauses and `delta_i >= ownerThreshold q_2 b_1 eps_i`, the
banked `TerminalTwoStream.terminalEntry` holds.  The third clause is discharged
by `hthr` **definitionally** -- `ownerThreshold` unfolds to its left-hand side --
which is the seam this repair closes.  General in the widths and the two
reals. -/
theorem terminalEntry_of_ownerThreshold {q₂ b₁ : ℕ} {epsI δ' : ℝ}
    (hq₂ : 16 ≤ q₂) (hlam : DenseBranchSelection.lambdaZero q₂ b₁ ≤ 1 / 8)
    (hthr : ownerThreshold q₂ b₁ epsI ≤ δ') :
    TerminalTwoStream.terminalEntry q₂ b₁ epsI δ' :=
  ⟨hq₂, hlam, hthr⟩

/-- **The bridge fired from the banked width record.**  The two structural
clauses come from `structuralReadout`, so at a Stage-2 width record the *only*
remaining input to `eq:terminal-entry` is the owner threshold itself -- exactly
what `09:1670--1671` asserts. -/
theorem terminalEntry_of_ownerThreshold_widths (W : StageTwoRelaxed.StageTwoWidths)
    {epsI δ' : ℝ} (hthr : ownerThreshold W.q₂ W.b₁ epsI ≤ δ') :
    TerminalTwoStream.terminalEntry W.q₂ W.b₁ epsI δ' :=
  terminalEntry_of_ownerThreshold (structuralReadout W).1 (structuralReadout W).2 hthr

/-- **`eq:wrapper-baseline-deficit-sum` (`09:1627--1642`), proved.**

"Indeed, summing over the disjoint owner baselines charges the initial deletion at
most `delta_U q m`.  A clean route loses less than `(q-1) A_0` reference rows for
each of at most `q` owners.  Hence
`sum_i eps_i < (delta_U q m + q(q-1) A_0)/m_G <= eta_R/(16g) + eta_R/(16g) =
eta_R/(8g)`, where `delta_U q = eta_R/16` and the last inequality is the third
gate in `eq:wrapper-initial-survival`."

The two majorants are the binders they are: `hdel` is `eq:q-deltaU`'s
`delta_U q = eta_R/16` read against `m/m_G = 1/g`, and `hroute` is literally the
third row of `eq:wrapper-initial-survival` (`09:1229`).  The conclusion is the
frozen `<=` after the frozen strict `<`.  General. -/
theorem wrapperBaselineDeficitSum {ι : Type*} (J : Finset ι) (eps : ι → ℝ)
    {delTerm routeTerm etaR g : ℝ}
    (hsum : ∑ i ∈ J, eps i < delTerm + routeTerm)
    (hdel : delTerm ≤ etaR / (16 * g)) (hroute : routeTerm ≤ etaR / (16 * g)) :
    ∑ i ∈ J, eps i ≤ etaR / (8 * g) := by
  have hhalf : etaR / (16 * g) + etaR / (16 * g) = etaR / (8 * g) := by
    rcases eq_or_ne g 0 with rfl | hg
    · norm_num
    · field_simp
      ring
  linarith

/-- **`09:1690--1697`, the summed owner thresholds.**

"`sum_i delta_i <= q lambda_0 + 5 eta_R/(8g) + 2q/q_2`": each of the at most `q`
good owners contributes `lambda_0 + 2/q_2`, and the deficits sum by
`eq:wrapper-baseline-deficit-sum`.  General. -/
theorem sum_ownerThreshold_le {ι : Type*} (J : Finset ι) (eps : ι → ℝ)
    {q q₂ b₁ : ℕ} {etaR g : ℝ}
    (hcard : (J.card : ℝ) ≤ (q : ℝ)) (hq₂ : 0 < q₂)
    (hdeficit : ∑ i ∈ J, eps i ≤ etaR / (8 * g)) :
    ∑ i ∈ J, ownerThreshold q₂ b₁ (eps i)
      ≤ (q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁ + 5 * (etaR / (8 * g))
          + 2 * (q : ℝ) / (q₂ : ℝ) := by
  classical
  have hq₂R : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂
  have hlam0 : 0 ≤ DenseBranchSelection.lambdaZero q₂ b₁ := le_of_lt (lambdaZero_pos hq₂)
  have hsplit : ∑ i ∈ J, ownerThreshold q₂ b₁ (eps i)
      = (J.card : ℝ) * (DenseBranchSelection.lambdaZero q₂ b₁ + 2 / (q₂ : ℝ))
          + 5 * ∑ i ∈ J, eps i := by
    unfold ownerThreshold
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      ← Finset.mul_sum]
    ring
  have hconst : (J.card : ℝ) * (DenseBranchSelection.lambdaZero q₂ b₁ + 2 / (q₂ : ℝ))
      ≤ (q : ℝ) * (DenseBranchSelection.lambdaZero q₂ b₁ + 2 / (q₂ : ℝ)) := by
    have hnn : 0 ≤ DenseBranchSelection.lambdaZero q₂ b₁ + 2 / (q₂ : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right hcard hnn
  rw [hsplit]
  have : (q : ℝ) * (DenseBranchSelection.lambdaZero q₂ b₁ + 2 / (q₂ : ℝ))
      = (q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁ + 2 * (q : ℝ) / (q₂ : ℝ) := by ring
  linarith [hconst, hdeficit, this]

/-! ## Section 7  `09:1643--1679`: the owner transfer bound -/

/-- **`09:1643--1646` and `09:1677--1679`, the transfer bound.**

"If a different donor `j` sent protected mass at least `2 mu_P delta_i` to
`own(i)`, one of the two reservoir types would arrive there at relative density at
least `delta_i`. ... Thus `lem:terminal-two-stream` applies and makes this
restriction, and hence the owner, `C`-hard.  Therefore every such transfer is
strictly below `2 mu_P delta_i`."

The frozen contrapositive, with the terminal-lemma endpoint carried as the
implication `hTerminal` (its own status is *stated, not proved*; see
`ownerHard_of_terminalTwoStream`) and the shallow-protocol budget as the banked
`DenseWrapperFrontier.finalNode_budget_contradiction`.  General. -/
theorem ownerTransfer_lt {C r B : ℕ} {transfer deltaI : ℝ} (hC : 3 ≤ C)
    (hbudget : B + r ≤ C + r - 1)
    (hTerminal : 2 * muP * deltaI ≤ transfer → C ≤ B) :
    transfer < 2 * muP * deltaI := by
  by_contra hcon
  exact finalNode_budget_contradiction hC hbudget (hTerminal (not_lt.mp hcon))

/-- **`09:1644--1646`, the reservoir halving at the owner.**

"one of the two reservoir types would arrive there at relative density at least
`delta_i`": a transfer of at least `2 mu_P delta_i` split between two reservoirs
of mass `mu_P` each leaves one of them at relative density at least `delta_i`.
Only the counting is used (GAP-EXPOSED M3); the two-reservoir structure is an
input.  General. -/
theorem reservoir_halving_of_pair {d₀ d₁ deltaI : ℝ} (hmuP : 0 < muP)
    (h : 2 * muP * deltaI ≤ muP * d₀ + muP * d₁) :
    deltaI ≤ d₀ ∨ deltaI ≤ d₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  nlinarith [hmuP, h0, h1]

/-- **`09:1646`, the frozen legality side condition.**  "Such a transfer is
possible only when `delta_i <= 1`": a relative density never exceeds one, so a
threshold above one is unreachable.  General. -/
theorem ownerTransfer_needs_deltaI_le_one {d deltaI : ℝ} (hd : d ≤ 1)
    (h : deltaI ≤ d) : deltaI ≤ 1 := le_trans h hd

/-- **`09:1661--1677`, `lem:terminal-two-stream` consumed BY PIN.**

"These are exactly hypotheses (a)--(c) of `lem:terminal-state-realization`, ...
That lemma supplies the explicit restriction-preserving maps and makes the owner
rectangle an `(eps_i, delta_i)`-two-stream terminal state. ... Thus
`lem:terminal-two-stream` applies and makes this restriction, and hence the owner,
`C`-hard."

The banked `TerminalTwoStream.TerminalTwoStream` is a `Prop`-valued `def` whose
body is the frozen implication chain; this theorem supplies its eight antecedents
as explicit binders and returns its conclusion
`C = terminalTarget b_cap r_2 r_3 <= comp Z`.  Nothing is re-proved and nothing is
strengthened: the banked lemma is **stated, not proved**, so this is a conditional
citation only.  `hstate` is precisely the `TwoStreamState` that
`lem:terminal-state-realization` would produce -- carried as a binder because of
the binder-shape mismatch recorded as GAP-EXPOSED M2. -/
theorem ownerHard_of_terminalTwoStream
    {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw] [DecidableEq Rw]
    [Fintype Cl] [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo]
    [DecidableEq Ltwo] [Fintype Rone] [DecidableEq Rone]
    (W : StageTwoRelaxed.StageTwoWidths)
    (q s mT dT bcap r₃ bT Lh vmax : ℕ) (Nmat : Rw → Cl → Bool)
    (Mmat : Cone → Rone → Bool) (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (rho : Slot s → Om → Slot W.q₂ × Cone) (YT : Slot s → Finset Cl)
    (zeta : Slot s → Cl → Ltwo) (XZ : Finset (Slot q × Rw))
    (YZ : Finset (Slot q → Cl)) (lamT eps2 epsProd xT y ε δ' : ℝ)
    (hTTS : TerminalTwoStream.TerminalTwoStream W q s mT dT bcap r₃ bT Lh vmax Nmat
      Mmat cFam Stwo RG RSig RD omg rho YT zeta XZ YZ lamT eps2 epsProd xT y ε δ')
    (hs : s = 2 ^ r₃) (hxT : xT = DenseStageFourOpening.xTdepth bT) (hy : y = 3 / 5)
    (hstate : TwoStreamState.TwoStreamState q s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (hentry : TerminalTwoStream.terminalEntry W.q₂ W.b₁ ε δ')
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT y)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ → W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂ (DenseWeightedCount.stoppingCapacity W.r₂ d)) :
    TerminalTwoStream.terminalTarget bcap W.r₂ r₃ ≤ D (subgame (interlaceFun Nmat q) XZ YZ) :=
  hTTS hs hxT hy hstate hentry hseed hfixed hcalls

/-- **THE JOIN (`09:1670--1677`): the owner-threshold half composed with the
terminal-lemma half.**

"`delta_i = lambda_0 + 5 eps_i + 2/q_2`, and the structural gates give
`q_2 >= 16` and `lambda_0 <= 1/8`. ... Thus `lem:terminal-two-stream` applies and
makes this restriction, and hence the owner, `C`-hard."

This is `ownerHard_of_terminalTwoStream` with its `eq:terminal-entry` argument
*produced* from the owner threshold of `eq:wrapper-owner-threshold` through
`terminalEntry_of_ownerThreshold_widths`, rather than assumed alongside it.  The
only entry input left is `hthr : ownerThreshold W.q_2 W.b_1 eps_i <= delta_i` --
exactly the frozen `delta_i >= lambda_0 + 5 eps_i + 2/q_2`.  The elaborated
application is the evidence that the two halves of this block compose: if the
owner-threshold constant and the banked `lambda_0` had drifted apart, this
declaration would not typecheck.  The conclusion inherits the *stated, not
proved* status of the banked terminal lemma and nothing here upgrades it. -/
theorem ownerHard_of_ownerThreshold
    {Rw Cl Om Cone Ltwo Rone : Type*} [Fintype Rw] [DecidableEq Rw]
    [Fintype Cl] [DecidableEq Cl] [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo]
    [DecidableEq Ltwo] [Fintype Rone] [DecidableEq Rone]
    (W : StageTwoRelaxed.StageTwoWidths)
    (q s mT dT bcap r₃ bT Lh vmax : ℕ) (Nmat : Rw → Cl → Bool)
    (Mmat : Cone → Rone → Bool) (cFam : Ltwo → Slot W.q₂ → Rone)
    (Stwo : Ltwo → Slot W.q₂ × Cone → Bool) (RG RSig RD : Finset Rw) (omg : Rw → Om)
    (rho : Slot s → Om → Slot W.q₂ × Cone) (YT : Slot s → Finset Cl)
    (zeta : Slot s → Cl → Ltwo) (XZ : Finset (Slot q × Rw))
    (YZ : Finset (Slot q → Cl)) (lamT eps2 epsProd xT y epsI deltaI : ℝ)
    (hTTS : TerminalTwoStream.TerminalTwoStream W q s mT dT bcap r₃ bT Lh vmax Nmat
      Mmat cFam Stwo RG RSig RD omg rho YT zeta XZ YZ lamT eps2 epsProd xT y epsI deltaI)
    (hs : s = 2 ^ r₃) (hxT : xT = DenseStageFourOpening.xTdepth bT) (hy : y = 3 / 5)
    (hstate : TwoStreamState.TwoStreamState q s W.q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT epsI deltaI)
    (hthr : ownerThreshold W.q₂ W.b₁ epsI ≤ deltaI)
    (hseed : TerminalTwoStream.terminalSeedInputs Mmat Stwo W.b₁ bcap W.r₂ r₃ bT xT y)
    (hfixed : TerminalTwoStream.ExtensionCallTwoFixedWidth W cFam bcap Lh vmax eps2 epsProd)
    (hcalls : ∀ d : ℕ, d ≤ W.r₂ → W.t₂ ≤ DenseWeightedCount.stoppingCapacity W.r₂ d →
      TerminalTwoStream.extensionCallTwo W.q₂ W.t₂ (DenseWeightedCount.stoppingCapacity W.r₂ d)) :
    TerminalTwoStream.terminalTarget bcap W.r₂ r₃ ≤ D (subgame (interlaceFun Nmat q) XZ YZ) :=
  ownerHard_of_terminalTwoStream W q s mT dT bcap r₃ bT Lh vmax Nmat Mmat cFam Stwo
    RG RSig RD omg rho YT zeta XZ YZ lamT eps2 epsProd xT y epsI deltaI hTTS hs hxT hy
    hstate (terminalEntry_of_ownerThreshold_widths W hthr) hseed hfixed hcalls

/-! ## Section 8  `eq:wrapper-owner-gates` and `eq:wrapper-good-to-good`
(`09:1681--1699`) -/

/-- **`eq:wrapper-owner-gates` (`09:1682--1689`).**

"The schedule imposes `2 mu_P q lambda_0 <= eta_R/16`, `mu_P <= g/20`,
`q_2 >= 64 mu_P q/eta_R`."

Transcribed as a predicate and **asserted nowhere**: `06:1213--1218` lists
`eq:wrapper-owner-gates` among the finite parameter conditions the effective
cutoff discharges, and `09:256--258` assumes it in `thm:first-wrapper`. -/
def wrapperOwnerGates (q q₂ : ℕ) (etaR g : ℝ) (b₁ : ℕ) : Prop :=
  2 * muP * (q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁ ≤ etaR / 16
    ∧ muP ≤ g / 20
    ∧ 64 * muP * (q : ℝ) / etaR ≤ (q₂ : ℝ)

/-- **`09:1685`, checked at the frozen constants.**  The middle gate
`mu_P <= g/20` holds outright at the frozen `mu_P = 1/184` (`09:1372`, banked)
and the frozen base-row fraction `g = 91/92` (`09:297`, banked): it is a checked
identity, which is why `09:257--258` says the clauses "are verified by
`eq:stage2-structural-gates` and the fixed duplication masses". -/
theorem muP_le_g_div_twenty : muP ≤ (91 / 92 : ℝ) / 20 := by
  norm_num [muP]

/-- **`eq:wrapper-good-to-good` (`09:1690--1699`), proved.**

"Using `eq:wrapper-baseline-deficit-sum`, each good donor therefore sends to all
other good owners total mass less than
`2 mu_P sum_i delta_i <= 2 mu_P (q lambda_0 + 5 eta_R/(8g) + 2q/q_2)
<= 3 eta_R/16 < eta_R/4`."

Both inequalities, with the frozen constant `3 eta_R/16` produced rather than
posited: the three gates of `eq:wrapper-owner-gates` contribute `eta_R/16` each.
The middle contribution is where `mu_P <= g/20` is load-bearing --
`2 mu_P * 5 eta_R/(8g) = (5/4)(mu_P/g) eta_R <= eta_R/16`.  General in `etaR`,
`g` and the summed thresholds. -/
theorem wrapperGoodToGood {q q₂ b₁ : ℕ} {etaR g Sdelta : ℝ}
    (hetaR : 0 < etaR) (hg : 0 < g) (hq₂ : 0 < q₂)
    (hgates : wrapperOwnerGates q q₂ etaR g b₁)
    (hS : Sdelta ≤ (q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁ + 5 * (etaR / (8 * g))
      + 2 * (q : ℝ) / (q₂ : ℝ)) :
    2 * muP * Sdelta ≤ 3 * etaR / 16 ∧ 3 * etaR / 16 < etaR / 4 := by
  obtain ⟨g1, g2, g3⟩ := hgates
  have hmuP0 : 0 < muP := muP_pos
  have hq₂R : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂
  -- second contribution: `2 mu_P * 5 eta_R/(8 g) <= eta_R/16`
  have hmid : 2 * muP * (5 * (etaR / (8 * g))) ≤ etaR / 16 := by
    have hmg : muP * 20 ≤ g := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 20)] at g2
      linarith
    have hstep : 2 * muP * (5 * (etaR / (8 * g))) = (10 * muP * etaR) / (8 * g) := by
      field_simp; ring
    rw [hstep, div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * g) (by norm_num : (0:ℝ) < 16)]
    nlinarith [hmuP0, hetaR, hg, hmg]
  -- third contribution: `2 mu_P * 2 q / q_2 <= eta_R/16`
  have hthird : 2 * muP * (2 * (q : ℝ) / (q₂ : ℝ)) ≤ etaR / 16 := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hkey : 64 * muP * (q : ℝ) ≤ (q₂ : ℝ) * etaR := by
      rw [div_le_iff₀ hetaR] at g3
      linarith
    have hstep : 2 * muP * (2 * (q : ℝ) / (q₂ : ℝ)) = (4 * muP * (q : ℝ)) / (q₂ : ℝ) := by
      field_simp; ring
    rw [hstep, div_le_div_iff₀ hq₂R (by norm_num : (0:ℝ) < 16)]
    linarith
  have hfirst : 2 * muP * ((q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁) ≤ etaR / 16 := by
    have : 2 * muP * (q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁
        = 2 * muP * ((q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁) := by
      ring
    linarith [g1, this]
  constructor
  · have hmul : 2 * muP * Sdelta
        ≤ 2 * muP * ((q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁ + 5 * (etaR / (8 * g))
            + 2 * (q : ℝ) / (q₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have hexp : 2 * muP * ((q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁
        + 5 * (etaR / (8 * g)) + 2 * (q : ℝ) / (q₂ : ℝ))
        = 2 * muP * ((q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁)
          + 2 * muP * (5 * (etaR / (8 * g)))
          + 2 * muP * (2 * (q : ℝ) / (q₂ : ℝ)) := by ring
    linarith [hmul, hexp ▸ hmul, hfirst, hmid, hthird]
  · linarith

/-! ## Section 9  The pigeonhole layer (`09:1700--1713`) -/

/-- **`09:1700--1701`.**  "Together with `eq:wrapper-mass-leaves-owner`, this says
that every good donor sends more than `eta_R/4` protected mass to exceptional
final nodes."  The residual after subtracting the good-to-good part.  General. -/
theorem goodDonor_to_exceptional_gt {etaR total toGood toExc : ℝ}
    (hetaR : 0 < etaR) (hleaves : etaR / 2 < total) (hsplit : total = toGood + toExc)
    (hgood : toGood ≤ 3 * etaR / 16) :
    etaR / 4 < toExc := by
  rw [hsplit] at hleaves
  linarith

/-- **`09:1702`.**  "If `e_T = 0`, this is already a contradiction": a strictly
positive mass cannot be distributed over an empty set of exceptional nodes.
General. -/
theorem exceptional_nonempty_of_positive_mass {ι : Type*} (T : Finset ι) (mss : ι → ℝ)
    {etaR : ℝ} (hetaR : 0 < etaR) (hpos : etaR / 4 < ∑ v ∈ T, mss v) :
    T.Nonempty := by
  rcases Finset.eq_empty_or_nonempty T with rfl | h
  · simp at hpos; linarith
  · exact h

/-- **`09:1704--1707`, the fibre pigeonhole.**

"For each good donor choose an exceptional node receiving more than
`eta_R/(4 e_T)` of its protected mass.  Some exceptional node `T_*` is chosen by
at least `|J_good|/e_T` donors."

The general averaging fact: for a choice map from `J` into a nonempty finite set
`T`, some fibre has at least `|J|/|T|` elements.  General in both index types. -/
theorem exists_heavy_fibre {ι κ : Type*} [DecidableEq κ] (J : Finset ι) (choice : ι → κ)
    (T : Finset κ) (hmaps : ∀ j ∈ J, choice j ∈ T) (hT : T.Nonempty) :
    ∃ t ∈ T, (J.card : ℝ) ≤ (T.card : ℝ) * ((J.filter fun j => choice j = t).card : ℝ) := by
  classical
  by_contra hcon
  push Not at hcon
  have hfib : J.card = ∑ t ∈ T, (J.filter fun j => choice j = t).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hstrict : ∑ t ∈ T, ((J.filter fun j => choice j = t).card : ℝ)
      < ∑ _t ∈ T, (J.card : ℝ) / (T.card : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hT ?_
    intro t ht
    have hTcard : (0 : ℝ) < (T.card : ℝ) := by
      have := Finset.card_pos.mpr hT
      exact_mod_cast this
    have := hcon t ht
    rw [lt_div_iff₀ hTcard]
    linarith
  have hTcard : (0 : ℝ) < (T.card : ℝ) := by
    have := Finset.card_pos.mpr hT
    exact_mod_cast this
  have hrhs : ∑ _t ∈ T, (J.card : ℝ) / (T.card : ℝ) = (J.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hlhs : ∑ t ∈ T, ((J.filter fun j => choice j = t).card : ℝ) = (J.card : ℝ) := by
    rw [← Nat.cast_sum, ← hfib]
  rw [hlhs, hrhs] at hstrict
  exact lt_irrefl _ hstrict

/-- **`eq:wrapper-terminal-density` (`09:1710--1713`).**
`delta_0 = eta_R/(8 e_T mu_P)`. -/
noncomputable def deltaZero (etaR : ℝ) (eT : ℕ) : ℝ := etaR / (8 * (eT : ℝ) * muP)

theorem deltaZero_pos {etaR : ℝ} {eT : ℕ} (hetaR : 0 < etaR) (heT : 0 < eT) :
    0 < deltaZero etaR eT := by
  have : (0 : ℝ) < (eT : ℝ) := by exact_mod_cast heT
  have := muP_pos
  unfold deltaZero; positivity

/-- **`09:1707--1713`, the density read-off.**

"One common reservoir type accounts for at least half of those donors; for each
selected donor its density at `T_*` is at least `delta_0 = eta_R/(8 e_T mu_P)`."

From the frozen per-donor mass `> eta_R/(4 e_T)`: halving between the two
reservoir types (GAP-EXPOSED M3, only its counting used) leaves at least
`eta_R/(8 e_T)`, and dividing by the reservoir mass `mu_P` turns that absolute
mass into the relative density `delta_0`.  General. -/
theorem deltaZero_of_pigeonhole {etaR massAt d₀ : ℝ} {eT : ℕ}
    (hetaR : 0 < etaR) (heT : 0 < eT)
    (hmass : etaR / (4 * (eT : ℝ)) < massAt)
    (hhalf : massAt / 2 ≤ muP * d₀) :
    deltaZero etaR eT ≤ d₀ := by
  have heTR : (0 : ℝ) < (eT : ℝ) := by exact_mod_cast heT
  have hmuP : 0 < muP := muP_pos
  have hstep : etaR / (8 * (eT : ℝ)) ≤ muP * d₀ := by
    have : etaR / (8 * (eT : ℝ)) = (etaR / (4 * (eT : ℝ))) / 2 := by
      field_simp; ring
    rw [this]
    linarith
  unfold deltaZero
  rw [div_le_iff₀ (by positivity)]
  have hexp : etaR / (8 * (eT : ℝ)) * (8 * (eT : ℝ)) = etaR := by field_simp
  nlinarith [hstep, heTR, hmuP]

/-! ## Section 10  The schedule layer (`09:1715--1744`)

`E_B`, `E_T`, `delta_term` and `u_term` are `eq:terminal-uniform-bounds`
(`06:715--730`) and are **already reified** in the banked
`ParameterSchedule`; they are consumed by pin here and defined nowhere in this
module.  `vartheta` likewise: the banked `DenseWrapperFrontier.vartheta` of the
`eq:wrapper-clean-count` side and the `ParameterSchedule.vartheta` of the
`eq:terminal-uniform-bounds` side are the same frozen `9/16`, recorded once
below so the two sides cannot drift. -/

/-- **Pin (`eq:terminal-uniform-bounds`, `06:718`: `vartheta = 9/16`).**

The frozen split constant occurs on both sides of this block -- inside
`eq:wrapper-clean-count`'s `K_B <= e_0/(1 - vartheta)` (banked in
`DenseWrapperFrontier`) and inside `E_B`/`E_T` (banked in `ParameterSchedule`)
-- and the two spellings are checked equal here rather than assumed to agree.
A seam test, not a definition: this module introduces no `vartheta`. -/
theorem vartheta_pin : vartheta = ParameterSchedule.vartheta := rfl

/-- **`09:1727--1731`, the legality of dividing by `E_T`.**

"Moreover `theta <= 1/160 < 18/25`, so `B_ref >= 2`; since `t_ref >= 4`,
`eq:cover-bounds` and `eq:terminal-uniform-bounds` give `e_0^max >= 1` and
`E_T >= 1`.  Thus the division by `E_T` below is legal."

The frozen chain, with `e_0^max >= 1` supplied as the binder it is (its own
derivation is the `06:639--653` cover search, banked as
`ParameterSchedule.e0maxSched`) and `E_T >= 1` produced.  Stated over the
banked `ParameterSchedule.ET`, whose two arguments are the frozen
`ceil(e_0^max/(1 - vartheta))` summand and `E_B`. -/
theorem one_le_ET_of_e0Max_pos {e0m EBv : ℕ} (he0 : 1 ≤ e0m) :
    1 ≤ ParameterSchedule.ET e0m EBv := by
  have hv : (1 : ℝ) - ParameterSchedule.vartheta = 7 / 16 :=
    ParameterSchedule.one_sub_vartheta
  have he0R : (1 : ℝ) ≤ (e0m : ℝ) := by exact_mod_cast he0
  have hpos : (1 : ℝ) ≤ (e0m : ℝ) / (1 - ParameterSchedule.vartheta) := by
    rw [hv]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 7/16)]
    linarith
  have : 1 ≤ ⌈(e0m : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ :=
    Nat.one_le_ceil_iff.mpr (by linarith)
  rw [ParameterSchedule.ET]
  omega

/-- **`09:1719--1726`, the derived good-donor count.**

"The size of `J_good` is not a schedule input.  It is a derived fact: by
`eq:wrapper-clean-count`, `eq:wrapper-bob-heavy-count`, `eq:cover-bounds`, and
`eq:terminal-uniform-bounds`,
`|J_good| = c - e_B >= q - ceil(e_0^max/(1-vartheta)) - E_B = q - E_T`."

The frozen arithmetic, with the two majorant steps as the binders they are.
General. -/
theorem goodDonorCount_ge {jgood c eB q ceilTerm EBr : ℝ}
    (hjgood : jgood = c - eB) (hc : q - ceilTerm ≤ c) (heB : eB ≤ EBr) :
    q - (ceilTerm + EBr) ≤ jgood := by
  rw [hjgood]; linarith

/-- **`eq:wrapper-terminal-donor-gate` (`09:1732--1741`), proved.**

"The first gate in `eq:terminal-wrapper-gates` gives `E_T <= q/8`, whereas its
second gate and `u_don <= u_term` give the other inequality below.  Consequently
the proof has `|J_good| > q/2`, `q/(4 E_T) > u_don B_theta`."

Both clauses.  The first: `|J_good| >= q - E_T >= q - q/8 = 7q/8 > q/2`, where
`q > 0` is *derived* from `E_T > 0` and the first gate rather than assumed -- a
separate `0 < q` binder would restate a derived fact.  The second:
`q > 4 E_T u_term B_theta >= 4 E_T u_don B_theta` and `E_T > 0`.  General in all
five reals. -/
theorem wrapperTerminalDonorGate {q ETr uDon uTerm Bt jgood : ℝ}
    (hET : 0 < ETr) (hBt : 0 < Bt)
    (hgate1 : 8 * ETr ≤ q) (hgate2 : 4 * ETr * uTerm * Bt < q)
    (huT : uDon ≤ uTerm)
    (hjgood : q - ETr ≤ jgood) :
    q / 2 < jgood ∧ uDon * Bt < q / (4 * ETr) := by
  constructor
  · have : ETr ≤ q / 8 := by linarith
    linarith
  · have h1 : (0 : ℝ) ≤ 4 * ETr := by linarith
    have hstep : 4 * ETr * uDon ≤ 4 * ETr * uTerm := mul_le_mul_of_nonneg_left huT h1
    have hmono : 4 * ETr * uDon * Bt ≤ 4 * ETr * uTerm * Bt :=
      mul_le_mul_of_nonneg_right hstep (le_of_lt hBt)
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < 4 * ETr)]
    nlinarith [hmono, hgate2]

/-- **`09:1742--1744`, the impossibility of `delta_0 >= 1`.**

"If `delta_0 >= 1`, the strict pigeonhole conclusion preceding
`eq:wrapper-terminal-density` is itself impossible.  We may therefore assume
`delta_0 < 1`."

A relative density never exceeds one, and the pigeonhole produced a *strict*
excess; so a threshold at or above one is unreachable.  General. -/
theorem deltaZero_lt_one_of_density {etaR d₀ : ℝ} {eT : ℕ}
    (hd1 : d₀ ≤ 1) (hstrict : d₀ < deltaZero etaR eT → False) :
    deltaZero etaR eT ≤ 1 := by
  by_contra hcon
  push Not at hcon
  exact hstrict (lt_of_le_of_lt hd1 hcon)

/-- **`09:1744`, "hence `u_don >= 8s`".**

`u_don` is the least power of two with `u_don delta_0 >= 8s`
(`06:1716--1718`); at `delta_0 <= 1` that forces `u_don >= 8s` outright.
General. -/
theorem uDon_ge_eight_s {s uDon : ℕ} {delta0 : ℝ}
    (hd1 : delta0 ≤ 1) (hdef : 8 * (s : ℝ) ≤ (uDon : ℝ) * delta0) :
    8 * s ≤ uDon := by
  have hu : (0 : ℝ) ≤ (uDon : ℝ) := Nat.cast_nonneg uDon
  have hstep : (uDon : ℝ) * delta0 ≤ (uDon : ℝ) := by nlinarith [hd1, hu]
  have : ((8 * s : ℕ) : ℝ) ≤ ((uDon : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-! ## Section 11  The final Extension call (`09:1746--1781`) -/

/-- **`09:1746--1749`, the surviving donors.**

"Apply the poor-`u_don` projection cover to the donors feeding `T_*`.  By
`eq:wrapper-terminal-donor-gate`, it leaves `u_don` donors whose joint outer
projection has density at least `rho_0`."

The counting content: the banked `WrapperProjectionCovers.productProjectionCover`
removes at most `u_don (B_theta - 1)` coordinates, and the donor count exceeds
`u_don B_theta`, so at least `u_don` donors survive.  The cover itself is
consumed by pin.  General. -/
theorem donors_survive_cover {donors coverSize uDon Bt : ℝ}
    (hcover : coverSize ≤ uDon * (Bt - 1)) (hdonors : uDon * Bt < donors) :
    uDon ≤ donors - coverSize := by
  nlinarith [hcover, hdonors]

/-- **`06:1157`, row (iv)'s entering column density.**  `h = rho_0 2^{-u_don-1}`,
at `u_don = 2^e` and the banked `rho_0 = 99/100`.  The analogue of the banked
`callThreeH` at row (iii)'s `rho_1`; the frozen rows differ exactly in that
base. -/
noncomputable def callFourH (e : ℕ) : ℝ := rhoZero / 2 ^ (2 ^ e + 1)

theorem callFourH_pos (e : ℕ) : 0 < callFourH e := by
  have := rhoZero_pos
  unfold callFourH; positivity

theorem callFourH_le_one (e : ℕ) : callFourH e ≤ 1 := by
  have h0 := rhoZero_lt_one
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (2 ^ e + 1) := one_le_pow₀ (by norm_num)
  unfold callFourH
  rw [div_le_one (by positivity)]
  linarith

/-- **Aux 11.1.**  Row (iv)'s density is strictly below row (iii)'s base ratio at
the same width, which is the frozen difference between `rho_0` and
`rho_1 = rho_0/2`: `callFourH e = 2 * callThreeH e`.  A checked identity tying
the two rows together, so that the two entering densities cannot silently
drift. -/
theorem callFourH_eq_two_mul_callThreeH (e : ℕ) :
    callFourH e = 2 * callThreeH e := by
  unfold callFourH callThreeH rhoOne
  rw [pow_succ]
  field_simp

/-- **`eq:wrapper-terminal-block-supply` (`09:1756--1765`), proved.**

"For each selected donor, partition its protected rows by their Stage-2
coordinate. ... Averaging these `q_2` parts gives at least `delta_0 q_2/2`
represented Stage-2 outer blocks whose surviving `C_1`-density is at least
`delta_0/2`.  Across all donors there are at least
`u_don delta_0 q_2/4 >= 2 s q_2` represented blocks satisfying this row-density
threshold."

Both the product `(u_don/2)(delta_0 q_2/2) = u_don delta_0 q_2/4` and the frozen
comparison against `2 s q_2`, the latter from `u_don delta_0 >= 8s`.  General in
all four quantities. -/
theorem terminalBlockSupply {s q₂ uDon : ℕ} {delta0 perDonor : ℝ}
    (hu : 2 ∣ uDon)
    (hud : 8 * (s : ℝ) ≤ (uDon : ℝ) * delta0)
    (hper : delta0 * (q₂ : ℝ) / 2 ≤ perDonor) :
    2 * (s : ℝ) * (q₂ : ℝ) ≤ ((uDon / 2 : ℕ) : ℝ) * perDonor := by
  have hhalf : ((uDon / 2 : ℕ) : ℝ) * 2 = (uDon : ℝ) := by
    obtain ⟨c, hc⟩ := hu
    subst hc
    have hc2 : 2 * c / 2 = c := by omega
    rw [hc2]; push_cast; ring
  have hnn : (0 : ℝ) ≤ ((uDon / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul : ((uDon / 2 : ℕ) : ℝ) * (delta0 * (q₂ : ℝ) / 2)
      ≤ ((uDon / 2 : ℕ) : ℝ) * perDonor := mul_le_mul_of_nonneg_left hper hnn
  have hstep : ((uDon / 2 : ℕ) : ℝ) * (delta0 * (q₂ : ℝ) / 2)
      = ((uDon : ℝ) * delta0) * (q₂ : ℝ) / 4 := by
    rw [← hhalf]; ring
  have hq₂ : (0 : ℝ) ≤ (q₂ : ℝ) := Nat.cast_nonneg q₂
  nlinarith [hmul, hstep, hud, hq₂]

/-- **`09:1767`, the frozen terminal capacity.**  `kappa = 2 s q_2`, which is the
banked `WrapperProtectedEarly.Kint` at `kappa = 2` -- the same represented-block
count with the frozen row-(iv) capacity substituted, and therefore not a new
constant. -/
def terminalCapacity (s q₂ : ℕ) : ℕ := Kint s 2 q₂

theorem terminalCapacity_eq (s q₂ : ℕ) : terminalCapacity s q₂ = 2 * s * q₂ := by
  unfold terminalCapacity Kint; ring

theorem terminalCapacity_dyadic (r₃ r₂ : ℕ) :
    terminalCapacity (2 ^ r₃) (2 ^ r₂) = 2 ^ (r₃ + 1 + r₂) := by
  unfold terminalCapacity Kint
  rw [show (2 : ℕ) ^ r₃ * 2 = 2 ^ (r₃ + 1) by rw [pow_succ], ← pow_add]

/-- **`09:1768--1770`, the ambient-width inequality.**

"Because `u_don >= 8s`, the ambient width `(u_don/2) q_2` is at least `2 kappa`,
so `r' = kappa/t_2` is legal."

The frozen comparison at `kappa = 2 s q_2`, with `u_don >= 8s` the exact
hypothesis printed.  Note the constant: row (iii) needed `4 K_int` (banked
`ambient_width_ge`), row (iv) needs `2 kappa`; the two are different frozen
demands and neither is used for the other.  General. -/
theorem terminal_ambient_width_ge {s q₂ uDon : ℕ} (hu : 2 ∣ uDon) (hs : 8 * s ≤ uDon) :
    2 * terminalCapacity s q₂ ≤ (uDon / 2) * q₂ := by
  have hhalf : 4 * s ≤ uDon / 2 := by omega
  calc 2 * terminalCapacity s q₂ = (4 * s) * q₂ := by rw [terminalCapacity_eq]; ring
    _ ≤ (uDon / 2) * q₂ := Nat.mul_le_mul_right _ hhalf

/-- **`06:1154--1159` with `06:1107--1130`, `06:1161--1162` and
`eq:contract-extension-exponents` (`D:746--764`), transcribed in full.**

Row (iv) of `sec:extension-call-ledger`, "Exceptional terminal recipient (the
final application in `sec:wrapper-mass-redistribution`)":
`v = u_don/2`, `K = 2 s q_2`, `h = rho_0 2^{-u_don-1}`, `a^sharp = 0`, and "The
donor average supplies per-block row density at least `delta_0/2`, again at least
`K 2^{-b_1}` by the structural gates."  The common binders are `06:1107--1113`
and the remaining integer binders `r = q_amb/t_2`, `r' = K/t_2` are
`06:1122--1125`.

`D:746--764` additionally demands that the call record **exhibit** natural numbers
`T, R, R_loc` with `t_2 = 2^T`, `q_amb = 2^{R+T}`, `K = 2^{R_loc+T}`,
`R_loc <= R`, and closes with the explicit warning that recording only
divisibility "does not discharge `eq:contract-extension-exponents`"; the three
exponents are therefore index parameters and the three equalities are fields.
`D:761--762`'s power-of-two product count is `u_don/2 = 2^{e-1}`.

This is a **record of the call's binders**, not a claim that Localized Extension
holds: the corollary's endpoint enters `terminalCall_contradiction` as the
separate named implication `hExtension`.  Modelled on the banked
`WrapperProtectedEarly.ExtensionCallThree`, with row (iv)'s three frozen
differences: the base of `h` (`rho_0`, not `rho_1`), the per-block row density
(`delta_0/2`, not `d_cls/4`), and the ambient-width demand (`2 kappa`, not
`4 K_int`). -/
structure ExtensionCallFour (T R Rloc b₁ e r₂ r₃ : ℕ) (delta0 colDens : ℝ) : Prop where
  /-- `09:1744`: `u_don >= 8s`, at `u_don = 2^e` and `s = 2^{r_3}`. -/
  uDon_lower : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e
  /-- `09:1762`: the block supply `u_don delta_0 >= 8s`. -/
  block_supply : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e * delta0
  /-- `09:1749--1752` and `D:761--762`: `u_don = 2^e` with `16 | u_don`, hence
  `4 | u_don` (which `lem:template-coordinate-extraction` needs) and
  `u_don/2 = 2^{e-1}`. -/
  four_le_e : 4 ≤ e
  /-- `A:117`: `t = t_2 = 2^T` is divisible by `16`. -/
  four_le_T : 4 ≤ T
  /-- `D:751`: `q_amb = (u_don/2) q_2 = 2^{R+T}`. -/
  ambient_exponent : R + T = (e - 1) + r₂
  /-- `D:752`: `K = kappa = 2 s q_2 = 2^{R_loc+T}`. -/
  capacity_exponent : Rloc + T = r₃ + 1 + r₂
  /-- `D:753`: `R_loc <= R`, i.e. `A:125`'s `r' <= r`. -/
  rloc_le_r : Rloc ≤ R
  /-- `09:1768--1770`: the ambient product width is at least `2 kappa`, so
  "`r' = kappa/t_2` is legal". -/
  ambient_width : 2 * terminalCapacity (2 ^ r₃) (2 ^ r₂) ≤ 2 ^ (e - 1) * 2 ^ r₂
  /-- `06:1158--1159`: the structural-gate comparison `delta_0/2 >= K 2^{-b_1}`,
  with `x = 2^{-b_1}` from `eq:extension-common-binders`. -/
  row_density_gate : ((2 : ℝ) ^ (r₃ + 1 + r₂)) / 2 ^ b₁ ≤ delta0 / 2
  /-- `06:1157` and `A:141` at `a^sharp = 0`: the entering column density is
  `h = rho_0 2^{-u_don-1}` and the selected child retains at least
  `h 2^{-a^sharp} = h`. -/
  column_density : callFourH e / 2 ^ (0 : ℕ) ≤ colDens

theorem ExtensionCallFour.one_le_r' {T R Rloc b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (_h : ExtensionCallFour T R Rloc b₁ e r₂ r₃ delta0 colDens) :
    1 ≤ (2 : ℕ) ^ Rloc := Nat.one_le_two_pow

theorem ExtensionCallFour.r'_le_r {T R Rloc b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (h : ExtensionCallFour T R Rloc b₁ e r₂ r₃ delta0 colDens) :
    (2 : ℕ) ^ Rloc ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) h.rloc_le_r

/-- **Aux 11.2 (`D:756`).**  `q_amb = r t` at the recorded exponents. -/
theorem ExtensionCallFour.ambient_eq {T R Rloc b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (h : ExtensionCallFour T R Rloc b₁ e r₂ r₃ delta0 colDens) :
    (2 : ℕ) ^ R * 2 ^ T = 2 ^ (e - 1) * 2 ^ r₂ := by
  rw [← pow_add, h.ambient_exponent, pow_add]

/-- **Aux 11.3 (`D:752`).**  `K = r' t` at the recorded exponents, with `K` the
frozen `kappa = 2 s q_2`. -/
theorem ExtensionCallFour.capacity_eq {T R Rloc b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (h : ExtensionCallFour T R Rloc b₁ e r₂ r₃ delta0 colDens) :
    (2 : ℕ) ^ Rloc * 2 ^ T = terminalCapacity (2 ^ r₃) (2 ^ r₂) := by
  rw [← pow_add, h.capacity_exponent, terminalCapacity_dyadic]

theorem ExtensionCallFour.capacity_dvd {T R Rloc b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (h : ExtensionCallFour T R Rloc b₁ e r₂ r₃ delta0 colDens) :
    (2 : ℕ) ^ T ∣ terminalCapacity (2 ^ r₃) (2 ^ r₂) := by
  rw [← h.capacity_eq]
  exact dvd_mul_left _ _

/-- **Aux 11.4 (`06:1128--1130`, `09:1767` and `A:138`).**  The exact output-size
equation `|Q_s| = r' p_seed = 9K/16`, i.e. "select exactly `9 kappa/16` of these
blocks", at the recorded exponents and without truncation: `16 | t_2` is what
makes both sides integral. -/
theorem ExtensionCallFour.selected_count {T R Rloc b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (h : ExtensionCallFour T R Rloc b₁ e r₂ r₃ delta0 colDens) :
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

/-- **Aux 11.5 (`lem:template-coordinate-extraction`'s width guard).**
`4 | u_don` at `u_don = 2^e`, supplied by `four_le_e`. -/
theorem ExtensionCallFour.four_dvd_uDon {T R Rloc b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (h : ExtensionCallFour T R Rloc b₁ e r₂ r₃ delta0 colDens) :
    (4 : ℕ) ∣ 2 ^ e := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact pow_dvd_pow 2 (by have := h.four_le_e; omega)

/-- **`09:1746--1770`, row (iv) CONSTRUCTED from schedule data.**

The record is never assumed: given the frozen dyadic widths, the block supply
`u_don delta_0 >= 8s` of `eq:wrapper-terminal-block-supply`, the width floor
`u_don >= 8s` of `09:1744`, the structural row-density gate and the produced
column density, all ten fields are discharged.  This is what `D:762--764` demands
when it warns that recording divisibility alone does not discharge
`eq:contract-extension-exponents`. -/
theorem extensionCallFour_of_width {T b₁ e r₂ r₃ : ℕ} {delta0 colDens : ℝ}
    (hT : 4 ≤ T) (he : 4 ≤ e) (hwidth : r₃ + 3 ≤ e) (hTe : T ≤ r₃ + 1 + r₂)
    (hlow : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e)
    (hsupply : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e * delta0)
    (hgate : ((2 : ℝ) ^ (r₃ + 1 + r₂)) / 2 ^ b₁ ≤ delta0 / 2)
    (hcol : callFourH e / 2 ^ (0 : ℕ) ≤ colDens) :
    ExtensionCallFour T ((e - 1) + r₂ - T) (r₃ + 1 + r₂ - T) b₁ e r₂ r₃ delta0 colDens where
  uDon_lower := hlow
  block_supply := hsupply
  four_le_e := he
  four_le_T := hT
  ambient_exponent := by omega
  capacity_exponent := by omega
  rloc_le_r := by omega
  ambient_width := by
    have hpow : (2 : ℕ) ^ (r₃ + 1 + r₂ + 1) ≤ 2 ^ ((e - 1) + r₂) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * terminalCapacity (2 ^ r₃) (2 ^ r₂)
        = 2 ^ (r₃ + 1 + r₂ + 1) := by rw [terminalCapacity_dyadic, pow_succ]; ring
      _ ≤ 2 ^ ((e - 1) + r₂) := hpow
      _ = 2 ^ (e - 1) * 2 ^ r₂ := by rw [pow_add]
  row_density_gate := hgate
  column_density := hcol

/-- **`09:1774--1779`, the endpoint identity, proved.**

"Its conclusion at `T_*` is
`B_cap + log_2 kappa = B_cap + log_2 q_2 + log_2 s + 1 = C`."

At the frozen dyadic widths `s = 2^{r_3}`, `q_2 = 2^{r_2}` and `kappa = 2 s q_2`
the exponent of `kappa` is `r_3 + 1 + r_2`, and `C` is the banked
`TerminalTwoStream.terminalTarget b_cap r_2 r_3 = D_2 + log_2 s + 1` with
`D_2 = B_cap + log_2 q_2` (`DenseBranchSelection.Dtwo`, consumed by pin).
Written subtraction-free.  General in the three exponents. -/
theorem terminalEndpoint_identity (bcap r₂ r₃ : ℕ) :
    bcap + (r₃ + 1 + r₂) = TerminalTwoStream.terminalTarget bcap r₂ r₃ := by
  simp [TerminalTwoStream.terminalTarget, DenseBranchSelection.Dtwo]
  omega

/-- **`09:1780`, "This again contradicts the shallow protocol."**

The endpoint puts `C` bits below `T_*`, while the suffix below a node reached
after `r` Alice queries in the alleged `(C+r-1)`-bit protocol has depth at most
`C-1`.  The arithmetic is the banked
`DenseWrapperFrontier.finalNode_budget_contradiction`; what this theorem adds is
the substitution of the frozen endpoint `B_cap + log_2 kappa` for `C`.  General. -/
theorem terminalCall_contradiction {bcap r₂ r₃ r B : ℕ}
    (hC : 3 ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃)
    (hbudget : B + r ≤ TerminalTwoStream.terminalTarget bcap r₂ r₃ + r - 1)
    (hExtension : bcap + (r₃ + 1 + r₂) ≤ B) : False := by
  rw [terminalEndpoint_identity] at hExtension
  exact finalNode_budget_contradiction hC hbudget hExtension

/-! ## Section 12  The assembly bridge to `hDenseRung` -/

/-- **`09:1192--1193`, the shape of the whole dense argument, as a bridge.**

"Fix an arbitrary retained matrix `U' in <U,1,1-delta_U,theta>` and suppose for
contradiction that a protocol `P` of cost at most `C+r-1` computes `U'`."

The general fact that turns that shape into a complexity lower bound: if every
protocol computing `f` costs at least `k`, then `comp f >= k`.  The nonemptiness
of the achievable-cost set is the vendored
`Workspace.UpperBound.AchievableCosts_nonempty` (the trivial reveal-everything
protocol), consumed by pin; without it `sInf` on `ℕ` would return `0`.  General in
both carriers. -/
theorem le_D_of_no_shallow_protocol {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (k : ℕ)
    (h : ∀ c ∈ AchievableCosts f, k ≤ c) : k ≤ D f := by
  have hne := Workspace.UpperBound.AchievableCosts_nonempty f
  exact h (D f) (Nat.sInf_mem hne)

/-- **Aux 12.1.**  The membership form spelled out: a cost is achievable exactly
when some protocol of that cost computes `f`.  This is the frozen "a protocol `P`
of cost at most `C+r-1` computes `U'`" read as a set membership, and it is what
makes `le_D_of_no_shallow_protocol` the frozen contradiction shape rather than an
abstract `sInf` manipulation. -/
theorem mem_achievableCosts_iff {X Y : Type*} (f : X → Y → Bool) (c : ℕ) :
    c ∈ AchievableCosts f
      ↔ ∃ P : Workspace.Types.Protocol.Protocol X Y Bool,
          P.cost = c ∧ Workspace.Types.Protocol.Protocol.Computes P f := Iff.rfl

/-- **The bridge to the deferred binder `hDenseRung` (`eq:wrapper-u-dense`).**

`ScaleAlignOpening.firstWrapper` defers `eq:wrapper-u-dense` as the binder
`hDenseRung : C + r <= Dfamily (interlaceFun (wrapperU N r) 1) (bracketGE ... 1
(1 - delta_U) theta)`.  The frozen proof of that binder is exactly `09:1188--1781`:
fix an arbitrary member and refute every shallow protocol on it.  This theorem
performs that reduction and no more -- the per-member refutation, which is the
routed certificate system of GAP-EXPOSED M1, stays the binder `hmember`.

Nonemptiness of the bracket family is the banked `NPCC.bracketGE.nonempty`,
consumed by pin, and the `forall`-to-`Dfamily` step is the vendored
`EthBridge.le_Dfamily`.  **This is a bridge, not a discharge**: it asserts
`eq:wrapper-u-dense` nowhere. -/
theorem denseRung_of_no_shallow_member {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C : ℕ) {δU θ : ℝ}
    (hθ1 : θ ≤ 1) (hδ1 : 1 - δU ≤ 1) (hRw : 1 ≤ Fintype.card Rw)
    (hmember : ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ,
      ∀ c ∈ AchievableCosts
          (subgame (interlaceFun (ScaleAlignOpening.wrapperU Nmat r) 1) RC.1 RC.2),
        C + r ≤ c) :
    C + r ≤ Dfamily (interlaceFun (ScaleAlignOpening.wrapperU Nmat r) 1)
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ) := by
  classical
  haveI : DecidableEq (Fin (2 ^ r) × Rw) := Classical.decEq _
  have hcard : 1 ≤ Fintype.card (Fin (2 ^ r) × Rw) := by
    have hq : 0 < 2 ^ r := pow_pos (by norm_num) r
    have : Nonempty Rw := Fintype.card_pos_iff.mp hRw
    exact Fintype.card_pos_iff.mpr ⟨(⟨0, hq⟩, Classical.arbitrary Rw)⟩
  have hne := NPCC.bracketGE.nonempty (X := Fin (2 ^ r) × Rw) (Y := Fin (2 ^ r) → Cl)
    1 (1 - δU) θ hδ1 hθ1 hcard
  refine EthBridge.le_Dfamily _ _ _ hne ?_
  intro RC hRC
  exact le_D_of_no_shallow_protocol _ _ (hmember RC hRC)


/-! ## Section 13  The scheduled point, EXPLICITLY CONDITIONAL

**Design of record.**  Every quantity this block reads from `sec:parameters` is
**defined** there, so none of them may be assigned a value here.  Accordingly
this section states the block's own gate system over quantities that are
*evaluated through the banked definitional chain in dependency order*, and
leaves the genuinely free inputs universally quantified:

* `theta` is **not** a free parameter.  `eq:Q-theta-choice` (`06:526--537`)
  fixes `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}`, `Q` = the least
  power of two at least `Q_0`, `theta = delta/(16Q)`, and `eq:q-deltaU`
  (`06:514--518`) fixes `delta_U = eta_R/(16q)` at `q = 2^{A_wrap L_P^2}`.  The
  first branch of that maximum is determined by `b_out`, `q` and `eta_R`, all
  of which the block itself carries, so no carve-out is available:
  `scheduledTheta` below is that whole composition and
  `scheduledTheta_le_of_coupling` records the exact consequence
  `theta <= eta_R/(204800 b_out q)`.  `09:1727`'s `theta <= 1/160` is a *use*
  of `theta`, never its definition, and is not taken as a legality clause.
* `t_ref = 2^{k_ref}` is the `eq:tref-search` least search (`06:557--571`), so
  its floor `k_ref >= max{2^19, c_seed L_P^2, clog_2(t_0(3/5))}` is
  **derived** from the banked search predicate
  (`two_pow_nineteen_le_of_KrefPred`) and never assigned; `09:1728`'s
  "since `t_ref >= 4`" is again a use.
* `t_2 = 2^{k_2}` is the `eq:t2-search` least search (`06:763--772`), which has
  **two independent floors** -- `k_2 >= max{4, 2^19, m_HS}` and
  `2^{k_2} >= 2 H_max` with `H_max` reading `L_h = max{b_2,b_T} + max{q,u_term}
  + 4`, i.e. the *width itself* and not its logarithm.  Both are derived from
  the banked predicate (`k2_floors_of_K2Pred`, `two_mul_width_le_two_pow_k2`).
* `eq:terminal-wrapper-gates` (`06:738--743`) has **three** rows, and
  `06:631--633` warns that the third "remains the separately named third row
  ...; it is not hidden inside the endpoint record".  This module consumes the
  banked `ParameterSchedule.terminalWrapperGates`, which carries all three, and
  `first_two_rows_do_not_give_third` records that the first two do not imply
  the third.
* `e_0^max`, `E_B`, `E_T`, `delta_term`, `u_term` are `eq:cover-bounds` and
  `eq:terminal-uniform-bounds` evaluated at the above, through the banked
  `ParameterSchedule.e0maxSched`, `.EB`, `.ET`, `.deltaTerm`, `.uTerm`.

**No declaration below claims a concrete legal schedule tuple, and no numeral
is assigned to any quantity `sec:parameters` fixes.**  What is proved is that
the block's gate system is *simultaneously satisfiable* at the schedule's own
symbolic point: non-vacuity is discharged by **exponent arithmetic at large
`A_wrap`** (`06:744--747`: "Their eventual validity is why `A_wrap` is chosen
after the universal coefficient audit"), through the banked
`ParameterSchedule.terminalWrapperGates_at_scheduled_point`.  Witnesses at the
genuinely free inputs are the paper's own closed-form accessor -- the
least-power-of-two search of `06:1253--1268`, banked as
`ParameterSchedule.leastPowTwoGe`/`leastPowTwoExp` -- never a numeral shortcut
of it.

**Canonical inhabitation is DEFERRED, not claimed.**  The paper's own instance
of this gate system is produced by the effective-cutoff audit
(`thm:eff-ledger`, `06:744--747`, `06:1213--1218`), which is not formalized;
the ledger row for this module carries that obligation, and the satisfiability
theorems below are explicitly *not* a substitute for it.

**Still not discharged, and deliberately not absorbed into the word "legal".**
The Stage-1 coupling gates `t_2 >= 8q_1` (`06:834`), `q_2 >= 64sq_1/zeta`
(`06:836`) and the `b_1` window `eq:b1-window` (`06:324--328`) constrain `t_2`,
`q_2` and `b_1` against `a, q_1, A_*, C_0, zeta` -- quantities `09:1512--1781`
never reads.  The existential witnesses for `q_2` and `b_1` below satisfy the
block's *own* gates and are not asserted to be the schedule's values for them.

### 13.1  The frozen least-power-of-two search, at the banked accessor

`u_term` and `u_don` are the *same* frozen search -- "the least power of two
with `u delta >= 8s`" (`06:726--728`, `09:1717--1718`) -- run at `delta_term`
and at `delta_0`.  It is banked once as `ParameterSchedule.uTerm` and is
**not** restated here; what this module adds is the antitonicity that turns the
frozen sentence `u_don <= u_term` (`09:1715--1716`) into a *consequence* of
`delta_term <= delta_0` instead of a second assumption. -/

/-- **Aux 13.1 (the banked accessor is monotone).**  A larger demand needs a
wider donor product.  General; stated about the banked
`ParameterSchedule.leastPowTwoGe`, which is defined through the least
admissible exponent rather than through a ceiling logarithm. -/
theorem leastPowTwoGe_mono {x y : ℝ} (h : x ≤ y) :
    ParameterSchedule.leastPowTwoGe x ≤ ParameterSchedule.leastPowTwoGe y := by
  simp only [ParameterSchedule.leastPowTwoGe]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact ParameterSchedule.leastPowTwoExp_le
    (le_trans h (ParameterSchedule.le_two_pow_leastPowTwoExp y))

/-- **Aux 13.2 (round-trip on the powers of two).**  The search is the identity
on the powers of two, so it cannot silently inflate a width that is already
dyadic.  General. -/
theorem leastPowTwoGe_pow (j : ℕ) :
    ParameterSchedule.leastPowTwoGe ((2 : ℝ) ^ j) = 2 ^ j := by
  have hupper : ParameterSchedule.leastPowTwoExp ((2 : ℝ) ^ j) ≤ j :=
    ParameterSchedule.leastPowTwoExp_le le_rfl
  have hlower : j ≤ ParameterSchedule.leastPowTwoExp ((2 : ℝ) ^ j) := by
    by_contra hcon
    push Not at hcon
    have hlt : (2 : ℝ) ^ ParameterSchedule.leastPowTwoExp ((2 : ℝ) ^ j) < 2 ^ j :=
      pow_lt_pow_right₀ (by norm_num) hcon
    have := ParameterSchedule.le_two_pow_leastPowTwoExp ((2 : ℝ) ^ j)
    linarith
  have : ParameterSchedule.leastPowTwoExp ((2 : ℝ) ^ j) = j := le_antisymm hupper hlower
  rw [ParameterSchedule.leastPowTwoGe, this]

/-- **Aux 13.3 (`06:726--728` is antitone in the density).**  A thinner
terminal density forces a wider donor product.  General; about the banked
`ParameterSchedule.uTerm`. -/
theorem uTerm_antitone {s : ℕ} {d d' : ℝ} (hd : 0 < d) (hle : d ≤ d') :
    ParameterSchedule.uTerm s d' ≤ ParameterSchedule.uTerm s d := by
  have hs : (0 : ℝ) ≤ 8 * (s : ℝ) := by positivity
  simp only [ParameterSchedule.uTerm]
  exact leastPowTwoGe_mono (div_le_div_of_nonneg_left hs hd hle)

/-- **`09:1715--1716`, "`e_T <= E_T` and `u_don <= u_term`", first half.**
"Every terminal many-donor application has density at least `delta_term`"
(`06:734--735`): at `e_T <= E_T` the block's own `delta_0` dominates the
schedule's uniform `delta_term`.  Stated over the banked
`ParameterSchedule.deltaTerm`.  General. -/
theorem deltaTerm_le_deltaZero {etaR : ℝ} {eT ETm : ℕ} (hetaR : 0 ≤ etaR)
    (heT : 0 < eT) (hle : eT ≤ ETm) :
    ParameterSchedule.deltaTerm etaR ETm ≤ deltaZero etaR eT := by
  have hmuP : (0 : ℝ) < muP := muP_pos
  have heTR : (0 : ℝ) < (eT : ℝ) := by exact_mod_cast heT
  have hmax : (eT : ℝ) ≤ ((max 1 ETm : ℕ) : ℝ) := by
    have : eT ≤ max 1 ETm := le_trans hle (le_max_right _ _)
    exact_mod_cast this
  have hb : (0 : ℝ) < 8 * (eT : ℝ) * muP := by
    have : (0 : ℝ) < 8 * (eT : ℝ) := by linarith
    exact mul_pos this hmuP
  have hbc : 8 * (eT : ℝ) * muP ≤ 8 * muP * ((max 1 ETm : ℕ) : ℝ) := by nlinarith
  rw [ParameterSchedule.deltaTerm, deltaZero]
  exact div_le_div_of_nonneg_left hetaR hb hbc

/-- **`09:1715--1716`, second half: `u_don <= u_term`, DERIVED.**

The frozen sentence is a consequence of the first half and of the fact that
`u_don` and `u_term` are the *same* least search run at two densities: at
`e_T <= E_T` the schedule's uniform `delta_term` is the smaller density, hence
the wider width.  Nothing is assumed.  General. -/
theorem uDon_le_uTerm {etaR : ℝ} {s eT ETm : ℕ} (hetaR : 0 ≤ etaR)
    (heT : 0 < eT) (hle : eT ≤ ETm)
    (hpos : 0 < ParameterSchedule.deltaTerm etaR ETm) :
    ParameterSchedule.uTerm s (deltaZero etaR eT)
      ≤ ParameterSchedule.uTerm s (ParameterSchedule.deltaTerm etaR ETm) :=
  uTerm_antitone hpos (deltaTerm_le_deltaZero hetaR heT hle)

/-! ### 13.1b  The frozen cover-search tested endpoint (`06:657--693`)

`eq:cover-bounds` names three least searches and `eq:cover-tested-endpoint`
bounds each of them *without evaluating it*.  The frozen proof is one general
argument -- write the reduced base as `a/b` with `0 < a < b` and the reduced
threshold as `u/v`, put `r = bl(v)`, and check `(a/b)^{br} < 2^{-r} < u/v` by
Bernoulli -- so it is transcribed here for a **real** base, in the form the
`coverExponent` least search consumes.  (The banked
`ParameterSchedule.cover_tested_endpoint` is the same frozen argument for a
*reduced integer* base `a/b`; neither form subsumes the other, and the two
instances the schedule needs at rational bases go through the banked one.) -/

/-- **`06:671--678`, the Bernoulli step of the tested endpoint.**

"Bernoulli's inequality gives `(b/(b-1))^b = (1 + 1/(b-1))^b >= 1 + b/(b-1) > 2`,
and hence `(a/b)^b <= ((b-1)/b)^b < 1/2`."  The left half, stated for the extreme
base `((b-1)/b)`, general in `b >= 2`; no numeral exponentiation is demanded of
the kernel, which is what lets the singleton search be bounded at a base as
close to `1` as `1 - eta_C`. -/
theorem geomBase_pow_self_lt_half {b : ℕ} (hb : 2 ≤ b) :
    (((b : ℝ) - 1) / (b : ℝ)) ^ b < 1 / 2 := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hcpos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hxpos : (0 : ℝ) < 1 / ((b : ℝ) - 1) := div_pos (by norm_num) hcpos
  have hbern : 1 + (b : ℝ) * (1 / ((b : ℝ) - 1)) ≤ (1 + 1 / ((b : ℝ) - 1)) ^ b :=
    one_add_mul_le_pow (by linarith) b
  have hval : (1 : ℝ) + 1 / ((b : ℝ) - 1) = (b : ℝ) / ((b : ℝ) - 1) := by
    field_simp
    ring
  have hgt1 : (1 : ℝ) < (b : ℝ) * (1 / ((b : ℝ) - 1)) := by
    rw [mul_one_div, lt_div_iff₀ hcpos]
    linarith
  have h2 : (2 : ℝ) < ((b : ℝ) / ((b : ℝ) - 1)) ^ b := by
    rw [← hval]
    linarith
  have hdivpos : (0 : ℝ) < (b : ℝ) / ((b : ℝ) - 1) := div_pos hbpos hcpos
  have hy : (0 : ℝ) < ((b : ℝ) / ((b : ℝ) - 1)) ^ b := pow_pos hdivpos b
  have hinv : ((b : ℝ) - 1) / (b : ℝ) = ((b : ℝ) / ((b : ℝ) - 1))⁻¹ := by
    rw [inv_div]
  have hgoal : (((b : ℝ) / ((b : ℝ) - 1)) ^ b)⁻¹ < 1 / 2 := by
    rw [inv_eq_one_div, div_lt_div_iff₀ hy (by norm_num : (0 : ℝ) < 2)]
    linarith
  calc (((b : ℝ) - 1) / (b : ℝ)) ^ b
      = (((b : ℝ) / ((b : ℝ) - 1))⁻¹) ^ b := by rw [hinv]
    _ = (((b : ℝ) / ((b : ℝ) - 1)) ^ b)⁻¹ := by rw [inv_pow]
    _ < 1 / 2 := hgoal

/-- **`eq:cover-tested-endpoint` (`06:664--680`), general.**

"In general, write the reduced base as `a/b`, with `0 < a < b`, and the reduced
positive threshold as `u/v`, with `u, v >= 1`.  Put `r = bl(v) = clog_2(v+1)`.
The compiler stores `B^* = br`, `(a/b)^{B^*} < u/v`, `1 <= B^*` ... `(a/b)^b <=
((b-1)/b)^b < 1/2`.  Also `2^r >= v+1 > v >= v/u`.  Therefore
`(a/b)^{br} < 2^{-r} < u/v`, proving the stored comparison without invoking the
value returned by the least search."

Stated with the threshold's own bound `2^{-r} < theta` in place of the reduced
`u/v` bookkeeping, which is the only use the three instances make of it.
General in the base, the threshold and the two integers. -/
theorem coverExponent_le_tested {a θ : ℝ} {b r : ℕ}
    (hb : 2 ≤ b) (ha0 : 0 ≤ a) (hab : a ≤ ((b : ℝ) - 1) / (b : ℝ))
    (hr : 1 ≤ r) (hθ : (1 : ℝ) / 2 ^ r < θ) :
    coverExponent a θ ≤ b * r := by
  have hbase : (0 : ℝ) ≤ ((b : ℝ) - 1) / (b : ℝ) := le_trans ha0 hab
  have hstep : (((b : ℝ) - 1) / (b : ℝ)) ^ b < 1 / 2 := geomBase_pow_self_lt_half hb
  have hnn : (0 : ℝ) ≤ (((b : ℝ) - 1) / (b : ℝ)) ^ b := pow_nonneg hbase b
  have hpow : ((((b : ℝ) - 1) / (b : ℝ)) ^ b) ^ r < ((1 : ℝ) / 2) ^ r :=
    pow_lt_pow_left₀ hstep hnn (by omega)
  have ha : a ^ (b * r) ≤ ((((b : ℝ) - 1) / (b : ℝ)) ^ b) ^ r := by
    rw [← pow_mul]
    exact pow_le_pow_left₀ ha0 hab (b * r)
  have hhalf : ((1 : ℝ) / 2) ^ r = 1 / 2 ^ r := by
    rw [div_pow]; norm_num
  refine coverExponent_le (Nat.mul_pos (by omega) (by omega)) ?_
  calc a ^ (b * r) ≤ ((((b : ℝ) - 1) / (b : ℝ)) ^ b) ^ r := ha
    _ < ((1 : ℝ) / 2) ^ r := hpow
    _ = 1 / 2 ^ r := hhalf
    _ < θ := hθ

/-! ### 13.2  The scheduled evaluation layer

Each definition below is the banked chain **composed in dependency order**;
none introduces a constant, and each names the display it evaluates.  The only
binders are the genuinely free inputs of `06:4--7`: the source scale `s`, the
source-side scalars `delta_v(G)` and `zeta`, the requested output depth
`b_out`, the interlace width `q`, and the reference exponent `k_ref`. -/

/-- **`eq:q-deltaU`, `06:517`, evaluated.**  `delta_U = eta_R/(16q)` at the
schedule's own `eta_R = eta_R(s, delta_v(G), zeta)`. -/
noncomputable def scheduledDeltaU (s : ℕ) (dv zeta : ℝ) (q : ℕ) : ℝ :=
  ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta) q

/-- **`eq:Q-theta-choice`, `06:529--532`, evaluated.**  `Q` is the banked least
power of two at least `Q_0`, at the `delta_U` the line above returns. -/
noncomputable def scheduledQ (bout s : ℕ) (dv zeta : ℝ) (q : ℕ) : ℕ :=
  EntryGates.Qwidth bout (scheduledDeltaU s dv zeta q)

/-- **`eq:Q-theta-choice`, `06:533`, evaluated.**  `theta = delta/(16Q)` at
that `Q`.  **This is the whole content of the `B1` repair**: `theta` is a
*function of* `(b_out, s, delta_v(G), zeta, q)`, so no value may be assigned to
it, and `09:1727`'s `theta <= 1/160` is a downstream use rather than a
definition. -/
noncomputable def scheduledTheta (bout s : ℕ) (dv zeta : ℝ) (q : ℕ) : ℝ :=
  ParameterSchedule.theta (scheduledQ bout s dv zeta q)

/-- **`eq:cover-bounds`, `06:647--651`, evaluated.**  `e_0^max` at the three
frozen bases, the scheduled `theta`, the schedule's own `eta_C`, and the
reference exponent `k_ref`. -/
noncomputable def scheduledE0Max (bout s : ℕ) (dv zeta : ℝ) (q kref : ℕ) : ℕ :=
  ParameterSchedule.e0maxSched (scheduledTheta bout s dv zeta q)
    (ParameterSchedule.etaC s dv) kref

/-- **`eq:terminal-uniform-bounds`, `06:720--722`, evaluated.** -/
noncomputable def scheduledEB (bout s : ℕ) (dv zeta : ℝ) (q kref : ℕ) : ℕ :=
  ParameterSchedule.EB (Btheta (scheduledTheta bout s dv zeta q)) (Lq q) s
    (scheduledE0Max bout s dv zeta q kref) (ParameterSchedule.etaR s dv zeta)

/-- **`eq:terminal-uniform-bounds`, `06:723`, evaluated.** -/
noncomputable def scheduledET (bout s : ℕ) (dv zeta : ℝ) (q kref : ℕ) : ℕ :=
  ParameterSchedule.ET (scheduledE0Max bout s dv zeta q kref)
    (scheduledEB bout s dv zeta q kref)

/-- **`eq:terminal-uniform-bounds`, `06:724--725`, evaluated.** -/
noncomputable def scheduledDeltaTerm (bout s : ℕ) (dv zeta : ℝ) (q kref : ℕ) : ℝ :=
  ParameterSchedule.deltaTerm (ParameterSchedule.etaR s dv zeta)
    (scheduledET bout s dv zeta q kref)

/-- **`eq:terminal-uniform-bounds`, `06:726--728`, evaluated.** -/
noncomputable def scheduledUTerm (bout s : ℕ) (dv zeta : ℝ) (q kref : ℕ) : ℕ :=
  ParameterSchedule.uTerm s (scheduledDeltaTerm bout s dv zeta q kref)

/-- **B1, the coupling read off the chain.**

All four links of `eq:Q-theta-choice` with `eq:q-deltaU`, as checked equations:
the full three-branch maximum of `Q_0` (nothing dropped), `Q = 2^{r_Q}`,
`Q_0 <= Q`, `theta = delta/(16Q)`, and `delta_U = eta_R/(16q)`.  General. -/
theorem scheduledTheta_coupling (bout s : ℕ) (dv zeta : ℝ) (q : ℕ) :
    EntryGates.Q0 bout (scheduledDeltaU s dv zeta q)
        = max (max (8 * (bout : ℝ)
            / (EntryGates.deltaFixed * scheduledDeltaU s dv zeta q))
          (8 / EntryGates.deltaFixed)) 16
      ∧ scheduledQ bout s dv zeta q
          = 2 ^ EntryGates.rQ bout (scheduledDeltaU s dv zeta q)
      ∧ EntryGates.Q0 bout (scheduledDeltaU s dv zeta q)
          ≤ ((scheduledQ bout s dv zeta q : ℕ) : ℝ)
      ∧ scheduledTheta bout s dv zeta q
          = EntryGates.deltaFixed / (16 * ((scheduledQ bout s dv zeta q : ℕ) : ℝ))
      ∧ scheduledDeltaU s dv zeta q
          = ParameterSchedule.etaR s dv zeta / (16 * (q : ℝ)) :=
  ⟨ParameterSchedule.schedule_Q0_eq_entry_Q0 _ _,
    EntryGates.Qwidth_eq_two_pow _ _,
    EntryGates.Q0_le_Qwidth _ _,
    ParameterSchedule.theta_eq_delta _,
    rfl⟩

/-- **B1, the exact consequence: `theta` is forced DOWN by `q` and `eta_R`.**

`Q_0 >= 8 b_out/(delta delta_U)` with `delta = 1/10` and
`delta_U = eta_R/(16q)` gives `Q_0 >= 1280 b_out q/eta_R`, hence
`theta = 1/(160 Q) <= eta_R/(204800 b_out q)`.

This is the statement that makes the `r4` failure impossible to repeat: a
`theta` chosen without reference to `(b_out, q, eta_R)` is refuted by this
inequality as soon as `q` is large, and the interlace width `q = 2^{A_wrap
L_P^2}` is exponentially large by construction.  General in all five inputs. -/
theorem scheduledTheta_le_of_coupling {bout s : ℕ} {dv zeta : ℝ} {q : ℕ}
    (hb : 1 ≤ bout) (hq : 0 < q) (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) :
    scheduledTheta bout s dv zeta q
      ≤ ParameterSchedule.etaR s dv zeta / (204800 * (bout : ℝ) * (q : ℝ)) := by
  have hetaR : 0 < ParameterSchedule.etaR s dv zeta :=
    ParameterSchedule.etaR_pos hs hdv hz
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hboutR : (1 : ℝ) ≤ (bout : ℝ) := by exact_mod_cast hb
  have hdelta : EntryGates.deltaFixed = 1 / 10 := rfl
  have hdU : scheduledDeltaU s dv zeta q
      = ParameterSchedule.etaR s dv zeta / (16 * (q : ℝ)) := rfl
  have hdUpos : 0 < scheduledDeltaU s dv zeta q := by
    rw [hdU]; positivity
  -- the first branch of the `Q_0` maximum, evaluated
  have hbranch : 8 * (bout : ℝ)
        / (EntryGates.deltaFixed * scheduledDeltaU s dv zeta q)
      = 1280 * (bout : ℝ) * (q : ℝ) / ParameterSchedule.etaR s dv zeta := by
    rw [hdelta, hdU]
    field_simp
    ring
  have hQ0 : 1280 * (bout : ℝ) * (q : ℝ) / ParameterSchedule.etaR s dv zeta
      ≤ EntryGates.Q0 bout (scheduledDeltaU s dv zeta q) := by
    rw [ParameterSchedule.schedule_Q0_eq_entry_Q0, ← hbranch]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hQ := EntryGates.Q0_le_Qwidth bout (scheduledDeltaU s dv zeta q)
  have hQge : 1280 * (bout : ℝ) * (q : ℝ) / ParameterSchedule.etaR s dv zeta
      ≤ ((scheduledQ bout s dv zeta q : ℕ) : ℝ) := le_trans hQ0 hQ
  have hQpos : (0 : ℝ) < ((scheduledQ bout s dv zeta q : ℕ) : ℝ) := by
    have : 0 < scheduledQ bout s dv zeta q := Nat.two_pow_pos _
    exact_mod_cast this
  have hmul : 1280 * (bout : ℝ) * (q : ℝ)
      ≤ ((scheduledQ bout s dv zeta q : ℕ) : ℝ) * ParameterSchedule.etaR s dv zeta := by
    rw [div_le_iff₀ hetaR] at hQge
    linarith
  rw [scheduledTheta, ParameterSchedule.theta_eq_delta, hdelta]
  rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 16 * ((scheduledQ bout s dv zeta q : ℕ) : ℝ))
    (by positivity : (0:ℝ) < 204800 * (bout : ℝ) * (q : ℝ))]
  nlinarith [hmul, hetaR, hQpos]

/-! ### 13.3  The two frozen least searches, floors DERIVED from the predicates

`06:1671--1678` and `06:744--747` place the *values* of `k_ref` and `k_2`
downstream of the effective-cutoff audit, so nothing here evaluates either.
What is proved is that the search predicates already force their floors, which
is what the `r4` park read off downstream use-sites instead. -/

universe u

/-- **B2 (`eq:tref-search`, `06:561--563`).**

Every `k` satisfying the banked `k_ref` search predicate clears all three
branches of the frozen floor `max{2^19, c_seed L_P^2, clog_2(t_0(3/5))}`.  In
particular `2^19 <= k_ref`, so `t_ref = 2^{k_ref}` is astronomically larger
than the `t_ref >= 4` that `09:1728` *uses*.  Derived, never assigned.
General. -/
theorem two_pow_nineteen_le_of_KrefPred {cseed LP t0clog Ccert lq Lth k : ℕ}
    (h : ParameterSchedule.KrefPred cseed LP t0clog Ccert lq Lth k) :
    2 ^ 19 ≤ k ∧ cseed * LP ^ 2 ≤ k ∧ t0clog ≤ k := by
  have hfloor : ParameterSchedule.krefFloor cseed LP t0clog ≤ k := h.1
  rw [ParameterSchedule.krefFloor] at hfloor
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hfloor
  · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hfloor
  · exact le_trans (le_max_right _ _) hfloor

/-- **B2, the consequence for `eq:cover-bounds`.**

`e_0^max = (B_ref - 1)(t_ref/2 + log_2 t_ref - 2) + ...` at `t_ref = 2^{k}`, so
at `B_ref >= 2` the reference term alone contributes `2^{k-1}`.  At a legal
`k_ref` this is `2^{2^19 - 1}`, not a two-digit number: the `r4` park's
`e_0^max <= 2^42` was an artifact of `k_ref = 2`.  Recorded as an exponent
inequality rather than a numeral, which is the only form the kernel can carry.
General. -/
theorem two_pow_pred_le_e0maxSched {θ eC : ℝ} {k : ℕ}
    (hB : 2 ≤ coverExponent rhoSmall θ) (hk : 2 ≤ k) :
    2 ^ (k - 1) ≤ ParameterSchedule.e0maxSched θ eC k := by
  rw [ParameterSchedule.e0maxSched_eq_display]
  have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ (k - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow' : (2 : ℕ) ≤ 2 ^ (k - 1) := by simpa using hpow
  have hone : 1 ≤ coverExponent rhoSmall θ - 1 := by omega
  have hstep : 2 ^ (k - 1) ≤ (coverExponent rhoSmall θ - 1) * (2 ^ (k - 1) + k - 2) := by
    calc 2 ^ (k - 1) = 1 * 2 ^ (k - 1) := by ring
      _ ≤ (coverExponent rhoSmall θ - 1) * (2 ^ (k - 1) + k - 2) :=
        Nat.mul_le_mul hone (by omega)
  omega

/-- **B3 (`eq:t2-search`, `06:766`).**  Both branches of the frozen floor
`k_2 >= max{4, 2^19, m_HS}`, plus the width clause `2^{k_2} >= 2 H_max`, all
read off the banked search predicate.  The `r4` park carried only `4 <= k_2`.
General. -/
theorem k2_floors_of_K2Pred {Lh Bcap Hmax k : ℕ}
    (h : ParameterSchedule.K2Pred.{u} Lh Bcap Hmax k) :
    4 ≤ k ∧ 2 ^ 19 ≤ k ∧ 2 * Hmax ≤ 2 ^ k := by
  have hfloor : ParameterSchedule.k2Floor.{u} ≤ k := h.1
  rw [ParameterSchedule.k2Floor] at hfloor
  refine ⟨?_, ?_, h.2.1⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hfloor
  · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hfloor

/-- **B3, the load-bearing half: `L_h` reads the WIDTH, not its logarithm.**

`eq:Hmax` (`06:757`) puts `max{q, u_term}` -- the width itself -- inside `L_h`,
and `H_max >= L_h`, so the `eq:t2-search` width clause `2^{k_2} >= 2 H_max`
forces `2^{k_2} >= 2q` and `2^{k_2} >= 2 u_term`.  The `r4` park read
`06:973`'s `t_2 >= 2 log_2 q_2` instead, which is the weakest consequence of
the chain.  General in all eight widths. -/
theorem two_mul_width_le_two_pow_k2 {b2 bT q uterm q1 lq lq2 Bcap Lh k : ℕ}
    (hLh : Lh = ParameterSchedule.LhSched b2 bT q uterm)
    (h : ParameterSchedule.K2Pred.{u} Lh Bcap
      (ParameterSchedule.HmaxSched Lh q1 lq lq2 Bcap) k) :
    2 * q ≤ 2 ^ k ∧ 2 * uterm ≤ 2 ^ k := by
  have hwidth : 2 * ParameterSchedule.HmaxSched Lh q1 lq lq2 Bcap ≤ 2 ^ k := h.2.1
  have hq : q ≤ Lh := by
    rw [hLh, ParameterSchedule.LhSched]
    have : q ≤ max q uterm := le_max_left _ _
    omega
  have hu : uterm ≤ Lh := by
    rw [hLh, ParameterSchedule.LhSched]
    have : uterm ≤ max q uterm := le_max_right _ _
    omega
  have hH : Lh ≤ ParameterSchedule.HmaxSched Lh q1 lq lq2 Bcap := by
    rw [ParameterSchedule.HmaxSched]; omega
  exact ⟨by omega, by omega⟩

/-! ### 13.4  The three named terminal gates, consumed with ALL THREE rows

`06:631--633`: "The downstream gate `q/4 >= t_ref` remains the separately named
third row of `eq:terminal-wrapper-gates`; it is not hidden inside the endpoint
record."  The banked `ParameterSchedule.terminalWrapperGates` carries all
three; this module consumes it and never states a two-row substitute. -/

/-- **B4, the third row is a named row.**  `q/4 >= t_ref`, in the integer form
`4 t_ref <= q`, projected out of the banked gate.  General. -/
theorem terminalWrapperGates_third_row {q ETv utermv Bthetav tref : ℕ}
    (h : ParameterSchedule.terminalWrapperGates q ETv utermv Bthetav tref) :
    4 * tref ≤ q := h.2.2

/-- **B4, REJECTION PROBE (claims no legality).**

The first two rows do **not** imply the third, so a "gate system" stating only
`q >= 8 max{1,E_T}` and `q > 4 E_T u_term B_theta` is strictly weaker than
`eq:terminal-wrapper-gates` and dropping row three is a real omission rather
than a cosmetic one.  The values here are chosen to make the guard fire and are
**not** claimed to be a legal schedule point. -/
theorem first_two_rows_do_not_give_third :
    ∃ q ETv utermv Bthetav tref : ℕ,
      8 * max 1 ETv ≤ q ∧ 4 * ETv * utermv * Bthetav < q ∧ ¬ (4 * tref ≤ q) := by
  refine ⟨8, 0, 0, 0, 1000, by norm_num, by norm_num, by norm_num⟩

/-- **The audit majorants are satisfiable: `2^n` outgrows any fixed product.**

`06:744--747` defers the first two rows of `eq:terminal-wrapper-gates` to the
universal coefficient audit and says the audit is why `A_wrap` is chosen last.
This lemma is the exponent arithmetic behind that sentence: for **any** values
of `E_T`, `u_term`, `B_theta` and `k_ref` there is a width exponent clearing
all three demands at once.  General; no numeral is assigned to anything. -/
theorem exists_width_exponent (ETv utermv Bthetav kref : ℕ) :
    ∃ e : ℕ, kref + 2 ≤ e ∧ 8 * max 1 ETv ≤ 2 ^ e
      ∧ 4 * ETv * utermv * Bthetav < 2 ^ e := by
  classical
  set M := max (kref + 2) (max (8 * max 1 ETv) (4 * ETv * utermv * Bthetav + 1))
    with hM
  have h1 : kref + 2 ≤ M := le_max_left _ _
  have h2 : 8 * max 1 ETv ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : 4 * ETv * utermv * Bthetav + 1 ≤ M :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have h4 : M < 2 ^ M := Nat.lt_two_pow_self
  exact ⟨M, h1, by omega, by omega⟩

/-- **NON-VACUITY of `eq:terminal-wrapper-gates` at the schedule's own point.**

All three rows fire at `q = 2^{A_wrap L_P^2}` once `A_wrap` is large, which is
exactly the frozen order of determination (`06:744--747`).  The discharge is
pure exponent arithmetic against the banked
`ParameterSchedule.terminalWrapperGates_at_scheduled_point`; `E_T`, `u_term`,
`B_theta`, `k_ref` and `L_P` all stay **symbolic**, and the returned `A_wrap`
clears the frozen floor `A_wrap > c_seed` of `06:1671`.

This is a *satisfiability* statement about the gate system, not a claim that
the returned `A_wrap` is the schedule's value: the paper's own `A_wrap` is
fixed by `thm:eff-ledger`, and that canonical-inhabitation obligation is
recorded as deferred in the ledger row for this module. -/
theorem terminalWrapperGates_nonvacuous (LP ETv utermv Bthetav kref : ℕ)
    (hLP : 1 ≤ LP) :
    ∃ Awrap : ℕ, ParameterSchedule.cSeed < Awrap ∧
      ParameterSchedule.terminalWrapperGates (ParameterSchedule.qWrap Awrap LP)
        ETv utermv Bthetav (2 ^ kref) := by
  obtain ⟨e, hk, h1, h2⟩ := exists_width_exponent ETv utermv Bthetav kref
  refine ⟨max (ParameterSchedule.cSeed + 1) e, ?_, ?_⟩
  · have := le_max_left (ParameterSchedule.cSeed + 1) e
    omega
  · have hLP2 : 1 ≤ LP ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hA : e ≤ max (ParameterSchedule.cSeed + 1) e := le_max_right _ _
    have hexp : e ≤ max (ParameterSchedule.cSeed + 1) e * LP ^ 2 := by
      calc e ≤ max (ParameterSchedule.cSeed + 1) e := hA
        _ = max (ParameterSchedule.cSeed + 1) e * 1 := (Nat.mul_one _).symm
        _ ≤ max (ParameterSchedule.cSeed + 1) e * LP ^ 2 :=
            Nat.mul_le_mul_left _ hLP2
    exact ParameterSchedule.terminalWrapperGates_at_scheduled_point h1 h2 hexp
      (le_trans hk hexp)

/-! ### 13.5  `eq:wrapper-owner-gates`, and the floor it really imposes -/

/-- **B5, the binding floor on `q_2`, named for what it is.**

`09:1687`'s third owner gate `q_2 >= 64 mu_P q/eta_R` is the comparison that
actually forces `q_2` upward at a large interlace width; the guarded-source
floor `q_2 >= 12s|E|` of `06:975` is not the binding one.  Projected out of
`wrapperOwnerGates` rather than restated.  General. -/
theorem ownerGates_force_q2_floor {q q₂ b₁ : ℕ} {etaR g : ℝ}
    (h : wrapperOwnerGates q q₂ etaR g b₁) :
    64 * muP * (q : ℝ) / etaR ≤ (q₂ : ℝ) := h.2.2

/-- **B5, REJECTION PROBE (claims no legality).**  A `q_2` strictly below that
floor is refuted outright, at symbolic `q`, `eta_R`, `g` and `b_1`.  This is
the honest form of the claim the `r4` park mis-titled "the frozen minimum":
what is available is a *floor with a rejection side*, not a minimality
theorem. -/
theorem ownerGates_reject_small_q2 {q q₂ b₁ : ℕ} {etaR g : ℝ}
    (hlt : (q₂ : ℝ) < 64 * muP * (q : ℝ) / etaR) :
    ¬ wrapperOwnerGates q q₂ etaR g b₁ := by
  intro h
  have := ownerGates_force_q2_floor h
  linarith

/-- **NON-VACUITY of `eq:wrapper-owner-gates` at DERIVED widths.**

At a positive interlace width and the schedule's own tolerance ceiling
`eta_R <= 1/36800` (`eq:eta-choice`'s `mu_Sigma` route, banked as
`ParameterSchedule.etaR_le_bound`, so this is not an extra demand), the three
owner gates of `09:1682--1689` are simultaneously satisfiable, and the two
witnesses are the **paper's own least-power-of-two accessor** of
`06:1253--1268` -- `q_2` at the threshold `64 mu_P q/eta_R` of the third gate
and `2^{b_1}` at the threshold `64 mu_P q q_2/eta_R` of the first -- never
numerals.  The two structural readouts `q_2 >= 16` and `16 q_2 <= 2^{b_1}` that
`09:1670--1671` needs come out with them.

`mu_P <= g/20` is the middle gate and enters as the checked identity it is
(`muP_le_g_div_twenty` at the frozen `g = 91/92`).

**Scope.**  `q_2` and `b_1` also carry the Stage-1 coupling constraints
`06:836` and `eq:b1-window`, which mention quantities this block never reads;
this theorem asserts satisfiability of the block's *own* gates and nothing
more. -/
theorem ownerGates_nonvacuous {q : ℕ} {etaR g : ℝ}
    (hq : 0 < q) (hetaR0 : 0 < etaR) (hetaR : etaR ≤ 1 / 36800)
    (hg : muP ≤ g / 20) :
    ∃ q₂ b₁ : ℕ, 16 ≤ q₂ ∧ 16 * q₂ ≤ 2 ^ b₁
      ∧ wrapperOwnerGates q q₂ etaR g b₁ := by
  classical
  have hmu : muP = 1 / 184 := rfl
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set q₂ : ℕ := ParameterSchedule.leastPowTwoGe (64 * muP * (q : ℝ) / etaR) with hq₂def
  have hx : 64 * muP * (q : ℝ) / etaR ≤ (q₂ : ℝ) :=
    ParameterSchedule.le_leastPowTwoGe _
  have hbig : (12800 : ℝ) ≤ (q₂ : ℝ) := by
    have h1 : (12800 : ℝ) ≤ 64 * muP * (q : ℝ) / etaR := by
      rw [le_div_iff₀ hetaR0, hmu]
      nlinarith [hetaR, hqR, hetaR0]
    linarith
  have hq₂16 : 16 ≤ q₂ := by
    have : (16 : ℝ) ≤ (q₂ : ℝ) := by linarith
    exact_mod_cast this
  have hq₂R : (0 : ℝ) < (q₂ : ℝ) := by linarith
  set b₁ : ℕ :=
    ParameterSchedule.leastPowTwoExp (64 * muP * (q : ℝ) * (q₂ : ℝ) / etaR) with hb₁def
  have hy : 64 * muP * (q : ℝ) * (q₂ : ℝ) / etaR ≤ (2 : ℝ) ^ b₁ :=
    ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hykey : 64 * muP * (q : ℝ) * (q₂ : ℝ) ≤ etaR * (2 : ℝ) ^ b₁ := by
    rw [div_le_iff₀ hetaR0] at hy
    linarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
  have hgate16 : 16 * q₂ ≤ 2 ^ b₁ := by
    have hR : (16 : ℝ) * (q₂ : ℝ) ≤ (2 : ℝ) ^ b₁ := by
      rw [hmu] at hykey
      nlinarith [hetaR, hqR, hetaR0, hq₂R, hykey]
    have : ((16 * q₂ : ℕ) : ℝ) ≤ (((2 : ℕ) ^ b₁ : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  refine ⟨q₂, b₁, hq₂16, hgate16, ?_, hg, hx⟩
  -- the first owner gate `2 mu_P q lambda_0 <= eta_R/16`
  have hlhs : 2 * muP * (q : ℝ) * DenseBranchSelection.lambdaZero q₂ b₁
      = (4 * muP * (q : ℝ) * (q₂ : ℝ)) / 2 ^ b₁ := by
    rw [DenseBranchSelection.lambdaZero]
    field_simp
    ring
  rw [hlhs, div_le_div_iff₀ hpow (by norm_num : (0 : ℝ) < 16)]
  nlinarith [hykey]

/-! ### 13.6  Row (iv)'s widths, at the paper's own accessors -/

/-- **NON-VACUITY of row (iv)'s width and structural-gate hypotheses.**

`extensionCallFour_of_width` takes the `09:1744` width floor, the
`eq:wrapper-terminal-block-supply` supply bound and the `06:1158--1159`
structural row-density gate as inputs.  This lemma exhibits them jointly
satisfiable at the block's **own derived** density `delta_0`, with both
exponents supplied by the paper's own least-power-of-two accessor: `e` is the
`09:1717--1718` search at `delta_0` (i.e. `u_don = 2^e`), and `b_1` is the
least exponent clearing `06:1158`'s comparison.  **No numeral is chosen**, and
`delta_0` is `eq:wrapper-terminal-density` evaluated, not posited.

`T` is deliberately *not* produced here: `T = log_2 t_2` is fixed by
`eq:t2-search`, whose floors are recorded in `k2_floors_of_K2Pred` and
`two_mul_width_le_two_pow_k2`, and inventing a value for it would be exactly
the `B3` defect.  The hypothesis `6 <= r_3` is the scheduled-record floor
`64 | s` of `05:420` ("hence `s >= 64`" at `06:975`) in dyadic form; it is what
turns `09:1744`'s `u_don >= 8s` into the ledger's common binder `4 <= e`
(`16 | u_don`, `D:761--762`) rather than that binder being posited. -/
theorem callFourWidths_satisfiable {etaR : ℝ} {eT r₂ r₃ : ℕ}
    (hetaR : 0 < etaR) (heT : 0 < eT) (hd1 : deltaZero etaR eT ≤ 1)
    (hr₃ : 6 ≤ r₃) :
    ∃ e b₁ : ℕ, r₃ + 3 ≤ e ∧ 4 ≤ e ∧ 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e
      ∧ 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e * deltaZero etaR eT
      ∧ ((2 : ℝ) ^ (r₃ + 1 + r₂)) / 2 ^ b₁ ≤ deltaZero etaR eT / 2 := by
  classical
  have hd0 : 0 < deltaZero etaR eT := deltaZero_pos hetaR heT
  set e : ℕ :=
    ParameterSchedule.leastPowTwoExp (8 * ((2 : ℝ) ^ r₃) / deltaZero etaR eT) with hedef
  set b₁ : ℕ :=
    ParameterSchedule.leastPowTwoExp
      (2 * ((2 : ℝ) ^ (r₃ + 1 + r₂)) / deltaZero etaR eT) with hbdef
  have he : 8 * ((2 : ℝ) ^ r₃) / deltaZero etaR eT ≤ (2 : ℝ) ^ e :=
    ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hsupply : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e * deltaZero etaR eT := by
    rw [div_le_iff₀ hd0] at he
    linarith
  have hlow : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e := by
    nlinarith [hsupply, hd1, hd0, pow_pos (by norm_num : (0:ℝ) < 2) e]
  have hexp : r₃ + 3 ≤ e := by
    by_contra hcon
    push Not at hcon
    have hlt : (2 : ℝ) ^ e < 2 ^ (r₃ + 3) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    have hrw : (2 : ℝ) ^ (r₃ + 3) = 8 * (2 : ℝ) ^ r₃ := by
      rw [pow_add]; ring
    linarith
  have hb : 2 * ((2 : ℝ) ^ (r₃ + 1 + r₂)) / deltaZero etaR eT ≤ (2 : ℝ) ^ b₁ :=
    ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hgate : ((2 : ℝ) ^ (r₃ + 1 + r₂)) / 2 ^ b₁ ≤ deltaZero etaR eT / 2 := by
    rw [div_le_iff₀ hd0] at hb
    have hpow : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
    rw [div_le_div_iff₀ hpow (by norm_num : (0 : ℝ) < 2)]
    linarith
  exact ⟨e, b₁, hexp, by omega, hlow, hsupply, hgate⟩

/-! ### 13.7  The endpoint: the block's hypothesis bundle is consistent

`B6`.  Every gate in this pipeline can pass while the principal deliverable is
vacuous, so the block's gate system is exhibited with a model -- **at one
point**, with all conjuncts threaded through the same `A_wrap`, `q_2` and
`b_1`.  A bundle whose conjuncts sat at different parameter points would
certify nothing. -/

/-- **The block's own gate system** (`eq:terminal-wrapper-gates`, `06:738--743`,
with `eq:wrapper-owner-gates`, `09:1682--1689`).

Two frozen displays conjoined and nothing else: no derived telescope is
restated as a field, and nothing here is a conclusion. -/
def BlockGates (q q₂ b₁ ETv utermv Bthetav tref : ℕ) (etaR g : ℝ) : Prop :=
  ParameterSchedule.terminalWrapperGates q ETv utermv Bthetav tref
    ∧ wrapperOwnerGates q q₂ etaR g b₁

/-- **Aux (the bundle is exactly those two displays).** -/
theorem blockGates_iff (q q₂ b₁ ETv utermv Bthetav tref : ℕ) (etaR g : ℝ) :
    BlockGates q q₂ b₁ ETv utermv Bthetav tref etaR g ↔
      (ParameterSchedule.terminalWrapperGates q ETv utermv Bthetav tref
        ∧ wrapperOwnerGates q q₂ etaR g b₁) := Iff.rfl

/-- **THE ENDPOINT (`B6`): the block's hypothesis bundle is CONSISTENT at the
schedule's symbolic point, with the frozen identifications INTACT.**

For every symbolic `L_P`, `E_T`, `u_term`, `B_theta`, `k_ref`, `r_3`, `T` and
every positive exceptional count `e_T`, at every legal tolerance
`0 < eta_R <= 1/36800` (the `eq:eta-choice` cap, banked as
`ParameterSchedule.etaR_le_bound`), every `g` with `mu_P <= g/20` (the frozen
`g = 91/92` clears it, `muP_le_g_div_twenty`), the frozen schedule comparison
`e_T <= E_T` (`09:1715--1716`) and the terminal density branch `delta_0 <= 1`
(`09:1742--1743`), there is a single scheduled point at which

* all **three** rows of `eq:terminal-wrapper-gates` hold,
* all three rows of `eq:wrapper-owner-gates` hold,
* the structural readout `lambda_0 <= 1/8` of `09:1671` holds,
* `eq:terminal-entry` is inhabited at the owner threshold itself,
* row (iv) of the extension-call ledger is **constructed**, not assumed, and
* the schedule's uniform density is dominated, `delta_term <= delta_0`, through
  this module's own `deltaTerm_le_deltaZero`.

**The three frozen identifications are carried, not relaxed.**  A bundle whose
conjuncts sat at *different* occurrences of one shared symbol would certify a
strict relaxation of the block's gate system rather than the system itself:

1. **One `b_1`.**  `eq:stage2-structural-gates` puts `2q_2 2^{-b_1} <= 1/8`
   (`06:838`), `2sq_2 2^{-b_1} <= delta_term/4` (`06:840`) and
   `2q mu_P q_2 2^{1-b_1} <= eta_R/16` (`06:841`) in ONE display, and
   `eq:extension-common-binders` (`06:1110`) fixes the extension row's
   `x = 2^{-b_1}` at that same `b_1`.  So a single `b_1` binder serves
   `wrapperOwnerGates`, `lambda_0`, `eq:terminal-entry` and `ExtensionCallFour`
   alike; the witness is the **max** of the paper's two least-power-of-two
   exponents, which is legal because every one of those rows is monotone in
   `2^{b_1}`.
2. **One `q_2`, and it is dyadic.**  `07:279` defines `q_2 = 2^{r_2}`, so `r_2`
   is existential here and `q_2` is *passed as* `2^{r_2}` to every row -- the
   owner gates, `lambda_0`, `eq:terminal-entry`, and the extension capacity
   `kappa = 2 s q_2 = 2^{r_3+1+r_2}` alike.  The witness is the least exponent
   clearing both the `09:1687` owner floor (through the paper's own
   `ParameterSchedule.leastPowTwoExp`) and the frozen divisibility
   `t_2 | q_2` of `07:278`; the returned `T <= r_2` is exactly the frozen
   `k_2 <= r_2` that `07:317` reads off that divisibility.
3. **`e_T <= E_T` is supplied.**  `09:1715--1716` states that the schedule
   computes `e_T <= E_T`; it enters as the hypothesis `heTle`, and
   `deltaTerm_le_deltaZero` turns it into `delta_term <= delta_0`, the frozen
   direction of `06:734--735`.

A constructive proof of the conjunction is the model, so no `False` follows
from the bundle.

**What this is not.**  `A_wrap`, `r_2` and `b_1` are produced here by the
paper's own accessors at large exponent; they are *not* claimed to be the
schedule's values, which `thm:eff-ledger`, `06:836` and `eq:b1-window` fix.
No concrete legal schedule tuple is claimed anywhere in this module, and the
canonical-inhabitation obligation -- the paper's own instance, which needs the
effective-cutoff audit -- is recorded as deferred in the ledger. -/
theorem massRedistribution_block_bundle_is_consistent
    (LP ETv utermv Bthetav kref r₃ T eT : ℕ) {etaR g : ℝ}
    (hLP : 1 ≤ LP) (hetaR0 : 0 < etaR) (hetaR : etaR ≤ 1 / 36800)
    (hg : muP ≤ g / 20) (heT : 0 < eT) (heTle : eT ≤ ETv)
    (hd1 : deltaZero etaR eT ≤ 1) (hr₃ : 6 ≤ r₃) (hT4 : 4 ≤ T) :
    ∃ (Awrap r₂ b₁ e : ℕ),
      ParameterSchedule.cSeed < Awrap
        ∧ T ≤ r₂
        ∧ BlockGates (ParameterSchedule.qWrap Awrap LP) (2 ^ r₂) b₁ ETv utermv
            Bthetav (2 ^ kref) etaR g
        ∧ DenseBranchSelection.lambdaZero (2 ^ r₂) b₁ ≤ 1 / 8
        ∧ TerminalTwoStream.terminalEntry (2 ^ r₂) b₁ 0
            (ownerThreshold (2 ^ r₂) b₁ 0)
        ∧ ExtensionCallFour T ((e - 1) + r₂ - T) (r₃ + 1 + r₂ - T) b₁ e r₂ r₃
            (deltaZero etaR eT) (callFourH e)
        ∧ 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e
        ∧ ParameterSchedule.deltaTerm etaR ETv ≤ deltaZero etaR eT := by
  classical
  have hmu : muP = 1 / 184 := rfl
  obtain ⟨Awrap, hAw, hgates⟩ :=
    terminalWrapperGates_nonvacuous LP ETv utermv Bthetav kref hLP
  set q : ℕ := ParameterSchedule.qWrap Awrap LP with hqdef
  have hq : 0 < q := ParameterSchedule.qWrap_pos Awrap LP
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hd0 : 0 < deltaZero etaR eT := deltaZero_pos hetaR0 heT
  -- `r_2` (`07:279`): the least exponent whose power of two clears the
  -- `09:1687` owner floor **and** keeps `t_2 = 2^T` a divisor of `q_2`
  -- (`07:278`, read off as `k_2 <= r_2` at `07:317`).
  set rA : ℕ := ParameterSchedule.leastPowTwoExp (64 * muP * (q : ℝ) / etaR)
    with hrAdef
  set r₂ : ℕ := max rA T with hr₂def
  have hleR : rA ≤ r₂ := by rw [hr₂def]; exact le_max_left _ _
  have hTr₂ : T ≤ r₂ := by rw [hr₂def]; exact le_max_right _ _
  have hx : 64 * muP * (q : ℝ) / etaR ≤ (2 : ℝ) ^ r₂ := by
    refine le_trans ?_ (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hleR)
    rw [hrAdef]
    exact ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hq₂pos : (0 : ℝ) < (2 : ℝ) ^ r₂ := by positivity
  have hbig : (12800 : ℝ) ≤ (2 : ℝ) ^ r₂ := by
    have h1 : (12800 : ℝ) ≤ 64 * muP * (q : ℝ) / etaR := by
      rw [le_div_iff₀ hetaR0, hmu]
      nlinarith [hetaR, hqR, hetaR0]
    linarith
  have hq₂16 : 16 ≤ (2 : ℕ) ^ r₂ := by
    have hcast : ((16 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ r₂ : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hcast
  -- `b_1`: ONE exponent for the whole display, the max of the paper's two
  -- least-power-of-two searches (`06:838--841` and `06:1158--1159`).
  set bA : ℕ :=
    ParameterSchedule.leastPowTwoExp (64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ / etaR)
    with hbAdef
  set bB : ℕ :=
    ParameterSchedule.leastPowTwoExp
      (2 * ((2 : ℝ) ^ (r₃ + 1 + r₂)) / deltaZero etaR eT) with hbBdef
  set b₁ : ℕ := max bA bB with hb₁def
  have hleA : bA ≤ b₁ := by rw [hb₁def]; exact le_max_left _ _
  have hleB : bB ≤ b₁ := by rw [hb₁def]; exact le_max_right _ _
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
  have hy : 64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ / etaR ≤ (2 : ℝ) ^ b₁ := by
    refine le_trans ?_ (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hleA)
    rw [hbAdef]
    exact ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hykey : 64 * muP * (q : ℝ) * (2 : ℝ) ^ r₂ ≤ etaR * (2 : ℝ) ^ b₁ := by
    rw [div_le_iff₀ hetaR0] at hy
    linarith
  have hgate16 : 16 * (2 : ℕ) ^ r₂ ≤ 2 ^ b₁ := by
    have hR : (16 : ℝ) * (2 : ℝ) ^ r₂ ≤ (2 : ℝ) ^ b₁ := by
      have hk := hykey
      rw [hmu] at hk
      nlinarith [hetaR, hqR, hetaR0, hq₂pos, hk]
    have hcast : ((16 * (2 : ℕ) ^ r₂ : ℕ) : ℝ) ≤ (((2 : ℕ) ^ b₁ : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hcast
  have howner : wrapperOwnerGates q (2 ^ r₂) etaR g b₁ := by
    refine ⟨?_, hg, ?_⟩
    · have hlhs :
          2 * muP * (q : ℝ) * DenseBranchSelection.lambdaZero (2 ^ r₂) b₁
            = (4 * muP * (q : ℝ) * (2 : ℝ) ^ r₂) / 2 ^ b₁ := by
        rw [DenseBranchSelection.lambdaZero]
        push_cast
        ring
      rw [hlhs, div_le_div_iff₀ hpow (by norm_num : (0 : ℝ) < 16)]
      nlinarith [hykey]
    · push_cast
      exact hx
  have hlam : DenseBranchSelection.lambdaZero (2 ^ r₂) b₁ ≤ 1 / 8 :=
    lambdaZero_le_eighth hgate16
  -- `u_don = 2^e`, the `09:1717--1718` search at the block's own `delta_0`.
  set e : ℕ :=
    ParameterSchedule.leastPowTwoExp (8 * ((2 : ℝ) ^ r₃) / deltaZero etaR eT)
    with hedef
  have he : 8 * ((2 : ℝ) ^ r₃) / deltaZero etaR eT ≤ (2 : ℝ) ^ e := by
    rw [hedef]
    exact ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hsupply : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e * deltaZero etaR eT := by
    rw [div_le_iff₀ hd0] at he
    linarith
  have hlow : 8 * ((2 : ℝ) ^ r₃) ≤ (2 : ℝ) ^ e := by
    nlinarith [hsupply, hd1, hd0, pow_pos (by norm_num : (0 : ℝ) < 2) e]
  have hexp : r₃ + 3 ≤ e := by
    by_contra hcon
    push Not at hcon
    have hlt : (2 : ℝ) ^ e < 2 ^ (r₃ + 3) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    have hrw : (2 : ℝ) ^ (r₃ + 3) = 8 * (2 : ℝ) ^ r₃ := by
      rw [pow_add]; ring
    linarith
  have hb : 2 * ((2 : ℝ) ^ (r₃ + 1 + r₂)) / deltaZero etaR eT ≤ (2 : ℝ) ^ b₁ := by
    refine le_trans ?_ (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hleB)
    rw [hbBdef]
    exact ParameterSchedule.le_two_pow_leastPowTwoExp _
  have hgateDens :
      ((2 : ℝ) ^ (r₃ + 1 + r₂)) / 2 ^ b₁ ≤ deltaZero etaR eT / 2 := by
    rw [div_le_iff₀ hd0] at hb
    rw [div_le_div_iff₀ hpow (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hdt : ParameterSchedule.deltaTerm etaR ETv ≤ deltaZero etaR eT :=
    deltaTerm_le_deltaZero (le_of_lt hetaR0) heT heTle
  refine ⟨Awrap, r₂, b₁, e, hAw, hTr₂, ⟨hgates, howner⟩, hlam,
    terminalEntry_of_ownerThreshold hq₂16 hlam le_rfl, ?_, hlow, hdt⟩
  exact extensionCallFour_of_width hT4 (by omega) hexp (by omega) hlow hsupply
    hgateDens (by norm_num)

/-! ## Section 14  Statement poles

A green build sees none of these failure modes. -/

/-- **Statement pole 1: `eq:wrapper-total-early-mass` needs a first-Bob node.**

The frozen display is *strict*.  At an empty first-Bob set both sides are zero and
`0 < 0` is false, so the nonemptiness binder of `wrapperTotalEarlyMass` is not
decoration: dropping it would make the statement false, not merely weaker.  (In
the frozen argument the corner is harmless -- with no first-Bob node the early
mass is zero and the redistribution proceeds -- but a Lean statement that asserted
the strict bound unconditionally would be wrong.) -/
theorem totalEarlyMass_needs_a_first_bob_node :
    ¬ (∀ (B : Finset (Fin 3)) (Pv κv : Fin 3 → ℝ) (cf e0 : ℝ), 0 < cf →
        (∀ v ∈ B, Pv v < cf * κv v) →
        (∑ v ∈ B, κv v ≤ e0 / (1 - vartheta)) →
        ∑ v ∈ B, Pv v < cf * (e0 / (1 - vartheta))) := by
  intro h
  have := h ∅ (fun _ => 0) (fun _ => 0) 1 0 (by norm_num) (by simp) (by simp [vartheta])
  simp at this

/-- **Statement pole 2: the four-category table is tight.**

`09:1600--1606` sums the four budgets to `7/8` of `eta_R`, leaving a strict
margin.  Were the third line's budget `eta_R/2` instead of the frozen
`eta_R/4` -- i.e. were "Bob-heavy" defined at `eta_R/2` -- the total would be
`9 eta_R/8 > eta_R` and the retention conclusion `1 - total > 1 - eta_R` would
**fail**.  So `09:1579`'s `eta_R/4` is load-bearing and the contrapositive is not
an artifact of loose bookkeeping. -/
theorem fourCategory_budget_is_tight :
    (1 : ℝ) / 16 + 1 / 16 + 1 / 4 + 1 / 2 = 7 / 8
      ∧ (7 : ℝ) / 8 < 1
      ∧ ¬ ((1 : ℝ) / 16 + 1 / 16 + 1 / 2 + 1 / 2 < 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Statement pole 3: `eq:wrapper-good-to-good` needs all three owner gates.**

Drop the third gate `q_2 >= 64 mu_P q/eta_R` -- i.e. let `q_2` be small against
`q/eta_R` -- and the summed contribution `2 mu_P (2q/q_2)` alone can exceed
`eta_R/4`, so the frozen strict comparison `3 eta_R/16 < eta_R/4` never gets a
chance to apply.  A REJECTION PROBE at values chosen to fire the guard: at
`mu_P = 1/184`, `q = 2^20`, `q_2 = 2` and `eta_R = 1/16` the third term already
exceeds `eta_R/4 = 1/64`.  No legality is claimed for those values. -/
theorem goodToGood_needs_the_third_gate :
    (1 : ℝ) / 64 < 2 * muP * (2 * (2 ^ 20 : ℝ) / 2) := by
  norm_num [muP]

/-- **Statement pole 4: the terminal endpoint is not the empty bound.**

`09:1774--1778` concludes `B_cap + log_2 kappa = C` at `T_*`, and `C` is the
banked `terminalTarget`, which is strictly positive.  A restatement that weakened
the endpoint to `0` would be the triviality `0 <= comp Z`; the frozen endpoint is
not that. -/
theorem terminalEndpoint_is_not_trivial (bcap r₂ r₃ : ℕ) :
    0 < bcap + (r₃ + 1 + r₂) := by
  rw [terminalEndpoint_identity]
  exact TerminalTwoStream.terminalTarget_pos bcap r₂ r₃

/-- **Statement pole 5: `u_don >= 8s` genuinely needs `delta_0 <= 1`.**

`09:1742--1744` first rules out `delta_0 >= 1` and only then concludes
`u_don >= 8s`.  Without that step the least-power-of-two definition gives nothing:
at `delta_0 = 8` and `s = 1` the width `u_don = 1` already satisfies
`u_don delta_0 >= 8s`, and `8s = 8 > 1 = u_don`.  So the frozen order of the two
steps is load-bearing.  A REJECTION PROBE; no legality is claimed. -/
theorem uDon_bound_needs_delta_le_one :
    8 * ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) * 8 ∧ ¬ (8 * 1 ≤ (1 : ℕ)) := by
  refine ⟨by norm_num, by norm_num⟩

/-- **Statement pole 6: the bridge to `hDenseRung` is not vacuous.**

`denseRung_of_no_shallow_member` would be worthless if its `hmember` binder were
automatically true.  It is not: the achievable-cost set is always nonempty, so a
binder demanding `C + r <= c` for **every** achievable cost genuinely constrains
the matrix.  Concretely, on the constant `false` game the cost `0` is achievable,
so `hmember` fails for every `C + r >= 1`. -/
theorem denseRung_member_binder_is_not_vacuous :
    (0 : ℕ) ∈ AchievableCosts (fun _ _ : Unit => false) := by
  exact ⟨Workspace.Types.Protocol.Protocol.leaf false, rfl, by intro a b; rfl⟩

/-- **Statement pole 7 (`r5`): the conditional endpoint is not satisfied by a
trivial width.**

`BlockGates` is an existential deliverable in `A_wrap`, and the trivial witness
`q = 1` fails it: the banked
`ParameterSchedule.terminalWrapperGates_refuted_at_unit_width` refutes the first
row at a degenerate interlace width for every choice of the other four
parameters.  So the endpoint of Section 13 is not "some tuple exists" -- it is a
statement about a width that grows with the audit constant. -/
theorem blockGates_refuted_at_unit_width (q₂ b₁ ETv utermv Bthetav tref : ℕ)
    (etaR g : ℝ) : ¬ BlockGates 1 q₂ b₁ ETv utermv Bthetav tref etaR g := by
  rintro ⟨hgates, -⟩
  exact ParameterSchedule.terminalWrapperGates_refuted_at_unit_width
    ETv utermv Bthetav tref hgates

/-! ## Section 15  The aux-lemma battery

General sanity properties of the objects this module introduces: identities,
monotonicities, round-trips, and the two regime separations.  An unprovable
member would disqualify the encoding. -/

/-- **Aux battery 1 (the hardest field of `ExtensionCallFour`, generally).**
`ambient_width` couples the width exponent `e`, the Stage-3 exponent `r_3` and
the Stage-2 exponent `r_2`; it is discharged from `09:1744`'s width floor in
its exponent form `r_3 + 3 <= e` alone, at every `r_2`.  General. -/
theorem extensionCallFour_ambient_width_holds {e r₂ r₃ : ℕ} (h : r₃ + 3 ≤ e) :
    2 * terminalCapacity (2 ^ r₃) (2 ^ r₂) ≤ 2 ^ (e - 1) * 2 ^ r₂ := by
  have hpow : (2 : ℕ) ^ (r₃ + 1 + r₂ + 1) ≤ 2 ^ ((e - 1) + r₂) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 * terminalCapacity (2 ^ r₃) (2 ^ r₂)
      = 2 ^ (r₃ + 1 + r₂ + 1) := by rw [terminalCapacity_dyadic, pow_succ]; ring
    _ ≤ 2 ^ ((e - 1) + r₂) := hpow
    _ = 2 ^ (e - 1) * 2 ^ r₂ := by rw [pow_add]

/-- **Aux battery 2 (identity).**  The frozen terminal capacity is the banked
`Kint` at `kappa = 2`, and its dyadic form has exponent `r_3 + 1 + r_2`; the two
readings agree.  A round-trip between the general block count and the frozen
row-(iv) substitution. -/
theorem terminalCapacity_roundTrip (r₃ r₂ : ℕ) :
    terminalCapacity (2 ^ r₃) (2 ^ r₂) = Kint (2 ^ r₃) 2 (2 ^ r₂)
      ∧ terminalCapacity (2 ^ r₃) (2 ^ r₂) = 2 ^ (r₃ + 1 + r₂) :=
  ⟨rfl, terminalCapacity_dyadic r₃ r₂⟩

/-- **Aux battery 3 (monotonicity).**  The entering column density of row (iv) is
antitone in the width exponent: a wider donor product enters at a lower density,
exactly as `h = rho_0 2^{-u_don-1}` demands.  General. -/
theorem callFourH_antitone {e e' : ℕ} (h : e ≤ e') : callFourH e' ≤ callFourH e := by
  have hpow : (2 : ℝ) ^ (2 ^ e + 1) ≤ (2 : ℝ) ^ (2 ^ e' + 1) := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    have : (2 : ℕ) ^ e ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) h
    omega
  have h0 : (0 : ℝ) < (2 : ℝ) ^ (2 ^ e + 1) := by positivity
  unfold callFourH
  exact div_le_div_of_nonneg_left (le_of_lt rhoZero_pos) h0 hpow

/-- **Aux battery 4 (monotonicity).**  The owner threshold `delta_i` is monotone
in the baseline deficit `eps_i`, which is what makes
`eq:wrapper-baseline-deficit-sum` usable as a bound on `sum_i delta_i`.
General. -/
theorem ownerThreshold_mono {q₂ b₁ : ℕ} {e e' : ℝ} (h : e ≤ e') :
    ownerThreshold q₂ b₁ e ≤ ownerThreshold q₂ b₁ e' := by
  unfold ownerThreshold; linarith

/-- **Aux battery 5 (round-trip).**  `delta_0` inverts its defining relation: at
a positive exceptional count, `8 e_T mu_P delta_0 = eta_R`, so the frozen density
carries exactly the mass the pigeonhole delivered and nothing more.  General. -/
theorem deltaZero_roundTrip {etaR : ℝ} {eT : ℕ} (heT : 0 < eT) :
    8 * (eT : ℝ) * muP * deltaZero etaR eT = etaR := by
  have heTR : (0 : ℝ) < (eT : ℝ) := by exact_mod_cast heT
  have hmuP : (0 : ℝ) < muP := muP_pos
  unfold deltaZero
  field_simp

/-- **Aux battery 6 (identity, `eq:wrapper-exceptional-count` composed).**  The
two clauses of `wrapperExceptionalCount` chain into the single frozen bound
`e_T <= e_0/(1-vartheta) + e_B`, which is the form `09:1723--1725` consumes.
General. -/
theorem wrapperExceptionalCount_chained {nT jgood c eB KB q e0 : ℝ}
    (hjgood : jgood = c - eB) (hKB0 : 0 ≤ KB) (hkraft : KB + nT ≤ q)
    (hclean : q - e0 / (1 - vartheta) ≤ c) :
    nT - jgood ≤ e0 / (1 - vartheta) + eB := by
  obtain ⟨h1, h2⟩ := wrapperExceptionalCount hjgood hKB0 hkraft hclean
  linarith

/-- **Aux battery 7 (identity -- the seam test for the banked `lambda_0`).**

The banked `eq:terminal-entry` is, clause for clause, "`q_2 >= 16`,
`lambda_0 <= 1/8`, and the owner threshold of `eq:wrapper-owner-threshold` is at
most `delta'`".  The proof is `Iff.rfl`: the two sides are **definitionally**
equal.  This is the unit test the `r0` draft failed -- with a second local
`lambda_0` (even one propositionally equal to the banked constant) the two sides
are only propositionally equal and `Iff.rfl` does not typecheck.  General in the
two widths and the two reals. -/
theorem terminalEntry_iff_ownerThreshold (q₂ b₁ : ℕ) (epsI δ' : ℝ) :
    TerminalTwoStream.terminalEntry q₂ b₁ epsI δ'
      ↔ 16 ≤ q₂ ∧ DenseBranchSelection.lambdaZero q₂ b₁ ≤ 1 / 8
          ∧ ownerThreshold q₂ b₁ epsI ≤ δ' := Iff.rfl

/-- **Aux battery 8 (round-trip on the bridge).**  `terminalEntry_of_ownerThreshold`
is inverted: from `eq:terminal-entry` one recovers exactly the owner-threshold
inequality that produced it, so the bridge loses nothing and adds nothing.
General. -/
theorem ownerThreshold_le_of_terminalEntry {q₂ b₁ : ℕ} {epsI δ' : ℝ}
    (h : TerminalTwoStream.terminalEntry q₂ b₁ epsI δ') :
    ownerThreshold q₂ b₁ epsI ≤ δ' := h.2.2

/-- **Aux battery 9 (monotonicity in the foreign density).**  `eq:terminal-entry`
is upward closed in `delta'`: raising the foreign-density threshold cannot
invalidate the entry conditions.  This is what lets the join be applied at any
`delta_i` above the owner threshold rather than at the threshold alone.
General. -/
theorem terminalEntry_mono_delta {q₂ b₁ : ℕ} {epsI δ' δ'' : ℝ}
    (h : TerminalTwoStream.terminalEntry q₂ b₁ epsI δ') (hle : δ' ≤ δ'') :
    TerminalTwoStream.terminalEntry q₂ b₁ epsI δ'' :=
  ⟨h.1, h.2.1, le_trans h.2.2 hle⟩

/-- **Aux battery 10 (antitonicity in the baseline deficit).**  `eq:terminal-entry`
is downward closed in `eps_i`: a *smaller* baseline deficit only makes the entry
condition easier, via `ownerThreshold_mono`.  Together with battery 9 this pins
the direction of both frozen monotonicities, so a sign slip in either would be
caught here rather than at the join.  General. -/
theorem terminalEntry_antitone_eps {q₂ b₁ : ℕ} {epsI epsI' δ' : ℝ}
    (h : TerminalTwoStream.terminalEntry q₂ b₁ epsI δ') (hle : epsI' ≤ epsI) :
    TerminalTwoStream.terminalEntry q₂ b₁ epsI' δ' :=
  ⟨h.1, h.2.1, le_trans (ownerThreshold_mono hle) h.2.2⟩

/-- **Aux battery 11 (the shape of every `2^{-b_1}` gate).**

`eq:stage2-structural-gates` states four of its clauses as `... 2^{-b_1} <= ...`,
and every one of them is discharged by the same dyadic comparison: an exponent
gap of `c` buys a factor `2^{-c}`.  Stated once, generally, so the `b_1`
arithmetic is not re-improvised per clause. -/
theorem two_pow_div_two_pow_le {a b c : ℕ} (h : a + c ≤ b) :
    ((2 : ℝ) ^ a) / 2 ^ b ≤ 1 / 2 ^ c := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) h

/-- **Aux battery 12 (`06:839` reduces to a dyadic comparison) -- PROVED, not
asserted.**

The claim that `q^2q_2 <= 2^{b_1}` *suffices* for the frozen
`2^{-b_1} <= delta_min/(8sqq_2)` at `delta_min = 64 B_theta L_q s/q` is
discharged here rather than left in a docstring: the frozen right-hand side
simplifies to `8 B_theta L_q/(q^2q_2)`, and `B_theta L_q >= 1` (`06:666--670`,
`06:719`) makes the numerator at least `8`, so the dyadic bound on the
denominator is enough.  Note where `s` goes: it cancels, which is exactly why the
scheduled `s >= 64` does **not** tighten this particular gate.  General in the
widths and in the product `B_theta L_q`. -/
theorem stage2_b1_gate_of_dyadic {q q₂ b₁ : ℕ} {BL : ℝ}
    (hq : 0 < q) (hq₂ : 0 < q₂) (hBL : 1 ≤ BL)
    (hdy : q * q * q₂ ≤ 2 ^ b₁) :
    (1 : ℝ) / 2 ^ b₁ ≤ 8 * BL / ((q : ℝ) * (q : ℝ) * (q₂ : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq₂R : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂
  have hD : (0 : ℝ) < (q : ℝ) * (q : ℝ) * (q₂ : ℝ) := by positivity
  have hdyR : (q : ℝ) * (q : ℝ) * (q₂ : ℝ) ≤ (2 : ℝ) ^ b₁ := by exact_mod_cast hdy
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b₁ := by positivity
  rw [div_le_div_iff₀ hpow hD]
  nlinarith [hBL, hD, hdyR]

/-- **Aux battery 13 (the schedule majorant is monotone in `s`).**

`eq:terminal-uniform-bounds` is monotone in the source scale, so raising the
scheduled floor can only raise the majorant and every downstream gate
(`q >= 8E_T`, `q > 4E_Tu_termB_theta`) must be re-solved rather than patched.
Stated over the banked `ParameterSchedule.EB`/`ET`.  General. -/
theorem ET_mono_s {Bt Lqv e0m : ℕ} {s s' : ℕ} {etaR : ℝ}
    (hetaR : 0 < etaR) (h : s ≤ s') :
    ParameterSchedule.ET e0m (ParameterSchedule.EB Bt Lqv s e0m etaR)
      ≤ ParameterSchedule.ET e0m (ParameterSchedule.EB Bt Lqv s' e0m etaR) := by
  have hc : (0 : ℝ) < (1 - ParameterSchedule.vartheta) * etaR := by
    have h1 : (0 : ℝ) < 1 - ParameterSchedule.vartheta := by
      rw [ParameterSchedule.one_sub_vartheta]; norm_num
    exact mul_pos h1 hetaR
  have hsR : ((s : ℕ) : ℝ) ≤ ((s' : ℕ) : ℝ) := by exact_mod_cast h
  have hb : (0 : ℝ) ≤ ((Bt : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ ((Lqv : ℕ) : ℝ) := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ ((e0m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcoef : (0 : ℝ) ≤ 512 * muP * ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) muP_pos.le) hb) hl
  have hnum : 512 * muP * ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ)
        * ((e0m : ℕ) : ℝ)
      ≤ 512 * muP * ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s' : ℕ) : ℝ)
        * ((e0m : ℕ) : ℝ) := by
    nlinarith [mul_nonneg hcoef he0, sub_nonneg.mpr hsR]
  have hdiv : 512 * muP * ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ)
        * ((e0m : ℕ) : ℝ) / ((1 - ParameterSchedule.vartheta) * etaR)
      ≤ 512 * muP * ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s' : ℕ) : ℝ)
        * ((e0m : ℕ) : ℝ) / ((1 - ParameterSchedule.vartheta) * etaR) := by
    rw [div_le_div_iff₀ hc hc]
    nlinarith [hnum, hc]
  have hEB : ParameterSchedule.EB Bt Lqv s e0m etaR
      ≤ ParameterSchedule.EB Bt Lqv s' e0m etaR := by
    simp only [ParameterSchedule.EB]
    exact Nat.ceil_le_ceil hdiv
  simp only [ParameterSchedule.ET]
  omega

/-- **Aux battery 14 (the two regimes, and that they are genuinely two).**

`05:420`'s scheduled `64 | s` implies Section 4's generic `s >= 4` at any
positive `s`, so a scheduled-record witness is automatically a legal Section-4
witness; the converse **fails**, and the counterexample is `s = 4`.  This is the
statement that keeps banked generic-floor witnesses from being falsely
implicated by the scheduled floor, and it keeps the scheduled floor from being
quietly weakened to the generic one.  General. -/
theorem scheduled_floor_implies_generic_but_not_conversely :
    (∀ s : ℕ, 0 < s → 64 ∣ s → 4 ≤ s) ∧ (4 ≤ 4 ∧ ¬ (64 ∣ 4)) := by
  refine ⟨fun s hs hdvd => ?_, by norm_num, by decide⟩
  obtain ⟨k, rfl⟩ := hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  · calc (4 : ℕ) ≤ 64 * 1 := by norm_num
      _ ≤ 64 * k := Nat.mul_le_mul_left 64 hk

/-- **Aux battery 15 (`eq:cover-bounds` is monotone in the singleton cover).**

`e_0^max` is a budget, so a larger cover number can only raise it.  This is what
makes the tested endpoint `B_sing <= B_sing^*` usable as an *upper* bound on
`e_0^max`: without monotonicity a bound on the search would say nothing about
the budget.  General in all four arguments. -/
theorem e0Max_mono_Bsing {Bref Bsing Bsing' Bpair k : ℕ} (h : Bsing ≤ Bsing') :
    e0Max Bref Bsing Bpair k ≤ e0Max Bref Bsing' Bpair k := by
  unfold e0Max
  omega

/-- **Aux battery 16 (`09:1730`'s `e_0^max >= 1`, proved generally).**

"Moreover `theta <= 1/160 < 18/25`, so `B_ref >= 2`; since `t_ref >= 4`,
`eq:cover-bounds` and `eq:terminal-uniform-bounds` give `e_0^max >= 1`."  The
frozen implication, at `t_ref = 2^k` with `k >= 2`: the reference term alone
contributes `(B_ref - 1)(2^{k-1} + k - 2) >= 1 . 2`.  General. -/
theorem two_le_e0Max {Bref Bsing Bpair k : ℕ} (hB : 2 ≤ Bref) (hk : 2 ≤ k) :
    2 ≤ e0Max Bref Bsing Bpair k := by
  have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ (k - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow' : (2 : ℕ) ≤ 2 ^ (k - 1) := by simpa using hpow
  have habs : ∀ E : ℕ, 2 ≤ E → 2 ≤ E + k - 2 := by intro E hE; omega
  have hcoef : 2 ≤ 2 ^ (k - 1) + k - 2 := habs _ hpow'
  have hone : 1 ≤ Bref - 1 := by omega
  unfold e0Max
  calc (2 : ℕ) = 1 * 2 := by norm_num
    _ ≤ (Bref - 1) * (2 ^ (k - 1) + k - 2) := Nat.mul_le_mul hone hcoef
    _ ≤ (Bref - 1) * (2 ^ (k - 1) + k - 2) + (Bsing - 1) := Nat.le_add_right _ _
    _ ≤ (Bref - 1) * (2 ^ (k - 1) + k - 2) + (Bsing - 1) + 2 * (Bpair - 1) :=
        Nat.le_add_right _ _

/-- **Aux battery 17 (`06:724--725` is antitone in the exceptional majorant).**

`delta_term = eta_R/(8 mu_P max{1,E_T})` shrinks as `E_T` grows, which is the
half of `09:1715--1716` that turns `e_T <= E_T` into `delta_term <= delta_0` and
hence `u_don <= u_term`.  Stated over the banked `ParameterSchedule.deltaTerm`.
General in `eta_R` and the two counts. -/
theorem deltaTerm_antitone_count {etaR : ℝ} (hetaR : 0 ≤ etaR) {a b : ℕ}
    (h : a ≤ b) :
    ParameterSchedule.deltaTerm etaR b ≤ ParameterSchedule.deltaTerm etaR a := by
  have hmuP : (0 : ℝ) < muP := muP_pos
  have ha : (1 : ℕ) ≤ max 1 a := le_max_left _ _
  have haR : (1 : ℝ) ≤ ((max 1 a : ℕ) : ℝ) := by exact_mod_cast ha
  have hmax : ((max 1 a : ℕ) : ℝ) ≤ ((max 1 b : ℕ) : ℝ) := by
    have : max 1 a ≤ max 1 b := max_le_max le_rfl h
    exact_mod_cast this
  have hpos : (0 : ℝ) < 8 * muP * ((max 1 a : ℕ) : ℝ) := by nlinarith
  rw [ParameterSchedule.deltaTerm, ParameterSchedule.deltaTerm]
  exact div_le_div_of_nonneg_left hetaR hpos (by nlinarith)

/-- **Aux battery 18 (the `E_T` floor at the Section-4 GENERIC scale floor, and
at the `eq:eta-choice` cap).**

Deliberately stated at the **generic** floor `s >= 4` of
`04:281`/`04:389`/`04:504`, not at the scheduled `64 | s` of `05:420`: it is the
statement that constrains *every* legal instantiation of a Section-4
guarded-source lemma, and weakening it to the scheduled regime would silently
exempt those.  The tolerance enters at the parameter-free `eq:eta-choice` cap
`0 < eta_R <= mu_Sigma/200 = 1/36800` (`06:203--218` with `06:133`) rather than
at a literal value -- a floor recorded at an illegal tolerance constrains
nothing.  With `e_0^max >= 1` (`09:1730`), `B_theta >= 1` and `L_q >= 1` the
frozen coefficient `512 mu_P . 16/7 = 65536/161` gives `E_T >= 936230`
**unconditionally**, so the first terminal gate forces `q > 7 . 10^6`.  General
in every argument. -/
theorem ET_ge_generic_floor {Bt Lqv s e0m : ℕ} {etaR : ℝ} (hB : 1 ≤ Bt)
    (hL : 1 ≤ Lqv) (hs : 4 ≤ s) (he0 : 1 ≤ e0m) (hetaR0 : 0 < etaR)
    (hetaR : etaR ≤ 1 / 36800) :
    936230 ≤ ParameterSchedule.ET e0m (ParameterSchedule.EB Bt Lqv s e0m etaR) := by
  have hBR : (1 : ℝ) ≤ ((Bt : ℕ) : ℝ) := by exact_mod_cast hB
  have hLR : (1 : ℝ) ≤ ((Lqv : ℕ) : ℝ) := by exact_mod_cast hL
  have hsR : (4 : ℝ) ≤ ((s : ℕ) : ℝ) := by exact_mod_cast hs
  have he0R : (1 : ℝ) ≤ ((e0m : ℕ) : ℝ) := by exact_mod_cast he0
  have hB0 : (0 : ℝ) ≤ ((Bt : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) := by nlinarith
  have hprod : (4 : ℝ) ≤ ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ) := by
    nlinarith
  have hkey : (4 : ℝ)
      ≤ ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ) * ((e0m : ℕ) : ℝ) := by
    nlinarith
  have hEB : 936229 ≤ ParameterSchedule.EB Bt Lqv s e0m etaR := by
    have hlt : (936228 : ℕ) < ParameterSchedule.EB Bt Lqv s e0m etaR := by
      rw [ParameterSchedule.EB]
      refine Nat.lt_ceil.mpr ?_
      have hmu : muP = 1 / 184 := rfl
      have hv : ParameterSchedule.vartheta = 9 / 16 := rfl
      rw [hmu, hv]
      rw [lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1 - 9 / 16) hetaR0)]
      have key : 512 * (1 / 184 : ℝ) * ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ)
            * ((s : ℕ) : ℝ) * ((e0m : ℕ) : ℝ)
          = (512 / 184 : ℝ)
              * (((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ)
                  * ((e0m : ℕ) : ℝ)) := by ring
      rw [key]
      push_cast
      nlinarith [hkey, hetaR, hetaR0]
    omega
  have hceil : 3 ≤ ⌈((e0m : ℕ) : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ := by
    have hv : (1 : ℝ) - ParameterSchedule.vartheta = 7 / 16 :=
      ParameterSchedule.one_sub_vartheta
    have h2 : (2 : ℕ) < ⌈((e0m : ℕ) : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ := by
      refine Nat.lt_ceil.mpr ?_
      rw [hv, lt_div_iff₀ (by norm_num : (0 : ℝ) < 7 / 16)]
      push_cast
      linarith
    omega
  rw [ParameterSchedule.ET]
  omega

/-- **Aux battery 19 (the same floor at the SCHEDULED scale floor).**

The companion to battery 18, and the reason the two are separate statements: on
the scheduled record `64 | s` forces `s >= 64` (`05:420`, `06:975`), and the
same frozen coefficient then gives `E_T >= 14979660` -- a sixteen-fold larger
unconditional floor.  A witness that only ever instantiates a Section-4 generic
lemma is governed by battery 18 and is **not** implicated by this bound.
General. -/
theorem ET_ge_scheduled_floor {Bt Lqv s e0m : ℕ} {etaR : ℝ} (hB : 1 ≤ Bt)
    (hL : 1 ≤ Lqv) (hs : 64 ≤ s) (he0 : 1 ≤ e0m) (hetaR0 : 0 < etaR)
    (hetaR : etaR ≤ 1 / 36800) :
    14979660 ≤ ParameterSchedule.ET e0m
      (ParameterSchedule.EB Bt Lqv s e0m etaR) := by
  have hBR : (1 : ℝ) ≤ ((Bt : ℕ) : ℝ) := by exact_mod_cast hB
  have hLR : (1 : ℝ) ≤ ((Lqv : ℕ) : ℝ) := by exact_mod_cast hL
  have hsR : (64 : ℝ) ≤ ((s : ℕ) : ℝ) := by exact_mod_cast hs
  have he0R : (1 : ℝ) ≤ ((e0m : ℕ) : ℝ) := by exact_mod_cast he0
  have hB0 : (0 : ℝ) ≤ ((Bt : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) := by nlinarith
  have hprod : (64 : ℝ) ≤ ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ) := by
    nlinarith
  have hkey : (64 : ℝ)
      ≤ ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ) * ((e0m : ℕ) : ℝ) := by
    nlinarith
  have hEB : 14979658 ≤ ParameterSchedule.EB Bt Lqv s e0m etaR := by
    have hlt : (14979657 : ℕ) < ParameterSchedule.EB Bt Lqv s e0m etaR := by
      rw [ParameterSchedule.EB]
      refine Nat.lt_ceil.mpr ?_
      have hmu : muP = 1 / 184 := rfl
      have hv : ParameterSchedule.vartheta = 9 / 16 := rfl
      rw [hmu, hv]
      rw [lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1 - 9 / 16) hetaR0)]
      have key : 512 * (1 / 184 : ℝ) * ((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ)
            * ((s : ℕ) : ℝ) * ((e0m : ℕ) : ℝ)
          = (512 / 184 : ℝ)
              * (((Bt : ℕ) : ℝ) * ((Lqv : ℕ) : ℝ) * ((s : ℕ) : ℝ)
                  * ((e0m : ℕ) : ℝ)) := by ring
      rw [key]
      push_cast
      nlinarith [hkey, hetaR, hetaR0]
    omega
  have hceil : 3 ≤ ⌈((e0m : ℕ) : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ := by
    have hv : (1 : ℝ) - ParameterSchedule.vartheta = 7 / 16 :=
      ParameterSchedule.one_sub_vartheta
    have h2 : (2 : ℕ) < ⌈((e0m : ℕ) : ℝ) / (1 - ParameterSchedule.vartheta)⌉₊ := by
      refine Nat.lt_ceil.mpr ?_
      rw [hv, lt_div_iff₀ (by norm_num : (0 : ℝ) < 7 / 16)]
      push_cast
      linarith
    omega
  rw [ParameterSchedule.ET]
  omega

end EthInapproximability.ParameterizedNP.WrapperMassRedistribution
