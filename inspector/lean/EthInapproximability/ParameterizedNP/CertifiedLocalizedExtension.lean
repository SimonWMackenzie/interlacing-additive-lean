import EthInapproximability.ParameterizedNP.TerminalFixedBinAssembly
import EthInapproximability.ParameterizedNP.RestrictionDatum

/-!
# Parameterized NP route: `thm:certified-localized-extension` and `eq:certified-E3`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every hash below was recomputed first-hand this
  tranche.
  * `A-certified-stopping.tex`
    (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`):
    * **`A:4--8`, the interface boundary this repair turns on**: "The first
      wrapper needs a lower bound at a certified scale `H` that can be smaller
      than the exact complexity of its reference matrix.  This is not the literal
      inherited Localized Extension corollary, whose target is `comp M`.  We
      therefore state and prove the limited reference-stopping lemma actually
      consumed by the wrapper."  `thm:certified-localized-extension` and the
      inherited corollary are **two different theorems with two different widths**
      (`t_ref` and `t_2`) and two different density bundles; the pre-repair
      generation of this module conflated them.
    * `A:104--107`, "For compatibility with the parameter schedule, the notation
      `t_0(3/5)` means the single integer `t_cert`", together with `A:16--18`
      ("Put once and for all `y_* = 3/5`.  No arbitrary real is an input to the
      cutoff computation below") -- the **defining display** of `y_*`, reified as
      `yStar`.
    * `A:26` (the display `A:25--27` inside `lem:certified-width-cutoff`,
      `A:22--54`), `t_cert := 2^{2^20}`, and `A:28` "It is a computable power of
      two divisible by `16`" -- the **defining display** of `t_cert`, reified as
      `tCert` with `sixteen_dvd_tCert` and `tCert_pos`.
    * `A:120` (`eq:certified-pt-ht`), `p_t = 9t/16` -- consumed by pin from
      `RestrictionDatum.certifiedPt`, never restated.
    * `A:122`, `h_t = 2^{-2^{0.49 sqrt(log_2 t)}}` -- consumed by pin from
      `HardSeedFacade.hardSeedColumnDensity` at `log_2 t`, with the identity
      recorded as `hardSeedColumnDensity_eq_ht`.
    * **`A:109--146`, this module's target**, `thm:certified-localized-extension`:
      the ambient guards `A:111--112` (`M` nonempty with `m` rows, `H >= 2`,
      `0 < x <= 1`), `eq:certified-base` (`A:113--116`), the **width binder**
      `A:117--118` (`t >= t_cert`, a power of two divisible by `16`, `t x <= 1`),
      the copy binders `A:125` (`r, r'` positive powers of two with `r' <= r`,
      `q = r t`), the family clause `A:126--128` (a `(q,t,eps)`-balanced family
      with `0 < eps < 1`, **or** the exact full product, in which case `eps = 0`),
      the parameter clause `A:128--129` (`h in (0,1]`, `a^sharp in {0,1}`), the
      two side inequalities `eq:certified-E1` (`A:131--134`) and `eq:certified-E2`
      (`A:135--136`), the restriction clause bundle `A:138--141`, and the
      conclusion **`eq:certified-E3`** (`A:142--145`), `H + log_2(r' t)`.
      **`t`, `h` and `a^sharp` are the theorem's own free binders**; nothing in
      `A:109--146` assigns them, and `eq:certified-E1`/`eq:certified-E2` are the
      only constraints linking them.
    * `A:148--162` (`lem:certified-row-ladder`) -- consumed by pin from the
      **proved** `TerminalTwoStream.certifiedRowLadder_of_base`; not restated and
      not re-derived.
    * `A:285--329`, the stopping argument, read first-hand to census exactly what
      a Lean proof of `thm:certified-localized-extension` still needs (see the
      open-obligation note below).
  * `06-parameter-schedule.tex`
    (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    * **`06:557--575` (`eq:tref-search`, label `06:571`), the certified reference
      width**: "Let `k_ref` be the least integer satisfying
      `k_ref >= max{2^19, c_seed L_P^2, clog_2(t_0(3/5))}`, ... ,
      `t_ref = 2^{k_ref}`", followed by `06:573--575`: "The `clog_2(t_0(3/5))`
      term verifies the sufficiently-large-width hypothesis in
      `thm:certified-localized-extension`".  With `A:104--107` this is the
      **defining display** of the only width at which `A:117`'s `t >= t_cert` is
      supplied by the schedule; `certifiedWidthLeg_of_kRefFloor` derives it.
    * **`06:763--773` (`eq:t2-search`, label `06:772`), by contrast**: "Let `k_2`
      be the least integer satisfying `k_2 >= max{4, 2^19, m_HS}`, ... ,
      `t_2 = 2^{k_2}`".  There is **no** `t_0(3/5)` term here, and `2^19 < 2^20`,
      so `A:117` is *not* suppliable at `t_2`; `tCert_not_le_two_pow_t2_floor`
      records that arithmetic.  This is the defect the repair removes.
    * `06:533--539` (`eq:Q-theta-choice`), `theta = c_theta/(2Q) = delta/(16Q)` --
      the value `h` takes at both certified sites, consumed by pin as a free real
      here and never restated.
    * `06:1102--1167` (`sec:extension-call-ledger`) is the **inherited**
      corollary's call table, not this theorem's: `06:1105--1106`, "There are
      exactly four uses of the inherited Localized Extension corollary in one
      level", closed at `06:1166--1167`, "No other invocation of the inherited
      corollary occurs in the proof", with common binders `t = t_2`,
      `x = 2^{-b_1}` (`06:1107--1113`) and row (ii) at `h = 49/64`,
      `a^sharp = 1` (`06:1140--1145`).  **Those numerals are call-(ii) data and
      appear in no declaration below.**
  * `09-first-wrapper.tex`
    (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`):
    * **`09:311--327` (inside `sec:wrapper-low-rungs`, label `09:275`), the first
      genuine invocation**: "Apply the certified-scale reference stopping lemma,
      `thm:certified-localized-extension`, using its fixed `y_* = 3/5` and the
      substitutions `M = G`, `H = C-1`, `x = x_T`, `t = t_ref`, `r = q/t_ref`,
      `r' = kappa_j/t_ref`, `eps = 0`, `h = theta`, `a^sharp = 0`", with
      `09:325--327` "the reference restriction is a full product, so its
      balancedness error is exactly zero; and `q/4 >= t_ref` makes all three
      values of `r'` legal".  This is the **canonical instance**, registered below
      as `CanonicalReferenceStoppingCall`.
    * **`09:1268--1276`, the second genuine invocation**: "Put `vartheta = 9/16`.
      We first close any first-Bob node satisfying `W_v >= vartheta kappa_v`.
      When `kappa_v >= t_ref`, follow the denser Bob child and invoke the
      certified-scale reference stopping lemma on `G` with `r' = kappa_v/t_ref`,
      `a^sharp = 1`.  The other parameters are those of
      `sec:wrapper-low-rungs`.  This gives residual complexity at least
      `C + log_2 kappa_v - 1`."  So `h = theta` at **both** certified sites, and
      the child followed there is **Bob's**.
    * `09:937--938`, `r_2 = log_2 q_2` and the stopping rule.
    * `09:953--954`, "At an isolation node `v` of depth `d_v`, put
      `kappa_v = 2^{r_2 - d_v}`", and `09:995--996`, "If `d_v` is the suffix depth
      of this node, then `kappa_v = 2^{r_2 - d_v}`" -- the **defining display** of
      the capacity, already banked as `DenseWeightedCount.stoppingCapacity` and
      consumed by pin here.
    * `09:1008--1012`, "Following the denser Alice child leaves typed density at
      least `49/128 > 9/25`" -- the post-query column density of call (ii) and the
      ceiling the odd-copy rung consumes.
    * `09:1014--1023`, the **terminal two-stream dispatch**: "If
      `kappa_v >= t_2`, select `9 kappa_v/16` ordinary coordinates, trim each to
      support `kappa_v 2^{-b_1}`, and invoke Localized Extension at the fixed
      physical width `t_2`.  This is exactly call (ii) in
      `sec:extension-call-ledger`; ...  If `2 <= kappa_v < t_2`, the inherited
      two-copy and odd-copy bounds give the same target.  If `kappa_v = 1`, the
      positive excess in `eq:terminal-first-alice` supplies either an unsplit
      attached pair or two ordinary coordinates."  Its first branch names the
      **inherited** corollary at width `t_2`, *not*
      `thm:certified-localized-extension`; see the scope note below.
    * `09:1023--1028`, the closing sentence "In every case one Alice child has
      complexity at least `B_cap + log_2 kappa_v`, which exceeds
      `eq:terminal-stage2-budget`" -- the target of `AliceChildCertificate`.
  * `07-one-level-construction.tex`
    (SHA-256 `4B593DFF2FADE0C9BED9AAFB374F2ADA0A81E8CB7CFD7D937631CFE9A6EED0A3`),
    `07:209--213` (`eq:stage1-robust-certificate`, display `209--213`, label
    `212`): `Lambda_3(M_1^T, 1, 2^{-b_1}, 3/5) >= B_cap`.  The column argument is
    the literal `3/5`, which is `A:16--18`'s `y_*`; this is the value the readout
    of §7 fires the banked frontier theorem at.
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and occurs in no hypothesis of this module: `A:126--128`'s balanced
  family enters only through the **`eps` legality disjunction**, carried as an
  explicit named hypothesis, never as an axiom (see the F3 note below).
  `LegacyNPCC.Stage12` -- whose closure reaches the cited AGHP balanced-family
  axiom -- is **not** imported, directly or transitively: the two imports are
  `TerminalFixedBinAssembly` and `RestrictionDatum`, whose ledger rows record the
  same exclusion.  No new `axiom` is declared and no opaque certificate is
  introduced.

## What this generation is: the licensed F1--F4 repair

The previous generation of this file (SHA-256
`F83ECE29FF219F22067ED4B2A9D496A041A27C0780717640E81AAA734B837F7C`, 31
declarations) was judged **BLOCK** on three declarations plus its provenance
prose.  This generation edits exactly those, under the licensed opening:

* **F1 (statement-level).**  `CertifiedExtensionEndpoint` carried the width guard
  as `tCert <= 2 ^ k_2`, i.e. on the **`t_2`** binder.  `eq:t2-search`
  (`06:763--773`) has floor `2^19` and **no** `t_0(3/5)` clause, while
  `tCert <= 2^{k}` needs `2^20 <= k`; the premise was therefore unsuppliable at
  the paper's own `t_2`.  **Repair:** `t` is restored as the theorem's own free
  natural binder with exactly `A:117--118`'s gates -- `tCert <= t`, `t` a power of
  two (`t = 2 ^ kt`), `16 | t`, `t x <= 1` -- and the width leg is *exhibited* as
  suppliable at `t_ref` by `certifiedWidthLeg_of_kRefFloor`, from
  `eq:tref-search`'s own `clog_2(t_0(3/5))` term.
* **F2 (statement-level, widened scope).**  The endpoint's density bundle was
  `h = 49/64`, `a^sharp = 1`, `h 2^{-a^sharp} = 49/128`, and its row density was
  `x = 2^{-b_1}` -- all three are **call-(ii)** data of the *inherited* corollary
  (`06:1107--1113`, `06:1140--1145`).  The two genuine certified sites use
  `h = theta` (`09:322`, `09:1275`) with `a^sharp = 0` then `1`, at `x = x_T`.
  **Repair:** `x`, `h` and `a^sharp` are restored as free binders with exactly
  `A:112` and `A:128--129`'s gates; **no call-(ii) numeral survives anywhere in
  this module's three repaired declarations**.  Freeing `x` alongside `h` and
  `a^sharp` is forced by the same finding: `x = 2^{-b_1}` is `06:1110` call-table
  data, and retaining it while freeing `t` would produce exactly the hybrid
  endpoint F2 warns against (`t x <= 1` at `t = t_ref` would read
  `k_ref <= b_1`, which the schedule nowhere supplies, whereas at `x = x_T` it is
  the banked `WrapperLowRungs.simple_gate_forces_tRef_row_legality`).
* **F3 (statement-hygiene).**  `A:126--128`'s family clause was encoded as the
  tautology `(0 : ℝ) = 0`.  **Repair:** `eps` is a free real and the clause is the
  genuine disjunction `(0 < eps ∧ eps < 1) ∨ eps = 0`, with `1 + eps` appearing in
  `eq:certified-E1` and `eq:certified-E2` where the frozen displays put it.
  `epsBranch_bounds` proves the clause has content and
  `epsBranch_rejects_neg_one` exhibits a real it excludes.  What is *not* encoded
  is the provenance half ("`Mhat` is formed from a `(q,t,eps)`-balanced family"):
  that is `EXPANDER-001`, which by design has no Lean declaration, so `Mhat`
  enters only through the restriction datum and the `eps` legality clause.
* **F4 (record defect).**  The header and §5 attributed
  `thm:certified-localized-extension` to the `09:1014--1023` terminal dispatch,
  whose first branch invokes the **inherited** corollary at width `t_2`.
  **Repair:** the module is re-paired to the theorem's two genuine sites,
  `09:311--327` and `09:1268--1276`, per `A:4--8`.

The other **28** declarations are untouched: their statements and proofs are
byte-identical to the `F83ECE29` pin, and no docstring of any of them was edited.

## Scope note: what this module does *not* supply after the repair

Branch 1 of the terminal dispatch (`09:1014--1019`, `kappa_v >= t_2`) invokes the
**inherited** Localized Extension corollary at width `t_2` -- call (ii) of
`06:1140--1145`.  That corollary is a *different* theorem from
`thm:certified-localized-extension` (`A:4--8`), and this module states only the
latter.  So after the repair:

* branches 2 and 3 of the terminal dispatch remain **discharged outright** below,
  from the banked row ladder and pair certificate;
* **branch 1 of the terminal dispatch is no longer claimed by this module** and is
  an open, ledger-registered item: it needs the inherited corollary at `t_2`, not
  anything stated here.  The pre-repair generation supplied it from
  `CertifiedExtensionEndpoint`, and that was the F1/F2/F4 defect.

`aliceChild_at_large_capacity` survives the repair as what it genuinely is: the
generic lift of `eq:certified-E3` along the T1 residual comparison to a
**child-cost** certificate, anchored at `09:1268--1276`, the certified lemma's own
child site.  Note that the child exhibited there is the **denser Bob child**
(`09:1269--1270`); `AliceChildCertificate` is child-agnostic (`∃ b : Bool`), so the
lift is sound, but the name is legacy and no declaration below feeds this theorem
into the terminal close.

## What the terminal dispatch costs, branch by branch

Writing `kappa_v = 2^ell` with `ell = r_2 - d_v` (`09:953--954`, `09:995--996`)
and `t_2 = 2^{k_2}`, the frozen trichotomy of `09:1014--1023` is the trichotomy
of `ell` against `k_2` (`capacity_trichotomy`), and:

1. **`kappa_v = 1`, i.e. `ell = 0` (`09:1021--1023`).**  **Discharged outright.**
   The frozen "unsplit attached pair or two ordinary coordinates" is the banked,
   *proved* `TerminalCertificateInputs.topTwoCopy_residual_at_pair_floor`, which
   gives `B_cap + 1` where the target is `B_cap + 0`.  No new hypothesis.
2. **`2 <= kappa_v < t_2`, i.e. `1 <= ell < k_2` (`09:1019--1021`).**
   **Discharged outright.**  The frozen "inherited two-copy and odd-copy bounds"
   are the `ell`-th rung of the banked, *proved*
   `TerminalTwoStream.certifiedRowLadder_of_base`, whose copy count
   `2^{ell-1} + 1` is exactly the odd count the frozen sentence names and whose
   row density `2^{ell} 2^{-b_1}` is exactly the `09:1015` trim
   `kappa_v 2^{-b_1}`.  No new hypothesis.
3. **`kappa_v >= t_2`, i.e. `k_2 <= ell` (`09:1014--1019`).**  **NOT supplied by
   this module** -- see the scope note above.  The frozen sentence invokes the
   *inherited* corollary "at the fixed physical width `t_2`", and this module
   states `thm:certified-localized-extension`, which `A:4--8` distinguishes from
   it.  The pre-repair generation discharged this branch from
   `CertifiedExtensionEndpoint`; that was the F1/F2/F4 conflation and the licence
   removes it.  The branch is an open, ledger-registered item.

`certifiedE3_of_datum` still carries the whole `A:138--141` clause bundle on the
datum -- `Dat.selCard_eq`, `Dat.rowFloor_le_rowsPerBlock`,
`Dat.colFloor_le_colDens`, `Dat.card_row_pos` -- and now also reads `A:128--129`'s
`h in (0,1]` and `a^sharp in {0,1}` off the datum's own `h_pos`, `h_le_one` and
`aSharp_le_one` fields.  So the free-parameter class that
`LARGE-CAPACITY-BRANCH-001` items (18), (20) and (21) recorded stays dead: no
caller chooses a block census, a per-block row count, a column density, a
row-carrier nonemptiness, or the `a^sharp` legality.  The pre-repair generation
routed the same discharge through the banked adapters
`RestrictionDatum.hcount_ofDatum`, `.hrows_ofDatum`, `.hcol_ofDatum` and
`.hGne_ofDatum`; those are stated only at `r' = 2^{l-k}`, `t = 2^k`,
`a^sharp = 1`, which is precisely the call-(ii) shape F2 removes, so the repaired
proof consumes instead the *general* banked lemmas they are themselves built from
(`RestrictionDatum.selCard_eq`, `.rowFloor_le_rowsPerBlock`,
`.colFloor_le_colDens`, `.card_row_pos`, `.certifiedPt_pos`), by pin and with no
restatement.

## The open obligation this tranche **registers** rather than closes

`thm:certified-localized-extension` itself is **not proved here**, and no
declaration below has `CertifiedE3` as an unconditional conclusion.  Its frozen
proof needs two ingredients that the development does not have:

* the certified hard seed `eq:certified-hard-seed` (`A:202--281`), which invokes
  the inherited iterated-partition endpoint
  `eq:contract-iterated-seed-domain`--`eq:contract-iterated-seed-output` at the
  literal substitution `(k,u,p,x,z,H) = (K,u,17,32x,y_*^2,H+5)` (`A:217--223`)
  together with `lem:certified-width-cutoff` (`A:22--54`); neither the iterated
  contract nor the cutoff lemma has a Lean declaration;
* the stopping argument `A:285--329`, which walks an alleged protocol for the
  restriction, retains a half-column child at each Bob query and a half-block
  child at each Alice query (`eq:certified-stopping-state`, `A:296--304`), and
  closes through the relaxed-to-classical transfer followed by
  `EthBridge.member_max_projection` (`A:307--313`).

So the honest reading of this module is: `eq:certified-E3` is now **asserted, at
the frozen substitution, with its restriction clauses carried by a real
restriction**, and it is **consumed exactly where the frozen text consumes it**.
Its own proof is a registered, deferred obligation.  Census item 9 of
`TerminalFixedBinAssembly` (the routed object system is not constructed from a
protocol) is **untouched**: every declaration below still quantifies over given
node data, and `hDenseRung` is neither discharged nor fed.

## Predecessor modules consumed **by pin**, never restated

* `RestrictionDatum`: the structure `RestrictionDatum` (whose `block_count` field
  carries `certifiedPt`, the `A:120` display, and whose `h_pos`, `h_le_one`,
  `aSharp_le_one` fields carry `A:128--129`), the frozen quantities
  `certifiedPt` (`A:120`), `certifiedRowFloor` (`A:139--140`) and
  `certifiedColFloor` (`A:141`), the readouts `selCard`, `rowsPerBlock` and
  `colDens`, the general readout lemmas `selCard_eq`, `rowFloor_le_rowsPerBlock`,
  `colFloor_le_colDens` and `card_row_pos`, `certifiedPt_pos`, and
  `sixteen_dvd_two_pow`.  The `a^sharp = 1`, `r' = 2^{l-k}`, `t = 2^k` adapters
  `hcount_ofDatum`, `hrows_ofDatum`, `hcol_ofDatum`, `hGne_ofDatum` are **no
  longer consumed here**: their index shape is the call-(ii) shape F2 removes.
* `TerminalFixedBinAssembly`: `stage2_frontier_from_certificates`,
  `stage2_no_alleged_protocol_at_forced_child`.
* `TerminalCertificateInputs`: `liftRows`, `pairRows`, `pairFloor`,
  `mem_bracketGE_of_floors`, `LambdaGE_le_member`,
  `topTwoCopy_residual_at_pair_floor`.
* `TerminalTwoStream`: `CertifiedRowLadder`, `certifiedRowLadder_of_base`.
* `TerminalResidualComparison`: `RouteRows`, `RouteCols`,
  `D_le_cost_descend_of_computes`.
* `DenseWeightedCount`: `stoppingCapacity`, `descend`, `descendStep`,
  `descend_append`, `descend_cons`, `aliceNodes`, `IsQueryPath`, `IsQueryNode`,
  `probeProtocol`, `probeProtocol_cost`.
* `HardSeedFacade`: `hardSeedColumnDensity`.
* `StageOneInterlace`: `xSeed`, `xSeed_pos`, `xSeed_le_one`.
* `Workspace.Types.CommComplexity.D`, `Workspace.Types.Protocol`,
  `NPCC.subgame`, `NPCC.bracketGE`, `NPCC.LambdaGE`,
  `Workspace.Types.Interlace.interlaceFun` -- the vendored, project-axiom-free
  interface reached through `LegacyNPCC.Core`.

## Reader counterpart: NONE claimable, re-verified first-hand this tranche

`routes/parameterized-np/reader-facing/sections/` was opened again this tranche
and searched for `certified`, `Localized Extension`, `localized`, `odd-copy`,
`kappa`, `capacity` and `child`; every hit was read.  Two near misses, both
declined:

* `02-preliminaries.tex:512--526`
  (SHA-256 `11C43E154C937761D9EFB1172F8D433BE559F3D190D28742AC14B6C5A5D6FAFB`),
  `cor:paper-localized-extension`, whose conclusion `CC(G) >= D + log(r' t)`
  (`02:524`) prints the same right-hand side as `eq:certified-E3`.  It is the
  **uncertified** corollary: no `t >= t_cert`, no `h_t`, no
  `eq:certified-E1`/`E2`, and its equipartition floor is
  `ceil(r' x_seed m)` (`02:519`) where `A:139--140` has `ceil(r' t x m)` -- the
  factor `t` that `A:5--7` calls out ("This is not the literal inherited
  Localized Extension corollary, whose target is `comp M`").  It is already
  declined on exactly this ground in the banked `WRAPPER-LOW-RUNGS-001`,
  `LARGE-CAPACITY-BRANCH-001`, `FIRST-WRAPPER-ASSEMBLY-001` and
  `RESTRICTION-DATUM-001` rows; citing it here would be a false counterpart.
* `A-stage4-details.tex:390--392`
  (SHA-256 `5B6E9BA0E271D67BF2B0525BD6D59D90C150A8170BDCE29DC74DA55AB39019C6`),
  "Its small-capacity and final-node closures use the certified row ladder
  `Cref{lem:paper-certified-row-ladder}`; they do not require a new odd-copy
  theorem", is the reader's one sentence about branches 1 and 2 of the dispatch.
  It is unnumbered proof prose (the reader-counterpart rule bars citing prose as a
  statement counterpart) **and** it is already assigned to
  `TERMINAL-TWO-STREAM-001`, with `SplitFirstBobInstance`, `DenseWrapperFrontier`
  and `FirstWrapperAssembly` recording the same assignment.  Declined.

`lem:paper-certified-row-ladder` (`02:244--256`) is claimed by
`TERMINAL-TWO-STREAM-001` and is not re-claimed here.  The reader prints no
`t_cert`, no `h_t`, no `y_*`, no `kappa_v`, no `49/128` and no three-case
dispatch at all.

## Canonical inhabitation: REGISTERED and DEFERRED, at the corrected site

The paper's own instance of `CertifiedExtensionEndpoint` is **not** the terminal
call (ii) the pre-repair generation named: it is the reference-stopping
invocation of `09:311--327`, at the substitution `M = G`, `H = C-1`, `x = x_T`,
`t = t_ref`, `r = q/t_ref`, `r' = kappa_j/t_ref`, `eps = 0`, `h = theta`,
`a^sharp = 0`.  That substitution is **registered in Lean** as
`CanonicalReferenceStoppingCall`, so the shape of the paper's own instance is
machine-checked rather than described, and its index and width legality is
*proved* at the paper's own floors by `canonicalCall_gates`.

Its **inhabitation** is deferred: it needs `G`, `x_T`, `theta` and the routed
restriction of the reference family, none of which is built, and `A:117` forces
`t >= t_cert = 2^{2^20}`, so no legal instance is `decide`-computable.  The
canonical-inhabitation obligation is therefore **ledger-registered and deferred**,
to be discharged when the reference construction lands -- never by a probe.  What
*is* proved here about instantiability is the F1 leg specifically:
`certifiedWidthLeg_of_kRefFloor` derives `A:117`'s `t >= t_cert` from
`eq:tref-search`'s own `clog_2(t_0(3/5))` term, so the premise that blocked every
consumer is now demonstrably suppliable at the paper's own width.  The two
`decide`-checkable readouts of §8 remain labelled **NON-FIDELITY** and audit our
encoding at points the frozen paper never visits.

`ladderRows` is a definition the paper *does* instantiate -- at every rung of
`09:1014--1023` -- and its two frozen instantiations are recorded as round trips:
`ladderRows_one` and `ladderRows_two` show it restricts to the banked
`TerminalCertificateInputs.liftRows` and `.pairRows` on the nose, so it is a
faithful generalization and not a new object.

## Aux-lemma battery

Every battery item is **proved**; nothing is stated and left open.

* `A` the frozen constants and the width leg, general (7): `sixteen_dvd_tCert`,
  `tCert_pos`, `yStar_eq`, `hardSeedColumnDensity_eq_ht`, `clog_two_tCert`,
  `certifiedWidthLeg_of_kRefFloor`, `certifiedWidthGates_of_kRefFloor`.
* `B` the odd-copy ladder lift, general (6): `mem_ladderRows`,
  `ladderRows_filter`, `ladderRows_fibre_card`, `ladderRows_card_le`,
  `ladderRows_one`, `ladderRows_two`.
* `C` the rung residual and its legality, general (2): `ladder_legal_of_le`,
  `ladderRung_residual`.
* `D` the certified endpoint and its canonical instance, general (6):
  `certifiedE3_of_datum`, `epsBranch_bounds`, `canonicalCall_gates`,
  `certifiedE3_at_canonicalCall`, `canonicalCall_matches_low_rung`,
  `canonicalCall_gates_nonvacuous`.
* `E` the child certificates, general (5): `capacity_trichotomy`,
  `aliceChildCertificate_of_child_game`, `aliceChild_at_unit_capacity`,
  `aliceChild_at_small_capacity`, `aliceChild_at_large_capacity`.
* `F` the close and the paper-`y` readout, general (2):
  `terminal_no_alleged_protocol_of_dispatch`, `stage2_frontier_at_paper_y`.

That is **28 general battery entries proved**, with `0` unproved, alongside
**five statement poles** (`aliceChildCertificate_is_not_free`,
`ladder_rung_needs_the_row_floor`, `certifiedE3_is_not_the_phase_one_target`,
`tCert_not_le_two_pow_t2_floor`, `epsBranch_rejects_neg_one`) and
**two NON-FIDELITY readouts** (`ladderRows_probe_is_nondegenerate`,
`aliceChildCertificate_at_probe`).

The module has **42** source declarations in all: 7 definitions (`tCert`,
`yStar`, `ladderRows`, `CertifiedE3`, `CertifiedExtensionEndpoint`,
`AliceChildCertificate`, `CanonicalReferenceStoppingCall`) and 35 theorems, with
**0** `structure`s, **0** `inductive`s, **0** `abbrev`s, **0** `instance`s and
**0** `axiom`s.

## HYPOTHESIS-CONSISTENCY note

The one premise bundle is `CertifiedExtensionEndpoint`, and it is a *hypothesis*
(an implication), never a conclusion, so it cannot be vacuously strong in the
dangerous direction: an inconsistent antecedent list would make the hypothesis
*free*.  Its antecedents are the frozen `A:111--141` list in frozen print order,
with the restriction half and the density pair read off a real `RestrictionDatum`
whose own satisfiability at the frozen side conditions is the banked
`RestrictionDatum.datum_consistent_with_frozen_side_conditions`.  No clause
conjoins two frozen items the paper states as separate cases: the `A:126--128`
alternatives are a disjunction, not a conjunction, and the three terminal-dispatch
branches are never assumed together.  (They are not, however, a partition as
encoded -- `capacity_trichotomy` proves only the three iff translations, and
`aliceChild_at_small_capacity` is stated at `ell <= k_2` rather than the frozen
`ell < k_2`.  Each branch theorem is separately proved, so the overlap costs
nothing; see `capacity_trichotomy`'s docstring.)

**What is machine-checked.**  `canonicalCall_gates_nonvacuous` *proves*, in this
module, that the whole integer half of the endpoint's antecedent list --
`A:117`'s `t >= t_cert` and `16 | t`, and `A:125`'s `r' <= r` and `q = r t` -- is
jointly satisfiable, at values taken from the paper as closed forms: `k_ref` at
`eq:tref-search`'s own floor term `clog_2(t_0(3/5))` (`06:563`), `j = 2` from the
frozen range `j in {0,1,2}` (`09:278`), and `k_q = k_ref + 2` at the boundary of
`09:327`'s `q/4 >= t_ref`.  `epsBranch_bounds` proves the `A:126--128` clause
leaves `1 + eps` in `(0,2)`, so neither side inequality is well-posed only
vacuously.  This replaces the previous generation's null `omega` probe, whose
failure carried no information.

**What remains a hand check.**  The two real-valued legs.  At the values above,
`eq:certified-E1` reads `y_*^{t_ref} <= theta 2^{-(C-1+log_2 q)}`, which is
`eq:tref-search`'s second inequality `2^{k_ref - 1} >= C_cert - 1 + log_2 q +
L_theta` (`06:564--565`) -- the exponent `2^{k_ref - 1}` dominates
`log_2(1/y_*) t_ref`'s requirement by orders of magnitude at `k_ref >= 2^20`; and
`eq:certified-E2` reads `h_{t_ref} <= theta 2^{-(C-1+k_ref)}`, which is
`eq:tref-search`'s third inequality `2^{j_49(k_ref)} >= C_cert - 1 + k_ref +
L_theta` (`06:566--567`), since `h_t = 2^{-2^{0.49 sqrt(log_2 t)}}` and
`0.49 sqrt(2^20) = 501.76`.  So after the repair the two side conditions are
*literally the paper's own terminating search inequalities*, and the schedule that
defines `t_ref` is the satisfiability argument.  Before the repair they were
stated at `t_2`, where `eq:t2-search` supplies neither (F1;
`tCert_not_le_two_pow_t2_floor`).  `eq:certified-base` constrains the matrix
rather than any numeral.  This paragraph is a hand check, not a machine-checked
one.

Machine evidence recorded by this generation
(`scratch/CertifiedLocalizedExtensionRepairProbes.lean`, disposable): `#print
axioms` for the three restated declarations, the eleven new ones, and the two
frozen constants `tCert` and `yStar` -- fourteen changed or new, sixteen probed
in all -- each depending on `propext`, `Classical.choice` and `Quot.sound` only,
and on no project axiom.  (Repaired by the `cc-t4w-r1` verify seat, judge
finding 2: the pre-verify wording called all sixteen "repaired and new".)

## Dependencies, imports and adapters

* Imports: `EthInapproximability.ParameterizedNP.TerminalFixedBinAssembly` and
  `EthInapproximability.ParameterizedNP.RestrictionDatum`.
* Proof status: **repair generation** of the `F83ECE29` pin.  Three declarations
  restated (`CertifiedExtensionEndpoint`, `certifiedE3_of_datum`,
  `aliceChild_at_large_capacity`), eleven added, twenty-eight untouched.
* Unproved placeholders, new axioms and opaque certificates: **none**.
* `hDenseRung` is **neither discharged nor fed** by this module;
  `eq:wrapper-u-dense` is asserted nowhere, the ranges `09:1184--1366`,
  `09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED exactly as `ScaleAlignOpening`
  records them, and **no route completion is claimed**.
-/

namespace EthInapproximability.ParameterizedNP.CertifiedLocalizedExtension

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.TerminalResidualComparison

/-! ## §1  The frozen constants of `A:16--18`, `A:25--28`, `A:119--123`, and the
`06:557--575` width leg

Each is reified from its own defining display, so that every value below is
obtained by evaluating this chain rather than by assignment.

**Record correction (F1), for the docstring of `tCert` immediately below.**
`tCert` is one of the 28 declarations this repair leaves byte-identical to the
`F83ECE29` pin, docstring included, so its own docstring still closes with "the
guard `A:117` enters as `tCert ≤ 2 ^ k₂`".  It no longer does: after the repair
`A:117` enters as `tCert ≤ t` on the certified theorem's **own free width
binder**, which the paper instantiates at `t_ref` (`09:319`), not at `t_2`.  The
`t_2` reading is the F1 defect; `tCert_not_le_two_pow_t2_floor` in §8 records why
it could not be supplied, and `certifiedWidthLeg_of_kRefFloor` below records how
`t_ref` supplies it. -/

section Constants

/-- **`t_cert := 2^{2^20}` (`A:26`), the uniform certified-scale width cutoff.**

This is the defining display (`A:25--27`) inside `lem:certified-width-cutoff`
(`A:22--54`), and `A:104--107`
records that "the notation `t_0(3/5)` means the single integer `t_cert`; no
function `t_0(y)` on arbitrary real inputs is used".  No numeral stands in for it
anywhere below: the guard `A:117` enters as `tCert ≤ 2 ^ k₂`. -/
def tCert : ℕ := 2 ^ 2 ^ 20

/-- **Aux A1 (`A:28`, first half).**  `t_cert` is divisible by `16`, so the
frozen natural division of `A:120` is exact at it and `certifiedPt` is the honest
`9 t/16`.  Proved through the banked `RestrictionDatum.sixteen_dvd_two_pow`. -/
theorem sixteen_dvd_tCert : 16 ∣ tCert :=
  RestrictionDatum.sixteen_dvd_two_pow (by norm_num)

/-- **Aux A2 (`A:28`, second half).**  `t_cert` is a positive power of two, so
`A:117`'s "power of two `t ≥ t_cert`" is a nonempty demand. -/
theorem tCert_pos : 0 < tCert := pow_pos (by norm_num) _

/-- **`y_* = 3/5` (`A:16--18`).**  "Put once and for all `y_* = 3/5`.  No
arbitrary real is an input to the cutoff computation below."  The same number is
the column argument of `eq:stage1-robust-certificate` at `07:210`, which is why
the F3 readout of §7 fires the banked frontier theorem at it. -/
noncomputable def yStar : ℝ := 3 / 5

/-- **Aux A3 (the identification `A:18` = `07:210`).**  The appendix's `y_*` and
the value `3/5` that `eq:stage1-robust-certificate` prints are the same real, so
firing a `y`-general theorem at `3/5` is firing it at `y_*`. -/
@[simp] theorem yStar_eq : yStar = 3 / 5 := rfl

/-- **Aux A4 (`A:122`, `h_t` is the pinned hard-seed column density).**  The
frozen `h_t = 2^{-2^{0.49 sqrt(log_2 t)}}` at `t = 2^{k}` is literally
`HardSeedFacade.hardSeedColumnDensity k` (`D:484`, `0.49 = 49/100`), so
`eq:certified-E2` below is stated at the banked quantity and no second definition
of `h_t` is introduced.  General in `k`. -/
theorem hardSeedColumnDensity_eq_ht (k : ℕ) :
    HardSeedFacade.hardSeedColumnDensity k
      = (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (k : ℝ)))) := rfl

/-- **Aux A5 (`clog_2(t_0(3/5)) = 2^20`).**

`eq:tref-search` (`06:557--571`) writes its width floor as
`k_ref >= max{2^19, c_seed L_P^2, clog_2(t_0(3/5))}`, and `A:104--107` fixes
`t_0(3/5) = t_cert`.  Evaluating that defining chain -- `t_cert = 2^{2^20}`
(`A:26`), so `clog_2 t_cert = 2^20` -- is what turns the third floor term into an
integer; no numeral is assigned in its place.  General (it is an identity of the
frozen constant). -/
theorem clog_two_tCert : Nat.clog 2 tCert = 2 ^ 20 :=
  Nat.clog_pow 2 (2 ^ 20) (by norm_num)

/-- **Aux A6 (the width leg of `A:117`, PROVED suppliable).**

`06:573--575`: "The `clog_2(t_0(3/5))` term verifies the sufficiently-large-width
hypothesis in `thm:certified-localized-extension`."  This is that sentence as a
Lean derivation: any `k_ref` above the `eq:tref-search` floor term
`clog_2(t_0(3/5))` gives `t_cert <= 2^{k_ref} = t_ref`, which is exactly `A:117`'s
first clause at the paper's own reference width.

This is the leg the pre-repair generation attached to `k_2` instead, where
`eq:t2-search` (`06:763--773`) does not supply it -- see
`tCert_not_le_two_pow_t2_floor`.  General in `k_ref`. -/
theorem certifiedWidthLeg_of_kRefFloor {kref : ℕ}
    (hfloor : Nat.clog 2 tCert ≤ kref) : tCert ≤ 2 ^ kref :=
  (Nat.clog_le_iff_le_pow (by norm_num)).1 hfloor

/-- **Aux A7 (both integer gates of `A:117` at the reference width).**

`A:117` asks for `t >= t_cert`, a power of two divisible by `16`.  At
`t = t_ref = 2^{k_ref}` the power-of-two clause is the shape itself, and the other
two follow from the single `eq:tref-search` floor term, since
`4 <= 2^20 = clog_2 t_cert <= k_ref`.  So the whole integer half of `A:117` is
suppliable from `06:561--563` alone.  General in `k_ref`. -/
theorem certifiedWidthGates_of_kRefFloor {kref : ℕ}
    (hfloor : Nat.clog 2 tCert ≤ kref) :
    tCert ≤ 2 ^ kref ∧ 16 ∣ (2 : ℕ) ^ kref := by
  refine ⟨certifiedWidthLeg_of_kRefFloor hfloor, ?_⟩
  refine RestrictionDatum.sixteen_dvd_two_pow ?_
  have h20 : (2 : ℕ) ^ 20 ≤ kref := clog_two_tCert ▸ hfloor
  have hsmall : (4 : ℕ) ≤ 2 ^ 20 := by norm_num
  omega

end Constants

/-! ## §2  The odd-copy row set of `09:1014--1015`

"select `9 kappa_v/16` ordinary coordinates, trim each to support
`kappa_v 2^{-b_1}`" -- one retained fibre per physical copy.  `liftRows` is this
at one copy and `pairRows` at two; the frozen dispatch needs it at the odd count
`2^{ell-1} + 1` of `lem:certified-row-ladder`, so the two banked constructions are
generalized here and both are recovered as round trips. -/

section LadderRows

variable {Cone : Type*} [DecidableEq Cone]

/-- **The `p`-copy row set assembled from one retained fibre per copy.**

`A:139--140` speaks of the rows retained "in each represented block", and
`09:1014--1015` trims each selected ordinary coordinate separately; the row set of
the `p`-fold interlace they jointly describe is the tagged disjoint union of the
`p` fibres. -/
def ladderRows (p : ℕ) (T : Slot p → Finset Cone) : Finset (Slot p × Cone) :=
  Finset.univ.biUnion (fun i => (T i).image (fun γ => (i, γ)))

/-- **Aux B1 (membership).**  A tagged row belongs to the ladder row set exactly
when its underlying value belongs to the fibre of its own tag.  General. -/
@[simp] theorem mem_ladderRows {p : ℕ} {T : Slot p → Finset Cone}
    {r : Slot p × Cone} : r ∈ ladderRows p T ↔ r.2 ∈ T r.1 := by
  obtain ⟨i, γ⟩ := r
  simp only [ladderRows, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨j, δ, hδ, rfl, rfl⟩
    exact hδ
  · intro h
    exact ⟨i, γ, h, rfl, rfl⟩

/-- **Aux B2 (the fibre is the fibre).**  The copy-`i` fibre of the ladder row set
is the tagged image of `T i` -- nothing leaks between copies, which is what keeps
the physical copies disjoint at `09:1006--1008`.  General. -/
theorem ladderRows_filter {p : ℕ} (T : Slot p → Finset Cone) (i : Slot p) :
    (ladderRows p T).filter (fun r => r.1 = i) = (T i).image (fun γ => (i, γ)) := by
  ext r
  obtain ⟨j, γ⟩ := r
  simp only [Finset.mem_filter, mem_ladderRows, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hγ, rfl⟩
    exact ⟨γ, hγ, rfl, rfl⟩
  · rintro ⟨δ, hδ, rfl, rfl⟩
    exact ⟨hδ, rfl⟩

/-- **Aux B3 (the frozen per-copy count).**  Hence the row floor `def:bracket-ge`
reads off copy `i` is exactly `|T i|`.  General. -/
theorem ladderRows_fibre_card {p : ℕ} (T : Slot p → Finset Cone) (i : Slot p) :
    ((ladderRows p T).filter (fun r => r.1 = i)).card = (T i).card := by
  rw [ladderRows_filter]
  refine Finset.card_image_of_injective _ ?_
  intro a b hab
  exact (Prod.mk.injEq _ _ _ _ ▸ hab).2

/-- **Aux B4 (no duplication).**  The assembled row set never exceeds the total
fibre count, so the construction adds no rows of its own.  General. -/
theorem ladderRows_card_le {p : ℕ} (T : Slot p → Finset Cone) :
    (ladderRows p T).card ≤ ∑ i : Slot p, (T i).card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  refine Finset.sum_le_sum ?_
  intro i _
  exact Finset.card_image_le

/-- **Aux B5 (round trip to the banked one-copy lift).**  At `p = 1` the ladder row
set *is* `TerminalCertificateInputs.liftRows`, the row set of the frozen
`09:943--946` one-copy certificate.  So `ladderRows` is a generalization of a
banked construction, not a competitor to it.  General. -/
theorem ladderRows_one (T : Finset Cone) :
    ladderRows 1 (fun _ => T) = TerminalCertificateInputs.liftRows T := by
  ext r
  obtain ⟨i, γ⟩ := r
  simp only [mem_ladderRows, TerminalCertificateInputs.liftRows, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨γ, h, Subsingleton.elim _ _, rfl⟩
  · rintro ⟨δ, hδ, rfl, rfl⟩
    exact hδ

/-- **Aux B6 (round trip to the banked pair lift).**  At `p = 2`, with the
ordinary fibre on copy `0` and the foreign fibre on copy `1` (`09:1006--1008`,
"ordinary tokens use its first factor and foreign tokens its second"; the foreign
token is attached to each coordinate of `Z` at `09:923--925`), the ladder row set
*is* `TerminalCertificateInputs.pairRows`.  Together with `Aux B5` this pins the
new definition against both frozen instantiations.  General. -/
theorem ladderRows_two (To Tf : Finset Cone) :
    ladderRows 2 (fun i => if i = 0 then To else Tf)
      = TerminalCertificateInputs.pairRows To Tf := by
  ext r
  obtain ⟨i, γ⟩ := r
  simp only [mem_ladderRows, TerminalCertificateInputs.pairRows, Finset.mem_union,
    Finset.mem_image, Prod.mk.injEq]
  fin_cases i <;> simp

end LadderRows

/-! ## §3  The odd-copy rung residual certificate (`09:1019--1021`)

"If `2 <= kappa_v < t_2`, the inherited two-copy and odd-copy bounds give the same
target."  The odd-copy bound is the `ell`-th rung of `lem:certified-row-ladder`,
whose copy count is `2^{ell-1} + 1` and whose row density is `2^{ell} x` -- at
`x = 2^{-b_1}` exactly the `09:1015` trim `kappa_v 2^{-b_1}`.  The ladder itself is
the banked *proved* `TerminalTwoStream.certifiedRowLadder_of_base` and is consumed
by pin. -/

section Rung

variable {Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone] [Fintype Rone]

/-- **Aux C1 (legality is inherited downwards).**  `A:118`'s `t x <= 1` at
`t = 2^{k_2}` supplies the ladder guard `2^{ell} x <= 1` at every `ell <= k_2`, so
the rungs the dispatch's middle branch uses are all legal.  General. -/
theorem ladder_legal_of_le {ℓ k : ℕ} {x : ℝ} (hx : 0 < x) (hℓk : ℓ ≤ k)
    (hlegal : (2 : ℝ) ^ k * x ≤ 1) : (2 : ℝ) ^ ℓ * x ≤ 1 := by
  refine le_trans ?_ hlegal
  have hpow : (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hℓk
  nlinarith

/-- **`09:1019--1021`, the odd-copy residual reading, PROVED.**

At a node whose `2^{ell-1} + 1` labelled fibres each meet the frozen trim floor
`ceil(2^{ell} x |C_1|)` (`09:1015`) and whose retained typed projection meets the
`z^2` ceiling, the local block of `M = M_1^T` has complexity at least `H + ell`.

The `ell = 1` instance is the banked
`TerminalCertificateInputs.topTwoCopy_residual_at_pair_floor` and the row set at
`ell = 1` is the banked `pairRows` by `ladderRows_two`; nothing is re-derived, the
ladder enters through `TerminalTwoStream.CertifiedRowLadder`.  General in both
carriers, in `H`, `ell`, `x` and `z`. -/
theorem ladderRung_residual (M1T : Cone → Rone → Bool) {H ℓ : ℕ} {x z : ℝ}
    (hlad : TerminalTwoStream.CertifiedRowLadder M1T H x z)
    (hℓ : 1 ≤ ℓ) (hlegal : (2 : ℝ) ^ ℓ * x ≤ 1)
    {T : Slot (2 ^ (ℓ - 1) + 1) → Finset Cone}
    (hrow : ∀ i, ⌈(2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ)⌉₊ ≤ (T i).card)
    {C : Finset (Slot (2 ^ (ℓ - 1) + 1) → Rone)}
    (hcol : ⌈((Fintype.card Rone : ℝ) ^ (2 ^ (ℓ - 1) + 1)) * z ^ 2⌉₊ ≤ C.card) :
    H + ℓ ≤ D (subgame (interlaceFun M1T (2 ^ (ℓ - 1) + 1))
      (ladderRows (2 ^ (ℓ - 1) + 1) T) C) := by
  have hmem : ((ladderRows (2 ^ (ℓ - 1) + 1) T, C) :
      Finset (Slot (2 ^ (ℓ - 1) + 1) × Cone) × Finset (Slot (2 ^ (ℓ - 1) + 1) → Rone))
      ∈ bracketGE Cone Rone (2 ^ (ℓ - 1) + 1) ((2 : ℝ) ^ ℓ * x) (z ^ 2) := by
    refine TerminalCertificateInputs.mem_bracketGE_of_floors (fun i => ?_) hcol
    rw [ladderRows_fibre_card]
    have hceil : (2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ)
        ≤ (⌈(2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have hstep : (⌈(2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ)⌉₊ : ℝ) ≤ ((T i).card : ℝ) := by
      exact_mod_cast hrow i
    calc (Fintype.card Cone : ℝ) * ((2 : ℝ) ^ ℓ * x)
        = (2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ) := by ring
      _ ≤ (⌈(2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ)⌉₊ : ℝ) := hceil
      _ ≤ ((T i).card : ℝ) := hstep
  exact le_trans (hlad ℓ hℓ hlegal)
    (TerminalCertificateInputs.LambdaGE_le_member (M := M1T) hmem)

end Rung

/-! ## §4  `eq:certified-E3` (`A:142--145`) and the endpoint that supplies it

Census item 8 of `TerminalFixedBinAssembly` is closed here in the only sense a
tranche can close it without proving `thm:certified-localized-extension`: the
conclusion is **named**, the frozen hypothesis list is **written down in frozen
print order**, and the `A:138--141` half of that list is **discharged from a real
restriction** through the banked `RestrictionDatum` readouts.

**Record correction (F2), for the docstring of `CertifiedE3` immediately below.**
`CertifiedE3` is one of the 28 declarations this repair leaves byte-identical to
the `F83ECE29` pin, docstring included, so its own docstring still reads
`H + log_2(r' t)` "at the call-(ii) substitution `H = B_cap`, `r' t = kappa_v`".
That substitution belongs to the *inherited* corollary (`06:1107--1113`,
`06:1140--1145`), not to `thm:certified-localized-extension`.  `CertifiedE3`
itself is substitution-neutral -- it is the plain inequality `bcap + l <= val` --
and at the theorem's two genuine sites the reading is `H = C - 1` with
`l = log_2(r' t_ref)`, which is `log_2 kappa_j` at the first site
(`09:318--321`) and `log_2 kappa_v` at the second (`09:1272`, where the capacity
is `kappa_v`, not `kappa_j`).  (Site-name split added by the `cc-t4w-r1` verify
seat, judge finding 5.) -/

section Endpoint

/-- **`eq:certified-E3` (`A:142--145`), the frozen conclusion `H + log_2(r' t)`.**

At the call-(ii) substitution `H = B_cap` (`06:1109`) and `r' t = kappa_v = 2^ell`
(`06:1124` with `09:953--954`), so `log_2(r' t) = ell` and the conclusion is
`B_cap + ell` measured against the complexity readout `val` of the object the
theorem is applied to.  It is a *statement*, never a field of any structure:
`M1--M10` keep the desired complexity conclusion out of constructor data. -/
def CertifiedE3 (bcap ℓ val : ℕ) : Prop := bcap + ℓ ≤ val

/-- **`thm:certified-localized-extension` (`A:109--146`) at the frozen call-(ii)
substitution-free, as one named conditional.**

Read against the frozen theorem, clause by clause and in frozen print order.
**Every binder the frozen theorem leaves free is a binder here**; nothing is
assigned a call-site numeral.

* `A:111` -- `M` a nonempty Boolean matrix with `m` rows, and `H >= 2`.  `M` is
  the free `M1T`, `m` is `Fintype.card Cone`, and `H` is the free `H`.
* `A:112` -- `0 < x <= 1`, at the free `x`.  (The pre-repair generation pinned
  `x = 2^{-b_1}`; that is `06:1110`, the *inherited* corollary's common binder.
  The certified sites use `x = x_T` -- `09:318`.)
* `A:113--116` -- `eq:certified-base`, `Lambda_3(M, 1, x, y_*) >= H`, at the frozen
  `y_* = 3/5` of `A:16--18`, reified as `yStar` rather than written as a numeral.
* `A:117` -- `t >= t_cert`, a power of two, divisible by `16`.  All three are
  separate clauses on the free `t`, with `kt = log_2 t` the exponent
  `eq:certified-E2` needs.  Suppliable at `t = t_ref` by
  `certifiedWidthLeg_of_kRefFloor`; *not* suppliable at `t = t_2`
  (`tCert_not_le_two_pow_t2_floor`).
* `A:118` -- `t x <= 1`, on the same free `t` and `x`.
* `A:125` -- `r, r'` positive powers of two with `r' <= r`, and `q = r t`, with
  `kr = log_2 r` and `kr' = log_2 r'`.  So `log_2 q = kr + kt` and
  `log_2(r' t) = kr' + kt`.
* `A:126--128` -- the family clause as the **genuine disjunction**: either a
  `(q,t,eps)`-balanced family with `0 < eps < 1`, or the exact full product, in
  which case `eps = 0`.  The provenance half ("`Mhat` is formed from ...") is
  `EXPANDER-001`, which by design has no Lean declaration; what is encoded is the
  legality of `eps`, which is what `eq:certified-E1`/`E2` actually consume.
* `A:128--129` -- `h in (0,1]` and `a^sharp in {0,1}`.  Both are free, and both
  are read off the datum's own `h_pos`, `h_le_one`, `aSharp_le_one` fields by
  `certifiedE3_of_datum`, so a caller cannot choose them either.
* `eq:certified-E1` (`A:131--134`): `(h 2^{-(H+log_2 q)}/(1+eps))^{1/t} >= y_*`,
  written in its equivalent `t`-th power form `y_*^t <= h 2^{-(H+log_2 q)}/(1+eps)`
  (both sides positive and `t >= 1`, so the two are interchangeable; this is also
  how the banked `RestrictionDatum.largeCapacityExtension_ofDatum` writes it).
* `eq:certified-E2` (`A:135--136`): `h 2^{-(H+log_2 t)}/(1+eps) >= h_t`, at the
  pinned `h_t = HardSeedFacade.hardSeedColumnDensity kt` (`A:122`).
* `A:138--141` -- the three restriction clauses, at the frozen defining
  quantities and read **off the datum**: `Dat.selCard = r' p_t` for `A:138--139`
  (`RestrictionDatum.certifiedPt`, the `A:120` display), `certifiedRowFloor` for
  `A:139--140`, and `certifiedColFloor h a^sharp` for `A:141`.  No numeral
  replaces `p_t`, `ceil(r' t x m)` or `h 2^{-a^sharp}`.
* `A:142--145` -- the conclusion, `CertifiedE3 H (kr' + kt) val`, i.e.
  `H + log_2(r' t) <= val`.

The conclusion is deliberately the **last** clause and is not a field of `Dat`.
This is a hypothesis of the declarations that consume it and is never a conclusion
of any declaration in this repository: `thm:certified-localized-extension` is a
registered, deferred obligation (see the module note). -/
def CertifiedExtensionEndpoint {Cone Rone : Type*} [Fintype Cone] [Fintype Rone]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (M1T : Cone → Rone → Bool) (H : ℕ) (x : ℝ)
    (t r r' q kt kr kr' : ℕ) (ε h : ℝ) (aSharp : ℕ)
    (Dat : RestrictionDatum.RestrictionDatum Blk Cone Col r' t aSharp x h)
    (val : ℕ) : Prop :=
  -- `A:111`, `M` nonempty with `m` rows, and `H >= 2`
  1 ≤ Fintype.card Cone →
  1 ≤ Fintype.card Rone →
  2 ≤ H →
  -- `A:112`, `0 < x <= 1`
  0 < x →
  x ≤ 1 →
  -- `A:113--116`, `eq:certified-base` at the frozen `y_*` of `A:16--18`
  H ≤ LambdaGE M1T 1 x yStar →
  -- `A:117`, `t >= t_cert`, a power of two, divisible by `16`
  tCert ≤ t →
  t = 2 ^ kt →
  16 ∣ t →
  -- `A:118`, `t x <= 1`
  (t : ℝ) * x ≤ 1 →
  -- `A:125`, `r, r'` positive powers of two with `r' <= r`, and `q = r t`
  r = 2 ^ kr →
  r' = 2 ^ kr' →
  r' ≤ r →
  q = r * t →
  -- `A:126--128`, the family clause: balanced with `0 < eps < 1`, or full product
  -- with `eps = 0`
  ((0 < ε ∧ ε < 1) ∨ ε = 0) →
  -- `A:128--129`, `h in (0,1]` and `a^sharp in {0,1}`
  0 < h →
  h ≤ 1 →
  aSharp ≤ 1 →
  -- `eq:certified-E1` (`A:131--134`), in its `t`-th power form
  yStar ^ t ≤ h * (2 : ℝ) ^ (-((H : ℝ) + (kr : ℝ) + (kt : ℝ))) / (1 + ε) →
  -- `eq:certified-E2` (`A:135--136`), at the pinned `h_t` of `A:122`
  HardSeedFacade.hardSeedColumnDensity kt
    ≤ h * (2 : ℝ) ^ (-((H : ℝ) + (kt : ℝ))) / (1 + ε) →
  -- `A:138--139`, exactly `r' p_t` represented outer blocks, read off the datum
  Dat.selCard = r' * RestrictionDatum.certifiedPt t →
  -- `A:139--140`, at least `ceil(r' t x m)` rows in each represented block
  RestrictionDatum.certifiedRowFloor r' t x (Fintype.card Cone) ≤ Dat.rowsPerBlock →
  -- `A:141`, column density at least `h 2^{-a^sharp}`
  RestrictionDatum.certifiedColFloor h aSharp ≤ Dat.colDens →
  -- `A:142--145`, `eq:certified-E3`, `H + log_2(r' t)`
  CertifiedE3 H (kr' + kt) val

/-- **`eq:certified-E3` obtained from the endpoint with `A:128--129`,
`A:138--141` and `A:111`'s nonemptiness discharged, PROVED.**

Five of the frozen clauses are **not** binders of this theorem -- `A:111`'s
`m >= 1`, `A:128`'s `h in (0,1]`, `A:129`'s `a^sharp in {0,1}` and all three
`A:138--141` restriction clauses.  They are read off the datum by the *general*
banked lemmas `RestrictionDatum.card_row_pos`, the fields `h_pos`, `h_le_one`,
`aSharp_le_one`, and `selCard_eq`, `rowFloor_le_rowsPerBlock`,
`colFloor_le_colDens`.  So at every call site there is nothing for a caller to
choose about the restriction or the density pair: the free-parameter class
recorded as `LARGE-CAPACITY-BRANCH-001` items (18), (20) and (21) stays dead.
What remains are exactly the ambient guards `A:111--137`, which the frozen theorem
states about the *data*, not about the restriction.

The banked `a^sharp = 1`, `r' = 2^{l-k}`, `t = 2^k` adapters
(`RestrictionDatum.hcount_ofDatum`, `.hrows_ofDatum`, `.hcol_ofDatum`,
`.hGne_ofDatum`) are deliberately **not** used: their index shape is call (ii)'s,
which is the conflation this repair removes.  The general lemmas they are
themselves proved from are consumed instead, by pin.

General in both matrix carriers, in the block and column carriers of the
restriction, in `H`, `x`, `t`, `r`, `r'`, `q`, their three exponents, `eps`, `h`,
`a^sharp` and the readout `val`. -/
theorem certifiedE3_of_datum {Cone Rone : Type*} [Fintype Cone] [Fintype Rone]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (M1T : Cone → Rone → Bool) {H : ℕ} {x : ℝ}
    {t r r' q kt kr kr' : ℕ} {ε h : ℝ} {aSharp val : ℕ}
    (Dat : RestrictionDatum.RestrictionDatum Blk Cone Col r' t aSharp x h)
    (hY : 1 ≤ Fintype.card Rone) (hH : 2 ≤ H)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hbase : H ≤ LambdaGE M1T 1 x yStar)
    (htcert : tCert ≤ t) (htpow : t = 2 ^ kt) (ht16 : 16 ∣ t)
    (htx : (t : ℝ) * x ≤ 1)
    (hr : r = 2 ^ kr) (hr' : r' = 2 ^ kr') (hrr : r' ≤ r) (hq : q = r * t)
    (heps : (0 < ε ∧ ε < 1) ∨ ε = 0)
    (hE1 : yStar ^ t ≤ h * (2 : ℝ) ^ (-((H : ℝ) + (kr : ℝ) + (kt : ℝ))) / (1 + ε))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kt
      ≤ h * (2 : ℝ) ^ (-((H : ℝ) + (kt : ℝ))) / (1 + ε))
    (hE3 : CertifiedExtensionEndpoint M1T H x t r r' q kt kr kr' ε h aSharp Dat val) :
    CertifiedE3 H (kr' + kt) val := by
  have htpos : 0 < t := lt_of_lt_of_le tCert_pos htcert
  have hr'pos : 0 < r' := by
    rw [hr']
    exact pow_pos (by norm_num) _
  have hpos : 0 < r' * RestrictionDatum.certifiedPt t :=
    Nat.mul_pos hr'pos (RestrictionDatum.certifiedPt_pos ht16 htpos)
  exact hE3 (Dat.card_row_pos hpos) hY hH hx0 hx1 hbase htcert htpow ht16 htx
    hr hr' hrr hq heps Dat.h_pos Dat.h_le_one Dat.aSharp_le_one hE1 hE2
    Dat.selCard_eq (Dat.rowFloor_le_rowsPerBlock hpos) Dat.colFloor_le_colDens

/-- **Aux D2 (the `A:126--128` clause has content).**  The `eps` disjunction bounds
the denominator that `eq:certified-E1` and `eq:certified-E2` divide by: `1 + eps`
is positive (so the two displays are well-posed) and below `2` (so neither side
inequality can be satisfied by inflating `eps`).  The pre-repair encoding
`(0 : ℝ) = 0` implied neither.  General in `eps`. -/
theorem epsBranch_bounds {ε : ℝ} (heps : (0 < ε ∧ ε < 1) ∨ ε = 0) :
    0 < 1 + ε ∧ 1 + ε < 2 := by
  rcases heps with ⟨h0, h1⟩ | h0
  · exact ⟨by linarith, by linarith⟩
  · subst h0
    exact ⟨by norm_num, by norm_num⟩

/-! ### The canonical instance: `09:311--327`

`09:313--323` is the paper's own invocation of `thm:certified-localized-extension`
and therefore the canonical inhabitant this encoding must accept.  Its substitution
is registered here so the shape is machine-checked rather than described. -/

/-- **`CanonicalReferenceStoppingCall` -- the `09:313--323` substitution, REGISTERED.**

"Apply the certified-scale reference stopping lemma,
`thm:certified-localized-extension`, using its fixed `y_* = 3/5` and the
substitutions `M = G`, `H = C-1`, `x = x_T`, `t = t_ref`, `r = q/t_ref`,
`r' = kappa_j/t_ref`, `eps = 0`, `h = theta`, `a^sharp = 0`" (`09:313--323`).

At `t_ref = 2^{k_ref}` (`06:569`), `q = 2^{k_q}` and `kappa_j = q/2^j`
(`09:280`), the three integer binders are `t = 2^{k_ref}`,
`r = 2^{k_q - k_ref}` and `r' = 2^{k_q - j - k_ref}`; the exponent of the
conclusion is `log_2(r' t) = k_q - j = log_2 kappa_j`.  `eps = 0` is `09:322`,
justified at `09:325--327` ("the reference restriction is a full product, so its
balancedness error is exactly zero"; the word "zero" falls on `09:327`), and
`a^sharp = 0` is `09:322`.

**Canonical inhabitation is DEFERRED, not claimed**: inhabiting this needs `G`,
`x_T`, `theta` and the routed restriction of the reference family, none of which
is built, and `A:117` forces `t_ref >= 2^{2^20}`, so no legal instance is
`decide`-computable.  The obligation is ledger-registered.  What *is* proved is
`canonicalCall_gates`: every integer and width gate of the substitution holds at
the paper's own `eq:tref-search` floor. -/
def CanonicalReferenceStoppingCall {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (G : Rw → Cl → Bool) (C kq kref j : ℕ) (xT θ : ℝ)
    (Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ)
    (val : ℕ) : Prop :=
  CertifiedExtensionEndpoint G (C - 1) xT
    (2 ^ kref) (2 ^ (kq - kref)) (2 ^ (kq - j - kref)) (2 ^ kq)
    kref (kq - kref) (kq - j - kref) (0 : ℝ) θ 0 Dat val

/-- **Aux D3 (the canonical substitution is legal at the paper's own floors),
PROVED.**

Given only `eq:tref-search`'s floor term `clog_2(t_0(3/5)) <= k_ref`
(`06:561--563`) and `09:327`'s legality condition in exponent form
(`k_ref + j <= k_q`, i.e. `q/2^j >= t_ref`), every integer gate of
`09:313--323` holds: `A:117`'s `t_cert <= t_ref` and `16 | t_ref`, `A:125`'s
`r' <= r` and `q = r t`, and the conclusion exponent
`log_2(r' t) = k_q - j = log_2 kappa_j`.  General in `k_q`, `k_ref` and `j`. -/
theorem canonicalCall_gates {kq kref j : ℕ}
    (hfloor : Nat.clog 2 tCert ≤ kref) (hj : kref + j ≤ kq) :
    tCert ≤ (2 : ℕ) ^ kref
      ∧ 16 ∣ (2 : ℕ) ^ kref
      ∧ (2 : ℕ) ^ (kq - j - kref) ≤ 2 ^ (kq - kref)
      ∧ (2 : ℕ) ^ kq = 2 ^ (kq - kref) * 2 ^ kref
      ∧ (kq - j - kref) + kref = kq - j := by
  obtain ⟨h1, h2⟩ := certifiedWidthGates_of_kRefFloor hfloor
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [← pow_add]
    congr 1
    omega
  · omega

/-- **Aux D4 (`eq:certified-E3` at the canonical instance is `09:329--331`),
PROVED.**

Firing `certifiedE3_of_datum` at the `09:313--323` substitution gives
`C - 1 + log_2 kappa_j <= val`, and `canonicalCall_matches_low_rung` records that
this is the frozen conclusion `comp(...) >= C + log_2 q - 1 - j` of `09:329--331`.
So the encoding's conclusion at the paper's own instance is the paper's own
conclusion, symbol for symbol.

Every hypothesis below is an `A:111--137` ambient guard about the data `G`, `C`,
`x_T` and `theta`; the restriction half and the density pair come off `Dat`.
General in the two matrix carriers, the restriction carriers, `C`, `k_q`,
`k_ref`, `j`, `x_T`, `theta` and `val`. -/
theorem certifiedE3_at_canonicalCall {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (G : Rw → Cl → Bool) {C kq kref j val : ℕ} {xT θ : ℝ}
    (Dat : RestrictionDatum.RestrictionDatum Blk Rw Col
      (2 ^ (kq - j - kref)) (2 ^ kref) 0 xT θ)
    (hfloor : Nat.clog 2 tCert ≤ kref) (hj : kref + j ≤ kq)
    (hY : 1 ≤ Fintype.card Cl) (hH : 2 ≤ C - 1)
    (hx0 : 0 < xT) (hx1 : xT ≤ 1)
    (hbase : C - 1 ≤ LambdaGE G 1 xT yStar)
    (htx : (((2 : ℕ) ^ kref : ℕ) : ℝ) * xT ≤ 1)
    (hE1 : yStar ^ ((2 : ℕ) ^ kref)
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + ((kq - kref : ℕ) : ℝ) + (kref : ℝ)))
        / (1 + (0 : ℝ)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kref
      ≤ θ * (2 : ℝ) ^ (-(((C - 1 : ℕ) : ℝ) + (kref : ℝ))) / (1 + (0 : ℝ)))
    (hcall : CanonicalReferenceStoppingCall G C kq kref j xT θ Dat val) :
    CertifiedE3 (C - 1) (kq - j) val := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := canonicalCall_gates (kq := kq) (kref := kref) (j := j)
    hfloor hj
  have hmain := certifiedE3_of_datum G Dat hY hH hx0 hx1 hbase h1 rfl h2 htx
    rfl rfl h3 h4 (Or.inr rfl) hE1 hE2 hcall
  rwa [h5] at hmain

/-- **Aux D5 (the canonical conclusion is the frozen `09:329--331`).**

`09:329--331` states the low-rung conclusion as
`comp(bracket(U,1,y_*/2^j,theta)) >= C + log_2 q - 1 - j`.  With
`log_2 q = k_q`, `eq:certified-E3`'s left-hand side at the canonical
substitution, `(C-1) + (k_q - j)`, is that number.  A pure arithmetic identity,
recorded so the two spellings are never taken for different targets.  General in
`C`, `k_q` and `j` at the frozen ranges `C >= 1`, `j <= k_q`. -/
theorem canonicalCall_matches_low_rung {C kq j : ℕ} (hC : 1 ≤ C) (hj : j ≤ kq) :
    (C - 1) + (kq - j) = C + kq - 1 - j := by omega

/-- **Aux D6 (the canonical substitution's integer gate list is jointly
satisfiable at paper-derived values), PROVED.**

LANE-GATE 3 for the endpoint's index half, machine-checked rather than argued.
The exhibited values are the paper's own, taken as closed forms and never as
numerals of ours:

* `k_ref` at its own `eq:tref-search` floor term, the expression
  `clog_2(t_0(3/5)) = clog_2 t_cert` (`06:563` with `A:104--107`);
* `j = 2`, the top of the frozen range "Fix `j in {0,1,2}`" (`09:278`);
* `k_q = k_ref + 2`, the boundary of `09:327`'s legality condition
  "`q/4 >= t_ref` makes all three values of `r'` legal".

At those values every conclusion of `canonicalCall_gates` holds, so `A:117`'s
width gates and `A:125`'s index gates are not vacuously unsatisfiable.

This is **not** canonical inhabitation: it exhibits no `RestrictionDatum`, no
matrix and no real parameters, and the two real-valued legs `eq:certified-E1` and
`eq:certified-E2` are outside its scope (they are `06:564--567`'s second and third
`eq:tref-search` inequalities; see the module note).  Canonical inhabitation
remains ledger-registered and deferred. -/
theorem canonicalCall_gates_nonvacuous :
    ∃ kref kq j : ℕ,
      Nat.clog 2 tCert ≤ kref ∧ j ≤ 2 ∧ kref + j ≤ kq
        ∧ tCert ≤ (2 : ℕ) ^ kref
        ∧ 16 ∣ (2 : ℕ) ^ kref
        ∧ (2 : ℕ) ^ (kq - j - kref) ≤ 2 ^ (kq - kref)
        ∧ (2 : ℕ) ^ kq = 2 ^ (kq - kref) * 2 ^ kref
        ∧ (kq - j - kref) + kref = kq - j := by
  refine ⟨Nat.clog 2 tCert, Nat.clog 2 tCert + 2, 2, le_rfl, le_rfl, le_rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    canonicalCall_gates (kq := Nat.clog 2 tCert + 2) (kref := Nat.clog 2 tCert)
      (j := 2) le_rfl le_rfl
  exact ⟨h1, h2, h3, h4, h5⟩

end Endpoint

/-! ## §5  The child certificate: two terminal branches, and the certified lift

Two different frozen sites meet in this section, and the repair keeps them apart.

* **The terminal two-stream dispatch, `09:1014--1023`.**  "In every case one Alice
  child has complexity at least `B_cap + log_2 kappa_v`" (`09:1023--1028`); with
  `kappa_v = 2^{r_2 - d_v}` (`09:953--954`, `09:995--996`) that is the literal
  body of the `hchild` binder of
  `TerminalFixedBinAssembly.stage2_no_alleged_protocol_at_forced_child`.  Its
  branches 2 and 3 (`09:1019--1023`) are discharged below from the banked row
  ladder and pair certificate.  Its branch 1 (`09:1014--1019`) invokes the
  **inherited** Localized Extension corollary at width `t_2` -- call (ii) of
  `06:1140--1145` -- which is *not* `thm:certified-localized-extension`
  (`A:4--8`), is stated nowhere in this module, and is left open.
* **The certified lemma's own child site, `09:1268--1276`.**  "When
  `kappa_v >= t_ref`, follow the denser Bob child and invoke the certified-scale
  reference stopping lemma on `G` with `r' = kappa_v/t_ref`, `a^sharp = 1`.  ...
  This gives residual complexity at least `C + log_2 kappa_v - 1`."  This is what
  `aliceChild_at_large_capacity` lifts, along the T1 residual comparison.
  `AliceChildCertificate` is child-agnostic (`∃ b : Bool`), so the lift is sound
  at a Bob child too; the declaration's name is legacy from the pre-repair
  generation and is retained only because the name is banked. -/

section Dispatch

variable {X Y : Type*}

/-- **The frozen child certificate of `09:1023--1028`, named.**

`B_cap + log_2 kappa_v` at `log_2 kappa_v = r_2 - d_v`, demanded of the cost of
one child of the node reached along `p`.  This is byte-for-byte the body of the
`hchild` binder of the banked
`TerminalFixedBinAssembly.stage2_no_alleged_protocol_at_forced_child`, so
supplying it is exactly what census item 8 asked for.

*Why the trivial witness fails.*  The existential is over `b : Bool` only, and at
a node whose two children are protocol leaves both costs are `0`, so neither
witness works whenever `0 < B_cap + (r_2 - d)`: see
`aliceChildCertificate_is_not_free`. -/
def AliceChildCertificate (Pstar : Protocol X Y Bool) (bcap r₂ : ℕ)
    (p : List Bool) : Prop :=
  ∃ b : Bool, bcap + (r₂ - p.length) ≤ (descendStep (descend Pstar p) b).cost

/-- **Aux E1 (the frozen trichotomy of `09:1014--1023`).**

The three cases the frozen dispatch splits on -- `kappa_v >= t_2`,
`2 <= kappa_v < t_2`, `kappa_v = 1` -- are, at `kappa_v = 2^{ell}` and
`t_2 = 2^{k_2}`, exactly the three cases `k_2 <= ell`, `1 <= ell < k_2` and
`ell = 0`.

What this theorem proves is precisely the three *iff translations* between the
capacity form and the exponent form; it does **not** assert exclusivity or
exhaustiveness, and neither does the encoding below.  Two scope notes, so the
prose does not outrun either: (a) the frozen middle branch is `ell < k_2`, but
`aliceChild_at_small_capacity` is stated at the strictly weaker `ell <= k_2`, so
the encoded branches 1 and 2 **overlap** at `ell = k_2`; (b) the overlap is
harmless -- each branch theorem is separately proved and no declaration ever
assumes two branch conditions together -- but it is an overlap, not a partition.
General in both exponents. -/
theorem capacity_trichotomy (ℓ k₂ : ℕ) :
    ((2 : ℕ) ^ k₂ ≤ 2 ^ ℓ ↔ k₂ ≤ ℓ)
      ∧ (2 ≤ (2 : ℕ) ^ ℓ ↔ 1 ≤ ℓ)
      ∧ ((2 : ℕ) ^ ℓ = 1 ↔ ℓ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.pow_le_pow_iff_right (by norm_num)
  · constructor
    · intro h
      by_contra hc
      have : ℓ = 0 := by omega
      subst this
      simp at h
    · intro h
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) h
  · exact Nat.pow_eq_one.trans (by omega)

/-- **Aux E2 (the residual reading at a child, PROVED).**

The T1 comparison `TerminalResidualComparison.D_le_cost_descend_of_computes` at
the route `p ++ [b]`: if the child's node game is read through row and column
sections that follow that route, the child's cost dominates the node game's
complexity, so a complexity bound at the node game becomes the frozen child
certificate.  This is the only place a protocol cost meets a bracket bound, and
nothing about protocols is re-proved.  General. -/
theorem aliceChildCertificate_of_child_game {A B : Type*} [Fintype A] [Fintype B]
    {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool} {gnode : A → B → Bool}
    {bcap r₂ : ℕ} {p : List Bool} (hcomp : Protocol.Computes Pstar gamb) (b : Bool)
    (iotaA : A → X) (iotaB : B → Y)
    (hrow : ∀ a, RouteRows Pstar (p ++ [b]) (iotaA a))
    (hcol : ∀ c, RouteCols Pstar (p ++ [b]) (iotaB c))
    (hgame : ∀ a c, gnode a c = gamb (iotaA a) (iotaB c))
    (hval : bcap + (r₂ - p.length) ≤ D gnode) :
    AliceChildCertificate Pstar bcap r₂ p := by
  refine ⟨b, le_trans hval ?_⟩
  have hD := D_le_cost_descend_of_computes hcomp iotaA iotaB hrow hcol hgame
  have hstep : descend Pstar (p ++ [b]) = descendStep (descend Pstar p) b := by
    rw [descend_append]
    rfl
  rwa [hstep] at hD

/-- **Branch 3 of the dispatch, `kappa_v = 1` (`09:1021--1023`), DISCHARGED.**

"If `kappa_v = 1`, the positive excess in `eq:terminal-first-alice` supplies either
an unsplit attached pair or two ordinary coordinates."  Both readings are two-copy
objects, and the banked *proved*
`TerminalCertificateInputs.topTwoCopy_residual_at_pair_floor` gives them residual
complexity `B_cap + 1`, while the target at `kappa_v = 1` is `B_cap + 0`.  So this
branch needs **no** new hypothesis beyond the node data and the banked Stage-1
certificate: `eq:certified-E3` is not consumed here.

`hunit` is the frozen `kappa_v = 1`, i.e. `d_v = r_2` (`09:958`).  General. -/
theorem aliceChild_at_unit_capacity {Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone]
    [Fintype Rone] {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool}
    {bcap b₁ r₂ : ℕ} {p : List Bool} (hcomp : Protocol.Computes Pstar gamb)
    (M1T : Cone → Rone → Bool) (b : Bool)
    (hunit : r₂ - p.length = 0)
    (hX : 1 ≤ Fintype.card Cone) (hY : 1 ≤ Fintype.card Rone) (hH : 2 ≤ bcap)
    (hlegal : 2 * StageOneInterlace.xSeed b₁ ≤ 1)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5))
    {To Tf : Finset Cone}
    (hTo : TerminalCertificateInputs.pairFloor Cone b₁ ≤ To.card)
    (hTf : TerminalCertificateInputs.pairFloor Cone b₁ ≤ Tf.card)
    {C : Finset (Slot 2 → Rone)}
    (hcolFloor : ⌈((Fintype.card Rone : ℝ) ^ 2) * (9 / 25)⌉₊ ≤ C.card)
    (iotaA : {a // a ∈ TerminalCertificateInputs.pairRows To Tf} → X)
    (iotaB : {c // c ∈ C} → Y)
    (hrow : ∀ a, RouteRows Pstar (p ++ [b]) (iotaA a))
    (hcol : ∀ c, RouteCols Pstar (p ++ [b]) (iotaB c))
    (hgame : ∀ a c,
      subgame (interlaceFun M1T 2) (TerminalCertificateInputs.pairRows To Tf) C a c
        = gamb (iotaA a) (iotaB c)) :
    AliceChildCertificate Pstar bcap r₂ p := by
  have hpair := TerminalCertificateInputs.topTwoCopy_residual_at_pair_floor M1T hX hY
    hH hlegal hseed hTo hTf hcolFloor
  refine aliceChildCertificate_of_child_game hcomp b iotaA iotaB hrow hcol hgame ?_
  rw [hunit]
  omega

/-- **Branch 2 of the dispatch, `2 <= kappa_v < t_2` (`09:1019--1021`),
DISCHARGED.**

"the inherited two-copy and odd-copy bounds give the same target."  The odd-copy
bound at capacity `kappa_v = 2^{ell}` is the `ell`-th rung of
`lem:certified-row-ladder`, which `TerminalTwoStream.certifiedRowLadder_of_base`
**proves** from the frozen Stage-1 certificate; its copy count `2^{ell-1} + 1` is
the odd count the frozen sentence names, its row density `2^{ell} 2^{-b_1}` is the
`09:1015` trim `kappa_v 2^{-b_1}`, and its column density `(3/5)^2 = 9/25` is the
frozen post-Alice guard of `09:1011`.  Like branch 3, this branch consumes **no**
new hypothesis: `eq:certified-E3` is not used.

`hcap` is the frozen `ell = r_2 - d_v` reading of `09:995--996`, and `hℓk` is the
branch condition `kappa_v < t_2` in exponent form.  General. -/
theorem aliceChild_at_small_capacity {Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone]
    [Fintype Rone] {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool}
    {bcap b₁ r₂ k₂ ℓ : ℕ} {p : List Bool} (hcomp : Protocol.Computes Pstar gamb)
    (M1T : Cone → Rone → Bool) (b : Bool)
    (hcap : r₂ - p.length = ℓ) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k₂)
    (hX : 1 ≤ Fintype.card Cone) (hY : 1 ≤ Fintype.card Rone) (hH : 2 ≤ bcap)
    (hlegal : ((2 : ℝ) ^ k₂) * StageOneInterlace.xSeed b₁ ≤ 1)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5))
    {T : Slot (2 ^ (ℓ - 1) + 1) → Finset Cone}
    (hrowFloor : ∀ i, ⌈(2 : ℝ) ^ ℓ * StageOneInterlace.xSeed b₁
      * (Fintype.card Cone : ℝ)⌉₊ ≤ (T i).card)
    {C : Finset (Slot (2 ^ (ℓ - 1) + 1) → Rone)}
    (hcolFloor : ⌈((Fintype.card Rone : ℝ) ^ (2 ^ (ℓ - 1) + 1)) * (3 / 5 : ℝ) ^ 2⌉₊
      ≤ C.card)
    (iotaA : {a // a ∈ ladderRows (2 ^ (ℓ - 1) + 1) T} → X)
    (iotaB : {c // c ∈ C} → Y)
    (hrow : ∀ a, RouteRows Pstar (p ++ [b]) (iotaA a))
    (hcol : ∀ c, RouteCols Pstar (p ++ [b]) (iotaB c))
    (hgame : ∀ a c,
      subgame (interlaceFun M1T (2 ^ (ℓ - 1) + 1)) (ladderRows (2 ^ (ℓ - 1) + 1) T) C a c
        = gamb (iotaA a) (iotaB c)) :
    AliceChildCertificate Pstar bcap r₂ p := by
  have hlad := TerminalTwoStream.certifiedRowLadder_of_base M1T hX hY hH
    (StageOneInterlace.xSeed_pos b₁) (by norm_num) (by norm_num) hseed
  have hrung := ladderRung_residual M1T hlad hℓ
    (ladder_legal_of_le (StageOneInterlace.xSeed_pos b₁) hℓk hlegal) hrowFloor hcolFloor
  refine aliceChildCertificate_of_child_game hcomp b iotaA iotaB hrow hcol hgame ?_
  rw [hcap]
  exact hrung

/-- **The certified endpoint lifted to a child-cost certificate (`09:1268--1276`),
PROVED -- and NOT branch 1 of the terminal dispatch.**

"When `kappa_v >= t_ref`, follow the denser Bob child and invoke the
certified-scale reference stopping lemma on `G` with `r' = kappa_v/t_ref`,
`a^sharp = 1`.  The other parameters are those of `sec:wrapper-low-rungs`.  This
gives residual complexity at least `C + log_2 kappa_v - 1`" (`09:1269--1276`).
That is this theorem: `certifiedE3_of_datum` bounds the complexity of the child's
node game, and `aliceChildCertificate_of_child_game` turns that bound into the
child-cost certificate at the route `p ++ [b]`.

**Scope, corrected (F1/F2/F4).**  The pre-repair generation presented this
declaration as branch 1 of the terminal dispatch, `09:1014--1019`.  It is not:
that branch invokes the *inherited* corollary "at the fixed physical width `t_2`"
(`09:1015--1016`), whose call-(ii) data are `h = 49/64`, `a^sharp = 1`,
`x = 2^{-b_1}` (`06:1140--1145`, `06:1110`), and `A:4--8` separates that corollary
from `thm:certified-localized-extension`.  This theorem is the *certified*
lemma's lift, at the certified lemma's own free binders, and its paper site is
`09:1268--1276`.  Two consequences a reader must not lose:

* the child exhibited at `09:1269--1270` is the **denser Bob child**;
  `AliceChildCertificate` is the child-agnostic `∃ b : Bool`, so the lift is
  sound, but this is not evidence about an Alice child;
* no declaration in this module feeds this theorem into
  `terminal_no_alleged_protocol_of_dispatch`, and branch 1 of the terminal
  dispatch stays open.

General in both matrix carriers, the restriction carriers, the node carriers, the
protocol, and every one of the certified lemma's free binders. -/
theorem aliceChild_at_large_capacity {Cone Rone : Type*} [Fintype Cone] [Fintype Rone]
    {Blk Col A : Type*} [DecidableEq Blk] [Fintype Col] [Fintype A]
    {Bc : Type*} [Fintype Bc]
    {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool} {gnode : A → Bc → Bool}
    {H : ℕ} {x : ℝ} {t r r' q kt kr kr' : ℕ} {ε h : ℝ} {aSharp r₂ : ℕ}
    {p : List Bool} (hcomp : Protocol.Computes Pstar gamb)
    (M1T : Cone → Rone → Bool) (b : Bool)
    (Dat : RestrictionDatum.RestrictionDatum Blk Cone Col r' t aSharp x h)
    (hcap : r₂ - p.length = kr' + kt)
    (hY : 1 ≤ Fintype.card Rone) (hH : 2 ≤ H)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hbase : H ≤ LambdaGE M1T 1 x yStar)
    (htcert : tCert ≤ t) (htpow : t = 2 ^ kt) (ht16 : 16 ∣ t)
    (htx : (t : ℝ) * x ≤ 1)
    (hr : r = 2 ^ kr) (hr' : r' = 2 ^ kr') (hrr : r' ≤ r) (hq : q = r * t)
    (heps : (0 < ε ∧ ε < 1) ∨ ε = 0)
    (hE1 : yStar ^ t ≤ h * (2 : ℝ) ^ (-((H : ℝ) + (kr : ℝ) + (kt : ℝ))) / (1 + ε))
    (hE2 : HardSeedFacade.hardSeedColumnDensity kt
      ≤ h * (2 : ℝ) ^ (-((H : ℝ) + (kt : ℝ))) / (1 + ε))
    (hE3 : CertifiedExtensionEndpoint M1T H x t r r' q kt kr kr' ε h aSharp Dat
      (D gnode))
    (iotaA : A → X) (iotaB : Bc → Y)
    (hrow : ∀ a, RouteRows Pstar (p ++ [b]) (iotaA a))
    (hcol : ∀ c, RouteCols Pstar (p ++ [b]) (iotaB c))
    (hgame : ∀ a c, gnode a c = gamb (iotaA a) (iotaB c)) :
    AliceChildCertificate Pstar H r₂ p := by
  have hE3' : CertifiedE3 H (kr' + kt) (D gnode) :=
    certifiedE3_of_datum M1T Dat hY hH hx0 hx1 hbase htcert htpow ht16 htx
      hr hr' hrr hq heps hE1 hE2 hE3
  refine aliceChildCertificate_of_child_game hcomp b iotaA iotaB hrow hcol hgame ?_
  rw [hcap]
  exact hE3'

end Dispatch

/-! ## §6  The close: `hchild` supplied, the alleged protocol excluded

`stage2_no_alleged_protocol_at_forced_child` took `hchild` as its one genuinely
external binder (census item 8).  Here it is carried as the explicit
`hdispatch` binder of `terminal_no_alleged_protocol_of_dispatch`.

**Record correction (F4, §6), for the docstring of
`terminal_no_alleged_protocol_of_dispatch` immediately below.**  That declaration
is one of the 28 this repair leaves byte-identical to the `F83ECE29` pin,
docstring included, so its docstring still reads "the three dispatch branches of
§5 produce that certificate -- two of them outright and the third from
`eq:certified-E3`" and "consumed only where `09:1014--1019` consumes it".  Both
sentences are pre-repair readings and neither survives F4:

* only **branches 2 and 3** of the `09:1014--1023` dispatch are produced in §5
  (`aliceChild_at_unit_capacity`, `aliceChild_at_small_capacity`), and both
  outright;
* **branch 1** (`09:1014--1019`, `kappa_v >= t_2`) invokes the *inherited*
  Localized Extension corollary at width `t_2` -- call (ii) of `06:1140--1145` --
  which `A:4--8` distinguishes from `thm:certified-localized-extension`.  It is
  no longer claimed by this module and is an open, ledger-registered item (see
  the scope note in the module header);
* `aliceChild_at_large_capacity`, the §5 declaration that does consume
  `CertifiedExtensionEndpoint`, is anchored at the certified lemma's **own**
  child site `09:1268--1276`, *not* at `09:1014--1019`.

The statement of `terminal_no_alleged_protocol_of_dispatch` is unaffected:
`hdispatch` is an explicit binder, so the theorem asserts nothing about where the
certificate comes from.  Only its docstring's account of the provenance is stale.
(Correction added by the `cc-t4w-r1` verify seat, judge finding 1; the locked
declaration docstring itself is carried to `OBLIGATION_LEDGER.md` unedited.) -/

section Close

variable {X Y ι : Type*} [Fintype ι]

/-- **`09:1023--1028` with `hchild` supplied by the `09:1014--1023` dispatch,
PROVED.**

The banked `TerminalFixedBinAssembly.stage2_no_alleged_protocol_at_forced_child`
is consumed by pin, with its `hchild` binder discharged from
`AliceChildCertificate` at every Alice node.  Since the three dispatch branches of
§5 produce that certificate -- two of them outright and the third from
`eq:certified-E3` -- census item 8 is no longer a free binder *at this site*: it is
the named statement `CertifiedExtensionEndpoint`, consumed only where
`09:1014--1019` consumes it.

Census item 9 is untouched: `hpath`, `hnode` and `hverdict` still quantify over
given routes and given first-Alice verdicts, and the frozen proof *builds* them.
General in the frontier index, the protocol and both exponents. -/
theorem terminal_no_alleged_protocol_of_dispatch
    {Pstar : Protocol X Y Bool} {route : ι → List Bool} {iso : ι → Prop}
    [DecidablePred iso] {hmass zmass : ι → ℕ} {bcap r₂ : ℕ}
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hpath : ∀ v ∈ aliceNodes iso, IsQueryPath Pstar (route v))
    (hnode : ∀ v ∈ aliceNodes iso, IsQueryNode (descend Pstar (route v)))
    (hverdict : ∃ v ∈ aliceNodes iso,
      3 * stoppingCapacity r₂ (route v).length ≤ 4 * hmass v ∧
        stoppingCapacity r₂ (route v).length < hmass v + zmass v)
    (hdispatch : ∀ v ∈ aliceNodes iso, AliceChildCertificate Pstar bcap r₂ (route v)) :
    False :=
  TerminalFixedBinAssembly.stage2_no_alleged_protocol_at_forced_child
    (hmass := hmass) (zmass := zmass) hbudget hpath hnode hverdict
    (fun v hv _ _ => hdispatch v hv)

end Close

/-! ## §7  The paper-`y` readout: the banked frontier theorem at `y_*`

(Called "the F3 readout" by the docstring of `yStar` in §1 and by the pre-repair
header; that `F3` is the third finding of an *earlier* tranche and is unrelated to
this repair's F3, the `A:126--128` family clause.)

`TerminalFixedBinAssembly.stage2_frontier_from_certificates` is general in the
column exponent `y`, and the frozen text fixes it: `eq:stage1-robust-certificate`
(`07:209--213`) is stated at `3/5`, which is `A:16--18`'s `y_*`.  This readout
fires the banked theorem at that value, so the general theorem is asserted at the
paper's own instantiation and not only in the abstract. -/

section FrontierReadout

variable {X Y Coord Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone] [Fintype Rone]

/-- **`09:937--978` at the paper's `y = y_* = 3/5`, PROVED.**

The banked `stage2_frontier_from_certificates` with `y` instantiated to the value
`eq:stage1-robust-certificate` prints (`07:210`), i.e. to `yStar` (`A:18`) by
`yStar_eq`.  Nothing is reshaped: every binder is the banked binder at that
substitution, and the conclusion is the banked conclusion.  General in all five
carriers and in the three exponents that remain free. -/
theorem stage2_frontier_at_paper_y
    {Pstar : Protocol X Y Bool} {gamb : X → Y → Bool}
    (hcomp : Protocol.Computes Pstar gamb) (M1T : Cone → Rone → Bool)
    (t : StoppedToken Pstar Coord) {r₂ b₁ bcap : ℕ}
    (hbcap : 0 < bcap)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5))
    {Tn Td : Finset Cone} {Cn Cd : Finset (Slot 1 → Rone)}
    (hTn : t.route.length ≤ r₂ →
      DenseRoutingInvariant.routingFloor Cone (2 ^ r₂) b₁ t.route.length ≤ Tn.card)
    (hCn : ⌈((Fintype.card Rone : ℝ) ^ 1) * (3 / 5 : ℝ)⌉₊ ≤ Cn.card)
    (iotaAn : {a // a ∈ TerminalCertificateInputs.liftRows Tn} → X)
    (iotaBn : {c // c ∈ Cn} → Y)
    (hrown : ∀ a, RouteRows Pstar t.route (iotaAn a))
    (hcoln : ∀ b, RouteCols Pstar t.route (iotaBn b))
    (hgamen : ∀ a b,
      subgame (interlaceFun M1T 1) (TerminalCertificateInputs.liftRows Tn) Cn a b
        = gamb (iotaAn a) (iotaBn b))
    (hTd : r₂ + 1 ≤ t.route.length →
      DenseRoutingInvariant.routingFloor Cone (2 ^ r₂) b₁ (r₂ + 1) ≤ Td.card)
    (hCd : ⌈((Fintype.card Rone : ℝ) ^ 1) * (3 / 5 : ℝ)⌉₊ ≤ Cd.card)
    (iotaAd : {a // a ∈ TerminalCertificateInputs.liftRows Td} → X)
    (iotaBd : {c // c ∈ Cd} → Y)
    (hrowd : ∀ a, RouteRows Pstar (t.route.take (r₂ + 1)) (iotaAd a))
    (hcold : ∀ b, RouteCols Pstar (t.route.take (r₂ + 1)) (iotaBd b))
    (hgamed : ∀ a b,
      subgame (interlaceFun M1T 1) (TerminalCertificateInputs.liftRows Td) Cd a b
        = gamb (iotaAd a) (iotaBd b)) :
    (t.event = StopEvent.isolation ∨ t.event = StopEvent.beforeAlice)
      ∧ t.route.length ≤ r₂ :=
  TerminalFixedBinAssembly.stage2_frontier_from_certificates hcomp M1T t hbcap hbudget
    hseed hTn hCn iotaAn iotaBn hrown hcoln hgamen hTd hCd iotaAd iotaBd hrowd hcold
    hgamed

end FrontierReadout

/-! ## §8  Statement poles and NON-FIDELITY readouts

A green build sees none of the three failure modes the poles record. -/

/-- **Statement pole 1 (the child certificate is not free).**  `AliceChildCertificate`
is an existential over `b : Bool`, so it would be worthless if some witness always
worked.  At an Alice query node whose two children are leaves, both children cost
`0`, so the certificate fails whenever the frozen demand `B_cap + (r_2 - d)` is
positive.  This is the **general** form of the banked
`TerminalFixedBinAssembly.alice_child_certificate_is_not_free`, which recorded the
same failure at one numeral triple.

The protocol is self-chosen and claims **no** legality: this is a rejection probe
exhibiting a node at which the certificate fails, in the sense of the
defined-vs-free witness rule. -/
theorem aliceChildCertificate_is_not_free (bcap r₂ : ℕ) (hpos : 0 < bcap) :
    IsQueryNode (Protocol.aNode (fun x : Bool => x) (Protocol.leaf false)
        (Protocol.leaf true) : Protocol Bool Bool Bool)
      ∧ ¬ AliceChildCertificate
          (Protocol.aNode (fun x : Bool => x) (Protocol.leaf false)
            (Protocol.leaf true) : Protocol Bool Bool Bool) bcap r₂ [] := by
  refine ⟨trivial, ?_⟩
  rintro ⟨b, hb⟩
  cases b <;> simp [descendStep, descend, Protocol.cost] at hb <;> omega

/-- **Statement pole 2 (the rung's row floor is load-bearing).**  Without the
per-copy trim floor of `09:1015` the rung certificate would be false: the *empty*
row set satisfies every column condition and every routing condition, yet the
frozen floor `ceil(2^{ell} x |C_1|)` is positive whenever `x > 0` and `|C_1| >= 1`,
so `ladderRung_residual`'s `hrow` is exactly what excludes it.  The readout is the
frozen ceiling's own arithmetic.  General. -/
theorem ladder_rung_needs_the_row_floor {Cone : Type*} [Fintype Cone]
    {ℓ : ℕ} {x : ℝ} (hx : 0 < x) (hX : 1 ≤ Fintype.card Cone) :
    ¬ ⌈(2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ)⌉₊ ≤ (∅ : Finset Cone).card := by
  have hXR : (1 : ℝ) ≤ (Fintype.card Cone : ℝ) := by exact_mod_cast hX
  have hcard : (0 : ℝ) < (Fintype.card Cone : ℝ) := by linarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ) :=
    mul_pos (mul_pos hpow hx) hcard
  have hceil : 0 < ⌈(2 : ℝ) ^ ℓ * x * (Fintype.card Cone : ℝ)⌉₊ := Nat.ceil_pos.2 hpos
  simp only [Finset.card_empty]
  omega

/-- **Statement pole 3 (`eq:certified-E3` is not the phase-1 target in disguise).**

`CertifiedE3` is a statement about *one child of one node*, at the scale
`B_cap + log_2 kappa_v`, whereas `eq:terminal-fixed-bin` is a statement about the
whole fixed-bin matrix at `D_2 + 1 = B_cap + r_2 + 1`.  At **every** suffix depth
the certified value is strictly below the phase-1 target -- the gap is the one bit
`TerminalFixedBinAssembly.assembly_does_not_reach_the_phase_one_target` records --
so no rearrangement of §4--§6 can be mistaken for it.  Unconditional, and general
in `B_cap`, `r_2` and the depth. -/
theorem certifiedE3_is_not_the_phase_one_target (bcap r₂ d : ℕ) :
    bcap + (r₂ - d) < TerminalFixedBin.fixedBinTarget bcap r₂ := by
  simp only [TerminalFixedBin.fixedBinTarget, DenseBranchSelection.Dtwo]
  omega

/-- **NON-FIDELITY 1 (the ladder row set is not the empty construction).**  At two
copies over a two-element carrier, with the ordinary fibre `{0,1}` and the foreign
fibre `{0}`, the assembled row set has three rows, its copy-`0` fibre has two and
its copy-`1` fibre one -- so the per-copy readout `ladderRows_fibre_card` reports
genuinely different numbers on different copies and the construction is not
constant.

The carrier and both fibres are self-chosen and claim **no** legality: this audits
our encoding at a point the frozen paper never visits, and is never evidence that
the terminal regime is inhabited. -/
theorem ladderRows_probe_is_nondegenerate :
    (ladderRows 2 (fun i : Slot 2 => if i = 0 then ({0, 1} : Finset (Fin 2)) else {0})).card
        = 3
      ∧ ((ladderRows 2
          (fun i : Slot 2 => if i = 0 then ({0, 1} : Finset (Fin 2)) else {0})).filter
          (fun r => r.1 = 0)).card = 2
      ∧ ((ladderRows 2
          (fun i : Slot 2 => if i = 0 then ({0, 1} : Finset (Fin 2)) else {0})).filter
          (fun r => r.1 = 1)).card = 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [ladderRows_fibre_card]; decide
  · rw [ladderRows_fibre_card]; decide

/-- **NON-FIDELITY 2 (the child certificate is inhabited).**  At the banked
`DenseWeightedCount.probeProtocol` -- one Bob query above one Alice query -- the
root's `true` child is the Alice query, of cost `1`, so the frozen demand
`B_cap + (r_2 - 0)` is met at `B_cap = 1`, `r_2 = 0`.  So `AliceChildCertificate`
is not quantified over an empty premise set, and pole 1 above really is about a
*failing* node rather than about an unsatisfiable shape.

The values are self-chosen and claim **no** legality: same NON-FIDELITY caveat as
readout 1.  Note also that the route here is `[]`, i.e. the **root** of
`probeProtocol`, which is a `Protocol.bNode` -- whereas the frozen certificate is
consumed at `v in aliceNodes`.  So this inhabits the *shape* of
`AliceChildCertificate` at a Bob node, and must not be read later as an
Alice-node instance. -/
theorem aliceChildCertificate_at_probe :
    AliceChildCertificate DenseWeightedCount.probeProtocol 1 0 [] := by
  refine ⟨true, ?_⟩
  simp [DenseWeightedCount.probeProtocol, descendStep, descend, Protocol.cost]

/-- **Statement pole 4 (F1: the width guard does not sit on `t_2`).**

`eq:t2-search` (`06:763--773`) fixes `k_2` by
`k_2 >= max{4, 2^19, m_HS}`, `2^{k_2} >= 2 H_max`,
`2^{j_49(k_2)} >= L_h + B_cap + k_2 + 4`, `t_2 = 2^{k_2}`.  There is no
`t_0(3/5)` term in it, and its own explicit floor is `2^19`; but `A:117` needs
`t_cert = 2^{2^20} <= t`, i.e. `2^20 <= log_2 t`.  So at the width the
`eq:t2-search` floor delivers, `A:117` **fails** -- which is exactly why the
pre-repair generation's `tCert <= 2 ^ k_2` premise was unsuppliable and why the
repair re-homes the guard onto the theorem's own free `t`, instantiated at
`t_ref` (`certifiedWidthLeg_of_kRefFloor`).

The value `2^19` is the frozen floor of `06:766`, not a numeral of ours, so this
pole reads the paper's own schedule rather than a self-chosen point. -/
theorem tCert_not_le_two_pow_t2_floor : ¬ tCert ≤ (2 : ℕ) ^ 2 ^ 19 := by
  intro hle
  unfold tCert at hle
  have hexp : (2 : ℕ) ^ 20 ≤ 2 ^ 19 :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  norm_num at hexp

/-- **Statement pole 5 (F3: the `eps` clause is not free).**

`A:126--128` allows exactly two shapes for the balancedness error: `0 < eps < 1`
(a balanced family) or `eps = 0` (the exact full product).  A real outside both --
here `eps = -1`, the one value that would make `eq:certified-E1` and
`eq:certified-E2` divide by zero -- is rejected by the clause, so the encoded
disjunction genuinely constrains the binder.  The pre-repair encoding
`(0 : ℝ) = 0` rejected nothing.

`-1` is self-chosen and claims **no** legality: this is a rejection probe
exhibiting a value the guard excludes, in the sense of the defined-vs-free witness
rule. -/
theorem epsBranch_rejects_neg_one :
    ¬ (((0 : ℝ) < (-1 : ℝ) ∧ (-1 : ℝ) < 1) ∨ (-1 : ℝ) = 0) := by
  rintro (⟨h0, -⟩ | h0) <;> norm_num at h0

end EthInapproximability.ParameterizedNP.CertifiedLocalizedExtension
