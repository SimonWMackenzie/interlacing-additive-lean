import EthInapproximability.ParameterizedNP.CoefficientTraversal
import EthInapproximability.ParameterizedNP.MassRedistributionTail
import EthInapproximability.ParameterizedNP.TruthTableExponent

/-!
# Parameterized NP route: the schedule majorant / tail / aux-source residue

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: opened under **`PARAM-001`** (the schedule-compiler thread), wiring
into `SIZE-001` (`SizePropagation`), `ENVELOPE-REALIZATION-001`
(`EnvelopeRealization`) and `COEFF-TRAVERSAL-001` (`CoefficientTraversal`).

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.
Every anchor below was opened first-hand in that source this tranche; the
41-page reader artifact, the ledger, the crosswalk and every summary are
navigation only.

## Scope

This module addresses the **sixteen open displays** of `sec:parameters` that the
banked schedule modules left unstated: the structural majorant block, the four
tail-error classes and the persistent tail registry, the `L`/`l(n)` substitution
sandwich, the five-step auxiliary source row, and the balanced-family and
dimension-coefficient envelopes of `sec:one-level-dimensions`.  Every display it
does land is stated **at its own anchor** and **through the banked accessors**;
nothing already banked is restated.  Two of the sixteen land **nothing** in this
revision -- displays 1 and 2 -- and the table below and "Withdrawn carriers"
record why in each case.

| # | frozen anchor (`06-parameter-schedule.tex` unless noted) | declaration |
| --- | --- | --- |
| 1 | `eq:structural-majorants`, label 1701, display 1691--1702 |
  *(none -- see "Withdrawn carriers")* |
| 2 | `eq:four-tail-errors`, label 1717, display 1712--1718 |
  *(none -- see "Withdrawn carriers")* |
| 3 | `eq:strict-tail-entry`, label 1753, display 1751--1754 | `tailT4_margin`
  (the `T4_Q` margin of `06:1777--1785` only) |
| 4 | `eq:tail-scaled-numerator`, label 1764, display 1761--1765 |
  `tailScaledNumerator`, `tailRatio`, `strictTailEntry_of_scaledNumerator` |
| 5 | `eq:L-ell-sandwich`, label 1849, display 1848 | `LSandwich` |
| 6 | `eq:aux-source-s-normalized`, label 1881, display 1878--1882 | `auxSourceRow` |
| 7 | `eq:aux-source-s-ecut`, label 1892, display 1890--1893 | `auxSourceEcutRow` |
| 8 | `eq:aux-source-s-le-n`, label 1905, display 1903--1906 |
  *(none here -- `AuxSourceDerivations.auxSourceSLeN`, downstream of the `B_s`
  pin; see "The auxiliary-source chain moves downstream")* |
| 9 | `eq:aux-source-s-minus-three`, label 1910, display 1908--1911 |
  *(none here -- `AuxSourceDerivations.auxSourceSMinusThree`, same reason)* |
| 10 | `eq:literal-balanced-family-size`, label 2130, display 2125--2131 |
  `literalBalancedFamilySize` |
| 11 | `eq:N2-explicit-code-envelope`, label 2143, display 2137--2144 | `n2ExplicitCodeEnvelope` |
| 12 | `eq:N2-dimension-code-bound`, label 2163, display 2160--2164 | `n2DimensionCodeBound` |
| 13 | `eq:dimension-coefficient-roots`, label 2180, display 2168--2181 | `dimensionRoots` |
| 14 | `eq:Cdim-literal-producer`, label 2199, display 2195--2200 |
  `DimRowChecked`, `cdimLiteral_dominates_rows` |
| 15 | `eq:raw-dimension`, label 2224, display 2213--2225 | `rawDimension` |
| 16 | `eq:one-level-log-size`, label 2248, display 2245--2249 | `oneLevelLogSize` |

**One unlabelled frozen span is added to the sixteen, at Section 4b below.**
`06:1766--1774` is the **tail-cutoff successor bump** `C_u^+ = C_u + 1`: it
carries no `\label`, so it is not a seventeenth display, but it is the step that
turns the coefficient pass's non-strict checked row into the *strict* stored
comparison `V_u < D_e` that display 4's cross-multiplication then consumes.
Ledger row `FRESH-1` of the `cc-t8a` `06:1745--2109` attribution sweep records it
as an undischarged frozen derivation with **no Lean owner**; the sweep found no
citation of it anywhere in the tree, and `docs/BANKED_SURFACE_INDEX.md` has no
entry for the span (the neighbouring entries are `06:1777` and `06:1777--1785`).
Section 4b lands it.

## What is consumed by pin and never restated

* `W(L) = 2^{C_size L^8}` and `C_size` -- `SizePropagation.structuralW`,
  `.csizeLiteral` (the first row of display 1 and `eq:Csize-literal-producer`).
* `C_dim`, `t_2 + s(q_1+s) + 1`, `zbar_N` -- `SizePropagation.cdimLiteral`,
  `.dimMultiplicity`, `.rawSideMajorant`.
* `A_wrap`, `C_exc`, `C_exc^0`, `B_exc^0`, `l(n)`, `E_c(n)`, the exact carrier
  recurrence -- `IterationAssembly.awrap`, `.cexcOf`, `.cexcZero`, `.bexcZero`,
  `.ellN`, `.envE`, `.carrierRowNext`, `.carrierColNext`.
* `L = clog_2(A_pre)`, `ECut`, the upper half of `eq:L-ell-sandwich` --
  `EnvelopeRealization.normalizedL`, `.ECutPred`, `.lSandwich_upper`.
* `j_49`, the least-power-of-two accessors, `s = 2^{B_s u^2}`, `q = 2^{A_wrap
  L_P^2}`, `L_P`, `P_0`, `c_seed`, `L_theta`, `e_0^max`, `E_B`, `E_T`,
  `delta_term`, `u_term` -- `ParameterSchedule.j49`, `.leastPowTwoExp`,
  `.leastPowTwoGe`, `.sScale`, `.qWrap`, `.LPwidth`, `.P0sched`, `.cSeed`,
  `.Ltheta`, `.e0maxSched`, `.EB`, `.ET`, `.deltaTerm`, `.uTerm`.
* `b_1 = 2^{j_49(a-2)}` and `a = C_0(log_2 A_*)^2` --
  `MassRedistributionTail.b1`, `.aStage1`.
* `B_theta = B_pair` -- `WrapperProtectedEarly.Btheta` through the banked
  `ParameterSchedule.schedule_Btheta_eq_Bpair`.

## DEFINED-vs-FREE

Every symbol of the sixteen displays was classified against the frozen source
before it was written.  The **DEFINED** ones are reified here only when no
banked reification exists, and each new reification cites its own defining
display, never the consuming display:

* `bl(x) = clog2N(x+1)` -- `02-mechanical-contract.tex:282`, with
  `clog2N(x) = min{r : x <= 2^r}` at `02:281`, i.e. `Nat.clog 2` exactly.  This
  quantity gets **no Lean definition anywhere in this module**: its single home
  is the frozen display, and every statement below that needs it writes the
  inline `Nat.clog 2 (x + 1)`.
* `X_bal(q,t,m) = max{q,1000mt^2,2}` -- `02-mechanical-contract.tex:181`
  (`xBal`), and `B_bal(q,t,m) = (2 X_bal)^t` -- `eq:balanced-family-envelope`,
  `02-mechanical-contract.tex`, label 187, display 183--188 (`bBal`).
* `k_T = log_2(s/4)` and `b_T = 2^{j_49(k_T)}` -- `06:237--243`.  Both are
  reified **once** for this route, in `ScheduleTemplateResidue` (`kT`, `bT`),
  over the banked `ParameterSchedule.j49`; this module carries no second copy
  and no statement here consumes them.
* `U_0 = max{2, b_out/eta_R}` -- `06:295--297`, and `A_*`, the least power of two
  at least `max{16,B_pub,z_R,log_2 q_2,s,ceil(log_2 U_0)}` -- `eq:Astar-choice`,
  label 304, display 299--305.  Both are reified **once** for this route, in
  `ScheduleTemplateResidue` (`U0sched`, `astarThreshold`, `astar`, `astarExp`),
  over the banked `ParameterSchedule.leastPowTwoGe` and `.leastPowTwoExp`; this
  module carries no second copy and no statement here consumes them.
  `ceil(log_2 U_0)` is the frozen core operation `clog_2(U_0)` of `02:288`, i.e.
  the banked `leastPowTwoExp`, and is **not** a real logarithm rounded by hand.
* `d_s = 2(c+1)` -- `06:1864` (`dsExp`).
* `y = 2^{2^{lambda-2}}` -- `06:1894` (`auxY`), at `lambda = l(n)` of `06:1864`.
* `P_dim = (t_2 + s(q_1+s)+1)Z` -- `06:2188--2191` (`pDim`), whose multiplicity
  factor is the banked `SizePropagation.dimMultiplicity`.

The quantities that stay **FREE in the frozen source itself**, and are therefore
binders, are exactly: the coefficient pass's own recorded rows (`rows12`,
`rows3`, `tbl`, `dimRows` -- compiler output that `06:1628--1631` forbids a
formalizer to supply, `PARAM-001`); the public inputs `b_out`, `B_pub`, `z_R`,
`clog_2(|E|+2)`, `C_cert`, `C_0`; the numerical source width `q_2`
and its logarithm; the source size `n`, the typed envelope bound `N_E`, the
incoming exponent `c`; the level's own carrier cardinalities and multiplicities;
and the level's dyadic widths `t_2`, `q_1`, `Z`, `Q`, `k_ref`.

**Two corrections to that list, carried by the `cc-t8c` repair.**  An earlier
revision also named `B_s` and `u` as FREE, and both were wrong.  `u` is
**DEFINED** by `eq:s-choice` (`06:116--117`), `u = clog_2(clog_2(A_pre + 16))`,
already reified once as the banked `ParameterSchedule.uAux`.  `B_s` is
**DEFINED** by the `K1` block, `B_s = T^2` with `T` the least integer `>= 64`
satisfying `9T^2 - 2 >= m_HS` (`02:815--819`), already reified once as the banked
`MechanicalCompilerResidue.bsSched`.  Where `B_s` and `u` still appear as
*binders* below, in displays 6 and 7, they are pinned **at the use site**: those
two rows are schemas fired at the definitional chain downstream, by
`ScheduleCompilerExistential.auxSourceNormalizedRow` and `.auxSourceECutRow`
(the latter under the explicit pin `hBs : C.K.Bs =
MechanicalCompilerResidue.bsSched`), at `Section5Admissibility.uAuxOf` and
`EnvelopeRealization.normalizedL`.  Displays 8 and 9 had no such firing site and
are no longer stated here at all -- see the next section.

Every Prop-valued display below is a **schema** in the display's own symbols --
the shape `ParameterSchedule.terminalWrapperGates` already uses.  **Both** of
them are fired at the evaluated definitional chain by a companion in this file
(`LSandwich` by `lSandwich_of_lower` at `EnvelopeRealization.normalizedL`,
`DimRowChecked` by `cdimLiteral_dominates_rows` at the banked
`SizePropagation.cdimLiteral`), so no source-defined quantity is left free at
any surviving schema's use site.  The one schema that had lost its firing site,
the display-1 premise bundle, is withdrawn entire (see "Withdrawn carriers")
rather than left standing unfired.

## Withdrawn carriers

This module declares **no new type**.  Five layers that an earlier revision of
this file carried were withdrawn: the first three because the route already
homes the quantity once elsewhere, the fourth because the frozen source does not
supply the object the carrier would have to hold, and the fifth because it had
lost its only firing site and no legal inhabitant remained:

* a `bl` definition -- withdrawn in favour of the inline `Nat.clog 2 (x + 1)`
  above.  `bl` has **no** named Lean home anywhere on this route: the sibling
  abbreviations in `SchedulePhysicalResidue` and `ScheduleTemplateResidue` were
  deleted in the same tranche under the same binding prescription, and the
  inline frozen expression of `02:282` is the single form;
* a second reification of `k_T`/`b_T` -- withdrawn in favour of the route's one
  reification in `ScheduleTemplateResidue`;
* a second reification of `U_0`/`A_*` (`06:295--297`, `eq:Astar-choice`) --
  withdrawn in favour of the route's one reification in
  `ScheduleTemplateResidue` (`U0sched`, `astarThreshold`, `astar`, `astarExp`);
* a four-constructor tail-class tag, a tail-entry record, and a registry-shape
  predicate for the 29-row persistent registry -- withdrawn because
  `06:1790--1793` requires "a bijection between all 29 entry IDs, their
  coefficient derivations, literal strict margins, and either persistent roots
  or one of the four fixed `T4_Q` records", and the frozen source prints
  neither the table nor a single row, nor the coefficient derivations and
  literal margins the checker compares against.  A two-clause count-and-Nodup
  predicate is *not* that checker, and no shorter predicate is the paper's, so
  the registry level is left unformalized rather than approximated;
* the **display-1 premise bundle and its helpers** -- a five-conjunct
  `Prop`-valued schema for `eq:structural-majorants` (`06:1691--1702`), its
  unfolding and `C_size`-monotonicity lemmas, the real-logarithm step its third
  row needed, the `B_theta = B_pair` restatement its fourth row leaned on, and
  its single **BEYOND-PAPER** probe.  The schedule-level firing declaration that
  supplied every source-defined symbol of that display from its own defining
  display in dependency order was withdrawn with the duplicate `b_T`
  reification above, and once it was gone the bundle had **no** paper firing
  site: the only remaining inhabitant was the self-chosen audit probe, which
  claims no legality and therefore cannot satisfy non-vacuity at legal
  parameter values.  A premise bundle whose sole inhabitant is BEYOND-PAPER
  states nothing about the paper's object, so the whole group is withdrawn
  rather than left standing.  Reinstating display 1 is an **unregistered future
  obligation**: it needs its own authorized ledger row and canonical-inhabitation
  requirement, and no such row currently exists.  It must land a paper-derived
  legal firing whose `b_T` comes from `ScheduleTemplateResidue.bT` by fully
  qualified pin, whose `U_0`/`A_*` come from `ScheduleTemplateResidue`
  (`U0sched`, `astarThreshold`, `astar`, `astarExp`), and whose `eta_R` comes
  from the banked `ParameterSchedule.etaR` -- the paper's own instance
  additionally needs the compiler's row
  production (`PARAM-001`) and the fixed-threshold choice of `B_s` at
  `06:285--287` ("Choosing `B_s` with `c_T sqrt(B_s) > 20` makes `b_T` dominate
  every polylogarithmic wrapper loss needed below"), which the frozen source
  states as an asymptotic threshold and never instantiates.

What survives of displays 2--4 is exactly the explicit-binder arithmetic those
displays state, over ordinary numeric binders: `tailScaledNumerator`,
`tailRatio`, `strictTailEntry_of_scaledNumerator` (the positive
cross-multiplication of `06:1788--1790`), and `tailT4_margin`.

## The auxiliary-source chain moves downstream

**Three** declarations that earlier revisions of this file carried are deleted
here and **re-authored, at the pin, in
`src/EthInapproximability/ParameterizedNP/AuxSourceDerivations.lean`**
(`AUX-SOURCE-DERIVATIONS-001`).  They are:

* `auxSourceSLeN` and `auxSourceSMinusThree` -- displays 8 and 9, which stated
  the chain over a free natural `sv` with `sv <= auxY n` and
  `auxY n ^ 2 - 15 <= n` **assumed**.  `sv` is not the paper's `s`: `06:118`
  defines `s = 2^{ceil(B_s u^2)}` at the `K1`-defined `B_s` (`02:815--819`), and
  the two assumed links are steps `06:1894` and `06:1895--1899` **derive**;
* `auxSourceChain_hypotheses_consistent` -- the chain-consistency probe, read at
  `B_s = 1` and `u = 1`, values the definitional chain can never take
  (`B_s = T^2 >= 4096` from `T >= 64` at `02:817`; `u >= 3` from the banked
  `ParameterSchedule.three_le_uAux`), hence at an unreachable point.

A **fourth** declaration, `ellN_at_241` (`l(241) = 4`), is deleted here and is
**not** re-authored anywhere, because nothing about it needs a pin: there is no
`B_s` in `l(241) = 4`.  Its history is a reversal and is recorded as one, at the
trailing note below and in the ledger row.  In brief: an earlier revision of
`cc-t8c-r2` lane C deleted it; the `cc-t8c-r2` gate ruled that deletion outside
the round's enumerated delta (finding **G4**) and ordered it **restored**, which
was done byte-identically; the `cc-t8c-r3` regate then established that
`IterationAssembly.envelope_fires_nondegenerate` (`:1393--1394`) **already
carries `ellN 241 = 4` as its third conjunct**, reachable here through the
whole-namespace `open` at `:324` and the import closure, and ruled that the
conjunct-level dedup rule **has no grandfather exception**.  The declaration and
its audit row are therefore deleted on that later order.  Any site needing the
fact consumes `IterationAssembly.envelope_fires_nondegenerate.2.2.1`; this module
has no consumer of it and none exists tree-wide.  The two claims an earlier
revision made -- that all four deletions were "re-authored at the pin" and that
each replacement is "strictly stronger" -- were and remain **false of this one**,
and are not reinstated by the deletion: `AuxSourceDerivations.ellN_at_leastSourceSize`
subsumed it by specialization rather than strengthening it, and that accessor's
guard has now been tightened past `lam = 4` so that the specialization no longer
occurs either.

The repair for the other three is a pin, `B_s := MechanicalCompilerResidue.bsSched`,
and **the pin cannot be written here**: `MechanicalCompilerResidue.lean:1` imports
this module, so the `B_s` owner is strictly downstream and a `bsSched`-pinned
statement in this file would close an import cycle.  What stays here is exactly
what is valid upstream of the pin -- `auxY`, `auxY_ge_sixteen`, `dsExp`, and
displays 6 and 7, whose free `B_s` and `u` are discharged at their own downstream
firing sites.  Nothing about displays 8 and 9 is withdrawn: those two are
re-stated downstream, strictly stronger, with both assumed links proved.

## Round marker

**Round marker.**  `cc-t8c-r2` lane C, plus the two in-round repair cycles that
applied the `cc-t8c-r2` and `cc-t8c-r3` gates' prescriptions to these bytes.  The
lane-C changes to this module are, in full: the three deletions listed above; the
FREE-binder correction for `B_s` and `u` recorded under "What is source-defined";
the declaration-count corrections; from the first repair cycle, the restoration of
`ellN_at_241` (gate finding G4) and the citation repair `06:1892--1893` ->
`06:1891` at the trailing note (G1); and from the second, the **deletion** of
`ellN_at_241` on the `cc-t8c-r3` gate's express reversal of G4, with that
reversal and its reason recorded rather than the declaration silently re-removed.
**No statement, hypothesis, binder or proof term of any surviving declaration
changed in any of the three steps** -- the lane-C delta against the r1 park is
deletions plus comments only, the first repair cycle's delta against that is one
restored declaration plus comments, and the second's is one deleted declaration
plus comments.  Written after its event: every sentence here describes bytes that
are in this file.

## Non-vacuity and canonical inhabitation

What *is* claimed, and is the paper's own arithmetic rather than ours, is the
`T4_Q` margin of `06:1777--1785`: "For each of its four entries,
`m/sigma <= 200 < 2^8`, and `L_P >= 4`, so `V_u <= 2^{C_exc L_P^2 + 8} <=
2^{(C_exc+1)L_P^2} < 2^{A_wrap L_P^2} = q` by `eq:Awrap-coefficient-search`."
`tailT4_margin` lands that inequality at the frozen extremal legal ratio
`m/sigma = 200`, over the banked `ParameterSchedule.qWrap` and the banked
`A_wrap > C_exc` of `IterationAssembly.coefficientPass_awrap`.

The four-constructor tail-class tag, tail-entry record, and registry-shape
predicate for the paper's 29-row persistent registry are **withdrawn, not
deferred**.  The module row `SCHEDULE-MAJORANT-RESIDUE-001` banked with this
tranche registers only this module's 30 landed declarations; it neither
authorizes that deleted registry surface nor carries a canonical-inhabitation
requirement for it.  Reintroduction requires fresh authorization and a ledger
row at that time.

Display 1 is not deferred behind a probe: it is **withdrawn** (see "Withdrawn
carriers").  Its five-conjunct schema had lost its firing site, and the only
inhabitant left was a self-chosen BEYOND-PAPER audit probe, which claims no
legality and cannot stand in for the paper's instance.  Rather than keep a
premise bundle that no legal instance is known to satisfy, this revision
carries **no** display-1 declaration at all.  Reinstating one is an
**unregistered future obligation**: it needs an authorized ledger row carrying
its own canonical-inhabitation requirement, and no such row exists --
the module row `SCHEDULE-MAJORANT-RESIDUE-001` banked with this tranche
registers only this module's 30 landed declarations; it neither authorizes
display-1 reinstatement nor carries that reinstatement's canonical-inhabitation
requirement.  This comment creates neither the missing authorization nor a
ledger row for it.

The BEYOND-PAPER labels that do survive are of a different kind and are kept.
`bBal_exponent_is_essential` claims **no** legality at all: it is a rejection
probe exhibiting that the reading `02:189--196` refutes is false.
`lSandwich_fires` and `dimRow_premise_inhabited` are premise-satisfiability
audits for two schemas that **do** have in-file firing sites at the evaluated
definitional chain (`lSandwich_of_lower`, `cdimLiteral_dominates_rows`), so
neither carries the weight of showing that its schema is about the paper's
object.  The withdrawn display-1 probe was the opposite case -- the only
inhabitant of a schema with no firing site -- which is why it goes rather than
stays.

## Reader counterpart

Exactly **one** reader item is claimed, by `bBal`:
`routes/parameterized-np/reader-facing/sections/C-effectivity-details.tex`,
`eq:paper-balanced-family-size` (label line 41, display lines 39--42),
"`N = p^t < (2 max{q,1000mt^2,2})^t`" inside
`lem:paper-explicit-balanced-family` (label line 32).  A sweep of the interval
`C-effectivity-details.tex:28--50` across this route's Lean modules, the
crosswalk and the ledger found no prior assignment of that display, and no other
line in the interval is claimed here.

**No other declaration in this module claims a reader item**, and the reason is
the reader's own content: the 41-page artifact prints none of `C_size`,
`C_exc`, `A_wrap`, `A_*`, `b_T`, `b_1`, `L_P`, `C_dim`, `U_dim`, `P_dim`, the
tail-error classes, the 29-entry persistent registry, the `L`/`l(n)`
substitution, or the auxiliary source row; its only neighbouring displays are
`eq:paper-envelope` (05-iteration.tex, label 190) and
`eq:paper-log-carrier-recurrence` (05-iteration.tex, label 175), and the
crosswalk assigns the latter to `SIZE-001`'s own declarations.  That assignment
is **declined here**, so `oneLevelLogSize` claims nothing.
-/

namespace EthInapproximability.ParameterizedNP.ScheduleMajorantResidue

open EthInapproximability.ParameterizedNP.IterationAssembly

/-! ## Section 1  Binary length -- no declaration

The frozen core operations of `02-mechanical-contract.tex:279--283` are
`subN(x,y) = max{x-y,0}`, `clog2N(x) = min{r : x <= 2^r}` and
`bl(x) = clog2N(x+1)`.  Only the third is needed below, and `clog2N` is
`Nat.clog 2` exactly (the least `r` with `x <= 2^r`).

`bl` is therefore **not defined here**, and it is not defined anywhere on this
route: `02:282` has no named Lean reification at all.  The two statements below
that need `bl` (`n2ExplicitCodeEnvelope`, `n2DimensionCodeBound`) write the
inline `Nat.clog 2 (x + 1)` in statement position, which is the frozen display
verbatim.  The three binary-length
rules `02:301--303` names -- product, maximum, and fixed square -- are taken as
local steps inside the proof
that needs them, so they add no module-level surface either. -/

/-! ## Section 2  The balanced-family envelope

`def:effective-schedule-certificate` (`02-mechanical-contract.tex`, label line
177) fixes the envelope that `sec:one-level-dimensions` consumes.  Both
quantities are reified at their own anchors; neither is banked elsewhere. -/

/-- **`X_bal(q,t,m) = max{q, 1000mt^2, 2}`** --
`02-mechanical-contract.tex:178--181`, "For positive integers `q,t,m`, put
`X_bal(q,t,m) = max{q,1000mt^2,2}`".  The three entries are kept in the frozen
order. -/
def xBal (q t m : ℕ) : ℕ := max (max q (1000 * m * t ^ 2)) 2

/-- **`B_bal(q,t,m) = (2 X_bal(q,t,m))^t`** -- `eq:balanced-family-envelope`
(`02-mechanical-contract.tex`, label line 187, display lines 183--188), "the
explicit family-size envelope".

Reader counterpart: `eq:paper-balanced-family-size`
(`routes/parameterized-np/reader-facing/sections/C-effectivity-details.tex`,
label line 41, display lines 39--42), "`N = p^t < (2 max{q,1000mt^2,2})^t`",
inside `lem:paper-explicit-balanced-family` (label line 32).  Opened first-hand
this tranche; it states the same right-hand side, with the reader's strict
`<` on the literal family size and the paper's non-strict envelope name.  This
is the only reader item claimed by this module.

`02:189--196` records why the exponent `t` may not be relaxed to a fixed-degree
polynomial in `q`, and that warning is what `bBal_exponent_is_essential`
exhibits in the kernel. -/
def bBal (q t m : ℕ) : ℕ := (2 * xBal q t m) ^ t

/-- **Aux X1 (the frozen floor of the envelope's base).**  `X_bal >= 2`, from
the third entry of the maximum, so the base `2 X_bal` is at least four and the
envelope is never the degenerate `1^t`.  General. -/
theorem two_le_xBal (q t m : ℕ) : 2 ≤ xBal q t m := le_max_right _ _

/-- **Aux X2 (positivity).**  `B_bal >= 1`, so `clog_2 B_bal` is defined on a
positive argument at every parameter triple.  General. -/
theorem bBal_pos (q t m : ℕ) : 0 < bBal q t m := by
  have h := two_le_xBal q t m
  have hb : 0 < 2 * xBal q t m := by omega
  exact pow_pos hb t

/-- **Statement pole (`02:189--196`): the exponent `t` is essential.**

"when `q` is the dominant scale, the literal family required by
`eq:effective-balanced-builder` has `q^{Theta(t)}` indexed members.  A
fixed-degree polynomial in `q` is not a valid envelope."  Exhibited in the
kernel at `q = 4`, `t = 4`, `m = 0`: the envelope is `8^4 = 4096`, while the
fixed-degree candidate `q^2 = 16` is far below it, so no fixed power of `q`
bounds `B_bal`.

**BEYOND-PAPER AUDIT** at `(q, t, m) = (4, 4, 0)` and at the candidate exponent
`2`: this is a rejection probe claiming no legality, exhibited to show that the
refuted reading is false, not that these are schedule values. -/
theorem bBal_exponent_is_essential : 4 ^ 2 < bBal 4 4 0 := by
  norm_num [bBal, xBal]

/-! ## Section 3  Display 1 -- the structural majorants -- no declaration

`eq:structural-majorants` (`06-parameter-schedule.tex`, label line 1701, display
lines 1691--1702), reached at lines 1689--1690 by "Beyond the constant input
cutoffs emitted by that traversal", is the five-row block

```
 every new logarithmic side length and auxiliary scale <= W(L) := 2^{C_size L^8},
 b_T >= L^20/C_size,   b_1 >= A_*^6/C_size,
 log_2(e_0^max E_T u_term B_theta + 2) <= C_exc L_P^2,
 L_theta <= 2^{C_size L_P},
```

with the frozen delineation at `06:1703--1706` ("Here `q_2` itself is not called
an auxiliary scale: only `log_2 q_2` appears among the new logarithmic side
lengths.  The exponent eight is not optimised; it is the largest entry in the
displayed, mechanically generated degree table").

**This module lands no declaration for it.**  An earlier revision carried a
five-conjunct `Prop`-valued schema in the display's own symbols, an unfolding
lemma, a `C_size`-monotonicity lemma, the single real-logarithm step the third
row needs, a restatement of the banked `B_theta = B_pair` its fourth row leans
on, and one BEYOND-PAPER audit probe.  It also carried the schedule-level
*firing* declaration that supplied every source-defined symbol of the display
from that symbol's own defining display in dependency order.  That firing
declaration was withdrawn together with the duplicate `b_T` reification
(see "Withdrawn carriers"), and a premise bundle with no firing site whose only
inhabitant is a self-chosen BEYOND-PAPER probe states nothing about the paper's
object: the probe claims no legality by construction, so it cannot serve as the
bundle's non-vacuity witness, and no legal inhabitant remained.  The whole group
is therefore withdrawn rather than left standing unfired.

Nothing needed by the block is reified here, and with the block gone nothing in
this module consumes any of it:

* `k_T = log_2(s/4)` and `b_T = 2^{j_49(k_T)}` (`06:237--243`) -- reified once
  for this route in `ScheduleTemplateResidue` (`kT`, `bT`) over the banked
  `ParameterSchedule.j49`; this module carries no second copy and takes no
  import of that module.
* `U_0 = max{2, b_out/eta_R}` (`06:295--297`) and `A_*` (`eq:Astar-choice`,
  label line 304, display lines 299--305, "let `A_*` be the least power of two
  at least `max{16, B_pub, z_R, log_2 q_2, s, ceil(log_2 U_0)}`") -- likewise
  reified once in `ScheduleTemplateResidue`, where `U0sched` is `06:296`
  verbatim, `astarThreshold` is the six-entry maximum in the frozen print order,
  and `astar`/`astarExp` are the search and its exponent over the banked
  `ParameterSchedule.leastPowTwoGe`/`.leastPowTwoExp`, with `ceil(log_2 U_0)`
  the frozen core operation `clog_2(U_0)` of `02:286--288` and no real logarithm
  rounded by hand.  The frozen floor `A_* >= 16` of `06:481--488` is
  `ScheduleTemplateResidue.le_astar` at
  `ScheduleTemplateResidue.sixteen_le_astarThreshold`.
* `W(L)` and `C_size` -- banked as `SizePropagation.structuralW`,
  `.csizeLiteral` (`eq:Csize-literal-producer`); `b_1` and `a` -- banked as
  `MassRedistributionTail.b1`, `.aStage1`; `B_theta = B_pair` (`06:718`) --
  banked as `ParameterSchedule.schedule_Btheta_eq_Bpair` over
  `WrapperProtectedEarly.Btheta`.  All are consumed by pin elsewhere on the
  route and are not restated here.

Reinstating display 1 is an **unregistered future obligation**: it needs an
authorized ledger row carrying its own canonical-inhabitation requirement, and
no such row exists.  The terms are recorded in "Withdrawn carriers" above. -/

/-! ## Section 4  Displays 2--4 -- the tail arithmetic

`06:1708--1724` and `06:1745--1795`.  What this section lands is the frozen
*arithmetic* of the tail entries over explicit numeric binders, and nothing
else: the four-class tag, the entry record and the registry-shape predicate are
the carriers withdrawn in the module header, because `06:1790--1793`'s checker
compares against coefficient derivations, literal strict margins and persistent
roots that the frozen source never prints.

One frozen delineation matters for what is *absent* here as much as for what is
present: there is **no** global minimum-slack clock ("There is deliberately no
global minimum-slack clock.  Such a clock would mix candidate-dependent slacks
from different classes and would not be a value available to the `c`-only
compiler", `06:1755--1757`), so nothing below quantifies over the registry as a
whole -- every statement is about one entry's own numbers. -/

/-- **Display 4 -- `eq:tail-scaled-numerator`, the scaled numerator**
(`06-parameter-schedule.tex`, label line 1764, display lines 1761--1765):
`V_u = m N_e/sigma`, with `tau_e = N_e/D_e`.

`06:1759--1761`: "Instead, for each entry separately, the coefficient pass
requests the exact scaled numerator".  Kept in `ℚ`, which is the frozen exact
arithmetic of `02:309--312`; no real-number placeholder is introduced. -/
def tailScaledNumerator (m Ne : ℕ) (σ : ℚ) : ℚ := (m : ℚ) * (Ne : ℚ) / σ

/-- **Display 4 -- `eq:tail-scaled-numerator`, the class ratio**
(same display): `tau_e = N_e/D_e`. -/
def tailRatio (Ne De : ℕ) : ℚ := (Ne : ℚ) / (De : ℚ)

/-- **Aux R1 (the frozen positive cross-multiplication).**

`06:1788--1790`: "Positive cross-multiplication of `eq:tail-scaled-numerator`
then gives `eq:strict-tail-entry`."  The stored persistent comparison
`V_u < D_e` therefore yields the entry's own strict comparison `m tau_e <
sigma`, and the two positivity side conditions used are exactly the ones the
frozen entry shape carries.  General. -/
theorem strictTailEntry_of_scaledNumerator {m Ne De : ℕ} {σ : ℚ}
    (hσ : 0 < σ) (hDe : 0 < De) (h : tailScaledNumerator m Ne σ < (De : ℚ)) :
    (m : ℚ) * tailRatio Ne De < σ := by
  have hDeQ : (0 : ℚ) < (De : ℚ) := by exact_mod_cast hDe
  rw [tailScaledNumerator, div_lt_iff₀ hσ] at h
  rw [tailRatio, mul_div_assoc', div_lt_iff₀ hDeQ]
  calc (m : ℚ) * (Ne : ℚ) < (De : ℚ) * σ := h
    _ = σ * (De : ℚ) := by ring

/-- **The `T4_Q` same-degree margin of `06:1777--1785`, in the kernel.**

"Class `T4_Q` is different: `D_e = q = 2^{A_wrap L_P^2}` has the same degree as
its numerator.  For each of its four entries, `m/sigma <= 200 < 2^8`, and
`L_P >= 4`, so `V_u <= 2^{C_exc L_P^2 + 8} <= 2^{(C_exc+1)L_P^2} <
2^{A_wrap L_P^2} = q` by `eq:Awrap-coefficient-search`."

The two frozen inputs are exactly the hypotheses: `A_wrap > C_exc`, which is the
banked conclusion of `IterationAssembly.coefficientPass_awrap`, and `L_P >= 4`,
which is the banked `ParameterSchedule.four_le_LPwidth_sched`.  `q` is the
banked `ParameterSchedule.qWrap`.  The numerals `200`, `8`, `4` are the frozen
ones at this anchor. -/
theorem tailT4_margin {Cexc Awrap LP : ℕ} (hA : Cexc < Awrap) (hLP : 4 ≤ LP) :
    200 * 2 ^ (Cexc * LP ^ 2) < ParameterSchedule.qWrap Awrap LP := by
  have h16 : 16 ≤ LP ^ 2 := by nlinarith
  have hstep : (Cexc + 1) * LP ^ 2 ≤ Awrap * LP ^ 2 :=
    Nat.mul_le_mul_right _ hA
  have hexpand : (Cexc + 1) * LP ^ 2 = Cexc * LP ^ 2 + LP ^ 2 := by ring
  have hexp : Cexc * LP ^ 2 + 16 ≤ Awrap * LP ^ 2 := by omega
  have hpow : (2 : ℕ) ^ (Cexc * LP ^ 2 + 16) ≤ 2 ^ (Awrap * LP ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hsplit : (2 : ℕ) ^ (Cexc * LP ^ 2 + 16) = 2 ^ (Cexc * LP ^ 2) * 65536 := by
    rw [pow_add]; norm_num
  have hpos : 0 < (2 : ℕ) ^ (Cexc * LP ^ 2) := pow_pos (by norm_num) _
  rw [ParameterSchedule.qWrap]
  omega

/-! ## Section 4b  The tail-cutoff successor bump (`06:1766--1774`)

The frozen span, whole and verbatim from
`sections/06-parameter-schedule.tex` of the release named by
`routes/parameterized-np/CURRENT_VERSION`:

```
and returns a literal coefficient \(C_u\), degree \(d_u\), and checked
derivation tree for \(V_u\le2^{C_uP^{d_u}}\).  For the first three classes,
the tail cutoff uses \(C_u^+=C_u+1\), not \(C_u\).  Since \(P\ge2\), its checked
non-strict exponent comparison gives
\[
 V_u\le2^{C_uP^{d_u}}
     <2^{(C_u+1)P^{d_u}}\le D_e,
\]
which is the stored persistent strict comparison \(V_u<D_e\).
```

`FRESH-1` of the ledger's `cc-t8a` sweep block.  The span carries **no**
`\label`, so it is not a display; it is the *derivation* joining the two
displays this section already owns -- the coefficient pass's non-strict row
bound on `V_u` (the scaled numerator of `eq:tail-scaled-numerator`, display 4)
to the strict stored comparison whose positive cross-multiplication at
`06:1788--1790` yields `eq:strict-tail-entry` (display 3).  Nothing here
restates either display: `tailScaledNumerator`, `tailRatio` and
`strictTailEntry_of_scaledNumerator` are consumed above by name.

**Scope of the bump.**  The frozen sentence restricts `C_u^+ = C_u + 1` to *the
first three classes* of `eq:four-tail-errors` -- `T1_Q2`, whose `D_e` is "its
`ECut` row", and `T2_BT` / `T3_B1`, whose `D_e` are "their respective `PCut`
rows" (`06:1774--1777`).  Class `T4_Q` is expressly *different* (`06:1777`:
"Class `T4_Q` is different") and is **not** covered here: its same-degree margin
is the separately banked `tailT4_margin` above, which is why nothing below is
stated at `q = 2^{A_wrap L_P^2}`.

**What `P` is, and why it is a binder.**  `P` is the coefficient pass's
*driver*, fixed per class rather than globally: `06:1609--1610` records that
"the C7 roots and nine T1--T2 factors use driver `L+2`, whereas the seven T3
factors use driver `A_*`", and the `T4_Q` paragraph runs the same shape at
driver `L_P` with degree two.  The frozen display is generic over that driver
and states its own floor in the same breath ("Since `P >= 2`"), so `P` enters as
a binder carrying exactly that hypothesis, and Section 4b's inhabitation lemma
then fires it at the paper's own `T1`/`T2` driver `L + 2` over the banked
`EnvelopeRealization.normalizedL`, discharging the floor from the banked
`EnvelopeRealization.four_le_normalizedL` (`06:1868--1869`, `L >= 4`).  The
other frozen driver `A_*` is `ScheduleTemplateResidue`'s reification and that
module is **not** in this module's import closure, so no firing at `A_*` is
attempted here rather than a second `A_*` being reified.

**Why `C_u` and `d_u` are binders.**  `06:1628--1631` is explicit: "the registry
determines a finite table of one checked row `(u, C_u, d_u, P_u)` per expanded
successor or tail factor root; no human or formalizer supplies a coefficient."
Supplying either would be the authoring defect that sentence forbids, so both
stay free and the checked comparison that consumes them stays a hypothesis.
`D_e` is likewise the entry's own denominator: the four-constructor tail-class
tag, the tail-entry record and the 29-row registry shape are the carriers
**withdrawn** in the module header (`06:1790--1793` demands a bijection against
coefficient derivations and literal strict margins the frozen source never
prints), so nothing below quantifies over the registry, exactly as the rest of
Section 4 does not.

**Canonical inhabitation is DEFERRED, and the inhabitation lemma below is not
it.**  The paper's own instances are the 29-row registry's first-three-class
entries, whose checked coefficient row `06:1628--1631` prints as
`(u, C_u, d_u, P_u)`, while per-entry cutoff, class placement and the 29-entry
bijection are governed by `06:1759--1793` / `06:1917--1949`.  The frozen source
prints no such row, so no canonical firing exists until `PARAM-001`'s compiler.
`tailCutoffBump_premises_inhabited` is a **synthetic satisfiability probe at the
paper's driver, not the paper's instance** (wording fixed at `cc-t8f-r2`, gate
finding 6; the `r2` bytes called it a "nondegenerate legal inhabitant" and said
the bundle was satisfiable "at legal values", and both overclaimed a legality
this round cannot supply).  It is labelled BEYOND-PAPER AUDIT / NON-FIDELITY at
its own docstring: it fires the bundle at the paper's own `T1`/`T2` driver and at
the two *endpoints* the frozen checked comparisons permit (`V_u` at its row
bound, `D_e` at the bumped power), stays general in `C_u`, `d_u` and the four
public inputs, and the conclusion is still strict.  The entry data `m`, `N_e`,
`σ` it supplies as existential witnesses are **ours**, which is precisely why the
lemma claims no legality.  It is evidence that the premise bundle is jointly
satisfiable; it is **not** a discharge of the canonical obligation, and the
ledger row `FRESH-1` should record that obligation as DEFERRED behind
`PARAM-001`'s compiler rather than closed. -/

/-- **Aux 4b.1 (the frozen "Since `P >= 2`" step, isolated).**

`06:1768`.  The whole content of the successor bump is that one added unit of
coefficient buys a strictly larger exponent, and it does so precisely because
the driver is at least two, hence `P^{d_u} >= 1` at every degree including
`d_u = 0`.  General in the coefficient, the degree and the driver. -/
theorem tailCutoffBump_exponent_strict {Cu du P : ℕ} (hP : 2 ≤ P) :
    Cu * P ^ du < (Cu + 1) * P ^ du := by
  have hpos : 0 < P ^ du := pow_pos (by omega) du
  calc Cu * P ^ du < Cu * P ^ du + P ^ du := Nat.lt_add_of_pos_right hpos
    _ = (Cu + 1) * P ^ du := by ring

/-- **Aux 4b.2 (the integer middle of the frozen chain).**

`06:1770--1773`, the two right-hand links `2^{C_u P^{d_u}} < 2^{(C_u+1)
P^{d_u}} <= D_e`, which mention no `V_u` and live entirely in `ℕ`: the bumped
coefficient's checked non-strict comparison against `D_e` places the *unbumped*
row strictly below `D_e`.  This is what makes the stored comparison strict, and
it is stated separately so that the strictness is not entangled with the
rational scaled numerator.

General in the coefficient, the degree, the driver and the denominator. -/
theorem tailCutoffBump_row_lt_denominator {Cu du P De : ℕ} (hP : 2 ≤ P)
    (hbump : (2 : ℕ) ^ ((Cu + 1) * P ^ du) ≤ De) :
    (2 : ℕ) ^ (Cu * P ^ du) < De := by
  have hexp : Cu * P ^ du < (Cu + 1) * P ^ du := tailCutoffBump_exponent_strict hP
  have hpow : (2 : ℕ) ^ (Cu * P ^ du) < 2 ^ ((Cu + 1) * P ^ du) :=
    Nat.pow_lt_pow_right (by norm_num) hexp
  exact lt_of_lt_of_le hpow hbump

/-- **The tail-cutoff successor bump, whole interval** -- `06:1766--1774`
(`FRESH-1`).

From the coefficient pass's checked row `V_u <= 2^{C_u P^{d_u}}` and the tail
cutoff's checked non-strict exponent comparison **taken at the bumped
coefficient** `C_u^+ = C_u + 1`, i.e. `2^{(C_u+1) P^{d_u}} <= D_e`, the frozen
chain

```
V_u <= 2^{C_u P^{d_u}} < 2^{(C_u+1) P^{d_u}} <= D_e
```

yields the stored persistent strict comparison `V_u < D_e`.  Both frozen
hypotheses are exactly the two the source names, and the only side condition is
the frozen `P >= 2`.

**`V_u` is NOT a free binder here.**  `06:1761--1765` *defines* `V_u = m N_e/σ`,
which is the banked `tailScaledNumerator` above, so every statement in this
section is pinned at that reification and no statement quantifies over a
free rational standing for `V_u`.  It is kept in `ℚ` because the frozen display
is a quotient by a positive rational slack, and the mechanical contract makes
that quotient *exact*: `02:266` is the operator `divQ(e_Rat, e_Rat, h_{!=0})`
with its checked nonzero-denominator field, `02:275--276` says every such
`h`-field "is checked proof data", and `02:277--278` says "The semantics are the
indicated exact operations".  `D_e`, `C_u`, `d_u` and `P` are the integers the
source calls them.  *(Citation repaired at `cc-t8f-r2`, judge §2: the `r2` bytes
cited `02:309--312` here.  Line `309` is blank and `02:310--312` is about
rational **serialization** -- `num` / `absNum` / `den` in reduced form -- which
supports the rational carrier only obliquely and is not the arithmetic claim
this sentence makes.)*  The purely integer middle of the chain, which mentions
no `V_u` at all, is `tailCutoffBump_row_lt_denominator` below.

The strictness is the *whole* deliverable and it is the bump that supplies it:
`tailCutoffBump_is_essential` exhibits that the unbumped comparison
`2^{C_u P^{d_u}} <= D_e` does not yield `V_u < D_e`, so the conclusion is not
reachable from the checked row alone and no trivial witness discharges it.

General in `C_u`, `d_u`, `P`, `D_e` and in the entry data `m`, `N_e`, `σ`.

**Reader counterpart: NONE, against the PINNED release** (`cc-t8f-r2` gate,
finding 2, and judge finding `O-7`).  The `r2` bytes qualified the NONE by
naming a "neighbouring sentence", `05-iteration.tex:169`, "The first three have
computable persistent cutoffs".  **That sentence does not exist at the pinned
release.**  Swept first-hand over all ten files of
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/reader-facing/`:
the strings "persistent cutoff", `F(c)`, `P(c)`, `A_wrap` and `C_exc` do not
occur anywhere in that tree, and `05-iteration.tex:169` is a line of
`eq:paper-log-carrier-recurrence`.  The wording the `r2` bytes quoted lives only
in the concurrent session's **uncommitted working-tree** reader rewrite, which is
foreign dirty state and is never an anchor for this route.  The unqualified fact
stands: the 41-page artifact prints neither the registry nor the coefficient
rows, so it states nothing this declaration could be the counterpart of.  **No
crosswalk row is added**, because NONE adds none. -/
theorem tailCutoffBumpStrict {m Ne De Cu du P : ℕ} {σ : ℚ} (hP : 2 ≤ P)
    (hrow : tailScaledNumerator m Ne σ ≤ ((2 ^ (Cu * P ^ du) : ℕ) : ℚ))
    (hbump : (2 : ℕ) ^ ((Cu + 1) * P ^ du) ≤ De) :
    tailScaledNumerator m Ne σ < (De : ℚ) := by
  have hQ : ((2 ^ (Cu * P ^ du) : ℕ) : ℚ) < (De : ℚ) := by
    exact_mod_cast tailCutoffBump_row_lt_denominator hP hbump
  exact lt_of_le_of_lt hrow hQ

/-- **Aux 4b.3 (the interval closes into display 3's banked owner).**

`06:1766--1790` end to end: the bump gives the stored persistent strict
comparison `V_u < D_e`, and "positive cross-multiplication of
`eq:tail-scaled-numerator` then gives `eq:strict-tail-entry`" (`06:1788--1790`),
which is the banked `strictTailEntry_of_scaledNumerator` above, consumed by name
and not restated.  So the entry's own frozen meaning `m τ_e < σ`
(`eq:strict-tail-entry`, `06:1751--1754`) follows from the two checked
comparisons plus the two positivity side conditions the entry shape carries.

General in every component of the quadruple `(u, e, m, σ)` that appears. -/
theorem strictTailEntry_of_tailCutoffBump {m Ne De Cu du P : ℕ} {σ : ℚ}
    (hσ : 0 < σ) (hDe : 0 < De) (hP : 2 ≤ P)
    (hrow : tailScaledNumerator m Ne σ ≤ ((2 ^ (Cu * P ^ du) : ℕ) : ℚ))
    (hbump : (2 : ℕ) ^ ((Cu + 1) * P ^ du) ≤ De) :
    (m : ℚ) * tailRatio Ne De < σ :=
  strictTailEntry_of_scaledNumerator hσ hDe (tailCutoffBumpStrict hP hrow hbump)

/- **Aux 4b.4 was DELETED at `cc-t8f-r2`** (gate ruling, lane B decl 5 /
finding `F5`).  The `r2` bytes carried `tailCutoffBumpStrict_mono_De`, the
upward closure of the conclusion in the denominator.  It had **no frozen
statement anchor** -- its own docstring called it "a general property of the
interval rather than a frozen sentence" -- and **zero consumers anywhere in
`src/`**.  The gate ordered it deleted rather than relabelled; if a later
anchored proof needs the monotone step, it is kept proof-local at that site.
The `06:1774--1777` observation that motivated it (the four classes are compared
against different roots, so no statement here may depend on `D_e` being least)
survives as a fact about the section's *statements*, every one of which takes
`D_e` as a free binder and never as a minimum. -/

/-- **Aux 4b.5 (rejection probe: the bump is load-bearing).**

**BEYOND-PAPER AUDIT, claiming no legality.**  This probe audits *our* encoding
at a point the frozen source never visits, and it exists to answer the statement
pole for `tailCutoffBumpStrict`: why does the trivial route fail?  The frozen
sentence insists the tail cutoff uses `C_u^+ = C_u + 1` "not `C_u`", and this
exhibits the reason -- with the *unbumped* checked comparison
`2^{C_u P^{d_u}} <= D_e` in place of the bumped one, and every other hypothesis
including `P >= 2` intact, `V_u < D_e` is false.  So `tailCutoffBumpStrict`
cannot be weakened to the unbumped comparison, and its strict conclusion is not
obtainable from the checked row alone.

The witnesses are self-chosen, as a rejection probe's must be; they claim no
legality and carry no canonical credit.  They are nevertheless taken at the
frozen entry shape rather than at a bare rational: `V_u` is the banked
`tailScaledNumerator` of a quadruple with positive multiplier and positive
slack, exactly as `06:1747--1750` requires. -/
theorem tailCutoffBump_is_essential :
    ∃ (Cu du P De m Ne : ℕ) (σ : ℚ),
      0 < σ ∧ 0 < m ∧ 2 ≤ P ∧
        tailScaledNumerator m Ne σ ≤ ((2 ^ (Cu * P ^ du) : ℕ) : ℚ) ∧
        (2 : ℕ) ^ (Cu * P ^ du) ≤ De ∧
        ¬ tailScaledNumerator m Ne σ < (De : ℚ) := by
  refine ⟨1, 1, 2, 4, 4, 1, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    simp [tailScaledNumerator]

/-- **Aux 4b.6 (SYNTHETIC SATISFIABILITY PROBE at the paper's driver).**

**BEYOND-PAPER AUDIT / NON-FIDELITY, and NOT canonical inhabitation** -- see the
section header.  *(Relabelled at `cc-t8f-r2`, gate finding 6: the `r2` bytes
titled this lemma "the premise bundle is inhabited at **legal values**".  That
wording overclaims.  The entry data `m`, `N_e`, `σ`, `D_e` are **ours**; the
frozen source prints no registry row, so no value here can be certified legal,
and calling the point "legal" imported a legality the round cannot supply.  The
lemma is a **synthetic satisfiability probe**: it shows the premise bundle is
jointly satisfiable, at the paper's own driver, with self-chosen entry data.)*
The frozen source never prints a registry row's
`(C_u, d_u, D_e, m, N_e, σ)`, so this lemma leaves `C_u` and `d_u` universally
quantified, supplies the entry data itself as existential witnesses that claim
no legality, and pins only what the source does fix:

* the driver `P = L + 2`, which is `06:1609--1610`'s driver for the C7 roots and
  the nine `T1`/`T2` factors, at the banked `EnvelopeRealization.normalizedL`
  (`L = clog_2(A_pre)`, `06:1867--1869`), consumed by pin and not re-reified;
* its floor `2 <= P`, discharged from the banked
  `EnvelopeRealization.four_le_normalizedL` (`L >= 4`), so the frozen `P >= 2`
  is *derived* here rather than assumed;
* `V_u` and `D_e` at the two endpoints the frozen checked comparisons permit --
  `V_u` at its row bound `2^{C_u P^{d_u}}`, `D_e` at the bumped power
  `2^{(C_u+1) P^{d_u}}` -- which is the tightest point the bundle's own
  comparisons permit, and therefore the one where a defective encoding would
  collapse.

**Exactly ONE of the two nondegeneracy conjuncts carries nondegeneracy, and the
`r2` claim that both do is WITHDRAWN** (`cc-t8f-r2`, judge finding `O-6`,
machine-checked at the corner).  The `r2` bytes said both conjuncts "fail at the
degenerate corner and so are not decoration".  At the corner `C_u = 0` that this
lemma's own `1 <= C_u` excludes:

* `2 <= V_u` **does** fail -- `V_u = 2^(0 . P^{d_u}) = 1` -- so this conjunct is
  genuine nondegeneracy and is what `1 <= C_u` is there to buy;
* `2 V_u <= D_e` **does NOT** fail.  It holds at `C_u = 0` for every legal
  `P >= 2` and every `d_u`, because `D_e = 2^{P^{d_u}} >= 2^1 = 2` while
  `V_u = 1`.  It is a true and useful reading of the factor of two that
  "Since `P >= 2`" buys, but it is **decoration** as a nondegeneracy claim, and
  it is no longer offered as one.

The hypothesis `1 <= C_u` is **ours**, not the source's: it excludes the
zero-coefficient corner, and it is stated as a hypothesis of this lemma rather
than asserted of the paper's registry rows.  The lemma's mathematics is
unaffected by this correction -- only the `r2` prose was false.

General in the four public inputs, in `C_u` and in `d_u`. -/
theorem tailCutoffBump_premises_inhabited (bout Bpub zR clE du Cu : ℕ)
    (hCu : 1 ≤ Cu) :
    ∃ (P De m Ne : ℕ) (σ : ℚ),
      P = EnvelopeRealization.normalizedL bout Bpub zR clE + 2 ∧
        2 ≤ P ∧ 0 < σ ∧ 0 < m ∧ 0 < De ∧
        tailScaledNumerator m Ne σ = ((2 ^ (Cu * P ^ du) : ℕ) : ℚ) ∧
        De = 2 ^ ((Cu + 1) * P ^ du) ∧
        tailScaledNumerator m Ne σ ≤ ((2 ^ (Cu * P ^ du) : ℕ) : ℚ) ∧
        (2 : ℕ) ^ ((Cu + 1) * P ^ du) ≤ De ∧
        2 ≤ tailScaledNumerator m Ne σ ∧
        2 * tailScaledNumerator m Ne σ ≤ (De : ℚ) ∧
        tailScaledNumerator m Ne σ < (De : ℚ) := by
  have hL : 4 ≤ EnvelopeRealization.normalizedL bout Bpub zR clE :=
    EnvelopeRealization.four_le_normalizedL bout Bpub zR clE
  set P : ℕ := EnvelopeRealization.normalizedL bout Bpub zR clE + 2 with hPdef
  have hP : 2 ≤ P := by omega
  have hone : 1 ≤ P ^ du := Nat.one_le_pow _ _ (by omega)
  have hexp : 1 ≤ Cu * P ^ du := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hVu : tailScaledNumerator 1 (2 ^ (Cu * P ^ du)) 1
      = ((2 ^ (Cu * P ^ du) : ℕ) : ℚ) := by
    simp [tailScaledNumerator]
  have hDpos : 0 < (2 : ℕ) ^ ((Cu + 1) * P ^ du) := pow_pos (by norm_num) _
  refine ⟨P, 2 ^ ((Cu + 1) * P ^ du), 1, 2 ^ (Cu * P ^ du), 1,
    rfl, hP, by norm_num, by norm_num, hDpos, hVu, rfl, le_of_eq hVu, le_rfl, ?_, ?_, ?_⟩
  · rw [hVu]
    have hnat : (2 : ℕ) ≤ 2 ^ (Cu * P ^ du) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Cu * P ^ du) := Nat.pow_le_pow_right (by norm_num) hexp
    exact_mod_cast hnat
  · rw [hVu]
    have hsplit : (Cu + 1) * P ^ du = Cu * P ^ du + P ^ du := by ring
    have h2 : (2 : ℕ) ≤ 2 ^ P ^ du := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ P ^ du := Nat.pow_le_pow_right (by norm_num) hone
    have hstep : (2 : ℕ) * 2 ^ (Cu * P ^ du) ≤ 2 ^ ((Cu + 1) * P ^ du) := by
      rw [hsplit, pow_add]
      calc (2 : ℕ) * 2 ^ (Cu * P ^ du) = 2 ^ (Cu * P ^ du) * 2 := by ring
        _ ≤ 2 ^ (Cu * P ^ du) * 2 ^ P ^ du := Nat.mul_le_mul le_rfl h2
    exact_mod_cast hstep
  · exact tailCutoffBumpStrict hP (le_of_eq hVu) le_rfl

/-! ## Section 4b statement-numeral screen and binder provenance (`cc-t8f`, regate 1)

**Rebuilt at the `cc-t8f` regate under `B-SCREEN-FIX`** (gate ruling on all six
surviving declarations, and finding `G3`).  The `r2` bytes carried no screen for
this section; the r3 bytes carried one whose numeral coverage the gate accepted
but whose rows carried **no literal locations** and whose binder rows **grouped
occurrences across declarations**, which the gate ruled
INCOMPLETE-BY-CONTRACT.  This rebuild obeys the two rules the gate imposed:

1. **one row per occurrence** -- of a numeral, of a witness, and of a binder --
   never one row per name;
2. **every row carries a literal `ScheduleMajorantResidue.lean:<line>`
   location**.  The declaration-key letters are auxiliary labels only, never
   locations.

Re-extracted from the final bytes of this round, after the deletion of
`tailCutoffBumpStrict_mono_De`.  Six declarations survive in this section:
`tailCutoffBump_exponent_strict` (E), `tailCutoffBump_row_lt_denominator` (R),
`tailCutoffBumpStrict` (S), `strictTailEntry_of_tailCutoffBump` (T),
`tailCutoffBump_is_essential` (I) and `tailCutoffBump_premises_inhabited` (N).

*Numerals in Section 4b declaration statements -- one row per occurrence.*

| # | occurrence | location | decl | classification |
| --- | --- | --- | --- | --- |
| 1 | `2` in `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:642` | E | **CANONICAL-FORM**,
  `06:1768`: "Since `P >= 2`", the frozen floor stated in the same breath as the derivation |
| 2 | `1` in the conclusion's `(Cu + 1)` | `ScheduleMajorantResidue.lean:643` | E |
  **CANONICAL-FORM**, `06:1768`: `C_u^+ = C_u + 1`, the bump itself, verbatim |
| 3 | `2` in `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:658` | R | **CANONICAL-FORM**,
  `06:1768`, as row 1 |
| 4 | base `2` in `hbump : (2 : ℕ) ^ ((Cu + 1) * P ^ du) ≤ De` |
  `ScheduleMajorantResidue.lean:659` | R | **CANONICAL-FORM**, `06:1770--1772`: the frozen chain
  is written in base two throughout (`V_u <= 2^{C_u P^{d_u}} < 2^{(C_u+1)P^{d_u}} <= D_e`); the
  base is the display's, not ours |
| 5 | `1` in `hbump`'s `(Cu + 1)` | `ScheduleMajorantResidue.lean:659` | R | **CANONICAL-FORM**,
  `06:1768`, as row 2 |
| 6 | base `2` in the conclusion `(2 : ℕ) ^ (Cu * P ^ du) < De` |
  `ScheduleMajorantResidue.lean:660` | R | **CANONICAL-FORM**, `06:1770--1772`, as row 4 |
| 7 | `2` in `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:719` | S | **CANONICAL-FORM**,
  `06:1768`, as row 1 |
| 8 | base `2` in `hrow : tailScaledNumerator m Ne σ ≤ ((2 ^ (Cu * P ^ du) : ℕ) : ℚ)` |
  `ScheduleMajorantResidue.lean:720` | S | **CANONICAL-FORM**, `06:1766--1767`: the coefficient
  pass "returns ... checked derivation tree for `V_u <= 2^{C_u P^{d_u}}`", verbatim |
| 9 | base `2` in `hbump` | `ScheduleMajorantResidue.lean:721` | S | **CANONICAL-FORM**,
  `06:1770--1772`, as row 4 |
| 10 | `1` in `hbump`'s `(Cu + 1)` | `ScheduleMajorantResidue.lean:721` | S |
  **CANONICAL-FORM**, `06:1768`, as row 2 |
| 11 | `0` in `hσ : 0 < σ` | `ScheduleMajorantResidue.lean:739` | T | **CANONICAL-FORM**,
  `06:1748--1750`: the entry quadruple's fourth component is "a positive rational slack".  The
  zero is the positivity the frozen text states, not a chosen floor |
| 12 | `0` in `hDe : 0 < De` | `ScheduleMajorantResidue.lean:739` | T | **CANONICAL-FORM**,
  `06:1788--1790`: the frozen step is "**positive** cross-multiplication of
  `eq:tail-scaled-numerator`", and `D_e` is that display's denominator, so its positivity is the
  frozen side condition |
| 13 | `2` in `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:739` | T | **CANONICAL-FORM**,
  `06:1768`, as row 1 |
| 14 | base `2` in `hrow` | `ScheduleMajorantResidue.lean:740` | T | **CANONICAL-FORM**,
  `06:1766--1767`, as row 8 |
| 15 | base `2` in `hbump` | `ScheduleMajorantResidue.lean:741` | T | **CANONICAL-FORM**,
  `06:1770--1772`, as row 4 |
| 16 | `1` in `hbump`'s `(Cu + 1)` | `ScheduleMajorantResidue.lean:741` | T |
  **CANONICAL-FORM**, `06:1768`, as row 2 |
| 17 | `0` in the conjunct `0 < σ` | `ScheduleMajorantResidue.lean:776` | I |
  **CANONICAL-FORM**, `06:1748--1750`, as row 11 |
| 18 | `0` in the conjunct `0 < m` | `ScheduleMajorantResidue.lean:776` | I |
  **CANONICAL-FORM**, `06:1748--1750`: the third component is "a positive integer multiplier" |
| 19 | `2` in the conjunct `2 ≤ P` | `ScheduleMajorantResidue.lean:776` | I |
  **CANONICAL-FORM**, `06:1768`.  The probe keeps the frozen floor intact -- that is the point of
  the probe: only the bump is dropped |
| 20 | base `2` in the `hrow`-shaped conjunct | `ScheduleMajorantResidue.lean:777` | I |
  **CANONICAL-FORM**, `06:1766--1767`, as row 8 |
| 21 | base `2` in the **unbumped** conjunct `(2 : ℕ) ^ (Cu * P ^ du) ≤ De` |
  `ScheduleMajorantResidue.lean:778` | I | **CANONICAL-FORM**, `06:1768`: the frozen sentence
  says the cutoff uses `C_u^+`, "**not** `C_u`", and this is the `C_u` version it forbids,
  exhibited to show it does not suffice |
| 22 | `1` in `hCu : 1 ≤ Cu` | `ScheduleMajorantResidue.lean:831` | N | **SELF-CHOSEN /
  BEYOND-PAPER.**  The frozen source states no lower bound on a registry coefficient;
  `06:1628--1631` forbids a formalizer to supply one at all.  This hypothesis excludes the
  zero-coefficient corner so that the `2 <= V_u` conjunct has content, and it is **ours**, stated
  as a hypothesis of this probe and never asserted of the paper's rows |
| 23 | `2` in `P = EnvelopeRealization.normalizedL bout Bpub zR clE + 2` |
  `ScheduleMajorantResidue.lean:833` | N | **CANONICAL-FORM**, `06:1609--1610`: "the C7 roots and
  nine `T1`--`T2` factors use driver `L+2`".  The `+2` is the frozen driver's own offset over the
  banked `normalizedL`; no value is chosen |
| 24 | `2` in the conjunct `2 ≤ P` | `ScheduleMajorantResidue.lean:834` | N | **DERIVED, not
  assumed**: discharged in the proof from the banked
  `EnvelopeRealization.four_le_normalizedL` (`06:1868--1869`, `L >= 4`), so the frozen `06:1768`
  floor is a consequence here rather than a hypothesis |
| 25 | `0` in the conjunct `0 < σ` | `ScheduleMajorantResidue.lean:834` | N |
  **CANONICAL-FORM**, `06:1748--1750` (positive rational slack) |
| 26 | `0` in the conjunct `0 < m` | `ScheduleMajorantResidue.lean:834` | N |
  **CANONICAL-FORM**, `06:1748--1750` (positive integer multiplier) |
| 27 | `0` in the conjunct `0 < De` | `ScheduleMajorantResidue.lean:834` | N |
  **CANONICAL-FORM**, `06:1788--1790` (the positive cross-multiplication's denominator) |
| 28 | base `2` in `tailScaledNumerator m Ne σ = ((2 ^ (Cu * P ^ du) : ℕ) : ℚ)` |
  `ScheduleMajorantResidue.lean:835` | N | **CANONICAL-FORM**, `06:1766--1767`; the *equality*
  (rather than `<=`) is the endpoint choice, screened as binder provenance below, not as a
  numeral |
| 29 | base `2` in `De = 2 ^ ((Cu + 1) * P ^ du)` | `ScheduleMajorantResidue.lean:836` | N |
  **CANONICAL-FORM**, `06:1770--1772`, as row 4 |
| 30 | `1` in that conjunct's `(Cu + 1)` | `ScheduleMajorantResidue.lean:836` | N |
  **CANONICAL-FORM**, `06:1768`, as row 2 |
| 31 | base `2` in the `hrow`-shaped conjunct | `ScheduleMajorantResidue.lean:837` | N |
  **CANONICAL-FORM**, `06:1766--1767`, as row 8 |
| 32 | base `2` in the `hbump`-shaped conjunct | `ScheduleMajorantResidue.lean:838` | N |
  **CANONICAL-FORM**, `06:1770--1772`, as row 4 |
| 33 | `1` in that conjunct's `(Cu + 1)` | `ScheduleMajorantResidue.lean:838` | N |
  **CANONICAL-FORM**, `06:1768`, as row 2 |
| 34 | factor-`2` occurrence (i): `2` in `2 ≤ tailScaledNumerator m Ne σ` |
  `ScheduleMajorantResidue.lean:839` | N | **SELF-CHOSEN / BEYOND-PAPER.**  The frozen source
  never bounds `V_u` below.  This is the probe's own nondegeneracy conjunct: it fails at the
  corner `C_u = 0` and is exactly what `hCu` buys.  It claims nothing about the paper's rows |
| 35 | factor-`2` occurrence (ii): `2` in `2 * tailScaledNumerator m Ne σ ≤ (De : ℚ)` |
  `ScheduleMajorantResidue.lean:840` | N | **SELF-CHOSEN / BEYOND-PAPER, and DECORATION**
  (judge finding `O-6`).  It is a true reading of the room `2^{P^{d_u}} >= 2` gives, but it does
  **not** fail at the corner `C_u = 0` and is therefore not a nondegeneracy claim; the `r2` prose
  that said it was is withdrawn at the declaration |

**Statement-position occurrences elsewhere in Section 4b: NONE.**  Lines
`ScheduleMajorantResidue.lean:722`, `:738`, `:742`, `:775`, `:779`, `:832` and
`:841` are statement lines carrying no numeric literal, and there is no other
statement line in the section.  Checked by re-extraction over the final bytes.

*Proof-term witnesses -- one row per occurrence.*  These are not statement
positions; they are the values the two existential probes supply.

| # | occurrence | location | decl | classification |
| --- | --- | --- | --- | --- |
| W1 | `C_u := 1`, first component of the witness tuple |
  `ScheduleMajorantResidue.lean:780` | I | **SELF-CHOSEN / BEYOND-PAPER.**  A rejection probe's
  witnesses must be self-chosen and this one claims no legality: the frozen source prints no
  registry row |
| W2 | `d_u := 1`, second component | `ScheduleMajorantResidue.lean:780` | I | **SELF-CHOSEN /
  BEYOND-PAPER**, as W1 |
| W3 | `P := 2`, third component | `ScheduleMajorantResidue.lean:780` | I | **SELF-CHOSEN /
  BEYOND-PAPER**, taken at the frozen driver floor `06:1768` so the refutation is of the unbumped
  comparison and not of an ill-formed entry.  The floor is the paper's; the *equality* is ours |
| W4 | `D_e := 4`, fourth component | `ScheduleMajorantResidue.lean:780` | I | **SELF-CHOSEN /
  BEYOND-PAPER.**  Chosen at the unbumped row bound `2^{C_u P^{d_u}} = 4`, which is where the
  unbumped hypothesis stops being strict |
| W5 | `m := 4`, fifth component | `ScheduleMajorantResidue.lean:780` | I | **SELF-CHOSEN /
  BEYOND-PAPER**, a positive multiplier in the sense of `06:1748--1750`.  Ours |
| W6 | `N_e := 1`, sixth component | `ScheduleMajorantResidue.lean:780` | I | **SELF-CHOSEN /
  BEYOND-PAPER**, chosen so `V_u = m N_e / σ = 4` sits exactly at the unbumped bound.  Ours |
| W7 | `σ := 1`, seventh component | `ScheduleMajorantResidue.lean:780` | I | **SELF-CHOSEN /
  BEYOND-PAPER**, a positive rational slack, `06:1748--1750`.  Ours |
| W8 | `P := EnvelopeRealization.normalizedL bout Bpub zR clE + 2`, bound at
  `ScheduleMajorantResidue.lean:844` and supplied at `ScheduleMajorantResidue.lean:853` | N |
  **PINNED, not chosen**: the frozen `T1`/`T2` driver of `06:1609--1610` over the banked
  `normalizedL`, consumed at its own four-binder signature |
| W9 | `D_e := 2 ^ ((Cu + 1) * P ^ du)` | `ScheduleMajorantResidue.lean:853` | N | **SELF-CHOSEN
  endpoint / BEYOND-PAPER**: the *tightest* denominator the frozen bumped comparison admits.
  Legality is not claimed; the frozen source prints no `D_e` |
| W10 | `m := 1` | `ScheduleMajorantResidue.lean:853` | N | **SELF-CHOSEN / BEYOND-PAPER**: the
  least positive multiplier `06:1748--1750` allows.  Ours |
| W11 | `N_e := 2 ^ (Cu * P ^ du)` | `ScheduleMajorantResidue.lean:853` | N | **SELF-CHOSEN
  endpoint / BEYOND-PAPER**: chosen so `V_u` sits exactly at its frozen row bound.  Ours |
| W12 | `σ := 1` | `ScheduleMajorantResidue.lean:853` | N | **SELF-CHOSEN / BEYOND-PAPER**: a
  positive rational slack, `06:1748--1750`.  Ours |

**No numeral in Section 4b stands where a source-defined quantity belongs.**
`V_u` is the banked `tailScaledNumerator` and `τ_e` the banked `tailRatio`,
consumed by name; neither is re-expressed, and no numeral is written for `C_u`,
`d_u`, `D_e`, `m`, `N_e` or `σ` in any *statement*.  Every BEYOND-PAPER row above
is a witness inside an existential probe, or `hCu`, never a hypothesis or
conclusion of a paper-facing theorem.

*Binders in Section 4b statements -- one row per occurrence.*  No `structure`, no
premise bundle and no `Prop`-valued `def` is minted in this section, so there are
no fields to classify.

| # | binder | location | decl | provenance |
| --- | --- | --- | --- | --- |
| C1 | `Cu : ℕ` | `ScheduleMajorantResidue.lean:642` | E | **GENUINELY-FREE.**
  `06:1628--1631`: "the registry determines a finite table of one checked row
  `(u, C_u, d_u, P_u)` ...; no human or formalizer supplies a coefficient."  Supplying it would
  be the defect that sentence forbids |
| C2 | `du : ℕ` | `ScheduleMajorantResidue.lean:642` | E | **GENUINELY-FREE**, same sentence,
  same reason |
| C3 | `P : ℕ` | `ScheduleMajorantResidue.lean:642` | E | **GENUINELY-FREE, with the frozen
  floor attached.**  `06:1609--1610` makes the driver class-dependent (`L+2` for C7/`T1`/`T2`,
  `A_*` for the seven `T3` factors), and the frozen display is generic over it while stating
  `P >= 2` in the same breath; the binder carries exactly that hypothesis and nothing more |
| C4 | `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:642` | E | **FROZEN HYPOTHESIS**, `06:1768`
  verbatim.  Not ours |
| C5 | `Cu : ℕ` | `ScheduleMajorantResidue.lean:658` | R | **GENUINELY-FREE**, as C1 |
| C6 | `du : ℕ` | `ScheduleMajorantResidue.lean:658` | R | **GENUINELY-FREE**, as C2 |
| C7 | `P : ℕ` | `ScheduleMajorantResidue.lean:658` | R | **GENUINELY-FREE**, as C3 |
| C8 | `De : ℕ` | `ScheduleMajorantResidue.lean:658` | R | **GENUINELY-FREE.**  `06:1774--1777`
  gives the four classes *different* denominators (an `ECut` row for `T1_Q2`, `PCut` rows for
  `T2_BT`/`T3_B1`, and `q` for `T4_Q`, which this section excludes), so no statement here may fix
  it or assume it least |
| C9 | `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:658` | R | **FROZEN HYPOTHESIS**, `06:1768` |
| C10 | `hbump : (2 : ℕ) ^ ((Cu + 1) * P ^ du) ≤ De` | `ScheduleMajorantResidue.lean:659` | R |
  **FROZEN HYPOTHESIS**, `06:1768--1772`: the tail cutoff's checked non-strict comparison *at the
  bumped coefficient*.  This is the one hypothesis the section exists to isolate |
| C11 | `m : ℕ` | `ScheduleMajorantResidue.lean:719` | S | **GENUINELY-FREE.**  The entry
  quadruple's positive multiplier, `06:1748--1750`; the registry is unbuilt (`PARAM-001`) and
  prints no value |
| C12 | `Ne : ℕ` | `ScheduleMajorantResidue.lean:719` | S | **GENUINELY-FREE.**  The class
  numerator of `eq:tail-scaled-numerator` (`06:1761--1765`); likewise unprinted |
| C13 | `De : ℕ` | `ScheduleMajorantResidue.lean:719` | S | **GENUINELY-FREE**, as C8 |
| C14 | `Cu : ℕ` | `ScheduleMajorantResidue.lean:719` | S | **GENUINELY-FREE**, as C1 |
| C15 | `du : ℕ` | `ScheduleMajorantResidue.lean:719` | S | **GENUINELY-FREE**, as C2 |
| C16 | `P : ℕ` | `ScheduleMajorantResidue.lean:719` | S | **GENUINELY-FREE**, as C3 |
| C17 | `σ : ℚ` | `ScheduleMajorantResidue.lean:719` | S | **GENUINELY-FREE, and rational by the
  frozen shape.**  The quadruple's positive rational slack, `06:1748--1750`; `06:1755--1757`
  refuses a global minimum-slack clock, so it cannot be a fixed value |
| C18 | `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:719` | S | **FROZEN HYPOTHESIS**, `06:1768` |
| C19 | `hrow : tailScaledNumerator m Ne σ ≤ ((2 ^ (Cu * P ^ du) : ℕ) : ℚ)` |
  `ScheduleMajorantResidue.lean:720` | S | **FROZEN HYPOTHESIS**, `06:1766--1767`: the
  coefficient pass's own checked non-strict row |
| C20 | `hbump : (2 : ℕ) ^ ((Cu + 1) * P ^ du) ≤ De` | `ScheduleMajorantResidue.lean:721` | S |
  **FROZEN HYPOTHESIS**, `06:1768--1772`, as C10 |
| C21 | `m : ℕ` | `ScheduleMajorantResidue.lean:738` | T | **GENUINELY-FREE**, as C11 |
| C22 | `Ne : ℕ` | `ScheduleMajorantResidue.lean:738` | T | **GENUINELY-FREE**, as C12 |
| C23 | `De : ℕ` | `ScheduleMajorantResidue.lean:738` | T | **GENUINELY-FREE**, as C8 |
| C24 | `Cu : ℕ` | `ScheduleMajorantResidue.lean:738` | T | **GENUINELY-FREE**, as C1 |
| C25 | `du : ℕ` | `ScheduleMajorantResidue.lean:738` | T | **GENUINELY-FREE**, as C2 |
| C26 | `P : ℕ` | `ScheduleMajorantResidue.lean:738` | T | **GENUINELY-FREE**, as C3 |
| C27 | `σ : ℚ` | `ScheduleMajorantResidue.lean:738` | T | **GENUINELY-FREE**, as C17 |
| C28 | `hσ : 0 < σ` | `ScheduleMajorantResidue.lean:739` | T | **FROZEN SIDE CONDITION**,
  `06:1748--1750`; one of the two positivity facts the banked
  `strictTailEntry_of_scaledNumerator` consumes, copied at that pin |
| C29 | `hDe : 0 < De` | `ScheduleMajorantResidue.lean:739` | T | **FROZEN SIDE CONDITION**,
  `06:1788--1790`; the second such fact, copied at the same pin |
| C30 | `hP : 2 ≤ P` | `ScheduleMajorantResidue.lean:739` | T | **FROZEN HYPOTHESIS**, `06:1768` |
| C31 | `hrow` | `ScheduleMajorantResidue.lean:740` | T | **FROZEN HYPOTHESIS**,
  `06:1766--1767`, as C19 |
| C32 | `hbump` | `ScheduleMajorantResidue.lean:741` | T | **FROZEN HYPOTHESIS**,
  `06:1768--1772`, as C10 |
| C33 | `Cu : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:775` | I |
  **EXISTENTIALLY BOUND**, witnessed by W1.  Not a free binder of a paper-facing claim |
| C34 | `du : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:775` | I |
  **EXISTENTIALLY BOUND**, witnessed by W2 |
| C35 | `P : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:775` | I |
  **EXISTENTIALLY BOUND**, witnessed by W3 |
| C36 | `De : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:775` | I |
  **EXISTENTIALLY BOUND**, witnessed by W4 |
| C37 | `m : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:775` | I |
  **EXISTENTIALLY BOUND**, witnessed by W5 |
| C38 | `Ne : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:775` | I |
  **EXISTENTIALLY BOUND**, witnessed by W6 |
| C39 | `σ : ℚ`, existentially bound | `ScheduleMajorantResidue.lean:775` | I |
  **EXISTENTIALLY BOUND**, witnessed by W7 |
| C40 | `bout : ℕ` | `ScheduleMajorantResidue.lean:830` | N | **BANKED BINDER, passed straight
  through**: it is, symbol for symbol, the first binder of `EnvelopeRealization.normalizedL` /
  `.four_le_normalizedL`, consumed at that signature and never re-quantified or re-reified here |
| C41 | `Bpub : ℕ` | `ScheduleMajorantResidue.lean:830` | N | **BANKED BINDER**, as C40, second
  position |
| C42 | `zR : ℕ` | `ScheduleMajorantResidue.lean:830` | N | **BANKED BINDER**, as C40, third
  position |
| C43 | `clE : ℕ` | `ScheduleMajorantResidue.lean:830` | N | **BANKED BINDER**, as C40, fourth
  position.  This module holds no `ScheduleContext`, so no defined accessor is available to
  evaluate these four at; the evaluation is done downstream by the modules that do |
| C44 | `du : ℕ` | `ScheduleMajorantResidue.lean:830` | N | **GENUINELY-FREE**, as C2 |
| C45 | `Cu : ℕ` | `ScheduleMajorantResidue.lean:830` | N | **GENUINELY-FREE**, as C1 |
| C46 | `hCu : 1 ≤ Cu` | `ScheduleMajorantResidue.lean:831` | N | **OURS / BEYOND-PAPER**, as
  numeral row 22.  Disclosed at the declaration and never asserted of the paper's registry rows |
| C47 | `P : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:832` | N |
  **EXISTENTIALLY BOUND and PINNED**, witnessed by W8: here `P` is not free, it is the frozen
  driver `normalizedL + 2` |
| C48 | `De : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:832` | N |
  **EXISTENTIALLY BOUND**, witnessed by W9 |
| C49 | `m : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:832` | N |
  **EXISTENTIALLY BOUND**, witnessed by W10 |
| C50 | `Ne : ℕ`, existentially bound | `ScheduleMajorantResidue.lean:832` | N |
  **EXISTENTIALLY BOUND**, witnessed by W11 |
| C51 | `σ : ℚ`, existentially bound | `ScheduleMajorantResidue.lean:832` | N |
  **EXISTENTIALLY BOUND**, witnessed by W12 | -/

/-! ## Section 5  Displays 5--9 -- the substitution sandwich and the auxiliary
source row

`06:1846--1915`.  The auxiliary source row is the compiler's **first** emitted
row and, by `06:1861--1862`, "is not a candidate target": `06:1912--1915`
records that its sole consumer is the source-template count cancellation and
that "it contributes no target gate". -/

/-- **Display 5 -- `eq:L-ell-sandwich`**
(`06-parameter-schedule.tex`, label line 1849, display line 1848):
`l(n) - 2 <= L <= (l(n)+2)^{c+1}`.

`l(n)` is the **banked** `IterationAssembly.ellN`, consumed by pin.  The frozen
`l(n)-2` is truncated natural subtraction, which is exact on the search domain
`l(n) >= 2` (banked `SizePropagation.two_le_ellN`).

Both halves are stated, unlike the banked `EnvelopeRealization.lSandwich_upper`,
which deliberately proves only the upper one; the lower half is `06:1851--1852`'s
"The lower bound follows from the normalised source size", which is not in
Lean and stays `PARAM-001`. -/
def LSandwich (L c n : ℕ) : Prop :=
  ellN n - 2 ≤ L ∧ L ≤ (ellN n + 2) ^ (c + 1)

/-- **Display 5, fired at `L = clog_2(A_pre)` with only its `PARAM-001` half
open.**

The upper half is the banked `EnvelopeRealization.lSandwich_upper`, consumed by
pin at the same five envelope hypotheses it takes; the lower half is the only
remaining input and is exactly `06:1851--1852`'s normalised-source-size clause.
So the display holds as soon as that one open clause is supplied, and no other
hypothesis is smuggled in. -/
theorem lSandwich_of_lower (bout Bpub zR clE c n : ℕ) (h16 : 16 ≤ envE c n)
    (hbout : bout ≤ envE c n) (hBpub : Bpub ≤ envE c n) (hzR : zR ≤ envE c n)
    (hclE : clE ≤ envE c n)
    (hlow : ellN n - 2 ≤ EnvelopeRealization.normalizedL bout Bpub zR clE) :
    LSandwich (EnvelopeRealization.normalizedL bout Bpub zR clE) c n :=
  ⟨hlow, EnvelopeRealization.lSandwich_upper bout Bpub zR clE c n h16 hbout hBpub hzR hclE⟩

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY probe: the sandwich is satisfiable at
the frozen `A_pre` floor.**

At public inputs below the frozen constant branch, `A_pre = 16` and so
`L = clog_2 16 = 4`, which is the floor `06:1868--1869` records; the banked
`TruthTableExponent.ellN_le_six` then bounds `l(n) - 2 <= 4` on the whole
frozen small-source range.  Nondegenerate: all four public inputs are positive
and `L` is its evaluated value, not an assigned numeral.

Labelled **BEYOND-PAPER AUDIT** because the four public inputs
`(b_out, B_pub, z_R, clog_2(|E|+2)) = (8, 4, 2, 1)` are **ours**: they are free
inputs of the frozen source, and the frozen source neither instantiates them at
an application site nor exhibits a closed form for them, so this probe audits
our *encoding* at a point the paper never visits.  It is strictly weaker
evidence than a paper application point, and it does **not** discharge any
canonical-inhabitation obligation. -/
theorem lSandwich_fires (c n : ℕ) (hn : n ≤ 2 ^ 63) :
    LSandwich (EnvelopeRealization.normalizedL 8 4 2 1) c n := by
  have hApre : ParameterSchedule.Apre 8 4 2 1 = 16 := by
    norm_num [ParameterSchedule.Apre]
  have hupper : EnvelopeRealization.normalizedL 8 4 2 1 ≤ 4 := by
    have hle : ParameterSchedule.Apre 8 4 2 1 ≤ 2 ^ 4 := by rw [hApre]; norm_num
    exact Nat.clog_le_of_le_pow hle
  have hlower : 4 ≤ EnvelopeRealization.normalizedL 8 4 2 1 :=
    EnvelopeRealization.four_le_normalizedL 8 4 2 1
  have hL : EnvelopeRealization.normalizedL 8 4 2 1 = 4 := by omega
  have hell6 : ellN n ≤ 6 := TruthTableExponent.ellN_le_six n hn
  have hell2 : 2 ≤ ellN n := SizePropagation.two_le_ellN n
  refine ⟨by omega, ?_⟩
  rw [hL]
  calc (4 : ℕ) ≤ ellN n + 2 := by omega
    _ ≤ (ellN n + 2) ^ (c + 1) := Nat.le_self_pow (by omega) _

/-- **`d_s = 2(c+1)`** -- `06:1863--1865`, "Put `lambda = l(n)`, `d_s = 2(c+1)`,
`h_s = log_2 s = ceil(B_s u^2) = B_s u^2`". -/
def dsExp (c : ℕ) : ℕ := 2 * (c + 1)

/-- **Aux H1 (`h_s = log_2 s = B_s u^2`, exactly).**

`06:1865--1867`: "`h_s = log_2 s = ceil(B_s u^2) = B_s u^2`.  The last equality
is exact because `B_s` and `u` are integers."  Over the banked
`ParameterSchedule.sScale` (`eq:s-choice`) and its banked power readout, the
frozen ceiling really is the identity here, so no rounding enters the auxiliary
row.  General. -/
theorem hsAux_eq (Bs u : ℕ) :
    Nat.log 2 (ParameterSchedule.sScale Bs u) = Bs * u ^ 2 := by
  rw [ParameterSchedule.sScale_eq_pow, Nat.log_pow (by norm_num)]

/-- **Display 6 -- `eq:aux-source-s-normalized`**
(`06-parameter-schedule.tex`, label line 1881, display lines 1878--1882):
`h_s <= 4 B_s L^2 <= 4 B_s (lambda+2)^{2(c+1)}`.

The two inputs are the frozen ones and neither is invented here: `u <= 2L` is
`06:1875--1877` ("Monotonicity of the ceiling logarithm and `clog_2(2L) <= 2L`
give `u <= 2L`"), and the second is "The upper half of `eq:L-ell-sandwich`
therefore yields the literal normalized row" at `06:1876--1878`.  `lambda` is
the banked `IterationAssembly.ellN` and `h_s = B_s u^2` is `06:1865`'s exact
equality, pinned by `hsAux_eq`.

**Proved**, not assumed: the frozen row is a consequence of its two stated
inputs. -/
theorem auxSourceRow (Bs u L c n : ℕ) (hu : u ≤ 2 * L)
    (hL : L ≤ (ellN n + 2) ^ (c + 1)) :
    Bs * u ^ 2 ≤ 4 * Bs * L ^ 2 ∧
      4 * Bs * L ^ 2 ≤ 4 * Bs * (ellN n + 2) ^ dsExp c := by
  constructor
  · have h1 : u ^ 2 ≤ (2 * L) ^ 2 := Nat.pow_le_pow_left hu 2
    have h2 : (2 * L) ^ 2 = 4 * L ^ 2 := by ring
    calc Bs * u ^ 2 ≤ Bs * (4 * L ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * Bs * L ^ 2 := by ring
  · have h1 : L ^ 2 ≤ ((ellN n + 2) ^ (c + 1)) ^ 2 := Nat.pow_le_pow_left hL 2
    have h2 : ((ellN n + 2) ^ (c + 1)) ^ 2 = (ellN n + 2) ^ dsExp c := by
      rw [dsExp, ← pow_mul]
      ring_nf
    exact Nat.mul_le_mul_left _ (by omega)

/-- **Display 7 -- `eq:aux-source-s-ecut`**
(`06-parameter-schedule.tex`, label line 1892, display lines 1890--1893):
`h_s <= 4 B_s (lambda+2)^{d_s} <= 2^{lambda-2}`.

`06:1888--1890` fixes the evaluation index and it is the content of this
statement: "When `lambda >= R(c)+2`, persistence is evaluated at the exact
ordinary index `r = lambda`, not at `lambda-2`".  Accordingly the persistence
input is the **banked** `EnvelopeRealization.ECutPred` at the compiler's own
inserted pair `(4B_s, d_s)` of `06:1883--1886`, read at `r = l(n)`, and not at a
shifted index -- the very confusion `lem:shifted-pcut-absorption` exists to keep
apart.

**Proved** from that persistence row and the two inputs of display 6. -/
theorem auxSourceEcutRow (Bs u L c n : ℕ) (hu : u ≤ 2 * L)
    (hL : L ≤ (ellN n + 2) ^ (c + 1))
    (hE : EnvelopeRealization.ECutPred (4 * Bs) (dsExp c) (ellN n)) :
    Bs * u ^ 2 ≤ 2 ^ (ellN n - 2) := by
  obtain ⟨h1, h2⟩ := auxSourceRow Bs u L c n hu hL
  obtain ⟨-, hcut, -⟩ := hE
  calc Bs * u ^ 2 ≤ 4 * Bs * L ^ 2 := h1
    _ ≤ 4 * Bs * (ellN n + 2) ^ dsExp c := h2
    _ ≤ 2 ^ (ellN n - 2) := hcut

/-- **`y = 2^{2^{lambda-2}}`** -- `06:1894`, "Set `y = 2^{2^{lambda-2}}`", at
`lambda = l(n)` of `06:1864`, over the banked `IterationAssembly.ellN`. -/
def auxY (n : ℕ) : ℕ := 2 ^ 2 ^ (ellN n - 2)

/-- **Aux Y1 (`06:1901`'s "The same guard gives `y >= 16`").**

The guard is `lambda >= 4`, which `06:1895--1896` gets from the eligibility step;
here it is the hypothesis, and the conclusion is the frozen one.  General. -/
theorem auxY_ge_sixteen {n : ℕ} (h : 4 ≤ ellN n) : 16 ≤ auxY n := by
  have h1 : (2 : ℕ) ^ 2 ≤ 2 ^ (ellN n - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ 4 ≤ 2 ^ 2 ^ (ellN n - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [auxY] using h2

/-! ### Displays 8 and 9 are not stated in this module

`eq:aux-source-s-le-n` (`06:1903--1906`) and `eq:aux-source-s-minus-three`
(`06:1908--1911`) are owned by
`src/EthInapproximability/ParameterizedNP/AuxSourceDerivations.lean`, downstream
of the `B_s` pin `MechanicalCompilerResidue.bsSched`, for the import-direction
reason recorded in "The auxiliary-source chain moves downstream" above.  The
free-`sv` variants that stood here are deleted, not withdrawn: the downstream
statements are strictly stronger, with `s` pinned to the banked
`ParameterSchedule.sScale` at `bsSched` and `ParameterSchedule.uAux`, and with
both previously assumed links (`06:1894` and `06:1895--1899`) proved. -/

/-! ## Section 6  Displays 10--16 -- the dimensions of one level

`sec:one-level-dimensions` (`06:2110--2273`).  `06:2122--2123` fixes the scope
of the whole subsection and it is preserved below: "The dimension statement
concerns the exact indexed family stored in `Pi`, not on balancedness alone",
repeated by the reading warning at `06:2251--2257`. -/

/-- **Display 10 -- `eq:literal-balanced-family-size`**
(`06-parameter-schedule.tex`, label line 2130, display lines 2125--2131):
`ceil(log_2 N_2) <= ceil(log_2 B_bal(q_2, t_2, |Rows(M_1)|))`, "For a family
inside the envelope `eq:balanced-family-envelope`".

The frozen envelope condition is `0 < N_2 <= B_bal` (`06:2030--2034`); only its
**upper** half is taken, which makes this statement strictly more general than
the frozen one and never stronger.  The frozen `ceil(log_2 .)` is `Nat.clog 2`,
the schedule's standing reading. -/
theorem literalBalancedFamilySize {N2 q2 t2 m1 : ℕ} (hle : N2 ≤ bBal q2 t2 m1) :
    Nat.clog 2 N2 ≤ Nat.clog 2 (bBal q2 t2 m1) :=
  Nat.clog_mono_right _ hle

/-- **Display 11 -- `eq:N2-explicit-code-envelope`**
(`06-parameter-schedule.tex`, label line 2143, display lines 2137--2144):

```
 bl(N_2) <= 1 + t_2(1 + max{bl(q_2), bl(1000) + bl(m_1) + 2 bl(t_2), 1}),
```

with `m_1 = |Rows(M_1)|` fixed at `06:2134--2136`.  This is
`eq:balanced-family-binary-length-envelope` (`02-mechanical-contract.tex`, label
line 300, display lines 294--300) read at the level's own triple, and
`06:2145--2147` records what it is for: "This exact right-hand side is traversed
in the `L+2` pass and receives a checked `SingleExp` tag of degree eight.  In
particular, there is no primitive degree-six bound for `N_2`."

**Proved** from the three binary-length rules `02:301--303` names -- product,
maximum, and fixed square -- taken as local steps on the inline
`Nat.clog 2 (x + 1)` of `02:282`, since `bl` has no definition on this route.
The frozen positivity side condition of `02:179` is not consumed and is
therefore not assumed. -/
theorem n2ExplicitCodeEnvelope {N2 q2 t2 m1 : ℕ} (hle : N2 ≤ bBal q2 t2 m1) :
    Nat.clog 2 (N2 + 1) ≤
      1 + t2 * (1 + max (max (Nat.clog 2 (q2 + 1))
        (Nat.clog 2 (1000 + 1) + Nat.clog 2 (m1 + 1) + 2 * Nat.clog 2 (t2 + 1))) 1) := by
  -- `02:301--303`'s monotonicity, product, maximum, doubling and fixed-power
  -- steps, stated locally on `bl(x) = clog2N(x+1)` (`02:282`)
  have hmono : ∀ a b : ℕ, a ≤ b → Nat.clog 2 (a + 1) ≤ Nat.clog 2 (b + 1) :=
    fun _ _ h => Nat.clog_mono_right _ (by omega)
  have hmul : ∀ a b : ℕ,
      Nat.clog 2 (a * b + 1) ≤ Nat.clog 2 (a + 1) + Nat.clog 2 (b + 1) := by
    intro a b
    have ha : a + 1 ≤ 2 ^ Nat.clog 2 (a + 1) := Nat.le_pow_clog (by norm_num) _
    have hb : b + 1 ≤ 2 ^ Nat.clog 2 (b + 1) := Nat.le_pow_clog (by norm_num) _
    have hprod : (a + 1) * (b + 1)
        ≤ 2 ^ Nat.clog 2 (a + 1) * 2 ^ Nat.clog 2 (b + 1) := Nat.mul_le_mul ha hb
    have hstep : a * b + 1 ≤ (a + 1) * (b + 1) := by
      have hexp : (a + 1) * (b + 1) = a * b + (a + b + 1) := by ring
      rw [hexp]
      exact Nat.add_le_add_left (by omega) _
    have hle2 : a * b + 1 ≤ 2 ^ (Nat.clog 2 (a + 1) + Nat.clog 2 (b + 1)) := by
      rw [pow_add]
      exact le_trans hstep hprod
    exact Nat.clog_le_of_le_pow hle2
  have hmax : ∀ a b : ℕ, Nat.clog 2 (max a b + 1)
      ≤ max (Nat.clog 2 (a + 1)) (Nat.clog 2 (b + 1)) := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_max_left _ _
  have hdouble : ∀ x : ℕ, Nat.clog 2 (2 * x + 1) ≤ 1 + Nat.clog 2 (x + 1) := by
    intro x
    have hx : x + 1 ≤ 2 ^ Nat.clog 2 (x + 1) := Nat.le_pow_clog (by norm_num) _
    have hle2 : 2 * x + 1 ≤ 2 ^ (1 + Nat.clog 2 (x + 1)) := by
      rw [pow_add, pow_one]
      omega
    exact Nat.clog_le_of_le_pow hle2
  have hpowRule : ∀ a k : ℕ,
      Nat.clog 2 (a ^ k + 1) ≤ 1 + k * Nat.clog 2 (a + 1) := by
    intro a k
    induction k with
    | zero =>
        have h1 : Nat.clog 2 2 ≤ 1 := Nat.clog_le_of_le_pow (by norm_num)
        simpa using h1
    | succ k ih =>
        have hstep : Nat.clog 2 (a ^ (k + 1) + 1)
            ≤ Nat.clog 2 (a ^ k + 1) + Nat.clog 2 (a + 1) := by
          rw [pow_succ]
          exact hmul _ _
        have hnext : Nat.clog 2 (a ^ k + 1) + Nat.clog 2 (a + 1)
            ≤ 1 + k * Nat.clog 2 (a + 1) + Nat.clog 2 (a + 1) :=
          Nat.add_le_add_right ih _
        calc Nat.clog 2 (a ^ (k + 1) + 1)
            ≤ Nat.clog 2 (a ^ k + 1) + Nat.clog 2 (a + 1) := hstep
          _ ≤ 1 + k * Nat.clog 2 (a + 1) + Nat.clog 2 (a + 1) := hnext
          _ = 1 + (k + 1) * Nat.clog 2 (a + 1) := by ring
  set M := max (max (Nat.clog 2 (q2 + 1))
    (Nat.clog 2 (1000 + 1) + Nat.clog 2 (m1 + 1) + 2 * Nat.clog 2 (t2 + 1))) 1 with hM
  have hmid : Nat.clog 2 (1000 * m1 * t2 ^ 2 + 1)
      ≤ Nat.clog 2 (1000 + 1) + Nat.clog 2 (m1 + 1) + 2 * Nat.clog 2 (t2 + 1) := by
    have hsq : t2 ^ 2 = t2 * t2 := by ring
    have h1 : Nat.clog 2 (1000 * m1 * t2 ^ 2 + 1)
        ≤ Nat.clog 2 (1000 * m1 + 1) + Nat.clog 2 (t2 ^ 2 + 1) := hmul _ _
    have h2 : Nat.clog 2 (1000 * m1 + 1)
        ≤ Nat.clog 2 (1000 + 1) + Nat.clog 2 (m1 + 1) := hmul _ _
    have h3 : Nat.clog 2 (t2 ^ 2 + 1)
        ≤ Nat.clog 2 (t2 + 1) + Nat.clog 2 (t2 + 1) := by
      rw [hsq]; exact hmul _ _
    omega
  have hmidM : Nat.clog 2 (1000 + 1) + Nat.clog 2 (m1 + 1)
      + 2 * Nat.clog 2 (t2 + 1) ≤ M := by
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have htwo : Nat.clog 2 (2 + 1) ≤ M := by
    have h2 : Nat.clog 2 (2 + 1) ≤ Nat.clog 2 (1000 + 1) := hmono _ _ (by norm_num)
    omega
  have hX : Nat.clog 2 (xBal q2 t2 m1 + 1) ≤ M := by
    have hstep1 : Nat.clog 2 (xBal q2 t2 m1 + 1)
        ≤ max (Nat.clog 2 (max q2 (1000 * m1 * t2 ^ 2) + 1))
          (Nat.clog 2 (2 + 1)) := by
      rw [xBal]; exact hmax _ _
    have hstep2 : Nat.clog 2 (max q2 (1000 * m1 * t2 ^ 2) + 1)
        ≤ max (Nat.clog 2 (q2 + 1))
          (Nat.clog 2 (1000 * m1 * t2 ^ 2 + 1)) := hmax _ _
    have hq : Nat.clog 2 (q2 + 1) ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    have hA : Nat.clog 2 (1000 * m1 * t2 ^ 2 + 1) ≤ M := le_trans hmid hmidM
    have : max (Nat.clog 2 (q2 + 1)) (Nat.clog 2 (1000 * m1 * t2 ^ 2 + 1)) ≤ M :=
      max_le hq hA
    exact le_trans hstep1 (max_le (le_trans hstep2 this) htwo)
  have hbase : Nat.clog 2 (2 * xBal q2 t2 m1 + 1) ≤ 1 + M :=
    le_trans (hdouble _) (by omega)
  have hpow : Nat.clog 2 (bBal q2 t2 m1 + 1) ≤ 1 + t2 * (1 + M) := by
    have h := hpowRule (2 * xBal q2 t2 m1) t2
    have hmulle : t2 * Nat.clog 2 (2 * xBal q2 t2 m1 + 1) ≤ t2 * (1 + M) :=
      Nat.mul_le_mul_left _ hbase
    have hb : bBal q2 t2 m1 = (2 * xBal q2 t2 m1) ^ t2 := rfl
    rw [hb]
    omega
  exact le_trans (hmono _ _ hle) hpow

/-- **`P_dim = (t_2 + s(q_1+s) + 1) Z`** -- `06:2188--2191`, the driver every
expanded dimension root is collected against.

The multiplicity factor is the **banked** `SizePropagation.dimMultiplicity`,
consumed by pin, whose non-additive shape is already refuted in the kernel by
`SizePropagation.dimMultiplicity_is_not_additive`. -/
def pDim (t2 s q1 Z : ℕ) : ℕ := SizePropagation.dimMultiplicity t2 s q1 * Z

/-- **Aux P1 (`P_dim` is exactly the driver of the banked raw-side majorant).**
`zbar_N = C_dim P_dim`, so the banked `SizePropagation.rawSideMajorant` and this
reification are the same expression written in the two places the frozen source
writes it (`06:2188--2191` and `exp:E-14-raw`, `11:846--851`).  General. -/
theorem rawSideMajorant_eq_cdim_mul_pDim (Cdim t2 s q1 Z : ℕ) :
    SizePropagation.rawSideMajorant Cdim t2 s q1 Z = Cdim * pDim t2 s q1 Z := by
  rw [SizePropagation.rawSideMajorant, pDim, mul_assoc]

/-- **Display 12 -- `eq:N2-dimension-code-bound`**
(`06-parameter-schedule.tex`, label line 2163, display lines 2160--2164):
`bl(N_2) <= 1 + 23 t_2 Z <= 23(t_2 + s(q_1+s)+1) Z`.

`06:2165--2166`: "The dimension ledger therefore uses coefficient `23`, not
`8`, for its `N_2` base."  The literal `23` is the frozen one and is not
recomputed; the first inequality is the traversal's output (`06:2149--2159`,
`PARAM-001`) and is the hypothesis, while the second -- the step that absorbs
the leading `1` into the multiplicity -- is **proved** here at the frozen floor
`Z >= 1` of the driver's own definition (`06:2116--2121`, the outer `max{1,
...}`).  The multiplicity is the banked `SizePropagation.dimMultiplicity`. -/
theorem n2DimensionCodeBound {N2 t2 s q1 Z : ℕ} (hZ : 1 ≤ Z)
    (h : Nat.clog 2 (N2 + 1) ≤ 1 + 23 * t2 * Z) :
    Nat.clog 2 (N2 + 1) ≤ 23 * SizePropagation.dimMultiplicity t2 s q1 * Z := by
  have hexpand : 23 * SizePropagation.dimMultiplicity t2 s q1 * Z
      = 23 * t2 * Z + 23 * (s * (q1 + s) + 1) * Z := by
    rw [SizePropagation.dimMultiplicity]; ring
  have hslack : 1 ≤ 23 * (s * (q1 + s) + 1) * Z := by
    have h1 : 1 ≤ s * (q1 + s) + 1 := Nat.le_add_left _ _
    calc (1 : ℕ) = 1 * 1 * 1 := by norm_num
      _ ≤ 23 * (s * (q1 + s) + 1) * Z :=
          Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) h1) hZ
  omega

/-- **Display 13 -- `eq:dimension-coefficient-roots`**
(`06-parameter-schedule.tex`, label line 2180, display lines 2168--2181):
`U_dim` expanded "in the displayed construction order".

The nineteen entries are kept in the frozen order and grouping:
`|Rows(M_1)|, |Cols(M_1)|`; `|Rows(M_2)|, |Cols(M_2)|`;
`|Rows(M_3)|, |Cols(M_3)|`; `|Rows(B)|, |Cols(B)|`, `w_0, w_Sigma, w_D, u_0,
u_temp`; `u_V, u_B`, `|Rows(A)|, |Cols(A)|, |Rows(N)|, |Cols(N)|`.

`06:2182--2185` names the three groups: "The first six and the two raw Stage--4
carriers are the exact equations of `sec:one-level`; the next seven are the
multiplicities displayed in the definition of the protected duplicate; and the
last four are the corresponding disjoint-sum and transpose equations."  Those
defining equations are the construction's own and are not restated here: this
declaration is the *expansion list* the traversal consumes, nothing more. -/
def dimensionRoots (rM1 cM1 rM2 cM2 rM3 cM3 rB cB w0 wSigma wD u0 utemp uV uB
    rA cA rN cN : ℕ) : List ℕ :=
  [rM1, cM1, rM2, cM2, rM3, cM3, rB, cB, w0, wSigma, wD, u0, utemp, uV, uB,
    rA, cA, rN, cN]

/-- **Aux D1 (`06:2201`: "a literal maximum over nineteen named, computed
rows").**  The expansion list has exactly nineteen entries.  General. -/
theorem dimensionRoots_length (rM1 cM1 rM2 cM2 rM3 cM3 rB cB w0 wSigma wD u0
    utemp uV uB rA cA rN cN : ℕ) :
    (dimensionRoots rM1 cM1 rM2 cM2 rM3 cM3 rB cB w0 wSigma wD u0 utemp uV uB
      rA cA rN cN).length = 19 := rfl

/-- **Display 14 -- the checked derivation of one dimension row**
(`06-parameter-schedule.tex:2192--2194`): "For each expanded root `v`, this
finite integer traversal returns `(v, K_v, Q_v)`, where `Q_v` is a checked
derivation of `ceil(log_2 v) <= K_v P_dim`."

The row predicate only, in the frozen shape.  The traversal that *produces* the
row is `PARAM-001` and is not modelled, exactly as for
`CoefficientTraversal.RowChecked`. -/
def DimRowChecked (Pdim v K : ℕ) : Prop := Nat.clog 2 v ≤ K * Pdim

/-- **Display 14 -- `eq:Cdim-literal-producer`**
(`06-parameter-schedule.tex`, label line 2199, display lines 2195--2200):
`C_dim = max({1} u {K_v : v in U_dim})`.

`C_dim` is the **banked** `SizePropagation.cdimLiteral` and is not restated;
what lands here is the display's *content* -- that the literal maximum dominates
every checked row of the expansion list, so every expanded root's ceiling
logarithm is at most `C_dim P_dim`.  `06:2201--2203` fixes what the constant is
not: "it is neither a big-`O` witness nor an extra configuration input".

**Proved** through the banked `SizePropagation.le_maxFrom`. -/
theorem cdimLiteral_dominates_rows (rows : List (ℕ × ℕ)) (Pdim : ℕ)
    (h : ∀ p ∈ rows, DimRowChecked Pdim p.1 p.2) :
    ∀ p ∈ rows,
      Nat.clog 2 p.1 ≤ SizePropagation.cdimLiteral (rows.map Prod.snd) * Pdim := by
  intro p hp
  have hrow := h p hp
  have hK : p.2 ≤ SizePropagation.cdimLiteral (rows.map Prod.snd) :=
    SizePropagation.le_maxFrom (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact le_trans hrow (Nat.mul_le_mul_right _ hK)

/-- **Display 15 -- `eq:raw-dimension`**
(`06-parameter-schedule.tex`, label line 2224, display lines 2213--2225):

```
 z_raw := max{log_2|Rows(A_raw)|, log_2|Cols(A_raw)|}
        <= max{z_raw, z_A, z_N} <= C_dim (t_2 + s(q_1+s)+1) Z.
```

`06:2205--2210` fixes the two inputs: `A_raw = B` is the unprotected Stage-4
matrix, `z_A = max{ceil(log_2|Rows(A)|), ceil(log_2|Cols(A)|)}`, and
`z_N = z_A`, "the second equality following from transposition".  That equality
is preserved **definitionally** here -- `z_N` is not a second binder -- so no
statement of this module can drift the transpose apart from its source.

The right-hand side is the banked `SizePropagation.rawSideMajorant`, consumed by
pin.  `06:2226--2228` records what the display buys: "Thus the protected
duplication and transpose are covered by the same produced integer coefficient,
rather than by an uninstantiated `O(z_raw)` constant." -/
theorem rawDimension (zraw zA Cdim t2 s q1 Z : ℕ)
    (hraw : zraw ≤ SizePropagation.rawSideMajorant Cdim t2 s q1 Z)
    (hA : zA ≤ SizePropagation.rawSideMajorant Cdim t2 s q1 Z) :
    zraw ≤ max (max zraw zA) zA ∧
      max (max zraw zA) zA ≤ SizePropagation.rawSideMajorant Cdim t2 s q1 Z :=
  ⟨le_trans (le_max_left zraw zA) (le_max_left _ _), max_le (max_le hraw hA) hA⟩

/-- **Display 16 -- `eq:one-level-log-size`**
(`06-parameter-schedule.tex`, label line 2248, display lines 2245--2249):

```
 max{log_2|Rows(R^+)|, log_2|Cols(R^+)|}
   = O(Q(log_2 q + z_N) + q z_N + log_2 Q).
```

The frozen `O(.)` is delivered here **at the explicit constant one**, which is
strictly stronger than the printed asymptotic statement and leaves no
uninstantiated witness: mechanical rule M2 forbids parking a desired bound in an
unnamed constant, and the statement-pole discipline forbids an existential whose
trivial witness would satisfy it (an `∃ C` version is satisfied by any large
`C` and would carry no content about *this* recurrence).

The two carriers are the **banked** `IterationAssembly.carrierRowNext` and
`.carrierColNext`, i.e. `eq:wrapper-dimensions` (`06:2238--2243`,
`|Rows(R^+)| = (q m_N)^Q`, `|Cols(R^+)| = Q n_N^q`), consumed by pin; both
interlace widths `q` and `Q` stay separate and in their frozen roles, the inner
one exponentiated in the row branch and multiplied in the column branch.

`z_N = max{ceil(log_2 m_N), ceil(log_2 n_N)}` is the level's own side exponent,
in the same `Nat.clog 2` reading the schedule uses everywhere. -/
theorem oneLevelLogSize (q Q mN nN : ℕ) :
    max (Nat.clog 2 (carrierRowNext q mN Q)) (Nat.clog 2 (carrierColNext Q nN q))
      ≤ Q * (Nat.clog 2 q + max (Nat.clog 2 mN) (Nat.clog 2 nN))
        + q * max (Nat.clog 2 mN) (Nat.clog 2 nN) + Nat.clog 2 Q := by
  set zN := max (Nat.clog 2 mN) (Nat.clog 2 nN) with hzN
  have hmul : ∀ a b : ℕ, Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
    intro a b
    have ha : a ≤ 2 ^ Nat.clog 2 a := Nat.le_pow_clog (by norm_num) _
    have hb : b ≤ 2 ^ Nat.clog 2 b := Nat.le_pow_clog (by norm_num) _
    have : a * b ≤ 2 ^ (Nat.clog 2 a + Nat.clog 2 b) := by
      rw [pow_add]; exact Nat.mul_le_mul ha hb
    exact Nat.clog_le_of_le_pow this
  have hpow : ∀ (a k : ℕ), Nat.clog 2 (a ^ k) ≤ k * Nat.clog 2 a := by
    intro a k
    have ha : a ≤ 2 ^ Nat.clog 2 a := Nat.le_pow_clog (by norm_num) _
    have : a ^ k ≤ 2 ^ (k * Nat.clog 2 a) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left ha k
    exact Nat.clog_le_of_le_pow this
  have hrow : Nat.clog 2 (carrierRowNext q mN Q) ≤ Q * (Nat.clog 2 q + zN) := by
    rw [carrierRowNext]
    refine le_trans (hpow (q * mN) Q) ?_
    refine Nat.mul_le_mul_left _ ?_
    refine le_trans (hmul q mN) ?_
    exact Nat.add_le_add_left (le_max_left _ _) _
  have hcol : Nat.clog 2 (carrierColNext Q nN q) ≤ Nat.clog 2 Q + q * zN := by
    rw [carrierColNext]
    refine le_trans (hmul Q (nN ^ q)) ?_
    refine Nat.add_le_add_left ?_ _
    refine le_trans (hpow nN q) ?_
    exact Nat.mul_le_mul_left _ (le_max_right _ _)
  exact max_le (by omega) (by omega)

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY probe: the dimension-row premise is
inhabited nondegenerately.**

The empty row list satisfies `DimRowChecked` vacuously, so the premise is
exhibited at a nonempty list whose single root has a positive ceiling logarithm
and whose recorded coefficient is not the floor `1` of
`eq:Cdim-literal-producer`.  The driver is the reified `P_dim` at the frozen
floor `Z >= 1` and at nondegenerate widths, never a numeral standing for it.

Labelled **BEYOND-PAPER AUDIT** because both the row `(v, K_v) = (4, 2)` and the
widths `(t_2, s, q_1, Z) = (2, 1, 6, 1)` are **ours**.  The rows of `U_dim` are
compiler output that `06:1628--1631` forbids a formalizer to supply
(`PARAM-001`), and the frozen source instantiates none of the four widths, so
this probe audits our *encoding* at a point the paper never visits.  It is
strictly weaker evidence than a paper application point and discharges no
canonical-inhabitation obligation. -/
theorem dimRow_premise_inhabited :
    ∃ rows : List (ℕ × ℕ), rows ≠ [] ∧
      (∀ p ∈ rows, 0 < Nat.clog 2 p.1) ∧
      (∀ p ∈ rows, DimRowChecked (pDim 2 1 6 1) p.1 p.2) := by
  refine ⟨[(4, 2)], by simp, ?_, ?_⟩
  · intro p hp
    have hp1 : p = (4, 2) := by simpa using hp
    subst hp1
    have hc : Nat.clog 2 4 = 2 := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4, Nat.clog_pow _ _ (by norm_num)]
    change 0 < Nat.clog 2 4
    omega
  · intro p hp
    have hp1 : p = (4, 2) := by simpa using hp
    subst hp1
    have hc : Nat.clog 2 4 = 2 := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4, Nat.clog_pow _ _ (by norm_num)]
    have hd : pDim 2 1 6 1 = 10 := by
      norm_num [pDim, SizePropagation.dimMultiplicity]
    change Nat.clog 2 4 ≤ 2 * pDim 2 1 6 1
    rw [hc, hd]
    norm_num

/-! ### Two deletions: the chain-consistency probe, and `ellN_at_241`

`auxSourceChain_hypotheses_consistent` stood here and is **deleted**.  It was
read at `lambda = 4`, `B_s = 1`, `u = 1`: the frozen `K1` block fixes `B_s = T^2`
with `T >= 64` (`02:815--819`) and `eq:s-choice` forces `u >= 3`
(`06:116--117`, the banked `ParameterSchedule.three_le_uAux`), so
`h_s = B_s u^2 >= 36864 > 2^15`, and `06:1891`'s persistence conclusion
`h_s <= 2^{lambda-2}` then forces `lambda >= 18`.  A point with `lambda = 4` is
therefore not merely beyond the paper but **unreachable**.

The replacement is `AuxSourceDerivations.auxSourceChain_hypotheses_consistent`,
which exhibits the same bundle at the pinned `B_s`, the evaluated `u` and `L`,
and a **closed-form** source size with `l(n) >= 18` where `06:1899` holds with
equality.  It keeps both the NON-FIDELITY and the BEYOND-PAPER labels, and the
canonical-inhabitation obligation `AUX-SOURCE-CANON-APP-001` stays registered
DEFERRED.

`ellN_at_241` (`l(241) = 4`) is **also deleted**, and that **reverses an order of
the previous gate** rather than repeating an earlier act.  The record, in order,
so the reversal is legible rather than silent:

* an earlier revision of `cc-t8c-r2` lane C deleted it; the `cc-t8c-r2` gate
  (finding **G4**) ruled that deletion outside the round's enumerated delta --
  it is banked at the round's baseline `ab37e4ab` and was not named by the r1
  verdict -- and ordered it **restored**, which the repair cycle did,
  byte-identically to the baseline;
* the `cc-t8c-r3` regate then established a fact neither the lane nor the earlier
  gate had: `IterationAssembly.envelope_fires_nondegenerate` (`:1393--1394`)
  already carries `ellN 241 = 4` as its **third conjunct**, proved there by
  essentially this proof.  `IterationAssembly` is in this module's import closure
  (via `MassRedistributionTail`) and is opened **whole-namespace** at `:324`
  above, so that conjunct is reachable here by projection.  `ellN 241 = 4`
  therefore stood in **three** places: here, there, and -- up to specialization
  at `lam := 4` -- in `AuxSourceDerivations.ellN_at_leastSourceSize`;
* the `cc-t8c-r3` gate ruled that the conjunct-level dedup rule **has no
  grandfather exception**, that this is grounds to revisit G4 rather than to
  register a pre-existing item, and ordered the declaration and its
  `tools/AxiomAudit.lean` row **deleted**.  That order is executed here.
  `AuxSourceDerivations.ellN_at_leastSourceSize`'s guard was tightened in the
  same change so that `lam = 4` is no longer in its range either.

**Nothing is lost and nothing is re-proved.**  Any site needing `l(241) = 4`
consumes `IterationAssembly.envelope_fires_nondegenerate.2.2.1`: the bundle is
the right-nested `ellN 1 = 3 and (depthB 1 = 512 and (ellN 241 = 4 and
(depthB 241 = 65536 and depthB 1 <> depthB 241)))`, so `.2.2.1` is exactly that
statement.  This module had **no** consumer of `ellN_at_241` once the probe above
went, and it has none tree-wide, so the deletion moves no proof term.  The
arithmetic is unchanged in the surviving copy: `241 + 16 = 257 > 256 = 2^{2^3}`
and `257 <= 2^{2^4}`. -/

end EthInapproximability.ParameterizedNP.ScheduleMajorantResidue
