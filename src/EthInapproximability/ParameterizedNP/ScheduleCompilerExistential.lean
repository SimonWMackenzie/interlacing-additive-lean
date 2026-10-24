import EthInapproximability.ParameterizedNP.EnvelopeRealization
import EthInapproximability.ParameterizedNP.MechanicalCompilerResidue
import EthInapproximability.ParameterizedNP.Section5Admissibility

/-!
# Parameterized NP route: the persistent-cutoff layer of the schedule-compiler existential

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchors (proof source).**  All references are to the
  **frozen** release named by `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization`.  Unqualified `06:mmm` citations are
  `sections/06-parameter-schedule.tex`; `02:mmm` is
  `sections/02-mechanical-contract.tex`; `05:mmm` is
  `sections/05-public-records.tex`.  Every anchor below was opened first-hand
  in that source this tranche; the reader artifact, the ledger, the crosswalk
  and every summary are navigation only.

  1. `eq:persistent-cutoffs` (label line 1810, display lines 1797--1811) with
     its scope sentence `06:1796` ("For positive integers `A, d`, and `e > d`,
     define") -- the three searches `ECut`, `PCut`, `DCut`, each printed as a
     `min{r >= 2 : ...}` over **two** conditions for `ECut` and `DCut` and one
     for `PCut`;
  2. the termination-and-persistence sentence `06:1812--1816`: "Each search
     terminates, and each predicate remains true for every larger `r`.  In
     `ECut`, the exponential doubles while the polynomial grows by at most a
     factor two; in `PCut`, the quotient power is nondecreasing; and in `DCut`,
     the exponential ratio is `2^{2r+1}`, which dominates the polynomial
     ratio."  (`06:1817` is blank and is deliberately excluded -- r0 finding 7.)
     All three clauses of the second sentence are the *proofs* the first
     sentence asserts, and this module discharges the `ECut` and `DCut` halves
     of both;
  3. the auxiliary source row `06:1861--1893`: the emission sentence
     `06:1861--1862` ("the compiler first emits one auxiliary source row that
     is not a candidate target"), `d_s = 2(c+1)` and
     `h_s = log_2 s = ceil(B_s u^2) = B_s u^2` (`06:1864--1865`, with `06:1867`
     recording that the last equality is exact), the derived `u <= 2L`
     (`06:1867--1876`), the normalized row `eq:aux-source-s-normalized`
     (label 1881, display 1878--1882), the inserted argument pair
     `(4 B_s, d_s)` with root `r_s = ECut(4 B_s, d_s)` (`06:1883--1887`), and
     the discharge `eq:aux-source-s-ecut` (label 1892, display 1890--1893) at
     the frozen guard "When `lambda >= R(c)+2`" (`06:1888--1889`);
  4. `eq:R-exact` (label 1951, display 1944--1952), consumed **by pin** from
     `EnvelopeRealization.CutoffEmission.R`.  `eq:nstep` (label 1956, display
     1955) and the cutoff sentence `06:1960--1962` ("If `n >= n_step(c)`, then
     `l(n) >= R(c)+2 >= 4`", whose first word is on `06:1960` and whose closing
     comparison is on `06:1962`) are named here because they are the anchors of
     the **deferred** declaration described under "What this round split off";
     **no declaration in this module consumes either of them**, and
     `CutoffEmission.nStep` does not occur below;
  5. `thm:eff-ledger` (`02:569--650`), specifically item (b)'s
     `R(c) = max({2} u ExecutedRoots(Cert_c))`, `n_step(c) = 2^{2^{R(c)+2}}`
     and the `ExecutedRoots` sentence `02:589--591`, together with the
     `Searches_c` field of `def:effective-schedule-certificate`
     (`02:485--487`), the storage sentence `02:341--342` ("Every executed
     search stores its nonemptiness, tested endpoint, and termination proof"),
     the C5/C6 emission paragraph `02:1016--1027` ("run only these
     compiler-executed, `c`-dependent least searches
     `eq:persistent-cutoffs`, and store each argument tuple, least root,
     successful endpoint comparisons, and persistence-rule tag"), and the
     runtime sentence `02:1414` ("Both `J_c` and `B_c` are finite by the
     executed-search termination proof") -- which is why the termination
     proofs below are load-bearing for item (b) and not decoration;
  6. `eq:s-choice` (`06:109--121`) for `A_pre`, `u`, `s` and `B_s`, together
     with the public-scale displays `06:47--54` (`B_pub = max{D, Y}` and
     `z_R = max{clog_2 |Rows(R)|, clog_2 |Cols(R)|}`), the configuration
     sentence `06:56--62` ("Read the following positive integers from the
     universal configuration field of `Pi`: `C_0, c_seed, A_wrap, B_s, c_b,
     C_in`"), the accessor roster `05:126--141` ("Their defining displays are
     ... The inequalities ... are admissibility checks, not definitions of
     these accessors"), and the compiler's own K1 choice `B_s = T^2`
     (`02:815--819`), "performed once and then compiled into every certificate
     machine" (`02:812--813`; `02:814` is the `\begin{enumerate}` that opens the
     `K1`--`K3` list and carries none of the sentence -- r1 finding Sol-1).

* **Reader counterpart: none, and the reason is the reader's own content.**
  The 41-page reader artifact prints no `ECut`, no `DCut`, no `R(c)`, no
  `h_s`, no `d_s` and no auxiliary source row.  Its only neighbouring material
  is in `reader-facing/sections/C-effectivity-details.tex`: the phrase "least
  cutoffs for persistent inequalities", which **crosses lines `83--84`**
  (r0 finding 6), names all three searches in one breath and is **already
  assigned** to `EnvelopeRealization.pCut` (interval `:82--84`); and lines
  `86--88`, "Because the graph is finite and every search has an explicit
  terminating comparison, this is a total algorithm", **already assigned** to
  `EnvelopeRealization.pCut_nonempty`.  Both intervals were opened first-hand
  this tranche.  Re-citing either would be the double assignment the
  reader-counterpart rule forbids, and the reader has no third sentence about
  the searches, so **every declaration below claims no reader item**.  The
  sentence naming `thm:paper-effective-level` occupies
  `C-effectivity-details.tex:80--81` (`:79` is blank -- r0 finding 5) and is
  prose, so it may not be cited as a statement either.

## What this module is

It is the first landed instalment of `PARAM-001`'s **compiler existential**,
and it takes the one piece of that existential that is *mathematics* rather
than unbuilt machinery: the frozen assertion `06:1812--1816` that each of the
three persistent integer searches terminates and that each predicate persists
upward.  Before this tranche exactly one third of that sentence was proved --
`PCut`, by the banked `EnvelopeRealization.pCut_nonempty` and
`.pCutPred_persist` -- and `EnvelopeRealization`'s own GAP register recorded
the other two thirds as open ("**`ECut` and `DCut` termination is not
proved**", its GAP-EXPOSED 3).  Both are proved here, from the paper's own two
reasons, and the `ECut` half is then run through the paper's own application
site: the auxiliary source row of `06:1861--1893`.

The gain is not cosmetic.  `02:1414` makes the executed-search termination
proof the reason the compiler's own step count `J_c` and bit width `B_c` are
finite, and `eq:R-exact` reads the three roots off searches that must actually
return.  A `sInf` over an empty set returns `0` in Lean, so before this round
an `ECut` or `DCut` row was a *number* without a *predicate*, and every
consumer had to route around it.

## What this round split off, and why

One declaration that stood here at the previous pin is **deleted and deferred**,
deliberately and by scope decision, not repaired: `auxSourceECutRow_at_cutoff`,
which restated `auxSourceECutRow` under the frozen cutoff hypothesis
`n >= n_step(c)` of `06:1960--1962` in place of the guard `lambda >= R(c)+2` of
`06:1888--1889`.

Its mathematics, its guard direction and its evaluation index were all judged
correct.  What it lacked was a **legal nondegenerate inhabitant of its own
premise bundle**.  That bundle needs a `Section5Admissibility.ScheduleContext`
together with an emission `E(c)` containing the paper's emitted pair, and the
paper's own such context is the materialized schedule of `06:859--887`, which
requires `LevelStep` -- the route-ledger row `S5-LEVEL-STEP`, **OPEN**.  The
only bundle inhabitant available at this pin was a synthetic one, built over a
labelled BEYOND-PAPER context and a truncated emission, and a NON-FIDELITY probe
is not a legal non-vacuity witness.  A declaration whose sole demonstration of
satisfiability is a probe that disclaims legality is a declaration whose premise
bundle is unwitnessed, so it does not land here.

It is therefore carried to the **`S5-LEVEL-STEP` arc** and is reinstated when the
materialized schedule lands, at which point the same statement acquires the
paper's own context and the paper's own `E(c)`.  Nothing about it is lost: it was
one application of `auxSourceECutRow` (which **does** land, at the paper's own
frozen guard) composed with the banked `EnvelopeRealization.cutoff_eligibility`.
Its sole consumer -- the labelled NON-FIDELITY audit of that bundle -- goes with
it, for the same reason and in the same round.

This deferral is registered as the OPEN obligation
`PARAM-COMPILER-CUTOFF-ROW-AT-NSTEP`.  It depends on `S5-LEVEL-STEP` and, for
the materialized schedule, `S5-EXT-CALL-THREE`; both prerequisites are OPEN.

## What this module is deliberately not

**It is not `thm:eff-ledger`, and no declaration below occupies any slot of
its quantifier prefix `02:630--649`.**  The five existential witnesses
`K_*`, `Cert`, `A_cert`, `R`, `n_step` and the two checked predicates
`SchemaChecked`, `NumChecked` are untouched:

* `K_*` is the banked `PublicRecords.LevelConfig` and is not re-declared;
* `Cert` is the banked `MechanicalCompilerResidue.Cert`, whose canonical
  inhabitant `Compile(c)` (`02:905--1120`) stays deferred under
  `MECHANICAL-COMPILER-RESIDUE-001`, and nothing below inhabits it;
* `R` is the banked `EnvelopeRealization.CutoffEmission.R`, consumed by pin and
  **not** restated -- in particular this module declares **no** second
  reification of `eq:R-exact`, and no `ExecutedRoots` accessor, for the reason
  in GAP register item 2.  `n_step` is the banked `.nStep`; after the split it
  is **not consumed by any declaration here at all**, because its only two
  consumers were the deferred declaration and the deferred declaration's audit;
* `A_cert`, `SchemaChecked` and `NumChecked` have **no declaration here and no
  axiom here**.  They are named in the closing census as owed.

**It reintroduces no withdrawn machinery.**  No expression graph is evaluated,
no node language is declared, no coefficient-pass evaluator is rebuilt and no
29-row tail registry is transcribed.  The only certificate-side objects
constructed are inhabitants of the banked `MechanicalCompilerResidue.SearchRow`
record, which is *data plus its three stored proofs* and nothing else.

## DEFINED-vs-FREE

Every symbol was classified against the frozen source before it was written.

* **DEFINED, consumed by pin, never re-reified:** `ECutPred`, `DCutPred`,
  `eCut`, `pCut`, `dCut` (`EnvelopeRealization`, at
  `eq:persistent-cutoffs`); `PCutPred` (`PilotPCut`); `R(c)`, `n_step(c)`,
  `CutoffEmission` (`EnvelopeRealization`, at `eq:R-exact`/`eq:nstep`);
  `l(n)` and `E_c(n)` (`IterationAssembly.ellN`, `.envE`); `L = clog_2 A_pre`
  and its sandwich (`EnvelopeRealization.normalizedL`, `.four_le_normalizedL`,
  `.lSandwich_upper`); `A_pre`, `u` and `s` (`ParameterSchedule.Apre`,
  `.uAux`, `.sScale`); **`d_s = 2(c+1)`
  (`ScheduleMajorantResidue.dsExp`, `06:1864`)**; the two frozen displays of
  the auxiliary source row (`ScheduleMajorantResidue.auxSourceRow` and
  `.auxSourceEcutRow`, `eq:aux-source-s-normalized` and
  `eq:aux-source-s-ecut`) and the exact ceiling identity
  (`.hsAux_eq`, `06:1865--1867`); the **public accessors** `B_pub`, `z_R`,
  `clog_2(|E|+2)`, `A_pre`, `u`, `s` evaluated at a schedule context
  (`Section5Admissibility.BpubOf`, `.zROf`, `.clEOf`, `.ApreOf`, `.uAuxOf`,
  `.sOf`, over `.ScheduleContext`), which `05:126--141` classifies as
  accessors with defining displays and `06:47--54` displays; `B_s = T^2`
  (`MechanicalCompilerResidue.bsSched`, `02:815--819`); the elementary
  `M^2 + 2M + 4 <= 2^M` of `02:892` (`IterationAssembly.sq_le_two_pow`); the
  executed-search record type (`MechanicalCompilerResidue.SearchRow`) and the
  cutoff class tag (`.CutKind`).

  **r0 finding 2, corrected.**  The r0 text of this block asserted that no
  banked reification of `d_s` existed.  That was **false**:
  `ScheduleMajorantResidue.dsExp` carries the identical body at the identical
  frozen display and is transitively in scope through
  `MechanicalCompilerResidue`.  The local duplicate has been deleted and every
  consumer repointed to the banked definition by pin.
* **DEFINED and reified here, citing its own defining display:** `h_s`
  (`hsOf`), `= log_2 s` at `06:1865`, exposed as `Nat.log 2` of the banked
  `Section5Admissibility.sOf` (itself `ParameterSchedule.sScale` at the
  context's own `B_s` and `u`), with its product form `B_s u^2` obtained from
  the banked `ScheduleMajorantResidue.hsAux_eq` rather than selected; and the
  compiler's emitted argument pair `(4 B_s, d_s)` of `06:1884`
  (`auxSourceECutArg`), whose two components are the pinned `bsSched` and the
  banked `dsExp`.  No numeral is assigned to any factor of either.
* **GENUINELY FREE, at the anchor that leaves them free:** the search
  arguments `A`, `d`, `e` -- `06:1796` defines the three searches for
  arbitrary positive integers with `e > d`, and the compiler supplies them
  through `E(c)`, `P(c)`, `D(c)` (`06:1856--1860`); the incoming exponent `c`
  and the source size `n` (both on `MechanicalCompilerResidue`'s own free
  list); the index `r` at which a predicate is tested; and the purely
  arithmetic binders `m`, `k`, `P` of the ratio and witness lemmas, which name
  no schedule quantity at all.
* **`A_pre` is DEFINED, and the r1 text of this block misclassified it (r1
  finding Sol-2, corrected).**  `A_pre` is fixed by the first line of
  `eq:s-choice` -- the display `06:111--115`,
  `A_pre = max{16, b_out, B_pub, z_R, clog_2(|E|+2)}` -- so it is **not** a
  quantity the frozen source leaves free anywhere, and the r1 wording, which
  listed it under GENUINELY FREE because `06:1868--1869` mentions only
  `A_pre >= 16`, read a *use site* as a definition.  That is the use-as-
  definition error, and it is withdrawn.  The Lean is unaffected, because the
  Lean never treated `A_pre` as a schedule input: `uAux_le_two_clog` is a
  **general arithmetic lemma** whose binder `Apreval` is a bare natural naming
  no schedule quantity -- exactly like `m`, `k`, `P` above -- and every
  declaration that needs the schedule's `A_pre` obtains it by **evaluating
  `06:111--115`** through the banked `Section5Admissibility.ApreOf` at a
  `ScheduleContext` (`uAux_le_two_normalizedL`, and every consumer downstream
  of it).  The correct classification is therefore: `A_pre` **SOURCE-DEFINED at
  `06:111--115`, pinned through `ApreOf`**; the general lemma's `Apreval` is a
  free natural of an arithmetic statement, not `A_pre`.

**No source-defined quantity enters any statement below as a free binder.**
In particular the four public inputs `b_out`, `B_pub`, `z_R`,
`clog_2(|E|+2)` -- which `05:126--141` classifies as accessors with defining
displays and `06:47--54` defines -- are **never** free binders here: every
declaration that needs them takes a `Section5Admissibility.ScheduleContext`
and evaluates them through `BpubOf`, `zROf`, `clEOf` and `ApreOf`, and
`b_out` is read as the public-record field `C.P.bout`.  The banked
`EnvelopeRealization.lSandwich_upper`, `.normalizedL` and
`.four_le_normalizedL` are still consumed **at their banked four-binder
signature**, applied at those evaluated arguments; nothing is
re-parameterized, so no banked interface is broken.

This module declares **no structure**, so it contributes no premise bundle and
no field standing in for a binder.

## Mechanical-rules compliance (Section 2, frozen)

* `M1`/`M2`/`M4`: every statement below is an inequality between naturals or a
  field equation of a data record.  No declaration has a `PromiseCase`
  argument, a protocol, or a transcript in scope; `02:1019--1021` calls these
  searches "`c`-dependent" and `02:1022--1024` explicitly separates them from
  the candidate-dependent symbolic ones, so no candidate context occurs.
* `M3`: nothing stores a derived telescope.  `R(c)` and `n_step(c)` are read
  from the banked emission; the three search rows *compute* their returned
  integer rather than carrying it as an independent field; `hsOf` computes
  `log_2 s` from the banked `s` rather than storing it.
* `M5`/`M8`: neither interlace width `q` nor `Q` occurs at all.
* `M7`: the one nonemptiness fact used is proved, not assumed -- that is the
  whole content of `eCut_nonempty` and `dCut_nonempty`.
* `M10`: no cardinality is introduced.

## GAP register

1. **The compiler's own run is not built.**  The canonical inhabitant of
   `MechanicalCompilerResidue.Cert` is `Compile(c)`; it stays deferred under
   `MECHANICAL-COMPILER-RESIDUE-001`, and nothing below inhabits it.  What is
   canonically inhabited is the *search-record* type at the *paper's own
   emitted argument*: `06:1883--1887` inserts `(4 B_s, d_s)` into `E(c)` and
   names its root `r_s = ECut(4 B_s, d_s)`, and
   `auxSourceExecutedRecord` is that record, with the frozen predicate, the
   frozen returned root and the frozen class tag.  It is the paper's instance,
   not a probe; the three generic constructors are the interface it is built
   through.
2. **`ExecutedRoots` is not reified, deliberately.**  `02:589--591` defines it
   as "the finite ordered list of roots stored in the compiler-executed cutoff
   records; it excludes every candidate-dependent symbolic search", while the
   banked `Cert.searches` field transcribes `02:485` ("lists **every** cutoff
   search") and carries no executed-versus-symbolic tag.  Reading
   `ExecutedRoots` off `Cert.searches` would therefore be a use-site-derived
   identification of a quantity whose defining sentence draws a distinction the
   record does not record, which is exactly the reading the use-as-definition
   ban forbids.  The honest consequence: `eq:R-exact` stays with the banked
   `CutoffEmission.roots`, and the `Cert`-side accessor is **owed**, together
   with the executed/symbolic tag `02:1022--1024` requires.
3. **`A_cert`, `SchemaChecked`, `NumChecked`, `Successor_16` are untouched.**
   No declaration, no axiom, no premise bundle standing in for one.  The
   runtime bound of `02:1400--1412` is likewise untouched; only its stated
   *reason* -- executed-search termination -- is supplied, for the `ECut` and
   `DCut` classes.
4. **The `PCut` third is banked, not re-proved.**  `pCut_nonempty` and
   `pCutPred_persist` are `EnvelopeRealization`'s, consumed by pin; the two
   declarations below that mention `PCut` are the `sInf` *leastness* and the
   packaged persistence eliminator, neither of which restates a banked
   statement.
5. **`h_s <= 4 B_s L^2` is claimed here; `s <= y <= y^2 - 15 <= n <= N_E` is
   not claimed or consumed by this module.**  (r0 findings 8 and 9, applied.)
   The continuation `06:1894--1915` -- the display `eq:aux-source-s-le-n`
   (`06:1903--1906`), the display `eq:aux-source-s-minus-three`
   (`06:1908--1911`), and the sentence `06:1912--1915` naming the persistent
   record `AUX.PRE.SOURCE.S_MINUS3_LE_NE` and its sole consumer; the r1
   citation stopped at `1905`, inside the first display, and dropped both the
   second display and the record sentence (r1 finding V-2) -- is **route
   content stated elsewhere** -- `AuxSourceDerivations.auxSourceSLeN` and
   `.auxSourceSMinusThree`, at the pinned `B_s =
   MechanicalCompilerResidue.bsSched` -- so it is false to call it "not in scope
   at the compilation unit"; the accurate statement, and the only one made, is
   that **no declaration below claims or consumes** `eq:aux-source-s-le-n` or
   `eq:aux-source-s-minus-three`.  **`cc-t8c` correction:** those two
   declarations stood in `ScheduleMajorantResidue`, which *is* transitively
   imported here, and this item said so; they were deleted there and re-authored
   in `AuxSourceDerivations`, which is a **sibling** module -- neither imports
   the other -- so the "transitively imported here" clause is withdrawn.  The
   two displays remain unclaimed and unconsumed by this module either way.
6. **No LEGAL SCHEDULED `ScheduleContext` exists yet, and none is claimed.**  The
   paper's own schedule context is the materialized schedule of `06:859--887`,
   which **consumes** `LevelStep`'s output.  Two route-ledger rows already carry
   that dependency and both are **OPEN**: `S5-LEVEL-STEP` (`proc:level-step`,
   `05:318--364` -- the procedure environment
   proper, from `\begin{procedure}` on `05:318` to `\end{procedure}` on
   `05:364`; `inv:construction-identity` (`05:366--374`) and the
   post-construction admissibility subsection opening at `05:376` are separate
   environments and are cited separately where needed -- r2 finding F5) and
   `S5-EXT-CALL-THREE`, which
   names `06:859--887` explicitly; `Section5Admissibility` cites them and
   labels its own two in-tree contexts BEYOND-PAPER probes.  Consequently the
   audit context of Part 8 is labelled **NON-FIDELITY / BEYOND-PAPER**, takes
   **zero** canonical credit, and discharges **no** legal non-vacuity
   obligation.

   [**R4 RECORD REPAIR at `cc-t8e`, 23 August 2026, comment-only** -- executed
   on the `cc-t8d` gate's finding R4.  This item used to say the materialized
   schedule "needs `LevelStep`" and to gloss `S5-LEVEL-STEP` as "the unbuilt
   `proc:level-step` constructor".  **The constructor is BANKED**:
   `LevelStepConstruction.levelStep` (`LevelStepConstruction.lean:1426`), gated
   78/0/0 at `cc-t7c-r4`, owned at `docs/BANKED_SURFACE_INDEX.md:695`, total at
   the frozen two-input domain of `05:320`; `LevelStepConstruction.ctxAt`
   inhabits the context type.  **The dependency sentence stays TRUE** -- the
   materialisation paragraph genuinely consumes the constructor's output -- and
   only "unbuilt" and "that is the remaining blocker" were stale.  **The
   residual is the canonical APPLICATION, not the constructor**:
   `S5-LEVEL-STEP` is OPEN on its *admissibility* half alone, whose residue the
   ledger names `S5-BUNDLE-INHABITATION` (the gate groups `06:863--873`,
   `06:877--884`, `09:387--395` rest on the unbuilt balanced-family existence
   argument), and `S5-EXT-CALL-THREE` is OPEN on its coverage *propositions*
   alone (`ExtNumeric`, `ExtDense`, `ExtTwo`, `ExtEarly`, `ExtTerminal`,
   `ExtensionCoverage`, all `PARAM-001` at `06:1671`), its four call domains
   already inhabited at the paper's own instances.  **Nothing in this module's
   statements, hypotheses, conclusions or proof terms is touched by this
   repair**, and no claim of this item is weakened: no legal scheduled context
   exists here, and none is claimed.]

   **This module claims no registration it cannot show (r1 finding Sol-4,
   corrected; r2 finding F1, corrected).**  The r1 text asserted that a
   canonical obligation named `PARAM-COMPILER-CONTEXT-INHABITATION` was
   "registered as deferred in the route ledger".  It was not: that string
   occurred nowhere in
   `routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`, so the
   sentence was a false statement about repository state -- the same class as
   the r0 header's false claim that no banked `d_s` reification existed, which
   makes it a **recurring** defect and not an isolated slip.  That claim is
   deleted rather than made true by minting a row under its name.

   The deferral of the deleted declaration **is** registered, under a different
   identifier: this deferral is registered as the OPEN obligation
   `PARAM-COMPILER-CUTOFF-ROW-AT-NSTEP`.  It depends on `S5-LEVEL-STEP` and,
   for the materialized schedule, `S5-EXT-CALL-THREE`; both prerequisites are
   OPEN.  (The r2 text of this block asserted the opposite -- that no
   identifier was minted at all -- which was the same false-repository-state
   class with its polarity inverted; r2 finding F1.)  The exact truth is: the
   canonical `ScheduleContext` inhabitation is **deferred to the
   `S5-LEVEL-STEP` arc**, is **not** discharged anywhere in
   this module, and becomes claimable when the materialized schedule lands.
   (r0 finding 10 also stands, applied: the r0 census turned a synthetic audit
   into legal non-vacuity credit, and that credit is withdrawn.)
-/

namespace EthInapproximability.ParameterizedNP.ScheduleCompilerExistential

open EthInapproximability.ParameterizedNP.EnvelopeRealization
open EthInapproximability.ParameterizedNP.IterationAssembly

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Part 1: the polynomial ratio, general in the index and the degree

`06:1813--1814` gives the `ECut` reason in six words -- "the polynomial grows
by at most a factor two" -- and `06:1815--1816` gives the `DCut` reason in the
same shape with `2^{2r+1}` in place of `2`.  Both reduce to one integer fact
about the ratio `((r+3)/(r+2))^d`, proved here in the two forms the persistence
step and the termination witness need.  Nothing in this part mentions a
schedule quantity. -/

/-- **Aux 1 (the integer form of `(1 + 1/m)^d <= m/(m-d)`).**

The one inequality behind both halves of Part 1, stated with natural truncated
subtraction so that it needs no side condition at all: above `d >= m` the left
factor `m - d` is zero and the claim is trivial, and below it the induction
step is `(m+1)(m-d-1) <= m(m-d)`, which loses exactly `d+1`.

General in the base and the degree. -/
theorem pow_succ_mul_sub_le (m d : ℕ) : (m + 1) ^ d * (m - d) ≤ m ^ (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rcases Nat.lt_or_ge m (d + 2) with hlt | hge
      · have hzero : m - (d + 1) = 0 := by omega
        simp [hzero]
      · have key : (m + 1) * (m - (d + 1)) ≤ m * (m - d) := by
          obtain ⟨a, ha⟩ : ∃ a, m = d + 2 + a := ⟨m - (d + 2), by omega⟩
          subst ha
          have h1 : d + 2 + a - (d + 1) = a + 1 := by omega
          have h2 : d + 2 + a - d = a + 2 := by omega
          rw [h1, h2]
          nlinarith
        calc (m + 1) ^ (d + 1) * (m - (d + 1))
            = (m + 1) ^ d * ((m + 1) * (m - (d + 1))) := by ring
          _ ≤ (m + 1) ^ d * (m * (m - d)) := Nat.mul_le_mul_left _ key
          _ = ((m + 1) ^ d * (m - d)) * m := by ring
          _ ≤ m ^ (d + 1) * m := Nat.mul_le_mul_right _ ih
          _ = m ^ (d + 1 + 1) := by ring

/-- **Aux 2 (`06:1813--1814`: the polynomial grows by at most a factor two).**

`(m+1)^d <= 2 m^d` as soon as the degree is at most half the base.  Written
`d + d <= m` rather than `2d <= m` so that the statement carries no numeral of
its own beyond the frozen factor two of `06:1802`; at `m = r + 2` it is exactly
the second clause of `ECut` in `eq:persistent-cutoffs`.

General in the base and the degree. -/
theorem pow_succ_le_two_mul {m d : ℕ} (h : d + d ≤ m) : (m + 1) ^ d ≤ 2 * m ^ d := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hd : d = 0 := by omega
    subst hd
    norm_num
  · have hkey := pow_succ_mul_sub_le m d
    have hle : m ≤ 2 * (m - d) := by omega
    have h5 : (m + 1) ^ d * m ≤ (2 * m ^ d) * m := by
      calc (m + 1) ^ d * m ≤ (m + 1) ^ d * (2 * (m - d)) := Nat.mul_le_mul_left _ hle
        _ = 2 * ((m + 1) ^ d * (m - d)) := by ring
        _ ≤ 2 * m ^ (d + 1) := Nat.mul_le_mul_left _ hkey
        _ = (2 * m ^ d) * m := by ring
    exact Nat.le_of_mul_le_mul_right h5 hm

/-- **Aux 3 (the ratio bound survives one step, at any factor).**

The half of `06:1812--1813` ("each predicate remains true for every larger
`r`") that neither `ECut` nor `DCut` gets for free: their *second* clause is a
statement about the polynomial ratio at the index, and it must be transported
to the successor index.  It is, because the ratio is decreasing:
`(m+2)m <= (m+1)^2`, so raising to the `d`-th power and cancelling `m^d` moves
the bound one step to the right.

Stated general in the factor `k`, which is why one lemma serves both the frozen
`2` of `ECut` (`06:1802`) and the frozen `2^{2r+1}` of `DCut` (`06:1808`).
General in the base, the degree and the factor. -/
theorem polyRatio_step {m d k : ℕ} (hm : 0 < m) (h : (m + 1) ^ d ≤ k * m ^ d) :
    (m + 2) ^ d ≤ k * (m + 1) ^ d := by
  have hpos : 0 < m ^ d := pow_pos hm d
  have hbase : (m + 2) * m ≤ (m + 1) * (m + 1) := by nlinarith
  have h1 : ((m + 2) * m) ^ d ≤ ((m + 1) * (m + 1)) ^ d := Nat.pow_le_pow_left hbase d
  have h2 : (m + 2) ^ d * m ^ d ≤ (m + 1) ^ d * (m + 1) ^ d := by
    simpa [mul_pow] using h1
  have h5 : (m + 2) ^ d * m ^ d ≤ (k * (m + 1) ^ d) * m ^ d := by
    calc (m + 2) ^ d * m ^ d ≤ (m + 1) ^ d * (m + 1) ^ d := h2
      _ ≤ (m + 1) ^ d * (k * m ^ d) := Nat.mul_le_mul_left _ h
      _ = (k * (m + 1) ^ d) * m ^ d := by ring
  exact Nat.le_of_mul_le_mul_right h5 hpos

/-- **Statement pole: the degree guard of Aux 2 is content.**

Without `d + d <= m` the factor-two clause of `06:1802` is simply false, so it
is a genuine condition on the search index rather than a formality -- which is
why `ECut` tests it as a *second* condition instead of deriving it from the
first.

**BEYOND-PAPER AUDIT** at `(m, d) = (1, 2)`: the frozen text asserts the
factor-two growth only inside the search brace and exhibits no counterexample,
so the pair is ours and audits *our* encoding.  It claims no legality. -/
theorem pow_succ_le_two_mul_needs_guard : ¬ ∀ m d : ℕ, (m + 1) ^ d ≤ 2 * m ^ d := by
  intro h
  have hbad := h 1 2
  norm_num at hbad

/-! ## Part 2: `ECut` terminates and persists

`eq:persistent-cutoffs`, first clause (`06:1799--1802`), against the sentence
`06:1812--1814`.  The predicate itself is the banked
`EnvelopeRealization.ECutPred` and is consumed by pin, never restated. -/

/-- **Aux 4 (the arithmetic of the termination witness).**

The three comparisons the `ECut` witness needs, isolated over a plain variable
`P` so that the exponential is an opaque bound and the argument is visibly
linear in it.  Instantiated below at `P = 2^k` with `k = A + d + 8`, where the
hypothesis is the banked `IterationAssembly.sq_le_two_pow` of `02:892`.

General in all three naturals. -/
theorem cutoffWitnessArithmetic {d k P : ℕ} (hkd : d ≤ k)
    (hsq : k ^ 2 + 2 * k + 4 ≤ P) :
    d + d ≤ P ∧ k + k * d + 4 ≤ P ∧ 4 ≤ P := by
  have hkk : k * d ≤ k ^ 2 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **`ECut` terminates** -- the first clause of `06:1812`, "Each search
terminates", for the `ECut` case.  This is `EnvelopeRealization`'s
GAP-EXPOSED 3, first half, discharged.

The witness is the paper's own shape rather than an opaque appeal: take the
index whose shifted base `r + 2` is the power of two `2^k` at
`k = A + d + 8`.  Then the polynomial `A(r+2)^d` has exponent `k + kd`, the
exponential `2^{r-2}` has exponent `2^k - 4`, and the banked elementary
comparison `M^2 + 2M + 4 <= 2^M` of `02:892` separates them; the second frozen
condition is Aux 2 at `d + d <= 2^k`.

General in the coefficient and the degree, with no side condition -- the frozen
scope sentence `06:1796` restricts to positive arguments, and the search is
nonempty even without that restriction. -/
theorem eCut_nonempty (A d : ℕ) : {r | ECutPred A d r}.Nonempty := by
  have hk8 : 8 ≤ A + d + 8 := by omega
  have hkA : A ≤ A + d + 8 := by omega
  have hkd : d ≤ A + d + 8 := by omega
  have hsq := IterationAssembly.sq_le_two_pow (A + d + 8) hk8
  obtain ⟨hdd, hbig, hP4⟩ := cutoffWitnessArithmetic hkd hsq
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hP4
  have e1 : m + 2 + 2 = 2 ^ (A + d + 8) := by rw [hm]; omega
  have e2 : m + 2 - 2 = m := by omega
  have e3 : m + 2 + 3 = 2 ^ (A + d + 8) + 1 := by rw [hm]; omega
  have hpred : ECutPred A d (m + 2) := by
    refine ⟨by omega, ?_, ?_⟩
    · rw [e1, e2]
      have hAle : A ≤ 2 ^ (A + d + 8) :=
        le_trans hkA (Nat.le_of_lt Nat.lt_two_pow_self)
      have hpow : ((2 : ℕ) ^ (A + d + 8)) ^ d = 2 ^ ((A + d + 8) * d) := by
        rw [← pow_mul]
      have hsum : (2 : ℕ) ^ (A + d + 8) * 2 ^ ((A + d + 8) * d)
          = 2 ^ ((A + d + 8) + (A + d + 8) * d) := by rw [← pow_add]
      have hexpm : (A + d + 8) + (A + d + 8) * d ≤ m := by
        rw [hm] at hbig; linarith
      rw [hpow]
      calc A * 2 ^ ((A + d + 8) * d)
          ≤ 2 ^ (A + d + 8) * 2 ^ ((A + d + 8) * d) := Nat.mul_le_mul_right _ hAle
        _ = 2 ^ ((A + d + 8) + (A + d + 8) * d) := hsum
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hexpm
    · rw [e1, e3]
      exact pow_succ_le_two_mul hdd
  exact ⟨m + 2, hpred⟩

/-- **Aux 5 (`ECut` persists by one step)** -- `06:1812--1814`.

Both frozen conditions are transported.  The exponential doubles while the
polynomial grows by at most a factor two, which is the paper's own sentence and
closes the first condition; the second is Aux 3 at factor two.  General. -/
theorem eCutPred_succ {A d r : ℕ} (h : ECutPred A d r) : ECutPred A d (r + 1) := by
  obtain ⟨h2, hexp, hrat⟩ := h
  have hrat' : (r + 2 + 1) ^ d ≤ 2 * (r + 2) ^ d := by
    have e : r + 2 + 1 = r + 3 := by omega
    rw [e]; exact hrat
  refine ⟨by omega, ?_, ?_⟩
  · have e1 : r + 1 + 2 = r + 3 := by omega
    have e2 : r + 1 - 2 = r - 2 + 1 := by omega
    rw [e1, e2, pow_succ]
    calc A * (r + 3) ^ d ≤ A * (2 * (r + 2) ^ d) := Nat.mul_le_mul_left _ hrat
      _ = 2 * (A * (r + 2) ^ d) := by ring
      _ ≤ 2 * 2 ^ (r - 2) := Nat.mul_le_mul_left _ hexp
      _ = 2 ^ (r - 2) * 2 := by ring
  · have e1 : r + 1 + 2 = r + 2 + 1 := by omega
    have e3 : r + 1 + 3 = r + 2 + 2 := by omega
    rw [e1, e3]
    exact polyRatio_step (by omega) hrat'

/-- **`ECut` persists at every larger index** -- the second clause of
`06:1812--1813`, "each predicate remains true for every larger `r`", for
`ECut`.  General in both indices. -/
theorem eCutPred_persist {A d r r' : ℕ} (h : ECutPred A d r) (hr : r ≤ r') :
    ECutPred A d r' := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact eCutPred_succ ih

/-- **Aux 6 (the emitted `ECut` root satisfies its own predicate).**

`Nat.sInf_mem` at `eCut_nonempty`: the frozen `min` of `eq:persistent-cutoffs`
is attained, so a stored `ECut` root is usable rather than the Lean default
`0`.  General. -/
theorem eCut_spec (A d : ℕ) : ECutPred A d (eCut A d) :=
  Nat.sInf_mem (eCut_nonempty A d)

/-- **Aux 7 (`ECut` returns the *least* index)** -- `02:486`, "its least
returned integer".  General. -/
theorem eCut_least (A d : ℕ) {k : ℕ} (h : k < eCut A d) : ¬ ECutPred A d k :=
  fun hk => absurd (Nat.sInf_le hk) (not_le.mpr h)

/-- **Aux 8 (the stored `ECut` persistence eliminator)** -- `02:486--487`, "an
integer proof that the predicate persists at all larger integers", in the form
a consumer uses.  General. -/
theorem eCut_persists (A d : ℕ) {k : ℕ} (h : eCut A d ≤ k) : ECutPred A d k :=
  eCutPred_persist (eCut_spec A d) h

/-- **Statement pole: the `ECut` search really searches.**

At its own floor `r = 2` the first frozen condition reads `A(r+2)^d <= 2^0 = 1`,
which already fails at the smallest interesting coefficient.  So `eCut` is not
the constant `2`, and `eCut_nonempty` is not a restatement of the floor.

**BEYOND-PAPER AUDIT** at `(A, d, r) = (2, 0, 2)`: a rejection probe claiming
no legality, exhibited only to show the guard fires. -/
theorem eCutPred_not_at_floor : ¬ ECutPred 2 0 2 := by
  rintro ⟨-, hbad, -⟩
  norm_num at hbad

/-! ## Part 3: `DCut` terminates and persists

`eq:persistent-cutoffs`, third clause (`06:1805--1808`), against
`06:1815--1816`: "in `DCut`, the exponential ratio is `2^{2r+1}`, which
dominates the polynomial ratio". -/

/-- **Aux 9 (`ECut` dominates `DCut` at every index).**

Both `DCut` conditions are weakenings of the corresponding `ECut` ones:
`2^{r-2} <= 2^{r^2}` because `r - 2 <= r <= r^2` on the search domain `r >= 2`,
and the factor `2` of `06:1802` is at most the factor `2^{2r+1}` of `06:1808`.
This is why the `DCut` search needs no separate witness.  General. -/
theorem eCutPred_imp_dCutPred {A d r : ℕ} (h : ECutPred A d r) : DCutPred A d r := by
  obtain ⟨h2, hexp, hrat⟩ := h
  refine ⟨h2, ?_, ?_⟩
  · refine le_trans hexp (Nat.pow_le_pow_right (by norm_num) ?_)
    have hself : r ≤ r ^ 2 := by nlinarith
    exact le_trans (Nat.sub_le r 2) hself
  · refine le_trans hrat (Nat.mul_le_mul_right _ ?_)
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`DCut` terminates** -- `06:1812`, "Each search terminates", for the
`DCut` case.  `EnvelopeRealization`'s GAP-EXPOSED 3, second half, discharged,
through Aux 9 rather than through a second witness search.  General. -/
theorem dCut_nonempty (A d : ℕ) : {r | DCutPred A d r}.Nonempty := by
  obtain ⟨r, hr⟩ := eCut_nonempty A d
  exact ⟨r, eCutPred_imp_dCutPred hr⟩

/-- **Aux 10 (`DCut` persists by one step)** -- `06:1815--1816`, transcribed:
the exponential ratio `2^{(r+1)^2 - r^2} = 2^{2r+1}` is exactly the factor the
second frozen condition allows the polynomial, so the first condition survives;
and the second survives by Aux 3 at that factor, enlarged to `2^{2(r+1)+1}`.
General. -/
theorem dCutPred_succ {A d r : ℕ} (h : DCutPred A d r) : DCutPred A d (r + 1) := by
  obtain ⟨h2, hexp, hrat⟩ := h
  have hrat' : (r + 2 + 1) ^ d ≤ 2 ^ (2 * r + 1) * (r + 2) ^ d := by
    have e : r + 2 + 1 = r + 3 := by omega
    rw [e]; exact hrat
  refine ⟨by omega, ?_, ?_⟩
  · have e1 : r + 1 + 2 = r + 3 := by omega
    have e2 : (r + 1) ^ 2 = r ^ 2 + (2 * r + 1) := by ring
    rw [e1, e2, pow_add]
    calc A * (r + 3) ^ d ≤ A * (2 ^ (2 * r + 1) * (r + 2) ^ d) :=
          Nat.mul_le_mul_left _ hrat
      _ = 2 ^ (2 * r + 1) * (A * (r + 2) ^ d) := by ring
      _ ≤ 2 ^ (2 * r + 1) * 2 ^ r ^ 2 := Nat.mul_le_mul_left _ hexp
      _ = 2 ^ r ^ 2 * 2 ^ (2 * r + 1) := by ring
  · have e1 : r + 1 + 2 = r + 2 + 1 := by omega
    have e3 : r + 1 + 3 = r + 2 + 2 := by omega
    rw [e1, e3]
    refine le_trans (polyRatio_step (by omega) hrat') ?_
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **`DCut` persists at every larger index** -- `06:1812--1813` for `DCut`.
General in both indices. -/
theorem dCutPred_persist {A d r r' : ℕ} (h : DCutPred A d r) (hr : r ≤ r') :
    DCutPred A d r' := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact dCutPred_succ ih

/-- **Aux 11 (the emitted `DCut` root satisfies its own predicate).**  General. -/
theorem dCut_spec (A d : ℕ) : DCutPred A d (dCut A d) :=
  Nat.sInf_mem (dCut_nonempty A d)

/-- **Aux 12 (`DCut` returns the least index)** -- `02:486`.  General. -/
theorem dCut_least (A d : ℕ) {k : ℕ} (h : k < dCut A d) : ¬ DCutPred A d k :=
  fun hk => absurd (Nat.sInf_le hk) (not_le.mpr h)

/-- **Aux 13 (the stored `DCut` persistence eliminator)** -- `02:486--487`.
General. -/
theorem dCut_persists (A d : ℕ) {k : ℕ} (h : dCut A d ≤ k) : DCutPred A d k :=
  dCutPred_persist (dCut_spec A d) h

/-! ## Part 4: the frozen sentence `06:1812--1816`, whole

The banked `PCut` third is consumed by pin: `pCut_nonempty` and
`pCutPred_persist` are `EnvelopeRealization`'s and are not restated.  What is
added for `PCut` is only what the `SearchRow` record needs and the banked
module does not carry: `sInf` leastness, and the persistence eliminator in
consumer form. -/

/-- **Aux 14 (`PCut` returns the least index)** -- `02:486`, over the banked
`EnvelopeRealization.pCut`.  General. -/
theorem pCut_least (A d e : ℕ) {k : ℕ} (h : k < pCut A d e) : ¬ PCutPred A d e k :=
  fun hk => absurd (Nat.sInf_le hk) (not_le.mpr h)

/-- **Aux 15 (the stored `PCut` persistence eliminator)** -- `02:486--487`,
assembled from the banked `pCut_spec` and `pCutPred_persist` at the frozen side
condition `e > d` of `06:1796`.  General. -/
theorem pCut_persists (A d e : ℕ) (hde : d < e) {k : ℕ} (h : pCut A d e ≤ k) :
    PCutPred A d e k :=
  pCutPred_persist (le_of_lt hde) (pCut_spec A d e hde) h

/-- **`06:1812`, first sentence, whole: each of the three searches
terminates.**

The `ECut` and `DCut` halves are this module's; the `PCut` half is the banked
`EnvelopeRealization.pCut_nonempty`, consumed by pin.  Assembled into one
statement because `02:1414` uses it as one fact: "Both `J_c` and `B_c` are
finite by the executed-search termination proof."

The side condition is the frozen one of `06:1796`, and it is needed only by the
`PCut` conjunct.  General in the arguments. -/
theorem persistentCutoffs_terminate (A d e : ℕ) (hde : d < e) :
    {r | ECutPred A d r}.Nonempty ∧ {r | PCutPred A d e r}.Nonempty ∧
      {r | DCutPred A d r}.Nonempty :=
  ⟨eCut_nonempty A d, pCut_nonempty A d e hde, dCut_nonempty A d⟩

/-- **`06:1812--1813`, second sentence, whole: each predicate remains true for
every larger `r`.**

Same assembly, same pin: the `PCut` conjunct is the banked
`EnvelopeRealization.pCutPred_persist`.  General in both indices. -/
theorem persistentCutoffs_persist {A d e r r' : ℕ} (hde : d ≤ e) (hr : r ≤ r') :
    (ECutPred A d r → ECutPred A d r') ∧
      (PCutPred A d e r → PCutPred A d e r') ∧
      (DCutPred A d r → DCutPred A d r') :=
  ⟨fun h => eCutPred_persist h hr, fun h => pCutPred_persist hde h hr,
    fun h => dCutPred_persist h hr⟩

/-! ## Part 5: the executed cutoff records of `Searches_c`

`02:485--487` and `02:341--342`: an executed search record is its exact integer
predicate, its least returned integer, and its stored nonemptiness, leastness
and persistence proofs; `02:1019--1021` says the compiler stores one such
record per emitted argument tuple of `eq:persistent-cutoffs`.  The record type
is the banked `MechanicalCompilerResidue.SearchRow`, consumed by pin; the three
constructors below are the only way this route can produce one for the three
frozen searches, because before this tranche two of the three predicates had no
nonemptiness proof at all. -/

/-- **The executed `ECut` record** (`eq:persistent-cutoffs` through
`02:485--487`).  Its predicate is the frozen `ECutPred`, its returned integer
the frozen `eCut`, its class tag the frozen `ECut` of `02:478`, and its three
proof fields are Aux 6, Aux 7 and Aux 8. -/
noncomputable def eCutSearchRow (A d : ℕ) : MechanicalCompilerResidue.SearchRow where
  predicate := ECutPred A d
  returned := eCut A d
  kind := MechanicalCompilerResidue.CutKind.ecut
  satisfied := eCut_spec A d
  least := fun _ hk => eCut_least A d hk
  persists := fun _ hk => eCut_persists A d hk

/-- **The executed `PCut` record**, at the frozen side condition `e > d` of
`06:1796`.  Its nonemptiness and persistence fields are the banked
`EnvelopeRealization.pCut_spec` and `.pCutPred_persist`, consumed by pin
through Aux 15. -/
noncomputable def pCutSearchRow (A d e : ℕ) (hde : d < e) :
    MechanicalCompilerResidue.SearchRow where
  predicate := PCutPred A d e
  returned := pCut A d e
  kind := MechanicalCompilerResidue.CutKind.pcut
  satisfied := pCut_spec A d e hde
  least := fun _ hk => pCut_least A d e hk
  persists := fun _ hk => pCut_persists A d e hde hk

/-- **The executed `DCut` record** (`eq:persistent-cutoffs`, third clause).
`02:1014` records that no *tail* class uses `DCut`; `06:1938--1939` still emits
`D(c)` for the common-depth request, which is why the record exists. -/
noncomputable def dCutSearchRow (A d : ℕ) : MechanicalCompilerResidue.SearchRow where
  predicate := DCutPred A d
  returned := dCut A d
  kind := MechanicalCompilerResidue.CutKind.dcut
  satisfied := dCut_spec A d
  least := fun _ hk => dCut_least A d hk
  persists := fun _ hk => dCut_persists A d hk

/-- **Aux 16 (each record stores the frozen search it is named for).**

The three returned integers are exactly the three cutoffs of
`eq:persistent-cutoffs`, the three predicates are exactly the three frozen
brace conditions, and the three class tags are the three registered classes of
`02:478`.  So no record silently drifts from the search it claims to execute,
and `eq:R-exact` may read its roots off these fields.  General. -/
theorem searchRows_store_the_frozen_searches (A d e : ℕ) (hde : d < e) :
    (eCutSearchRow A d).returned = eCut A d ∧
      (pCutSearchRow A d e hde).returned = pCut A d e ∧
      (dCutSearchRow A d).returned = dCut A d ∧
      (eCutSearchRow A d).predicate = ECutPred A d ∧
      (pCutSearchRow A d e hde).predicate = PCutPred A d e ∧
      (dCutSearchRow A d).predicate = DCutPred A d :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Aux 17 (the three records carry the three distinct registered classes).**

`02:478` prints `Cutoff(u, ECut/PCut/DCut)` as three tags, and the banked
`MechanicalCompilerResidue.cutKindsIsTheCompleteRoster` proves the roster is
exactly those three; here the three constructed records are shown to occupy
them pairwise distinctly, so no two of the frozen searches are stored under one
tag.  General. -/
theorem executedSearchRows_are_three_distinct_classes (A d e : ℕ) (hde : d < e) :
    (eCutSearchRow A d).kind ≠ (pCutSearchRow A d e hde).kind ∧
      (eCutSearchRow A d).kind ≠ (dCutSearchRow A d).kind ∧
      (pCutSearchRow A d e hde).kind ≠ (dCutSearchRow A d).kind := by
  have h1 : (eCutSearchRow A d).kind = MechanicalCompilerResidue.CutKind.ecut := rfl
  have h2 : (pCutSearchRow A d e hde).kind = MechanicalCompilerResidue.CutKind.pcut :=
    rfl
  have h3 : (dCutSearchRow A d).kind = MechanicalCompilerResidue.CutKind.dcut := rfl
  rw [h1, h2, h3]
  exact ⟨by decide, by decide, by decide⟩

/-! ## Part 6: the emitted roots and `eq:R-exact`

The banked `EnvelopeRealization.pCut_le_R` records that an emitted `PCut`
tuple's root is at most `R(c)`.  Its two siblings are supplied here, at the
same display `eq:R-exact` (`06:1944--1952`) and by the same argument; `R(c)`
itself is consumed by pin and is not re-reified. -/

/-- **An emitted `ECut` argument's root is dominated by `R(c)`** --
`eq:R-exact`, second line of the displayed union.  General in the emission, the
exponent and the argument pair. -/
theorem eCut_le_R {Em : CutoffEmission} {c A d : ℕ} (h : (A, d) ∈ Em.eArgs c) :
    eCut A d ≤ Em.R c := by
  refine le_trans (le_literalMax ?_) (le_max_right 2 _)
  simp only [CutoffEmission.roots, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨(A, d), h, rfl⟩))

/-- **An emitted `DCut` argument's root is dominated by `R(c)`** --
`eq:R-exact`, fourth line of the displayed union.  General. -/
theorem dCut_le_R {Em : CutoffEmission} {c A d : ℕ} (h : (A, d) ∈ Em.dArgs c) :
    dCut A d ≤ Em.R c := by
  refine le_trans (le_literalMax ?_) (le_max_right 2 _)
  simp only [CutoffEmission.roots, List.mem_append, List.mem_map]
  exact Or.inr ⟨(A, d), h, rfl⟩

/-! ## Part 7: the auxiliary source row, the paper's own `ECut` application

`06:1861--1893`.  This is the one place in the frozen source where `ECut` is
instantiated at a named argument, so it is where the canonical-inhabitation
question for an executed `ECut` record is settled.

**Binder provenance for this part** -- every declaration of Part 7, and equally
of Part 8.  (The r1 text keyed this paragraph to a list of r0 declaration
numbers, one of which named the declaration deferred this round; the paragraph
is stated over the parts themselves instead, so it cannot go stale again.)  The
four public inputs `b_out`, `B_pub`, `z_R`, `clog_2(|E|+2)` are *defined
accessors* -- `06:47--54` displays two of them and `05:126--141` lists all of
them as accessors with defining displays -- so none of them is a free binder
here.  Every declaration below that needs one takes a
`Section5Admissibility.ScheduleContext` and evaluates it: `C.P.bout` is the
public-record field, `BpubOf C`, `zROf C`, `clEOf C` and `ApreOf C` are the
banked evaluations, and `uAuxOf C` is `u` at that `A_pre`.  The banked
`EnvelopeRealization.lSandwich_upper` and `.normalizedL` are still applied at
their own four-binder signature, now at those evaluated arguments, so the
banked interface is consumed exactly as pinned and nothing is
re-parameterized.  `d_s` is the banked `ScheduleMajorantResidue.dsExp`; this
module declares no `dsExp` of its own. -/

/-- **`h_s = log_2 s`** -- `06:1865`, "`h_s = log_2 s = ceil(B_s u^2) = B_s
u^2`", evaluated at a schedule context.

Exposed the way the frozen text writes it -- as the base-two logarithm of the
scale `s` of `eq:s-choice` -- over the banked `Section5Admissibility.sOf`,
which is `ParameterSchedule.sScale` at the context's own configuration `B_s`
(`06:56--62`) and its own `u = uAux (ApreOf C)` (`06:116--117`).  Nothing is
selected and no factor is assigned: the product form is *derived* in `hsOf_eq`
from the banked ceiling identity. -/
noncomputable def hsOf (C : Section5Admissibility.ScheduleContext V E) : ℕ :=
  Nat.log 2 (Section5Admissibility.sOf C)

/-- **Aux 18 (`h_s = B_s u^2`, exactly)** -- the frozen chain
`log_2 s = ceil(B_s u^2) = B_s u^2` of `06:1865`, with `06:1867` recording that
the last equality is exact "because `B_s` and `u` are integers".

Proved by consuming the banked `ScheduleMajorantResidue.hsAux_eq` in the proof
term, so the ceiling step is the banked one and is not re-derived.  General in
the context. -/
theorem hsOf_eq (C : Section5Admissibility.ScheduleContext V E) :
    hsOf C = C.K.Bs * Section5Admissibility.uAuxOf C ^ 2 :=
  ScheduleMajorantResidue.hsAux_eq C.K.Bs (Section5Admissibility.uAuxOf C)

/-- **The compiler's emitted `ECut` argument pair** -- `06:1883--1884`, "The
compiler inserts `(4 B_s, d_s)` into `E(c)`", with its root
`r_s = ECut(4 B_s, d_s)` at `06:1886`.

Both components are evaluated, never assigned: `B_s` is the compiler's own K1
choice `B_s = T^2` (`02:815--819`, the banked
`MechanicalCompilerResidue.bsSched`), which `02:812--813` says is "performed
once and then compiled into every certificate machine"; `d_s` is the banked
`ScheduleMajorantResidue.dsExp` at its own frozen display `06:1864`.

This is the module's **unique** reification of the emitted pair, and every
declaration below that mentions the pair consumes it. -/
noncomputable def auxSourceECutArg (c : ℕ) : ℕ × ℕ :=
  (4 * MechanicalCompilerResidue.bsSched, ScheduleMajorantResidue.dsExp c)

/-- **Aux 19 (the emitted pair's two components, read off the accessor).**

The projection readout of `auxSourceECutArg`, consumed by
`auxSourceExecutedRecord_isThePaperRoot` so that the canonical readout is
stated through the accessor rather than by repeating the defining pair.
General in the exponent. -/
theorem auxSourceECutArg_eq (c : ℕ) :
    (auxSourceECutArg c).1 = 4 * MechanicalCompilerResidue.bsSched ∧
      (auxSourceECutArg c).2 = ScheduleMajorantResidue.dsExp c :=
  ⟨rfl, rfl⟩

/-- **`u <= 2L`, general in `A_pre`** -- `06:1867--1876`, transcribed link by
link: `A_pre >= 16` and `L = clog_2(A_pre)` give `L >= 4` and
`A_pre + 16 <= 2 A_pre <= 2^{L+1}`, hence `clog_2(A_pre + 16) <= L + 1 <= 2L`;
and `clog_2(2L) <= 2L`, so the outer ceiling logarithm of `eq:s-choice` lands
inside `2L` as well.

The frozen derivation uses **exactly one** input, `A_pre >= 16` (`06:1868`), so
that is the only hypothesis.  `A_pre` itself is **not** free: it is
SOURCE-DEFINED by the first line of `eq:s-choice` (`06:111--115`).  What is free
here is this lemma's own binder `Apreval`, the arbitrary natural of a *general*
arithmetic statement that is strictly stronger than the frozen sentence; the
paper-facing consumer `uAux_le_two_normalizedL` specializes it by **evaluating**
the definitional chain, at `Section5Admissibility.ApreOf C`.  No public accessor
occurs in this statement (r1 finding Sol-2; completed at r2 finding F2). -/
theorem uAux_le_two_clog (Apreval : ℕ) (h16 : 16 ≤ Apreval) :
    ParameterSchedule.uAux Apreval ≤ 2 * Nat.clog 2 Apreval := by
  have hApow : Apreval ≤ 2 ^ Nat.clog 2 Apreval := Nat.le_pow_clog (by norm_num) _
  have hpow3 : (2 : ℕ) ^ 3 < Apreval := by norm_num; omega
  have hL4 : 4 ≤ Nat.clog 2 Apreval := by
    have := ParameterSchedule.lt_clog_of_pow_lt (b := 2) (by norm_num) hpow3
    omega
  have hdouble : Apreval + 16 ≤ 2 ^ (Nat.clog 2 Apreval + 1) := by
    rw [pow_succ]
    calc Apreval + 16 ≤ Apreval + Apreval := by omega
      _ = Apreval * 2 := by ring
      _ ≤ 2 ^ Nat.clog 2 Apreval * 2 := Nat.mul_le_mul_right _ hApow
  have hinner : Nat.clog 2 (Apreval + 16) ≤ Nat.clog 2 Apreval + 1 :=
    Nat.clog_le_of_le_pow hdouble
  have hinner2 : Nat.clog 2 (Apreval + 16) ≤ 2 * Nat.clog 2 Apreval := by omega
  have hself : 2 * Nat.clog 2 Apreval ≤ 2 ^ (2 * Nat.clog 2 Apreval) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  unfold ParameterSchedule.uAux
  exact Nat.clog_le_of_le_pow (le_trans hinner2 hself)

/-- **`u <= 2L` at a schedule context** -- `06:1867--1876` with the four public
inputs evaluated through their own defining displays rather than bound free:
`b_out` is the public-record field `C.P.bout` (`05:13--52`), and `B_pub`,
`z_R`, `clog_2(|E|+2)` are `Section5Admissibility.BpubOf`, `.zROf`, `.clEOf`
at `06:47--54` and `06:115`, so `A_pre` is `ApreOf C` and `u` is `uAuxOf C`.

`L` is the banked `EnvelopeRealization.normalizedL` **consumed at its own
four-binder signature**, applied at those evaluated arguments; `A_pre >= 16` is
the banked `ParameterSchedule.sixteen_le_Apre`.  General in the context. -/
theorem uAux_le_two_normalizedL (C : Section5Admissibility.ScheduleContext V E) :
    Section5Admissibility.uAuxOf C
      ≤ 2 * normalizedL C.P.bout (Section5Admissibility.BpubOf C)
          (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C) :=
  uAux_le_two_clog (Section5Admissibility.ApreOf C)
    (ParameterSchedule.sixteen_le_Apre C.P.bout (Section5Admissibility.BpubOf C)
      (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C))

/-- **`eq:aux-source-s-normalized`** (`06:1878--1882`),
`h_s <= 4 B_s L^2 <= 4 B_s (lambda+2)^{2(c+1)}`, **both links**, derived rather
than assumed.

The two inputs are the frozen ones: `u <= 2L` (`06:1875--1876`) and the upper
half of `eq:L-ell-sandwich`, whose **defining display** is `06:1846--1850`
(`l(n) - 2 <= L <= (l(n)+2)^{c+1}`, introduced by "the normalization program
substitutes" on `06:1846`).  The r1 citation gave `06:1877--1878` instead, which
is the *reference* to that display at the consuming site and not the display --
a use-site citation standing in for a definition (r1 finding Sol-3).  That
reference sentence in fact crosses `06:1876--1877` ("The upper half of" ends
`06:1876`; "\eqref{eq:L-ell-sandwich} therefore yields the literal normalized
row" is `06:1877`), while `06:1878` is the `\begin{equation}` of the row
display itself, so the withdrawn citation was also misdescribed by one line
(r2 finding F3).  The
formalization consumes the banked
`EnvelopeRealization.lSandwich_upper` at its own five envelope hypotheses, which
is that display and not its reference.
The row itself is the banked `ScheduleMajorantResidue.auxSourceRow`, **consumed
in the proof term**; nothing of its algebra is re-derived here.  What this
declaration adds is the instantiation the compiler application needs -- `B_s`,
`u` and `L` specialized to the context, and the frozen intermediate `4 B_s L^2`
kept visible as the first conjunct.

General in the context, the exponent and the source size. -/
theorem auxSourceNormalizedRow (C : Section5Admissibility.ScheduleContext V E)
    (c n : ℕ) (h16 : 16 ≤ envE c n) (hbout : C.P.bout ≤ envE c n)
    (hBpub : Section5Admissibility.BpubOf C ≤ envE c n)
    (hzR : Section5Admissibility.zROf C ≤ envE c n)
    (hclE : Section5Admissibility.clEOf C ≤ envE c n) :
    hsOf C ≤ 4 * C.K.Bs * normalizedL C.P.bout (Section5Admissibility.BpubOf C)
        (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C) ^ 2 ∧
      4 * C.K.Bs * normalizedL C.P.bout (Section5Admissibility.BpubOf C)
          (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C) ^ 2
        ≤ 4 * C.K.Bs * (ellN n + 2) ^ ScheduleMajorantResidue.dsExp c := by
  have hu := uAux_le_two_normalizedL C
  have hL := lSandwich_upper C.P.bout (Section5Admissibility.BpubOf C)
    (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C) c n h16 hbout hBpub
    hzR hclE
  have hrow := ScheduleMajorantResidue.auxSourceRow C.K.Bs
    (Section5Admissibility.uAuxOf C)
    (normalizedL C.P.bout (Section5Admissibility.BpubOf C)
      (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C)) c n hu hL
  rw [hsOf_eq]
  exact hrow

/-- **`eq:aux-source-s-ecut`** (`06:1890--1893`),
`h_s <= 4 B_s (lambda+2)^{d_s} <= 2^{lambda-2}`.

The frozen guard is `06:1888--1889`: "When `lambda >= R(c)+2`, persistence is
evaluated at the exact ordinary index `r = lambda`, not at `lambda-2`."  That
is exactly what happens: the emitted pair `auxSourceECutArg c` lies in `E(c)`,
so its root is at most `R(c)` by `eCut_le_R`, hence at most `l(n)`, and
`eCut_persists` supplies the frozen `ECut` predicate *at* `l(n)`.  The row is
then the banked `ScheduleMajorantResidue.auxSourceEcutRow`, **consumed in the
proof term** rather than re-derived.

`hBs` is the frozen identification of the context's configuration `B_s`
(`06:56--62`) with the compiler's own K1 choice `B_s = T^2` (`02:815--819`),
which `02:812--813` compiles "into every certificate machine": it is what makes
the context's `h_s` and the compiler's emitted coefficient `4 B_s` the same
`B_s`, and it is stated explicitly rather than assumed silently.

General in the emission, the context, the exponent and the source size. -/
theorem auxSourceECutRow (Em : CutoffEmission)
    (C : Section5Admissibility.ScheduleContext V E) (c n : ℕ)
    (hBs : C.K.Bs = MechanicalCompilerResidue.bsSched)
    (hemit : auxSourceECutArg c ∈ Em.eArgs c)
    (hlam : Em.R c + 2 ≤ ellN n) (h16 : 16 ≤ envE c n)
    (hbout : C.P.bout ≤ envE c n)
    (hBpub : Section5Admissibility.BpubOf C ≤ envE c n)
    (hzR : Section5Admissibility.zROf C ≤ envE c n)
    (hclE : Section5Admissibility.clEOf C ≤ envE c n) :
    hsOf C ≤ 2 ^ (ellN n - 2) := by
  have hroot : eCut (4 * MechanicalCompilerResidue.bsSched)
      (ScheduleMajorantResidue.dsExp c) ≤ Em.R c := eCut_le_R hemit
  have hpred : ECutPred (4 * C.K.Bs) (ScheduleMajorantResidue.dsExp c) (ellN n) := by
    rw [hBs]
    exact eCut_persists _ _ (by omega)
  have hu := uAux_le_two_normalizedL C
  have hL := lSandwich_upper C.P.bout (Section5Admissibility.BpubOf C)
    (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C) c n h16 hbout hBpub
    hzR hclE
  have hrow := ScheduleMajorantResidue.auxSourceEcutRow C.K.Bs
    (Section5Admissibility.uAuxOf C)
    (normalizedL C.P.bout (Section5Admissibility.BpubOf C)
      (Section5Admissibility.zROf C) (Section5Admissibility.clEOf C)) c n hu hL hpred
  rw [hsOf_eq]
  exact hrow

/-! ### DEFERRED (deleted this round, not repaired): the same row at the frozen
cutoff hypothesis

The declaration that stood here restated `auxSourceECutRow` under the frozen
cutoff hypothesis `n >= n_step(c)` of `06:1960--1962` ("If `n >= n_step(c)`,
then `l(n) >= R(c)+2 >= 4`", the single word `If` on `06:1960` and the closing
comparison on `06:1962`) in place of the guard `lambda >= R(c)+2` of
`06:1888--1889`, discharging that guard from the banked
`EnvelopeRealization.cutoff_eligibility`.

It is **deferred to the `S5-LEVEL-STEP` arc** for the reason given in full under
"What this round split off": its premise bundle demands a canonical
`Section5Admissibility.ScheduleContext` together with an emission containing the
paper's emitted pair, and both come from the materialized schedule of
`06:859--887`, which needs the unbuilt `LevelStep`.  Its mathematics is not in
question and nothing about it was found wrong; what it lacked was a **legal**
nondegenerate inhabitant of that bundle, and the only inhabitant available here
was a labelled NON-FIDELITY probe, which is not one.

Nothing downstream depends on it: `auxSourceECutRow` below carries the same
conclusion at the paper's own frozen guard, and the deferred statement is just
that result composed with `cutoff_eligibility`.  Consequently
`CutoffEmission.nStep` and the sentence `06:1960--1962` are consumed by **no**
declaration in this module. -/

/-! ## Part 8: canonical inhabitation, and the audit that is not one

`06:1883--1887` is the frozen source's own instantiation of `ECut`.  The
executed record it describes is therefore the required witness for the
`SearchRow` type on this route, and it is exhibited rather than probed.

The **context** side is different, and is labelled accordingly: the paper's own
schedule context is the materialized schedule of `06:859--887`, which is not
built, so the context exhibited below is an explicitly labelled
**NON-FIDELITY / BEYOND-PAPER audit** with zero canonical credit and no legal
non-vacuity credit.  See GAP register item 6.

**What this part no longer does.**  At the previous pin this part closed with a
labelled NON-FIDELITY audit theorem asserting that the deferred
`auxSourceECutRow_at_cutoff` bundle was simultaneously satisfiable over
`auditContext` and `auxOnlyEmission`.  That theorem is **deleted with the
declaration it disclaimed**: a probe whose own docstring denies legality cannot
be the satisfiability evidence for a premise bundle, and keeping it after the
deferral would leave an audit of a statement that is not here.  The four
objects it was built from -- `auxOnlyEmission`, `auditConfig`, `auditContext`
and `auditContext_envelope` -- **remain**, because each states something true
and self-contained about our encoding, and because they are the scaffolding the
`S5-LEVEL-STEP` arc will replace object by object with the paper's own.  None of
them takes canonical credit.

Their consumption is *internal to this chain and stops inside it* (r2 finding
F6, correcting a looser earlier wording that called all four unconsumed):
`auditConfig` is consumed by `auditContext` (as its `K` field), and
`auditContext` is consumed by `auditContext_envelope`.  What is true of all four
is that **nothing outside this chain consumes any of them** -- the chain's two
endpoints, `auxOnlyEmission` and the terminal theorem `auditContext_envelope`,
have no consumer at all. -/

/-- **CANONICAL INHABITANT: the paper's own executed `ECut` record.**

`06:1883--1887`: "The compiler inserts `(4 B_s, d_s)` into `E(c)`, with cutoff
root `r_s = ECut(4 B_s, d_s)`."  This is that record -- the paper's argument
pair, the paper's root, the paper's class -- built from the two **projections
of `auxSourceECutArg c`**, so the defining pair is written once and consumed,
never repeated.

It is **not** a probe and takes canonical credit for `SearchRow` only.  It
takes **no** credit for `MechanicalCompilerResidue.Cert`, whose canonical
inhabitant is `Compile(c)` and stays deferred, and none for `thm:eff-ledger`. -/
noncomputable def auxSourceExecutedRecord (c : ℕ) : MechanicalCompilerResidue.SearchRow :=
  eCutSearchRow (auxSourceECutArg c).1 (auxSourceECutArg c).2

/-- **Aux 20 (the canonical record stores the paper's own root `r_s`).**

Its returned integer is literally `ECut(4 B_s, d_s)` of `06:1886`, its
predicate is the frozen `ECut` brace at that argument, and its class tag is
`ECut`.  So the inhabitant is the paper's object rather than a record that
merely typechecks.  Stated through the emitted-pair accessor and proved by
consuming `auxSourceECutArg_eq`.  General in the exponent. -/
theorem auxSourceExecutedRecord_isThePaperRoot (c : ℕ) :
    (auxSourceExecutedRecord c).returned
        = eCut (4 * MechanicalCompilerResidue.bsSched)
            (ScheduleMajorantResidue.dsExp c) ∧
      (auxSourceExecutedRecord c).predicate
        = ECutPred (4 * MechanicalCompilerResidue.bsSched)
            (ScheduleMajorantResidue.dsExp c) ∧
      (auxSourceExecutedRecord c).kind = MechanicalCompilerResidue.CutKind.ecut := by
  obtain ⟨h1, h2⟩ := auxSourceECutArg_eq c
  refine ⟨?_, ?_, rfl⟩
  · change eCut (auxSourceECutArg c).1 (auxSourceECutArg c).2 = _
    rw [h1, h2]
  · change ECutPred (auxSourceECutArg c).1 (auxSourceECutArg c).2 = _
    rw [h1, h2]

/-- **Aux 21 (the canonical record is nondegenerate).**

Its stored root really satisfies the frozen predicate at the emitted pair -- in
particular the second condition of `06:1802` holds at it -- so the record is
not an empty search returning the Lean default.  This is non-vacuity at a
**legal** parameter value: the argument pair is the paper's own, evaluated
through `auxSourceECutArg`, not ours.  General in the exponent. -/
theorem auxSourceExecutedRecord_nondegenerate (c : ℕ) :
    ECutPred (auxSourceECutArg c).1 (auxSourceECutArg c).2
      (auxSourceExecutedRecord c).returned :=
  eCut_spec _ _

/-- **The emission carrying only the auxiliary source row.**

`06:1861--1862` says the compiler "first emits one auxiliary source row that is
not a candidate target"; this is an emission carrying exactly that row, through
`auxSourceECutArg`, and nothing else.

**BEYOND-PAPER and NON-FIDELITY.**  The paper's own `E(c)`, `P(c)`, `D(c)`,
`F(c)` also carry the `T1_Q2` entries, the two `T2_BT`/`T3_B1` classes, the
absorbed successor tuple and the common-depth request -- the paragraph
`06:1917--1941`, which runs from "`E(c)` receives the comparisons ..." on
`06:1917` to the sentence "Fixed rational gates emit their directly checked
constant cutoff; collect these in the finite set `F(c)`", whose "collect these
in the finite set" begins on `06:1940` and whose final line `06:1941` carries
only `\(\mathcal F(c)\).` (r2 finding F4).  (The r1
citation `06:1906--1943` opened on the `\end{equation}` of
`eq:aux-source-s-le-n` and closed on "Thus the cutoff is the literal integer",
so it straddled both neighbouring blocks -- r1 finding V-1.)  None of that is
built, so this truncated emission is **not** the paper's `E(c)` and is not
claimed to be.

**It is consumed by no theorem in this module.**  Its only consumer was the
labelled audit of the deferred `auxSourceECutRow_at_cutoff`, deleted with it
this round; it is retained as the scaffolding the `S5-LEVEL-STEP` arc replaces
with the compiler's own emission.  It claims **no** legality, **no**
canonical-inhabitation credit and **no** legal non-vacuity credit. -/
noncomputable def auxOnlyEmission : CutoffEmission where
  fixedRational := fun _ => []
  eArgs := fun c => [auxSourceECutArg c]
  pArgs := fun _ => []
  dArgs := fun _ => []

/-- **NON-FIDELITY AUDIT configuration.**

The banked `PublicRecords.levelConfigWitness` with its `B_s` field replaced by
the compiler's own K1 value `B_s = T^2` (`02:815--819`, the banked
`MechanicalCompilerResidue.bsSched`), which is *evaluated*, not chosen; `B_s >
0` (`05:411`) is discharged from the banked `tLeastSpec`.

**NON-FIDELITY / BEYOND-PAPER.**  The other five configuration entries are the
banked witness's, and the paper fixes them by its own lexicographically-least
gate search (`06:66--69`), so this configuration is *not* the compiler's
tuple.  Zero canonical credit. -/
noncomputable def auditConfig : PublicRecords.LevelConfig :=
  { PublicRecords.levelConfigWitness with
    Bs := MechanicalCompilerResidue.bsSched
    Bspos := by
      have h64 := MechanicalCompilerResidue.tLeastSpec.1
      have htpos : 0 < MechanicalCompilerResidue.tLeast := by omega
      simpa [MechanicalCompilerResidue.bsSched] using pow_pos htpos 2 }

/-- **NON-FIDELITY AUDIT context.**

The banked `Section5Admissibility.scheduleContextProbe`'s public record and
Stage-2 widths -- both already-judged nondegenerate witnesses -- over
`auditConfig`.  Its public accessors are then *evaluated*: `b_out = 1`,
`B_pub = max{D, Y}`, `z_R = max{clog_2 m_R, clog_2 n_R}` at the probe's
genuinely two-valued matrix, and `clog_2(|E| + 2)`.  In particular `z_R` is
**not** `0`, so the record is not at the cardinality-contradictory point the r0
witness sat at.

**NON-FIDELITY / BEYOND-PAPER AUDIT INSTANCE, zero canonical credit.**  The
paper's own schedule context is the materialized schedule of `06:859--887`,
which **consumes** `LevelStep`'s output; that canonical inhabitation is
**deferred to the `S5-LEVEL-STEP` arc** (GAP register item 6, with
`S5-EXT-CALL-THREE` naming `06:859--887` itself -- both rows OPEN) and is not
discharged here.  This
context audits *our encoding* at a point the paper never visits, and discharges
**no** legal premise-bundle non-vacuity obligation.

[**R4 RECORD REPAIR at `cc-t8e`, 23 August 2026, comment-only** -- this
paragraph used to say the materialized schedule "needs `LevelStep`", which read
as "`LevelStep` is unbuilt".  It is **built and banked**
(`LevelStepConstruction.levelStep`, `LevelStepConstruction.lean:1426`,
`cc-t7c-r4` 78/0/0); the dependency is real but it is a *consumption* direction,
and the residual of both cited rows is the canonical **application**, not the
constructor.  See GAP register item 6 above for the full ruling.  Nothing here
weakens: this context remains BEYOND-PAPER, still takes zero canonical credit,
and is still not a legal scheduled instance.]

This module consumes the context only through `auditContext_envelope`, which
states a property of the context itself.  [**Consumer update, `cc-t8e`:** the
downstream `LevelStepAuxSourceChain.auxSourceChain_at_auditContext` now consumes
`auditContext`, `auxOnlyEmission` and `auditContext_envelope` from outside this
module -- the three objects this module recorded as having "no consumer at all".
That consumer is itself labelled BEYOND-PAPER / NON-FIDELITY and changes nothing
about this declaration's own credit.] -/
noncomputable def auditContext : Section5Admissibility.ScheduleContext (Fin 3) (Fin 3) where
  P := PublicRecords.publicInputYes
  K := auditConfig
  W := StageTwoRelaxed.widthsWitness

/-- **Aux 22 (the audit context's four public accessors are inside the
envelope).**

Each of the four is *evaluated* through its own defining display and then
compared with the frozen `16` branch of `A_pre` (`06:113`; the r0 citation
`06:112` pointed at `&=\max\left\{` -- r0 finding 4), which the banked
`EnvelopeRealization.sixteen_le_envE` puts under `E_c(n)` above the scheduled
exponent floor.  So the five envelope hypotheses of the banked
`lSandwich_upper` are met at this context for every source size. -/
theorem auditContext_envelope (c n : ℕ) (hc : 3 ≤ c) :
    auditContext.P.bout ≤ envE c n ∧
      Section5Admissibility.BpubOf auditContext ≤ envE c n ∧
      Section5Admissibility.zROf auditContext ≤ envE c n ∧
      Section5Admissibility.clEOf auditContext ≤ envE c n := by
  have h16 : 16 ≤ envE c n := sixteen_le_envE n hc
  have hb : auditContext.P.bout ≤ 16 := by
    change (1 : ℕ) ≤ 16
    norm_num
  have hBp : Section5Admissibility.BpubOf auditContext ≤ 16 := by
    change ScheduleTemplateResidue.Bpub 3 0 ≤ 16
    simp [ScheduleTemplateResidue.Bpub]
  have hz : Section5Admissibility.zROf auditContext ≤ 16 := by
    change ScheduleTemplateResidue.zRpub 2 2 ≤ 16
    refine max_le ?_ ?_ <;>
      exact Nat.clog_le_of_le_pow (by norm_num)
  have hcl : Section5Admissibility.clEOf auditContext ≤ 16 := by
    change Nat.clog 2 (Fintype.card (Fin 3) + 2) ≤ 16
    refine Nat.clog_le_of_le_pow ?_
    simp
  exact ⟨by omega, by omega, by omega, by omega⟩

/-! ### DEFERRED (deleted this round, not repaired): the NON-FIDELITY audit of
the deferred bundle

The theorem that stood here asserted that every hypothesis of the deferred
`auxSourceECutRow_at_cutoff` was simultaneously satisfiable over `auditContext`
and `auxOnlyEmission`, with a nondegenerate conclusion, under an explicit
NON-FIDELITY / BEYOND-PAPER label and with zero canonical credit.

It goes with the declaration it audited, and the reason is the reason for that
deferral rather than a second one: its own label denied it any legal
non-vacuity credit, so it never was -- and could not become -- the legal
inhabitant that bundle owes.  Keeping it after the deferral would leave an audit
of a statement no longer present, and a reader could mistake a labelled probe
for the missing witness.  The legal inhabitant arrives with the materialized
schedule of `06:859--887` on the `S5-LEVEL-STEP` arc, at which point the
deferred theorem and its canonical -- not audited -- inhabitation land together.

`auditContext` and `auxOnlyEmission` remain.  `auxOnlyEmission` has no consumer
at all; `auditContext` is consumed only inside the audit chain itself, by
`auditContext_envelope`, which is in turn consumed by nothing (r2 finding F6).
Nothing in this module now claims that any hypothesis bundle of a deferred
statement is satisfiable. -/

/-! ## Closing census: what this module discharges, and what stays owed

**Discharged.**

* `06:1812`, "Each search terminates", for `ECut` (`eCut_nonempty`) and for
  `DCut` (`dCut_nonempty`).  This is `EnvelopeRealization`'s GAP-EXPOSED 3,
  both halves, and with the banked `PCut` case it completes the frozen
  sentence: `persistentCutoffs_terminate`.
* `06:1812--1813`, "each predicate remains true for every larger `r`", for
  `ECut` (`eCutPred_persist`) and `DCut` (`dCutPred_persist`), with the banked
  `PCut` case: `persistentCutoffs_persist`.  Both proofs are the frozen
  reasons of `06:1813--1816`, not substitutes for them.
* `eq:aux-source-s-normalized` (`06:1878--1882`) and `eq:aux-source-s-ecut`
  (`06:1890--1893`) at the compiler's application site, **by consuming** the
  banked `ScheduleMajorantResidue.auxSourceRow` and `.auxSourceEcutRow` in the
  proof terms, with the frozen input `u <= 2L` (`06:1867--1876`) supplied here
  and the public accessors evaluated through
  `Section5Admissibility.ApreOf`/`BpubOf`/`zROf`/`clEOf`.
* Canonical inhabitation of `MechanicalCompilerResidue.SearchRow` at the
  paper's own emitted argument (`auxSourceExecutedRecord`, through
  `auxSourceECutArg`), and the three generic executed-record constructors it is
  built through.

**Deferred to the `S5-LEVEL-STEP` arc (deleted this round, not repaired).**

* `auxSourceECutRow_at_cutoff` -- `auxSourceECutRow` restated under the cutoff
  hypothesis `n >= n_step(c)` of `06:1960--1962` -- and its sole consumer, the
  labelled NON-FIDELITY audit of that theorem's premise bundle.  Both are
  **absent from this module**, deliberately: the bundle needs a canonical
  `Section5Admissibility.ScheduleContext` and a canonical `E(c)`, i.e. the
  materialized schedule of `06:859--887` and the unbuilt `LevelStep`, so it had
  no **legal** nondegenerate inhabitant here, and a probe that disclaims
  legality cannot supply one.  The mathematics was not at fault and is not
  discarded: the statement is one application of `auxSourceECutRow` -- which
  **does** land, at the paper's own guard `06:1888--1889` -- composed with the
  banked `EnvelopeRealization.cutoff_eligibility`, and it returns with the
  paper's own context.
* Consequently `eq:nstep` (`06:1955`), the sentence `06:1960--1962`, and
  `CutoffEmission.nStep` are consumed by **no** declaration in this module.

**Explicitly NOT discharged (r0 finding 10, applied; r1 finding Sol-4,
corrected).**

* **Legal non-vacuity of an auxiliary-source premise bundle at a paper
  context.**  Nothing in this module claims it, and after the deferral above
  nothing in this module even audits it.  `auditContext` and `auxOnlyEmission`
  survive as labelled BEYOND-PAPER scaffolding consumed by nothing outside
  their own audit chain (`auditConfig` -> `auditContext` ->
  `auditContext_envelope`, whose endpoints have no consumer at all -- r2
  finding F6).  The canonical
  obligation -- a `Section5Admissibility.ScheduleContext` from the materialized
  schedule of `06:859--887`, together with the compiler's own `E(c)` -- is
  **deferred to the `S5-LEVEL-STEP` arc**, with `S5-EXT-CALL-THREE` naming
  `06:859--887` itself; both rows exist in the route ledger and both are
  **OPEN**.  This deferral is registered as the OPEN obligation
  `PARAM-COMPILER-CUTOFF-ROW-AT-NSTEP`.  It depends on `S5-LEVEL-STEP` and, for
  the materialized schedule, `S5-EXT-CALL-THREE`; both prerequisites are OPEN.
  The r1 text's claim that an obligation named
  `PARAM-COMPILER-CONTEXT-INHABITATION` was registered is deleted as false, and
  the r2 text's claim that no identifier was minted at all is corrected here
  (GAP register item 6; r2 finding F1).
* The `ENVELOPE-REALIZATION-001` GAP-EXPOSED 3 discharge is claimed for the two
  *termination* halves only, which are proved above outright; it carries no
  claim about the context layer.

**Still owed, and named.**

* `thm:eff-ledger` itself (`02:569--650`).  `K_*`, `Cert`, `A_cert`, `R`,
  `n_step`, `SchemaChecked`, `NumChecked` and `Successor_16` are not claimed
  here; `A_cert`, `SchemaChecked` and `NumChecked` have **no declaration and no
  axiom** on this route.  `MECHANICAL-COMPILER-RESIDUE-001` keeps the
  `Compile(c)` canonical-inhabitation obligation for `Cert`.
* `ExecutedRoots` (`02:589--591`) and the executed-versus-symbolic tag of
  `02:1022--1024`: **not reified**, for the reason in GAP register item 2.  So
  `eq:R-exact` is still read off the banked `CutoffEmission`, and the
  identification of that list with `ExecutedRoots(Cert_c)` is owed.
* The runtime bound of `02:1400--1412` -- `J_c`, `B_c`, `K_cert`, `r_cert` and
  the composed `time` inequality -- is untouched.  Only its stated reason is
  supplied.
* The continuation `06:1894--1915` (`eq:aux-source-s-le-n` at `06:1903--1906`,
  `eq:aux-source-s-minus-three` at `06:1908--1911`, and the auxiliary record
  `AUX.PRE.SOURCE.S_MINUS3_LE_NE` named at `06:1912--1915`; the r1 citation
  stopped at `1905`, inside the first display -- r1 finding V-2) is **already
  banked route content** in
  `ScheduleMajorantResidue`; it is **not newly claimed or consumed** by any
  declaration here (GAP register item 5).
* `06:1796`'s positivity scope is not imposed anywhere below: every theorem is
  proved for all natural arguments, which is strictly stronger and never
  weaker, and no declaration derives content from positivity it did not
  assume.
-/

end EthInapproximability.ParameterizedNP.ScheduleCompilerExistential
