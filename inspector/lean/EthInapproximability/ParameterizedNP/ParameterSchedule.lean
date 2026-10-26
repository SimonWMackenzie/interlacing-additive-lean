import EthInapproximability.ParameterizedNP.WrapperProtectedEarly

/-!
# Parameterized NP route: the Section-6 parameter schedule, reified

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/06-parameter-schedule.tex`, `sec:parameters`.
  Every declaration below is one **defining display** of that section, opened
  first-hand at the line range printed in its docstring.  The anchors traced
  here, in the frozen print order, are:
  * `06:56--69`, the universal configuration integers `C_0, c_seed, A_wrap,
    B_s, c_b, C_in` with `c_b >= 6`, and `06:62`, "put `c_theta = delta/8`";
  * `eq:s-choice` (label `06:120`, display `06:109--121`), the three-step
    source-scale chain `A_pre -> u -> s = 2^{ceil(B_s u^2)}`, with `06:122`
    ("Thus `s` is a public power of two"), the divisibility `06:975`
    ("The penultimate comparison uses `64 | s`, hence `s >= 64`") and the
    source-scale gate `eq:hard-seed-width-gates` (label `06:268`, display
    `06:264--269`) that `16 | (s/4)` records;
  * `06:465--472`, the wrapper threshold
    `P_0 = max{16, C_cert, s, log_2 q_2, ceil(log_2 U_0), z_R}` and the width
    exponent `L_P = clog_2(P_0)`;
  * `06:578` ("The fixed choice `c_seed = 100`") together with `06:1671`
    ("Choose `A_wrap > c_seed` as the least integer satisfying
    `eq:Awrap-coefficient-search`"), the two displays that fix the floors of
    the reference-endpoint gate firing;
  * `eq:Hmax` (label `06:761`, display `06:754--762`), `v_max`, `L_h` and
    `H_max`, with `06:808` ("Since `H_max >= L_h + B_cap`");
  * `06:72--80`, the two exact integer primitives `clog_2(z) = min{j >= 0 :
    z <= 2^j}` and `j_49(k) = max{j >= 0 : 10000 j^2 <= 2401 k}`, with
    `eq:j49-window` (label `06:84`) and the search certificate
    `eq:j49-search-data` (label `06:97`, display `06:92--96`);
  * `eq:eta-choice` (label `06:219`, display `06:204--220`), the two deletion
    tolerances `eta_C` and `eta_R`, together with `06:221--225` ("Since
    `rho_temp = 1/1000`, the first term in the definition of `eta_C` is
    `nu_T rho_temp/s`") and the chain `06:227--235`
    (`0 < eta_R <= eta_C/2 < tau < x_N`, "No later step decreases either
    tolerance");
  * `eq:q-deltaU` (label `06:518`, display `06:514--519`),
    `q = 2^{A_wrap L_P^2}` and `delta_U = eta_R/(16 q)`, with `06:520--522`
    ("The integer `A_wrap` is fixed universally below ... it never depends on a
    reached transcript");
  * `eq:Q-theta-choice` (label `06:537`, display `06:525--538`):
    `lambda_def`, `L`, `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}`,
    "`Q` = the least power of two at least `Q_0`",
    `theta = c_theta/(2Q) = delta/(16Q)`, `L_theta = clog_2(1/theta)`;
    `06:539`, "Here `1/theta = 160 Q` is an integer because `delta = 1/10`";
    `eq:direct-theta-gates` (label `06:545`, display `06:541--546`),
    `Q theta = delta/16 < delta/2` and `4 Q_0 theta <= delta/4 < delta`;
    and `06:547`, "We also impose the finite gate `delta_U <= 1/200`";
  * `eq:tref-search` (label `06:571`, display `06:559--570`), the certified
    reference width, with its tested endpoint `eq:kref-tested-endpoint`
    (label `06:590`), the four persistence records
    `eq:kref-fixed-persistence` (label `06:607`), the feasible `j_49`
    candidate `eq:kref-j49-candidate` (label `06:620`) and the minimality
    argument `06:622--629`;
  * `eq:cover-bounds` (label `06:653`, display `06:639--654`), the three cover
    numbers and `e_0^max`; the generic tested endpoint
    `eq:cover-tested-endpoint` (label `06:669`, display `06:666--670`) with its
    exact Bernoulli proof `06:671--681`; the three literal instances
    `eq:cover-instance-tested-endpoints` (label `06:692`, display
    `06:682--693`); and `06:698--700`, `rho_* = max{rho_sing, 1 - eta_C}
    = 1 - eta_C`, together with the legality premises `06:658--661`;
  * `eq:terminal-uniform-bounds` (label `06:730`, display `06:716--731`):
    `vartheta = 9/16`, `B_theta = B_pair` and `L_q = ceil(log_2(2q)) + 1`
    (both pinned to their banked objects by checked equation, `06:718--719`),
    `E_B`, `E_T`, `delta_term`, `u_term`;
  * `eq:terminal-wrapper-gates` (label `06:742`, display `06:738--743`), the
    three named search gates `q >= 8 max{1, E_T}`,
    `q > 4 E_T u_term B_theta` and `q/4 >= t_ref`, with `06:744--747`
    ("Their eventual validity is why `A_wrap` is chosen after the universal
    coefficient audit ... no parameter in `eq:terminal-uniform-bounds` depends
    on which terminal state a protocol happens to reach") and `06:631--634`
    ("The downstream gate `q/4 >= t_ref` remains the separately named third
    row of `eq:terminal-wrapper-gates`; it is not hidden inside the endpoint
    record");
  * `eq:t2-search` (label `06:772`, display `06:764--773`), the single
    Stage-2 width search, with `eq:k2-tested-endpoint` (label `06:779`),
    `eq:k2-j49-candidate` (label `06:794`), the named integer lemma
    `eq:k2-fixed-growth-lemma` (label `06:802`) and the **whole endpoint
    verification** `06:781--812`, all three clauses of which are proved here;
  * `06:1253--1268`, the least-power-of-two record discipline, with
    `eq:least-power-tested-returned` (label `06:1263`) and the four-row
    instance table `06:1271--1278`.

  Everything else in `sec:parameters` is **out of scope for this module** and
  nothing here states it: the Stage-1 scales `eq:stage1-scales`, the three
  Stage-1 seed calls, the Stage-2 structural gates
  `eq:stage2-structural-gates`, the physical Stage-4 gates
  `eq:physical-stage4-gates`, the low-rung margins, the Localized-Extension
  call table `sec:extension-call-ledger`, and the whole normalization
  algorithm and literal coefficient pass of `sec:effective-cutoff`.

* **Modules consumed by pin, never restated.**  The Section-6 displays that
  another banked row already owns are *used*, not redefined:
  * `EntryGates.Q0`, `.rQ`, `.Qwidth`, `.deltaFixed` (`BRIDGE-ENTRY-001`).
    `eq:Q-theta-choice` prints `Q_0` and "the least power of two at least
    `Q_0`" **letter for letter** as `10-direct-bridge.tex:47--51`, so the
    Section-6 occurrence is the *same object*; `entry_rQ_eq_leastPowTwoExp`
    and `schedule_Q0_eq_entry_Q0` record the identification definitionally
    rather than introducing a second `Q_0`.
  * `RawLowProfileBody.J49Feasible` and its three search-certificate lemmas
    (`RAW-LOW-PROFILE-001`) -- the predicate `P_k(j)` of `06:89`.  Only the
    *value* `j_49(k)` is new here.
  * `WrapperProjectionCovers.coverExponent`, `.e0Max`, `.rhoSmall`,
    `.rhoPair` (`WRAPPER-PROJECTION-COVERS-001`) -- the three least searches
    of `eq:cover-bounds` and the `e_0^max` arithmetic.
  * `WrapperProtectedEarly.muP`, `.Lq`, `.Btheta`, `.rhoZero_eq_rhoPair`
    (`WRAPPER-PROTECTED-EARLY-001`) -- `06:718--719` prints `B_theta = B_pair`
    and `L_q = ceil(log_2(2q)) + 1`, and `schedule_Btheta_eq_Bpair` and
    `schedule_Lq_eq_display` record both identifications as checked equations
    rather than editorial remarks, so the `Btheta`/`Lqv` arguments of `EB` are
    not free inventions.
  * `DenseStageFourOpening.rhoTemp`, `.xN`, `.tauMass` and
    `DenseSynchronisation.nuTempR`, `.nuSrcR`, `.muR`
    (`STAGE4-PROTECTED-OPENING-001`, `DENSE-SYNC-001`) -- the fixed protected
    masses of `eq:fixed-protected-masses`, which `eq:eta-choice` reads.
  * `HardSeedFacade.mHS` (`HARD-SEED-FACADE-001`) -- the exponent threshold
    `m_HS` that the `k_2` floor of `eq:t2-search` names.

## Reader counterparts

`routes/parameterized-np/reader-facing/sections/`.  Each cited item was opened
and checked to state the same fact, one reader item per declaration group, and
**no reader item is claimed twice** here or by any earlier row.

* `03-parameterized-construction.tex:64--67`, the display
  "`b_1 = 2^{j_49(a-2)}, k_T = log_2(s/4), b_T = 2^{j_49(k_T)}, x_T = 2^{-b_T}`"
  -> `j49` and its three search-certificate theorems.  (The reader's own
  `eq:paper-j49-definition`, label line 45, is the *definition*; it is
  unclaimed by any module and is taken here together with the display at
  64--67 as one item, since 64--67 is the only place the reader *uses* it.)
* `03-parameterized-construction.tex:81--82`, "Choose the protected
  multiplicities and dyadic scale-alignment width `q = 2^{r_q}` by the total
  parameter schedule of `thm:paper-effective-level`" -> `qWrap`.
* `03-parameterized-construction.tex:92`, "There are public rationals
  `0 < delta_U < 1` and `0 < theta <= 1/4`" -> `deltaU` and `theta`, together
  with their positivity/upper-bound theorems.
* `05-iteration.tex:226--229`, "The producer computes the protected deletion
  tolerances, the common row threshold, and the least dyadic bridge width, and
  verifies `4 Q_0 theta <= delta` together with every source-survival,
  scale-alignment, and defect-induction gate" -> `etaC`, `etaR`, and the
  canonical-inhabitation theorem `schedule_fires_directEntryGates`.
  **Boundary with `SIZE-001`:** that row holds the *displayed successor bound
  and the logarithmic-cardinality sentence* at `05-iteration.tex:221--226`
  (`SizePropagation.lean:1164`).  The item claimed here is the **next
  sentence**, which begins inside line 226 with "The producer computes the
  protected deletion tolerances" and runs to line 229; it is a different
  reader item, and neither row claims the other's.

**Reader items deliberately declined, with the reason recorded** (precedent:
`CLOCK-001`/`cc-t1x`, `SOURCE-SLAB-001`/`cc-t2b`, `RECORD-LAYER-001`):

* `leastPowTwoExp`/`leastPowTwoGe` claim **no** reader item.  The reader never
  displays the generic accessor; it writes "the least power of two at least
  `Q_0`" once, at `04-bridge.tex:94`, and that locus is already held by
  `BRIDGE-ENTRY-001` for `rQ`/`Qwidth`.  Citing it again would assign one
  reader item to two declarations, which the reader-counterpart rule forbids.
* `Apre`, `uAux`, `sScale`, `P0sched`, `LPwidth`, `cSeed`, `vMax`, `LhSched`,
  `HmaxSched`, `krefFloor`, `krefPred`, `kref`, `krefStar`, `k2Floor`,
  `k2Star`, `j2Star` and the terminal bounds `EB`, `ET`, `deltaTerm`, `uTerm`,
  `e0maxSched` claim **no** reader item.  (`A_pre`, `P_0`, `L_P`, `B_s`,
  `H_max`, `c_seed` and `A_wrap` were searched for across all ten reader
  section files and appear in **none** of them; the only `P_0` in the reader,
  at `B-bridge-details.tex:20--23`, is a set in a partition and a different
  object entirely.)  The reader compresses the entire finite gate list
  behind `thm:paper-effective-level` ("The finite gate list for one level is
  an acyclic expression graph ... Evaluating it gives the following total
  compiler", `05-iteration.tex:194--196`) and never prints a single one of
  these searches, floors, or cover bounds.  There is no reader sentence that
  states the same fact, so none is cited; citing the compiler theorem's
  *summary* would be citing prose as a statement.
* the two legality theorems of `06:658--661`, `etaC_le_nu_lt_one` and
  `one_sub_etaC_legal`, claim **no** reader item.  They are general properties
  of `etaC`, whose reader item (`05-iteration.tex:226--229`) is already taken
  above and may not be assigned twice; and the reader prints neither display,
  its only occurrence of `eta_C` being the *use* `D_N(1; 1-eta_R, 1-eta_C) >= C`
  at `A-stage4-details.tex:217--220`, which is a dense-Stage-4 profile display
  belonging to another block, not a statement of these premises.
* `terminalWrapperGates` claims **no** reader item, for the same reason: the
  reader's `03-parameterized-construction.tex:72--73` lists the *Stage-2*
  structural gates (`16 | t_2`, `4 t_2 <= q_2`, `t_2 <= 2^{b_1}`), which are a
  different display (`eq:stage2-structural-gates`) and are not stated here.

Crosswalk row: `READER_CROSSWALK.md`, "Simultaneous parameters and size".

## Status and dependencies

* Ledger row: **`SCHEDULE-001`**
  (`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`).
* Proof status: **new (elementary)** throughout.  Every declaration is either
  a plain transcription of a frozen defining display, a general property of
  one of those transcriptions, or one of the section's own displayed
  derivations (`06:221--225`, `06:227--233`, `06:541--546`, `06:615--629`,
  `06:658--681`, `06:789--803`, `06:1265--1268`) carried out in the kernel.
  No communication-complexity lemma is introduced, adapted, or re-proved, and
  no admissibility gate of any other section is claimed.
* Imports: `EthInapproximability.ParameterizedNP.WrapperProtectedEarly` only,
  hence transitively `EthInapproximability.Prelude`, `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported, so the AGHP balanced-family axiom is not in scope.
* External adapters: none.  Nothing here is axiomatized.  `EXPANDER-001` has
  no Lean declaration by design and is not touched; `A_wrap`, `c_seed`,
  `C_0`, `B_s`, `c_b`, `C_in` stay **explicit binders**, never silent
  constants, exactly as `06:56--69` requires ("The mathematical one-level
  theorem treats these integers as explicit input data").
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`):
  at most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings considered, and why this one landed

**`j_49`.**  `06:77--78` writes a *maximum* over a set with an explicit finite
support bound (`06:94`: "`k` is an explicit finite-support bound").
* *Candidate A (landed).* `Nat.findGreatest (J49Feasible k) k`.  This is the
  bounded maximum with exactly the frozen support bound, and its three
  Mathlib eliminators are, one for one, the three rows of
  `eq:j49-search-data`: `Nat.findGreatest_spec` is "zero proves
  nonemptiness", `Nat.le_findGreatest` is the maximality eliminator, and
  `Nat.findGreatest_le` is `j_49(k) <= k`.  All three aux lemmas proved in
  one line each, with no side condition.
* *Candidate B (rejected).* `sSup {j | J49Feasible k j}`.  Provable too, but
  every eliminator needs `BddAbove` re-derived at each use, and `sSup` on `ℕ`
  is the junk `0` off the bounded case -- the frozen text's finite-support row
  would then be a *hypothesis of the eliminators* rather than a theorem, which
  inverts `06:99--103`.  Ranking (aux lemmas proved, faithfulness, length):
  A = 3/3, guard-free, 3 lines; B = 3/3, re-derived guard at each use, 12
  lines.  A landed.

**`theta`.**  `06:533` prints two forms, `c_theta/(2Q)` and `delta/(16Q)`.
The *first* is landed as the definition and the second as a theorem, because
`c_theta` is the configuration field of `06:62` and reading the schedule
backwards from the simplified form would silently discard it.  `theta_eq_delta`
and `theta_inv_eq` recover both other spellings.

## Faithfulness notes (mechanical rules M1--M10)

* **No synthetic tuple.**  There is no `structure` in this module and no
  aggregate "schedule record": `06:4--13` fixes the parameters one display at
  a time in a stated dependency order, and a bundle would both invent an
  object the paper does not have and let a derived telescope be restated as a
  field.  Every deliverable takes **explicit binders**.
* **Use-sites are never definitions.**  `q/4 >= t_ref` is read from its
  *defining* display `eq:terminal-wrapper-gates` (`06:738--743`) and from the
  sentence `06:631--632` that names it as the third row there -- never from a
  consumption site.  Likewise `Q_0` is read from `eq:Q-theta-choice`, not from
  the `4 Q_0 theta <= delta` inequality that consumes it.
* **Both interlace widths are kept apart.**  `qWrap` is the scale-alignment
  width `q` of `eq:q-deltaU`; `EntryGates.Qwidth` is the bridge width `Q` of
  `eq:Q-theta-choice`.  They have different definitions, different arguments
  and different types of dependence, and no theorem here conflates them.
* **Ceilings are preserved.**  `EB` and `ET` keep the frozen `Nat.ceil`; no
  ceiling is replaced by its argument or by `x + 1`.
* **Nonemptiness and positivity survive.**  `etaC_pos`, `etaR_pos`,
  `theta_pos`, `deltaTerm_pos` are proved from the frozen side conditions
  (`3 < s`, `0 < delta_v(G)`, `0 < zeta`), never assumed.
* **No conclusion in constructor data.**  `terminalWrapperGates` is a `Prop`
  abbreviation for the three inequalities the paper displays and nothing more;
  `terminalWrapperGates_iff` shows it is exactly that conjunction, and
  `terminalWrapperGates_refuted_at_unit_width` shows it is not free.
* **Trivial-witness pole.**  The only existential-flavoured deliverables are
  the least searches, and each is a *pinned* construction: `kref_le_star` and
  the `leastPowTwo` minimality lemmas are refuted, not satisfied, by a
  gratuitously large candidate, so "take something huge" is not a witness.
* **Vacuous-hypothesis pole.**  The full hypothesis bundle of the canonical
  instance is exhibited satisfiable *together with its conclusion* by
  `scheduledPoint_hypotheses_consistent`, so no `False` derives from it.  That
  probe assigns **no numeral to any defined quantity**: `s` is pinned by
  equation to `eq:s-choice` evaluated (`sScale (uAux (Apre ...))`) and `q` to
  `eq:q-deltaU` evaluated at the *defined* exponent `L_P = clog_2(P_0)`, and
  the legality facts `3 < s`, `64 | s`, `4 <= L_P` are then *read off* those
  chains rather than imposed.  Only the frozen legality of the free
  configuration fields is hypothesised (`1 <= B_s` from `06:56`, `1 <= b_out`
  from `10-direct-bridge.tex:41`, `c_seed < A_wrap` from `06:1671`), and
  `delta_v(G)` and `zeta` stay universally quantified.  Conversely the
  conclusion is not free: the banked
  `EntryGates.directEntryGates_refuted_at_deltaU_eq_delta` makes it **false**
  at `delta_U = 1/10`, so the schedule's own `delta_U` is doing the work.

## Canonical inhabitation

`schedule_fires_directEntryGates` is the **paper's own instance**: the
Section-6 schedule feeding the Section-10 bridge entry apparatus.  Both halves
of `eq:direct-entry-gates` are discharged by *evaluating the definitional
chain* -- `eta_C` from the frozen protected masses, `eta_R` from `eta_C`,
`delta_U = eta_R/(16 q)`, `Q_0` from `delta_U`, `Q` from `Q_0`,
`theta = c_theta/(2 Q)` -- with **no numeral assigned to any defined
quantity** and with `s`, `delta_v(G)`, `zeta`, `b_out`, `A_wrap`, `L_P` left
symbolic.  `terminalWrapperGates_at_scheduled_point` is the same for the three
named search gates, with the exponents symbolic exactly as `06:744--747`
leaves them.

## GAP-EXPOSED

No parameter *admissibility* claim is made.  In particular:

* the four `KREF-*` persistence records of `eq:kref-fixed-persistence` enter
  `kref_le_star` as **explicit named hypotheses**; this module does not prove
  them, because their proofs are the cutoff argument of `sec:effective-cutoff`
  (`PARAM-001`, Lean pending).  The `k_2` endpoint is **not** in that class:
  `06:781--812` proves its three clauses inline with no cutoff record,
  `k2Star_meets_search` states that membership (`06:813`) once and proves it
  outright, and `k2_le_star_at_Hmax` carries it to the reified `eq:Hmax` with
  no hypothesis at all;
* the audit majorants on `E_T`, `u_term`, `B_theta` used by
  `terminalWrapperGates_at_scheduled_point` are likewise named hypotheses, in
  the exact shape `06:744--747` defers them to `thm:eff-ledger`;
* the middle row of `eq:cover-instance-tested-endpoints` (the `B_sing`
  endpoint at base `1 - eta_C`) is **not** claimed: its denominator code is
  not a fixed numeral, and the coefficient row it needs belongs to the
  literal coefficient pass;
* `eq:j49-window` itself (the real square-root window `06:82--85`) is **not**
  claimed here; only the exact integer search certificate `eq:j49-search-data`
  is;
* of the **three** rows of `eq:hard-seed-width-gates` (`06:264--269`) exactly
  one is landed: the divisibility row `16 | (s/4)`, in the equivalent
  power-of-two form `64 | s` that `06:975` records ("The penultimate comparison
  uses `64 | s`, hence `s >= 64`"), proved by `sScale_floor` off the
  `eq:s-choice` chain.  The other two rows, `k_T = log_2(s/4) >= m_HS` and
  `log_2 s < b_T`, are **not** claimed: they bind `k_T`, `m_HS` and `b_T`,
  which are outside this module's binder set, so no consumer may read either
  of them off this module;
* of the **three** rows of `eq:cover-tested-endpoint` (`06:666--670`) the
  exported theorem `cover_tested_endpoint` carries two: the stored value
  `B^* = b bl(v)` appears as the literal exponent of its conclusion, and the
  stored comparison `(a/b)^{B^*} < u/v` is that conclusion.  The third row,
  `1 <= B^*`, is **not** exported: it is discharged inline at each use site
  (the `1 <= B` conjunct of `coverExponent`, supplied at `Bref_le_tested` and
  `Bpair_le_tested`), so no consumer may cite this module for it;
* nothing about `thm:eff-ledger`, route completion, or any complexity or
  robustness conclusion is claimed.
-/

universe u

namespace EthInapproximability.ParameterizedNP.ParameterSchedule

open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.RawLowProfileBody
open EthInapproximability.ParameterizedNP.HardSeedFacade
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperProtectedEarly
open EthInapproximability.ParameterizedNP.EntryGates

/-! ## Section 0  The exact integer primitive `j_49`

`06:72--80` and `eq:j49-search-data` (`06:92--97`).  The predicate `P_k(j)` is
the banked `RawLowProfileBody.J49Feasible` and is **not** redefined; only the
value returned by the frozen maximum is new. -/

/-- **`j_49(k) = max{j >= 0 : 10000 j^2 <= 2401 k}`** (`06:77--78`; reader
`eq:paper-j49-definition`, `03-parameterized-construction.tex:44`, used at
`03:64--67`).

`06:94` supplies the explicit finite-support bound "`P_k(j) => j <= k`", so the
frozen maximum is a *bounded* maximum and is transcribed as one.  No real
square root is evaluated: `06:86` says "The square root appears only in the
analysis of this exact integer predicate." -/
def j49 (k : ℕ) : ℕ := Nat.findGreatest (fun j => 10000 * j ^ 2 ≤ 2401 * k) k

/-- **Aux J1 (`eq:j49-search-data`, first row: zero proves nonemptiness).**
The returned value is feasible.  General in `k`. -/
theorem j49_feasible (k : ℕ) : J49Feasible k (j49 k) :=
  Nat.findGreatest_spec (m := 0) (Nat.zero_le k) (J49Feasible.zero k)

/-- **Aux J2 (`eq:j49-search-data`, third row: the maximality eliminator).**
Every feasible candidate is at most `j_49(k)`.  `06:100--103`: "any lower bound
on `j_49(k)` used below must come from a displayed feasible candidate followed
by that eliminator."  General in `k` and `j`. -/
theorem j49_max {k j : ℕ} (h : J49Feasible k j) : j ≤ j49 k :=
  Nat.le_findGreatest h.le_index h

/-- **Aux J3 (`eq:j49-search-data`, fourth row).**  `j_49(k) <= k`, the
explicit finite-support bound.  General in `k`. -/
theorem j49_le (k : ℕ) : j49 k ≤ k := Nat.findGreatest_le k

/-! ## Section 1  The least-power-of-two accessors

`06:1253--1268`.  "every least-power-of-two record distinguishes its *tested
power* from the sharper majorant for the value returned by the search", with
the returned-result bound `eq:least-power-tested-returned`.  Three of the four
rows of the instance table `06:1271--1278` (`ASTAR`, `QDIRECT`, `UTERM`) have
real or rational thresholds and are served by this one accessor; the fourth
(`Q2`, at threshold `12 s N_E`) is the banked `GuardedSourceSlab.q2` and is
not redefined. -/

/-- **The exponent of the least power of two at least a real threshold**
(`06:1258--1260`: "If `p(t)` denotes the least power of two at least a
nonnegative threshold `t` ...").

Since `r ↦ 2^r` is monotone, the least power of two at least `x` is `2` raised
to the least admissible exponent.  This is the *same* encoding the banked
`EntryGates.rQ` uses for the `QDIRECT` row, and
`entry_rQ_eq_leastPowTwoExp` records that identification definitionally. -/
noncomputable def leastPowTwoExp (x : ℝ) : ℕ := sInf {r : ℕ | x ≤ (2 : ℝ) ^ r}

/-- **The least power of two at least a real threshold** (`06:1258--1260`).
A width, hence a natural number; comparisons against the real threshold cast
it. -/
noncomputable def leastPowTwoGe (x : ℝ) : ℕ := 2 ^ leastPowTwoExp x

/-- **Aux L1 (the exponent set is nonempty).**  Archimedean in `ℝ`; no
property of `x` is used, so the infimum is never the junk value `0` by
default.  General. -/
theorem leastPowTwoExp_setNonempty (x : ℝ) :
    ∃ r : ℕ, x ≤ (2 : ℝ) ^ r := by
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  exact ⟨r, hr.le⟩

/-- **Aux L2 (the defining upper property).**  `x <= 2^{exponent}`, with no
side condition.  General. -/
theorem le_two_pow_leastPowTwoExp (x : ℝ) : x ≤ (2 : ℝ) ^ leastPowTwoExp x :=
  Nat.sInf_mem (leastPowTwoExp_setNonempty x)

/-- **Aux L3 (least-search minimality).**  Every admissible exponent bounds
the returned one.  This is the substantive half of "*least* power of two":
without it any large power of two would do.  General. -/
theorem leastPowTwoExp_le {x : ℝ} {r : ℕ} (h : x ≤ (2 : ℝ) ^ r) :
    leastPowTwoExp x ≤ r :=
  Nat.sInf_le h

/-- **Aux L4 (the returned width meets its threshold).**  General. -/
theorem le_leastPowTwoGe (x : ℝ) : x ≤ ((leastPowTwoGe x : ℕ) : ℝ) := by
  have h := le_two_pow_leastPowTwoExp x
  rwa [leastPowTwoGe, Nat.cast_pow, Nat.cast_ofNat]

/-- **Aux L5 (`eq:least-power-tested-returned`, `06:1261--1268`).**

"`p(t) <= max{1, 2 ceil t}`.  Indeed, this is immediate when `p(t) = 1`;
otherwise `p(t)/2` is a power of two, so minimality gives `p(t)/2 < t` and
hence `p(t) < 2 t <= 2 ceil t`.  Thus the right side is *not* the tested
power."  The frozen proof, carried out in the kernel.  General for `0 <= x`. -/
theorem leastPowTwoGe_le_tested {x : ℝ} (hx : 0 ≤ x) :
    leastPowTwoGe x ≤ max 1 (2 * ⌈x⌉₊) := by
  rcases Nat.eq_zero_or_pos (leastPowTwoExp x) with h0 | hpos
  · simp [leastPowTwoGe, h0]
  · -- the predecessor exponent is inadmissible
    have hlt : leastPowTwoExp x - 1 < leastPowTwoExp x := by omega
    have hnot : leastPowTwoExp x - 1 ∉ {r : ℕ | x ≤ (2 : ℝ) ^ r} :=
      Nat.notMem_of_lt_sInf hlt
    have hstrict : (2 : ℝ) ^ (leastPowTwoExp x - 1) < x := by
      simpa only [Set.mem_setOf_eq, not_le] using hnot
    have hsplit : leastPowTwoExp x = (leastPowTwoExp x - 1) + 1 := by omega
    have hnat : leastPowTwoGe x = 2 * 2 ^ (leastPowTwoExp x - 1) := by
      rw [leastPowTwoGe]
      conv_lhs => rw [hsplit]
      rw [pow_succ]; ring
    have hR : ((leastPowTwoGe x : ℕ) : ℝ)
        = 2 * (2 : ℝ) ^ (leastPowTwoExp x - 1) := by
      rw [hnat]; push_cast; ring
    have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hxnn : (0 : ℝ) ≤ (⌈x⌉₊ : ℝ) := le_trans hx hceil
    have hbound : ((leastPowTwoGe x : ℕ) : ℝ) < 2 * (⌈x⌉₊ : ℝ) := by
      rw [hR]; linarith [hxnn]
    have : (leastPowTwoGe x : ℕ) < 2 * ⌈x⌉₊ := by exact_mod_cast hbound
    exact le_trans (le_of_lt this) (le_max_right _ _)

/-- **Pin (the `QDIRECT` row of `06:1271--1278`).**  The banked
`EntryGates.rQ` *is* this accessor at the threshold `Q_0`; the schedule does
not introduce a second least-power-of-two search for the bridge width. -/
theorem entry_rQ_eq_leastPowTwoExp (bout : ℕ) (δU : ℝ) :
    rQ bout δU = leastPowTwoExp (Q0 bout δU) := rfl

/-- **Pin.**  Likewise for the width itself. -/
theorem entry_Qwidth_eq_leastPowTwoGe (bout : ℕ) (δU : ℝ) :
    Qwidth bout δU = leastPowTwoGe (Q0 bout δU) := rfl

/-- **Pin (`eq:Q-theta-choice`, `06:529--531`, against
`10-direct-bridge.tex:47--49`).**  The `Q_0` of the schedule display is the
banked `EntryGates.Q0`, spelled out so that the identification is a checked
equation and not an editorial remark. -/
theorem schedule_Q0_eq_entry_Q0 (bout : ℕ) (δU : ℝ) :
    Q0 bout δU
      = max (max (8 * (bout : ℝ) / (deltaFixed * δU)) (8 / deltaFixed)) 16 :=
  rfl

/-! ## Section 1b  The source scale `s`

`eq:s-choice` (`06:109--121`).  The scale `s` is **not** a free input and no
numeral may be assigned to it: `06:111--118` fixes it by a three-step
definitional chain `A_pre -> u -> s` over the public inputs.  Everything below
that consumes `s` -- `eq:eta-choice`, `eq:hard-seed-width-gates`
(`06:264--269`), `P_0` -- reads the value produced by this chain.

The genuinely free inputs of the chain are the public data `b_out`,
`B_pub = max{D, Y}` (`06:49`), `z_R` (`06:51--54`), `clog_2(|E|+2)`, and the
universal configuration field `B_s` of `06:56--60`; they stay **explicit
binders**. -/

/-- **The minimality eliminator of the frozen `clog_2`** (`06:75--76`,
`clog_2(z) = min{j >= 0 : z <= 2^j}`).

If `b^m` is *strictly* below `z` then `m` is not an admissible exponent, hence
`m < clog_b(z)`.  This is the only direction of the frozen minimum used below,
and it is the one that turns a displayed branch of a maximum into a floor on a
ceiling logarithm.  General. -/
theorem lt_clog_of_pow_lt {b n m : ℕ} (hb : 1 < b) (h : b ^ m < n) :
    m < Nat.clog b n :=
  Nat.lt_of_not_le fun hc =>
    absurd ((Nat.clog_le_iff_le_pow hb).mp hc) (Nat.not_le.mpr h)

/-- **`A_pre = max{16, b_out, B_pub, z_R, clog_2(|E|+2)}`** (`eq:s-choice`,
`06:111--115`).

The five branches in the frozen print order.  `clog_2(|E|+2)` is supplied as
the natural `clE`, since its own defining display is the integer primitive of
`06:75--76` and no edge count is in scope here. -/
def Apre (bout Bpub zR clE : ℕ) : ℕ :=
  max (max (max (max 16 bout) Bpub) zR) clE

/-- **`u = clog_2(clog_2(A_pre + 16))`** (`eq:s-choice`, `06:116--117`).

The doubly iterated frozen ceiling logarithm.  `Nat.clog 2` is the exact
integer primitive `clog_2(z) = min{j >= 0 : z <= 2^j}` of `06:75--76` on a
natural argument. -/
def uAux (Apreval : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 (Apreval + 16))

/-- **`s = 2^{ceil(B_s u^2)}`** (`eq:s-choice`, `06:118`).

The frozen ceiling is **kept** rather than silently dropped: `06:56--60` reads
`B_s` from the universal configuration as an integer, so the ceiling is the
identity at every legal configuration, and `sScale_eq_pow` records exactly
that.  `06:122`: "Thus `s` is a public power of two." -/
noncomputable def sScale (Bs u : ℕ) : ℕ := 2 ^ ⌈(Bs : ℝ) * (u : ℝ) ^ 2⌉₊

/-- **Aux S1 (`06:113`, the first branch).**  `A_pre >= 16`.  General.

*Pointer repair (`cc-t8k` rider (i), executed at `cc-t8l`).*  This docstring
cited `06:112`; in the frozen release `06:112` is the display's
`&=\max\left\{` and the `16` branch is on `06:113`
(`16,\bout,B_{\mathrm{pub}},z_R,`).  Comment-only: no statement or proof byte
of this module changed. -/
theorem sixteen_le_Apre (bout Bpub zR clE : ℕ) :
    16 ≤ Apre bout Bpub zR clE :=
  le_trans (le_trans (le_trans (le_max_left 16 bout) (le_max_left _ _))
    (le_max_left _ _)) (le_max_left _ _)

/-- **Aux S2 (the ceiling of `06:118` at an integer configuration field).**
`s = 2^{B_s u^2}`.  General. -/
theorem sScale_eq_pow (Bs u : ℕ) : sScale Bs u = 2 ^ (Bs * u ^ 2) := by
  have hcast : (Bs : ℝ) * (u : ℝ) ^ 2 = ((Bs * u ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [sScale, hcast, Nat.ceil_natCast]

/-- **Aux S3 (the auxiliary depth is never degenerate).**  `3 <= u`, *derived*
from `A_pre >= 16` through the two frozen ceiling logarithms and never
assumed: `A_pre + 16 >= 32 > 2^4` forces `clog_2(A_pre + 16) >= 5`, and
`5 > 2^2` forces `clog_2(5) >= 3`.  General. -/
theorem three_le_uAux (bout Bpub zR clE : ℕ) :
    3 ≤ uAux (Apre bout Bpub zR clE) := by
  have hA := sixteen_le_Apre bout Bpub zR clE
  have hinner : 5 ≤ Nat.clog 2 (Apre bout Bpub zR clE + 16) := by
    have h : (2 : ℕ) ^ 4 < Apre bout Bpub zR clE + 16 := by omega
    exact lt_clog_of_pow_lt (by norm_num) h
  have hfive : 3 ≤ Nat.clog 2 5 := by
    have h : (2 : ℕ) ^ 2 < 5 := by norm_num
    exact lt_clog_of_pow_lt (by norm_num) h
  exact le_trans hfive (Nat.clog_mono_right 2 hinner)

/-- **Aux S4 (the evaluated scale clears the frozen source-scale floor).**

At `1 <= B_s` (the positivity `06:56` demands of every universal
configuration field) and the derived `3 <= u`, the exponent `B_s u^2` is at
least `9`, so `s >= 512`.  In particular `3 < s`, which is the side condition
`eq:eta-choice` needs, and `64 | s`, which is the divisibility `06:975`
records ("The penultimate comparison uses `64 | s`, hence `s >= 64`") and
which `eq:hard-seed-width-gates` (`06:264--269`) demands through
`16 | (s/4)`.  No numeral is assigned to `s`: both facts are read off the
definitional chain. -/
theorem sScale_floor {Bs u : ℕ} (hBs : 1 ≤ Bs) (hu : 3 ≤ u) :
    3 < sScale Bs u ∧ 64 ∣ sScale Bs u := by
  have hexp : 9 ≤ Bs * u ^ 2 := by nlinarith
  have hpow : (2 : ℕ) ^ 9 ≤ 2 ^ (Bs * u ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  rw [sScale_eq_pow]
  refine ⟨by omega, ?_⟩
  have hsplit : (2 : ℕ) ^ (Bs * u ^ 2) = 2 ^ 6 * 2 ^ (Bs * u ^ 2 - 6) := by
    rw [← pow_add]
    congr 1
    omega
  exact ⟨2 ^ (Bs * u ^ 2 - 6), by simpa using hsplit⟩

/-! ## Section 2  The protected deletion tolerances

`eq:eta-choice` (`06:204--220`).  The masses `nu_T, nu_V, nu_B, mu_Sigma,
mu_D` are the banked constants of `eq:fixed-protected-masses`, consumed by
pin; `delta_v(G)` and `zeta` are the source-side scalars of Section 4 and stay
**explicit binders**, since `eq:eta-choice` reads them from the guarded source
rather than fixing them. -/

/-- **`eta_C`** (`eq:eta-choice`, first line, `06:206--211`):
`eta_C = (1/2) min{nu_T/(1000 s), nu_V delta_v(G)/16, nu_B/(16(s-3))}`.

The three-term minimum written literally.  `nu_V = nu_B = 2^{-22}` is the one
banked constant `nuSrcR` (`08:137`); `nu_T = 2^{-21}` is `nuTempR`.  The
subtraction `s - 3` is taken in `ℝ` on the cast, so the truncation of `ℕ`
subtraction cannot silently change the third branch. -/
noncomputable def etaC (s : ℕ) (dv : ℝ) : ℝ :=
  (1 / 2) * min (min (nuTempR / (1000 * (s : ℝ))) (nuSrcR * dv / 16))
    (nuSrcR / (16 * ((s : ℝ) - 3)))

/-- **`eta_R`** (`eq:eta-choice`, second line, `06:212--217`):
`eta_R = (1/2) min{mu_Sigma/100, mu_D zeta/(32 s), eta_C}`.

`mu_Sigma = mu_D = 1/184` is the one banked constant `muR` (`08:134`).  The
third branch is `eta_C` itself, so the dependency order of
`fig:parameter-order` is visible in the type. -/
noncomputable def etaR (s : ℕ) (dv zeta : ℝ) : ℝ :=
  (1 / 2) * min (min (muR / 100) (muR * zeta / (32 * (s : ℝ)))) (etaC s dv)

/-- **`06:221--223`.**  "Since `rho_temp = 1/1000`, the first term in the
definition of `eta_C` is `nu_T rho_temp/s`."  The frozen identification,
checked against the banked `rhoTemp`.  General for `s ≠ 0`. -/
theorem etaC_first_branch (s : ℕ) (hs : (s : ℝ) ≠ 0) :
    nuTempR / (1000 * (s : ℝ)) = nuTempR * rhoTemp / (s : ℝ) := by
  rw [rhoTemp]
  field_simp

/-- **Aux E1 (`06:659`).**  `eta_C <= nu_T/(2000 s)`, the exact upper bound the
cover-search legality premise uses.  General; no side condition, because the
first branch alone bounds the minimum. -/
theorem etaC_le_nu (s : ℕ) (dv : ℝ) :
    etaC s dv ≤ nuTempR / (2000 * (s : ℝ)) := by
  have h : min (min (nuTempR / (1000 * (s : ℝ))) (nuSrcR * dv / 16))
      (nuSrcR / (16 * ((s : ℝ) - 3))) ≤ nuTempR / (1000 * (s : ℝ)) :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [etaC]
  calc (1 / 2 : ℝ) * min (min (nuTempR / (1000 * (s : ℝ))) (nuSrcR * dv / 16))
        (nuSrcR / (16 * ((s : ℝ) - 3)))
      ≤ (1 / 2) * (nuTempR / (1000 * (s : ℝ))) := this
    _ = nuTempR / (2000 * (s : ℝ)) := by ring

/-- **Aux E2 (`06:658--661`).**  `0 < eta_C` at the frozen side conditions
`3 < s` and `0 < delta_v(G)`.  Positivity is *derived* from the three branches,
never assumed. -/
theorem etaC_pos {s : ℕ} {dv : ℝ} (hs : 3 < s) (hdv : 0 < dv) :
    0 < etaC s dv := by
  have hnuT : nuTempR = 1 / 2 ^ 21 := protectedMasses_agree.1
  have hnuS : nuSrcR = 1 / 2 ^ 22 := protectedMasses_agree.2.1
  have hs3 : (3 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hspos : (0 : ℝ) < (s : ℝ) := by linarith
  have h1 : 0 < nuTempR / (1000 * (s : ℝ)) := by rw [hnuT]; positivity
  have h2 : 0 < nuSrcR * dv / 16 := by rw [hnuS]; positivity
  have h3 : 0 < nuSrcR / (16 * ((s : ℝ) - 3)) := by
    rw [hnuS]
    have : (0 : ℝ) < (s : ℝ) - 3 := by linarith
    positivity
  rw [etaC]
  have := lt_min (lt_min h1 h2) h3
  linarith

/-- **Aux E2a (`06:658--661`, first line).**  `0 < eta_C <= nu_T/(2000 s) < 1`
--- the display's first chain, landed **in frozen order** with all three of its
comparisons present: positivity, the exact upper bound, and the strict
`nu_T/(2000 s) < 1` on which the second line's `0 < 1 - eta_C` rests.  The
frozen side conditions `3 < s` and `0 < delta_v(G)` are carried unweakened; the
middle comparison alone needs neither (`etaC_le_nu`), which is the paper's own
asymmetry -- the third comparison is about `nu_T = 2^{-21}` against `2000 s`,
and `eq:eta-choice` reads the masses of `eq:fixed-protected-masses` by pin,
never re-fixing `2^{-21}` here. -/
theorem etaC_le_nu_lt_one {s : ℕ} {dv : ℝ} (hs : 3 < s) (hdv : 0 < dv) :
    0 < etaC s dv ∧ etaC s dv ≤ nuTempR / (2000 * (s : ℝ)) ∧
      nuTempR / (2000 * (s : ℝ)) < 1 := by
  have hnuT : nuTempR = 1 / 2 ^ 21 := protectedMasses_agree.1
  have hs3 : (3 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  refine ⟨etaC_pos hs hdv, etaC_le_nu s dv, ?_⟩
  rw [hnuT]
  rw [div_lt_one (by positivity)]
  nlinarith

/-- **Aux E3 (`06:658--661`, second line).**  `0 < 1 - eta_C < 1`, strict on
**both** sides exactly as the frozen display prints it: the legality premises
`eq:cover-bounds` needs in order to run the singleton least search at the base
`rho_* = 1 - eta_C` of `06:700`.

The left strictness is load-bearing rather than decorative.  The generic tested
endpoint `eq:cover-tested-endpoint` (`06:666--670`) is stated for a reduced
base `a/b` with `0 < a < b`, so a non-strict `0 <= 1 - eta_C` would allow the
degenerate base `0`, which the frozen premise excludes.  Hypotheses are the
frozen side conditions `3 < s` and `0 < delta_v(G)`, unweakened. -/
theorem one_sub_etaC_legal {s : ℕ} {dv : ℝ} (hs : 3 < s) (hdv : 0 < dv) :
    0 < 1 - etaC s dv ∧ 1 - etaC s dv < 1 := by
  obtain ⟨hpos, hle, hsmall⟩ := etaC_le_nu_lt_one hs hdv
  exact ⟨by linarith, by linarith⟩

/-- **Aux E4 (`06:228`, first comparison).**  `eta_R <= eta_C/2`, immediately
from the third branch of the minimum.  General; no side condition. -/
theorem etaR_le_etaC_half (s : ℕ) (dv zeta : ℝ) :
    etaR s dv zeta ≤ etaC s dv / 2 := by
  have h : min (min (muR / 100) (muR * zeta / (32 * (s : ℝ)))) (etaC s dv)
      ≤ etaC s dv := min_le_right _ _
  have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [etaR]
  linarith

/-- **Aux E5 (the schedule's own ceiling on `eta_R`).**  `eta_R <= 1/36800`,
from the first branch `mu_Sigma/100 = 1/18400`.  General; no side condition.
This is what makes the finite gate `06:547` (`delta_U <= 1/200`) automatic
rather than an extra demand on the compiler. -/
theorem etaR_le_bound (s : ℕ) (dv zeta : ℝ) :
    etaR s dv zeta ≤ 1 / 36800 := by
  have hmu : muR = 1 / 184 := protectedMasses_agree.2.2
  have h : min (min (muR / 100) (muR * zeta / (32 * (s : ℝ)))) (etaC s dv)
      ≤ muR / 100 := le_trans (min_le_left _ _) (min_le_left _ _)
  have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [etaR]
  rw [hmu] at this
  linarith

/-- **Aux E6.**  `0 < eta_R` at the frozen side conditions
`3 < s`, `0 < delta_v(G)`, `0 < zeta`. -/
theorem etaR_pos {s : ℕ} {dv zeta : ℝ} (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) : 0 < etaR s dv zeta := by
  have hmu : muR = 1 / 184 := protectedMasses_agree.2.2
  have hs3 : (3 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hspos : (0 : ℝ) < (s : ℝ) := by linarith
  have h1 : 0 < muR / 100 := by rw [hmu]; norm_num
  have h2 : 0 < muR * zeta / (32 * (s : ℝ)) := by rw [hmu]; positivity
  have h3 := etaC_pos hs hdv
  rw [etaR]
  have := lt_min (lt_min h1 h2) h3
  linarith

/-- **Claim (`06:227--233`, the frozen chain).**

"`0 < eta_R <= eta_C/2 < tau < x_N`."  All four comparisons, in the frozen
order, at the frozen side conditions.  `tau = 1/92` and `x_N = 1/16` are the
banked constants of `eq:fixed-protected-masses`; neither is re-fixed here. -/
theorem eta_chain {s : ℕ} {dv zeta : ℝ} (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) :
    0 < etaR s dv zeta ∧ etaR s dv zeta ≤ etaC s dv / 2 ∧
      etaC s dv / 2 < ((tauMass : ℚ) : ℝ) ∧ ((tauMass : ℚ) : ℝ) < xN := by
  have hnuT : nuTempR = 1 / 2 ^ 21 := protectedMasses_agree.1
  have hs3 : (3 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hle := etaC_le_nu s dv
  have hsmall : nuTempR / (2000 * (s : ℝ)) < 1 / 46 := by
    rw [hnuT]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨etaR_pos hs hdv hz, etaR_le_etaC_half s dv zeta, ?_, ?_⟩
  · have : etaC s dv < 1 / 46 := by linarith
    have htau : ((tauMass : ℚ) : ℝ) = 1 / 92 := by
      rw [tauMass]; norm_num
    rw [htau]; linarith
  · have htau : ((tauMass : ℚ) : ℝ) = 1 / 92 := by rw [tauMass]; norm_num
    rw [htau, xN]; norm_num

/-! ## Section 3  The first-wrapper width and the deletion tolerance it feeds

`eq:q-deltaU` (`06:514--519`).  `A_wrap` and `L_P` are **explicit binders**:
`06:520--522` says the integer `A_wrap` "is fixed universally below" by the
coefficient audit and "never depends on a reached transcript", so pinning a
numeral here would replace a schedule degree of freedom by an invented
constant. -/

/-- **`q = 2^{A_wrap L_P^2}`** (`eq:q-deltaU`, `06:515`; reader
`03-parameterized-construction.tex:81--82`).

The scale-alignment interlace width.  This is the interlace width `q`, not the
bridge width `Q` of `eq:Q-theta-choice`. -/
def qWrap (Awrap LP : ℕ) : ℕ := 2 ^ (Awrap * LP ^ 2)

/-- **Aux Q1.**  The width is a positive power of two.  General. -/
theorem qWrap_pos (Awrap LP : ℕ) : 0 < qWrap Awrap LP :=
  Nat.two_pow_pos _

/-- **Aux Q2 (the width is monotone in the audit constant).**  Raising
`A_wrap`, which is exactly what `06:744--747` does to make the three search
gates fire, never shrinks `q`.  General. -/
theorem qWrap_mono {A A' LP : ℕ} (h : A ≤ A') :
    qWrap A LP ≤ qWrap A' LP :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

/-- **Aux Q3 (the exponent readout).**  `log_2 q = A_wrap L_P^2` in the exact
sense the selector cost needs.  General. -/
theorem qWrap_eq_two_pow (Awrap LP : ℕ) :
    qWrap Awrap LP = 2 ^ (Awrap * LP ^ 2) := rfl

/-- **`delta_U = eta_R/(16 q)`** (`eq:q-deltaU`, `06:517`; reader
`03-parameterized-construction.tex:92`, "There are public rationals
`0 < delta_U < 1`").

The deletion tolerance the bridge consumes.  `q` is a binder, so the schedule's
own `qWrap` and the abstract width of the bridge statement are the same
symbol. -/
noncomputable def deltaU (eR : ℝ) (q : ℕ) : ℝ := eR / (16 * (q : ℝ))

/-- **Aux D1.**  `0 < delta_U` at a legal width and a positive tolerance. -/
theorem deltaU_pos {eR : ℝ} {q : ℕ} (h : 0 < eR) (hq : 0 < q) :
    0 < deltaU eR q := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [deltaU]; positivity

/-- **Aux D2 (the finite gate `06:547`, discharged rather than imposed).**

"We also impose the finite gate `delta_U <= 1/200`."  At the schedule's own
`eta_R` this is not an extra demand: `eta_R <= 1/36800` and `q >= 1` already
give `delta_U <= 1/588800`.  The stronger `delta_U <= 1/60` is what the banked
`EntryGates.secondEntryGate_of_deltaU_small` needs, so both are returned. -/
theorem deltaU_le_gates {s : ℕ} {dv zeta : ℝ} {q : ℕ} (hq : 0 < q) :
    deltaU (etaR s dv zeta) q ≤ 1 / 200 ∧
      deltaU (etaR s dv zeta) q ≤ 1 / 60 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbound := etaR_le_bound s dv zeta
  have hstep : deltaU (etaR s dv zeta) q ≤ (1 / 36800) / 16 := by
    rw [deltaU]
    have h16 : (0 : ℝ) < 16 * (q : ℝ) := by linarith
    rw [div_le_iff₀ h16]
    nlinarith
  constructor <;> linarith

/-- **Aux D3 (`03-parameterized-construction.tex:92`: `delta_U < 1`).**
The reader's legality range for the public rational. -/
theorem deltaU_lt_one {s : ℕ} {dv zeta : ℝ} {q : ℕ} (hq : 0 < q) :
    deltaU (etaR s dv zeta) q < 1 := by
  have := (deltaU_le_gates (s := s) (dv := dv) (zeta := zeta) hq).1
  linarith

/-! ## Section 3b  The wrapper threshold `P_0`, the exponent `L_P`, and the
frozen floor on `A_wrap`

`06:465--472` and `06:578`, `06:1671--1678`.  Neither argument of `qWrap` is
free: `L_P` is **defined** by `L_P = clog_2(P_0)` over the displayed maximum
`P_0`, and `A_wrap` is the least integer *strictly* above `c_seed` satisfying
`eq:Awrap-coefficient-search`.  This block reifies the first and records the
integer consequence of the second, so that no numeral is ever assigned to
either. -/

/-- **`P_0 = max{16, C_cert, s, log_2 q_2, ceil(log_2 U_0), z_R}`**
(`06:467--470`).

The six branches in the frozen print order.  `C_cert` (`eq:Ccert`,
`06:430--434`), `log_2 q_2`, `ceil(log_2 U_0)` (`06:296`) and `z_R` are
explicit binders: their own defining displays are elsewhere in `sec:parameters`
and none is stated here.  `s` is **not** a binder in the canonical instance --
it is the value of `sScale`. -/
def P0sched (Ccert s lq2 clU0 zR : ℕ) : ℕ :=
  max (max (max (max (max 16 Ccert) s) lq2) clU0) zR

/-- **`L_P = clog_2(P_0)`** (`06:471`).  The first-wrapper width exponent that
`eq:q-deltaU` squares. -/
def LPwidth (P0v : ℕ) : ℕ := Nat.clog 2 P0v

/-- **`c_seed = 100`** (`06:578`: "The fixed choice `c_seed = 100`"), the
universal configuration field of `06:56--60` that `eq:tref-search` uses in its
floor `c_seed L_P^2` and that `06:1671` compares `A_wrap` against. -/
def cSeed : ℕ := 100

/-- **Aux P1 (`06:467`, the first branch).**  `16 <= P_0`.  General. -/
theorem sixteen_le_P0sched (Ccert s lq2 clU0 zR : ℕ) :
    16 ≤ P0sched Ccert s lq2 clU0 zR :=
  le_trans (le_trans (le_trans (le_trans (le_max_left 16 Ccert)
    (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)

/-- **Aux P2 (`06:467--471`, the floor the width exponent inherits).**

`16 <= P_0` forces `4 <= L_P`, since `clog_2` is monotone and
`2^3 = 8 < 16`.  This is the *paper's* floor on `L_P`: it is derived from the
first branch of the displayed maximum, never chosen.  General. -/
theorem four_le_LPwidth {P0v : ℕ} (h : 16 ≤ P0v) : 4 ≤ LPwidth P0v := by
  have hlt : (2 : ℕ) ^ 3 < P0v := by omega
  exact lt_clog_of_pow_lt (by norm_num) hlt

/-- **Aux P3.**  The same floor at the evaluated threshold.  General. -/
theorem four_le_LPwidth_sched (Ccert s lq2 clU0 zR : ℕ) :
    4 ≤ LPwidth (P0sched Ccert s lq2 clU0 zR) :=
  four_le_LPwidth (sixteen_le_P0sched Ccert s lq2 clU0 zR)

/-- **Aux P4 (`06:1671`, the strict comparison).**

"Choose `A_wrap > c_seed` as the least integer satisfying
`eq:Awrap-coefficient-search`."  The comparison the frozen text prints is
**strict**, and over the integers its exact consequence at `c_seed = 100` is
`101 <= A_wrap` -- not `102`, which the paper never displays and which would
exclude the paper's own least admissible value.  General. -/
theorem hundredOne_le_of_cSeed_lt {A : ℕ} (h : cSeed < A) : 101 ≤ A := by
  rw [cSeed] at h; omega

/-! ## Section 4  The bridge width `Q` and the common row threshold `theta`

`eq:Q-theta-choice` (`06:525--538`) and `06:539`.  `Q_0` and `Q` are the banked
`EntryGates.Q0` and `EntryGates.Qwidth` -- the very display of
`10-direct-bridge.tex:47--51` -- and are consumed, never restated. -/

/-- **`c_theta = delta/8`** (`06:62`), the configuration field the row
threshold is built from.  It is a *field of the universal configuration*, not
an anonymous constant, so it is named before it is used. -/
noncomputable def cTheta : ℝ := deltaFixed / 8

/-- **`theta = c_theta/(2Q)`** (`eq:Q-theta-choice`, `06:533`; reader
`03-parameterized-construction.tex:92`, "`0 < theta <= 1/4`").

The frozen display's *first* spelling is the definition, so the configuration
field `c_theta` of `06:62` is not silently discarded; `theta_eq_delta` returns
the second spelling `delta/(16Q)`. -/
noncomputable def theta (Q : ℕ) : ℝ := cTheta / (2 * (Q : ℝ))

/-- **Claim (`06:533`, second spelling).**  `theta = delta/(16 Q)`. -/
theorem theta_eq_delta (Q : ℕ) : theta Q = deltaFixed / (16 * (Q : ℝ)) := by
  rw [theta, cTheta, div_div]
  ring_nf

/-- **Claim (`06:539`).**  "Here `1/theta = 160 Q` is an integer because
`delta = 1/10`."  Exactly that, at every positive width. -/
theorem theta_inv_eq {Q : ℕ} (hQ : 0 < Q) : 1 / theta Q = 160 * (Q : ℝ) := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  rw [theta_eq_delta, deltaFixed_eq]
  field_simp
  norm_num

/-- **Aux T1.**  `0 < theta` at a legal width. -/
theorem theta_pos {Q : ℕ} (hQ : 0 < Q) : 0 < theta Q := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  rw [theta_eq_delta, deltaFixed_eq]; positivity

/-- **Claim (`eq:direct-theta-gates`, first row, `06:542`).**
`Q theta = delta/16 < delta/2`. -/
theorem Q_mul_theta {Q : ℕ} (hQ : 0 < Q) :
    (Q : ℝ) * theta Q = deltaFixed / 16 ∧ deltaFixed / 16 < deltaFixed / 2 := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  constructor
  · rw [theta_eq_delta]; field_simp
  · rw [deltaFixed_eq]; norm_num

/-- **`L_theta = clog_2(1/theta)`** (`eq:Q-theta-choice`, `06:535`).

By `06:539` the argument `1/theta = 160 Q` is a *natural number*, so the frozen
`clog_2` is the natural-number ceiling logarithm and no rational search is
needed.  `06:1288--1292`: "For a natural argument `x`, exponent `x` is a
termination witness, but the returned and coefficient majorant is
`clog_2^ℕ(x) <= bl(x)`." -/
def Ltheta (Q : ℕ) : ℕ := Nat.clog 2 (160 * Q)

/-- **Aux T2 (the defining property of `L_theta`).**  `1/theta <= 2^{L_theta}`,
in the frozen `clog_2` sense `min{j >= 0 : z <= 2^j}`. -/
theorem Ltheta_spec {Q : ℕ} (hQ : 0 < Q) :
    1 / theta Q ≤ (2 : ℝ) ^ Ltheta Q := by
  rw [theta_inv_eq hQ]
  have h : (160 * Q : ℕ) ≤ 2 ^ Nat.clog 2 (160 * Q) :=
    Nat.le_pow_clog (by norm_num) _
  have : ((160 * Q : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 (160 * Q) : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Ltheta]
  push_cast at this ⊢
  linarith

/-- **Claim (`eq:direct-theta-gates`, second row, `06:543`).**

`4 Q_0 theta <= delta/4 < delta` at the schedule's own row threshold
`theta = theta(Q)`, where `Q` is the banked least power of two at least `Q_0`.
The proof is the frozen one: `Q_0 <= Q` and `Q theta = delta/16`.

This is the *schedule's* verification of the first half of
`eq:direct-entry-gates`, and it is what `05-iteration.tex:228` records the
producer as checking. -/
theorem four_Q0_theta_le (bout : ℕ) (δU : ℝ) :
    4 * Q0 bout δU * theta (Qwidth bout δU) ≤ deltaFixed / 4 ∧
      deltaFixed / 4 < deltaFixed := by
  have hQpos : 0 < Qwidth bout δU := Nat.two_pow_pos _
  have hθ := theta_pos hQpos
  have hle := Q0_le_Qwidth bout δU
  have heq := (Q_mul_theta hQpos).1
  constructor
  · have : 4 * Q0 bout δU * theta (Qwidth bout δU)
        ≤ 4 * ((Qwidth bout δU : ℕ) : ℝ) * theta (Qwidth bout δU) := by
      have h4 : (0 : ℝ) ≤ 4 := by norm_num
      nlinarith
    calc 4 * Q0 bout δU * theta (Qwidth bout δU)
        ≤ 4 * ((Qwidth bout δU : ℕ) : ℝ) * theta (Qwidth bout δU) := this
      _ = 4 * (((Qwidth bout δU : ℕ) : ℝ) * theta (Qwidth bout δU)) := by ring
      _ = 4 * (deltaFixed / 16) := by rw [heq]
      _ = deltaFixed / 4 := by ring
  · rw [deltaFixed_eq]; norm_num

/-! ## Section 5  The cover numbers and `e_0^max`

`eq:cover-bounds` (`06:639--654`), its generic tested endpoint
`eq:cover-tested-endpoint` (`06:666--681`) and the two literal instances of
`eq:cover-instance-tested-endpoints` whose bases are fixed numerals.  The three
least searches themselves are the banked `coverExponent`, and the `e_0^max`
arithmetic is the banked `e0Max`; both are consumed by pin. -/

/-- **`eq:cover-tested-endpoint` (`06:666--681`), the generic stored
endpoint.**

"write the reduced base as `a/b`, with `0 < a < b`, and the reduced positive
threshold as `u/v`, with `u, v >= 1`.  Put `r = bl(v) = clog_2(v+1)`.  The
compiler stores `B^* = b r`, `(a/b)^{B^*} < u/v`."

The frozen proof, in the kernel: Bernoulli's inequality gives
`(b/(b-1))^b >= 1 + b/(b-1) > 2`, hence `(a/b)^b <= ((b-1)/b)^b < 1/2`; also
`2^r >= v+1 > v >= v/u`; therefore `(a/b)^{br} < 2^{-r} < u/v`, "proving the
stored comparison without invoking the value returned by the least search."
General in all four integers. -/
theorem cover_tested_endpoint {a b u v : ℕ} (ha : 0 < a) (hab : a < b)
    (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ((a : ℝ) / (b : ℝ)) ^ (b * Nat.clog 2 (v + 1)) < (u : ℝ) / (v : ℝ) := by
  have hb2 : 2 ≤ b := by omega
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
  have hb1R : (1 : ℝ) ≤ (b : ℝ) - 1 := by linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  -- Bernoulli: `(1 + 1/(b-1))^b >= 1 + b/(b-1) > 2`
  have hbern : 1 + (b : ℝ) * (1 / ((b : ℝ) - 1))
      ≤ (1 + 1 / ((b : ℝ) - 1)) ^ b :=
    one_add_mul_le_pow
      (by have hx : (0 : ℝ) ≤ 1 / ((b : ℝ) - 1) := by positivity
          linarith) b
  have hgt2 : (2 : ℝ) < (1 + 1 / ((b : ℝ) - 1)) ^ b := by
    have hfrac : (1 : ℝ) < (b : ℝ) * (1 / ((b : ℝ) - 1)) := by
      rw [mul_one_div, lt_div_iff₀ (by linarith)]
      linarith
    linarith
  have hrw : 1 + 1 / ((b : ℝ) - 1) = (b : ℝ) / ((b : ℝ) - 1) := by
    field_simp
    ring
  rw [hrw] at hgt2
  have hpred : (((b : ℝ) - 1) / (b : ℝ)) ^ b < 1 / 2 := by
    have hXpos : (0 : ℝ) < (((b : ℝ) - 1) / (b : ℝ)) ^ b :=
      pow_pos (div_pos (by linarith) hbpos) b
    have hprod : (((b : ℝ) - 1) / (b : ℝ)) ^ b * (((b : ℝ) / ((b : ℝ) - 1)) ^ b)
        = 1 := by
      rw [← mul_pow]
      have hone : ((b : ℝ) - 1) / (b : ℝ) * ((b : ℝ) / ((b : ℝ) - 1)) = 1 := by
        field_simp
      rw [hone, one_pow]
    nlinarith [hprod, hgt2, hXpos]
  -- `(a/b)^b < 1/2`
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hale : (a : ℝ) ≤ (b : ℝ) - 1 := by
    have : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hbase : ((a : ℝ) / (b : ℝ)) ^ b < 1 / 2 := by
    have hstep : (a : ℝ) / (b : ℝ) ≤ ((b : ℝ) - 1) / (b : ℝ) := by
      rw [div_le_div_iff₀ hbpos hbpos]
      nlinarith
    have hmono : ((a : ℝ) / (b : ℝ)) ^ b ≤ (((b : ℝ) - 1) / (b : ℝ)) ^ b :=
      pow_le_pow_left₀ (by positivity) hstep b
    linarith
  -- exponent `r = clog_2 (v+1) >= 1`
  set r := Nat.clog 2 (v + 1) with hrdef
  have hrpos : 0 < r := Nat.clog_pos (by norm_num) (by omega)
  have hpow : (((a : ℝ) / (b : ℝ)) ^ b) ^ r < ((1 : ℝ) / 2) ^ r := by
    exact pow_lt_pow_left₀ hbase (by positivity) (by omega)
  have hsplit : ((a : ℝ) / (b : ℝ)) ^ (b * r)
      = (((a : ℝ) / (b : ℝ)) ^ b) ^ r := by rw [pow_mul]
  -- `2^{-r} < u/v`
  have hvpow : (v + 1 : ℕ) ≤ 2 ^ r := Nat.le_pow_clog (by norm_num) _
  have hvR : ((v : ℝ) + 1) ≤ (2 : ℝ) ^ r := by
    have : ((v + 1 : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hvpow
    push_cast at this
    linarith
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    have : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    linarith
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have h2rpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hfinal : ((1 : ℝ) / 2) ^ r < (u : ℝ) / (v : ℝ) := by
    rw [div_pow, one_pow]
    rw [div_lt_div_iff₀ h2rpos hvpos]
    nlinarith
  rw [hsplit]
  exact lt_trans hpow hfinal

/-- **`eq:cover-instance-tested-endpoints`, first row (`06:684--685`).**

`B_ref^* = 25 bl(den theta)` at the reference base `18/25 = rho_small`, whose
value at the schedule's own threshold `theta = 1/(160Q)` is
`25 clog_2(160Q + 1)`.  Least-search minimality then bounds the returned
`B_ref` without evaluating it. -/
theorem Bref_le_tested {Q : ℕ} (hQ : 0 < Q) :
    coverExponent rhoSmall (theta Q) ≤ 25 * Nat.clog 2 (160 * Q + 1) := by
  have hclog : 0 < Nat.clog 2 (160 * Q + 1) :=
    Nat.clog_pos (by norm_num) (by omega)
  have hθ : theta Q = (1 : ℝ) / ((160 * Q : ℕ) : ℝ) := by
    rw [theta_eq_delta, deltaFixed_eq]
    push_cast
    field_simp
    norm_num
  have hend := cover_tested_endpoint (a := 18) (b := 25) (u := 1)
    (v := 160 * Q) (by norm_num) (by norm_num) (by norm_num) (by omega)
  refine coverExponent_le (by omega) ?_
  have hbase : rhoSmall = ((18 : ℕ) : ℝ) / ((25 : ℕ) : ℝ) := by
    rw [rhoSmall]; norm_num
  rw [hbase, hθ]
  simpa using hend

/-- **`eq:cover-instance-tested-endpoints`, third row (`06:689--690`).**

`B_pair^* = 100 bl(den theta)` at the pair base `99/100 = rho_pair`.  Same
frozen endpoint, same minimality step. -/
theorem Bpair_le_tested {Q : ℕ} (hQ : 0 < Q) :
    coverExponent rhoPair (theta Q) ≤ 100 * Nat.clog 2 (160 * Q + 1) := by
  have hclog : 0 < Nat.clog 2 (160 * Q + 1) :=
    Nat.clog_pos (by norm_num) (by omega)
  have hθ : theta Q = (1 : ℝ) / ((160 * Q : ℕ) : ℝ) := by
    rw [theta_eq_delta, deltaFixed_eq]
    push_cast
    field_simp
    norm_num
  have hend := cover_tested_endpoint (a := 99) (b := 100) (u := 1)
    (v := 160 * Q) (by norm_num) (by norm_num) (by norm_num) (by omega)
  refine coverExponent_le (by omega) ?_
  have hbase : rhoPair = ((99 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) := by
    rw [rhoPair]; norm_num
  rw [hbase, hθ]
  simpa using hend

/-- **`e_0^max`** (`eq:cover-bounds`, `06:647--651`):

`e_0^max = (B_ref - 1)(t_ref/2 + log_2 t_ref - 2) + (B_sing - 1)
          + 2(B_pair - 1)`.

The three cover numbers are the banked least search at the three frozen bases
-- `18/25` for the reference (`rho_small`), `1 - eta_C` for the singleton (the
value `06:698--700` fixes for `rho_*`), and `99/100` for the pair
(`rho_pair`) -- and the arithmetic is the banked `e0Max` at `t_ref = 2^{k_ref}`.
Nothing new is defined; the schedule's contribution is the *choice of the three
bases and of `k_ref`*. -/
noncomputable def e0maxSched (θ eC : ℝ) (kref : ℕ) : ℕ :=
  e0Max (coverExponent rhoSmall θ) (coverExponent (1 - eC) θ)
    (coverExponent rhoPair θ) kref

/-- **Claim (`eq:cover-bounds`, the displayed arithmetic).**  With
`t_ref = 2^{k_ref}`, the banked `e0Max` is literally the frozen display:
`t_ref/2 = 2^{k_ref - 1}` and `log_2 t_ref = k_ref`. -/
theorem e0maxSched_eq_display (θ eC : ℝ) (kref : ℕ) :
    e0maxSched θ eC kref
      = (coverExponent rhoSmall θ - 1) * (2 ^ (kref - 1) + kref - 2)
        + (coverExponent (1 - eC) θ - 1)
        + 2 * (coverExponent rhoPair θ - 1) := rfl

/-- **Aux C1 (monotone in the reference exponent).**  Enlarging `k_ref`, which
is the only way the reference search can move, never decreases the recorded
exceptional-coordinate bound.  General. -/
theorem e0maxSched_mono {θ eC : ℝ} {k k' : ℕ} (h : k ≤ k') :
    e0maxSched θ eC k ≤ e0maxSched θ eC k' := by
  rw [e0maxSched_eq_display, e0maxSched_eq_display]
  have hpow : 2 ^ (k - 1) ≤ 2 ^ (k' - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ (k - 1) + k - 2 ≤ 2 ^ (k' - 1) + k' - 2 := by omega
  have := Nat.mul_le_mul_left (coverExponent rhoSmall θ - 1) this
  omega

/-! ## Section 6  The terminal uniform bounds

`eq:terminal-uniform-bounds` (`06:716--731`).  `06:746--747`: "no parameter in
`eq:terminal-uniform-bounds` depends on which terminal state a protocol happens
to reach", so every argument below is a schedule quantity and none is a
transcript. -/

/-- **`vartheta = 9/16`** (`eq:terminal-uniform-bounds`, `06:718`). -/
noncomputable def vartheta : ℝ := 9 / 16

/-- **Pin (`eq:terminal-uniform-bounds`, `06:718`: `B_theta = B_pair`).**

The identification is a checked equation, not an editorial remark: the banked
`WrapperProtectedEarly.Btheta` is the least search at `rho_0`, and `rho_0` and
`rho_pair` are the same value (`WrapperProtectedEarly.rhoZero_eq_rhoPair`), so
the Section-6 `B_theta` really is the *pair* cover number of `eq:cover-bounds`
and not a second search.  The `Btheta` argument of `EB` below therefore has a
defining display and is not a free invention. -/
theorem schedule_Btheta_eq_Bpair (θ : ℝ) :
    Btheta θ = coverExponent rhoPair θ := by
  rw [Btheta, rhoZero_eq_rhoPair]

/-- **Pin (`eq:terminal-uniform-bounds`, `06:719`:
`L_q = ceil(log_2(2q)) + 1`).**

Likewise for the number of dyadic donor classes: the `Lqv` argument of `EB` is
the banked `WrapperProtectedEarly.Lq` at the schedule's own first-wrapper
width, with the frozen `ceil(log_2 .)` read as `Nat.clog 2`. -/
theorem schedule_Lq_eq_display (q : ℕ) : Lq q = Nat.clog 2 (2 * q) + 1 := rfl

/-- **`E_B`** (`eq:terminal-uniform-bounds`, `06:720--722`):
`E_B = ceil( 512 mu_P B_theta L_q s e_0^max / ((1 - vartheta) eta_R) )`.

The frozen ceiling is kept.  `mu_P = 1/184` and `L_q` are the banked constants
of `WRAPPER-PROTECTED-EARLY-001`; `B_theta = B_pair` by `06:718`. -/
noncomputable def EB (Btheta Lqv s e0m : ℕ) (eR : ℝ) : ℕ :=
  ⌈512 * muP * (Btheta : ℝ) * (Lqv : ℝ) * (s : ℝ) * (e0m : ℝ) /
    ((1 - vartheta) * eR)⌉₊

/-- **`E_T`** (`eq:terminal-uniform-bounds`, `06:723`):
`E_T = ceil( e_0^max/(1 - vartheta) ) + E_B`.  Both ceilings preserved. -/
noncomputable def ET (e0m EBv : ℕ) : ℕ :=
  ⌈(e0m : ℝ) / (1 - vartheta)⌉₊ + EBv

/-- **`delta_term`** (`eq:terminal-uniform-bounds`, `06:724--725`):
`delta_term = eta_R/(8 mu_P max{1, E_T})`.  The frozen `max{1, ·}` is kept, so
the density is defined even at `E_T = 0`. -/
noncomputable def deltaTerm (eR : ℝ) (ETv : ℕ) : ℝ :=
  eR / (8 * muP * (max 1 ETv : ℕ))

/-- **`u_term`** (`eq:terminal-uniform-bounds`, `06:726--728`): "the least
power of two with `u_term delta_term >= 8 s`".

Read as the least power of two at least the threshold `8 s/delta_term`, which
is the `UTERM` row of the instance table `06:1276`. -/
noncomputable def uTerm (s : ℕ) (dTerm : ℝ) : ℕ :=
  leastPowTwoGe (8 * (s : ℝ) / dTerm)

/-- **Aux U1 (`06:726--728`, the defining property).**
`u_term delta_term >= 8 s`, at a positive terminal density. -/
theorem uTerm_spec {s : ℕ} {dTerm : ℝ} (hd : 0 < dTerm) :
    8 * (s : ℝ) ≤ ((uTerm s dTerm : ℕ) : ℝ) * dTerm := by
  have h := le_leastPowTwoGe (8 * (s : ℝ) / dTerm)
  rw [uTerm]
  rw [div_le_iff₀ hd] at h
  linarith

/-- **Aux U2.**  `0 < delta_term` at a positive tolerance. -/
theorem deltaTerm_pos {eR : ℝ} {ETv : ℕ} (h : 0 < eR) :
    0 < deltaTerm eR ETv := by
  have hmu : muP = 1 / 184 := rfl
  have hmax : (1 : ℕ) ≤ max 1 ETv := le_max_left _ _
  have hmaxR : (1 : ℝ) ≤ ((max 1 ETv : ℕ) : ℝ) := by exact_mod_cast hmax
  rw [deltaTerm, hmu]
  have : (0 : ℝ) < 8 * (1 / 184) * ((max 1 ETv : ℕ) : ℝ) := by nlinarith
  exact div_pos h this

/-- **Aux U3 (`06:718`, the frozen split constant).**  `1 - vartheta = 7/16`,
so both `E_B` and `E_T` divide by a positive rational and their ceilings are
taken of a genuine quantity.  General. -/
theorem one_sub_vartheta : 1 - vartheta = 7 / 16 := by
  rw [vartheta]; norm_num

/-- **Aux U4 (the frozen sum shape of `E_T`).**  `E_B <= E_T`: the terminal
exceptional bound of `06:723` dominates the Bob-heavy bound of `06:720--722`,
which is what makes `q >= 8 max{1, E_T}` the binding first row of
`eq:terminal-wrapper-gates`.  General. -/
theorem EB_le_ET (e0m EBv : ℕ) : EBv ≤ ET e0m EBv :=
  Nat.le_add_left _ _

/-- **Aux U5 (`06:726`: "the least power of two").**  The donor width really is
a power of two, so the dyadic bookkeeping of `sec:first-wrapper` applies to it.
General. -/
theorem uTerm_isPowTwo (s : ℕ) (dTerm : ℝ) :
    ∃ r : ℕ, uTerm s dTerm = 2 ^ r :=
  ⟨leastPowTwoExp (8 * (s : ℝ) / dTerm), rfl⟩

/-! ## Section 7  The three named search gates

`eq:terminal-wrapper-gates` (`06:738--743`).  `06:631--632` names the third row
explicitly: "The downstream gate `q/4 >= t_ref` remains the separately named
third row of `eq:terminal-wrapper-gates`; it is not hidden inside the endpoint
record."  Accordingly all three rows are one `Prop` with three conjuncts, and
the third is a full-fledged conjunct rather than a consequence. -/

/-- **`eq:terminal-wrapper-gates`** (`06:739--741`):

`q >= 8 max{1, E_T}`, `q > 4 E_T u_term B_theta`, and `q/4 >= t_ref`.

The third row is transcribed as `4 t_ref <= q`, which is the integer form of
`q/4 >= t_ref` and avoids a truncating natural division.  This is a `Prop`
abbreviation for the three inequalities the paper displays -- never a bundle of
derived facts, and never a conclusion. -/
def terminalWrapperGates (q ETv utermv Bthetav tref : ℕ) : Prop :=
  8 * max 1 ETv ≤ q ∧ 4 * ETv * utermv * Bthetav < q ∧ 4 * tref ≤ q

/-- **Aux G1.**  The gate is exactly that conjunction and nothing more. -/
theorem terminalWrapperGates_iff (q ETv utermv Bthetav tref : ℕ) :
    terminalWrapperGates q ETv utermv Bthetav tref ↔
      (8 * max 1 ETv ≤ q ∧ 4 * ETv * utermv * Bthetav < q ∧
        4 * tref ≤ q) :=
  Iff.rfl

/-- **Aux G2 (the third row by exponent arithmetic).**

`4 t_ref <= q` with `t_ref = 2^{k_ref}` and `q = 2^{A_wrap L_P^2}` is exactly
`k_ref + 2 <= A_wrap L_P^2`.  This is the shape `06:744--745` gives the gate:
"Their eventual validity is why `A_wrap` is chosen after the universal
coefficient audit."  General. -/
theorem tref_gate_of_exponent {Awrap LP kref : ℕ}
    (h : kref + 2 ≤ Awrap * LP ^ 2) :
    4 * 2 ^ kref ≤ qWrap Awrap LP := by
  have : (4 : ℕ) * 2 ^ kref = 2 ^ (kref + 2) := by ring
  rw [this, qWrap]
  exact Nat.pow_le_pow_right (by norm_num) h

/-- **Aux G3 (the gate is not free).**  At the degenerate width `q = 1` the
gate fails for every choice of the other four parameters, so a "witness"
sitting at a trivial width is refuted rather than admitted. -/
theorem terminalWrapperGates_refuted_at_unit_width
    (ETv utermv Bthetav tref : ℕ) :
    ¬ terminalWrapperGates 1 ETv utermv Bthetav tref := by
  rintro ⟨h1, -, -⟩
  have : (1 : ℕ) ≤ max 1 ETv := le_max_left _ _
  omega

/-- **Claim (`eq:terminal-wrapper-gates` at the scheduled point, with
symbolic exponents).**

All three rows fire at `q = 2^{A_wrap L_P^2}` once the audit majorants of
`06:744--747` are available.  The two audit bounds enter as **explicit named
hypotheses**, in exactly the shape the frozen text defers them to
`thm:eff-ledger`; the third row is proved outright from the reference
endpoint.  No numeral is assigned to any of `E_T`, `u_term`, `B_theta`,
`k_ref`, `A_wrap`, `L_P`. -/
theorem terminalWrapperGates_at_scheduled_point {Awrap LP kref ETv utermv
    Bthetav e : ℕ}
    (hfirst : 8 * max 1 ETv ≤ 2 ^ e)
    (hsecond : 4 * ETv * utermv * Bthetav < 2 ^ e)
    (hexp : e ≤ Awrap * LP ^ 2)
    (hkref : kref + 2 ≤ Awrap * LP ^ 2) :
    terminalWrapperGates (qWrap Awrap LP) ETv utermv Bthetav (2 ^ kref) := by
  have hmono : (2 : ℕ) ^ e ≤ qWrap Awrap LP :=
    Nat.pow_le_pow_right (by norm_num) hexp
  exact ⟨le_trans hfirst hmono, lt_of_lt_of_le hsecond hmono,
    tref_gate_of_exponent hkref⟩

/-! ## Section 8  The certified reference width `t_ref`

`eq:tref-search` (`06:559--570`), its tested endpoint
`eq:kref-tested-endpoint` (`06:587--591`), the four persistence records
`eq:kref-fixed-persistence` (`06:598--608`), the feasible `j_49` candidate
`eq:kref-j49-candidate` (`06:615--621`) and the minimality argument
`06:622--629`.

`C_cert`, `log_2 q`, `L_theta` and `clog_2(t_0(3/5))` are **explicit binders**:
their own defining displays live elsewhere (`eq:Ccert` at `06:430--434`, the
inherited `t_0` in `thm:certified-localized-extension`), and this module states
no value for them. -/

/-- **The floor of the `k_ref` search** (`eq:tref-search`, `06:561--563`):
`max{2^19, c_seed L_P^2, clog_2(t_0(3/5))}`. -/
def krefFloor (cseed LP t0clog : ℕ) : ℕ :=
  max (max (2 ^ 19) (cseed * LP ^ 2)) t0clog

/-- **The `k_ref` search predicate** (`eq:tref-search`, `06:560--568`).

The three clauses, in the frozen order: the floor, the exponential width
comparison `2^{k-1} >= C_cert - 1 + log_2 q + L_theta`, and the hard-seed
comparison `2^{j_49(k)} >= C_cert - 1 + k + L_theta`.  `06:572`: "This is a
terminating search over integer comparisons." -/
noncomputable def KrefPred (cseed LP t0clog Ccert lq Lth : ℕ) (k : ℕ) : Prop :=
  krefFloor cseed LP t0clog ≤ k ∧
    Ccert - 1 + lq + Lth ≤ 2 ^ (k - 1) ∧
    Ccert - 1 + k + Lth ≤ 2 ^ j49 k

/-- **`k_ref`** (`eq:tref-search`, `06:558`): "the least integer satisfying"
the three clauses. -/
noncomputable def kref (cseed LP t0clog Ccert lq Lth : ℕ) : ℕ :=
  sInf {k : ℕ | KrefPred cseed LP t0clog Ccert lq Lth k}

/-- **`t_ref = 2^{k_ref}`** (`eq:tref-search`, `06:569`). -/
noncomputable def tref (cseed LP t0clog Ccert lq Lth : ℕ) : ℕ :=
  2 ^ kref cseed LP t0clog Ccert lq Lth

/-- **`k_ref^* = 100 L_P^2`** (`eq:kref-tested-endpoint`, `06:588`), the
explicit nonrecursive tested endpoint. -/
def krefStar (LP : ℕ) : ℕ := 100 * LP ^ 2

/-- **`j_ref^* = 4 L_P`** (`eq:kref-tested-endpoint`, `06:589`), the displayed
feasible `j_49` candidate at that endpoint. -/
def jrefStar (LP : ℕ) : ℕ := 4 * LP

/-- **`eq:kref-j49-candidate` (`06:615--621`).**

"`10000 (j_ref^*)^2 = 160000 L_P^2 <= 240100 L_P^2 = 2401 k_ref^*`."  The exact
integer derivation, so `j_ref^*` is a *displayed feasible candidate* in the
sense of `eq:j49-search-data`.  General in `L_P`. -/
theorem kref_j49_candidate (LP : ℕ) :
    J49Feasible (krefStar LP) (jrefStar LP) := by
  rw [J49Feasible, krefStar, jrefStar]
  ring_nf
  omega

/-- **`06:622--624`.**  "Thus `j_ref^*` is a feasible `j_49`-candidate, and
maximality in `eq:j49-search-data` gives `4 L_P <= j_49(k_ref^*)`."  The
maximality eliminator applied to the displayed candidate -- never a lower bound
read off a returned value. -/
theorem jrefStar_le_j49 (LP : ℕ) : 4 * LP ≤ j49 (krefStar LP) :=
  j49_max (kref_j49_candidate LP)

/-- **`06:624--628`, least-search minimality at the tested endpoint.**

"The last two rows of `eq:kref-fixed-persistence`, together with monotonicity
of powers of two, prove the remaining two clauses of `eq:tref-search` at
`k_ref^*`.  Least-search minimality therefore gives `k_ref <= k_ref^*`."

The four conclusions of `eq:kref-fixed-persistence` (`06:598--608`) enter as
**explicit named hypotheses**: they are the four persistent-cutoff records
`KREF-LOWER-2P19`, `KREF-LOWER-T0`, `KREF-EXP-WIDTH`, `KREF-J49-WIDTH`, each
with "its own cutoff root and its own base-case and one-step persistence
derivations" (`06:595--597`), and those derivations belong to
`sec:effective-cutoff`, not here.  `06:628--629`: "Neither the returned value
nor a growth assertion about it proves termination." -/
theorem kref_le_star {LP t0clog Ccert lq Lth : ℕ}
    (hrec1 : (2 : ℕ) ^ 19 ≤ 100 * LP ^ 2)
    (hrec2 : t0clog ≤ 100 * LP ^ 2)
    (hrec3 : Ccert - 1 + lq + Lth ≤ 2 ^ (100 * LP ^ 2 - 1))
    (hrec4 : Ccert - 1 + 100 * LP ^ 2 + Lth ≤ 2 ^ (4 * LP)) :
    kref 100 LP t0clog Ccert lq Lth ≤ krefStar LP := by
  refine Nat.sInf_le ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [krefFloor, krefStar]
    exact max_le (max_le hrec1 le_rfl) hrec2
  · rw [krefStar]; exact hrec3
  · rw [krefStar]
    refine le_trans hrec4 ?_
    exact Nat.pow_le_pow_right (by norm_num) (jrefStar_le_j49 LP)

/-! ## Section 9  The single Stage-2 width search

`eq:t2-search` (`06:764--773`) with its tested endpoint
`eq:k2-tested-endpoint` (`06:775--780`), the feasible candidate
`eq:k2-j49-candidate` (`06:789--795`) and the named integer lemma
`eq:k2-fixed-growth-lemma` (`06:799--803`).

`H_max`, `L_h` and `v_max` are **defined** by `eq:Hmax` (`06:754--762`) and are
reified here, because the endpoint verification `06:781--812` uses the *shape*
of `H_max` (through `H_max >= L_h + B_cap`) to discharge the hard-seed clause
of `eq:t2-search`.  `B_cap`, `b_2`, `b_T`, `q`, `q_1`, `log_2 q`, `log_2 q_2`
and `u_term` stay **explicit binders**: their own defining displays are
elsewhere and this module states no value for them. -/

/-- **`v_max = max{2, q, u_term}`** (`eq:Hmax`, `06:756`), the shared
Localized-Extension alphabet floor of the level. -/
def vMax (q uterm : ℕ) : ℕ := max (max 2 q) uterm

/-- **`L_h = max{b_2, b_T} + max{q, u_term} + 4`** (`eq:Hmax`, `06:757`).

The frozen sum of two maxima and the displayed additive margin `4`. -/
def LhSched (b2 bT q uterm : ℕ) : ℕ := max b2 bT + max q uterm + 4

/-- **`H_max = L_h + 8 q_1 + log_2 q + log_2 q_2 + B_cap + 10`** (`eq:Hmax`,
`06:758--759`).

The six frozen summands in print order.  `06:824` records that this is the
quantity `eq:t2-search` compares against, and `06:808` reads
`H_max >= L_h + B_cap` straight off this display. -/
def HmaxSched (Lh q1 lq lq2 Bcap : ℕ) : ℕ := Lh + 8 * q1 + lq + lq2 + Bcap + 10

/-- **Aux H1 (`06:808`).**  "Since `H_max >= L_h + B_cap`" -- the frozen
inequality, read off the shape of `eq:Hmax` rather than assumed.  This is the
step the hard-seed clause of the `k_2` endpoint proof needs, and it is exactly
what makes that clause provable here instead of deferred.  General. -/
theorem Hmax_ge_Lh_add_Bcap (Lh q1 lq lq2 Bcap : ℕ) :
    Lh + Bcap ≤ HmaxSched Lh q1 lq lq2 Bcap := by
  rw [HmaxSched]; omega

/-- **Aux H2 (monotone in the auxiliary depth).**  Enlarging `L_h`, the only
Localized-Extension datum `eq:Hmax` reads, never decreases the shared width
threshold.  General. -/
theorem HmaxSched_mono {Lh Lh' q1 lq lq2 Bcap : ℕ} (h : Lh ≤ Lh') :
    HmaxSched Lh q1 lq lq2 Bcap ≤ HmaxSched Lh' q1 lq lq2 Bcap := by
  rw [HmaxSched, HmaxSched]; omega

/-- **Aux H3 (`06:756--757`, the two carriers stay apart).**  The alphabet
floor `v_max` and the depth `L_h` both read `max{q, u_term}`, and `v_max`
never exceeds the depth: `L_h` carries the extra `max{b_2, b_T} + 4`.
General. -/
theorem vMax_le_LhSched (b2 bT q uterm : ℕ) :
    vMax q uterm ≤ LhSched b2 bT q uterm := by
  rw [vMax, LhSched]
  omega

/-- **`K_0 = max{4, 2^19, m_HS}`** (the floor of `eq:t2-search`, `06:766`, named
`K_0` at `eq:k2-tested-endpoint`, `06:776`).

`m_HS` is the banked exponent threshold of `HARD-SEED-FACADE-001`, consumed by
pin; `D:516--517` forbids naming a numeral for it and none appears. -/
noncomputable def k2Floor : ℕ := max (max 4 (2 ^ 19)) mHS.{u}

/-- **`z = max{16, K_0, clog_2(H_max + 1)}`** (`eq:k2-tested-endpoint`,
`06:777`). -/
noncomputable def zEndpoint (Hmax : ℕ) : ℕ :=
  max (max 16 k2Floor.{u}) (Nat.clog 2 (Hmax + 1))

/-- **`k_2^* = K_0 + 10000 z^2`** (`eq:k2-tested-endpoint`, `06:778`). -/
noncomputable def k2Star (Hmax : ℕ) : ℕ :=
  k2Floor.{u} + 10000 * (zEndpoint.{u} Hmax) ^ 2

/-- **`j_2^* = 49 z`** (`06:787`), the displayed feasible `j_49` candidate at
the `k_2` endpoint. -/
noncomputable def j2Star (Hmax : ℕ) : ℕ := 49 * zEndpoint.{u} Hmax

/-- **`eq:k2-j49-candidate` (`06:789--795`).**

"`10000 (j_2^*)^2 = 2401 * 10000 z^2 <= 2401 (K_0 + 10000 z^2) = 2401 k_2^*`."
The exact integer derivation. -/
theorem k2_j49_candidate (Hmax : ℕ) :
    J49Feasible (k2Star.{u} Hmax) (j2Star.{u} Hmax) := by
  rw [J49Feasible, k2Star, j2Star]
  have : 10000 * (49 * zEndpoint.{u} Hmax) ^ 2
      = 2401 * (10000 * zEndpoint.{u} Hmax ^ 2) := by ring
  rw [this]
  exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

/-- **`06:796--797`.**  "The maximality eliminator in `eq:j49-search-data`
therefore gives `49 z <= j_49(k_2^*)`." -/
theorem j2Star_le_j49 (Hmax : ℕ) :
    49 * zEndpoint.{u} Hmax ≤ j49 (k2Star.{u} Hmax) :=
  j49_max (k2_j49_candidate.{u} Hmax)

/-- **`06:804--807`, the elementary base-and-induction inequality.**

"`10001 z^2 + 3 <= 2^{2z}` for `z >= 16`."  Proved outright, by the induction
the frozen text names.  General. -/
theorem k2_elementary_growth {z : ℕ} (hz : 16 ≤ z) :
    10001 * z ^ 2 + 3 ≤ 2 ^ (2 * z) := by
  induction z, hz using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by
        have : 2 * (n + 1) = 2 * n + 2 := by ring
        rw [this, pow_add]; ring
      rw [hstep]
      have h4 : 4 * (10001 * n ^ 2 + 3) ≤ 4 * 2 ^ (2 * n) :=
        Nat.mul_le_mul_left 4 ih
      nlinarith [hn]

/-- **`eq:k2-fixed-growth-lemma` (`06:799--803`), the named integer lemma.**

"`z >= 16  =>  2^{49z} >= H_max + K_0 + 10000 z^2 + 4`."

The frozen proof (`06:804--808`): "`H_max <= 2^z - 1`, `K_0 <= z`, and the
elementary base-and-induction inequality `10001 z^2 + 3 <= 2^{2z}` for
`z >= 16` bound the right side by `2^z + 2^{2z} <= 2^{2z+1} <= 2^{49z}`."
Its two structural premises (`H_max + 1 <= 2^z` and `K_0 <= z`, both immediate
from `eq:k2-tested-endpoint`'s definition of `z`) are explicit binders. -/
theorem k2_fixed_growth_lemma {z Hmax K0v : ℕ} (hz : 16 ≤ z)
    (hH : Hmax + 1 ≤ 2 ^ z) (hK : K0v ≤ z) :
    Hmax + K0v + 10000 * z ^ 2 + 4 ≤ 2 ^ (49 * z) := by
  have hgrow := k2_elementary_growth hz
  have hzz : z ≤ z ^ 2 := Nat.le_self_pow (by norm_num) z
  have hstep : Hmax + K0v + 10000 * z ^ 2 + 4 ≤ 2 ^ z + 2 ^ (2 * z) := by
    have h1 : Hmax ≤ 2 ^ z - 1 := by omega
    have hpos : 1 ≤ 2 ^ z := Nat.one_le_two_pow
    omega
  have hdouble : 2 ^ z + 2 ^ (2 * z) ≤ 2 ^ (2 * z + 1) := by
    have hle : (2 : ℕ) ^ z ≤ 2 ^ (2 * z) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ (2 * z + 1) = 2 ^ (2 * z) + 2 ^ (2 * z) := by
      rw [pow_succ]; ring
    omega
  have hfinal : (2 : ℕ) ^ (2 * z + 1) ≤ 2 ^ (49 * z) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **The `k_2` search predicate** (`eq:t2-search`, `06:765--771`).

The three clauses in the frozen order: `k_2 >= max{4, 2^19, m_HS}`,
`2^{k_2} >= 2 H_max`, and `2^{j_49(k_2)} >= L_h + B_cap + k_2 + 4`. -/
noncomputable def K2Pred (Lh Bcap Hmax : ℕ) (k : ℕ) : Prop :=
  k2Floor.{u} ≤ k ∧ 2 * Hmax ≤ 2 ^ k ∧ Lh + Bcap + k + 4 ≤ 2 ^ j49 k

/-- **`k_2`** (`eq:t2-search`, `06:763`): "the least integer satisfying" those
three clauses.  **`t_2 = 2^{k_2}`** (`06:770`). -/
noncomputable def k2 (Lh Bcap Hmax : ℕ) : ℕ :=
  sInf {k : ℕ | K2Pred.{u} Lh Bcap Hmax k}

/-- **`t_2 = 2^{k_2}`** (`eq:t2-search`, `06:770`). -/
noncomputable def t2 (Lh Bcap Hmax : ℕ) : ℕ := 2 ^ k2.{u} Lh Bcap Hmax

/-- **Aux Z1 (`06:777`, the first branch).**  `16 <= z`, so the `z >= 16`
premise of `eq:k2-fixed-growth-lemma` is discharged by the definition of the
endpoint and never assumed.  General. -/
theorem sixteen_le_zEndpoint (Hmax : ℕ) : 16 ≤ zEndpoint.{u} Hmax :=
  le_trans (le_max_left 16 k2Floor.{u}) (le_max_left _ _)

/-- **Aux Z2 (`06:777`, the second branch).**  `K_0 <= z`, the second premise
of `eq:k2-fixed-growth-lemma`, likewise read off the definition of `z`.
General. -/
theorem k2Floor_le_zEndpoint (Hmax : ℕ) : k2Floor.{u} ≤ zEndpoint.{u} Hmax :=
  le_trans (le_max_right 16 k2Floor.{u}) (le_max_left _ _)

/-- **Aux Z3 (`06:782`).**  "`H_max + 1 <= 2^z`", from the third branch
`z >= clog_2(H_max + 1)` of `06:777` and the defining property of the frozen
`clog_2`.  General. -/
theorem Hmax_succ_le_two_pow_zEndpoint (Hmax : ℕ) :
    Hmax + 1 ≤ 2 ^ zEndpoint.{u} Hmax := by
  refine le_trans (Nat.le_pow_clog (b := 2) (by norm_num) (Hmax + 1)) ?_
  exact Nat.pow_le_pow_right (by norm_num)
    (le_max_right (max 16 k2Floor.{u}) (Nat.clog 2 (Hmax + 1)))

/-- **Aux Z4 (`06:782--783`).**  "the displayed formula gives `k_2^* >= z + 1`",
i.e. `10000 z^2` alone already exceeds `z`.  General. -/
theorem zEndpoint_succ_le_k2Star (Hmax : ℕ) :
    zEndpoint.{u} Hmax + 1 ≤ k2Star.{u} Hmax := by
  have hz := sixteen_le_zEndpoint.{u} Hmax
  have hsq : zEndpoint.{u} Hmax ≤ zEndpoint.{u} Hmax ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  rw [k2Star]
  omega

/-- **Aux Z5 (`06:784--786`, the width clause of `eq:t2-search` at the
endpoint).**

"`2^{k_2^*} >= 2^{z+1} >= 2(H_max + 1) > 2 H_max`."  The frozen three-step
chain, proved outright.  No cutoff record is involved.  General. -/
theorem two_mul_Hmax_le_two_pow_k2Star (Hmax : ℕ) :
    2 * Hmax ≤ 2 ^ k2Star.{u} Hmax := by
  have hstep : (2 : ℕ) ^ (zEndpoint.{u} Hmax + 1) ≤ 2 ^ k2Star.{u} Hmax :=
    Nat.pow_le_pow_right (by norm_num) (zEndpoint_succ_le_k2Star.{u} Hmax)
  have hsucc := Hmax_succ_le_two_pow_zEndpoint.{u} Hmax
  have hsplit : (2 : ℕ) ^ (zEndpoint.{u} Hmax + 1)
      = 2 * 2 ^ zEndpoint.{u} Hmax := by rw [pow_succ]; ring
  calc 2 * Hmax
      ≤ 2 * (Hmax + 1) := by omega
    _ ≤ 2 * 2 ^ zEndpoint.{u} Hmax := Nat.mul_le_mul_left 2 hsucc
    _ = 2 ^ (zEndpoint.{u} Hmax + 1) := hsplit.symm
    _ ≤ 2 ^ k2Star.{u} Hmax := hstep

/-- **`06:813`: the three clauses of `eq:t2-search` hold at the displayed
tested endpoint `k_2^*`.**

"Thus all three clauses of `eq:t2-search` hold at the displayed tested
endpoint" (`06:813`).  This is the **membership** statement of `06:781--812` in
its own right, and it is the sentence the frozen text actually proves before it
takes the minimality step; `06:817--818` says why it has to be a statement
rather than an inference: "Termination and the returned endpoint bound are
therefore checked data, not inferred from the word *least*."

All three clause verifications are carried out here, with no cutoff record and
no deferred premise: the floor clause from `k_2^* >= K_0` (`06:781`), the width
clause from `Hmax_succ_le_two_pow_zEndpoint` and `zEndpoint_succ_le_k2Star`
(`06:782--786`), and the hard-seed clause from `eq:k2-fixed-growth-lemma`
together with `06:808`'s `H_max >= L_h + B_cap`.  That last inequality is the
**only** hypothesis, and it is not an assumption about the search: it is the
shape of `eq:Hmax`, discharged by `Hmax_ge_Lh_add_Bcap` at the reified `H_max`
in `k2_le_star_at_Hmax` below.

**Why this is stated separately from `k2_le_star`** (`cc-t7j`): `k2` is
`sInf {k | K2Pred ...}` and `Nat.sInf` returns `0` on an empty set, so a `<=`
against `sInf` is vacuously available and the conclusion `k_2 <= k_2^*` cannot
be turned back into membership.  Consumers of `eq:t2-search` that need the
clauses *at the accessor* -- i.e. that the search is nonempty at all -- need
this theorem and cannot get it from `k2_le_star`.

**Ownership, stated against the bytes and not on faith** (`cc-t7j-r1`, Sol
finding F-1).  The `cc-t7j` park landed this theorem while
`MassRedistributionTail.K2Pred_at_k2Star` still carried the identical statement
and an identical proof modulo the namespace qualifier -- two owners, and the
short-name check could not see it because the names differ.  That downstream
theorem is **deleted** in this round, not wrapped: endpoint membership is
stated here, once, where the display it verifies is reified;
`k2_le_star` below derives `06:813--814` from it by `Nat.sInf_le`, and
`MassRedistributionTail.K2Pred_at_k2` derives membership at the accessor from
it by `Nat.sInf_mem`.  The direction is the dependency-legal one:
`ParameterSchedule` is in the transitive import closure of every consumer
(`MassRedistributionTail`, `WrapperMassRedistribution`,
`BalancedFamilyBuilder`), and none of them is in its closure.  So `06:781--812`
is proved in exactly one place on the route.  General in the three schedule
inputs. -/
theorem k2Star_meets_search {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    K2Pred.{u} Lh Bcap Hmax (k2Star.{u} Hmax) := by
  refine ⟨Nat.le_add_right _ _, two_mul_Hmax_le_two_pow_k2Star.{u} Hmax, ?_⟩
  have hgrow := k2_fixed_growth_lemma (z := zEndpoint.{u} Hmax) (Hmax := Hmax)
    (K0v := k2Floor.{u}) (sixteen_le_zEndpoint.{u} Hmax)
    (Hmax_succ_le_two_pow_zEndpoint.{u} Hmax) (k2Floor_le_zEndpoint.{u} Hmax)
  have hk2 : k2Star.{u} Hmax
      = k2Floor.{u} + 10000 * zEndpoint.{u} Hmax ^ 2 := rfl
  have hseed : Lh + Bcap + k2Star.{u} Hmax + 4
      ≤ 2 ^ (49 * zEndpoint.{u} Hmax) := by
    rw [hk2]
    calc Lh + Bcap + (k2Floor.{u} + 10000 * zEndpoint.{u} Hmax ^ 2) + 4
        ≤ Hmax + (k2Floor.{u} + 10000 * zEndpoint.{u} Hmax ^ 2) + 4 :=
          Nat.add_le_add_right (Nat.add_le_add_right hshape _) 4
      _ = Hmax + k2Floor.{u} + 10000 * zEndpoint.{u} Hmax ^ 2 + 4 := by ring
      _ ≤ 2 ^ (49 * zEndpoint.{u} Hmax) := hgrow
  exact le_trans hseed
    (Nat.pow_le_pow_right (by norm_num) (j2Star_le_j49.{u} Hmax))

/-- **`06:813--814`, least-search minimality at the `k_2` tested endpoint.**

"... and least-search minimality gives `k_2 <= k_2^*`."  Exactly that step and
nothing else: the endpoint membership is `k2Star_meets_search` above, consumed
here, and `Nat.sInf_le` is the minimality of the least-search.  The statement
is byte-unchanged from its `cc-t6n-r4` form; only its proof now names the
membership lemma instead of inlining it (`cc-t7j`, zero behaviour change). -/
theorem k2_le_star {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    k2.{u} Lh Bcap Hmax ≤ k2Star.{u} Hmax :=
  Nat.sInf_le (k2Star_meets_search.{u} hshape)

/-- **`06:813--814` at the reified `eq:Hmax`.**

The same endpoint bound with **no hypothesis at all**, because the shape
premise is discharged by `Hmax_ge_Lh_add_Bcap`.  This is the form
`06:781--812` actually proves: at the schedule's own `H_max` the three clauses
of `eq:t2-search` hold unconditionally at `k_2^*`. -/
theorem k2_le_star_at_Hmax (Lh q1 lq lq2 Bcap : ℕ) :
    k2.{u} Lh Bcap (HmaxSched Lh q1 lq lq2 Bcap)
      ≤ k2Star.{u} (HmaxSched Lh q1 lq lq2 Bcap) :=
  k2_le_star.{u} (Hmax_ge_Lh_add_Bcap Lh q1 lq lq2 Bcap)

/-! ## Section 10  Canonical inhabitation: the paper's own scheduled point

`06:525--547` composed with `10-direct-bridge.tex:36--56`.  The Section-6
schedule *is* the instance the Section-10 entry apparatus is applied to, so the
fidelity test of this encoding is whether the paper's own point inhabits it.
Both halves of `eq:direct-entry-gates` are discharged by evaluating the
definitional chain, with `s`, `delta_v(G)`, `zeta`, `b_out`, `q` symbolic. -/

/-- **Canonical inhabitation (the paper's instance).**

At the schedule's own `delta_U = eta_R/(16 q)` and `theta = c_theta/(2Q)`,
where `Q` is the banked least power of two at least `Q_0`, **both** halves of
the banked `EntryGates.directEntryGates` hold at the route's fixed `y = 3/5`.

Every quantity is *evaluated through its defining display* -- `eta_C` from the
frozen protected masses (`eq:fixed-protected-masses`), `eta_R` from `eta_C`
(`eq:eta-choice`), `delta_U` from `eta_R` and `q` (`eq:q-deltaU`), `Q_0` from
`delta_U` and `Q` from `Q_0` (`eq:Q-theta-choice`) -- and **no numeral is
assigned to any defined quantity**.  The only binders are the genuinely free
inputs of `06:4--7`: the source scale `s`, the source-side scalars
`delta_v(G)` and `zeta`, the requested output depth `b_out`, and the interlace
width `q`.

The first half is `eq:direct-theta-gates`, second row (`06:543`); the second
half is the banked `EntryGates.secondEntryGate_of_deltaU_small`, whose
hypothesis `delta_U <= 1/60` the schedule's own `eta_R` supplies through
`deltaU_le_gates` -- i.e. the finite gate `06:547` is *discharged*, not
imposed. -/
theorem schedule_fires_directEntryGates {s : ℕ} {dv zeta : ℝ} {q bout : ℕ}
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) :
    directEntryGates bout (deltaU (etaR s dv zeta) q)
      (theta (Qwidth bout (deltaU (etaR s dv zeta) q))) (3 / 5) := by
  have hpos : 0 < deltaU (etaR s dv zeta) q :=
    deltaU_pos (etaR_pos hs hdv hz) hq
  have hsmall := (deltaU_le_gates (s := s) (dv := dv) (zeta := zeta) hq).2
  refine ⟨?_, secondEntryGate_of_deltaU_small hpos hsmall⟩
  have h := (four_Q0_theta_le bout (deltaU (etaR s dv zeta) q)).1
  have h2 := (four_Q0_theta_le bout (deltaU (etaR s dv zeta) q)).2
  linarith

/-- **Non-vacuity: the schedule's own row threshold is inside the frozen
range.**

`03-parameterized-construction.tex:92` demands `0 < theta <= 1/4` of the public
rational, and `10-direct-bridge.tex:39` demands `0 < theta <= 1`.  The
schedule's `theta(Q)` clears both at the banked `Q`, whose exponent
`EntryGates.four_le_rQ` puts at `>= 4`.  So the canonical instance does not sit
on a boundary. -/
theorem schedule_theta_in_range (bout : ℕ) (δU : ℝ) :
    0 < theta (Qwidth bout δU) ∧ theta (Qwidth bout δU) ≤ 1 / 4 := by
  have hQpos : 0 < Qwidth bout δU := Nat.two_pow_pos _
  have h4 : 4 ≤ rQ bout δU := four_le_rQ bout δU
  have hQ16 : (16 : ℕ) ≤ Qwidth bout δU := by
    rw [Qwidth]
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ rQ bout δU := Nat.pow_le_pow_right (by norm_num) h4
  have hQ16R : (16 : ℝ) ≤ ((Qwidth bout δU : ℕ) : ℝ) := by exact_mod_cast hQ16
  refine ⟨theta_pos hQpos, ?_⟩
  rw [theta_eq_delta, deltaFixed_eq]
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Hypothesis-consistency probe, at the *evaluated* scheduled point.**

The full hypothesis bundle of `schedule_fires_directEntryGates` is exhibited
satisfiable in the kernel *together with its conclusion*, so no `False`
derives from it and the canonical instance is not vacuous.

**Nothing here is a chosen numeral.**  Both quantities the probe supplies are
*defined* by `sec:parameters`, and each is pinned by an equation to the value
its own defining chain returns, evaluated in dependency order:

* `s = sScale B_s (uAux (Apre b_out B_pub z_R clog_2(|E|+2)))` is
  `eq:s-choice` (`06:109--121`) evaluated -- `A_pre`, then `u`, then
  `s = 2^{ceil(B_s u^2)}`.  Its two legality facts are then *read off the
  chain*, not assumed: `3 < s`, which `eq:eta-choice` needs, and `64 | s`,
  which `06:975` records and `eq:hard-seed-width-gates` (`06:264--269`)
  demands through `16 | (s/4)`.  Both follow from `u >= 3`, which
  `three_le_uAux` derives from the first branch `16` of `A_pre`.
  A numeral for `s` -- even `64`, the value `06:975` bounds it below by --
  would be an *assignment* to a quantity `eq:s-choice` already fixes, and none
  appears.
* `q = qWrap A_wrap (LPwidth (P0sched C_cert s log_2 q_2 ceil(log_2 U_0) z_R))`
  is `eq:q-deltaU` (`06:514--519`) evaluated at the *defined* exponent
  `L_P = clog_2(P_0)` of `06:471`, whose floor `4 <= L_P` comes from the first
  branch `16` of `P_0`.  Evaluating `qWrap` at a self-chosen exponent -- say
  `L_P = 1` -- would sit *below* that floor and is therefore not a legal
  scheduled point; the exponent here is the one the chain returns.

The remaining inputs are the genuinely free ones and stay **universally
quantified**: the public data `b_out`, `B_pub`, `z_R`, `clog_2(|E|+2)`, the
Section-6 quantities `C_cert`, `log_2 q_2`, `ceil(log_2 U_0)` whose defining
displays are outside this module's scope, the configuration fields `B_s`
(positive, `06:56`) and `A_wrap` (strictly above `c_seed`, `06:1671`), and the
source-side scalars `delta_v(G)` and `zeta` that `eq:eta-choice` reads from the
guarded source.  The three named hypotheses `1 <= B_s`, `1 <= b_out` and
`c_seed < A_wrap` are exactly the frozen legality of those fields, and none of
them fixes a value.

The witnesses are not free: the two defining equations determine `s` and `q`
uniquely from the binders, so a "take something convenient" witness does not
satisfy this statement. -/
theorem scheduledPoint_hypotheses_consistent
    {bout Bpub zR clE Bs Ccert lq2 clU0 Awrap : ℕ} {dv zeta : ℝ}
    (hBs : 1 ≤ Bs) (hbout : 1 ≤ bout) (hAwrap : cSeed < Awrap)
    (hdv : 0 < dv) (hz : 0 < zeta) :
    ∃ s q : ℕ,
      s = sScale Bs (uAux (Apre bout Bpub zR clE)) ∧
      q = qWrap Awrap (LPwidth (P0sched Ccert s lq2 clU0 zR)) ∧
      3 < s ∧ 64 ∣ s ∧ 0 < q ∧ 1 ≤ bout ∧
      4 ≤ LPwidth (P0sched Ccert s lq2 clU0 zR) ∧ 101 ≤ Awrap ∧
        directEntryGates bout (deltaU (etaR s dv zeta) q)
          (theta (Qwidth bout (deltaU (etaR s dv zeta) q))) (3 / 5) := by
  have hfloor := sScale_floor hBs (three_le_uAux bout Bpub zR clE)
  refine ⟨sScale Bs (uAux (Apre bout Bpub zR clE)), _, rfl, rfl,
    hfloor.1, hfloor.2, qWrap_pos _ _, hbout,
    four_le_LPwidth_sched _ _ _ _ _, hundredOne_le_of_cSeed_lt hAwrap, ?_⟩
  exact schedule_fires_directEntryGates hfloor.1 hdv hz (qWrap_pos _ _)

/-- **Canonical inhabitation of the three named search gates, with symbolic
exponents.**

The paper's scheduled point for `eq:terminal-wrapper-gates`: the reference
endpoint `k_ref <= 100 L_P^2` of `06:627` feeds the third row through pure
exponent arithmetic, and the two audit majorants of `06:744--747` feed the
first two.

**Both floors are the paper's own, at its own least admissible point.**
`4 <= L_P` is `four_le_LPwidth` -- the consequence of the first branch
`16` of `P_0` at `06:467--471`.  `101 <= A_wrap` is
`hundredOne_le_of_cSeed_lt` -- the exact integer content of the *strict*
comparison `A_wrap > c_seed` at `06:1671` together with the fixed choice
`c_seed = 100` at `06:578`.  Their product suffices, because
`101 L_P^2 = 100 L_P^2 + L_P^2 >= 100 L_P^2 + 16`; the frozen text never
displays `102`, and demanding it would exclude the paper's own least
admissible pair `(A_wrap, L_P) = (101, 4)`.  All of `L_P`, `A_wrap`, `k_ref`,
`E_T`, `u_term`, `B_theta` stay symbolic. -/
theorem terminalWrapperGates_at_reference_endpoint {Awrap LP kref ETv utermv
    Bthetav : ℕ}
    (hLP : 4 ≤ LP) (hA : 101 ≤ Awrap)
    (hkref : kref ≤ 100 * LP ^ 2)
    (hfirst : 8 * max 1 ETv ≤ 2 ^ (100 * LP ^ 2))
    (hsecond : 4 * ETv * utermv * Bthetav < 2 ^ (100 * LP ^ 2)) :
    terminalWrapperGates (qWrap Awrap LP) ETv utermv Bthetav (2 ^ kref) := by
  have hLP2 : 16 ≤ LP ^ 2 := by nlinarith
  have hexp : 100 * LP ^ 2 ≤ Awrap * LP ^ 2 :=
    Nat.mul_le_mul_right _ (by omega)
  have hkexp : kref + 2 ≤ Awrap * LP ^ 2 := by
    have h101 : 101 * LP ^ 2 ≤ Awrap * LP ^ 2 :=
      Nat.mul_le_mul_right _ hA
    nlinarith
  exact terminalWrapperGates_at_scheduled_point (e := 100 * LP ^ 2) hfirst
    hsecond hexp hkexp

end EthInapproximability.ParameterizedNP.ParameterSchedule
