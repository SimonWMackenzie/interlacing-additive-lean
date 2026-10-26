import EthInapproximability.ParameterizedNP.IterationAssembly
import EthInapproximability.ParameterizedNP.ParameterSchedule

/-!
# Parameterized NP route: the level-indexed carrier specification
(`thm:fixed-level-gap-size` clause (ii), `eq:fixed-level-carriers`)

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger rows: opened under **`SIZE-001`** (the level-indexed half of the exact
carrier growth); the seed-accessor landing of Part 0 is recorded against
**`SEED-001`**'s Lean column, and the *per-step* form of the same recurrence
stays with **`ITER-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`).

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

## What this module lands

`12-iteration-specification.tex`, `thm:fixed-level-gap-size` (label line 192),
clause (ii) at lines 255--265:

```
m_{N,i} = |Rows(N_i)|,   n_{N,i} = |Cols(N_i)|,
m_{i+1} = (q_i m_{N,i})^{Q_i},   n_{i+1} = Q_i (n_{N,i})^{q_i}      (12:261--263)
```

described by frozen line 258 as "the exact, rather than asymptotic, recurrence"
that "the carrier clause C4 of `thm:one-level` gives".

The banked `IterationAssembly.iterationCarrierStep` already owns **one step** of
this, at one matrix and one pair of widths.  What is new here is the
**level-indexed family**: a zero-based specification carrying the whole schedule
`i = 0, 1, 2, ...` at once, in which

* **level zero is anchored to the banked one-level base by pin.**  The frozen
  application site `12:360--368` sets
  `b_i = B(n)` for every `i`, `R_0 = Can(F_{B(n)})`, `m_0 = |Rows(F_{B(n)})|`
  and `n_0 = |Cols(F_{B(n)})|`.  `SeedAnchored` is exactly those three
  equations, with `B(n)` taken through the banked `IterationAssembly.depthB`
  and `F_b` through the banked `OneLevelCompletion.fullCube` at the reified
  width `q_seed`.  No level-zero carrier is a numeral: both are *evaluated*
  through the definitional chain
  `n -> ellN n -> depthB n -> aSeed -> qSeed -> (2 ^ qSeed, qSeed)`.
* **the two interlace widths stay distinct and carry no numerals.**  The inner
  scale-alignment width is `q_i = 2^{A_wrap,i L_{P,i}^2}` through the banked
  `ParameterSchedule.qWrap` (`eq:q-deltaU`, `06-parameter-schedule.tex:515`);
  the outer bridge width is `Q_i` through the banked `EntryGates.Qwidth`, which
  the banked `ParameterSchedule.entry_Qwidth_eq_leastPowTwoGe` pins to the
  schedule's own least-power-of-two accessor at `Q_0` (`eq:Q-theta-choice`).
  Neither width is ever assigned an integer here, and
  `widths_are_not_interchangeable` is a kernel separation of the two roles: `q`
  multiplies and `Q` exponentiates on the row side, and the roles are exchanged
  on the column side.
* **every schedule quantity runs through a banked `ParameterSchedule` def.**
  `A_wrap` through `IterationAssembly.awrap` at the banked
  `ParameterSchedule.cSeed`, `L_P` through `ParameterSchedule.LPwidth` at
  `ParameterSchedule.P0sched`, `Q` through `EntryGates.Qwidth`, `q` through
  `ParameterSchedule.qWrap`, `delta_U` through `ParameterSchedule.deltaU` at
  `ParameterSchedule.etaR`, `B(n)` through `IterationAssembly.depthB`.  Nothing
  below re-derives any of them.  In particular `delta_U` is a **DEFINED**
  schedule quantity, not a free input: `eq:q-deltaU`
  (`06-parameter-schedule.tex:513--519`) fixes *both* widths of its display by
  equality, `q = 2^{A_wrap L_P^2}` at line 515 and `delta_U = eta_R/(16q)` at
  line 517, so the canonical instance of Part 5 obtains it by **evaluating that
  chain at the inner width `q`**, never by assignment and never at the outer
  width `Q`.
* **the seed minimality rule is reified rather than evaluated at one depth.**
  `12:16--21` fixes `a_seed >= 3` to be the **least** integer with
  `q_seed = 2^{a_seed} - 2 >= 64(b+1)`.  `aSeed` is that least-integer
  accessor and `qSeed` its width; the banked `OneLevelCompletion` pinned only
  the two numerals `a_seed = 7`, `q_seed = 126` obtained by evaluating the rule
  at the out-of-range `b = 0`, and `aSeed_at_banked_depth_zero` reproduces
  exactly those numerals from the accessor so the banked pin is checked rather
  than re-asserted.

The **conclusion** `eq:fixed-level-carriers` is *derived*, never a field: the
specification carries schedule inputs and legality guards only, the carriers are
*defined* by the banked step functions
`IterationAssembly.carrierRowNext` / `.carrierColNext`, and
`fixedLevelCarriers_realized` proves that the family so defined is exactly what
the banked one-level construction produces at each level.

## Reader counterparts

The reader artifact of the same frozen release,
`.../reader-facing/sections/05-iteration.tex`, was opened first-hand this
tranche and every cited item read.

**Claimed:** `thm:paper-finite-iteration` (label line 120), **hypothesis lines
121--122 only** --

> "Fix `k >= 0`, and fix any public sequence of `k` legal calls to the one-level
> amplifier."

-- to `LevelCarrierSpec`, which is exactly that public sequence: schedule
inputs and legality guards, one entry per level, with no promise field.  The
banked `ITER-001` tranche partitioned this theorem's *conclusions* (lines
129--133, 137, 138 and 143) across four declarations; the hypothesis line was
not assigned to any of them and is not assigned to any other row.

**Deliberately not claimed**, to avoid a double assignment:

* `lem:paper-full-cube-seed` (label line 27, statement lines 28--44), whose
  lines 28--31 are the reader form of the minimality rule reified in Part 0, is
  **`SEED-001`'s reader item** ("not assigned to any other row", ledger line
  158) and was already declined on those grounds by `BRIDGE-COMPLETION-001`.
  It is named here as navigation only; the Part 0 landing is recorded in
  `SEED-001`'s Lean column.
* `eq:paper-exact-carrier-recurrence` (label line 166) is claimed by
  `IterationAssembly.iterationCarrierStep`; `eq:paper-log-carrier-recurrence`
  (label line 174) and `eq:paper-fixed-level-growth` (label line 289) are
  claimed by `SizePropagation`; lines 280--283 are the navigation locus of
  `OneLevelCompletion.pinnedOutput_carriers_invariant`; line 272 is
  `IterationAssembly.depthThread_constant`'s.  None of them is re-claimed.
* Reader lines 91--94 ("We use the same gap source at every level.  All widths
  are functions of that source and of the public seed, budgets, and requested
  depths; none depends on which promise holds.  Let `R_i` denote the seed
  entering level `i`, and let `N_i` be the protected Stage-4 matrix") state
  precisely the promise-freedom and public-data character of `LevelCarrierSpec`,
  but they are **proof-adjacent prose inside a subsection preamble, not a
  labelled statement**, so they are named as navigation and not claimed.

Crosswalk row: `READER_CROSSWALK.md` row 12 ("Slow iteration, padding, and ETH
interface").

## Dependencies, imports, external adapters

* Imports `IterationAssembly.lean` and `ParameterSchedule.lean` only, hence
  transitively `OneLevelAssembly`, `OneLevelCompletion`, `EntryGates`,
  `BridgeOutputEquality`, the wrapper chain, and `EthInapproximability.Prelude`,
  and through it `LegacyNPCC.Core` (project-axiom-free) and `LegacyNPCC.Bridge`.
  `LegacyNPCC.Stage12` is **not** imported, so the cited AGHP balanced-family
  axiom stays outside this module's closure.  There is no contact with
  `EXPANDER-001`, which by design has no Lean declaration; nothing below turns a
  cited external interface into an axiom.
* Consumed, never edited, widened or re-proved (names grep-verified against the
  banked sources before use):
  * `OneLevelAssembly.oneLevelAssembly_carriers` -- clause C4a, the exact
    double-interlace carrier equations at one level;
  * `IterationAssembly.carrierRowNext`, `.carrierColNext` -- the two halves of
    `eq:fixed-level-carriers` as banked step functions;
  * `IterationAssembly.depthB`, `.depthB_ge`, `.ellN` -- the scheduled depth
    thread `B(n) = E_2(n)` and its floor `512`;
  * `IterationAssembly.awrap`, `.coefficientPass_awrap` -- `A_wrap`;
  * `ParameterSchedule.qWrap`, `.LPwidth`, `.P0sched`, `.cSeed`,
    `.four_le_LPwidth_sched`, `.hundredOne_le_of_cSeed_lt`,
    `.entry_Qwidth_eq_leastPowTwoGe`;
  * `EntryGates.Qwidth`, `.rQ`, `.four_le_rQ`, `.Qwidth_eq_two_pow`;
  * `OneLevelCompletion.fullCube`, `.levelOutput`;
  * `BridgeOutputEquality.rowsCard`, `.colsCard`.
* External theorem adapters: **none new**.
* Proof status: **new (elementary)** throughout -- `Nat.find` minimality,
  monotone power estimates, and applications of the banked route facades.
* Axiom surface (Appendix D; `#print axioms` in `tools/AxiomAudit.lean`): at
  most `propext`, `Classical.choice`, `Quot.sound`.

## Candidate encodings, and the ranking

The genuinely open choice is **where the recurrence lives**.

**Candidate A (landed) -- inputs in the record, carriers defined by the banked
step, realization proved.**  `LevelCarrierSpec` carries the per-level schedule
inputs (`A_wrap`, `L_P`, `b_out`, `delta_U`, the two pre-wrapper counts) and the
two level-zero carriers, plus six legality guards and nothing else.
`rowCarrier` / `colCarrier` are a zero-based definition whose successor clause
is literally `IterationAssembly.carrierRowNext` / `.carrierColNext`, and
`fixedLevelCarriers_realized` proves that these numbers are the cardinalities
the banked `OneLevelCompletion.levelOutput` actually has.  No field is a
conclusion and no field restates a derived telescope.

**Candidate B (refuted) -- the recurrence as a record field.**  Add
`row_rec : forall i, i < k -> m (i+1) = (q i * mN i)^(Q i)` as constructor data.
Refuted on two counts.  (1) Frozen line 258 attributes the recurrence to clause
C4 of `thm:one-level`, i.e. it is a *derived* consequence of the one-level
theorem, and the frozen hypothesis block F2 requires instead the *chaining*
`m_{i+1} = |Rows(R_i^+)|` (`eq:iterated-canonical-chaining`, label line 229);
recording the consequence as a premise deletes the derivation and would make
`fixedLevelCarriers_realized` unprovable-as-content (it would hold by
assumption).  (2) It is exactly the banned "bundle field that restates a derived
telescope": with `rowCarrier` defined by the banked step, the same field is
`rfl`, so it would carry no information while looking like an obligation.

**Candidate C (refuted) -- a dependent per-level carrier *type* family.**
Carry `Row : ℕ -> Type` and `N : forall i, Row i -> Col i -> Bool` and iterate.
Refuted by `def:canonical-reindexing` (`12-iteration-specification.tex`, label
line 107), which closes at line 135 with "It never denotes a heterogeneous
equality of functions": a dependent iteration forces exactly that heterogeneous
carrier equality, and the route has no Lean `Can`.  This is the same refutation
`ITER-001` recorded for its Candidate B, re-checked here at the level-indexed
scale; it is why every statement below is read on `rowsCard` / `colsCard`.

Aux battery: A = 14/14 below.  B cannot state aux 12 (`fixedLevelCarriers` would
be a projection) and fails the non-vacuity gate for the same reason.  C cannot
state aux 5--8 at all.  **A is landed; B and C survive only as their own
refutations.**

## GAP-EXPOSED

1. **No route completion is claimed.**  Nothing below produces a level's
   pre-wrapper matrix `N_i` from the previous level's output `R_i`: the Stage-1
   to Stage-4 chain and the two wrappers (`STAGE1-001` .. `WRAP-001`) are not in
   Lean.  `mN` and `nN` are therefore **explicit binders** of the record --
   `|Rows(N_i)|` and `|Cols(N_i)|` as *recorded public integers*, never as
   derived values -- and `fixedLevelCarriers_realized` takes the level's matrix
   as a hypothesis rather than constructing it.
2. **Canonical inhabitation is landed on the schedule half and deferred on the
   Stage-4 half.**  The frozen application site `12:360--368` is the paper's own
   instance of this record's level-zero data, and `paperSeedSpec` realizes it
   exactly: `b_i = B(n)`, `m_0 = |Rows(F_{B(n)})|`, `n_0 = |Cols(F_{B(n)})|`,
   all evaluated through the definitional chain.  **Every schedule field is
   likewise evaluated, `delta_U` included**: `delta_U,i = eta_R/(16 q_i)` at the
   inner width, through the banked `ParameterSchedule.deltaU` and `.etaR`, with
   only the quantities the schedule layer itself leaves symbolic
   (`s`, `delta_v(G)`, `zeta`, and the recorded coefficient/threshold tables)
   promoted to binders -- which is the precedent set by `ParameterSchedule`'s
   own canonical instance.  The *per-level* fields `mN`, `nN` depend on unbuilt
   Stage-1--4 machinery, so `paperSeedSpec` leaves them as binders and
   `fixedLevelCarriers_fires` quantifies over all legal values; the instance is
   therefore **canonical on everything the schedule fixes and NON-FIDELITY at
   the two Stage-4 counts**, and that residual canonical-inhabitation obligation
   is registered against `SIZE-001` and carried by
   `FIXED-LEVEL-CARRIERS-001` (discharged when `STAGE1-001` .. `WRAP-001` land,
   never by this probe).
3. **`lem:full-cube-seed` is consumed for carriers only.**  Its complexity and
   robustness displays (`12:33--41`) are banked **only at requested depth
   `b = 0`** and at the numerals `a_seed = 7`, `q_seed = 126`
   (`OneLevelCompletion.fullCubeSeed_D`, `.fullCubeSeed_lambda`; that module's
   GAP-EXPOSED 7).  The anchor here runs at `b = B(n) >= 512`, where **neither**
   display is in Lean.  Accordingly `SeedAnchored` pins the two *cardinalities*
   of `F_{B(n)}` and nothing else: no `comp F_{B(n)}`, no
   `Lambda_3(F_{B(n)}, 1, 2^{-B(n)}, 3/5)`, and no `D_0 = Y_0 = a_seed + 1`
   claim is made or used anywhere below.  What the anchor *does* improve on the
   banked pin is the frozen range: `12:16` states the minimality rule for
   `b >= 1`, the banked pin evaluates it at the out-of-range `b = 0`, and
   `seedAnchor_inside_frozen_range` proves `B(n) >= 512 >= 1` for every
   `n >= 1`, so the accessor is used **inside** the rule's own range.
4. **`lem:canonical-reindexing-invariance` is not formalized.**
   `12-iteration-specification.tex` label line 140 is the transport
   `comp Can(M) = comp M` and its bracket analogue.  The frozen chaining
   `R_{i+1} = Can_{m_{i+1},n_{i+1}}(R_i^+)` is therefore read here on
   cardinalities only, which is exactly the data that lemma preserves; the
   invariance itself stays with `ITER-001`.
5. **No *guard* of the record constrains `delta_U`, but the carriers do depend
   on it.**  This is a statement about the six legality guards, and about
   nothing else.  `Q_i = Qwidth (b_out,i) (delta_{U,i})` and
   `rowCarrier (i+1) = (q_i m_{N,i})^{Q_i}`, so `delta_U` enters both carriers
   through the outer width; what is true is only that the record imposes no
   lower or upper bound on it and that `sixteen_le_Q` holds **unconditionally**
   from the banked `EntryGates.four_le_rQ`, since `EntryGates.Qwidth` is total
   in `delta_U`.  Totality of the width is therefore not a licence to treat
   `delta_U` as free data: it is DEFINED by `eq:q-deltaU` (`06:517`) and the
   canonical instance evaluates it (GAP-EXPOSED 2).  A level's *complexity*
   conclusions do need `directEntryGates`, and those are the banked
   `OneLevelAssembly.oneLevelAssembly_yes` / `.oneLevelAssembly_no`, which
   nothing here restates or weakens.
6. **The size envelope is not claimed.**  `eq:paper-fixed-level-growth`
   (`z(R_j) <= E_{c_j}(n)`, reader label line 289) and the uniform side
   majorant `exp:E-14-raw` stay with `SIZE-001`/`EFFECTIVE-001`; this module
   states the **exact** carriers and no asymptotic bound on them.  The frozen
   clause quantifies `0 <= i < k`; every theorem below is general in `i`, which
   is strictly stronger, and `k` therefore appears nowhere as data.
-/

namespace EthInapproximability.ParameterizedNP.FixedLevelCarriers

open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.BridgeOutputEquality
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.OneLevelAssembly
open EthInapproximability.ParameterizedNP.IterationAssembly

/-! ## Part 0: the seed accessors of `sec:full-cube-seed`

`12-iteration-specification.tex:16--21` fixes `a_seed` by a **least-integer
rule**, not by a numeral.  Part 0 reifies that rule, so that every level-zero
carrier below is obtained by evaluating a definitional chain rather than by
assignment.  These declarations belong to `SEED-001`'s Lean column; the reader
item `lem:paper-full-cube-seed` is that row's and is named here as navigation
only. -/

/-- The seed exponent rule of `12:16--21` is inhabited at every requested depth.

The witness is `a = b + 7`: then `2^{b+7} = 128 * 2^b >= 128(b+1) >= 64b + 66`,
so `2^a - 2 >= 64(b+1)`, and `b + 7 >= 3`.  Recorded as a lemma because
`Nat.find` needs it; it asserts nothing about minimality. -/
lemma seedExp_exists (b : ℕ) : ∃ a : ℕ, 3 ≤ a ∧ 64 * (b + 1) ≤ 2 ^ a - 2 := by
  refine ⟨b + 7, by omega, ?_⟩
  have hb : b + 1 ≤ 2 ^ b := Nat.lt_two_pow_self
  have hp : 2 ^ (b + 7) = 2 ^ b * 128 := by rw [pow_add]; norm_num
  omega

/-- **`a_seed`** -- `12-iteration-specification.tex:16--21`, "Let
`a_seed >= 3` be the least integer for which `q_seed = 2^{a_seed} - 2 >=
64(b+1)`"; reader `lem:paper-full-cube-seed` lines 28--31 (`SEED-001`'s item,
navigation only here).

The **least-integer accessor**, not an evaluation of it.  Public data: a
function of the requested depth alone, with no promise case, no certificate and
no complexity or robustness field. -/
def aSeed (b : ℕ) : ℕ := Nat.find (seedExp_exists b)

/-- **`q_seed = 2^{a_seed} - 2`** -- the same display, `12:19--20`. -/
def qSeed (b : ℕ) : ℕ := 2 ^ aSeed b - 2

/-- **The full-cube seed `F_b` at the reified width** -- `eq:full-cube-seed`
(`12-iteration-specification.tex`, label line 29, display lines 23--30),
consumed through the banked `OneLevelCompletion.fullCube`.

**Carriers only.**  Neither display of `lem:full-cube-seed` is available at a
general `b` (GAP-EXPOSED 3); this abbreviation exists so that the level-zero
anchor can name the paper's own matrix when pinning `m_0` and `n_0`, and it is
never used to assert `comp F_b` or a robustness rung. -/
def seedMatrix (b : ℕ) : (Fin (qSeed b) → Bool) → Fin (qSeed b) → Bool :=
  fullCube (qSeed b)

/-! ## Part 1: the two interlace widths, level-indexed

Both widths are carried as *functions of the level index*, through banked
schedule definitions, and they are never conflated: `q_i` is the inner
scale-alignment width of `eq:q-deltaU` and `Q_i` the outer bridge width of
`eq:Q-theta-choice`.  No numeral is assigned to either. -/

/-- **`log_2 q_i = A_wrap,i L_{P,i}^2`** -- the exponent of `eq:q-deltaU`
(`06-parameter-schedule.tex:515`), level-indexed.

The banked `OneLevelCompletion.levelOutput` takes the inner width by its
**exponent** (`q = 2^{w_q}`), which is why this is the quantity handed to it. -/
def innerExp (Awrap LP : ℕ → ℕ) (i : ℕ) : ℕ := Awrap i * LP i ^ 2

/-- **`q_i = 2^{A_wrap,i L_{P,i}^2}`** -- `eq:q-deltaU`
(`06-parameter-schedule.tex:515`) through the banked
`ParameterSchedule.qWrap`, level-indexed.  Reader
`03-parameterized-construction.tex:81--82`. -/
def innerWidth (Awrap LP : ℕ → ℕ) (i : ℕ) : ℕ :=
  ParameterSchedule.qWrap (Awrap i) (LP i)

/-- **`Q_i`** -- the outer bridge width, level-indexed, through the banked
`EntryGates.Qwidth`.

`ParameterSchedule.entry_Qwidth_eq_leastPowTwoGe` pins that accessor to the
schedule's own least-power-of-two search at the threshold `Q_0` of
`eq:Q-theta-choice` (`06-parameter-schedule.tex:529--531`), so this is the
schedule's width and not a second search. -/
noncomputable def outerWidth (bout : ℕ → ℕ) (dU : ℕ → ℝ) (i : ℕ) : ℕ :=
  Qwidth (bout i) (dU i)

/-! ## Part 2: the level-indexed specification

The record carries **schedule inputs and legality guards only**.  It has no
complexity, robustness or promise field (mechanical rules M1, M2, M4), no
carrier *type* family (GAP-EXPOSED 4), and no field stating the recurrence
(Candidate B). -/

/-- **A public sequence of legal one-level calls, zero-based.**

Autoformalization anchor: `thm:fixed-level-gap-size`
(`12-iteration-specification.tex`, label line 192), hypothesis block F1--F2 at
lines 195--245, restricted to the data clause (ii) reads:  the per-level
schedule inputs, and the two carrier sequences.

Reader counterpart: `thm:paper-finite-iteration` (`05-iteration.tex`, label line
120) **hypothesis lines 121--122 only**, "Fix `k >= 0`, and fix any public
sequence of `k` legal calls to the one-level amplifier".  The theorem's
conclusions (lines 129--133, 137, 138, 143) belong to `ITER-001`'s four
declarations and are not re-claimed.

**Zero-based index.**  Level `0` is the base and level `i + 1` the output of the
`i`-th call, matching `conv:finite-slots` and the frozen `0 <= i < k`.  The
families are total on `ℕ`: `k` is where a caller stops, and every theorem below
is general in `i`, which is strictly stronger than the frozen range
(GAP-EXPOSED 6).

**What each field is.**
* `Awrap i`, `LP i` -- the coefficient-audit constant `A_wrap` and the
  first-wrapper exponent `L_P` at level `i`; `06:520--522` records that `A_wrap`
  "is fixed universally below" and never depends on a reached transcript, so
  neither is a numeral here.
* `bout i` -- the outgoing requested depth `b_{i+1}` of the level's public
  record (`12:205--211`).
* `dU i` -- the deletion tolerance `delta_{U,i}` the bridge consumes
  (`eq:q-deltaU`, `06:517`).
* `mN i`, `nN i` -- `|Rows(N_i)|` and `|Cols(N_i)|` for the pre-wrapper matrix
  field `N_i` of the trace `T_i` (`12:255--257`), as **recorded public
  integers**: the chain producing `N_i` from `R_i` is not in Lean
  (GAP-EXPOSED 1).
* `mBase`, `nBase` -- `m_0` and `n_0`, the level-zero carriers of F2.

**The six guards.**  `1 <= Awrap i` and `1 <= LP i` are the frozen legality
`q = 2^{w_q} >= 2` of `02-mechanical-contract.tex:771--775` in exponent form;
`1 <= mN i`, `1 <= nN i`, `1 <= mBase`, `1 <= nBase` are the frozen positivity
"fix positive integers `m_i, n_i, b_i`" of `12:201--203` together with the
realized-input invariant "`m_N, n_N >= 1`" of `02:771--775`.  All six are lower
bounds on widths and carriers and never upper bounds. -/
structure LevelCarrierSpec where
  /-- `A_wrap` at each level (`06:520--522`). -/
  Awrap : ℕ → ℕ
  /-- `L_P` at each level (`06:471`). -/
  LP : ℕ → ℕ
  /-- The outgoing requested depth `b_{i+1}` at each level (`12:205--211`). -/
  bout : ℕ → ℕ
  /-- The deletion tolerance `delta_U` at each level (`06:517`). -/
  dU : ℕ → ℝ
  /-- `m_{N,i} = |Rows(N_i)|` (`12:255--256`), a recorded public integer. -/
  mN : ℕ → ℕ
  /-- `n_{N,i} = |Cols(N_i)|` (`12:256--257`), a recorded public integer. -/
  nN : ℕ → ℕ
  /-- `m_0`, the level-zero row carrier of F2 (`12:201--203`). -/
  mBase : ℕ
  /-- `n_0`, the level-zero column carrier of F2 (`12:201--203`). -/
  nBase : ℕ
  /-- `q_i >= 2` in exponent form (`02:771--775`). -/
  one_le_Awrap : ∀ i, 1 ≤ Awrap i
  /-- `q_i >= 2` in exponent form (`02:771--775`). -/
  one_le_LP : ∀ i, 1 ≤ LP i
  /-- `m_{N,i} >= 1` (`02:771--775`). -/
  one_le_mN : ∀ i, 1 ≤ mN i
  /-- `n_{N,i} >= 1` (`02:771--775`). -/
  one_le_nN : ∀ i, 1 ≤ nN i
  /-- `m_0 >= 1` (`12:201--203`). -/
  one_le_mBase : 1 ≤ mBase
  /-- `n_0 >= 1` (`12:201--203`). -/
  one_le_nBase : 1 ≤ nBase

namespace LevelCarrierSpec

variable (S : LevelCarrierSpec)

/-- **`q_i`, the inner scale-alignment width at level `i`.** -/
def q (i : ℕ) : ℕ := innerWidth S.Awrap S.LP i

/-- **`log_2 q_i`, the exponent the banked one-level output consumes.** -/
def qExp (i : ℕ) : ℕ := innerExp S.Awrap S.LP i

/-- **`Q_i`, the outer bridge width at level `i`.** -/
noncomputable def Q (i : ℕ) : ℕ := outerWidth S.bout S.dU i

/-- **The row half of the level-indexed carrier family** --
`eq:fixed-level-carriers` (`12-iteration-specification.tex`, label line 264,
display lines 260--265), row equation at line 261:
`m_{i+1} = (q_i m_{N,i})^{Q_i}`.

Zero-based: level `0` is the base carrier `m_0` and the successor clause is the
**banked** `IterationAssembly.carrierRowNext`, consumed by pin rather than
restated.  Noncomputable because `Q_i` runs through the banked real-valued
least-power-of-two search. -/
noncomputable def rowCarrier : ℕ → ℕ
  | 0 => S.mBase
  | i + 1 => carrierRowNext (S.q i) (S.mN i) (S.Q i)

/-- **The column half of the level-indexed carrier family** --
`eq:fixed-level-carriers`, column equation at line 263:
`n_{i+1} = Q_i (n_{N,i})^{q_i}`.

The two widths appear in **exchanged roles** relative to `rowCarrier`: here
`Q_i` multiplies and `q_i` exponentiates.  The successor clause is the banked
`IterationAssembly.carrierColNext`. -/
noncomputable def colCarrier : ℕ → ℕ
  | 0 => S.nBase
  | i + 1 => carrierColNext (S.Q i) (S.nN i) (S.q i)

end LevelCarrierSpec

/-- **The level-zero anchor of the frozen application site** --
`12-iteration-specification.tex:360--368`:

> "For the intended fixed-level application, set `b_i = B(n) = E_2(n)` for every
> `i`, take `R_0 = Can(F_{B(n)})`, `m_0 = |Rows(F_{B(n)})|`,
> `n_0 = |Cols(F_{B(n)})|` ..."

Three equations, in the frozen order, with every quantity taken through a banked
definition: `B(n)` through `IterationAssembly.depthB`, `F_b` through
`seedMatrix` at the reified `qSeed`, and the two carriers through the banked
`rowsCard` / `colsCard`.  **No numeral occurs.**

The frozen sentence also sets `D_0 = Y_0 = comp F_{B(n)} = a_seed + 1`; that
budget identity is *deliberately absent* here, because the complexity display of
`lem:full-cube-seed` is banked only at `b = 0` (GAP-EXPOSED 3).  This predicate
is about carriers and the depth thread, and about nothing else. -/
def SeedAnchored (S : LevelCarrierSpec) (n : ℕ) : Prop :=
  S.bout = (fun _ => depthB n) ∧
    S.mBase = rowsCard (seedMatrix (depthB n)) ∧
    S.nBase = colsCard (seedMatrix (depthB n))

/-! ## Part 3: the aux-lemma battery

Fourteen general properties.  None is about a pinned instance: each quantifies
over arbitrary depths, specifications, levels or carrier counts. -/

/-- **Aux 1 (the reified rule satisfies itself).**

`12:16--21` in both halves: `a_seed >= 3` and `q_seed = 2^{a_seed} - 2 >=
64(b+1)`.  General in the requested depth. -/
theorem aSeed_spec (b : ℕ) : 3 ≤ aSeed b ∧ 64 * (b + 1) ≤ qSeed b :=
  Nat.find_spec (seedExp_exists b)

/-- **Aux 2 (the reified rule is *least*).**

"Let `a_seed >= 3` be the **least** integer for which ..." -- the minimality is
the substantive half of the frozen rule, and without it any large exponent would
do.  General in the depth and in the tested exponent. -/
theorem aSeed_min {b a : ℕ} (h3 : 3 ≤ a) (hge : 64 * (b + 1) ≤ 2 ^ a - 2) :
    aSeed b ≤ a :=
  Nat.find_min' (seedExp_exists b) ⟨h3, hge⟩

/-- **Aux 3 (the seed width is monotone in the requested depth).**

A deeper request never permits a narrower cube: the tested predicate at `b'`
implies the one at `b <= b'`, so minimality transports.  General in both
depths. -/
theorem aSeed_mono {b b' : ℕ} (h : b ≤ b') : aSeed b ≤ aSeed b' := by
  obtain ⟨h3, hge⟩ := aSeed_spec b'
  exact aSeed_min h3 (le_trans (by omega) hge)

/-- **Aux 4 (the seed carriers, evaluated).**

`eq:full-cube-seed` has row set `{0,1}^{q_seed}` and column set `[q_seed]`, so
the two cardinalities of the banked `fullCube` at the reified width are
`2^{q_seed}` and `q_seed`.  This is the evaluation step that makes the level-zero
anchor a *computed* pin rather than an assignment.  General in the depth. -/
theorem seedMatrix_carriers (b : ℕ) :
    rowsCard (seedMatrix b) = 2 ^ qSeed b ∧ colsCard (seedMatrix b) = qSeed b := by
  constructor
  · simp [rowsCard]
  · simp [colsCard]

/-- **Aux 5 (the inner width is legal at every level).**

`q_i = 2^{A_wrap,i L_{P,i}^2} >= 2` -- the frozen `q >= 2` of
`02-mechanical-contract.tex:771--775`, discharged from the record's own two
exponent guards rather than assumed.  General in the specification and the
level. -/
theorem two_le_q (S : LevelCarrierSpec) (i : ℕ) : 2 ≤ S.q i := by
  have hA := S.one_le_Awrap i
  have hL := S.one_le_LP i
  have he : 1 ≤ S.qExp i := by
    have : 1 ≤ S.LP i ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := Nat.mul_le_mul hA this
    simpa [LevelCarrierSpec.qExp, innerExp] using this
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ S.qExp i := Nat.pow_le_pow_right (by norm_num) he
    _ = S.q i := rfl

/-- **Aux 6 (the outer width is legal at every level, unconditionally).**

`Q_i = 2^{r_{Q,i}}` and the banked `EntryGates.four_le_rQ` gives
`r_Q >= 4`, so `Q_i >= 16 >= 2` with **no** gate hypothesis: the carrier
equations consume no entry gate (GAP-EXPOSED 5).  General in the specification
and the level. -/
theorem sixteen_le_Q (S : LevelCarrierSpec) (i : ℕ) : 16 ≤ S.Q i := by
  have h4 : 4 ≤ rQ (S.bout i) (S.dU i) := four_le_rQ _ _
  calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ rQ (S.bout i) (S.dU i) := Nat.pow_le_pow_right (by norm_num) h4
    _ = S.Q i := rfl

/-- **Aux 7 (the row step is monotone in the pre-wrapper row count).**

A general property of the banked `IterationAssembly.carrierRowNext`: growing
`m_N` never shrinks the successor row carrier.  This is what lets a level's
recorded count be replaced by any upper bound in a later size argument.  General
in all four numbers. -/
theorem carrierRowNext_mono (q Q : ℕ) {mN mN' : ℕ} (h : mN ≤ mN') :
    carrierRowNext q mN Q ≤ carrierRowNext q mN' Q :=
  Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h) Q

/-- **Aux 8 (the column step is monotone in the pre-wrapper column count).**

The same for `IterationAssembly.carrierColNext`, with the widths in their
exchanged roles.  General in all four numbers. -/
theorem carrierColNext_mono (Q q : ℕ) {nN nN' : ℕ} (h : nN ≤ nN') :
    carrierColNext Q nN q ≤ carrierColNext Q nN' q :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h q)

/-- **Aux 9 (the realized-input invariant is preserved at every successor).**

`02-mechanical-contract.tex:767--775`: "the exact successor equations give
`m_next = (q m_N)^Q >= 2`, `n_next = Q n_N^q >= 2` because `q, Q >= 2` and
`m_N, n_N >= 1`.  Hence realization preserves the invariant."  All three frozen
premises are discharged from the record's guards and from aux 5--6; none is
assumed.  Reader locus (navigation, already assigned to
`OneLevelCompletion.pinnedOutput_carriers_invariant`):
`05-iteration.tex:280--283`.  General in the specification and the level. -/
theorem carriers_two_le_succ (S : LevelCarrierSpec) (i : ℕ) :
    2 ≤ S.rowCarrier (i + 1) ∧ 2 ≤ S.colCarrier (i + 1) := by
  have hq := two_le_q S i
  have hQ := sixteen_le_Q S i
  have hm := S.one_le_mN i
  have hn := S.one_le_nN i
  constructor
  · change 2 ≤ (S.q i * S.mN i) ^ S.Q i
    have hbase : 2 ≤ S.q i * S.mN i :=
      le_trans hq (Nat.le_mul_of_pos_right _ hm)
    have hstep : S.q i * S.mN i ≤ (S.q i * S.mN i) ^ S.Q i :=
      Nat.le_self_pow (by omega) _
    exact le_trans hbase hstep
  · change 2 ≤ S.Q i * S.nN i ^ S.q i
    have hpow : 1 ≤ S.nN i ^ S.q i := Nat.one_le_pow _ _ hn
    have hstep : S.Q i * 1 ≤ S.Q i * S.nN i ^ S.q i :=
      Nat.mul_le_mul_left _ hpow
    omega

/-- **Aux 10 (the two carrier levels are positive everywhere, base included).**

The level-zero half comes from the record's own two base guards, so the family
is nondegenerate at *every* index and not only above the base.  General. -/
theorem carriers_pos (S : LevelCarrierSpec) (j : ℕ) :
    1 ≤ S.rowCarrier j ∧ 1 ≤ S.colCarrier j := by
  cases j with
  | zero => exact ⟨S.one_le_mBase, S.one_le_nBase⟩
  | succ i =>
    obtain ⟨hr, hc⟩ := carriers_two_le_succ S i
    exact ⟨by omega, by omega⟩

/-- **Aux 11 (the two widths are not interchangeable).**

A statement pole for `eq:fixed-level-carriers`, at the audit point where the
recorded pre-wrapper counts are one: there the row carrier is `q^Q` and the
column carrier is `Q`, and

```
Q < 2^Q <= q^Q
```

so the column value is *strictly* below the row value.  A single carrier
equation, or one that read `q` and `Q` in the same role on both sides, cannot
produce this separation; it is the kernel form of "`q` multiplies on the row
side and exponentiates on the column side".  General in the specification and
the level, under the two recorded counts. -/
theorem widths_are_not_interchangeable (S : LevelCarrierSpec) (i : ℕ)
    (hm : S.mN i = 1) (hn : S.nN i = 1) :
    S.colCarrier (i + 1) < S.rowCarrier (i + 1) := by
  have hq := two_le_q S i
  have hrow : S.rowCarrier (i + 1) = S.q i ^ S.Q i := by
    change (S.q i * S.mN i) ^ S.Q i = _
    rw [hm, Nat.mul_one]
  have hcol : S.colCarrier (i + 1) = S.Q i := by
    change S.Q i * S.nN i ^ S.q i = _
    rw [hn, Nat.one_pow, Nat.mul_one]
  have h1 : S.Q i < 2 ^ S.Q i := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ S.Q i ≤ S.q i ^ S.Q i := Nat.pow_le_pow_left hq _
  omega

/-- **Aux 12 (the exact equations per level, in the frozen spelling).**

`eq:fixed-level-carriers` (`12-iteration-specification.tex`, label line 264,
display lines 260--265) read off the definitions, at **every** level index:

```
m_{i+1} = (q_i m_{N,i})^{Q_i},     n_{i+1} = Q_i (n_{N,i})^{q_i}.
```

This is the readout of the banked step functions; the substantive statement --
that these numbers are the carriers the construction actually has -- is
`fixedLevelCarriers_realized` below.  General in the specification and the
level. -/
theorem fixedLevelCarriers (S : LevelCarrierSpec) (i : ℕ) :
    S.rowCarrier (i + 1) = (S.q i * S.mN i) ^ S.Q i ∧
      S.colCarrier (i + 1) = S.Q i * S.nN i ^ S.q i :=
  ⟨rfl, rfl⟩

/-- **Aux 13 (the anchor's depth sits inside the frozen range).**

`12:16` states the minimality rule for a requested depth `b >= 1`; the banked
seed pin evaluates it at the out-of-range `b = 0`
(`OneLevelCompletion.fullCubeSeed_parameters`).  The application-site depth
`B(n) = E_2(n)` is instead `>= 512` for every `n >= 1`, by the banked
`IterationAssembly.depthB_ge`, so the accessor of Part 0 is used **inside** its
own frozen range.  General in the source size. -/
theorem seedAnchor_inside_frozen_range (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ depthB n ∧ 512 ≤ depthB n := by
  obtain ⟨h512, h1⟩ := depthB_ge n hn
  exact ⟨h1, h512⟩

/-- **Aux 14 (the accessor reproduces the banked depth-zero pin).**

`OneLevelCompletion.fullCubeSeed_parameters` recorded `a_seed = 7`,
`q_seed = 126` as the numerals obtained by evaluating the frozen rule at
`b = 0`.  Evaluating the reified accessor at the same depth returns exactly
those two values, so the banked numerals are **checked against the rule** rather
than re-asserted.  The first legal depth is included for the same reason: at
`b = 1` the rule selects `a_seed = 8`, `q_seed = 254`, which is the value the
banked docstring records and which the depth-zero pin does not see. -/
theorem aSeed_at_banked_depth_zero :
    aSeed 0 = 7 ∧ qSeed 0 = 126 ∧ aSeed 1 = 8 ∧ qSeed 1 = 254 := by
  have h0 : aSeed 0 = 7 := by
    rw [aSeed, Nat.find_eq_iff]
    refine ⟨by norm_num, ?_⟩
    intro j hj
    interval_cases j <;> decide
  have h1 : aSeed 1 = 8 := by
    rw [aSeed, Nat.find_eq_iff]
    refine ⟨by norm_num, ?_⟩
    intro j hj
    interval_cases j <;> decide
  refine ⟨h0, ?_, h1, ?_⟩
  · rw [qSeed, h0]; norm_num
  · rw [qSeed, h1]; norm_num

/-! ## Part 4: the level-indexed carrier specification, realized

The substantive statement of the module: the numeric family of Part 2 is
exactly what the banked one-level construction produces, level by level. -/

/-- **`eq:fixed-level-carriers`, realized against the banked one-level base**
(`12-iteration-specification.tex`, clause (ii), lines 255--265).

Frozen line 258: "the carrier clause C4 of `thm:one-level` gives the exact,
rather than asymptotic, recurrence".  This theorem *is* that attribution, at the
level-indexed family: given any pre-wrapper matrix `N` whose two cardinalities
are the level's recorded counts `m_{N,i}`, `n_{N,i}`, the banked one-level
output `R_i^+ = levelOutput N (log_2 q_i) b_{i+1} delta_{U,i}` has exactly the
carriers `m_{i+1}`, `n_{i+1}` of the specification.

The proof is the frozen one and re-proves nothing: the banked
`OneLevelAssembly.oneLevelAssembly_carriers` (clause C4a) applied once, read
through the two banked step names.  Its own conditional status is discharged
here rather than inherited: the guard `hq : 1 <= w_q` -- the frozen legality
`q = 2^{w_q} >= 2` of `02-mechanical-contract.tex:771--775` -- is supplied from
the record's two exponent guards.

The two conclusions are stated on the **cardinalities** `|Rows(R_i^+)|` and
`|Cols(R_i^+)|`, which is the frozen chaining `m_{i+1} = |Rows(R_i^+)|`,
`n_{i+1} = |Cols(R_i^+)|` of `eq:iterated-canonical-chaining` (label line 229)
and exactly the data `lem:canonical-reindexing-invariance` preserves
(GAP-EXPOSED 4).  The matrix `N` is a **hypothesis**, not a construction: the
chain producing it is not in Lean (GAP-EXPOSED 1).

Reader locus (navigation only; the labelled display
`eq:paper-exact-carrier-recurrence` is `ITER-001`'s):
`05-iteration.tex:157--167`. -/
theorem fixedLevelCarriers_realized {X Y : Type*} [Fintype X] [Fintype Y]
    (S : LevelCarrierSpec) (i : ℕ) (N : X → Y → Bool)
    (hm : rowsCard N = S.mN i) (hn : colsCard N = S.nN i) :
    rowsCard (levelOutput N (S.qExp i) (S.bout i) (S.dU i)) = S.rowCarrier (i + 1) ∧
      colsCard (levelOutput N (S.qExp i) (S.bout i) (S.dU i))
        = S.colCarrier (i + 1) := by
  have hA := S.one_le_Awrap i
  have hL := S.one_le_LP i
  have hq : 1 ≤ S.qExp i := by
    have h1 : 1 ≤ S.LP i ^ 2 := Nat.one_le_pow _ _ (by omega)
    have := Nat.mul_le_mul hA h1
    simpa [LevelCarrierSpec.qExp, innerExp] using this
  obtain ⟨-, -, hrow, hcol⟩ :=
    oneLevelAssembly_carriers N (S.qExp i) (S.bout i) (S.dU i) hq
  refine ⟨?_, ?_⟩
  · rw [hrow, hm]
    rfl
  · rw [hcol, hn]
    rfl

/-- **The level-zero anchor, evaluated** -- `12:360--368`.

Under `SeedAnchored`, the two base carriers of the specification are the two
cardinalities of the paper's own seed at the paper's own depth, and both are
*computed* through the definitional chain
`n -> ellN n -> depthB n -> aSeed -> qSeed`:

```
m_0 = 2^{q_seed(B(n))},     n_0 = q_seed(B(n)),     b_i = B(n) for every i.
```

Carriers and the depth thread only: no complexity and no robustness statement
about `F_{B(n)}` is made here, because neither display of `lem:full-cube-seed`
is banked at that depth (GAP-EXPOSED 3).  General in the source size. -/
theorem seedAnchored_carriers {S : LevelCarrierSpec} {n : ℕ}
    (h : SeedAnchored S n) :
    S.rowCarrier 0 = 2 ^ qSeed (depthB n) ∧
      S.colCarrier 0 = qSeed (depthB n) ∧
      ∀ i, S.bout i = depthB n := by
  obtain ⟨hb, hmB, hnB⟩ := h
  obtain ⟨hrow, hcol⟩ := seedMatrix_carriers (depthB n)
  refine ⟨?_, ?_, ?_⟩
  · change S.mBase = _
    rw [hmB, hrow]
  · change S.nBase = _
    rw [hnB, hcol]
  · intro i
    rw [hb]

/-! ## Part 5: non-vacuity

The paper's own level-zero instance, plus the firing theorem.  Per the
canonical-inhabitation discipline: level zero is the **paper's** instance
(`12:360--368`), evaluated; the per-level pre-wrapper counts depend on unbuilt
Stage-1--4 machinery and are therefore left as binders, which makes the instance
NON-FIDELITY above level zero and leaves that obligation registered
(GAP-EXPOSED 2). -/

/-- **The paper's fixed-level application, as a specification.**

`12-iteration-specification.tex:360--368`, with every quantity taken through a
banked definition and **no numeral assigned**:

* `b_i = B(n)` for every `i` -- `IterationAssembly.depthB`;
* `m_0 = |Rows(F_{B(n)})|`, `n_0 = |Cols(F_{B(n)})|` -- `seedMatrix` at the
  reified `qSeed`, through the banked `rowsCard` / `colsCard`;
* `A_wrap` -- the banked search `IterationAssembly.awrap` at the banked
  `ParameterSchedule.cSeed`, applied to a *recorded* coefficient table
  `(C_exc^0, B_exc^0)` which the frozen `step:I-01` treats as arbitrary recorded
  data;
* `L_P` -- the banked `ParameterSchedule.LPwidth` at the banked
  `ParameterSchedule.P0sched`;
* `delta_U` -- **evaluated, not assigned and not a binder.**  `eq:q-deltaU`
  (`06-parameter-schedule.tex:513--519`) fixes it by the equality
  `delta_U = eta_R/(16 q)` at line 517, at the *same* display's inner width
  `q = 2^{A_wrap L_P^2}` of line 515.  So the field is the banked
  `ParameterSchedule.deltaU` applied to the banked
  `ParameterSchedule.etaR` (the reification of `eq:eta-choice`, `06:212--217`)
  and to `innerWidth` at **this instance's own `A_wrap` and `L_P`** -- the
  paper's width branch, never the outer `Q` and never the `16` floor of
  `eq:Q-theta-choice`.  Only `s`, `delta_v(G)` and `zeta`, which the schedule
  layer itself leaves symbolic, remain universally quantified, exactly as in
  `ParameterSchedule`'s own canonical instance.

**`mN` and `nN` are binders (NON-FIDELITY at the two Stage-4 counts).**  They
are `|Rows(N_i)|`, `|Cols(N_i)|` for the unbuilt Stage-4 trace field, so no
value for them is paper-derived yet; they are taken as arguments with their
frozen positivity guards, which is strictly stronger than choosing values and is
the registered deferral of GAP-EXPOSED 2. -/
noncomputable def paperSeedSpec (n C0 B0 Ccert s lq2 clU0 zR : ℕ) (dv zeta : ℝ)
    (mN nN : ℕ → ℕ) (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i) :
    LevelCarrierSpec where
  Awrap := fun _ => awrap ParameterSchedule.cSeed C0 B0
  LP := fun _ => ParameterSchedule.LPwidth (ParameterSchedule.P0sched Ccert s lq2 clU0 zR)
  bout := fun _ => depthB n
  dU := fun i =>
    ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta)
      (innerWidth (fun _ => awrap ParameterSchedule.cSeed C0 B0)
        (fun _ => ParameterSchedule.LPwidth
          (ParameterSchedule.P0sched Ccert s lq2 clU0 zR)) i)
  mN := mN
  nN := nN
  mBase := rowsCard (seedMatrix (depthB n))
  nBase := colsCard (seedMatrix (depthB n))
  one_le_Awrap := by
    intro _
    have hgt := (coefficientPass_awrap ParameterSchedule.cSeed C0 B0).2.2.1
    have := ParameterSchedule.hundredOne_le_of_cSeed_lt hgt
    omega
  one_le_LP := by
    intro _
    have := ParameterSchedule.four_le_LPwidth_sched Ccert s lq2 clU0 zR
    omega
  one_le_mN := hmN
  one_le_nN := hnN
  one_le_mBase := by
    rw [(seedMatrix_carriers (depthB n)).1]
    exact Nat.one_le_two_pow
  one_le_nBase := by
    rw [(seedMatrix_carriers (depthB n)).2]
    have := (aSeed_spec (depthB n)).2
    omega

/-- **The specification fires at the paper's own level-zero data.**

Seven conclusions about one inhabitant, at legal parameter values:

1. it satisfies `SeedAnchored` at the frozen application site -- so the
   level-zero pin is the **paper's**, not a synthetic choice;
2. its base row carrier is the evaluated `2^{q_seed(B(n))}`;
3. its base column carrier is the evaluated `q_seed(B(n))`;
4. its inner width is legal at every level (`q_i >= 2`);
5. its outer width is legal at every level (`Q_i >= 16`), unconditionally;
6. both successor carriers exceed one, so the realized-input invariant is not
   degenerate;
7. the successor row carrier is at least `2^{16}`, i.e. the family is far from
   the trivial fixed point `1`.

The free inputs that remain universally quantified are exactly the ones the
frozen schedule layer itself leaves symbolic -- the recorded coefficient table,
the schedule threshold inputs, `s`, `delta_v(G)`, `zeta` -- together with the
two pre-wrapper count sequences of the unbuilt Stage-4 chain.  That is strictly
stronger than exhibiting one choice of them.  **No quantity the frozen source
DEFINES is left free here:** `A_wrap`, `L_P`, `q`, `Q`, `B(n)`, `m_0`, `n_0`
and `delta_U = eta_R/(16 q)` (`eq:q-deltaU`, `06:517`) are each obtained by
evaluating their defining chain.

**Range.**  `n` is the source size and carries `1 <= n`, which is the range in
which the banked `IterationAssembly.depthB_ge` -- and hence aux 13
`seedAnchor_inside_frozen_range`, and hence the frozen `b >= 1` of `12:16` --
actually holds, so the exhibited instance sits *inside* the paper's range rather
than merely containing it.

**Fidelity:** conclusions 1--3 are the paper's own instance (`12:360--368`) and
the schedule fields carry the paper's own evaluated values; conclusions 4--7
hold at *every* legal value of the unbuilt Stage-4 counts, and the canonical
instance of those two counts stays deferred (GAP-EXPOSED 2).  Conclusion 5 is
the unconditional `Q_i >= 16` of aux 6, which is a *floor*: at the instance's
own evaluated `delta_U` the schedule's `Q_0 = max{8 b_out/(delta delta_U),
8/delta, 16}` is far larger, and nothing here claims otherwise. -/
theorem fixedLevelCarriers_fires (n C0 B0 Ccert s lq2 clU0 zR : ℕ) (hn : 1 ≤ n)
    (dv zeta : ℝ)
    (mN nN : ℕ → ℕ) (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i) (i : ℕ) :
    SeedAnchored (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN) n ∧
      (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).rowCarrier 0
        = 2 ^ qSeed (depthB n) ∧
      (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).colCarrier 0
        = qSeed (depthB n) ∧
      2 ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).q i ∧
      16 ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).Q i ∧
      2 ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).rowCarrier (i + 1) ∧
      2 ^ 16 ≤
        (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).rowCarrier (i + 1) := by
  set S := paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN with hS
  -- The anchor's requested depth is inside the frozen `b >= 1` range (aux 13).
  have _hrange : 1 ≤ depthB n ∧ 512 ≤ depthB n := seedAnchor_inside_frozen_range n hn
  have hanch : SeedAnchored S n := ⟨rfl, rfl, rfl⟩
  obtain ⟨hrow0, hcol0, -⟩ := seedAnchored_carriers hanch
  have hq := two_le_q S i
  have hQ := sixteen_le_Q S i
  have hsucc := (carriers_two_le_succ S i).1
  have hbig : 2 ^ 16 ≤ S.rowCarrier (i + 1) := by
    have hbase : 2 ≤ S.q i * S.mN i :=
      le_trans hq (Nat.le_mul_of_pos_right _ (S.one_le_mN i))
    have hstep : (2 : ℕ) ^ 16 ≤ (S.q i * S.mN i) ^ S.Q i :=
      le_trans (Nat.pow_le_pow_left hbase 16)
        (Nat.pow_le_pow_right (by omega) hQ)
    exact hstep
  exact ⟨hanch, hrow0, hcol0, hq, hQ, hsucc, hbig⟩

/-- **Aux 15 (the two halves of `eq:q-deltaU` are read at the *same* width).**

`06-parameter-schedule.tex:513--519` is one display with two equations,
`q = 2^{A_wrap L_P^2}` (line 515) and `delta_U = eta_R/(16 q)` (line 517), and
the `q` of the second is the `q` of the first.  This lemma is that identity for
the canonical instance: its `delta_U` field is the banked
`ParameterSchedule.deltaU` at **its own inner width** `q_i` -- the level's
`LevelCarrierSpec.q`, not the outer bridge width `Q_i` of
`eq:Q-theta-choice` and not a third quantity.

It holds by `rfl`, which is exactly the point: the field was *evaluated*
through the defining chain rather than assigned, so the identity is
definitional.  A version of this module in which `delta_U` were a free binder
could not state it.  General in every free input and every level. -/
theorem paperSeedSpec_deltaU_at_own_inner_width
    (n C0 B0 Ccert s lq2 clU0 zR : ℕ) (dv zeta : ℝ) (mN nN : ℕ → ℕ)
    (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i) (i : ℕ) :
    (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i
      = ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta)
          ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).q i) :=
  rfl

/-- **Aux 16 (the evaluated tolerance is positive and inside the frozen finite
gate).**

At the frozen side conditions of `eq:eta-choice` (`06:212--217`) -- `3 < s`,
`0 < delta_v(G)`, `0 < zeta`, which are the schedule layer's own hypotheses and
not new demands -- the instance's evaluated `delta_{U,i}` satisfies

```
0 < delta_{U,i} <= 1/200   and   delta_{U,i} <= 1/60,
```

the finite gate `06:547` being *discharged* by the schedule's own `eta_R`
rather than imposed.  This is the substance of the DEFINED-VS-FREE repair: a
free `dU` binder is certified at values such as `delta_U <= 0`, where the
frozen `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}` has no meaning; the
evaluated field can never take them.  General in every free input and every
level. -/
theorem paperSeedSpec_deltaU_pos_and_gated
    (n C0 B0 Ccert : ℕ) {s : ℕ} (lq2 clU0 zR : ℕ) {dv zeta : ℝ}
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (mN nN : ℕ → ℕ)
    (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i) (i : ℕ) :
    0 < (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i ∧
      (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i ≤ 1 / 200 ∧
      (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i ≤ 1 / 60 := by
  set S := paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN with hS
  have hqpos : 0 < S.q i := by
    have := two_le_q S i
    omega
  have hval : S.dU i = ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta) (S.q i) :=
    rfl
  have hgates := ParameterSchedule.deltaU_le_gates (s := s) (dv := dv) (zeta := zeta) hqpos
  have hpos : 0 < ParameterSchedule.deltaU (ParameterSchedule.etaR s dv zeta) (S.q i) :=
    ParameterSchedule.deltaU_pos (ParameterSchedule.etaR_pos hs hdv hz) hqpos
  refine ⟨?_, ?_, ?_⟩
  · rw [hval]; exact hpos
  · rw [hval]; exact hgates.1
  · rw [hval]; exact hgates.2

/-- **Aux 17 (the instance's own entry gates fire).**

The banked `ParameterSchedule.schedule_fires_directEntryGates` returns
`EntryGates.directEntryGates` at the schedule's own `delta_U` and `theta`, at
the route's fixed `y = 3/5`.  Applied here it says that the canonical
instance's *own* level data -- outgoing depth `b_{i+1} = B(n)`, evaluated
tolerance `delta_{U,i}`, and the threshold `theta(Q_i)` at the instance's own
outer width -- clears both halves of `eq:direct-entry-gates`.

The carrier equations of this module consume no gate (GAP-EXPOSED 5), so this
is not needed for any conclusion above; it is recorded because it is a
consequence the parked, free-binder form of `paperSeedSpec` could not have: at
an arbitrary `dU` the gates simply fail.  It is therefore the sharpest
available check that the repaired instance sits at the paper's own schedule
point rather than at an audit point the paper never visits.  General in every
free input and every level. -/
theorem paperSeedSpec_entry_gates_fire
    (n C0 B0 Ccert : ℕ) {s : ℕ} (lq2 clU0 zR : ℕ) {dv zeta : ℝ}
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (mN nN : ℕ → ℕ)
    (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i) (i : ℕ) :
    directEntryGates
      ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).bout i)
      ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i)
      (ParameterSchedule.theta
        ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).Q i))
      (3 / 5) := by
  set S := paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN with hS
  have hqpos : 0 < S.q i := by
    have := two_le_q S i
    omega
  exact ParameterSchedule.schedule_fires_directEntryGates
    (bout := S.bout i) (q := S.q i) hs hdv hz hqpos

/-- **The realization hypotheses of `fixedLevelCarriers_realized` are
simultaneously satisfiable at every level.**

Without this the principal theorem could hold vacuously: it is an implication
out of `|Rows(N)| = m_{N,i}` and `|Cols(N)| = n_{N,i}`, and if no matrix met
both the statement would be empty.  A matrix on `[m_{N,i}] x [n_{N,i}]` meets
both by construction, so the conclusion fires at every level of every
specification, with no side condition.

**NON-FIDELITY (registered, GAP-EXPOSED 2).**  The matrix used here is a
*count-realizing stand-in*, not the paper's pre-wrapper `N_i`: producing `N_i`
from `R_i` is the unbuilt Stage-1--4 chain.  What this theorem certifies is the
non-vacuity of the hypothesis pair, and nothing about the construction.  It does
**not** discharge the canonical-inhabitation obligation, which stays open until
`STAGE1-001` .. `WRAP-001` land. -/
theorem fixedLevelCarriers_realized_fires (S : LevelCarrierSpec) (i : ℕ) :
    rowsCard (levelOutput (fun (_ : Fin (S.mN i)) (_ : Fin (S.nN i)) => false)
        (S.qExp i) (S.bout i) (S.dU i)) = S.rowCarrier (i + 1) ∧
      colsCard (levelOutput (fun (_ : Fin (S.mN i)) (_ : Fin (S.nN i)) => false)
        (S.qExp i) (S.bout i) (S.dU i)) = S.colCarrier (i + 1) :=
  fixedLevelCarriers_realized S i _ (by simp [rowsCard]) (by simp [colsCard])

/-- **The level-zero anchor is a genuine constraint.**

A specification whose base carriers are *not* the seed's fails `SeedAnchored`,
so the anchor is content and not notation.  The witness modifies only the base
row carrier of the paper's own instance, keeping every other field and every
guard, and the separation is `1 < 2^{q_seed(B(n))}` -- which holds because
`q_seed(B(n)) >= 64(B(n)+1) >= 1`.  General in every free input. -/
theorem seedAnchor_is_not_automatic (n C0 B0 Ccert s lq2 clU0 zR : ℕ)
    (dv zeta : ℝ) (mN nN : ℕ → ℕ) (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i) :
    ¬ SeedAnchored
        { paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN with
          mBase := 1
          one_le_mBase := le_refl 1 } n := by
  rintro ⟨-, hmB, -⟩
  rw [(seedMatrix_carriers (depthB n)).1] at hmB
  have hq : 64 * (depthB n + 1) ≤ qSeed (depthB n) := (aSeed_spec (depthB n)).2
  have h1 : (2 : ℕ) ^ 1 ≤ 2 ^ qSeed (depthB n) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [] at hmB
  omega

end EthInapproximability.ParameterizedNP.FixedLevelCarriers
