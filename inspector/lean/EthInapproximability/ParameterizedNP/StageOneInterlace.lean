import EthInapproximability.ParameterizedNP.FiniteSlots
import EthInapproximability.ParameterizedNP.PilotStage3
import EthInapproximability.ParameterizedNP.PublicRecords

/-!
# Parameterized NP route: the Stage-1 interlace and its certified scale

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** `sec:one-level`, subsection
  *The four stages*, in the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/07-one-level-construction.tex`,
  **lines 116--215** (the Stage-1 block).  The anchors traced here are
  * lines 118--127, the compiler-fixed `a >= 3`, `q_1 = 2^a - 2`,
    `L_1 = q_1 + s + 1`, "This ambient copy count is even", and the genuinely
    odd subinterlace `p_odd = 2^{a-1} + 1 <= q_1`;
  * lines 128--139, the two displayed inclusions `iota_1 = inc_{q_1,L_1}` and
    `kappa_1(r) = q_1 + r` with partitioned images, and the derived tail
    function `tail_{s+1}(gamma)(r) = gamma(kappa_1(r))`;
  * `eq:stage1-universes-and-value` (label line 147, display lines 141--148),
    the Stage-1 universes `C_1 = Cols(R)^{L_1}`,
    `Rows(M_1) = [q_1] x Rows(R)` and the value equation
    `M_1((i,x),gamma) = R(x, gamma(iota_1(i)))`;
  * lines 149--159, the `NO`-case exact scale `comp(M_1) = D + a` and the
    public certified scale `B_cap := D + a`, together with the frozen sentence
    that in a `YES` instance this "is a target used to choose widths, not a
    claim about the actual complexity of `M_1`";
  * lines 161--173, the three independent scalar hard-seed calls and their
    exact conclusion `eq:stage1-three-scalar-seeds` (label line 172);
  * lines 175--205, the transport of the three scalar estimates to the three
    target rungs, including the block-count trimming and the fixed-coordinate
    projection step;
  * `eq:stage1-robust-certificate` (label line 212, display lines 209--213),
    `Lambda_3(M_1^T, 1, 2^{-b_1}, 3/5) >= B_cap`, with `b_1` the integer fixed
    in `eq:stage1-scales`.

  The Stage-1 *numerals* come from `sections/06-parameter-schedule.tex`:
  `eq:stage1-scales` (label line 319), `eq:stage1-three-seeds` (label line
  346), `eq:stage1-hard-seed-threshold` (label line 351),
  `eq:stage1-three-seed-gates` (label line 367),
  `eq:stage1-projection-ceilings` (label line 382), and the uniform
  satisfiability calculation of lines 394--417, whose displayed identity
  `(T-2)(3/5 - 1/256) - (9/16)T = (43T - 1526)/1280 > 0` is transcribed
  verbatim as `blockCount_pre_ceiling`.

  Two further frozen numerals are consumed by `HardSeedRung` and must be read
  from their own anchors, not from the Stage-1 block:
  * the **input-depth request** `b_0 >= a + 2 + log_2 s + C_in` with
    `C_in >= 0`, `eq:input-depth-request` (label line 449, display lines
    446--450, inside the reading warning "The input-depth request"),
    together with the accessor clauses "`A_*, s, q_2, q, Q, t_1, b_1, ...` are
    positive powers of two" and `64 | s` of
    `05-public-records.tex:416--420`, from which the frozen text derives
    `64 | s, hence s >= 64` (`06-parameter-schedule.tex:975`) and then
    `alpha_{1,j} <= 2^{-j}/(4s) <= 2^{-j}/256` (`06:394--398`);
  * the **`b_1` window** `b_1 = 2^{j_49(a-2)} <= 2^{(49/100) sqrt(a-2)}`, from
    `eq:stage1-scales` (label line 319) together with `eq:j49-window`
    (label line 84), which is the frozen justification of `h_{1,j} <= x_1`
    printed at `06:411--417`.

  The frozen guard on the Stage-3 bin width used in this module is the
  `s >= 4` of `04-guarded-source.tex:281` (`def:unslabbed-guarded-copy`).
  That anchor states **only** `s >= 4`; it does not say `s` is a power of two.
  The power-of-two and divisibility facts are therefore cited from
  `05-public-records.tex:416--420` alone, and every concrete slot binding
  declared in this module takes `s = 64`, the least value satisfying all
  three.

  The inherited endpoints named by the frozen text are
  `sections/D-inherited-contracts.tex`: `eq:contract-hard-seed` (label line
  486) with its `j = 5`, `delta = 1/10` convention (lines 495--519),
  `eq:contract-odd-rungs` (label line 367), `eq:contract-block-balancing`
  (label line 572), `eq:contract-comp-transpose` (label line 284), and the
  required reboot facade `eq:contract-stage1-input` /
  `eq:contract-stage1-output` (labels lines 864 and 872), of which the frozen
  appendix says outright: "No generic inherited declaration currently has
  [it] as its type".

* **Reader counterparts** (`routes/parameterized-np/reader-facing/sections/`
  `03-parameterized-construction.tex`, §"Stage 1: an arbitrary robust seed"),
  one reader item per declaration, none of them claimed by any earlier ledger
  row (the only previously claimed loci in this reader file are lines 53--58,
  59, 100--101, 105--107, 142, `eq:paper-W-definition` and
  `eq:paper-W-carriers`, held by `RECORD-LAYER-001` and `SIZE-001`, and none
  of them is touched here; line 142 is `q_1 := 2^a - 2` and stays with
  `SIZE-001`):
  * `eq:paper-M1-definition` (label line 156, display lines 148--157)
    -> `stageOne`, with `stageOne_apply` as its value equation;
  * `eq:paper-M1-exact` (label line 174, display lines 172--175)
    -> `stageOne_scale_eq_bCap`;
  * `eq:paper-stage1-three-calls` (label line 194, display lines 187--195)
    -> the six seed scalars `mSeed`, `wSeed`, `pSeed`, `alphaSeed`,
    `betaSeed`, `hSeed`;
  * `eq:paper-stage1-three-seeds` (label line 201, display lines 197--202)
    -> `HardSeedRung` and `hardSeedRung_conclusion`;
  * `eq:paper-stage1-extraction-gates` (label line 217, display lines
    204--218) -> `blockCount_pre_ceiling` (the `ceil(q_1 (beta-alpha)/
    (1-alpha)) >= p_j` half of display line 1, lines 206--210) and
    `projectionCeiling_strict` (display line 2, lines 211--215);
  * `eq:paper-M1-robust` (label line 247, display lines 245--248)
    -> `stage1RobustCertificate`.

  **Reader items deliberately declined, with the reason recorded.**
  * `pOdd` and its four facts claim **no** reader item.  The reader states the
    odd subinterlace only in prose ("For the reverse inequality retain any
    `2^{a-1}+1` outer blocks", lines 166--167), and prose is never cited as a
    statement; the nearest reader *display* is `eq:paper-odd-copy` (label
    `02-preliminaries.tex:150`), which is the inherited odd-copy contract
    itself and belongs to `INHERIT-001`.
  * `columnDensityCeiling_*` and the `Nat.clog` selector-width lemmas have no
    reader display: the reader records the projection ceilings only inside
    `eq:paper-stage1-extraction-gates`, already assigned above, and never
    prints a selector width for Stage 1.
  * The tail function `tail_{s+1}`, `iota_1` and `kappa_1` are **banked**
    (`SLOTS-001`, `FiniteSlots.lean`) and are consumed by pin here; their
    reader item is already held by that row and is not reclaimed.
  * The five `HardSeedRung.gate_*` theorems, `gates_hold`, `gates_are_numeric`
    and the derived facts `j_le_a`, `sixtyFour_le_s`, `six_le_log_s`,
    `eight_add_a_le_b₀`, `mSeed_le_b₀`, `binding`, `alpha_le_bound` claim
    **no** reader item.  The reader prints only the two clauses of
    `eq:paper-stage1-extraction-gates` (the strict density comparison
    `0 < alpha_j < beta_j` and the ceiling gate), whose display is already
    assigned above; the remaining clauses of the *autoformalization*
    `eq:stage1-three-seed-gates` (`m_HS <= m_{1,j} <= b_0`,
    `1 <= p_{1,j} <= q_1 < L_1`, `0 < h_{1,j} <= x_1 <= 1`) have no reader
    display at all -- the reader states only "The schedule chooses the depths
    so that each call is in range" (line 203), which is prose and is never
    cited as a statement.  Nothing here reassigns an already-claimed item.
  * `stage1Legal`, `HardSeedRung.raiseDepth`, `HardSeedRung.atRung`, the
    non-vacuity witnesses and the statement/consistency poles are
    verification apparatus with no counterpart in either document, and claim
    no reader item.
  * `eq:input-depth-request` and the `b_1` window have no reader display
    either: the reader introduces `x_1 := 2^{-b_1}` in an unlabelled display
    (lines 180--184) with no depth inequality attached, and states a depth
    request only in **unlabelled inline prose**, in two places -- the
    hypothesis list "Suppose `b_0 >= a + 2 + log_2 s`" (line 70), which drops
    `C_in`, and "the parameter choice includes `a+1 <= b_0`" (line 169), which
    is strictly weaker (`eight_add_a_le_b₀` implies it).  Neither is a
    labelled display, so neither is citable as a statement, and both are
    therefore cited to the autoformalization source only.  The demoted clause
    `m_{1,j} <= b_0` likewise has no reader display: the reader's
    `eq:paper-stage1-extraction-gates` (label line 217) prints only
    `0 < alpha_j < beta_j`, the ceiling gate and the projection strictness,
    and the depth-range condition appears only in the prose of line 203.

## Dependencies, imports, adapters

* `EthInapproximability.ParameterizedNP.FiniteSlots` (banked `SLOTS-001`,
  consumed by pin) for `Slot`, `inc`, `slotHead`, `slotTail`, `slotAppend`,
  `Stage1SlotBinding` and its derived `q_1`, `L_1`, `iota_1`, `kappa_1`,
  `stage1Tail`, `stage1Minimal`;
  `EthInapproximability.ParameterizedNP.PilotStage3` (banked, consumed by pin)
  for `interlace_selector_upper`, the kernel-checked
  `lem:interlace-selector-protocol`; and
  `EthInapproximability.ParameterizedNP.PublicRecords` (banked
  `RECORD-LAYER-001`, consumed by pin) for `D_const`.
  Nothing from any of the three is restated.
* Through them, `EthInapproximability.Prelude`, hence `LegacyNPCC.Core`
  (project-axiom-free) and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is
  **not** imported anywhere in this chain, so the cited AGHP balanced-family
  axiom is **not** in the closure of any declaration here.
* Vendored declarations *consumed, never re-proved*: `NPCC.comp_transpose`
  (`eq:contract-comp-transpose`) and `NPCC.D_mapNodes_le`
  (`vendor/npc-cc/NPCC/Twin.lean:132`, the protocol-pullback vehicle for
  `lem:duplication-invariance`), together with the definitional layer
  `NPCC.Dfamily`, `NPCC.bracketGE`, `NPCC.subgame`, `NPCC.LambdaGE` and
  `Workspace.Types.Interlace.interlaceFun`,
  `Workspace.Types.CommComplexity.D`.
* **External theorem adapters: none is taken as an axiom.**  Of the three
  inherited theorems the frozen Stage-1 argument calls, one is now *consumed
  by pin* -- the interlace selector protocol
  `lem:interlace-selector-protocol`, banked as
  `PilotStage3.interlace_selector_upper`, which makes the upper half
  `comp(M_1) <= comp(R) + a` a **proved theorem**
  (`stageOne_selector_upper`) rather than a hypothesis.  The remaining two --
  the General Hard Seed corollary `eq:contract-hard-seed` and the odd-copy
  bound `eq:contract-odd-rungs` -- enter as **explicit named binders** on the
  theorems that use them (`hardSeedRung_conclusion`, `stageOne_scale_eq_bCap`,
  `stage1RobustCertificate`), never as silent axioms and never as bundle
  fields, because the full Stage-1 certificate `eq:contract-stage1-output` is
  an open reboot facade obligation
  (`D-inherited-contracts.tex:874--885`).
* Proof status of every declaration below: **new** (first transcription of the
  frozen Stage-1 block), except `D_stageOneT`, `D_stageOne_le_interlace` and
  `D_interlace_le_stageOne`, which are one-line consumptions of the checked
  inherited `NPCC.comp_transpose` and `NPCC.D_mapNodes_le`.

## Coverage limits, binding on every consumer

1. `stageOne_scale_eq_bCap` does **not** prove `comp(M_1) = D + a`.  Its
   **upper** half is proved outright (`stageOne_selector_upper`, from the
   banked selector protocol plus duplication invariance plus `clog_q₁`); its
   **lower** half -- the odd-copy call at `p_odd` -- is a named hypothesis, and
   `scale_upper_half_alone_holds` shows the gap is one-directional.  The reboot
   facade `EthInapproximability.reboot_stage1_certificate` of
   `D-inherited-contracts.tex:874` remains **open**.
2. `stage1RobustCertificate` does **not** prove the three transported rung
   bounds.  It proves that the three of them, at the frozen offsets, are
   *exactly* `eq:stage1-robust-certificate`, and `stage1RobustCertificate_tight`
   shows no bit is lost or gained in the assembly.  The three transports
   themselves (block balancing, fixed-coordinate projection, transpose
   invariance, restriction monotonicity) are named binders.
3. No `Robust(M_1^T, 1/10, b_1)` predicate is stated here.  The frozen
   `eq:contract-stage1-output` asks for it; deriving it from
   `eq:stage1-robust-certificate` is Stage-2 input and is not claimed.
4. `a`, `s`, `b_0`, `b_1` are carried as explicit parameters.  The straight-line
   program of `sec:parameters` that computes them is not transcribed, so **no
   parameter schedule may be read out of this module**.

## Mechanical-contract compliance (`M1`--`M10`, frozen Section 2)

* `M1`/`M2`/`M4`: **no complexity, robustness, promise or lower-bound field
  appears in any structure here.**  The one new structure, `HardSeedRung`,
  carries only *numeric* data (`a`, `j`, `s`, `b_0`, `b_1`, `C_in`, `m_HS`)
  and the frozen numeric side conditions that are **not** derivable from the
  others -- seven of them: the hard-seed threshold pair `5 <= m_HS <= a - 2`,
  the rung range `j <= 2`, the two frozen `s` clauses `0 < s` and `64 | s`,
  the input-depth request, and the `b_1` window.  Every remaining clause of
  `eq:stage1-three-seed-gates` is a **theorem** on the structure, never a
  field (`M3` forbids restating a derived telescope).  That includes **both**
  halves of clause 1: `m_{1,j} <= b_0` is the derived telescope
  `s_pos` + `64 | s` + `input_depth` `=>` `a + 8 <= b_0` `=>`
  `m_{1,j} = a - j <= a <= b_0`, and is carried as the theorem
  `HardSeedRung.mSeed_le_b₀`, not as constructor data.  So
  `gate_exponent`, `gate_copy_count`, `gate_row_column_density`,
  `gate_column_density` and `gate_block_count` together are the frozen clause
  set, and `gates_are_numeric` checks in the kernel that the seven-clause
  field bundle alone never produces a complexity claim.  The inherited theorem's
  conclusion is supplied to `hardSeedRung_conclusion` as an explicit
  `hardSeed` binder and is read off only by that *theorem*, never by a
  projection of constructor data.
* `M3`: `q_1`, `L_1`, `iota_1`, `kappa_1` are banked derived accessors and are
  re-exported, never restated; `wSeed`, `pSeed`, `alphaSeed`, `betaSeed`,
  `hSeed`, `bCap` are derived definitions, not fields.
* `M5`/`M8`: this module is upstream of the interlace layer of the bridge; the
  widths `q` and `Q` do **not** appear here at all, and the only width in play
  is the Stage-1 copy count `q_1` with its odd subinterlace `p_odd`.  They are
  kept distinct: `pOdd_lt_q₁` is proved, so no consumer may confuse them.
* `M7`: nonemptiness is preserved -- `stageOne_rows_nonempty`,
  `stageOne_cols_nonempty`, and the two ceiling floors
  `one_le_rowCeiling`, `one_le_colCeiling` of
  `eq:stage1-projection-ceilings` line 1.
* `M9`: the two promise branches are never merged.  `bCap` mentions no matrix;
  `stageOne_scale_eq_bCap` is the `NO`-case statement and carries the `NO`
  reading as a named hypothesis, and `bCap_is_not_a_complexity_claim` exhibits
  a legal binding and a legal matrix where `comp(M_1) < B_cap`, which is
  exactly the frozen `YES`-side caveat of line 158.
* `M10`: every count is a `Fintype.card` or a `Nat.ceil` of a real density;
  no two distinct slots are identified.

## Candidate encodings of `eq:stage1-universes-and-value`

Two encodings of `M_1` were built and raced.

* **Candidate A (landed).**  `stageOne` is typed at the frozen carriers
  directly: rows `Slot q_1 x X`, columns `Slot L_1 -> Y`, value
  `R p.2 (gamma (iota_1 p.1))`.  Both frozen universes are the *types* of the
  declaration, so `eq:stage1-universes-and-value` holds by `rfl`
  (`stageOne_apply`, `stageOne_rows_card`, `stageOne_cols_card`).
* **Candidate B (rejected).**  `M_1` as a restriction of the *full* `L_1`-fold
  classical interlace `interlaceFun R L_1`, with the frozen row carrier
  recovered as the `iota_1`-image block.

Both are mathematically the same matrix -- `stageOne_eq_fullInterlace_restrict`
proves the identity by `rfl`, so nothing is lost by recording it.  Candidate B
is rejected on the discriminating battery item: under B the *typed* copy count
is `L_1`, so the selector width that the type offers is `ceil(log_2 L_1)`, and
`candidateB_selector_width_is_wrong` proves in the kernel that at the schedule-
legal binding `a = 7, s = 64` (`q_1 = 126`, `L_1 = 191`) this equals `8`,
whereas the frozen certified scale of line 152 needs exactly `a = 7` selector
bits there.  Candidate B therefore reads the certified scale off by one bit
unless a restriction step is inserted by hand, while under A `clog_q₁` gives
`ceil(log_2 q_1) = a` at every legal binding.
Ranking (aux lemmas proved, faithfulness, length): A wins the first two and is
no longer.

## Concrete slot bindings declared here

`stage1Legal` (`a = 7`, `s = 64`) is the **only** concrete `Stage1SlotBinding`
this module introduces, and `seedBinding` and `candidateBBinding` are named
aliases of it.  Every *literal Stage-1 gate transcribed here* holds at it
simultaneously: `a >= 3` (`07:118`), `a >= 7` (`06:404`, the consequence of
`eq:stage1-hard-seed-threshold`), `s >= 4` (`04:281`), `s` a positive power of
two and `64 | s` (`05:416--420`), hence `s >= 64` (`06:975`).  It is **not**
the pair the compiler computes -- `eq:stage1-C0-gate` (`06:309`) forces a far
larger `a` through `a = C_0 (log_2 A_*)^2` -- and coverage limit 4 below
forbids reading any parameter schedule out of this module.

The banked `FiniteSlots.stage1Minimal` (`a = 3`, `s = 1`) is the *structure*-
minimal inhabitant of `Stage1SlotBinding` and is kept there for the slot-layer
facts, but it sits below the frozen `s >= 4` and `a >= 7`, so **no statement
pole or non-vacuity witness in this module is taken at it**.
-/

namespace EthInapproximability.ParameterizedNP.StageOneInterlace

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.FiniteSlots

variable {X Y : Type*}

/-! ## §0  The gate-legal concrete slot binding

Every concrete witness, statement pole and non-vacuity claim below is taken at
one binding, declared once here so that its legality can be audited in one
place. -/

/-- **The gate-legal Stage-1 slot binding**: `a = 7`, `s = 64`, hence
`q_1 = 2^7 - 2 = 126` and `L_1 = 126 + 64 + 1 = 191`.

Legality, clause by clause, against the frozen release source:

* `a >= 3` -- the compiler-fixed guard of `07-one-level-construction.tex:118`
  (the `three_le_a` field of the banked `Stage1SlotBinding`);
* `a >= 7` -- `06-parameter-schedule.tex:404`, the frozen consequence of
  `eq:stage1-hard-seed-threshold` that the satisfiability calculation of
  `06:394--410` actually uses, and the smallest exponent at which a Stage-1
  hard-seed call passes the literal Stage-1 gate group;
* `s >= 4` -- `04-guarded-source.tex:281` (`def:unslabbed-guarded-copy`);
* `s` a positive power of two, and `64 | s` -- the accessor clauses of
  `05-public-records.tex:416--420`, whence `s >= 64`
  (`06-parameter-schedule.tex:975`).

`s = 64` is the least value meeting the last three and `a = 7` the least
meeting the first two, so this is the smallest binding passing every gate
**this module transcribes**.

*Honest scope, and a recorded coverage limit.*  `(a, s) = (7, 64)` is **not**
the pair the full parameter schedule computes.  `eq:stage1-scales` (`06:317`)
sets `a = C_0 (log_2 A_*)^2` and `eq:stage1-C0-gate` (`06:309`) demands
`2401(C_0 - 2) > 360000`, so the compiler's own `a` is very much larger than
`7`.  That straight-line program is deliberately not transcribed here
(coverage limit 4 above), and `a = 7` is used only as the smallest value at
which the literal Stage-1 gate comparisons can be exhibited non-vacuously.
**No parameter schedule may be read out of `stage1Legal`.** -/
def stage1Legal : Stage1SlotBinding where
  a := 7
  s := 64
  three_le_a := by norm_num
  s_pos := by norm_num

@[simp] theorem stage1Legal_q₁ : stage1Legal.q₁ = 126 := rfl

@[simp] theorem stage1Legal_L₁ : stage1Legal.L₁ = 191 := rfl

/-- The binding is nondegenerate at the slot layer: both blocks of the `[L_1]`
partition are nonempty and the Stage-1 block is a proper subset.  The statement
also records the two frozen bin-width clauses the binding satisfies -- `4 <= s`
(`04-guarded-source.tex:281`) and `64 | s` (`05-public-records.tex:420`) -- so
that the legality being asserted here is the full one, not just the partition
half. -/
theorem stage1Legal_nondegenerate :
    0 < stage1Legal.q₁ ∧ stage1Legal.q₁ < stage1Legal.L₁ ∧ 4 ≤ stage1Legal.s ∧
      64 ∣ stage1Legal.s :=
  ⟨stage1Legal.q₁_pos, stage1Legal.q₁_lt_L₁, by norm_num [stage1Legal],
    by norm_num [stage1Legal]⟩

/-! ## §1  The Stage-1 universes and value equation

`eq:stage1-universes-and-value` (`07-one-level-construction.tex:141--148`):
```
C_1            = Cols(R)^{L_1}
Rows(M_1)      = [q_1] x Rows(R)
M_1((i,x),γ)   = R(x, γ(iota_1(i)))
```
The slot binding `F` -- hence `q_1 = 2^a - 2`, `L_1 = q_1 + s + 1`, `iota_1`
and `kappa_1` -- is the banked `FiniteSlots.Stage1SlotBinding` and is consumed
by pin. -/

/-- The Stage-1 column universe `C_1 = Cols(R)^{L_1}` of
`eq:stage1-universes-and-value`. -/
abbrev Stage1Cols (F : Stage1SlotBinding) (Y : Type*) : Type _ := Slot F.L₁ → Y

/-- The Stage-1 row universe `Rows(M_1) = [q_1] x Rows(R)` of
`eq:stage1-universes-and-value`. -/
abbrev Stage1Rows (F : Stage1SlotBinding) (X : Type*) : Type _ := Slot F.q₁ × X

/-- **The Stage-1 interlace `M_1`** of `eq:stage1-universes-and-value`
(`07-one-level-construction.tex:145`), reader `eq:paper-M1-definition`
(`03-parameterized-construction.tex:153`):
`M_1((i,x), gamma) = R(x, gamma(iota_1(i)))`.

`M_1` is the classical interlace of `R` on its **first `q_1`** ambient
coordinates; the remaining `s + 1` coordinates of `[L_1]` are reserved for
Stage 4 and are not read (`stageOne_tail_invariant`). -/
def stageOne (F : Stage1SlotBinding) (R : X → Y → Bool) :
    Stage1Rows F X → Stage1Cols F Y → Bool :=
  fun p γ => R p.2 (γ (F.iota₁ p.1))

/-- The transposed Stage-1 matrix `M_1^T`, the object whose three-rung
robustness certificate `eq:stage1-robust-certificate` is the Stage-2 input. -/
def stageOneT (F : Stage1SlotBinding) (R : X → Y → Bool) :
    Stage1Cols F Y → Stage1Rows F X → Bool :=
  fun γ p => stageOne F R p γ

/-- The frozen value equation, definitionally. -/
@[simp] theorem stageOne_apply (F : Stage1SlotBinding) (R : X → Y → Bool)
    (i : Slot F.q₁) (x : X) (γ : Stage1Cols F Y) :
    stageOne F R (i, x) γ = R x (γ (F.iota₁ i)) := rfl

@[simp] theorem stageOneT_apply (F : Stage1SlotBinding) (R : X → Y → Bool)
    (γ : Stage1Cols F Y) (p : Stage1Rows F X) :
    stageOneT F R γ p = stageOne F R p γ := rfl

/-! ## §2  Aux-lemma battery A1: `M_1` reads only the Stage-1 template block

`07-one-level-construction.tex:123--126`: "Stage 1 itself is the classical
interlace of `R` on its first `q_1` coordinates, with `s+1` further seed
coordinates reserved for Stage 4."  Reader lines 158--159: "Although `C_1`
contains the reserved coordinates, `M_1` reads only the first `q_1`."
Every lemma in this battery is general in `F`, `R`, `X`, `Y`. -/

/-- **Aux 1 (head-only reading).**  `M_1` is the classical `q_1`-fold interlace
of `R` precomposed with the banked head restriction along `iota_1`. -/
theorem stageOne_eq_interlace_head (F : Stage1SlotBinding) (R : X → Y → Bool)
    (p : Stage1Rows F X) (γ : Stage1Cols F Y) :
    stageOne F R p γ = interlaceFun R F.q₁ p (slotHead F.split γ) := rfl

/-- **Aux 2 (tail invariance).**  Two ambient column vectors that agree on the
Stage-1 template block give the same `M_1` column: the `s+1` reserved
coordinates are not read. -/
theorem stageOne_congr_head (F : Stage1SlotBinding) (R : X → Y → Bool)
    {γ γ' : Stage1Cols F Y} (h : ∀ i : Slot F.q₁, γ (F.iota₁ i) = γ' (F.iota₁ i)) :
    (fun p => stageOne F R p γ) = fun p => stageOne F R p γ' := by
  funext p
  simp only [stageOne, h p.1]

/-- **Aux 3 (tail invariance, explicit form).**  Overwriting the whole reserved
tail `kappa_1([s+1])` by an arbitrary pattern leaves the `M_1` column
unchanged.  This is the kernel form of the frozen sentence that the reserved
coordinates "do not alter its complexity". -/
theorem stageOne_tail_invariant (F : Stage1SlotBinding) (R : X → Y → Bool)
    (γ : Stage1Cols F Y) (t : Slot (F.s + 1) → Y) :
    (fun p => stageOne F R p (slotAppend F.split (slotHead F.split γ) t)) =
      fun p => stageOne F R p γ := by
  refine stageOne_congr_head F R ?_
  intro i
  exact congrFun (slotHead_slotAppend F.split (slotHead F.split γ) t) i

/-- **Aux 4 (the tail really is free).**  As soon as the column alphabet has two
distinct letters, the assignment `gamma |-> M_1(-, gamma)` is **not** injective:
the reserved Stage-4 coordinates carry information `M_1` discards.  Without this
the "reserved coordinates" of `eq:stage1-universes-and-value` would be a naming
convention rather than content. -/
theorem stageOne_column_map_not_injective (F : Stage1SlotBinding)
    (R : X → Y → Bool) {y₀ y₁ : Y} (hy : y₀ ≠ y₁) :
    ¬ Function.Injective
        (fun (γ : Stage1Cols F Y) => fun p => stageOne F R p γ) := by
  intro hinj
  set γ₀ : Stage1Cols F Y := fun _ => y₀ with hγ₀
  set γ₁ : Stage1Cols F Y :=
    slotAppend F.split (slotHead F.split γ₀) (fun _ => y₁) with hγ₁
  have hEq : (fun p => stageOne F R p γ₁) = fun p => stageOne F R p γ₀ :=
    stageOne_tail_invariant F R γ₀ (fun _ => y₁)
  have hγ : γ₁ = γ₀ := hinj hEq
  have hlast : γ₁ (F.kappa₁ F.nuS) = y₁ :=
    congrFun (slotTail_slotAppend F.split (slotHead F.split γ₀) (fun _ => y₁)) F.nuS
  rw [hγ] at hlast
  exact hy (by simpa [hγ₀] using hlast)

/-! ## §3  Aux-lemma battery A2: exact finite carriers (`M7`, `M10`) -/

/-- **Aux 5 (row carrier).**  `|Rows(M_1)| = q_1 * m_R`. -/
theorem stageOne_rows_card (F : Stage1SlotBinding) (X : Type*) [Fintype X] :
    Fintype.card (Stage1Rows F X) = F.q₁ * Fintype.card X := by
  simp [Stage1Rows]

/-- **Aux 6 (column carrier).**  `|C_1| = n_R ^ L_1`, the literal finite power
`Cols(R)^{L_1}` of `eq:stage1-universes-and-value`. -/
theorem stageOne_cols_card (F : Stage1SlotBinding) (Y : Type*) [Fintype Y] :
    Fintype.card (Stage1Cols F Y) = Fintype.card Y ^ F.L₁ := by
  simp [Stage1Cols]

/-- **Aux 7 (nonempty rows).**  The Stage-1 row carrier is nonempty whenever the
source row carrier is: `q_1 >= 6 > 0` is banked. -/
instance stageOne_rows_nonempty (F : Stage1SlotBinding) (X : Type*)
    [Nonempty X] : Nonempty (Stage1Rows F X) :=
  ⟨(⟨0, F.q₁_pos⟩, Classical.arbitrary X)⟩

/-- **Aux 8 (nonempty columns).**  The Stage-1 column carrier is nonempty
whenever the source column carrier is. -/
instance stageOne_cols_nonempty (F : Stage1SlotBinding) (Y : Type*)
    [Nonempty Y] : Nonempty (Stage1Cols F Y) :=
  ⟨fun _ => Classical.arbitrary Y⟩

/-- **Aux 9 (transpose invariance).**  `comp(M_1^T) = comp(M_1)`, by direct
consumption of the checked inherited `NPCC.comp_transpose`
(`eq:contract-comp-transpose`, `D-inherited-contracts.tex:284`).  Nothing is
re-proved. -/
theorem D_stageOneT (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] :
    D (stageOneT F R) = D (stageOne F R) :=
  NPCC.comp_transpose (stageOne F R)

/-! ### Duplication invariance of the reserved coordinates

`lem:duplication-invariance` (`03-preliminaries.tex:175--185`) at the instance
the frozen Stage-1 paragraph needs: the head restriction
`slotHead : Cols(R)^{L_1} -> Cols(R)^{q_1}` is a surjection with the fixed
right inverse `slotAppend`, so padding the interlace's columns with the `s+1`
reserved coordinates changes nothing.  Reader lines 158--159: "Although `C_1`
contains the reserved coordinates, `M_1` reads only the first `q_1`.
Consequently these coordinates do not alter its complexity." -/

/-- **Aux 9a (one half of duplication invariance).**  Padding never raises the
complexity: `M_1` is a column pullback of the classical `q_1`-fold interlace
along `slotHead`. -/
theorem D_stageOne_le_interlace (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] :
    D (stageOne F R) ≤ D (interlaceFun R F.q₁) :=
  NPCC.D_mapNodes_le (interlaceFun R F.q₁) (fun p : Stage1Rows F X => p)
    (fun γ : Stage1Cols F Y => slotHead F.split γ)

/-- **Aux 9b (the other half).**  The fixed right inverse `slotAppend` -- which
sets every reserved coordinate to a default letter -- exhibits the classical
interlace as a column pullback of `M_1`, so padding never lowers the
complexity either.  The `Nonempty Y` guard is the frozen nonempty-carrier
policy (`M7`). -/
theorem D_interlace_le_stageOne (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] [Nonempty Y] :
    D (interlaceFun R F.q₁) ≤ D (stageOne F R) := by
  have hconv : (fun (a : Stage1Rows F X) (b : Slot F.q₁ → Y) =>
      stageOne F R a (slotAppend F.split b (fun _ => Classical.arbitrary Y)))
      = interlaceFun R F.q₁ := by
    funext a b
    exact congrArg (R a.2)
      (congrFun (slotHead_slotAppend F.split b (fun _ => Classical.arbitrary Y)) a.1)
  rw [← hconv]
  exact NPCC.D_mapNodes_le (stageOne F R) (fun p : Stage1Rows F X => p)
    (fun c : Slot F.q₁ → Y =>
      slotAppend F.split c (fun _ => Classical.arbitrary Y))

/-- **`lem:duplication-invariance` at the Stage-1 instance.**  The reserved
Stage-4 coordinates do not alter the complexity of `M_1`. -/
theorem D_stageOne_eq_interlace (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] [Nonempty Y] :
    D (stageOne F R) = D (interlaceFun R F.q₁) :=
  Nat.le_antisymm (D_stageOne_le_interlace F R) (D_interlace_le_stageOne F R)

/-! ## §4  The even ambient count and the odd subinterlace

`07-one-level-construction.tex:119--123`: "This ambient copy count is even.
The NO lower bound does not apply an odd-copy theorem to `q_1`.  It restricts
to the genuinely odd subinterlace `p_odd = 2^{a-1}+1 <= q_1`, applies the
inherited odd-copy theorem there, and then uses restriction monotonicity." -/

/-- The genuinely odd subinterlace `p_odd = 2^{a-1} + 1` of
`07-one-level-construction.tex:122`. -/
def pOdd (F : Stage1SlotBinding) : ℕ := 2 ^ (F.a - 1) + 1

/-- `p_odd` is exactly the copy count `2^{l-1} + 1` of the inherited odd-copy
contract `eq:contract-odd-rungs` (`D-inherited-contracts.tex:364`) taken at
`l = a`.  This is the identity that makes the odd-copy call legal. -/
theorem pOdd_eq_oddCopyCount (F : Stage1SlotBinding) :
    pOdd F = 2 ^ (F.a - 1) + 1 := rfl

/-- The ambient Stage-1 copy count is **even** (`07:119--120`), so the
odd-copy theorem is not applicable to it. -/
theorem q₁_even (F : Stage1SlotBinding) : Even F.q₁ := by
  have hpow : 2 ^ (F.a - 1) * 2 = 2 ^ F.a := by
    rw [← pow_succ]; congr 1; have := F.three_le_a; omega
  have hx : (1:ℕ) ≤ 2 ^ (F.a - 1) := Nat.one_le_two_pow
  have hq : F.q₁ = 2 ^ F.a - 2 := rfl
  exact ⟨2 ^ (F.a - 1) - 1, by omega⟩

/-- **Statement pole for the odd subinterlace.**  `q_1` is not odd, so the frozen
refusal to "apply an odd-copy theorem to `q_1`" is content, not caution. -/
theorem q₁_not_odd (F : Stage1SlotBinding) : ¬ Odd F.q₁ :=
  (Nat.not_odd_iff_even).mpr (q₁_even F)

/-- `p_odd` **is** odd. -/
theorem pOdd_odd (F : Stage1SlotBinding) : Odd (pOdd F) := by
  have h4 : (4:ℕ) ≤ 2 ^ (F.a - 1) := by
    have : (2:ℕ) ^ 2 ≤ 2 ^ (F.a - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by have := F.three_le_a; omega)
    simpa using this
  have heven : Even (2 ^ (F.a - 1)) := by
    refine ⟨2 ^ (F.a - 1 - 1), ?_⟩
    have : 2 ^ (F.a - 1 - 1) * 2 = 2 ^ (F.a - 1) := by
      rw [← pow_succ]; congr 1; have := F.three_le_a; omega
    omega
  obtain ⟨k, hk⟩ := heven
  exact ⟨k, by simp only [pOdd, hk]; omega⟩

/-- `2 <= p_odd`: the odd-copy contract's guard `2 <= l` is met at `l = a`
because `a >= 3`. -/
theorem two_le_pOdd (F : Stage1SlotBinding) : 2 ≤ pOdd F := by
  have : (1:ℕ) ≤ 2 ^ (F.a - 1) := Nat.one_le_two_pow
  simp only [pOdd]; omega

/-- `p_odd <= q_1` (`07:122`): the odd subinterlace sits **inside** the ambient
Stage-1 block, which is what makes restriction monotonicity available. -/
theorem pOdd_le_q₁ (F : Stage1SlotBinding) : pOdd F ≤ F.q₁ := by
  have hpow : 2 ^ (F.a - 1) * 2 = 2 ^ F.a := by
    rw [← pow_succ]; congr 1; have := F.three_le_a; omega
  have h4 : (4:ℕ) ≤ 2 ^ (F.a - 1) := by
    have : (2:ℕ) ^ 2 ≤ 2 ^ (F.a - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by have := F.three_le_a; omega)
    simpa using this
  simp only [pOdd, Stage1SlotBinding.q₁]
  omega

/-- **Width-separation pole (`M5`).**  The subinterlace is *strictly* smaller
than the ambient block, so `p_odd` and `q_1` can never be silently identified. -/
theorem pOdd_lt_q₁ (F : Stage1SlotBinding) : pOdd F < F.q₁ := by
  rcases lt_or_eq_of_le (pOdd_le_q₁ F) with h | h
  · exact h
  · exact absurd (h ▸ pOdd_odd F) (q₁_not_odd F)

/-! ## §5  The selector width and the public certified scale `B_cap`

`07-one-level-construction.tex:149--159`.  The `NO`-case exact scale is
`comp(M_1) = D + a`, and `B_cap := D + a` is the *public certified scale*.
`lem:interlace-selector-protocol` (`03-preliminaries.tex:148`) gives the upper
half at cost `comp(R) + ceil(log_2 p)`; the arithmetic that turns that ceiling
into the frozen `a` is `clog_q₁` below. -/

/-- **Selector width (`M3`, selector costs preserved).**
`ceil(log_2 q_1) = a` at every legal Stage-1 binding.  This is the exact
constant that `lem:interlace-selector-protocol` contributes to `comp(M_1)`:
`q_1 = 2^a - 2` sits strictly above `2^{a-1}` and at most `2^a`. -/
theorem clog_q₁ (F : Stage1SlotBinding) : Nat.clog 2 F.q₁ = F.a := by
  have hpow : 2 ^ (F.a - 1) * 2 = 2 ^ F.a := by
    rw [← pow_succ]; congr 1; have := F.three_le_a; omega
  have h4 : (4:ℕ) ≤ 2 ^ (F.a - 1) := by
    have : (2:ℕ) ^ 2 ≤ 2 ^ (F.a - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by have := F.three_le_a; omega)
    simpa using this
  have hle : F.q₁ ≤ 2 ^ F.a := by
    simp only [Stage1SlotBinding.q₁]; omega
  have hlt : 2 ^ (F.a - 1) < F.q₁ := by
    simp only [Stage1SlotBinding.q₁]; omega
  have hupper : Nat.clog 2 F.q₁ ≤ F.a := (Nat.clog_le_iff_le_pow (by norm_num)).2 hle
  have hlower : F.a - 1 < Nat.clog 2 F.q₁ :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hlt
  have := F.three_le_a
  omega

/-- The **public certified scale** `B_cap := D + a` of
`07-one-level-construction.tex:156`.

It is a function of the two public integers `(D, a)` alone: no matrix, no
promise certificate and no protocol enters its definition.  In a `YES` instance
it is, verbatim, "a target used to choose widths, not a claim about the actual
complexity of `M_1`" (line 158), and `bCap_is_not_a_complexity_claim` makes
that caveat checkable. -/
def bCap (Dsrc a : ℕ) : ℕ := Dsrc + a

@[simp] theorem bCap_eq (Dsrc a : ℕ) : bCap Dsrc a = Dsrc + a := rfl

/-- **The upper half of the certified scale, proved.**
`comp(M_1) <= comp(R) + a`.

Nothing here is a hypothesis: the banked `lem:interlace-selector-protocol`
(`PilotStage3.interlace_selector_upper`, `eq:interlace-selector-upper`) is
consumed by pin at the Stage-1 copy count `q_1`, duplication invariance
(`D_stageOne_le_interlace`) discards the reserved coordinates, and `clog_q₁`
turns the selector's `ceil(log_2 q_1)` into the frozen `a`. -/
theorem stageOne_selector_upper (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] :
    D (stageOne F R) ≤ D R + F.a := by
  have h := interlace_selector_upper R F.q₁ F.q₁_pos
  rw [clog_q₁] at h
  exact le_trans (D_stageOne_le_interlace F R) h

/-- **The `NO`-case certified scale, `eq:paper-M1-exact`.**

The upper half is proved (`stageOne_selector_upper`).  Exactly **two** named
binders remain, and neither is an axiom:

* `hR` -- the `NO` reading `comp(R) = D` of `def:level-certificates`;
* `hlower` -- the inherited odd-copy bound `eq:contract-odd-rungs` at the odd
  subinterlace `p_odd = 2^{a-1}+1`, followed by restriction monotonicity
  (`07-one-level-construction.tex:120--123`).  This is precisely the half that
  `eq:contract-stage1-output` leaves open.

What this theorem contributes beyond the two halves is the exact arithmetic of
line 152: the selector's `ceil(log_2 q_1)` is *equal* to `a`, so the two halves
close with no slack at all. -/
theorem stageOne_scale_eq_bCap (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] (Dsrc : ℕ) (hR : D R = Dsrc)
    (hlower : Dsrc + F.a ≤ D (stageOne F R)) :
    D (stageOne F R) = bCap Dsrc F.a := by
  have hupper := stageOne_selector_upper F R
  rw [hR] at hupper
  exact Nat.le_antisymm hupper hlower

/-- **Statement pole for the `YES` side (`M9`), frozen line 158.**
`B_cap` is *not* a claim about `comp(M_1)`: at the gate-legal binding
`stage1Legal` and the legal constant source matrix, `comp(M_1) = 0` while
`B_cap = 7`.  So the lower-bound hypothesis of `stageOne_scale_eq_bCap` is
genuine content and can fail off the `NO` branch. -/
theorem bCap_is_not_a_complexity_claim :
    D (stageOne stage1Legal (fun (_ : Bool) (_ : Bool) => false)) = 0 ∧
      bCap (D (fun (_ : Bool) (_ : Bool) => false)) stage1Legal.a = 7 := by
  constructor
  · exact PublicRecords.D_const false
  · rw [bCap_eq, PublicRecords.D_const false]
    rfl

/-! ## §6  The three scalar seeds of `eq:stage1-three-seeds`

`06-parameter-schedule.tex:335--347`, for `j in {0,1,2}`:
```
m_{1,j} = a - j,            w_{1,j} = 2^{m_{1,j}},
p_{1,j} = 18 * 2^{m_{1,j}-5} = (9/16) w_{1,j},
alpha_{1,j} = w_{1,j} 2^{-b_0},   beta_{1,j} = (3/5)/2^j,
h_{1,j} = 2^{-2^{(49/100) sqrt(m_{1,j})}},   L_1 = q_1 + s + 1.
```
Reader `eq:paper-stage1-three-calls`
(`03-parameterized-construction.tex:187--195`). -/

/-- `m_{1,j} = a - j`. -/
def mSeed (a j : ℕ) : ℕ := a - j

/-- `w_{1,j} = 2^{m_{1,j}}`. -/
def wSeed (a j : ℕ) : ℕ := 2 ^ mSeed a j

/-- `p_{1,j} = 18 * 2^{m_{1,j}-5}`, the copy count of the hard-seed call. -/
def pSeed (a j : ℕ) : ℕ := 18 * 2 ^ (mSeed a j - 5)

/-- `alpha_{1,j} = w_{1,j} 2^{-b_0}`, the retained **row** density. -/
noncomputable def alphaSeed (a b₀ j : ℕ) : ℝ :=
  (wSeed a j : ℝ) * (2 : ℝ) ^ (-(b₀ : ℝ))

/-- `beta_{1,j} = (3/5)/2^j`, the target **column** density of rung `j`. -/
noncomputable def betaSeed (j : ℕ) : ℝ := (3 / 5) / 2 ^ j

/-- `h_{1,j} = 2^{-2^{(49/100) sqrt(m_{1,j})}}`, the retained **column**
density of the hard-seed call.  The orientation row-density/column-density is
the one `D-inherited-contracts.tex:488--492` forbids reversing. -/
noncomputable def hSeed (a j : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (mSeed a j : ℕ))))

/-- `x_1 = 2^{-b_1}` of `eq:stage1-scales` (`06-parameter-schedule.tex:317`),
the retained row density used at all three target rungs. -/
noncomputable def xSeed (b₁ : ℕ) : ℝ := (2 : ℝ) ^ (-(b₁ : ℝ))

/-! ### Aux-lemma battery A3: frozen identities of the seed scalars -/

/-- **Aux 10 (the frozen closed form).**  `p_{1,j} = (9/16) w_{1,j}` whenever
the hard-seed exponent threshold `5 <= m_{1,j}` of
`eq:stage1-three-seed-gates` holds (`m_HS >= 5`,
`D-inherited-contracts.tex:496`). -/
theorem pSeed_eq_nine_sixteenths (a j : ℕ) (h : 5 ≤ mSeed a j) :
    (pSeed a j : ℝ) = 9 / 16 * (wSeed a j : ℝ) := by
  have hsplit : 2 ^ mSeed a j = 2 ^ (mSeed a j - 5) * 32 := by
    have : (2:ℕ) ^ (mSeed a j - 5) * 2 ^ 5 = 2 ^ (mSeed a j - 5 + 5) := by
      rw [pow_add]
    rw [show mSeed a j = mSeed a j - 5 + 5 by omega, ← this]
    norm_num
  simp only [pSeed, wSeed, hsplit]
  push_cast
  ring

/-- **Aux 11 (the inherited call is at `j = 5`).**  `p_{1,j}` is *literally* the
copy count `(2^{j-1}+2) 2^{m-j}` of `eq:contract-hard-seed`
(`D-inherited-contracts.tex:482`) at the frozen fixed choice `j = 5`
("Every active call fixes `j=5` and `delta=1/10`", line 495). -/
theorem pSeed_eq_hardSeed_copyCount (a j : ℕ) :
    pSeed a j = (2 ^ (5 - 1) + 2) * 2 ^ (mSeed a j - 5) := by
  norm_num [pSeed]

/-- **Aux 12 (rung alignment).**  The three frozen column densities are exactly
the three rungs `y, y/2, y/4` of `def:lambda` at `y = 3/5`.  This is the
identity that makes `eq:stage1-robust-certificate` an instance of `Lambda_3`
rather than a separate definition. -/
theorem betaSeed_zero : betaSeed 0 = 3 / 5 := by norm_num [betaSeed]

theorem betaSeed_one : betaSeed 1 = betaSeed 0 / 2 := by norm_num [betaSeed]

theorem betaSeed_two : betaSeed 2 = betaSeed 0 / 4 := by norm_num [betaSeed]

/-- **Aux 13 (range).**  Every `beta_{1,j}` is a legal density. -/
theorem betaSeed_pos (j : ℕ) : 0 < betaSeed j := by
  unfold betaSeed; positivity

theorem betaSeed_le_one (j : ℕ) : betaSeed j ≤ 1 := by
  unfold betaSeed
  rw [div_le_one (by positivity)]
  have : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  linarith

/-- **Aux 13a (range).**  `alpha_{1,j} = w_{1,j} 2^{-b_0}` is positive: the
first half of clause 3 of `eq:stage1-three-seed-gates`. -/
theorem alphaSeed_pos (a b₀ j : ℕ) : 0 < alphaSeed a b₀ j := by
  have hw : (0:ℝ) < (wSeed a j : ℝ) := by
    have h1 : (1:ℕ) ≤ wSeed a j := Nat.one_le_two_pow
    have : (0:ℕ) < wSeed a j := h1
    exact_mod_cast this
  exact mul_pos hw (Real.rpow_pos_of_pos (by norm_num) _)

/-- `alpha_{1,j}` in closed rpow form: `alpha_{1,j} = 2^{m_{1,j} - b_0}`. -/
theorem alphaSeed_eq_rpow (a b₀ j : ℕ) :
    alphaSeed a b₀ j = (2:ℝ) ^ (((mSeed a j : ℕ) : ℝ) + (-(b₀:ℝ))) := by
  have hw : (wSeed a j : ℝ) = (2:ℝ) ^ ((mSeed a j : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    simp only [wSeed]
    push_cast
    ring
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), ← hw]
  rfl

/-- **Aux 13b (the schedule's own row-density bound).**  The frozen derivation
of `06-parameter-schedule.tex:394--398`: from `eq:input-depth-request` with
`C_in >= 0` and `64 | s` (so `log_2 s >= 6`, i.e. `b_0 >= a + 8`),
`alpha_{1,j} <= 2^{-j}/(4s) <= 2^{-j}/256`. -/
theorem alphaSeed_le_bound {a b₀ j : ℕ} (hja : j ≤ a) (hb : a + 8 ≤ b₀) :
    alphaSeed a b₀ j ≤ (1 / 2 ^ j) / 256 := by
  have h8 : (2:ℝ) ^ ((8:ℕ) : ℝ) = 256 := by
    rw [Real.rpow_natCast]; norm_num
  have hrhs : (1 / (2:ℝ) ^ j) / 256 = (2:ℝ) ^ ((-(j:ℝ)) + (-((8:ℕ):ℝ))) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (j:ℝ),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (((8:ℕ)):ℝ), h8,
      Real.rpow_natCast]
    ring
  rw [alphaSeed_eq_rpow, hrhs]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hcast : ((mSeed a j : ℕ) : ℝ) = (a : ℝ) - (j : ℝ) := by
    simp only [mSeed]
    exact Nat.cast_sub hja
  have hb' : (a : ℝ) + 8 ≤ (b₀ : ℝ) := by exact_mod_cast hb
  rw [hcast]
  push_cast
  linarith

/-- **Aux 13c (clause 3 of `eq:stage1-three-seed-gates`).**
`alpha_{1,j} < beta_{1,j}`, because the schedule's bound puts
`alpha_{1,j}` below `2^{-j}/256` while `beta_{1,j} = (3/5) 2^{-j}`. -/
theorem alphaSeed_lt_betaSeed {a b₀ j : ℕ} (hja : j ≤ a) (hb : a + 8 ≤ b₀) :
    alphaSeed a b₀ j < betaSeed j := by
  have hbound := alphaSeed_le_bound hja hb
  have hinv : (0:ℝ) < ((2:ℝ) ^ j)⁻¹ := by positivity
  have hlt : (1 / (2:ℝ) ^ j) / 256 < betaSeed j := by
    have e₁ : (1 / (2:ℝ) ^ j) / 256 = (1 / 256 : ℝ) * ((2:ℝ) ^ j)⁻¹ := by
      ring
    have e₂ : betaSeed j = (3 / 5 : ℝ) * ((2:ℝ) ^ j)⁻¹ := by
      simp only [betaSeed]; ring
    rw [e₁, e₂]
    exact mul_lt_mul_of_pos_right (by norm_num) hinv
  linarith

/-- **Aux 13d (monotonicity).**  The retained row density `alpha_{1,j}` is
antitone in the incoming robustness depth: a level that supplies *more* depth
retains *fewer* rows.  This is the general shape behind the frozen derivation
of `06:394--398`, where the input-depth request is a lower bound on `b_0` and
is used only through the resulting upper bound on `alpha_{1,j}`. -/
theorem alphaSeed_antitone_in_b₀ (a j : ℕ) {b b' : ℕ} (h : b ≤ b') :
    alphaSeed a b' j ≤ alphaSeed a b j := by
  rw [alphaSeed_eq_rpow, alphaSeed_eq_rpow]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hb : (b : ℝ) ≤ (b' : ℝ) := by exact_mod_cast h
  linarith

/-- **Aux 14 (range).**  `x_1 = 2^{-b_1}` is a legal density. -/
theorem xSeed_pos (b₁ : ℕ) : 0 < xSeed b₁ := by
  unfold xSeed; positivity

theorem xSeed_le_one (b₁ : ℕ) : xSeed b₁ ≤ 1 := by
  unfold xSeed
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (neg_nonpos.mpr (Nat.cast_nonneg b₁))

/-- **Aux 15 (range).**  `h_{1,j}` is a legal density. -/
theorem hSeed_pos (a j : ℕ) : 0 < hSeed a j := by
  unfold hSeed; positivity

theorem hSeed_le_one (a j : ℕ) : hSeed a j ≤ 1 := by
  unfold hSeed
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  have : (0:ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (mSeed a j : ℕ)) := by positivity
  linarith

/-- **Aux 15a (clause 4 of `eq:stage1-three-seed-gates`).**
`h_{1,j} <= x_1 = 2^{-b_1}`.

This is the frozen argument printed at `06-parameter-schedule.tex:411--417`:
`eq:j49-window` gives `b_1 = 2^{j_49(a-2)} <= 2^{(49/100) sqrt(a-2)}`, and
`m_{1,j} = a - j >= a - 2` for `j <= 2`, so
`b_1 <= 2^{(49/100) sqrt(m_{1,j})}`, i.e. `2^{-2^{(49/100) sqrt(m_{1,j})}}`
is at most `2^{-b_1}`.  The `b_1` window is the hypothesis; nothing about
`j_49` is re-derived here. -/
theorem hSeed_le_xSeed {a b₁ j : ℕ} (hj : j ≤ 2)
    (hwin : (b₁ : ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((mSeed a 2 : ℕ) : ℝ))) :
    hSeed a j ≤ xSeed b₁ := by
  have hmle : mSeed a 2 ≤ mSeed a j := by
    simp only [mSeed]; omega
  have hsqrt : Real.sqrt ((mSeed a 2 : ℕ) : ℝ) ≤ Real.sqrt ((mSeed a j : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmle)
  have hstep : (2:ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((mSeed a 2 : ℕ) : ℝ))
      ≤ (2:ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((mSeed a j : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hb : (b₁ : ℝ) ≤ (2:ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((mSeed a j : ℕ) : ℝ)) :=
    le_trans hwin hstep
  unfold hSeed xSeed
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **Aux 16 (copy-count legality).**  `1 <= p_{1,j}`, the first half of the
frozen gate `1 <= p_{1,j} <= q_1 < L_1` of `eq:stage1-three-seed-gates`. -/
theorem one_le_pSeed (a j : ℕ) : 1 ≤ pSeed a j := by
  have : (1:ℕ) ≤ 2 ^ (mSeed a j - 5) := Nat.one_le_two_pow
  simp only [pSeed]; omega

/-- **Aux 17 (copy-count legality).**  `p_{1,j} <= q_1` whenever `j <= 2` and
`m_{1,j} <= a`, closing the frozen gate `1 <= p_{1,j} <= q_1 < L_1`.  The proof
is the frozen closed form: `p_{1,j} = (9/16) 2^{a-j} <= (9/16) 2^a < 2^a - 2`
for `a >= 6`. -/
theorem pSeed_le_q₁ (F : Stage1SlotBinding) (j : ℕ) (ha : 6 ≤ F.a) :
    pSeed F.a j ≤ F.q₁ := by
  have hm : mSeed F.a j ≤ F.a := Nat.sub_le _ _
  have hstep : 18 * 2 ^ (mSeed F.a j - 5) ≤ 18 * 2 ^ (F.a - 5) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsplit : 2 ^ F.a = 2 ^ (F.a - 5) * 32 := by
    conv_lhs => rw [show F.a = F.a - 5 + 5 by omega]
    rw [pow_add]
    norm_num
  have hpos : (1:ℕ) ≤ 2 ^ (F.a - 5) := Nat.one_le_two_pow
  have h2 : (2:ℕ) ≤ 2 ^ (F.a - 5) * 32 := by omega
  simp only [pSeed, Stage1SlotBinding.q₁, hsplit]
  omega

/-! ### Aux-lemma battery A4: the two ceiling gates of
`eq:stage1-projection-ceilings` (`06-parameter-schedule.tex:372--392`) -/

/-- **Aux 18 (row-ceiling floor and cap).**  `1 <= ceil(m_R alpha) <= m_R` for a
density `alpha in (0,1]` and a nonempty row carrier: the first clause of
`eq:stage1-projection-ceilings` line 1. -/
theorem one_le_rowCeiling {m : ℕ} {α : ℝ} (hm : 1 ≤ m) (hα0 : 0 < α) :
    1 ≤ ⌈(m : ℝ) * α⌉₊ := by
  refine Nat.one_le_iff_ne_zero.mpr ?_
  intro h
  have hpos : 0 < (m : ℝ) * α := by
    have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    nlinarith
  exact absurd (Nat.ceil_eq_zero.mp h) (not_le.mpr hpos)

theorem rowCeiling_le {m : ℕ} {α : ℝ} (hα1 : α ≤ 1) : ⌈(m : ℝ) * α⌉₊ ≤ m := by
  refine Nat.ceil_le.mpr ?_
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  nlinarith

/-- **Aux 19 (column-ceiling floor and cap).**
`1 <= ceil(n_R^p h) <= n_R^p`: the second clause of the same line. -/
theorem one_le_colCeiling {n p : ℕ} {h : ℝ} (hn : 1 ≤ n) (hh0 : 0 < h) :
    1 ≤ ⌈((n : ℝ) ^ p) * h⌉₊ := by
  refine Nat.one_le_iff_ne_zero.mpr ?_
  intro hzero
  have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpow : (1:ℝ) ≤ (n:ℝ) ^ p := one_le_pow₀ hn'
  have hpos : 0 < ((n : ℝ) ^ p) * h := by nlinarith
  exact absurd (Nat.ceil_eq_zero.mp hzero) (not_le.mpr hpos)

theorem colCeiling_le {n p : ℕ} {h : ℝ} (hh1 : h ≤ 1) :
    ⌈((n : ℝ) ^ p) * h⌉₊ ≤ n ^ p := by
  refine Nat.ceil_le.mpr ?_
  have hn : (0:ℝ) ≤ (n:ℝ) ^ p := by positivity
  push_cast
  nlinarith

/-- **Aux 20 (the strict projection gate).**  The third clause of
`eq:stage1-projection-ceilings` (`06-parameter-schedule.tex:377--380`),
with the frozen proof of lines 385--391:
```
(ceil(n^p h) - 1) n^{L-p} < n^L h <= n^L x <= ceil(n^L x).
```
This is exactly the inequality that forces the fixed-coordinate projection of
`07-one-level-construction.tex:191--196` to have at least `ceil(n^p h)`
distinct image points. -/
theorem projectionCeiling_strict {n p L : ℕ} {h x : ℝ}
    (hn : 1 ≤ n) (hpL : p ≤ L) (hh0 : 0 < h) (hhx : h ≤ x) :
    ((⌈((n : ℝ) ^ p) * h⌉₊ - 1 : ℕ) : ℝ) * ((n : ℝ) ^ (L - p)) <
      (⌈((n : ℝ) ^ L) * x⌉₊ : ℝ) := by
  have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hone : 1 ≤ ⌈((n : ℝ) ^ p) * h⌉₊ := one_le_colCeiling hn hh0
  have hcast : ((⌈((n : ℝ) ^ p) * h⌉₊ - 1 : ℕ) : ℝ)
      = (⌈((n : ℝ) ^ p) * h⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hone]; norm_num
  have hceil : (⌈((n : ℝ) ^ p) * h⌉₊ : ℝ) - 1 < ((n : ℝ) ^ p) * h := by
    have hnn : (0:ℝ) ≤ ((n : ℝ) ^ p) * h := by positivity
    have := Nat.ceil_lt_add_one hnn
    linarith
  have htail : (0:ℝ) < (n : ℝ) ^ (L - p) := by positivity
  have hsplit : ((n : ℝ) ^ p) * ((n : ℝ) ^ (L - p)) = (n : ℝ) ^ L := by
    rw [← pow_add]
    congr 1
    omega
  have hstep : ((⌈((n : ℝ) ^ p) * h⌉₊ - 1 : ℕ) : ℝ) * ((n : ℝ) ^ (L - p))
      < ((n : ℝ) ^ L) * h := by
    rw [hcast]
    calc ((⌈((n : ℝ) ^ p) * h⌉₊ : ℝ) - 1) * ((n : ℝ) ^ (L - p))
        < (((n : ℝ) ^ p) * h) * ((n : ℝ) ^ (L - p)) := by
          exact mul_lt_mul_of_pos_right hceil htail
      _ = ((n : ℝ) ^ L) * h := by rw [← hsplit]; ring
  have hmono : ((n : ℝ) ^ L) * h ≤ ((n : ℝ) ^ L) * x := by
    have : (0:ℝ) ≤ (n : ℝ) ^ L := by positivity
    nlinarith
  have hceil2 : ((n : ℝ) ^ L) * x ≤ (⌈((n : ℝ) ^ L) * x⌉₊ : ℝ) := Nat.le_ceil _
  linarith

/-! ### Aux-lemma battery A5: the exact block-count gate

`06-parameter-schedule.tex:394--410` proves the last line of
`eq:stage1-three-seed-gates` *before the ceiling*, by the displayed identity
```
(T-2)(3/5 - 1/256) - (9/16)T = (43T - 1526)/1280 > 0,   T = 2^a.
```
Reader: first line of `eq:paper-stage1-extraction-gates`. -/

/-- **Aux 21 (the frozen block-count calculation).**  With `T = 2^a`,
`u = 2^{-j}` and the schedule's `alpha_{1,j} <= u/256`, the exact block-count
gate of `eq:stage1-three-seed-gates` holds *before* taking the ceiling.  The
guard `6 <= a` is the frozen `43T >= 1526` threshold; the schedule delivers
`a >= 7` (`06-parameter-schedule.tex:404`). -/
theorem blockCount_abstract {T u α : ℝ} (hT : 64 ≤ T) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hα0 : 0 < α) (hα : α ≤ u / 256) :
    9 / 16 * T * u ≤ (T - 2) * (3 / 5 * u - α) / (1 - α) := by
  have hα1 : α ≤ 1 / 256 := by
    have : u / 256 ≤ 1 / 256 := by linarith
    linarith
  have hden : (0:ℝ) < 1 - α := by linarith
  have hT2 : (0:ℝ) ≤ T - 2 := by linarith
  have hnum : 0 ≤ 3 / 5 * u - α := by nlinarith
  -- the frozen identity `(T-2)(3/5 - 1/256) - (9/16)T = (43T - 1526)/1280 > 0`
  have hkey : 9 / 16 * T * u ≤ (T - 2) * (3 / 5 * u - u / 256) := by
    nlinarith [mul_nonneg hu0.le (show (0:ℝ) ≤ 43 * T - 1526 by linarith)]
  have hstep : (T - 2) * (3 / 5 * u - u / 256) ≤ (T - 2) * (3 / 5 * u - α) := by
    nlinarith
  have hdiv : (T - 2) * (3 / 5 * u - α) ≤ (T - 2) * (3 / 5 * u - α) / (1 - α) := by
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg hT2 hnum]
  linarith

theorem blockCount_pre_ceiling (F : Stage1SlotBinding) (j : ℕ) (α : ℝ)
    (ha : 6 ≤ F.a) (hj : 5 ≤ mSeed F.a j) (hα0 : 0 < α)
    (hα : α ≤ (1 / 2 ^ j) / 256) :
    (pSeed F.a j : ℝ) ≤ (F.q₁ : ℝ) * (betaSeed j - α) / (1 - α) := by
  have hjle : j ≤ F.a := by simp only [mSeed] at hj; omega
  have hupos : (0:ℝ) < 1 / 2 ^ j := by positivity
  have hu1 : (1:ℝ) / 2 ^ j ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hT64 : (64:ℝ) ≤ (2:ℝ) ^ F.a := by
    calc (64:ℝ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ F.a := pow_le_pow_right₀ (by norm_num) ha
  have hq₁ : (F.q₁ : ℝ) = (2:ℝ) ^ F.a - 2 := by
    have h2 : (2:ℕ) ≤ 2 ^ F.a := by
      have : (2:ℕ) ^ 1 ≤ 2 ^ F.a := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    have hcast : ((2 ^ F.a - 2 : ℕ) : ℝ) = (2:ℝ) ^ F.a - 2 := by
      rw [Nat.cast_sub h2]; push_cast; ring
    simpa [Stage1SlotBinding.q₁] using hcast
  have hβ : betaSeed j = 3 / 5 * (1 / 2 ^ j) := by
    simp only [betaSeed]; ring
  have hTsplit : (2:ℝ) ^ F.a = (2:ℝ) ^ (F.a - j) * 2 ^ j := by
    rw [← pow_add]; congr 1; omega
  have hpj : (pSeed F.a j : ℝ) = 9 / 16 * ((2:ℝ) ^ F.a) * (1 / 2 ^ j) := by
    rw [pSeed_eq_nine_sixteenths F.a j hj]
    have hw : (wSeed F.a j : ℝ) = (2:ℝ) ^ (F.a - j) := by
      simp only [wSeed, mSeed]; push_cast; ring
    rw [hw, hTsplit]
    field_simp
  rw [hpj, hq₁, hβ]
  exact blockCount_abstract hT64 hupos hu1 hα0 (by simpa using hα)

/-! ## §7  The three scalar hard-seed calls, `eq:stage1-three-scalar-seeds`

`07-one-level-construction.tex:161--173`.  For each `j in {0,1,2}` the frozen
text makes an **independent** call to the inherited General Hard Seed theorem
at exponent `m_{1,j} = a - j`, whose exact conclusion is
```
comp <R, p_{1,j}, alpha_{1,j}, h_{1,j}>  >=  D + a - j.
```
Reader `eq:paper-stage1-three-seeds`. -/

/-- **One frozen Stage-1 hard-seed call.**

The record carries the numeric parameters of the call together with exactly
those side conditions of `eq:stage1-three-seed-gates`,
`eq:stage1-hard-seed-threshold`, `eq:input-depth-request` and
`eq:stage1-scales` that are **not** consequences of the others.  Everything
else in the frozen clause set is a theorem below -- `gate_exponent`,
`gate_copy_count`, `gate_row_column_density`, `gate_column_density`,
`gate_block_count` -- so the structure never restates a derived telescope
(`M3`).

*Honest scope.*  This record is **not** a certificate that a hard-seed call
succeeded, and it asserts nothing about any matrix.  It is the frozen
*admissibility* side of one call: seven numeric fields whose satisfaction is
checkable from `(a, j, s, b_0, b_1, C_in, m_HS)` alone (`gates_are_numeric`).
`M2`/`M4` compliance: the inherited theorem's conclusion is **not** a field;
it is supplied to `hardSeedRung_conclusion` as an explicit binder, so no
complexity claim can be read out of constructor data.  In particular a
`HardSeedRung` may exist for a source matrix for which the General Hard Seed
hypotheses `Robust(R, 1/10, b_0)`, `1 <= b_0`, `3 <= comp(R)` all fail: the
record does not carry them, and no theorem here pretends it does. -/
structure HardSeedRung where
  /-- The compiler-fixed Stage-1 exponent. -/
  a : ℕ
  /-- The rung index `j in {0,1,2}`. -/
  j : ℕ
  /-- The Stage-3 bin width `s`, which enters through the input-depth
  request `eq:input-depth-request` (`06-parameter-schedule.tex:449`). -/
  s : ℕ
  /-- The incoming robustness depth `b_0`. -/
  b₀ : ℕ
  /-- The Stage-1 output depth `b_1` of `eq:stage1-scales`
  (`06-parameter-schedule.tex:319`), which fixes `x_1 = 2^{-b_1}`. -/
  b₁ : ℕ
  /-- The universal configuration field `C_in` of the input-depth reading
  warning (`06-parameter-schedule.tex:437--465`); `C_in >= 0` is automatic
  in `ℕ`. -/
  cIn : ℕ
  /-- The hard-seed exponent threshold `m_HS`, the canonical least witness of
  `eq:contract-hard-seed-threshold-names`; no numeral is required. -/
  mHS : ℕ
  /-- `5 <= m_HS`, the first conjunct of the tail predicate `HSThreshold`
  (`D-inherited-contracts.tex:496`). -/
  five_le_mHS : 5 ≤ mHS
  /-- `eq:stage1-hard-seed-threshold` (`06-parameter-schedule.tex:351`):
  `a - 2 >= m_HS`. -/
  threshold : mHS ≤ a - 2
  /-- `eq:stage1-three-seed-gates`: the rung index range. -/
  j_le_two : j ≤ 2
  /-- `05-public-records.tex:416--418`: `s` is a **positive** power of two. -/
  s_pos : 0 < s
  /-- `05-public-records.tex:420`: `64 | s`. -/
  sixtyFour_dvd_s : 64 ∣ s
  /-- `eq:input-depth-request` (`06-parameter-schedule.tex:449`):
  `b_0 >= a + 2 + log_2 s + C_in`. -/
  input_depth : a + 2 + Nat.log 2 s + cIn ≤ b₀
  /-- The `b_1` window: `b_1 = 2^{j_49(a-2)} <= 2^{(49/100) sqrt(a-2)}`, from
  `eq:stage1-scales` (`06:319`) and `eq:j49-window` (`06:84`).  This is the
  frozen hypothesis behind `h_{1,j} <= x_1` (`06:411--417`); `j_49` itself is
  not transcribed, only the window it certifies. -/
  b₁_window :
    (b₁ : ℝ) ≤ (2:ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((mSeed a 2 : ℕ) : ℝ))

namespace HardSeedRung

variable (S : HardSeedRung)

/-- The rung's exponent `m_{1,j}`. -/
def m : ℕ := mSeed S.a S.j

/-- The rung's copy count `p_{1,j}`. -/
def p : ℕ := pSeed S.a S.j

/-- The rung's retained row density `alpha_{1,j}`. -/
noncomputable def α : ℝ := alphaSeed S.a S.b₀ S.j

/-- The rung's retained column density `h_{1,j}`. -/
noncomputable def h : ℝ := hSeed S.a S.j

/-- The rung's target column density `beta_{1,j}`. -/
noncomputable def β : ℝ := betaSeed S.j

/-- The gate `m_HS <= m_{1,j}` is derivable, not assumed twice (`M3`): the
threshold clause plus `j <= 2` already give it. -/
theorem mHS_le_m : S.mHS ≤ S.m := by
  have := S.threshold
  have := S.j_le_two
  simp only [m, mSeed]
  omega

/-- The frozen closed form is available at every legal rung: `5 <= m_{1,j}`,
hence `p_{1,j} = (9/16) w_{1,j}`. -/
theorem five_le_m : 5 ≤ S.m := le_trans S.five_le_mHS S.mHS_le_m

/-- `a >= 7` at every legal rung -- the frozen consequence of
`eq:stage1-hard-seed-threshold` recorded at `06-parameter-schedule.tex:404`. -/
theorem seven_le_a : 7 ≤ S.a := by
  have h1 := S.five_le_mHS
  have h2 := S.threshold
  omega

/-- `j <= a` at every legal rung, so the natural subtraction in `m_{1,j}` is
the honest one.  (`D-inherited-contracts.tex:494` makes the same remark about
`m - j` in `eq:contract-hard-seed`.) -/
theorem j_le_a : S.j ≤ S.a := le_trans S.j_le_two (le_trans (by norm_num) S.seven_le_a)

/-- `s >= 64`: the frozen derivation of `06-parameter-schedule.tex:975`
("`64 | s`, hence `s >= 64`") from the two accessor clauses. -/
theorem sixtyFour_le_s : 64 ≤ S.s := Nat.le_of_dvd S.s_pos S.sixtyFour_dvd_s

/-- `log_2 s >= 6`, the numeric content of `s >= 64` used by the input-depth
request. -/
theorem six_le_log_s : 6 ≤ Nat.log 2 S.s := by
  have h64 : Nat.log 2 64 = 6 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  calc (6:ℕ) = Nat.log 2 64 := h64.symm
    _ ≤ Nat.log 2 S.s := Nat.log_mono_right S.sixtyFour_le_s

/-- `b_0 >= a + 8`: `eq:input-depth-request` with `C_in >= 0` and
`log_2 s >= 6`.  This is the exact strength the frozen schedule uses at
`06:394--398` to get `alpha_{1,j} <= 2^{-j}/256`. -/
theorem eight_add_a_le_b₀ : S.a + 8 ≤ S.b₀ := by
  have h := S.input_depth
  have h6 := S.six_le_log_s
  omega

/-- The gate `m_{1,j} <= b_0` -- the **second** half of clause 1 of
`eq:stage1-three-seed-gates` (`06-parameter-schedule.tex:355`) -- is derivable
too, so it is not carried as constructor data (`M3` forbids restating a
derived telescope).  The telescope is
`s_pos` + `64 | s` `=>` `log_2 s >= 6`, with `eq:input-depth-request` `=>`
`a + 8 <= b_0`, whence `m_{1,j} = a - j <= a <= a + 8 <= b_0`.  Note that
`j_le_two` is *not* needed: the bound holds at every rung index, which is what
makes `atRung` uniform in `j`. -/
theorem mSeed_le_b₀ : mSeed S.a S.j ≤ S.b₀ := by
  have h := S.eight_add_a_le_b₀
  simp only [mSeed]
  omega

/-- The rung's Stage-1 slot binding, derived from `(a, s)`.  It exists at
every legal rung because `a >= 7 >= 3` and `s > 0`; nothing new is assumed. -/
def binding : Stage1SlotBinding where
  a := S.a
  s := S.s
  three_le_a := le_trans (by norm_num) S.seven_le_a
  s_pos := S.s_pos

@[simp] theorem binding_a : S.binding.a = S.a := rfl

@[simp] theorem binding_s : S.binding.s = S.s := rfl

/-- The schedule's row-density bound `alpha_{1,j} <= 2^{-j}/256`
(`06-parameter-schedule.tex:394--398`). -/
theorem alpha_le_bound : S.α ≤ (1 / 2 ^ S.j) / 256 :=
  alphaSeed_le_bound S.j_le_a S.eight_add_a_le_b₀

/-! ### The frozen clause set of `eq:stage1-three-seed-gates`, in order

`06-parameter-schedule.tex:355--368` prints five clauses, simultaneously for
`j = 0,1,2`.  All five hold at every legal rung, and only the parts that are
not consequences of the rest are fields. -/

/-- **Clause 1**: `m_HS <= m_{1,j} <= b_0`. -/
theorem gate_exponent : S.mHS ≤ S.m ∧ S.m ≤ S.b₀ :=
  ⟨S.mHS_le_m, S.mSeed_le_b₀⟩

/-- **Clause 2**: `1 <= p_{1,j} <= q_1 < L_1`. -/
theorem gate_copy_count :
    1 ≤ S.p ∧ S.p ≤ S.binding.q₁ ∧ S.binding.q₁ < S.binding.L₁ :=
  ⟨one_le_pSeed S.a S.j,
    pSeed_le_q₁ S.binding S.j (le_trans (by norm_num) S.seven_le_a),
    S.binding.q₁_lt_L₁⟩

/-- **Clause 3**: `0 < alpha_{1,j} < beta_{1,j} <= 1`. -/
theorem gate_row_column_density : 0 < S.α ∧ S.α < S.β ∧ S.β ≤ 1 :=
  ⟨alphaSeed_pos _ _ _,
    alphaSeed_lt_betaSeed S.j_le_a S.eight_add_a_le_b₀,
    betaSeed_le_one S.j⟩

/-- **Clause 4**: `0 < h_{1,j} <= x_1 = 2^{-b_1} <= 1`. -/
theorem gate_column_density :
    0 < S.h ∧ S.h ≤ xSeed S.b₁ ∧ xSeed S.b₁ ≤ 1 :=
  ⟨hSeed_pos _ _, hSeed_le_xSeed S.j_le_two S.b₁_window, xSeed_le_one S.b₁⟩

/-- **Clause 5**: the exact block-count gate
`p_{1,j} <= ceil(q_1 (beta_{1,j} - alpha_{1,j})/(1 - alpha_{1,j}))`, obtained
from the pre-ceiling calculation of `06:394--410` and `Nat.le_ceil`. -/
theorem gate_block_count :
    S.p ≤ ⌈(S.binding.q₁ : ℝ) * (S.β - S.α) / (1 - S.α)⌉₊ := by
  have hreal : (S.p : ℝ) ≤ (S.binding.q₁ : ℝ) * (S.β - S.α) / (1 - S.α) :=
    blockCount_pre_ceiling S.binding S.j S.α
      (le_trans (by norm_num) S.seven_le_a) S.five_le_m
      (alphaSeed_pos _ _ _) S.alpha_le_bound
  have := le_trans hreal (Nat.le_ceil _)
  exact_mod_cast this

/-- **The whole frozen clause set at one rung.**  This is
`eq:stage1-three-seed-gates` (`06-parameter-schedule.tex:355--368`) in the
kernel, clause by clause and in the printed order. -/
theorem gates_hold :
    (S.mHS ≤ S.m ∧ S.m ≤ S.b₀) ∧
    (1 ≤ S.p ∧ S.p ≤ S.binding.q₁ ∧ S.binding.q₁ < S.binding.L₁) ∧
    (0 < S.α ∧ S.α < S.β ∧ S.β ≤ 1) ∧
    (0 < S.h ∧ S.h ≤ xSeed S.b₁ ∧ xSeed S.b₁ ≤ 1) ∧
    S.p ≤ ⌈(S.binding.q₁ : ℝ) * (S.β - S.α) / (1 - S.α)⌉₊ :=
  ⟨S.gate_exponent, S.gate_copy_count, S.gate_row_column_density,
    S.gate_column_density, S.gate_block_count⟩

/-- **`M1`/`M4` check.**  The fields of a rung are a purely numeric
predicate: they are decided by `(a, j, s, b_0, b_1, C_in, m_HS)` alone and
mention no matrix, no protocol and no promise certificate.  The one real-valued
field, the `b_1` window, is a comparison between two real numbers built from
`b_1` and `a` alone. -/
theorem gates_are_numeric :
    5 ≤ S.mHS ∧ S.mHS ≤ S.a - 2 ∧ S.j ≤ 2 ∧
      0 < S.s ∧ 64 ∣ S.s ∧ S.a + 2 + Nat.log 2 S.s + S.cIn ≤ S.b₀ ∧
      (S.b₁ : ℝ) ≤ (2:ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((mSeed S.a 2 : ℕ) : ℝ)) :=
  ⟨S.five_le_mHS, S.threshold, S.j_le_two, S.s_pos,
    S.sixtyFour_dvd_s, S.input_depth, S.b₁_window⟩

/-! ### Aux-lemma battery A6: general structural properties of `HardSeedRung`

Three unit tests that are **general in the rung**, not statements about the
concrete witness.  Each would fail if the encoding were wrong in a specific
way, which is what makes them tests rather than decoration. -/

/-- **Aux 24 (upward closure in the incoming depth).**  Every gate is upward
closed in `b_0`: a level that supplies *more* robustness depth than
`eq:input-depth-request` demands still yields a legal rung, with all other
parameters unchanged.

*What this test detects.*  Had `b_0` been pinned by an equation (say
`b_0 = a + 2 + log_2 s + C_in`) instead of the frozen `>=`-request, this
declaration would not typecheck. -/
def raiseDepth (S : HardSeedRung) {b₀' : ℕ} (h : S.b₀ ≤ b₀') : HardSeedRung where
  a := S.a
  j := S.j
  s := S.s
  b₀ := b₀'
  b₁ := S.b₁
  cIn := S.cIn
  mHS := S.mHS
  five_le_mHS := S.five_le_mHS
  threshold := S.threshold
  j_le_two := S.j_le_two
  s_pos := S.s_pos
  sixtyFour_dvd_s := S.sixtyFour_dvd_s
  input_depth := le_trans S.input_depth h
  b₁_window := S.b₁_window

@[simp] theorem raiseDepth_a {b₀' : ℕ} (h : S.b₀ ≤ b₀') :
    (S.raiseDepth h).a = S.a := rfl

@[simp] theorem raiseDepth_b₀ {b₀' : ℕ} (h : S.b₀ ≤ b₀') :
    (S.raiseDepth h).b₀ = b₀' := rfl

/-- **Aux 25 (the promised monotone effect).**  Raising the incoming depth
does not merely preserve legality; it shrinks the retained row density, which
is the direction the schedule's `alpha_{1,j} <= 2^{-j}/256` bound needs. -/
theorem raiseDepth_alpha_le {b₀' : ℕ} (h : S.b₀ ≤ b₀') :
    (S.raiseDepth h).α ≤ S.α :=
  alphaSeed_antitone_in_b₀ S.a S.j h

/-- **Aux 26 (uniformity in the rung index).**  The three Stage-1 calls are
three instances of **one** construction, repeated independently for
`j = 0, 1, 2` (`07-one-level-construction.tex:206`).  The encoding must
therefore be uniform in `j`: from a legal rung at one index, a legal rung at
any other index in range exists, with every other parameter untouched.

*What this test detects.*  Any field that silently coupled the rung index to a
schedule quantity -- e.g. a `b_1` that depended on `j`, or an `m_HS <= m_{1,j}`
carried as a field rather than derived -- would break this. -/
def atRung (S : HardSeedRung) {j' : ℕ} (hj' : j' ≤ 2) : HardSeedRung where
  a := S.a
  j := j'
  s := S.s
  b₀ := S.b₀
  b₁ := S.b₁
  cIn := S.cIn
  mHS := S.mHS
  five_le_mHS := S.five_le_mHS
  threshold := S.threshold
  j_le_two := hj'
  s_pos := S.s_pos
  sixtyFour_dvd_s := S.sixtyFour_dvd_s
  input_depth := S.input_depth
  b₁_window := S.b₁_window

@[simp] theorem atRung_j {j' : ℕ} (hj' : j' ≤ 2) : (S.atRung hj').j = j' := rfl

@[simp] theorem atRung_a {j' : ℕ} (hj' : j' ≤ 2) : (S.atRung hj').a = S.a := rfl

@[simp] theorem atRung_binding {j' : ℕ} (hj' : j' ≤ 2) :
    (S.atRung hj').binding = S.binding := rfl

/-- **Aux 27 (round trip).**  Re-indexing to the rung one already sits at is
the identity on every gate-relevant quantity: the exponent, the copy count and
the three densities are recovered exactly. -/
theorem atRung_self :
    (S.atRung S.j_le_two).m = S.m ∧ (S.atRung S.j_le_two).p = S.p ∧
      (S.atRung S.j_le_two).α = S.α ∧ (S.atRung S.j_le_two).β = S.β ∧
      (S.atRung S.j_le_two).h = S.h :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Aux-lemma battery A6b: the seven-clause reconstruction

Three further tests, general in the rung, that pin the *field boundary* of
`HardSeedRung` after the second half of clause 1 was demoted from constructor
data to the theorem `mSeed_le_b₀` (`M3`).  A structure demanding more than the
frozen seven clauses would fail `ofNumeric`; a structure still carrying the
demoted clause would fail `ofNumeric_roundTrip`. -/

/-- **Aux 28 (the demoted clause, free of the structure).**  The second half of
clause 1 of `eq:stage1-three-seed-gates`, `m_{1,j} <= b_0`, follows from just
**three** of the seven side conditions -- `0 < s`, `64 | s` and
`eq:input-depth-request` -- and does so **uniformly in `j`**, with no appeal to
`j <= 2`, to `m_HS`, or to `eq:stage1-hard-seed-threshold`.

*What this test detects.*  The demotion needs only `a <= b_0`, and the frozen
`eq:input-depth-request` supplies it with room to spare (`a + 8 <= b_0`, via
`64 | s` forcing `log_2 s >= 6`).  Dropping the depth request entirely makes
the lemma false -- take `a = 1`, `j = 0`, `b_0 = 0` -- so the clause could not
be demoted in a structure without it.  What the lemma pins is *which* fields
carry the demoted clause: the retained `s_pos`, `sixtyFour_dvd_s` and
`input_depth`, and not `j_le_two`, `m_HS` or
`eq:stage1-hard-seed-threshold`. -/
theorem mSeed_le_b₀_of_input_depth {a j s b₀ cIn : ℕ} (hs : 0 < s) (hd : 64 ∣ s)
    (hin : a + 2 + Nat.log 2 s + cIn ≤ b₀) : mSeed a j ≤ b₀ := by
  have h64 : (64 : ℕ) ≤ s := Nat.le_of_dvd hs hd
  have hlog : 6 ≤ Nat.log 2 s := by
    have h : Nat.log 2 64 = 6 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    calc (6 : ℕ) = Nat.log 2 64 := h.symm
      _ ≤ Nat.log 2 s := Nat.log_mono_right h64
  simp only [mSeed]
  omega

/-- **Aux 29 (inhabitation from the frozen clauses alone).**  A rung can be
built from the seven frozen numeric side conditions and nothing else.

*What this test detects.*  Any field beyond the seven -- a re-stated telescope,
an inherited-conclusion field, or a complexity/robustness field forbidden by
`M1`/`M2`/`M4` -- would leave this definition with an unfilled field. -/
def ofNumeric {a j s b₀ b₁ cIn mHS : ℕ}
    (h₁ : 5 ≤ mHS) (h₂ : mHS ≤ a - 2) (h₃ : j ≤ 2)
    (h₄ : 0 < s) (h₅ : 64 ∣ s) (h₆ : a + 2 + Nat.log 2 s + cIn ≤ b₀)
    (h₇ : (b₁ : ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt ((mSeed a 2 : ℕ) : ℝ))) :
    HardSeedRung where
  a := a
  j := j
  s := s
  b₀ := b₀
  b₁ := b₁
  cIn := cIn
  mHS := mHS
  five_le_mHS := h₁
  threshold := h₂
  j_le_two := h₃
  s_pos := h₄
  sixtyFour_dvd_s := h₅
  input_depth := h₆
  b₁_window := h₇

/-- **Aux 30 (round trip on the field boundary).**  Feeding a rung's own seven
clauses back through `ofNumeric` returns that rung, definitionally.  Together
with `gates_are_numeric` -- which reads the same seven clauses off a rung --
this says the structure is *exactly* the seven-clause numeric predicate: no
more (or `ofNumeric` would not typecheck) and no fewer (or this identity would
not hold). -/
theorem ofNumeric_roundTrip :
    ofNumeric S.five_le_mHS S.threshold S.j_le_two S.s_pos S.sixtyFour_dvd_s
      S.input_depth S.b₁_window = S := rfl

end HardSeedRung

/-- **`eq:stage1-three-scalar-seeds`, read off from one legal rung.**

The inherited General Hard Seed corollary `eq:contract-hard-seed` is the named
binder `hardSeed`; the content of this theorem is the frozen *identification*
of its conclusion with `D + m_{1,j} = D + a - j` (line 170), which is where the
rung index enters the Stage-1 bookkeeping. -/
theorem hardSeedRung_conclusion {X Y : Type*} [Fintype X] [Fintype Y]
    (S : HardSeedRung) (R : X → Y → Bool) (Dsrc : ℕ)
    (hardSeed : Dsrc + S.m ≤
      Dfamily (interlaceFun R S.p) (bracketGE X Y S.p S.α S.h)) :
    Dsrc + (S.a - S.j) ≤
      Dfamily (interlaceFun R S.p) (bracketGE X Y S.p S.α S.h) := by
  simpa [HardSeedRung.m, mSeed] using hardSeed

/-! ## §8  The Stage-1 robustness certificate `eq:stage1-robust-certificate`

`07-one-level-construction.tex:206--215`: "This argument is repeated
independently for `j = 0,1,2`; no theorem adds bits to the `j = 2` conclusion.
By the definition of the three-rung quantity, the three inequalities are
exactly
```
Lambda_3(M_1^T, 1, 2^{-b_1}, 3/5) >= B_cap.
```
"  Reader `eq:paper-M1-robust`. -/

/-- **Aux 22 (no theorem adds bits).**  The frozen sentence of line 206--207
made checkable: the `Lambda_3` offsets `+1` and `+2` exactly cancel the losses
`-1` and `-2` of the rungs `j = 1, 2`, so all three transported bounds land on
the *same* value `B_cap`. -/
theorem noBitsAdded (Dsrc a : ℕ) (ha : 2 ≤ a) :
    Dsrc + (a - 0) = bCap Dsrc a ∧
      1 + (Dsrc + (a - 1)) = bCap Dsrc a ∧
      2 + (Dsrc + (a - 2)) = bCap Dsrc a := by
  refine ⟨by simp [bCap], ?_, ?_⟩ <;> simp only [bCap] <;> omega

/-- **`eq:stage1-robust-certificate`.**

From the three *independently transported* target-rung bounds of
`07-one-level-construction.tex:202--205`,
```
comp <M_1^T, 1, x_1, beta_{1,j}>  >=  D + a - j    (j = 0,1,2),
```
the three-rung quantity of `def:lambda` satisfies
`Lambda_3(M_1^T, 1, x_1, 3/5) >= B_cap`.

The three hypotheses are **named binders**: each is the endpoint of one
independent transport (block balancing at `alpha_{1,j}`, fixed-coordinate
projection through `eq:stage1-projection-ceilings`, transpose invariance and
restriction monotonicity), and none of them is an axiom here.  What this
this theorem establishes is that the three of them, at exactly those offsets,
are the frozen certificate -- with the column densities `beta_{1,j}` matched to the
`Lambda_3` rungs `y, y/2, y/4` at `y = 3/5` by `betaSeed_one`/`betaSeed_two`.

*Trivial-witness pole.*  The conclusion is a lower bound on a `min`, so it is
not satisfiable by a degenerate reading: `stage1RobustCertificate_not_automatic`
exhibits a legal matrix at which `Lambda_3(-, 1, x_1, 3/5) = 0 < B_cap`, so the
three hypotheses do real work; and `stage1RobustCertificate_tight` shows the
bound is attained, so none of the three is over-strong. -/
theorem stage1RobustCertificate (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] (Dsrc b₁ : ℕ)
    (rung₀ : Dsrc + (F.a - 0) ≤
      Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (betaSeed 0)))
    (rung₁ : Dsrc + (F.a - 1) ≤
      Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (betaSeed 1)))
    (rung₂ : Dsrc + (F.a - 2) ≤
      Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (betaSeed 2))) :
    bCap Dsrc F.a ≤ LambdaGE (stageOneT F R) 1 (xSeed b₁) (3 / 5) := by
  have ha : 2 ≤ F.a := le_trans (by norm_num) F.three_le_a
  obtain ⟨e₀, e₁, e₂⟩ := noBitsAdded Dsrc F.a ha
  have h₀ : bCap Dsrc F.a ≤
      Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (3 / 5)) := by
    rw [← e₀, ← betaSeed_zero]; exact rung₀
  have h₁ : bCap Dsrc F.a ≤
      1 + Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (3 / 5 / 2)) := by
    rw [← e₁]
    have : (3 / 5 / 2 : ℝ) = betaSeed 1 := by rw [betaSeed_one, betaSeed_zero]
    rw [this]
    omega
  have h₂ : bCap Dsrc F.a ≤
      2 + Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (3 / 5 / 4)) := by
    rw [← e₂]
    have : (3 / 5 / 4 : ℝ) = betaSeed 2 := by rw [betaSeed_two, betaSeed_zero]
    rw [this]
    omega
  unfold LambdaGE
  exact le_min h₀ (le_min h₁ h₂)

/-- **Tightness pole for `stage1RobustCertificate`.**  If the three rungs hold
with *equality* -- which is what `eq:stage1-three-scalar-seeds` delivers, since
the inherited theorem's conclusion is exact -- then the three-rung quantity is
exactly `B_cap`.  So no hypothesis above is stronger than the frozen text
supplies, and no bit is silently gained. -/
theorem stage1RobustCertificate_tight (F : Stage1SlotBinding) (R : X → Y → Bool)
    [Fintype X] [Fintype Y] (Dsrc b₁ : ℕ)
    (eq₀ : Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (3 / 5))
      = Dsrc + (F.a - 0))
    (eq₁ : Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (3 / 5 / 2))
      = Dsrc + (F.a - 1))
    (eq₂ : Dfamily (interlaceFun (stageOneT F R) 1)
        (bracketGE (Stage1Cols F Y) (Stage1Rows F X) 1 (xSeed b₁) (3 / 5 / 4))
      = Dsrc + (F.a - 2)) :
    LambdaGE (stageOneT F R) 1 (xSeed b₁) (3 / 5) = bCap Dsrc F.a := by
  have ha : 2 ≤ F.a := le_trans (by norm_num) F.three_le_a
  obtain ⟨e₀, e₁, e₂⟩ := noBitsAdded Dsrc F.a ha
  unfold LambdaGE
  rw [eq₀, eq₁, eq₂, e₀, e₁, e₂]
  simp

/-! ### Statement pole: the certificate is not automatic

`Lambda_3(-, 1, x, 3/5) >= B_cap` fails for a constant matrix, so the three
transported rungs of `stage1RobustCertificate` are genuine content and cannot
be dropped. -/

/-- **Aux 23 (general).**  Every bracket family over a *constant* ambient game
has family complexity `0`: each member's subgame is constant, and the empty
family takes `sInf` of the empty set. -/
theorem Dfamily_const {A B : Type*} (b : Bool)
    (Φ : Set (Finset A × Finset B)) :
    Dfamily (fun (_ : A) (_ : B) => b) Φ = 0 := by
  classical
  refine Nat.sInf_eq_zero.mpr ?_
  by_cases hΦ : ∃ RC, RC ∈ Φ
  · obtain ⟨RC, hRC⟩ := hΦ
    left
    refine ⟨RC, hRC, ?_⟩
    exact (PublicRecords.D_const (X := {a // a ∈ RC.1}) (Y := {c // c ∈ RC.2}) b).symm
  · right
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨RC, hRC, -⟩
    exact hΦ ⟨RC, hRC⟩

/-- **Statement pole.**  At the gate-legal slot binding and the legal
constant source matrix the three-rung quantity is `0`, while `B_cap = 7`.  So
`stage1RobustCertificate` cannot hold with its hypotheses removed. -/
theorem stage1RobustCertificate_not_automatic (b₁ : ℕ) :
    LambdaGE (stageOneT stage1Legal (fun (_ : Bool) (_ : Bool) => false)) 1
        (xSeed b₁) (3 / 5) = 0 ∧
      ¬ bCap 0 stage1Legal.a ≤
        LambdaGE (stageOneT stage1Legal (fun (_ : Bool) (_ : Bool) => false)) 1
          (xSeed b₁) (3 / 5) := by
  have hconst : (stageOneT stage1Legal (fun (_ : Bool) (_ : Bool) => false))
      = fun (_ : Stage1Cols stage1Legal Bool)
            (_ : Stage1Rows stage1Legal Bool) => false := rfl
  have hzero : LambdaGE (stageOneT stage1Legal
      (fun (_ : Bool) (_ : Bool) => false)) 1 (xSeed b₁) (3 / 5) = 0 := by
    rw [hconst]
    unfold LambdaGE
    have hI : ∀ k : ℕ, interlaceFun
        (fun (_ : Stage1Cols stage1Legal Bool)
             (_ : Stage1Rows stage1Legal Bool) => false) k
        = fun (_ : Fin k × Stage1Cols stage1Legal Bool)
              (_ : Fin k → Stage1Rows stage1Legal Bool) => false := fun _ => rfl
    rw [hI 1, Dfamily_const, Dfamily_const, Dfamily_const]
    norm_num
  refine ⟨hzero, ?_⟩
  rw [hzero]
  simp [bCap, stage1Legal]

/-! ## §9  Candidate B, kept as refuted evidence

Candidate B presents `M_1` as a restriction of the **full** `L_1`-fold
classical interlace.  The presentation is mathematically correct
(`stageOne_eq_fullInterlace_restrict`), but the typed copy count it offers is
`L_1`, not `q_1`, and the frozen certified scale of line 152 is read off the
selector width. -/

/-- Candidate B's identity: `M_1` is the `iota_1`-row-block restriction of the
full `L_1`-fold classical interlace of `R`.  True by `rfl`, so nothing is lost
by recording it. -/
theorem stageOne_eq_fullInterlace_restrict (F : Stage1SlotBinding)
    (R : X → Y → Bool) (p : Stage1Rows F X) (γ : Stage1Cols F Y) :
    stageOne F R p γ = interlaceFun R F.L₁ (F.iota₁ p.1, p.2) γ := rfl

/-- The binding at which the two candidate encodings are compared: the
gate-legal `stage1Legal`, i.e. `a = 7` and `s = 64`.

Citation correction (this is where the parked draft was wrong): the frozen
`04-guarded-source.tex:281` states only `s >= 4` for the unslabbed guarded
copy and says nothing about `s` being a power of two, and `s = 4` is anyway
excluded by the accessor clause `64 | s` of `05-public-records.tex:420`.  The
comparison is therefore made at `s = 64`, the least value satisfying
`s >= 4`, "`s` is a positive power of two" and `64 | s` together. -/
def candidateBBinding : Stage1SlotBinding := stage1Legal

@[simp] theorem candidateBBinding_q₁ : candidateBBinding.q₁ = 126 := rfl

@[simp] theorem candidateBBinding_L₁ : candidateBBinding.L₁ = 191 := rfl

/-- **The discriminating battery item.**  At the gate-legal binding the two
encodings offer different selector widths: Candidate A's `ceil(log_2 q_1)` is
the frozen `a = 7`, while Candidate B's `ceil(log_2 L_1) = ceil(log_2 191)` is
`8`.  Reading the certified scale `B_cap = D + a` of line 156 off Candidate B
therefore costs one bit, which is exactly the defect `M5`/`M8` forbid.
Candidate B is rejected. -/
theorem candidateB_selector_width_is_wrong :
    Nat.clog 2 candidateBBinding.q₁ = candidateBBinding.a ∧
      Nat.clog 2 candidateBBinding.L₁ = candidateBBinding.a + 1 := by
  refine ⟨clog_q₁ candidateBBinding, ?_⟩
  have ha : candidateBBinding.a = 7 := rfl
  rw [candidateBBinding_L₁, ha]
  have hupper : Nat.clog 2 191 ≤ 8 :=
    (Nat.clog_le_iff_le_pow (by norm_num)).2 (by norm_num)
  have hlower : 7 < Nat.clog 2 191 :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by norm_num)
  omega

/-! ## §10  Non-vacuity: nondegenerate inhabitants at legal parameter values

Two witnesses, both taken at `stage1Legal` -- the *smallest binding passing
every literal Stage-1 gate this module transcribes*: `a = 7`
(`06-parameter-schedule.tex:404`) and `s = 64` (`04:281`, `05:416--420`,
`06:975`).  The first exercises the Stage-1 matrix; the second exercises the
three-seed row and its full gate clause set.  The larger `a` that
`eq:stage1-C0-gate` forces on the compiler is out of scope here; see the
`stage1Legal` docstring. -/

/-- The source matrix `AND` on the two-element carriers -- nonconstant, so the
Stage-1 witness is not degenerate. -/
def witnessSource : Bool → Bool → Bool := fun x y => x && y

theorem witnessSource_nonconstant :
    witnessSource true true ≠ witnessSource true false := by decide

/-- The Stage-1 matrix at the gate-legal binding `a = 7`, `s = 64`. -/
def stageOneWitness : Stage1Rows stage1Legal Bool →
    Stage1Cols stage1Legal Bool → Bool :=
  stageOne stage1Legal witnessSource

/-- **Non-vacuity 1.**  The witness is nonconstant, both carriers are nonempty
and of the frozen sizes `q_1 m_R = 126 * 2 = 252` and
`n_R^{L_1} = 2^{191}`, and the reserved tail is genuinely unread. -/
theorem stageOneWitness_nondegenerate :
    stageOneWitness (⟨0, by norm_num⟩, true) (fun _ => true) = true ∧
      stageOneWitness (⟨0, by norm_num⟩, true) (fun _ => false) = false ∧
      Fintype.card (Stage1Rows stage1Legal Bool) = 252 ∧
      Fintype.card (Stage1Cols stage1Legal Bool) = 2 ^ 191 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [stageOne_rows_card]; rfl
  · rw [stageOne_cols_card]; rfl

/-- **Non-vacuity 2 (the hardest field).**  The reserved Stage-4 tail really is
discarded by the witness: the column map is not injective. -/
theorem stageOneWitness_tail_unread :
    ¬ Function.Injective
        (fun (γ : Stage1Cols stage1Legal Bool) => fun p => stageOneWitness p γ) :=
  stageOne_column_map_not_injective stage1Legal witnessSource
    (by decide : (true : Bool) ≠ false)

/-- The Stage-1 slot binding used by the seed witnesses.  It is `stage1Legal`:
`a = 7` is the smallest exponent `eq:stage1-hard-seed-threshold` permits
(`06-parameter-schedule.tex:404`) and `s = 64` the smallest bin width the
accessor clauses permit (`05-public-records.tex:416--420`,
`06-parameter-schedule.tex:975`). -/
def seedBinding : Stage1SlotBinding := stage1Legal

@[simp] theorem seedBinding_q₁ : seedBinding.q₁ = 126 := rfl

@[simp] theorem seedBinding_L₁ : seedBinding.L₁ = 191 := rfl

/-- **Non-vacuity 3.**  A legal `HardSeedRung` for each `j in {0,1,2}` at
`a = 7`, `s = 64`, `b_0 = 15`, `b_1 = 2`, `C_in = 0`, `m_HS = 5`.

Every value is forced to lie in a narrow legal window, and three of the seven
side-condition fields are discharged **at their boundary**:

* `m_HS = 5` is the least value `HSThreshold` permits
  (`D-inherited-contracts.tex:496`), and `m_HS <= a - 2 = 5` is tight, which
  is exactly `eq:stage1-hard-seed-threshold` at the smallest legal `a`;
* `s = 64` is the least value satisfying `s >= 4`, "`s` is a positive power of
  two" and `64 | s` simultaneously, so `log_2 s = 6`;
* `b_0 = 15` is the least legal incoming depth here, and both binding bounds
  meet at it: `eq:input-depth-request` gives
  `b_0 >= a + 2 + log_2 s + C_in = 7 + 2 + 6 + 0 = 15`, and the schedule's
  derived `b_0 >= a + 8 = 15` (`06-parameter-schedule.tex:394--398`) gives the
  same value, so `input_depth` is discharged as `15 <= 15` and
  `no_rung_with_small_b₀`'s `15 <= b_0` is tight.  The parked draft's
  `b_0 = 7` is *excluded* by exactly this clause, which is why its clause-3
  gate `alpha_{1,j} < beta_{1,j}` failed;
* `b_1 = 2 = 2^{j_49(5)}` is the frozen `eq:stage1-scales` value at `a = 7`
  (`j_49(5) = max{ j : 10000 j^2 <= 2401 * 5 } = 1`), and it satisfies the
  `b_1` window `b_1 <= 2^{(49/100) sqrt 5}` because `(49/100) sqrt 5 >= 1`.

At this extremal binding the schedule's row-density bound is met with
*equality* -- `alpha_{1,j} = 2^{m_{1,j} - b_0} = 2^{(7 - j) - 15}
= 2^{-j}/256` -- so the witness sits exactly on the `06:394--398` boundary the
block-count calculation consumes, and clause 5 still fires
(`seedRung_gates_hold`).  The full frozen clause set of
`eq:stage1-three-seed-gates` holds at all three rungs, which is the
LANE-GATE-3 requirement the parked draft failed. -/
def seedRung (j : ℕ) (hj : j ≤ 2) : HardSeedRung where
  a := 7
  j := j
  s := 64
  b₀ := 15
  b₁ := 2
  cIn := 0
  mHS := 5
  five_le_mHS := le_refl 5
  threshold := by norm_num
  j_le_two := hj
  s_pos := by norm_num
  sixtyFour_dvd_s := dvd_refl 64
  input_depth := by
    have h64 : Nat.log 2 64 = 6 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    omega
  b₁_window := by
    have hm : ((mSeed 7 2 : ℕ) : ℝ) = 5 := by norm_num [mSeed]
    rw [hm]
    have hs : (100 / 49 : ℝ) ≤ Real.sqrt 5 := by
      have h1 : Real.sqrt ((100 / 49 : ℝ) ^ 2) ≤ Real.sqrt 5 :=
        Real.sqrt_le_sqrt (by norm_num)
      rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 100 / 49)] at h1
    have hexp : (1:ℝ) ≤ (49 / 100 : ℝ) * Real.sqrt 5 := by linarith
    have hmono : (2:ℝ) ^ (1:ℝ) ≤ (2:ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt 5) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    rw [Real.rpow_one] at hmono
    simpa using hmono

/-- **Non-vacuity 4.**  The three rungs are *distinct and nondegenerate*: their
exponents are `7, 6, 5`, their copy counts `72, 36, 18`, and every copy count
satisfies the frozen gate `1 <= p_{1,j} <= q_1 = 126`. -/
theorem seedRung_values :
    (seedRung 0 (by norm_num)).m = 7 ∧ (seedRung 0 (by norm_num)).p = 72 ∧
    (seedRung 1 (by norm_num)).m = 6 ∧ (seedRung 1 (by norm_num)).p = 36 ∧
    (seedRung 2 (by norm_num)).m = 5 ∧ (seedRung 2 (by norm_num)).p = 18 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The rungs' derived slot binding is exactly `stage1Legal`, so the copy-count
gate of clause 2 is read against the frozen `q_1 = 126 < 191 = L_1`. -/
@[simp] theorem seedRung_binding (j : ℕ) (hj : j ≤ 2) :
    (seedRung j hj).binding = stage1Legal := rfl

theorem seedRung_p_le_q₁ (j : ℕ) :
    pSeed seedBinding.a j ≤ seedBinding.q₁ :=
  pSeed_le_q₁ seedBinding j (by norm_num [seedBinding, stage1Legal])

/-- **Non-vacuity 5.**  The frozen closed form `p_{1,j} = (9/16) w_{1,j}` fires
at every rung of the witness. -/
theorem seedRung_closed_form (j : ℕ) (hj : j ≤ 2) :
    (pSeed 7 j : ℝ) = 9 / 16 * (wSeed 7 j : ℝ) :=
  pSeed_eq_nine_sixteenths 7 j (by have := hj; simp only [mSeed]; omega)

/-- **Non-vacuity 6.**  The exact block-count gate of
`eq:stage1-three-seed-gates` fires at the witness binding and at the frozen
row-density bound `alpha_{1,j} <= 2^{-j}/256`, for every `j in {0,1,2}`.  This
is the hypothesis bundle of `blockCount_pre_ceiling` inhabited at legal values,
so that bundle is not vacuous. -/
theorem blockCount_fires (j : ℕ) (hj : j ≤ 2) :
    (pSeed seedBinding.a j : ℝ)
      ≤ (seedBinding.q₁ : ℝ) * (betaSeed j - (1 / 2 ^ j) / 512) / (1 - (1 / 2 ^ j) / 512) := by
  refine blockCount_pre_ceiling seedBinding j _ (by norm_num [seedBinding, stage1Legal])
    (by simp only [mSeed]; norm_num [seedBinding, stage1Legal]; omega) (by positivity) ?_
  have : (0:ℝ) < 1 / 2 ^ j := by positivity
  linarith

/-! ### Rung-level non-vacuity: the frozen clause set actually fires

`seedRung` is not merely *typeable*; the five clauses of
`eq:stage1-three-seed-gates` all hold there, and the two that the parked draft
silently omitted (clauses 3 and 4) hold **strictly** and with a real gap. -/

/-- **Non-vacuity 7 (the decisive one).**  The complete frozen clause set of
`eq:stage1-three-seed-gates` holds at all three rungs of the witness. -/
theorem seedRung_gates_hold (j : ℕ) (hj : j ≤ 2) :
    ((seedRung j hj).mHS ≤ (seedRung j hj).m ∧ (seedRung j hj).m ≤ (seedRung j hj).b₀) ∧
    (1 ≤ (seedRung j hj).p ∧ (seedRung j hj).p ≤ stage1Legal.q₁ ∧
      stage1Legal.q₁ < stage1Legal.L₁) ∧
    (0 < (seedRung j hj).α ∧ (seedRung j hj).α < (seedRung j hj).β ∧
      (seedRung j hj).β ≤ 1) ∧
    (0 < (seedRung j hj).h ∧ (seedRung j hj).h ≤ xSeed (seedRung j hj).b₁ ∧
      xSeed (seedRung j hj).b₁ ≤ 1) ∧
    (seedRung j hj).p ≤
      ⌈(stage1Legal.q₁ : ℝ) * ((seedRung j hj).β - (seedRung j hj).α) /
        (1 - (seedRung j hj).α)⌉₊ :=
  (seedRung j hj).gates_hold

/-- **Non-vacuity 8.**  The retained row density of the witness is
`alpha_{1,j} = 2^{-8-j}`, a genuinely nontrivial density: it is strictly
positive and strictly below the target column density `beta_{1,j}`.  A
degenerate reading with `alpha = 0` or `alpha >= beta` is excluded. -/
theorem seedRung_alpha_nondegenerate (j : ℕ) (hj : j ≤ 2) :
    0 < (seedRung j hj).α ∧ (seedRung j hj).α < (seedRung j hj).β :=
  ⟨(seedRung j hj).gate_row_column_density.1,
    (seedRung j hj).gate_row_column_density.2.1⟩

/-- `2^{-k} = 1/2^k` for a natural exponent, the only real-power fact the
witness's density values need. -/
theorem two_rpow_neg_natCast (k : ℕ) : (2:ℝ) ^ (-(k:ℝ)) = 1 / 2 ^ k := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, one_div]

/-- **Non-vacuity 8b (the witness sits exactly on the schedule boundary).**
Because `b_0 = 15 = a + 8` is the *least* legal incoming depth, the retained
row density of the witness meets the schedule's own bound
`alpha_{1,j} <= 2^{-j}/256` (`06-parameter-schedule.tex:394--398`) with
**equality**: `alpha_{1,j} = 2^{(7-j)-15} = 2^{-j}/256`.

This is the boundary-tightness claim of `seedRung`'s docstring made
kernel-checkable rather than asserted.  It is also the sharpest legal place to
stand: by `alphaSeed_antitone_in_b₀` every legal rung at `a = 7` has
`alpha_{1,j}` no larger than this, so the clause-5 block-count gate still
firing here (`seedRung_gates_hold`) is the hardest instance of that gate the
frozen schedule admits at `a = 7`. -/
theorem seedRung_alpha_eq_bound (j : ℕ) (hj : j ≤ 2) :
    (seedRung j hj).α = (1 / 2 ^ j) / 256 := by
  change alphaSeed 7 15 j = _
  rw [alphaSeed_eq_rpow]
  interval_cases j
  · rw [show ((mSeed 7 0 : ℕ) : ℝ) + -((15:ℕ) : ℝ) = -((8:ℕ) : ℝ) by
      norm_num [mSeed], two_rpow_neg_natCast]
    norm_num
  · rw [show ((mSeed 7 1 : ℕ) : ℝ) + -((15:ℕ) : ℝ) = -((9:ℕ) : ℝ) by
      norm_num [mSeed], two_rpow_neg_natCast]
    norm_num
  · rw [show ((mSeed 7 2 : ℕ) : ℝ) + -((15:ℕ) : ℝ) = -((10:ℕ) : ℝ) by
      norm_num [mSeed], two_rpow_neg_natCast]
    norm_num

/-- **Non-vacuity 9.**  The Stage-1 output density is `x_1 = 2^{-b_1} = 1/4`,
strictly between `0` and `1`.  This is the field the parked draft did not
carry at all: with `b_1 = 0` one would get `x_1 = 1`, i.e. *no* column
restriction, and clause 4 would say nothing. -/
theorem seedRung_xSeed_value (j : ℕ) (hj : j ≤ 2) :
    xSeed (seedRung j hj).b₁ = 1 / 4 := by
  change xSeed 2 = 1 / 4
  unfold xSeed
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  norm_num

theorem seedRung_xSeed_nondegenerate (j : ℕ) (hj : j ≤ 2) :
    0 < xSeed (seedRung j hj).b₁ ∧ xSeed (seedRung j hj).b₁ < 1 := by
  rw [seedRung_xSeed_value j hj]
  norm_num

/-- **Non-vacuity 10.**  The input-depth request is *tight* at the witness in
the sense that the parked draft's `b_0 = 7` is refuted: at `a = 7`, `s = 64`,
`C_in = 0` the frozen request forces `b_0 >= 15`, so no `HardSeedRung` with
`b_0 < 15` exists at those values.  This is the LANE-GATE-3 defect made
checkable. -/
theorem no_rung_with_small_b₀ (S : HardSeedRung) (ha : S.a = 7) : 15 ≤ S.b₀ := by
  have h := S.eight_add_a_le_b₀
  omega

/-- **Non-vacuity 10b (the witness's depth is extremal, not merely legal).**
The two halves of `no_rung_with_small_b₀` and `seedRung` meet: `b_0 = 15` is
attained by the witness, and `15` is a lower bound for **every** legal rung at
`a = 7`.  So the witness's incoming depth is the least the frozen schedule
permits at that exponent -- there is no legal rung strictly below it and none
to lower it to.

This replaces an asserted minimality claim with a checked one.  (The bound
needs neither `s = 64` nor `C_in = 0`: `64 | s` alone forces
`log_2 s >= 6`.) -/
theorem seedRung_b₀_is_least (j : ℕ) (hj : j ≤ 2) :
    (seedRung j hj).b₀ = 15 ∧ ∀ S : HardSeedRung, S.a = 7 → 15 ≤ S.b₀ :=
  ⟨rfl, fun S ha => no_rung_with_small_b₀ S ha⟩

/-! ## §11  Hypothesis consistency

Every headline statement of this module is a conditional over named binders, so
the standing check is that no bundle is self-contradictory at the frozen side
conditions.  Three probes, one refutation pole, and one recorded coverage
limit. -/

/-- **Consistency probe 1, `stageOne_scale_eq_bCap`.**  Its one remaining
hypothesis `hlower` is *equivalent*, given the proved upper half, to the single
frozen equation `comp(M_1) = comp(R) + a` of line 152.  So it is contradictory
only if that equation is, and nothing stronger than the frozen text is
assumed. -/
theorem scale_hypothesis_iff {X Y : Type*} [Fintype X] [Fintype Y]
    (F : Stage1SlotBinding) (R : X → Y → Bool) :
    (D R + F.a ≤ D (stageOne F R)) ↔ D (stageOne F R) = D R + F.a := by
  constructor
  · intro h; exact Nat.le_antisymm (stageOne_selector_upper F R) h
  · intro h; exact le_of_eq h.symm

/-- **Consistency probe 2, `stage1RobustCertificate`.**  The three rung
hypotheses are the three conclusions of **one** construction (frozen line 206:
"This argument is repeated independently for `j = 0,1,2`"), not two cases of a
promise split, so conjoining them is legitimate; and their numeric shape is
satisfiable *simultaneously with* the frozen conclusion at every `(D, a)`.
So no contradiction follows from the bundle. -/
theorem stage1RobustCertificate_hypotheses_consistent (Dsrc a : ℕ) :
    ∃ d₀ d₁ d₂ : ℕ,
      Dsrc + (a - 0) ≤ d₀ ∧ Dsrc + (a - 1) ≤ d₁ ∧ Dsrc + (a - 2) ≤ d₂ ∧
        bCap Dsrc a ≤ min d₀ (min (1 + d₁) (2 + d₂)) := by
  refine ⟨Dsrc + a, Dsrc + a, Dsrc + a, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · simp only [bCap]
    exact le_min (le_refl _) (le_min (by omega) (by omega))

/-- **Consistency probe 3, `HardSeedRung`.**  The seven-field bundle is
inhabited, so no contradiction follows from it.  This is the check the parked
draft failed: its record omitted clauses 3 and 4 of
`eq:stage1-three-seed-gates`, and its only inhabitant sat at `b_0 = a`, where
the omitted clause 3 (`alpha_{1,j} < beta_{1,j}`) is **false** at all three
rungs -- `alpha_{1,0} = 2^a 2^{-a} = 1 > 3/5 = beta_{1,0}`.  Carrying the full
clause set and inhabiting it at the least legal `b_0 = 15 = a + 8` repairs
both halves at once. -/
theorem hardSeedRung_bundle_consistent : Nonempty HardSeedRung :=
  ⟨seedRung 0 (by norm_num)⟩

/-- **Statement pole for the repair.**  The parked draft's binding is now
refuted inside the type: at `a = 7` no rung has `b_0 = 7`, because
`eq:input-depth-request` with `64 | s` forces `b_0 >= 15`. -/
theorem parked_binding_is_illegal :
    ¬ ∃ S : HardSeedRung, S.a = 7 ∧ S.b₀ = 7 := by
  rintro ⟨S, ha, hb⟩
  have h := S.eight_add_a_le_b₀
  omega

/-- **Coverage limit, binding on every consumer.**  Neither hypothesis is
*inhabited* here at a concrete matrix.  For `stageOne_scale_eq_bCap` the
obstruction is exactly the open reboot facade `eq:contract-stage1-output`
(`D-inherited-contracts.tex:872`): its lower half is the odd-copy call at
`p_odd`, and `bCap_is_not_a_complexity_claim` shows the only matrices whose
Stage-1 complexity is computable here -- the constant ones -- fail it.  For
`stage1RobustCertificate` the obstruction is the three transports of lines
175--205.  This theorem records that the failure is a *missing lower bound*,
not an inconsistency: the proved upper half holds on the constant matrix with
room to spare, so the missing side is one-directional. -/
theorem scale_upper_half_alone_holds :
    D (stageOne stage1Legal (fun (_ : Bool) (_ : Bool) => false))
      ≤ D (fun (_ : Bool) (_ : Bool) => false) + stage1Legal.a ∧
    ¬ (D (fun (_ : Bool) (_ : Bool) => false) + stage1Legal.a
        ≤ D (stageOne stage1Legal (fun (_ : Bool) (_ : Bool) => false))) := by
  have h : D (stageOne stage1Legal (fun (_ : Bool) (_ : Bool) => false)) = 0 :=
    PublicRecords.D_const false
  refine ⟨stageOne_selector_upper _ _, ?_⟩
  rw [h, PublicRecords.D_const false]
  simp [stage1Legal]

end EthInapproximability.ParameterizedNP.StageOneInterlace
