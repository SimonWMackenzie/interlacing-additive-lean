import EthInapproximability.ParameterizedNP.FirstWrapperClose
import EthInapproximability.ParameterizedNP.EntryGates

/-!
# Parameterized NP route: the opening of the direct bridge, and its entry point

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`BRIDGE-OPENING-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`).

## What this module is

The **opening** of Section 10: the sentence that throws away the construction
and the display that names what survives it.  The bridge is handed a Boolean
matrix `W`, its exact complexity `C_W`, and the two common-threshold lower
bounds -- nothing else -- and this module is the Lean rendering of *that
handover*, together with the two base estimates the frozen text immediately
rules into scope from it.

The handover object is **not redefined here**.  It is the banked
`FirstWrapperClose.CommonThreshold`, consumed strictly **by pin**: imported,
cited, never restated and never widened.  That structure is the Lean form of
the `interfacebox` at `09:1809--1816` ("From this point onward, `W` is an
ordinary Boolean matrix known only through `eq:common-exact`--`eq:common-low`
and its explicit `YES` protocol"), and its three fields are literally the three
clauses Section 10 opens by listing.  `bridgeEntry_iff` below checks that
identification in the kernel: the input type is exactly `comp W = C_W` plus the
two clauses of `eq:direct-input`, with **no** fourth field.

**Why the wiring matters, stated without claiming anything downstream.**  The
banked `BridgeOutputEquality.directRobustification` (`BRIDGE-OUTPUT-003`) takes
`thm:direct-robustification`'s input as three *free* hypotheses -- `hCWeq`,
`hNear`, `hInput` at the fixed `y = 3/5` -- and its own non-vacuity note records
that "the bridge's input has no exhibited inhabitant and can have none until
Stages 1--4 land".  Those three hypotheses are exactly the three fields of the
Section-9 interface: `bridgeEntry_iff` and `directInput_at_fixed_y` below
identify them in the kernel, and `opening_at_the_paper_instance` supplies the
paper's own object for them, conditionally.  **No conclusion of that banked
theorem is restated, weakened, or re-derived here** (GAP-EXPOSED G1).

`thm:direct-robustification`'s own binders stay **theorem hypotheses and never
record fields**: `C_W >= 3` (`10:40`), the row-threshold legality `0 < theta <= 1`
(`10:39`), the deletion range `0 < delta_U < 1` (`10:38`), `b_out >= 1`
(`10:41`) and the first entry gate (`10:53`) are all written as binders of the
theorems that need them.  Nothing about them is folded into the consumed
structure, which would silently change the interface Section 9 delivers.

## Autoformalization anchors

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
`autoformalization`.

* `sections/10-direct-bridge.tex` (SHA-256
  `ae0defbd6dd93950fc67db70584da3d0e68061a060b04cae78b1d4584358c984`):
  * lines **4--6**, "At this point all construction-specific information is
    discarded.  We use only a Boolean matrix `W`, its exact complexity `C_W`,
    and the two common-threshold lower bounds";
  * **`eq:direct-input`** (label line 11), display lines **8--10** --
    `comp<W,1,theta,1-delta_U> >= C_W` and
    `Lambda_3(W,1,theta,y) >= C_W - 1`;
  * lines **13--17**, "The first clause retains full strength after a small
    column deletion.  The second may be one bit lower, but survives two further
    column halvings.  The point of the bridge is that these two facts, at the
    same row threshold `theta`, are enough to build an ordinary robust seed at
    any requested finite depth";
  * lines **19--21**, the two-copy applicability sentence, and
    **`eq:direct-two-copy`** (label line 24);
  * line **26**, "Its bottom rung has complexity at least `C_W - 2`, which is
    positive in every application";
  * lines **27--28** and **`eq:direct-three-copy`** (label line 31);
  * `thm:direct-robustification` (label line 35), its binder list only:
    lines **36--37** (the globally fixed `delta = 1/10`, `y = 1/2 + delta = 3/5`),
    line **38** (`0 < delta_U < 1`), line **39** (`0 < theta <= 1`), line **40**
    (`comp W = C_W >= 3`), line **41** (`b_out >= 1`), the first gate of
    `eq:direct-entry-gates` (display line **53**), and the legality sentence at
    lines **58--60**.
* `sections/09-first-wrapper.tex`, the `interfacebox` **`09:1809--1816`** -- the
  supplier of the entry point, landed as `FIRST-WRAPPER-CLOSE-001`.
* `sections/03-preliminaries.tex`, lines **215--219**, the globally fixed
  `delta = 1/10` and `y = 1/2 + delta = 3/5`.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/04-bridge.tex`.  The file was
opened and the cited item checked to state the same fact.  **Exactly one**
reader item is claimed by this module, and it is one no other declaration in
`src/` claims:

* **`eq:bridge-common-input`** (label line **15**, statement lines **12--14**),
  `D_W(1; theta, 1 - delta_U) >= C_W` and `Lambda_W(1, theta, 3/5) >= C_W - 1`
  -- claimed by `directInput_at_fixed_y` and by nothing else.  It states the
  same fact as the frozen `eq:direct-input` at the globally fixed `y = 3/5`,
  which is why that declaration is written at `yFixed` rather than at a free
  `y`.

**Deliberately not claimed**, to avoid a double assignment:

* `lem:bridge-base-estimates` (label line 31): its **first** inequality is
  already assigned to `BRIDGE-TWOCOPY-001` (`TwoCopyLadder.lean`) and its
  **second** to `BRIDGE-THREECOPY-001` (`ThreeCopyRowStep.lean`).  The
  composition theorems below consume those two landed results by pin and claim
  no reader item of their own.
* the fixed-constant display at lines 22--26, `eq:bridge-Q0` (label line 92),
  the sentence at line 94, and `eq:bridge-exact-Q-gates` (label line 99) are
  already assigned to `BRIDGE-ENTRY-001` (`EntryGates.lean`).  `yFixed` below
  reifies the frozen `y = 1/2 + delta` of `10:36--37` / `03:215--219`, a
  *defining display* that `BRIDGE-ENTRY-001` did not reify (it reified
  `delta` only, as `deltaFixed`), and claims no reader item.
* `eq:bridge-output` (label line 110), `eq:bridge-carriers` (label line 117)
  and the selector sentence at lines 112--113 stay with `BRIDGE-001` and are
  untouched: **this module states none of `thm:direct-robustification`'s
  conclusions.**
* the reader's opening prose at lines 4--10 and 17--20 is prose and is **not**
  cited as a statement.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Conditional statuses of the consumed chain, disclosed exactly

Everything below the opening is consumed **by pin**; the ledger statuses of the
consumed rows travel unchanged and this module improves none of them.

1. **`FIRST-WRAPPER-CLOSE-001`** supplies `CommonThreshold`.  Its own
   `firstWrapperClose` runs under the **named, undischarged** binder
   `FirstWrapperClose.DenseRung` -- `eq:wrapper-u-dense` (`09:262--263`), whose
   frozen proof is the seven blocks `09:335--1781`.  Consequently
   `commonThreshold_of_firstWrapperClose`, the paper's own instance of the entry
   point, is **conditional**, and so is `opening_at_the_paper_instance` here.
2. Through that row travel, unchanged: `TERMINAL-TWO-STREAM-001` (the headline
   `lem:terminal-two-stream` is landed as a **stated** claim, not a proved
   theorem -- and it is not invoked anywhere below),
   `DENSE-WRAPPER-FRONTIER-001` and `WRAPPER-PROTECTED-EARLY-001` (landed, with
   their GAP-EXPOSED items intact), and `WRAPPER-MASS-REDISTRIBUTION-001`
   (landed with four GAP-EXPOSED items, and with its own **deferred canonical
   inhabitation** obligation on record).
3. **`BRIDGE-TWOCOPY-001`** and **`BRIDGE-THREECOPY-001`** supply
   `eq:direct-two-copy` and `eq:direct-three-copy` from `eq:direct-input`
   clause two; both are landed and are consumed here without restatement.
4. **`BRIDGE-ENTRY-001`** supplies `Q_0`, `lambda`, `r_Q`, `Q`, the gate pair
   and the legality implication `10:58--60`.  This module assigns no numeral to
   any of them and states no schedule legality.
5. **`SCHEDULE-001`** is not consumed at all: no quantity that `sec:parameters`
   defines is given a value here.

## GAP-EXPOSED, named

* **G1 (`10:61--74`).**  `thm:direct-robustification`'s *conclusions* --
  `R^+ = ^T Int_Q(W)`, `eq:direct-output`, and the selector sentence -- are
  **not** stated, proved, or approximated here.  They stay with `BRIDGE-001`
  and its Lean rows.  This module stops at the theorem's binder list and at the
  two base estimates the text derives before the theorem is stated.
* **G2 (`10:76--571`).**  The column-defect apparatus, `lem:defect-induction`,
  the level readouts, and everything after them are other rows'
  (`BRIDGE-DEFECT-001`, `BRIDGE-COPYREST-001`, and the output rows).  Nothing
  here touches them.
* **G3 (unconditional entry).**  An *unconditional* inhabitant of the entry
  point at the route's own `W` is not exhibited, because `DenseRung` is
  undischarged upstream.  See the registered obligation below.
* **G4 (no protocol object).**  The `YES` protocol that `09:1815` lists beside
  the three displays is **not** a field of the consumed structure and is not
  reconstructed here; `FirstWrapperClose.promise_cases_do_not_conjoin` records
  why conjoining it with `eq:common-exact` would be inconsistent.

## DEFERRED CANONICAL INHABITATION (registered, open)

The paper constructs exactly one object that enters this bridge: the Section-9
output `W = ^T U` at `C_W = C + r` (`09:1794--1795`).  That instance -- not a
synthetic one -- is the required witness, and it is landed here as
`opening_at_the_paper_instance`, **conditionally** on
`FirstWrapperClose.DenseRung` and the low-rung inputs, exactly as its supplier
is.  The unconditional form is **not** claimed; it is discharged precisely when
`DenseRung` is proved, i.e. when the routed certificate system of GAP-EXPOSED
M1 of `WRAPPER-MASS-REDISTRIBUTION-001` lands in Lean.

**No synthetic stand-in is offered, and that is forced rather than chosen.**
`bridgeEntry_forces_dense_rows` proves that *any* inhabitant of the entry point
at `C_W >= 2` satisfies `|Rows(W)| * theta > 1`, and
`bridgeEntry_forces_large_row_carrier` turns that, under the frozen first entry
gate, into `|Rows(W)| > 640`.  So a small hand-built matrix cannot enter this
bridge at all, and in particular the NON-FIDELITY probe of
`FIRST-WRAPPER-CLOSE-001` cannot: `opening_rejects_the_wrapper_close_probe`
refutes it in the kernel, at every density triple, because its complexity is
`2` and the opening demands `3 <= C_W`.  What *is* exhibited synthetically is
only the arithmetic half -- `opening_entry_parameters_are_satisfiable` shows the
binder list `10:38--41` together with the first gate is satisfiable at legal
values -- and that theorem is explicitly about the parameters, never about a
matrix.

## Axiom surface

`LegacyNPCC.Core` and `LegacyNPCC.Bridge` only, through the existing chain.
`LegacyNPCC.Stage12` is **not** imported and the AGHP balanced-family axiom is
**not** reached.  Every declaration is `Classical`-only; this module declares no
`axiom`, contains no unproved placeholder of either kind the release gate scans
for, and carries no opaque certificate.

**No route completion is claimed anywhere in this module.**
-/

namespace EthInapproximability.ParameterizedNP.DirectBridgeOpening

open NPCC
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.FirstWrapperClose

/-! ## Section 1  The globally fixed `y`

`10:36--37` and `03:215--219` fix `y` by a *defining display*,
`y = 1/2 + delta`, on top of the `delta` that `BRIDGE-ENTRY-001` already
reified as `EntryGates.deltaFixed`.  It is therefore reified as a `def` that
evaluates through that definitional chain, never as the numeral `3/5`; the
numeral is a *consequence*, recorded as `yFixed_eq`. -/

/-- **`y = 1/2 + delta = 3/5`** (`10-direct-bridge.tex:36--37`;
`03-preliminaries.tex:215--219`).

Written as the paper writes it -- one half plus the globally fixed `delta` of
`EntryGates.deltaFixed` -- so that the value is obtained by evaluating the
defining chain rather than by assigning a numeral.  Reader: the fixed-constant
display at `04-bridge.tex:22--26`, which `BRIDGE-ENTRY-001` claims; no reader
item is claimed for this `def`. -/
noncomputable def yFixed : ℝ := 1 / 2 + EntryGates.deltaFixed

/-- **Aux 1.1.**  Evaluating the defining chain of `yFixed` gives the paper's
own printed value `3/5`.  This is the *conclusion* of the display, not its
definition. -/
@[simp] theorem yFixed_eq : yFixed = 3 / 5 := by
  rw [yFixed, EntryGates.deltaFixed_eq]; norm_num

/-- **Aux 1.2.**  `yFixed` lies in the range `(0, 1]` that every bracket-family
side condition of the consumed chain requires, so the frozen constant never
needs a side hypothesis of its own. -/
theorem yFixed_mem : 0 < yFixed ∧ yFixed ≤ 1 := by
  rw [yFixed_eq]; constructor <;> norm_num

/-! ## Section 2  The entry point (`10:4--12`), consumed by pin -/

/-- **Battery 1 (identity): the entry point is exactly `10:4--10`, and nothing
more.**

`10:4--6` says the bridge uses "only a Boolean matrix `W`, its exact complexity
`C_W`, and the two common-threshold lower bounds".  The banked
`FirstWrapperClose.CommonThreshold` is that list and is closed under it: the
`iff` below is provable in both directions precisely because the structure has
three fields and no fourth.  If a field were ever added to the interface -- an
extra promise, a carrier bound, a protocol -- this direction-`mpr` would break,
which is the point of stating it.

General in the carriers, the matrix, `C_W` and the three real parameters. -/
theorem bridgeEntry_iff {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) (θ δU y : ℝ) :
    CommonThreshold W CW θ δU y ↔
      (D W = CW
        ∧ CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU))
        ∧ CW - 1 ≤ LambdaGE W 1 θ y) :=
  ⟨fun h => ⟨h.exact, h.dense, h.low⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- **`eq:direct-input` at the globally fixed `y` (`10:8--10`).**

*Reader counterpart:* `04-bridge.tex`, `eq:bridge-common-input` (label line 15,
statement lines 12--14), `D_W(1; theta, 1 - delta_U) >= C_W` and
`Lambda_W(1, theta, 3/5) >= C_W - 1`.  The reader writes the second estimate
with `y` already instantiated at the globally fixed `3/5`, which is why this
declaration -- the one that claims that item -- is stated at `yFixed` and reads
the numeral off through `yFixed_eq`.

The exact complexity `comp W = C_W` of `10:5` is deliberately **not** returned
here: the reader's line 10 states it in prose, and prose is not claimed.  It is
available from the same record as `bridgeEntry_iff`'s first component. -/
theorem directInput_at_fixed_y {X Y : Type*} [Fintype X] [Fintype Y]
    {W : X → Y → Bool} {CW : ℕ} {θ δU : ℝ}
    (h : CommonThreshold W CW θ δU yFixed) :
    CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU))
      ∧ CW - 1 ≤ LambdaGE W 1 θ (3 / 5) := by
  refine ⟨h.dense, ?_⟩
  have hlow := h.low
  rwa [yFixed_eq] at hlow

/-! ## Section 3  Two general facts the opening needs -/

/-- **General aux: a game that ignores its row input costs at most one bit.**

If every row of `g` agrees with the row `a_0`, then Bob can announce the answer
and the protocol has depth `1`.  Stated with an explicit witness row `a_0`
rather than a `Subsingleton` instance, so that it applies verbatim to the
subtype carriers `{a // a in R}` that `subgame` produces.

Unregistered supporting lemma about the vendored
`Workspace.Types.Protocol.Protocol`; general in both carriers. -/
theorem D_le_one_of_row_independent {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) (a₀ : A) (h : ∀ a b, g a b = g a₀ b) : D g ≤ 1 := by
  refine Nat.sInf_le ⟨Workspace.Types.Protocol.Protocol.bNode (fun b => g a₀ b)
    (Workspace.Types.Protocol.Protocol.leaf false)
    (Workspace.Types.Protocol.Protocol.leaf true), ?_, ?_⟩
  · simp [Workspace.Types.Protocol.Protocol.cost]
  · intro a b
    simp only [Workspace.Types.Protocol.Protocol.eval]
    by_cases hb : g a₀ b = true
    · simp [hb, h a b]
    · simp only [Bool.not_eq_true] at hb
      simp [hb, h a b]

/-- **Battery 2 (nondegeneracy): the entry point forces a dense row carrier.**

Any matrix that enters the bridge at `C_W >= 2` satisfies
`|Rows(W)| * theta > 1`.

Reason: if `ceil(|Rows(W)| * theta) <= 1` then the one-row set
`{(0, x_0)}` together with the full column set is a legal member of the
one-copy bracket family `<W, 1, theta, 1 - delta_U>` -- the row ceiling is met
by a single row and the column ceiling is met by all columns because
`1 - delta_U <= 1`.  Its induced subgame ignores Alice, so it costs one bit,
and `eq:common-dense` caps `C_W` at `1`.

This is the statement pole that makes the deferred canonical inhabitation
**forced**: no small hand-built matrix can inhabit the bridge's entry point, so
a synthetic stand-in for the paper's `W` is not merely undesirable but
unavailable.  General in the carriers, the matrix, `C_W`, and the three real
parameters. -/
theorem bridgeEntry_forces_dense_rows {X Y : Type*} [Fintype X] [Fintype Y]
    {W : X → Y → Bool} {CW : ℕ} {θ δU y : ℝ}
    (hδ0 : 0 ≤ δU) (hX : 1 ≤ Fintype.card X) (hCW : 2 ≤ CW)
    (h : CommonThreshold W CW θ δU y) :
    (1 : ℝ) < (Fintype.card X : ℝ) * θ := by
  classical
  haveI : DecidableEq X := Classical.decEq _
  by_contra hcon
  have hcon' : (Fintype.card X : ℝ) * θ ≤ 1 := not_lt.mp hcon
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card X)
  have hceil : ⌈(Fintype.card X : ℝ) * θ⌉₊ ≤ 1 :=
    Nat.ceil_le.mpr (by exact_mod_cast hcon')
  -- the one-row member of the one-copy bracket family
  have hfilter : ((({((0 : Fin 1), x₀)} : Finset (Fin 1 × X))).filter
      (fun p => p.1 = (0 : Fin 1))).card = 1 := by
    rw [Finset.filter_singleton]
    simp
  have hRow : IsEquipartitionedGE ({((0 : Fin 1), x₀)} : Finset (Fin 1 × X))
      (Finset.univ : Finset (Fin 1)) ⌈(Fintype.card X : ℝ) * θ⌉₊ := by
    intro q _
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    rw [hfilter]
    exact hceil
  have hcolcard : (Finset.univ : Finset (Fin 1 → Y)).card = Fintype.card Y := by
    simp
  have hCol : ⌈((Fintype.card Y : ℝ) ^ (1 : ℕ)) * (1 - δU)⌉₊
      ≤ (Finset.univ : Finset (Fin 1 → Y)).card := by
    rw [hcolcard]
    refine Nat.ceil_le.mpr ?_
    have hn : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := by positivity
    have hstep : ((Fintype.card Y : ℝ) ^ (1 : ℕ)) * (1 - δU)
        ≤ ((Fintype.card Y : ℝ) ^ (1 : ℕ)) * 1 := by
      refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc ((Fintype.card Y : ℝ) ^ (1 : ℕ)) * (1 - δU)
        ≤ ((Fintype.card Y : ℝ) ^ (1 : ℕ)) * 1 := hstep
      _ = (Fintype.card Y : ℝ) := by rw [pow_one, mul_one]
  have hmem : (({((0 : Fin 1), x₀)} : Finset (Fin 1 × X)),
      (Finset.univ : Finset (Fin 1 → Y))) ∈ bracketGE X Y 1 θ (1 - δU) :=
    ⟨hRow, hCol⟩
  have hle : Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU))
      ≤ D (subgame (interlaceFun W 1)
        ({((0 : Fin 1), x₀)} : Finset (Fin 1 × X))
        (Finset.univ : Finset (Fin 1 → Y))) :=
    HardSeedFacade.Dfamily_le_of_mem (interlaceFun W 1) _ hmem
  -- the induced subgame ignores Alice
  have ha₀ : ((0 : Fin 1), x₀) ∈ ({((0 : Fin 1), x₀)} : Finset (Fin 1 × X)) :=
    Finset.mem_singleton_self _
  have hone : D (subgame (interlaceFun W 1)
      ({((0 : Fin 1), x₀)} : Finset (Fin 1 × X))
      (Finset.univ : Finset (Fin 1 → Y))) ≤ 1 := by
    refine D_le_one_of_row_independent _ ⟨((0 : Fin 1), x₀), ha₀⟩ ?_
    rintro ⟨a, hA⟩ c
    have ha : a = ((0 : Fin 1), x₀) := Finset.mem_singleton.mp hA
    simp only [subgame]
    rw [ha]
  have hdense := h.dense
  omega

/-- **Battery 2b: the entry point forces a large row carrier, quantitatively.**

Under the frozen first entry gate `4 Q_0 theta <= delta` (`10:53`), the banked
`EntryGates.entryGate_theta_le` caps the row threshold at `theta <= 1/640`; with
Battery 2 that gives `|Rows(W)| > 640` for every matrix entering the bridge at
`C_W >= 2`.

Consumed by pin from `BRIDGE-ENTRY-001`; no gate arithmetic is re-derived.
General in the carriers, the matrix, `C_W`, `b_out`, and the three real
parameters. -/
theorem bridgeEntry_forces_large_row_carrier {X Y : Type*} [Fintype X] [Fintype Y]
    {W : X → Y → Bool} {CW bout : ℕ} {θ δU y : ℝ}
    (hδ0 : 0 ≤ δU) (hX : 1 ≤ Fintype.card X) (hCW : 2 ≤ CW) (hθ0 : 0 < θ)
    (hgate : 4 * EntryGates.Q0 bout δU * θ ≤ EntryGates.deltaFixed)
    (h : CommonThreshold W CW θ δU y) :
    640 < Fintype.card X := by
  have hdense := bridgeEntry_forces_dense_rows hδ0 hX hCW h
  have hθ := EntryGates.entryGate_theta_le hθ0 hgate
  by_contra hcon
  have hcon' : Fintype.card X ≤ 640 := Nat.not_lt.mp hcon
  have hm : (Fintype.card X : ℝ) ≤ 640 := by exact_mod_cast hcon'
  have h1 : (Fintype.card X : ℝ) * θ ≤ 640 * θ :=
    mul_le_mul_of_nonneg_right hm (le_of_lt hθ0)
  have h2 : (640 : ℝ) * θ ≤ 1 := by linarith
  linarith

/-! ## Section 4  The development the opening rules into scope (`10:19--32`) -/

/-- **The two base estimates from the entry point (`10:19--32`).**

From the entry point alone, under `C_W >= 3` (`10:40`) and the legal row
request `4 theta <= 1` (`10:27`), the frozen text derives
`eq:direct-two-copy` and `eq:direct-three-copy`.  Both are landed elsewhere --
`BRIDGE-TWOCOPY-001` and `BRIDGE-THREECOPY-001` -- and are consumed here by pin
through `ThreeCopyRowStep.bridgeBaseEstimates`, fed with the record's `low`
field.  The two-copy guard `2 theta <= 1` of line 19 is *derived* inside that
banked theorem from `4 theta <= 1`, so no hypothesis is added.

What is new is only the wiring: this is the first declaration in `src/` that
takes the Section-9 interface as its input.  General. -/
theorem openingBaseEstimates {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) {θ δU y : ℝ}
    (hCW : 3 ≤ CW) (hθ0 : 0 < θ) (hθ : 4 * θ ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h : CommonThreshold W CW θ δU y) :
    CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)
      ∧ CW + 1 ≤ Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * θ) (y ^ 2)) :=
  ThreeCopyRowStep.bridgeBaseEstimates W CW hCW hθ0 hθ hy0 hy1 h.low

/-- **Battery 3 (`10:26`): the bottom rung is positive in every application.**

"Its bottom rung has complexity at least `C_W - 2`, which is positive in every
application."  Both halves: the `ℕ`-truncated form the display writes, and the
untruncated positivity that `C_W >= 3` buys.  The rung is read off the landed
`eq:direct-two-copy` with the banked `TwoCopyLadder.LambdaGE_le_rungs` at offset
`2`, i.e. at column density `y^2/4`.

This is where the frozen sentence's second half ("positive in every
application") becomes a checked fact rather than a remark, and it is the
hypothesis `ThreeCopyRowStep` needs for its row step.  General. -/
theorem opening_bottom_rung_positive {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) {θ y : ℝ} (hCW : 3 ≤ CW)
    (hTwo : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)) :
    CW - 2 ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * θ) (y ^ 2 / 4))
      ∧ 1 ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * θ) (y ^ 2 / 4)) := by
  have hrung := (TwoCopyLadder.LambdaGE_le_rungs W 2 (2 * θ) (y ^ 2)).2.2
  omega

/-- **Battery 4 (round trip along an entrywise identification).**

`10:4` says all construction-specific information is discarded.  The honest
kernel form of that: the opening's deliverables are statements about the entry
function alone, so they transport along a pointwise equality of matrices.  No
provenance survives into either base estimate.

Stated at the *conclusions* rather than at the input record, so that it is a
fact about this module's deliverable and not a restatement of the banked
`FirstWrapperClose.commonThreshold_congr`.  General. -/
theorem opening_congr {X Y : Type*} [Fintype X] [Fintype Y]
    {W₁ W₂ : X → Y → Bool} {CW : ℕ} {θ y : ℝ} (hW : ∀ a b, W₁ a b = W₂ a b)
    (h : CW ≤ LambdaGE W₁ 2 (2 * θ) (y ^ 2)
      ∧ CW + 1 ≤ Dfamily (interlaceFun W₁ 3) (bracketGE X Y 3 (4 * θ) (y ^ 2))) :
    CW ≤ LambdaGE W₂ 2 (2 * θ) (y ^ 2)
      ∧ CW + 1 ≤ Dfamily (interlaceFun W₂ 3) (bracketGE X Y 3 (4 * θ) (y ^ 2)) := by
  have hfun : W₁ = W₂ := funext fun a => funext fun b => hW a b
  subst hfun
  exact h

/-- **Battery 5 (disclosure): the gate subsumes the binder `theta <= 1`.**

`10:39` states `0 < theta <= 1` as a binder of `thm:direct-robustification`,
and `10:53--60` separately gives `4 theta <= delta/Q_0 < 1`.  The second
implies the first, so the binder is redundant *on the route*.  It is kept as an
explicit hypothesis of `directBridgeOpening` below because the frozen theorem
states it, and the redundancy is recorded here as a theorem rather than hidden
as a comment.  General. -/
theorem entryGate_subsumes_theta_le_one {bout : ℕ} {δU θ : ℝ} (hθ0 : 0 < θ)
    (hgate : 4 * EntryGates.Q0 bout δU * θ ≤ EntryGates.deltaFixed) : θ ≤ 1 := by
  have h := EntryGates.entryGate_row_request_legal bout hgate
  linarith

/-! ## Section 5  The opening theorem -/

/-- **The opening of the direct bridge (`10:4--32` under the binders of
`10:36--41` and `10:53`).**

Hypotheses, in the frozen order the theorem prints them:

* `hCW : 3 <= C_W` (`10:40`);
* `hδ0`, `hδ1` : `0 < delta_U < 1` (`10:38`);
* `hθ0`, `hθ1` : `0 < theta <= 1` (`10:39`) -- the row-threshold legality, kept
  as a binder even though `entryGate_subsumes_theta_le_one` shows the second
  half follows from the gate;
* `hbout : 1 <= b_out` (`10:41`);
* `hy0`, `hy1` : the range of `y`; the route's own value is `yFixed = 3/5`
  (`10:36--37`), and generality here asserts no other value;
* `hX : 1 <= |Rows(W)|` -- the row-carrier nonemptiness fact, carried
  explicitly rather than assumed away;
* `hgate` : the **first** half of `eq:direct-entry-gates` (`10:53`),
  `4 Q_0 theta <= delta`;
* `h` : the entry point itself, the banked `CommonThreshold` -- `W`, `C_W`, and
  the two common-threshold lower bounds, and nothing else.

Conclusions, in frozen print order:

1. `comp W = C_W` (`10:5`);
2. `Lambda_3(W,2,2theta,y^2) >= C_W`, i.e. `eq:direct-two-copy` (`10:23`);
3. `comp<W,3,4theta,y^2> >= C_W + 1`, i.e. `eq:direct-three-copy` (`10:30`);
4. the positive bottom rung of `10:26`;
5. `16 < Q_0`, the nondegenerate form of the `Q_0 >= 16` that the legality
   sentence `10:58` invokes by name;
6. the one-copy bracket family of `eq:direct-input` is **nonempty**, so the
   first clause of `10:8` is not a vacuous statement about an empty family
   (where `Dfamily` would collapse to `sInf` of the empty set);
7. `640 < |Rows(W)|` -- the carrier lower bound of
   `bridgeEntry_forces_large_row_carrier`.

Every binder is used: `hδ0`, `hδ1`, `hbout` by conclusion 5; `hθ1` and `hX` by
conclusion 6; `hθ0`, `hgate`, `hCW` by conclusion 7.

**None of `thm:direct-robustification`'s own conclusions appears here** (see
GAP-EXPOSED G1): `R^+`, `eq:direct-output`, and the selector sentence are not
stated.  This theorem is the opening only, and no route completion is claimed. -/
theorem directBridgeOpening {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW bout : ℕ) {θ δU y : ℝ}
    (hCW : 3 ≤ CW) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hbout : 1 ≤ bout)
    (hy0 : 0 < y) (hy1 : y ≤ 1) (hX : 1 ≤ Fintype.card X)
    (hgate : 4 * EntryGates.Q0 bout δU * θ ≤ EntryGates.deltaFixed)
    (h : CommonThreshold W CW θ δU y) :
    D W = CW
      ∧ CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2)
      ∧ CW + 1 ≤ Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * θ) (y ^ 2))
      ∧ 1 ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * θ) (y ^ 2 / 4))
      ∧ (16 : ℝ) < EntryGates.Q0 bout δU
      ∧ (bracketGE X Y 1 θ (1 - δU)).Nonempty
      ∧ 640 < Fintype.card X := by
  classical
  haveI : DecidableEq X := Classical.decEq _
  have hθ4 : 4 * θ ≤ 1 := EntryGates.entryGate_row_request_legal bout hgate
  obtain ⟨hTwo, hThree⟩ := openingBaseEstimates W CW hCW hθ0 hθ4 hy0 hy1 h
  exact ⟨h.exact, hTwo, hThree,
    (opening_bottom_rung_positive W CW hCW hTwo).2,
    EntryGates.Q0_gt_sixteen_of_route hbout hδ0 hδ1,
    NPCC.bracketGE.nonempty (X := X) (Y := Y) 1 θ (1 - δU) hθ1 (by linarith) hX,
    bridgeEntry_forces_large_row_carrier (le_of_lt hδ0) hX (by omega) hθ0 hgate h⟩

/-! ## Section 6  Statement poles -/

/-- **Statement pole (the trivial witness fails the deliverable).**

`eq:direct-three-copy` asks for a *positive* family complexity, `C_W + 1`, and
the trivial witness -- a constant matrix -- supplies `0`: the full bracket
member exists whenever `4 theta <= 1`, `y^2 <= 1` and the row carrier is
nonempty, and its induced subgame is constant.  So the opening's second
deliverable is refuted at the degenerate object for **every** `C_W`, including
`C_W = 0`, and the conclusion is not met by an object that carries no content.

Consumed by pin: `NPCC.bracketGE.nonempty`, `HardSeedFacade.Dfamily_le_of_mem`,
`PublicRecords.D_const`.  General in the carriers, the constant, and `C_W`. -/
theorem directThreeCopy_fails_for_constant {X Y : Type*} [Fintype X] [Fintype Y]
    (b : Bool) (CW : ℕ) {θ y : ℝ} (hθ : 4 * θ ≤ 1) (hy : y ^ 2 ≤ 1)
    (hX : 1 ≤ Fintype.card X) :
    ¬ (CW + 1 ≤ Dfamily (interlaceFun (fun (_ : X) (_ : Y) => b) 3)
        (bracketGE X Y 3 (4 * θ) (y ^ 2))) := by
  classical
  haveI : DecidableEq X := Classical.decEq _
  obtain ⟨RC, hRC⟩ :=
    NPCC.bracketGE.nonempty (X := X) (Y := Y) 3 (4 * θ) (y ^ 2) hθ hy hX
  have hle := HardSeedFacade.Dfamily_le_of_mem
    (interlaceFun (fun (_ : X) (_ : Y) => b) 3) _ hRC
  have hconst : subgame (interlaceFun (fun (_ : X) (_ : Y) => b) 3) RC.1 RC.2
      = fun _ _ => b := rfl
  rw [hconst, PublicRecords.D_const] at hle
  omega

/-- **Statement pole (the Section-9 NON-FIDELITY probe cannot enter the
bridge).**

`FIRST-WRAPPER-CLOSE-001` inhabits its interface synthetically with the
two-by-two exchange game at `C_W = 2`, explicitly labelled NON-FIDELITY there.
That probe is **not** available as a stand-in here, at any densities: the
opening demands `3 <= C_W` (`10:40`) while `FirstWrapperClose.probeW_D` pins the
probe's complexity at exactly `2`.

Together with `bridgeEntry_forces_dense_rows` -- which rules out *every* small
row carrier under the route's tiny `theta` -- this is why the canonical
inhabitation below is deferred rather than replaced by a probe. -/
theorem opening_rejects_the_wrapper_close_probe (CW : ℕ) (θ δU y : ℝ)
    (hCW : 3 ≤ CW) : ¬ CommonThreshold FirstWrapperClose.probeW CW θ δU y := by
  intro h
  have hx := h.exact
  rw [FirstWrapperClose.probeW_D] at hx
  omega

/-- **Non-vacuity of the parameter binders (arithmetic only).**

The binder list `10:38--41` together with the first entry gate `10:53` is
satisfiable at legal, nondegenerate values: `b_out = 1`, `delta_U = 1/60`,
`theta = 1/192000`, `y = 3/5 = yFixed`.  Every value is strictly inside the
frozen ranges, the gate is tight, and `Q_0 = 4800` sits far above its constant
branch.

The witness is **not** self-chosen: it is the banked
`EntryGates.directEntryGates_fires`, the non-vacuity point that
`BRIDGE-ENTRY-001` already carries for `eq:direct-entry-gates`, consumed by
pin.  This theorem is about the **parameters only** and exhibits no matrix; it
is therefore not, and does not pretend to be, an inhabitation of the entry
point.  See the registered deferred obligation in the module header. -/
theorem opening_entry_parameters_are_satisfiable :
    (0 : ℝ) < 1 / 60 ∧ (1 / 60 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 192000
      ∧ (1 / 192000 : ℝ) ≤ 1 ∧ 1 ≤ (1 : ℕ) ∧ 0 < yFixed ∧ yFixed ≤ 1
      ∧ 4 * EntryGates.Q0 1 (1 / 60) * (1 / 192000 : ℝ) ≤ EntryGates.deltaFixed
      ∧ (16 : ℝ) < EntryGates.Q0 1 (1 / 60) := by
  obtain ⟨⟨hgate, -⟩, -, -, -, h16, -, -⟩ := EntryGates.directEntryGates_fires
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_rfl,
    yFixed_mem.1, yFixed_mem.2, hgate, h16⟩

/-! ## Section 7  Canonical inhabitation of the entry point, deferred

Read the module header's registered obligation before consuming this section.
The paper's own instance is the required witness, and it is delivered here
**conditionally**, exactly as its supplier delivers it. -/

/-- **Canonical inhabitation: the paper's own entry object (`09:1794--1804`
into `10:4--12`).**

The only object the paper ever hands to this bridge is the Section-9 output
`W = ^T U` at `C_W = C + r`.  This theorem runs the opening on that object: its
hypotheses are exactly the banked
`FirstWrapperClose.commonThreshold_of_firstWrapperClose`'s, plus the two
Section-10 binders the opening needs (`b_out >= 1` and the first entry gate),
and its conclusion is verbatim `directBridgeOpening`'s at
`ScaleAlignOpening.wrapperW Nmat r` and `C + r`.

**Conditional, and registered as such.**  `hDense` is the named, undischarged
`FirstWrapperClose.DenseRung` -- `eq:wrapper-u-dense` (`09:262--263`) -- and
`hne`, `hmem` are the low-rung inputs of `09:274--334`.  The unconditional form
is GAP-EXPOSED G3 and is discharged only when `DenseRung` is proved.  Nothing
here weakens, discharges, or reorients that binder, and **no route completion is
claimed**. -/
theorem opening_at_the_paper_instance {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Nmat : Rw → Cl → Bool) (r C bout : ℕ) {δU θ y : ℝ}
    (hC : 3 ≤ C) (hN : D Nmat = C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) (hbout : 1 ≤ bout)
    (hRw : 1 ≤ Fintype.card Rw) (hCl : 1 ≤ Fintype.card Cl)
    (hgate : 4 * EntryGates.Q0 bout δU * θ ≤ EntryGates.deltaFixed)
    (hDense : FirstWrapperClose.DenseRung Nmat r C δU θ)
    (hne : ∀ j : ℕ, j ≤ 2 →
      (bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ).Nonempty)
    (hmem : ∀ j : ℕ, j ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (y / 2 ^ j) θ,
        C + r ≤ j + 1 + D (subgame
          (interlaceFun (ScaleAlignOpening.wrapperU Nmat r) 1) RC.1 RC.2)) :
    D (ScaleAlignOpening.wrapperW Nmat r) = C + r
      ∧ C + r ≤ LambdaGE (ScaleAlignOpening.wrapperW Nmat r) 2 (2 * θ) (y ^ 2)
      ∧ C + r + 1 ≤ Dfamily (interlaceFun (ScaleAlignOpening.wrapperW Nmat r) 3)
          (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 3 (4 * θ) (y ^ 2))
      ∧ 1 ≤ Dfamily (interlaceFun (ScaleAlignOpening.wrapperW Nmat r) 2)
          (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 2 (2 * θ) (y ^ 2 / 4))
      ∧ (16 : ℝ) < EntryGates.Q0 bout δU
      ∧ (bracketGE (Fin (2 ^ r) → Cl) (Fin (2 ^ r) × Rw) 1 θ (1 - δU)).Nonempty
      ∧ 640 < Fintype.card (Fin (2 ^ r) → Cl) := by
  classical
  have hIn : CommonThreshold (ScaleAlignOpening.wrapperW Nmat r) (C + r) θ δU y :=
    FirstWrapperClose.commonThreshold_of_firstWrapperClose Nmat r C hC hN hθ0 hθ1
      (by linarith) (by linarith) hy0 hy1 hRw hCl hDense hne hmem
  have hne' : Nonempty Cl := Fintype.card_pos_iff.mp (by omega)
  have hX : 1 ≤ Fintype.card (Fin (2 ^ r) → Cl) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Classical.choice hne'⟩
  exact directBridgeOpening _ (C + r) bout (by omega) hδ0 hδ1 hθ0 hθ1 hbout
    hy0 hy1 hX hgate hIn

end EthInapproximability.ParameterizedNP.DirectBridgeOpening
