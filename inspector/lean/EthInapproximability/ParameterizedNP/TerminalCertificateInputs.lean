import EthInapproximability.ParameterizedNP.Stage3ProtocolRouting

/-!
# Parameterized NP route: the terminal phase-1 certificate inputs

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, opened first-hand this
  round.  The tranche traces, in the order the blocking list names them:

  * **(T1)** `09:943--948` -- the **one-copy residual certificate**: "At any such
    node, project to the coordinate carried by an ordinary token and transpose
    the resulting local block.  Its surviving `C_1`-support is the row
    restriction of `M = M_1^T`, and the retained typed projection is its column
    restriction.  Both have the thresholds in `eq:stage1-robust-certificate`, so
    one-copy robustness gives residual complexity `B_cap`."
  * **(T1)** `09:949--950` -- the **top two-copy rung**: "an unsplit attached pair
    there has residual complexity `B_cap + 1` by the inherited top two-copy
    rung."
  * **(T2)** `09:1076--1078` -- the **fibre-set invariance**: "Until the first Bob
    query, these Alice restrictions do not change the ordinary and foreign fibre
    sets `O_alpha, F_alpha`, so the averages `eq:terminal-averages` are
    unchanged."
  * **(T3)** `09:937--938` and `09:1084--1085` -- **coordinate isolation as a
    construction**: "Stop a token at the first Alice query or when its Stage-2
    coordinate is isolated" and "Stop each routed object immediately before its
    first Bob query or when its Stage-3 outer block is isolated", whose *test* is
    the frozen `08:982--983` "At a coordinate-isolation node, every other
    coordinate fibre is empty."

* **Cross-anchors opened first-hand for this tranche.**
  * `07:190--215` -- `eq:stage1-robust-certificate` itself,
    `Lambda_{M_1^T}(1, 2^{-b_1}, 3/5) >= B_cap`, with `07:214--215` ("Here `b_1`
    is the integer fixed in `eq:stage1-scales`; no later step changes it").
  * `09:836--859` -- `eq:terminal-entry` and `eq:terminal-seed-inputs`, which is
    where the two thresholds `x = 2^{-b_1}` and `y` enter the terminal lemma's
    binder set; `09:854--855` pins `S_2 = M_2^T` and `D_2 = B_cap + log_2 q_2`.
  * `09:471--480` -- the frozen `M = M_1^T`, `comp M = B_cap`, `x = 2^{-b_1}`,
    `lambda_0 = 2 q_2 x`.
  * `09:482--656` -- `def:two-stream-state`, in particular clause (i)'s
    `O_alpha, F_alpha, r_alpha, f_alpha` (`09:510--546`), clause (iv)'s selector
    data `R_p`, `K_ord` (`09:609--632`), and the bin readout
    `rho_p(c) = j(p) in J_2 = [q_2] x C_1` of `09:512--516`.
  * `09:862--900` -- `eq:terminal-averages` (label `09:878`) and the counting it
    feeds.
  * `09:937--942` -- the ladder floor `lambda_d >= lambda_{r_2} = 2^{1-b_1}`,
    which is the *row density* the two-copy rung consumes.
  * `09:1004--1012` -- "Following the denser Alice child leaves typed density at
    least `49/128 > 9/25`", which is the *column density* `z^2 = (3/5)^2` the
    same rung consumes.
  * `09:1039--1044` -- the Stage-3 selector orientation: "Alice owns the `s`
    outer row blocks of `interlace(S_2, s)`, while Bob owns its product
    columns", and "the ordinary column set remains unchanged until the first Bob
    query".
  * `08:946--1015` -- `lem:dense-no-leaf`, the frontier classification
    `08:981--985`, and `eq:isolation-capacity`.
  * `03:384--390` -- the inherited-contracts row *Two-copy and odd-copy bounds*,
    which names `lem:two-copy-ladder` and `cor:robust-two-copy-ladder` and whose
    `03:388` reads "The two-copy rung sends `(H,x,z)` to `(H+1,2x,z^2)`".  That
    row is what makes the rung of `09:950` **inherited**, and it is the frozen
    identification of the rung this module reads at the top.
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and occurs in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively; the sole import is `Stage3ProtocolRouting`,
  whose ledger row records the same exclusion.  No axiom, no opaque
  conclusion-bearing certificate, and no compiler-trusted decision procedure
  beyond closed `decide`/`norm_num` evaluations that go through the kernel.

## What this tranche closes, and in which banked row

`Stage3ProtocolRouting.lean`'s **GAP-EXPOSED 1** ("what remains for phase 1 are
the *certificate* inputs -- the one-copy and top two-copy residual readings at a
node ... carried here as **explicit binders**") and `TerminalStageThreeLift.lean`'s
**GAP-EXPOSED 7** ("The fibre-set invariance of `09:1076--1078` is not
transcribed") name two of the three items below; the third is the coordinate
isolation that `Stage3ProtocolRouting`'s own GAP-EXPOSED 3 and
`DenseWeightedCount`'s coverage limit 4 both leave as a named predicate.

**Landed.**

1. **The bracket entry point (`07:209--213` read at a node).**
   `mem_bracketGE_of_floors` turns the two frozen thresholds -- a per-copy row
   floor and a column floor -- into membership of the vendored
   `NPCC.bracketGE`, and `LambdaGE_le_member` reads the inherited `Lambda` bound
   off at that member.  Both are compositions of banked facts
   (`HardSeedFacade.row_floor_of_density`, `HardSeedFacade.Dfamily_le_of_mem`,
   `TerminalTwoStream.LambdaGE_le_Dfamily`); nothing about brackets is
   re-proved.
2. **The one-copy residual certificate `09:943--948`, PROVED.**
   `liftRows` is the frozen "project to the coordinate carried by an ordinary
   token and transpose the resulting local block": the surviving `C_1`-support
   *is* the one-copy row set, so it is **constructed** from the support and is
   not a free field.  `oneCopy_residual_at_seed_floor` then derives
   `B_cap <= D(local block)` from `eq:terminal-seed-inputs` alone.  This is the
   binder `honeCopy` of `Stage3ProtocolRouting.stage2_routed_token_frontier`,
   now a theorem.
3. **The top two-copy rung `09:949--950`, PROVED.**  `topTwoCopy_rung` is the
   `ell = 1` instance of the banked `lem:certified-row-ladder` at the frozen
   `(H, x, z) = (B_cap, 2^{-b_1}, 3/5)`, i.e. exactly the `03:388` rung
   `(H,x,z) -> (H+1, 2x, z^2)`.  Its output row density `2 * 2^{-b_1}` is the
   frozen ladder floor `lambda_{r_2} = 2^{1-b_1}` of `09:941`
   (`two_mul_xSeed_eq_lambdaAt_frontier`) and its output column density `(3/5)^2 = 9/25`
   is the frozen post-Alice guard of `09:1011` -- the two coincidences that
   identify this rung as the one the frozen sentence calls "inherited top".
   `topTwoCopy_residual_at_pair_floor` reads it off at the two labelled fibres,
   which is the binder `hpair` of `Stage3ProtocolRouting`, now a theorem.
4. **The two t4k discharges.**  `stage2_routed_token_frontier_at_certificates`
   and `stage2_isolation_capacity_at_certificates` re-run the banked frontier and
   isolation-capacity conclusions with `honeCopy` and `hpair` **supplied**, not
   assumed.  What remains a binder in both is the *residual* comparison
   `D(node game) <= (descend P p).cost`, which is protocol bookkeeping and not a
   certificate; it is named at every use site.
5. **The fibre-set invariance of `09:1076--1078`, PROVED (TSL GAP-EXPOSED 7).**
   `binImage` is the frozen bin readout `rho_p(c) = j(p)` of `09:512--516` on
   selector column tuples, `kordAt` is the frozen "joint ordinary column set" at
   a protocol node (`09:1085`), and `fibreAt` is `O_alpha`/`F_alpha` read there.
   `alice_query_preserves_fibreAt` is the frozen invariance across one Alice
   query, `alice_query_preserves_meanFibreDensity` is the frozen "so the averages
   `eq:terminal-averages` are unchanged", and
   `fibres_unchanged_until_first_bob` is the whole-prefix form, i.e. the frozen
   "Until the first Bob query".  The helper `bobCols_append` is new here and is
   the exact dual of the banked `Stage3ProtocolRouting.aliceCols_append`.
6. **Coordinate isolation as a construction (`08:982--983`).**  `IsolatedAt` is
   the frozen test ("every other coordinate fibre is empty"), decidable at every
   finite coordinate type; `card_liveCoords_le_one_of_isolationNode` is the
   frozen `08:1004--1005` "an isolation node contains at most one routed object",
   i.e. the `huniq` premise the banked `eq:isolation-capacity` carries as a
   hypothesis, now **derived from the isolation test**.  The classification with
   its tie-break is the banked `DenseWeightedCount.frontierClass`, consumed by
   pin at `iso := IsIsolationNode . fib`; no second classification is defined.

**Deliberately open (GAP-EXPOSED).**

1. **`eq:terminal-fixed-bin` is still not proved, and neither is `StageThreeLift`.**
   Nothing below concludes either.  What this tranche removes is the *certificate*
   half of `Stage3ProtocolRouting`'s GAP-EXPOSED 1; the residual comparisons and
   the Localized Extension corollary's conclusion `eq:certified-E3` remain
   exactly as that module records them, and `eq:certified-E3` is asserted
   nowhere here.
2. **The two Extension preconditions named in `Stage3ProtocolRouting`'s
   GAP-EXPOSED 2 are still not modelled** -- the ordinary-token support floor
   `2 kappa_v 2^{-b_1}` of `09:1005--1006` and the trimming step of `09:1015` --
   and nothing below assumes them.  This module supplies the *seed*-floor and
   *pair*-floor trims of `09:941`, which are a different pair of thresholds.
3. **The identification of the state's stream images with the selector column
   carrier is a binder, not a theorem.**  `09:628--630` says the witness
   "includes the actual row and column sections", but the frozen text nowhere
   displays an equation between `rho_{p}(omega(selCol k))` and `k(p)`.  So
   `terminal_averages_unchanged_until_first_bob` carries that identification as
   the two explicit hypotheses `hpresOrd`, `hpresFor`, and it is asserted nowhere.
   The invariance statements of item 5 above are unconditional; only the
   *transport to the record's own fields* uses the binders.
4. **No frontier-wide counting is claimed.**  `eq:frontier-conservation` and
   Kraft's inequality stay with `DenseFrontierConservation` /
   `FrontierIndexing`, consumed by pin.
5. **`sec:wrapper-projection-covers` is untouched.**  This block neither
   discharges nor feeds `hDenseRung`; the ranges `09:1184--1366`,
   `09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED exactly as
   `ScaleAlignOpening` records them, and **no route completion is claimed**.

## Consumed by pin (never restated)

* `NPCC`: `LambdaGE`, `Dfamily`, `bracketGE`, `IsEquipartitionedGE`, `subgame`.
  `Workspace.Types.Interlace`: `interlaceFun`.
  `Workspace.Types.CommComplexity`: `D`.
* `HardSeedFacade`: `row_floor_of_density`, `Dfamily_le_of_mem`.
* `TerminalTwoStream`: `LambdaGE_le_Dfamily`, `certifiedRowLadder_of_base`,
  `CertifiedRowLadder`, `lambdaAt_stage2_frontier`, `post_alice_density_gt`,
  `probeWidths`.
* `StageOneInterlace`: `xSeed`, `xSeed_pos`, `xSeed_le_one`.
* `DenseRoutingThresholds`: `xSeed_eq_inv_pow`, `lambdaAt`.
* `DenseRoutingInvariant`: `routingFloor`.
* `DenseWeightedCount`: `seedFloor`, `two_mul_xSeed_le_lambdaAt_of_le`,
  `StoppedToken`, `StopEvent`, `descend`, `descend_cons`, `descendStep`,
  `IsQueryPath`, `IsBobNode`, `stoppingCapacity`, `frontierClass`,
  `frontierClass_isolation_iff`, `frontierClass_isolation_of_both`,
  `isolationNodes`, `aliceNodes`, `frontier_disjoint`, `frontier_union`.
* `DenseBranchSelection`: `Dtwo`.
* `DenseSynchronisation`: `IsANode`.
* `RoutedCertificateSystem`: `IsAlicePath`, `bobCols`, `bobCols_cons`,
  `bobConstraint`, `bobConstraint_of_isANode`, `retainedCols`,
  `retainedCols_of_isAlicePath`, `retainedCols_subset`, `bobCappedLadder`,
  `bobCols_pole_at_bob_query`.
* `Stage3ProtocolRouting`: `stage2_routed_token_frontier`,
  `stage2_unsplit_pair_capacity_two`, `stage2_isolation_capacity_from_protocol`.
* `TwoStreamState`: `colFibre`, `mem_colFibre`, `fibreDensity`,
  `meanFibreDensity`, `streamImage`, and the record `TwoStreamState` with its
  fields `pOrd`, `pFor`, `iOrd`, `iFor`, `Rfor`, `Kord`, `ordinary_density`,
  `foreign_density`.

## Canonical inhabitation

The frozen argument is an **adversary argument against an arbitrary protocol**
(`09:918--919`, `09:1037`), so every protocol-side declaration below is
universally quantified over the alleged protocol and the paper's object is
covered by construction.  Likewise, every certificate theorem of SS3--SS4 is
proved at **every** matrix satisfying `eq:terminal-seed-inputs`, hence at the
paper's `M = M_1^T`; and every fibre statement of SS6 is proved at **every**
`TwoStreamState`, hence at the paper's state.

Two carriers are introduced: `liftRows`/`pairRows` (defs over a support, not
structures) and `IsolatedAt`/`IsIsolationNode` (a predicate on a fibre
assignment, not a structure).  Neither is a premise bundle and neither restates a
derived telescope.

The **deferred canonical-inhabitation obligation** this tranche registers is on
the *node data* of the frozen adversary argument: the paper never constructs the
protocol whose nodes carry the local blocks, so the concrete evaluations
`liftRows_probe_is_nondegenerate`, `pairRows_probe_is_nondegenerate`,
`isolation_probe_fires` and `isolation_probe_rejects_two_live_fibres` are
labelled **NON-FIDELITY** (they audit our encoding at points the frozen paper
never visits) and are never evidence that the terminal regime is inhabited.  The
obligation is discharged when phase 1 becomes provable, never by these probes.

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, opened first-hand
this round.  **No declaration below claims a reader item.**  The reader's account
of the three items formalized here is unnumbered prose in three places:
**A:256--265** ("Quotient-support routing follows every Bob query; the weighted
stopping count records coordinate isolation, the first Alice query, and premature
leaves.  Classify each stopping node as either an Alice node or a
coordinate-isolation node, giving priority to isolation if both descriptions
apply"), **A:380--383** ("realizes the ordinary stream in one copy and the tagged
ordinary--protected pair in two copies"), and **A:387--390**, which
`TERMINAL-FIXED-BIN-001` already records as unclaimed prose.  The
reader-counterpart discipline bars citing prose as a statement counterpart, so
nothing is claimed and no reader item is assigned twice; A:256--265 and
A:380--383 are recorded here as unclaimed prose and were cited by no previous
module.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the bracket entry point, general (2): `mem_bracketGE_of_floors`,
  `LambdaGE_le_member`.
* `B` the one-copy lift of a support, general (4): `liftRows_card`,
  `liftRows_fibre`, `liftRows_fibre_card`, `oneCopy_residual_at_seed_floor`.
* `C` the pair lift and the top two-copy rung, general (6):
  `pairRows_fibre_zero`, `pairRows_fibre_one`, `two_mul_xSeed_eq_lambdaAt_frontier`,
  `pairFloor_le_routingFloor`, `topTwoCopy_rung`,
  `topTwoCopy_residual_at_pair_floor`.
* `D` the two t4k discharges, general (2):
  `stage2_routed_token_frontier_at_certificates`,
  `stage2_isolation_capacity_at_certificates`.
* `E` the fibre layer and its invariance, general (7): `bobCols_append`,
  `alice_query_preserves_bobCols`, `alice_query_preserves_kordAt`,
  `alice_query_preserves_fibreAt`, `alice_query_preserves_meanFibreDensity`,
  `fibres_unchanged_until_first_bob`,
  `terminal_averages_unchanged_until_first_bob`.
* `F` coordinate isolation, general (5): `mem_liveCoords`,
  `liveCoords_subset_of_isolatedAt`, `card_liveCoords_le_one_of_isolationNode`,
  `isolationNode_of_card_liveCoords_le_one`, `isolatedAt_unique`.

That is **26 general battery entries proved**, with `0` unproved, alongside
**three statement poles** (`bracket_entry_needs_the_column_floor`,
`fibre_invariance_needs_the_alice_node`, `isolation_test_is_not_free`), **four
NON-FIDELITY readouts** (`liftRows_probe_is_nondegenerate`,
`pairRows_probe_is_nondegenerate`, `isolation_probe_fires`,
`isolation_probe_rejects_two_live_fibres`), **two consistency readouts**
(`topTwoCopy_hypotheses_consistent`, `certificate_floors_are_satisfiable`) and
**one banked composition** (`frontier_classification_at_isolation_test`).  The
module has **49 declarations** in total: 36 theorems, 11 `def`s and 2
`instance`s.

## HYPOTHESIS-CONSISTENCY note

Every theorem below is an implication.  The one bundle that could be
inconsistent is the triple `(hseed, hH, hlegal)` of `topTwoCopy_rung`: it demands
`2 <= B_cap`, `2 * 2^{-b_1} <= 1` and the Stage-1 certificate at `y = 3/5`
simultaneously.  `topTwoCopy_hypotheses_consistent` covers exactly the *scale*
clause and the column pins: it exhibits `b_1 = 24` (the banked
`TerminalTwoStream.probeWidths.b₁`) satisfying `2 * 2^{-b_1} <= 1` together with
`(3/5)^2 = 9/25 < 49/128`.  The two clauses it does **not** exhibit are named
here rather than glossed.  `hH : 2 <= B_cap` is not exhibited because `B_cap` is
universally quantified and occurs in no other arithmetic clause of the bundle, so
it can conflict with nothing; `hseed` is not exhibited because it is an inherited
Stage-1 conclusion and is not re-derived.

The frozen thresholds are never conjoined across cases: `09:943--948` and
`09:949--950` are the *ordinary* and the *unsplit pair* readings of one node and
are landed as two separate theorems with different copy counts (`1` and `2`),
different row densities (`2^{-b_1}` and `2^{1-b_1}`) and different column
densities (`y` and `y^2`), exactly as the frozen text prints them.
-/

namespace EthInapproximability.ParameterizedNP.TerminalCertificateInputs

open Finset
open NPCC
open Workspace.Types.Protocol
open Workspace.Types.CommComplexity
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.FiniteSlots

/-! ## §1  The bracket entry point (`07:209--213`, read at a node)

`eq:stage1-robust-certificate` is a bound on `Lambda_{M_1^T}(1, 2^{-b_1}, 3/5)`,
and `Lambda` is a minimum over the bracket family.  So to read a residual bound
off *one* local block, one exhibits that block as a bracket member.  The two
steps are banked; this section composes them and adds nothing. -/

section BracketEntry

variable {Xc Yc : Type*} [Fintype Xc] [Fintype Yc]

/-- **Aux A1 (`def:bracket-ge` at the two frozen thresholds).**  Extraction data
whose every copy fibre carries at least `|X| x` rows and whose column set carries
at least `ceil(|Y|^p y)` columns is a member of the bracket family.  The row half
is the banked `HardSeedFacade.row_floor_of_density`; the column half is the
frozen ceiling itself.  General in the carriers, the copy count and both
densities. -/
theorem mem_bracketGE_of_floors {p : ℕ} {x y : ℝ}
    {R : Finset (Slot p × Xc)} {C : Finset (Slot p → Yc)}
    (hrow : ∀ i : Slot p,
      (Fintype.card Xc : ℝ) * x ≤ ((R.filter fun r => r.1 = i).card : ℝ))
    (hcol : ⌈((Fintype.card Yc : ℝ) ^ p) * y⌉₊ ≤ C.card) :
    ((R, C) : Finset (Slot p × Xc) × Finset (Slot p → Yc)) ∈ bracketGE Xc Yc p x y :=
  ⟨HardSeedFacade.row_floor_of_density hrow, hcol⟩

/-- **Aux A2 (`Lambda` bounds every member).**  The three-rung minimum is at most
its first rung, which is the family infimum, which is at most the complexity of
any member.  Both steps are banked (`TerminalTwoStream.LambdaGE_le_Dfamily`,
`HardSeedFacade.Dfamily_le_of_mem`).  General. -/
theorem LambdaGE_le_member {M : Xc → Yc → Bool} {p : ℕ} {x y : ℝ}
    {RC : Finset (Slot p × Xc) × Finset (Slot p → Yc)}
    (h : RC ∈ bracketGE Xc Yc p x y) :
    LambdaGE M p x y ≤ D (subgame (interlaceFun M p) RC.1 RC.2) :=
  le_trans (TerminalTwoStream.LambdaGE_le_Dfamily M p x y)
    (HardSeedFacade.Dfamily_le_of_mem _ _ h)

/-- **Statement pole 1 (the column floor is load-bearing).**  Without it the
entry point would be false: at any nonempty column type the *empty* column set
meets no positive column ceiling, yet it satisfies every row condition, and the
resulting "block" would carry no complexity at all.  The readout is the frozen
ceiling's own arithmetic: `ceil(|Y|^p y) > 0` whenever `y > 0` and `|Y| >= 1`, so
`empty` is excluded by exactly the hypothesis `hcol`. -/
theorem bracket_entry_needs_the_column_floor {p : ℕ} {y : ℝ} (hy : 0 < y)
    (hY : 1 ≤ Fintype.card Yc) :
    ¬ (⌈((Fintype.card Yc : ℝ) ^ p) * y⌉₊ ≤ (∅ : Finset (Slot p → Yc)).card) := by
  have hYR : (1 : ℝ) ≤ (Fintype.card Yc : ℝ) := by exact_mod_cast hY
  have hpow : (1 : ℝ) ≤ (Fintype.card Yc : ℝ) ^ p := one_le_pow₀ hYR
  have hpos : (0 : ℝ) < ((Fintype.card Yc : ℝ) ^ p) * y := by nlinarith
  have := Nat.ceil_pos.mpr hpos
  simp only [Finset.card_empty]
  omega

end BracketEntry

/-! ## §2  The one-copy lift of a surviving support (`09:943--946`)

"At any such node, project to the coordinate carried by an ordinary token and
transpose the resulting local block.  Its surviving `C_1`-support is the row
restriction of `M = M_1^T`."

The frozen sentence identifies the local block's **row set** with the token's
surviving support.  So the row set is *constructed* from the support here and is
never a free datum: `liftRows` places the support in the single copy slot of the
one-fold interlace. -/

section OneCopyLift

variable {Cone : Type*} [DecidableEq Cone]

/-- **`09:943--945`.**  The surviving `C_1`-support, read as the row set of the
one-fold interlace of `M = M_1^T`.  There is exactly one copy slot, so the map is
the frozen "project to the coordinate carried by an ordinary token". -/
def liftRows (T : Finset Cone) : Finset (Slot 1 × Cone) :=
  T.image (fun γ => ((0 : Slot 1), γ))

/-- **Aux B1.**  Lifting neither loses nor duplicates support.  General. -/
theorem liftRows_card (T : Finset Cone) : (liftRows T).card = T.card := by
  unfold liftRows
  refine Finset.card_image_of_injective _ ?_
  intro a b hab
  exact (Prod.mk.injEq _ _ _ _ ▸ hab).2

/-- **Aux B2.**  The single copy fibre of the lift is the lift itself: a `Slot 1`
index has nowhere else to be.  General. -/
theorem liftRows_fibre (T : Finset Cone) (i : Slot 1) :
    (liftRows T).filter (fun r => r.1 = i) = liftRows T := by
  refine Finset.filter_true_of_mem ?_
  intro r hr
  obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hr
  exact Subsingleton.elim _ _

/-- **Aux B3.**  Hence the frozen row floor at the single copy is the support's
own cardinality.  General. -/
theorem liftRows_fibre_card (T : Finset Cone) (i : Slot 1) :
    ((liftRows T).filter (fun r => r.1 = i)).card = T.card := by
  rw [liftRows_fibre, liftRows_card]

end OneCopyLift

/-! ## §3  The one-copy residual certificate (`09:943--948`)

"Both have the thresholds in `eq:stage1-robust-certificate`, so one-copy
robustness gives residual complexity `B_cap`."

The Stage-1 certificate enters as the first clause of the banked
`TerminalTwoStream.terminalSeedInputs` (`eq:terminal-seed-inputs`, `09:846--853`),
which is where `lem:terminal-two-stream` carries it; this module reads it, never
re-derives it. -/

section OneCopyCertificate

variable {Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone] [Fintype Rone]

/-- **`09:943--948`, PROVED.**  At a node whose surviving `C_1`-support meets the
banked seed floor `ceil(2^{-b_1}|C_1|)` and whose retained typed projection meets
the frozen column ceiling at `y`, the local block of `M = M_1^T` has complexity
at least `B_cap`.

`hseed` is the first clause of `eq:terminal-seed-inputs`, i.e.
`eq:stage1-robust-certificate` as the terminal lemma carries it; it is an
inherited Stage-1 conclusion and is **not** re-derived here.  The row hypothesis
is exactly the output of the banked trimming step
`DenseWeightedCount.trim_to_seed_floor`, so this theorem plugs directly into the
routing.  General in both carriers, in `b_1`, in `B_cap` and in `y`. -/
theorem oneCopy_residual_at_seed_floor (M1T : Cone → Rone → Bool) {b₁ bcap : ℕ}
    {y : ℝ} (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) y)
    {T : Finset Cone} (hrow : DenseWeightedCount.seedFloor Cone b₁ ≤ T.card)
    {C : Finset (Slot 1 → Rone)}
    (hcol : ⌈((Fintype.card Rone : ℝ) ^ 1) * y⌉₊ ≤ C.card) :
    bcap ≤ D (subgame (interlaceFun M1T 1) (liftRows T) C) := by
  have hfloor : StageOneInterlace.xSeed b₁ * (Fintype.card Cone : ℝ) ≤ (T.card : ℝ) := by
    refine le_trans (DenseWeightedCount.seedFloor_le Cone b₁) ?_
    exact_mod_cast hrow
  have hmem : ((liftRows T, C) : Finset (Slot 1 × Cone) × Finset (Slot 1 → Rone))
      ∈ bracketGE Cone Rone 1 (StageOneInterlace.xSeed b₁) y := by
    refine mem_bracketGE_of_floors (fun i => ?_) hcol
    rw [liftRows_fibre_card T i]
    calc (Fintype.card Cone : ℝ) * StageOneInterlace.xSeed b₁
        = StageOneInterlace.xSeed b₁ * (Fintype.card Cone : ℝ) := by ring
      _ ≤ (T.card : ℝ) := hfloor
  exact le_trans hseed (LambdaGE_le_member (M := M1T) hmem)

/-- **Non-vacuity for §2--§3 (NON-FIDELITY).**  The lift is not the empty
construction: on a two-element `C_1` the lifted support has two rows, both in the
single copy fibre, so the frozen row floor it reports is genuinely the support's
size.  The carrier is self-chosen and claims **no** legality -- it audits our
encoding at a point the frozen paper never visits. -/
theorem liftRows_probe_is_nondegenerate :
    (liftRows ({0, 1} : Finset (Slot 2))).card = 2
      ∧ ((liftRows ({0, 1} : Finset (Slot 2))).filter (fun r => r.1 = 0)).card = 2 := by
  refine ⟨?_, ?_⟩
  · rw [liftRows_card]; decide
  · rw [liftRows_fibre_card]; decide

end OneCopyCertificate

/-! ## §4  The unsplit attached pair and the inherited top two-copy rung
(`09:949--950`)

"an unsplit attached pair there has residual complexity `B_cap + 1` by the
inherited top two-copy rung."

`03:388` fixes what that rung is: it "sends `(H,x,z)` to `(H+1,2x,z^2)`".  At the
terminal pins `(H,x,z) = (B_cap, 2^{-b_1}, 3/5)` its output row density is
`2^{1-b_1}`, which is the frozen ladder floor `lambda_{r_2}` of `09:941`, and its
output column density is `(3/5)^2 = 9/25`, which is the frozen post-Alice guard
of `09:1011`.  Those two coincidences are what identify the rung, and both are
machine-checked below. -/

section PairLift

variable {Cone : Type*} [DecidableEq Cone]

/-- **`09:932--933`, `09:949`.**  The two labelled fibres of an attached pair,
read as the row set of the **two**-fold interlace: the ordinary fibre is copy `0`
and the foreign fibre copy `1`.  The tags keep the two physical copies apart even
when the underlying `C_1`-values coincide (`09:534--537`). -/
def pairRows (To Tf : Finset Cone) : Finset (Slot 2 × Cone) :=
  To.image (fun γ => ((0 : Slot 2), γ)) ∪ Tf.image (fun γ => ((1 : Slot 2), γ))

/-- **Aux C1.**  Copy `0` of the pair carries exactly the ordinary fibre.
General. -/
theorem pairRows_fibre_zero (To Tf : Finset Cone) :
    ((pairRows To Tf).filter (fun r => r.1 = (0 : Slot 2))).card = To.card := by
  classical
  have hcard : (To.image (fun γ => ((0 : Slot 2), γ))).card = To.card := by
    refine Finset.card_image_of_injective _ ?_
    intro a b hab
    exact (Prod.mk.injEq _ _ _ _ ▸ hab).2
  rw [← hcard]
  congr 1
  ext r
  simp only [pairRows, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | h, hr⟩
    · exact h
    · obtain ⟨γ, _, rfl⟩ := h
      simp at hr
  · intro h
    obtain ⟨γ, hγ, rfl⟩ := h
    exact ⟨Or.inl ⟨γ, hγ, rfl⟩, rfl⟩

/-- **Aux C2.**  Copy `1` of the pair carries exactly the foreign fibre.
General. -/
theorem pairRows_fibre_one (To Tf : Finset Cone) :
    ((pairRows To Tf).filter (fun r => r.1 = (1 : Slot 2))).card = Tf.card := by
  classical
  have hcard : (Tf.image (fun γ => ((1 : Slot 2), γ))).card = Tf.card := by
    refine Finset.card_image_of_injective _ ?_
    intro a b hab
    exact (Prod.mk.injEq _ _ _ _ ▸ hab).2
  rw [← hcard]
  congr 1
  ext r
  simp only [pairRows, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h | h, hr⟩
    · obtain ⟨γ, _, rfl⟩ := h
      simp at hr
    · exact h
  · intro h
    obtain ⟨γ, hγ, rfl⟩ := h
    exact ⟨Or.inr ⟨γ, hγ, rfl⟩, rfl⟩

end PairLift

section PairFloor

variable (Γ : Type*) [Fintype Γ]

/-- **`09:941`.**  The integer target of the pair trim, `ceil(2^{1-b_1}|C_1|)`:
the frozen ladder floor at the Stage-2 frontier, written at the banked seed
scale.  It is the row density the two-copy rung consumes. -/
noncomputable def pairFloor (b₁ : ℕ) : ℕ :=
  ⌈2 * StageOneInterlace.xSeed b₁ * (Fintype.card Γ : ℝ)⌉₊

variable {Γ}

/-- **Aux C3 (`09:941`, the identification).**  `2 * 2^{-b_1}` is literally the
banked `lambda_{r_2}`, so the rung's output row density and the frozen ladder
floor are the same number and not two coincidentally equal expressions.
General in both exponents. -/
theorem two_mul_xSeed_eq_lambdaAt_frontier (r₂ b₁ : ℕ) :
    2 * StageOneInterlace.xSeed b₁
      = DenseRoutingThresholds.lambdaAt (2 ^ r₂) b₁ r₂ := by
  rw [TerminalTwoStream.lambdaAt_stage2_frontier, DenseRoutingThresholds.xSeed_eq_inv_pow]
  ring

/-- **Aux C4 (the pair trim is legal at every depth the frozen proof uses).**  At
suffix depth `d <= r_2` the banked routing floor dominates the pair floor, so a
routed pair whose two fibres meet the routing invariant meets the two-copy rung's
row threshold.  The threshold comparison is the banked
`DenseWeightedCount.two_mul_xSeed_le_lambdaAt_of_le`.  General. -/
theorem pairFloor_le_routingFloor {r b₁ d : ℕ} (hd : d ≤ r) :
    pairFloor Γ b₁ ≤ DenseRoutingInvariant.routingFloor Γ (2 ^ r) b₁ d := by
  unfold pairFloor DenseRoutingInvariant.routingFloor
  refine Nat.ceil_le_ceil ?_
  exact mul_le_mul_of_nonneg_right
    (DenseWeightedCount.two_mul_xSeed_le_lambdaAt_of_le hd) (by positivity)

end PairFloor

section TopTwoCopy

variable {Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone] [Fintype Rone]

omit [DecidableEq Cone] in
/-- **`09:949--950` with `03:388`, the rung itself, PROVED.**  The inherited
two-copy rung sends `(H, x, z)` to `(H + 1, 2x, z^2)`; at the terminal pins
`(B_cap, 2^{-b_1}, 3/5)` that is
`B_cap + 1 <= Lambda_{M_1^T}(2, 2^{1-b_1}, 9/25)`.

This is the `ell = 1` instance of the banked `lem:certified-row-ladder`
(`TerminalTwoStream.certifiedRowLadder_of_base`), and nothing is re-derived: the
frozen antecedents `H >= 2`, `2x <= 1`, the two carrier nonemptiness clauses and
the base certificate are separate binders exactly as the banked lemma states
them.  General in both carriers, in `b_1` and in `B_cap`. -/
theorem topTwoCopy_rung (M1T : Cone → Rone → Bool) {b₁ bcap : ℕ}
    (hX : 1 ≤ Fintype.card Cone) (hY : 1 ≤ Fintype.card Rone)
    (hH : 2 ≤ bcap) (hlegal : 2 * StageOneInterlace.xSeed b₁ ≤ 1)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5)) :
    bcap + 1 ≤ LambdaGE M1T 2 (2 * StageOneInterlace.xSeed b₁) (9 / 25) := by
  have hlad := TerminalTwoStream.certifiedRowLadder_of_base M1T hX hY hH
    (StageOneInterlace.xSeed_pos b₁) (by norm_num) (by norm_num) hseed
  have h1 := hlad 1 le_rfl (by simpa using hlegal)
  have hz : ((3 : ℝ) / 5) ^ 2 = 9 / 25 := by norm_num
  have hx : (2 : ℝ) ^ (1 : ℕ) * StageOneInterlace.xSeed b₁
      = 2 * StageOneInterlace.xSeed b₁ := by norm_num
  simpa [hz, hx] using h1

/-- **`09:949--950`, the residual reading, PROVED.**  At a node whose two labelled
fibres each meet the pair floor `ceil(2^{1-b_1}|C_1|)` and whose retained typed
two-copy projection meets the frozen `9/25` ceiling, the pair's local block has
complexity at least `B_cap + 1`.

This is the binder `hpair` of `Stage3ProtocolRouting.stage2_unsplit_pair_depth_lt`
and `.stage2_unsplit_pair_capacity_two`, now a theorem.  General. -/
theorem topTwoCopy_residual_at_pair_floor (M1T : Cone → Rone → Bool) {b₁ bcap : ℕ}
    (hX : 1 ≤ Fintype.card Cone) (hY : 1 ≤ Fintype.card Rone)
    (hH : 2 ≤ bcap) (hlegal : 2 * StageOneInterlace.xSeed b₁ ≤ 1)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5))
    {To Tf : Finset Cone}
    (hTo : pairFloor Cone b₁ ≤ To.card) (hTf : pairFloor Cone b₁ ≤ Tf.card)
    {C : Finset (Slot 2 → Rone)}
    (hcol : ⌈((Fintype.card Rone : ℝ) ^ 2) * (9 / 25)⌉₊ ≤ C.card) :
    bcap + 1 ≤ D (subgame (interlaceFun M1T 2) (pairRows To Tf) C) := by
  have hbase : 2 * StageOneInterlace.xSeed b₁ * (Fintype.card Cone : ℝ)
      ≤ (pairFloor Cone b₁ : ℝ) := Nat.le_ceil _
  have hmem : ((pairRows To Tf, C) : Finset (Slot 2 × Cone) × Finset (Slot 2 → Rone))
      ∈ bracketGE Cone Rone 2 (2 * StageOneInterlace.xSeed b₁) (9 / 25) := by
    refine mem_bracketGE_of_floors (fun i => ?_) hcol
    have hswap : (Fintype.card Cone : ℝ) * (2 * StageOneInterlace.xSeed b₁)
        = 2 * StageOneInterlace.xSeed b₁ * (Fintype.card Cone : ℝ) := by ring
    rw [hswap]
    by_cases hi : i = 0
    · subst hi
      rw [pairRows_fibre_zero]
      refine le_trans hbase ?_
      exact_mod_cast hTo
    · have hi1 : i = 1 := by
        refine Fin.ext ?_
        have h0 : (i : ℕ) ≠ 0 := fun hc => hi (Fin.ext hc)
        have hlt : (i : ℕ) < 2 := i.isLt
        have hone : ((1 : Slot 2) : ℕ) = 1 := rfl
        omega
      subst hi1
      rw [pairRows_fibre_one]
      refine le_trans hbase ?_
      exact_mod_cast hTf
  exact le_trans (topTwoCopy_rung M1T hX hY hH hlegal hseed) (LambdaGE_le_member (M := M1T) hmem)

/-- **HYPOTHESIS-CONSISTENCY for §4.**  The *scale* clause of `topTwoCopy_rung`
is satisfiable at the banked **balance-minimum** width record, jointly with the
frozen column
pins: at `b_1 = TerminalTwoStream.probeWidths.b₁ = 24` the *scale* legality
`2 * 2^{-b_1} <= 1` holds with room to spare, and `(3/5)^2 = 9/25 < 49/128` is
the banked post-Alice comparison.  So the theorem is not quantified over an
empty scale regime.

Two clauses of the bundle are deliberately **not** exhibited, and this readout
does not claim them: `hH : 2 <= B_cap`, because `B_cap` is universally
quantified and occurs in no other arithmetic clause, so it can conflict with
nothing; and the certificate clause `hseed`, because it is an inherited Stage-1
conclusion and is not re-derived here.

`probeWidths` is legal for the four proof fields of
`StageTwoRelaxed.StageTwoWidths` and is **not** a legal schedule width record:
its `k_2 = 5` fails the `eq:t2-search` floor `k_2 >= max{4, 2^{19}, m_HS}`
(`06:766`, `2^{19} = 524288`).  So this readout is arithmetic consistency
evidence about our encoding of the scale clause, never a witness at the paper's
parameter values.  (Unqualified legality reading repaired at `cc-t7q`, ledger
item `(b14)`.) -/
theorem topTwoCopy_hypotheses_consistent :
    2 * StageOneInterlace.xSeed TerminalTwoStream.probeWidths.b₁ ≤ 1
      ∧ ((3 : ℝ) / 5) ^ 2 = 9 / 25
      ∧ (9 : ℝ) / 25 < 49 / 128 := by
  refine ⟨?_, by norm_num, TerminalTwoStream.post_alice_density_gt⟩
  rw [DenseRoutingThresholds.xSeed_eq_inv_pow]
  have hb : TerminalTwoStream.probeWidths.b₁ = 24 := rfl
  rw [hb]
  norm_num

/-- **LANE-GATE 3 for §3--§4: the geometric half of both certificate bundles is
inhabited (NON-FIDELITY).**

The three floors the two certificate theorems impose -- the seed floor of
`09:477`, the pair floor of `09:941`, and the column ceilings of `07:210` and
`09:1011` -- are simultaneously satisfiable at a concrete carrier and at the
banked **balance-minimum** scale `b_1 = TerminalTwoStream.probeWidths.b₁ = 24`: a
two-element
`C_1` with both fibres full and the full column set clears all four.  So neither
`oneCopy_residual_at_seed_floor` nor `topTwoCopy_residual_at_pair_floor` is
quantified over an empty geometry.

What is **not** exhibited, and deliberately so, is the certificate hypothesis
`hseed`: it is the inherited Stage-1 conclusion `eq:stage1-robust-certificate`
and cannot be witnessed at a two-element carrier.  The carrier is self-chosen and
claims **no** legality -- it audits our encoding of the floors, not the frozen
regime.  Neither does the scale: `probeWidths` is legal for the four proof fields
of `StageTwoRelaxed.StageTwoWidths` and is **not** a legal schedule width record,
its `k_2 = 5` failing the `eq:t2-search` floor `k_2 >= max{4, 2^{19}, m_HS}`
(`06:766`).  (Unqualified legality reading repaired at `cc-t7q`, ledger item
`(b14)`.) -/
theorem certificate_floors_are_satisfiable :
    DenseWeightedCount.seedFloor (Slot 2) TerminalTwoStream.probeWidths.b₁
        ≤ ({0, 1} : Finset (Slot 2)).card
      ∧ pairFloor (Slot 2) TerminalTwoStream.probeWidths.b₁
        ≤ ({0, 1} : Finset (Slot 2)).card
      ∧ ⌈((Fintype.card (Slot 2) : ℝ) ^ 1) * (3 / 5)⌉₊
        ≤ (Finset.univ : Finset (Slot 1 → Slot 2)).card
      ∧ ⌈((Fintype.card (Slot 2) : ℝ) ^ 2) * (9 / 25)⌉₊
        ≤ (Finset.univ : Finset (Slot 2 → Slot 2)).card := by
  have hb : TerminalTwoStream.probeWidths.b₁ = 24 := rfl
  have hcard : Fintype.card (Slot 2) = 2 := by simp
  have hx : StageOneInterlace.xSeed 24 = 1 / 2 ^ 24 :=
    DenseRoutingThresholds.xSeed_eq_inv_pow 24
  have htwo : ({0, 1} : Finset (Slot 2)).card = 2 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hb, htwo, DenseWeightedCount.seedFloor, hcard, hx]
    exact Nat.ceil_le.2 (by norm_num)
  · rw [hb, htwo, pairFloor, hcard, hx]
    exact Nat.ceil_le.2 (by norm_num)
  · rw [hcard]
    have : (Finset.univ : Finset (Slot 1 → Slot 2)).card = 2 := by simp
    rw [this]
    exact Nat.ceil_le.2 (by norm_num)
  · rw [hcard]
    have : (Finset.univ : Finset (Slot 2 → Slot 2)).card = 4 := by simp
    rw [this]
    exact Nat.ceil_le.2 (by norm_num)

/-- **Non-vacuity for §4 (NON-FIDELITY).**  Both labelled fibres of the pair are
genuinely present and genuinely separated by their tags: on a two-element `C_1`
the two copies each carry two rows even though the underlying values coincide,
which is the frozen `09:534--537` "their physical images are disjoint ... there
is no requirement that the underlying subsets be disjoint".  The carrier is
self-chosen and claims **no** legality. -/
theorem pairRows_probe_is_nondegenerate :
    ((pairRows ({0, 1} : Finset (Slot 2)) ({0, 1} : Finset (Slot 2))).filter
        (fun r => r.1 = (0 : Slot 2))).card = 2
      ∧ ((pairRows ({0, 1} : Finset (Slot 2)) ({0, 1} : Finset (Slot 2))).filter
        (fun r => r.1 = (1 : Slot 2))).card = 2
      ∧ (pairRows ({0, 1} : Finset (Slot 2)) ({0, 1} : Finset (Slot 2))).card = 4 := by
  refine ⟨by rw [pairRows_fibre_zero]; decide, by rw [pairRows_fibre_one]; decide, by decide⟩

end TopTwoCopy

/-! ## §5  The two `Stage3ProtocolRouting` discharges

The predecessor module states its GAP-EXPOSED 1 as: "what remains for phase 1
are the *certificate* inputs -- the one-copy and top two-copy residual readings
at a node ... carried here as **explicit binders** at every theorem that consumes
them".  Both are now theorems, so the two banked conclusions are re-run with the
binders supplied. -/

section Discharges

variable {X Y Z Coord Cone Rone : Type*} [Fintype Cone] [DecidableEq Cone] [Fintype Rone]

/-- **`09:937--978` with its certificate supplied.**  The banked Stage-2 frontier
conclusion, with `honeCopy` **discharged** by `oneCopy_residual_at_seed_floor`
instead of assumed.  The node game is the frozen local block itself -- the
one-copy restriction of `M = M_1^T` on the token's surviving support and the
node's retained typed projection -- so no abstract game family is quantified
over.

The residual comparison `hresidual` stays an explicit binder: it says the alleged
protocol's subtree at the node still solves the node's game, which is protocol
bookkeeping and not a certificate.  General. -/
theorem stage2_routed_token_frontier_at_certificates {Pstar : Protocol X Y Z}
    (M1T : Cone → Rone → Bool) (t : DenseWeightedCount.StoppedToken Pstar Coord)
    (supp : List Bool → Finset Cone) (cols : List Bool → Finset (Slot 1 → Rone))
    {bcap r₂ b₁ : ℕ} {y : ℝ}
    (hbcap : 0 < bcap)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) y)
    (hcolFloor : ∀ p : List Bool,
      ⌈((Fintype.card Rone : ℝ) ^ 1) * y⌉₊ ≤ (cols p).card)
    (hnodeFloor : t.route.length ≤ r₂ →
      DenseRoutingInvariant.routingFloor Cone (2 ^ r₂) b₁ t.route.length
        ≤ (supp t.route).card)
    (hdeepFloor : r₂ + 1 ≤ t.route.length →
      DenseRoutingInvariant.routingFloor Cone (2 ^ r₂) b₁ (r₂ + 1)
        ≤ (supp (t.route.take (r₂ + 1))).card)
    (hresidual : ∀ p : List Bool,
      D (subgame (interlaceFun M1T 1) (liftRows (supp p)) (cols p))
        ≤ (DenseWeightedCount.descend Pstar p).cost) :
    (t.event = DenseWeightedCount.StopEvent.isolation
        ∨ t.event = DenseWeightedCount.StopEvent.beforeAlice)
      ∧ t.route.length ≤ r₂ :=
  Stage3ProtocolRouting.stage2_routed_token_frontier
    (fun p => subgame (interlaceFun M1T 1) (liftRows (supp p)) (cols p))
    t supp hbcap hbudget hnodeFloor hdeepFloor
    (fun p hp => oneCopy_residual_at_seed_floor M1T hseed hp (hcolFloor p))
    hresidual

/-- **`09:953--965` with its certificate supplied.**  The banked
`eq:isolation-capacity` at a Stage-2 isolation node, with the `B_cap + 1` rung
`hpair` **discharged** by `topTwoCopy_residual_at_pair_floor` instead of assumed.
The pair's local block is the frozen two-copy restriction on the two labelled
fibres, and the capacity premise `htwo` is derived from the alleged protocol's
own budget inside the banked composition.

`huniq` is the frozen coordinatewise uniqueness, which §7 constructs from the
isolation test; here it is the named hypothesis the banked lemma states.
General. -/
theorem stage2_isolation_capacity_at_certificates {Pstar : Protocol X Y Z}
    (M1T : Cone → Rone → Bool) {p : List Bool} {bcap r₂ b₁ h z : ℕ}
    (hX : 1 ≤ Fintype.card Cone) (hY : 1 ≤ Fintype.card Rone)
    (hH : 2 ≤ bcap) (hlegal : 2 * StageOneInterlace.xSeed b₁ ≤ 1)
    (hseed : bcap ≤ LambdaGE M1T 1 (StageOneInterlace.xSeed b₁) (3 / 5))
    (huniq : h ≤ 1) (hz : z ≤ h)
    (hpath : DenseWeightedCount.IsQueryPath Pstar p)
    (hbudget : Pstar.cost ≤ DenseBranchSelection.Dtwo bcap r₂)
    {To Tf : Finset Cone}
    (hTo : pairFloor Cone b₁ ≤ To.card) (hTf : pairFloor Cone b₁ ≤ Tf.card)
    {C : Finset (Slot 2 → Rone)}
    (hcol : ⌈((Fintype.card Rone : ℝ) ^ 2) * (9 / 25)⌉₊ ≤ C.card)
    (hres : 0 < z →
      D (subgame (interlaceFun M1T 2) (pairRows To Tf) C)
        ≤ (DenseWeightedCount.descend Pstar p).cost) :
    h + z ≤ DenseWeightedCount.stoppingCapacity r₂ p.length :=
  Stage3ProtocolRouting.stage2_isolation_capacity_from_protocol
    (gpair := subgame (interlaceFun M1T 2) (pairRows To Tf) C)
    huniq hz hpath hbudget
    (fun _ => topTwoCopy_residual_at_pair_floor M1T hX hY hH hlegal hseed hTo hTf hcol)
    hres

end Discharges

/-! ## §6  The fibre sets at a protocol node, and the invariance of
`09:1076--1078`  (TSL GAP-EXPOSED 7)

"Until the first Bob query, these Alice restrictions do not change the ordinary
and foreign fibre sets `O_alpha, F_alpha`, so the averages `eq:terminal-averages`
are unchanged."

In the Stage-3 selector orientation of `09:1039--1041` Alice owns the outer row
blocks of `interlace(S_2, s)` and **Bob owns its product columns**
`Cols(S_2)^s = J_2^s`, so the fibre sets -- which live in
`J_2 = [q_2] x C_1` -- are Bob-side data.  The frozen readout that produces them
from a column tuple is `rho_p(c) = j(p)` (`09:512--516`): evaluate the tuple at
the bin.  That is `binImage` below; nothing is invented for it. -/

section Fibres

variable {s q₂ : ℕ} {Cone Xr Zo : Type*} [Fintype Cone] [DecidableEq Cone]

/-- **`09:512--516`.**  The frozen bin readout `rho_p` on selector column tuples:
`rho_p(j) = j(p) in J_2 = [q_2] x C_1`.  Applied to a set of tuples it produces
the frozen image `E` whose `alpha`-fibres are `O_alpha` and `F_alpha`. -/
def binImage (K : Finset (Slot s → Slot q₂ × Cone)) (p : Slot s) :
    Finset (Slot q₂ × Cone) :=
  K.image (fun k => k p)

/-- **`09:1085--1086`.**  "the joint ordinary column set `K_ord`" surviving at a
protocol node, i.e. the banked `retainedCols` of the Stage-3 Bob carrier.  The
banked definition is consumed, not restated. -/
def kordAt (P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo)
    (K : Finset (Slot s → Slot q₂ × Cone)) (route : List Bool) :
    Finset (Slot s → Slot q₂ × Cone) :=
  RoutedCertificateSystem.retainedCols P₃ K route

/-- **`09:522`, `09:525` read at a protocol node.**  `O_alpha` (and, at the
foreign bin, `F_alpha`) of the carrier surviving at `route`.  One definition
serves both bins, exactly as the frozen display uses one formula. -/
def fibreAt (P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo)
    (K : Finset (Slot s → Slot q₂ × Cone)) (route : List Bool) (p : Slot s)
    (α : Slot q₂) : Finset Cone :=
  TwoStreamState.colFibre (binImage (kordAt P₃ K route) p) α

/-- **Aux E1 (a helper the banked module does not carry; dual of the banked
`Stage3ProtocolRouting.aliceCols_append`).**  Bob's surviving column set
decomposes along any split of the address.  General. -/
theorem bobCols_append : ∀ {P : Protocol Xr (Slot s → Slot q₂ × Cone) Zo}
    (p r : List Bool),
    RoutedCertificateSystem.bobCols P (p ++ r)
      = RoutedCertificateSystem.bobCols P p
        ∩ RoutedCertificateSystem.bobCols (DenseWeightedCount.descend P p) r := by
  intro P p
  induction p generalizing P with
  | nil =>
      intro r
      simp [DenseWeightedCount.descend]
  | cons b p ih =>
      intro r
      rw [List.cons_append, RoutedCertificateSystem.bobCols_cons, ih,
        RoutedCertificateSystem.bobCols_cons, DenseWeightedCount.descend_cons,
        Finset.inter_assoc]

/-- **`09:1076--1077`, the protocol-side half.**  An Alice query places no
constraint on Bob's columns, so the surviving column set is untouched by the
answer bit.  The step itself is the banked
`RoutedCertificateSystem.bobConstraint_of_isANode`.  General. -/
theorem alice_query_preserves_bobCols
    {P : Protocol Xr (Slot s → Slot q₂ × Cone) Zo} {route : List Bool}
    (h : DenseSynchronisation.IsANode (DenseWeightedCount.descend P route)) (b : Bool) :
    RoutedCertificateSystem.bobCols P (route ++ [b])
      = RoutedCertificateSystem.bobCols P route := by
  rw [bobCols_append route [b], RoutedCertificateSystem.bobCols_cons,
    RoutedCertificateSystem.bobConstraint_of_isANode h b]
  simp

/-- **`09:1085--1086`, "the joint ordinary column set `K_ord` is unchanged".**
General. -/
theorem alice_query_preserves_kordAt
    {P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo}
    (K : Finset (Slot s → Slot q₂ × Cone)) {route : List Bool}
    (h : DenseSynchronisation.IsANode (DenseWeightedCount.descend P₃ route)) (b : Bool) :
    kordAt P₃ K (route ++ [b]) = kordAt P₃ K route := by
  simp only [kordAt, RoutedCertificateSystem.retainedCols,
    alice_query_preserves_bobCols h b]

/-- **`09:1076--1078`, the frozen invariance itself, PROVED.**  "these Alice
restrictions do not change the ordinary and foreign fibre sets
`O_alpha, F_alpha`."  At an Alice query every fibre of every bin is literally the
same `Finset`.  General in the state's carriers, the bin and the coordinate. -/
theorem alice_query_preserves_fibreAt
    {P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo}
    (K : Finset (Slot s → Slot q₂ × Cone)) {route : List Bool}
    (h : DenseSynchronisation.IsANode (DenseWeightedCount.descend P₃ route)) (b : Bool)
    (p : Slot s) (α : Slot q₂) :
    fibreAt P₃ K (route ++ [b]) p α = fibreAt P₃ K route p α := by
  simp only [fibreAt, alice_query_preserves_kordAt K h b]

/-- **`09:1077--1078`, the frozen consequence, PROVED.**  "so the averages
`eq:terminal-averages` are unchanged."  Both frozen averages are computed from
the bin image, which the previous theorem leaves fixed.  General. -/
theorem alice_query_preserves_meanFibreDensity
    {P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo}
    (K : Finset (Slot s → Slot q₂ × Cone)) {route : List Bool}
    (h : DenseSynchronisation.IsANode (DenseWeightedCount.descend P₃ route)) (b : Bool)
    (p : Slot s) :
    TwoStreamState.meanFibreDensity (binImage (kordAt P₃ K (route ++ [b])) p)
      = TwoStreamState.meanFibreDensity (binImage (kordAt P₃ K route) p) := by
  rw [alice_query_preserves_kordAt K h b]

/-- **`09:1076`, "Until the first Bob query", PROVED.**  Along a whole Alice-only
address the surviving carrier is the ambient one, so every fibre set and both
averages are the *unrestricted* ones.  The prefix fact is the banked
`RoutedCertificateSystem.retainedCols_of_isAlicePath`; what is new is that it
transports through the frozen bin readout to the fibre sets themselves.
General. -/
theorem fibres_unchanged_until_first_bob
    {P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo}
    (K : Finset (Slot s → Slot q₂ × Cone)) {route : List Bool}
    (h : RoutedCertificateSystem.IsAlicePath P₃ route) :
    kordAt P₃ K route = K
      ∧ (∀ (p : Slot s) (α : Slot q₂),
          fibreAt P₃ K route p α = TwoStreamState.colFibre (binImage K p) α)
      ∧ (∀ p : Slot s,
          TwoStreamState.meanFibreDensity (binImage (kordAt P₃ K route) p)
            = TwoStreamState.meanFibreDensity (binImage K p)) := by
  have hK : kordAt P₃ K route = K := by
    simp only [kordAt]
    exact RoutedCertificateSystem.retainedCols_of_isAlicePath h
  refine ⟨hK, ?_, ?_⟩
  · intro p α
    simp only [fibreAt, hK]
  · intro p
    rw [hK]

/-- **`09:1076--1078` transported to the record's own fields.**

Given the frozen identification of the state's two stream images with the bin
readouts of its selector column carrier -- `09:628--630`'s "the witness includes
the actual row and column sections", carried here as the two **explicit binders**
`hpresOrd` and `hpresFor` because the frozen text displays no equation for it --
the fibre sets at every Alice-only node are the record's own, and the two frozen
averages `eq:terminal-averages` hold there verbatim.

This is the exact statement `TerminalStageThreeLift`'s GAP-EXPOSED 7 records as
missing, at the strength the frozen sentence claims and no more.  General in the
state, the protocol and the address. -/
theorem terminal_averages_unchanged_until_first_bob
    {Rw Cl Om Ltwo Rone : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl]
    [DecidableEq Cl] [Fintype Ltwo] [DecidableEq Ltwo]
    {q mT dT : ℕ} {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool}
    {cFam : Ltwo → Slot q₂ → Rone} {Stwo : Ltwo → Slot q₂ × Cone → Bool}
    {RG RSig RD : Finset Rw} {omg : Rw → Om}
    {rho : Slot s → Om → Slot q₂ × Cone} {YT : Slot s → Finset Cl}
    {zeta : Slot s → Cl → Ltwo} {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)}
    {lamT eps2 xT ε δ' : ℝ}
    (st : TwoStreamState.TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD
      omg rho YT zeta XZ YZ lamT eps2 xT ε δ')
    (P₃ : Protocol Xr (Slot s → Slot q₂ × Cone) Zo) {route : List Bool}
    (h : RoutedCertificateSystem.IsAlicePath P₃ route)
    (hpresOrd : binImage st.Kord st.pOrd
      = TwoStreamState.streamImage omg rho st.pOrd XZ st.iOrd RG)
    (hpresFor : binImage st.Kord st.pFor
      = TwoStreamState.streamImage omg rho st.pFor XZ st.iFor st.Rfor) :
    (∀ α : Slot q₂, fibreAt P₃ st.Kord route st.pOrd α
        = TwoStreamState.colFibre
            (TwoStreamState.streamImage omg rho st.pOrd XZ st.iOrd RG) α)
      ∧ (∀ α : Slot q₂, fibreAt P₃ st.Kord route st.pFor α
        = TwoStreamState.colFibre
            (TwoStreamState.streamImage omg rho st.pFor XZ st.iFor st.Rfor) α)
      ∧ 1 - ε ≤ TwoStreamState.meanFibreDensity
          (binImage (kordAt P₃ st.Kord route) st.pOrd)
      ∧ δ' ≤ TwoStreamState.meanFibreDensity
          (binImage (kordAt P₃ st.Kord route) st.pFor) := by
  obtain ⟨-, hfib, hmean⟩ := fibres_unchanged_until_first_bob (P₃ := P₃) st.Kord h
  refine ⟨fun α => ?_, fun α => ?_, ?_, ?_⟩
  · rw [hfib st.pOrd α, hpresOrd]
  · rw [hfib st.pFor α, hpresFor]
  · rw [hmean st.pOrd, hpresOrd]
    exact st.ordinary_density
  · rw [hmean st.pFor, hpresFor]
    exact st.foreign_density

end Fibres

/-- **Statement pole 2 (the Alice-node hypothesis of §6 is load-bearing).**  A
*Bob* query genuinely deletes columns, so the invariance is not a tautology about
`bobCols`: at a Bob query whose predicate is nonconstant the node's column set is
strictly smaller than its parent's, and the frozen sentence's "Until the first
Bob query" is doing real work.  The witness is the banked
`RoutedCertificateSystem.bobCols_pole_at_bob_query`, consumed by pin. -/
theorem fibre_invariance_needs_the_alice_node {Xr Zo : Type*}
    (a : Xr → Bool) (z : Zo) :
    (true : Bool) ∉ RoutedCertificateSystem.bobCols
      (RoutedCertificateSystem.bobCappedLadder (X := Xr) a (fun y : Bool => y) z 0)
      [false] :=
  RoutedCertificateSystem.bobCols_pole_at_bob_query a (fun y : Bool => y) z rfl

/-! ## §7  Coordinate isolation as a construction (`08:982--983`, `09:937--938`,
`09:1084--1085`)

"At a coordinate-isolation node, every other coordinate fibre is empty."
(`08:982--983`)  That sentence is a *test*, and the banked `DenseWeightedCount`
carries it only abstractly (its coverage limit 4: "the isolation predicate is
carried **abstractly** ... and the uniqueness consequence `08:1004--1005` is the
named hypothesis `huniq`").  This section builds the test and derives the
uniqueness.

One definition serves both frozen stopping rules: the Stage-2 rule of `09:937--938`
instantiates it at the Stage-2 coordinates, the Stage-3 rule of `09:1084--1085` at
the outer blocks. -/

section Isolation

variable {Coord Γ : Type*}

/-- **`08:982--983`.**  "At a coordinate-isolation node, every other coordinate
fibre is empty": the node's fibre assignment is isolated at `alpha`. -/
def IsolatedAt (fib : Coord → Finset Γ) (α : Coord) : Prop :=
  ∀ β, β ≠ α → fib β = ∅

instance decidableIsolatedAt [Fintype Coord] [DecidableEq Coord] [DecidableEq Γ]
    (fib : Coord → Finset Γ) (α : Coord) : Decidable (IsolatedAt fib α) := by
  unfold IsolatedAt
  infer_instance

/-- **`08:982--984`.**  A node is a coordinate-isolation node when the frozen
description applies at some coordinate.

**On the existential.**  Its "trivial witness" -- an assignment with *every*
fibre empty -- does satisfy this predicate, and that is correct rather than a
defect: such a node carries no routed object at all, so the frozen consequence
`08:1004--1005` ("contains at most one routed object") holds there a fortiori,
and `isolationNode_of_card_liveCoords_le_one` shows the predicate is *exactly*
"at most one live coordinate".  The deliverable is therefore never an existence
claim: it is the universally quantified
`card_liveCoords_le_one_of_isolationNode`, whose non-triviality is the pole
`isolation_test_is_not_free`. -/
def IsIsolationNode [Fintype Coord] (fib : Coord → Finset Γ) : Prop :=
  ∃ α, IsolatedAt fib α

instance decidableIsIsolationNode [Fintype Coord] [DecidableEq Coord] [DecidableEq Γ]
    (fib : Coord → Finset Γ) : Decidable (IsIsolationNode fib) := by
  unfold IsIsolationNode
  infer_instance

/-- The coordinates still carrying a routed object at the node -- the frozen
"routed objects" whose count `08:1005` bounds. -/
def liveCoords [Fintype Coord] [DecidableEq Coord] (fib : Coord → Finset Γ) :
    Finset Coord :=
  Finset.univ.filter (fun α => (fib α).Nonempty)

variable [Fintype Coord] [DecidableEq Coord]

/-- **Aux F1.**  Membership in the live set is nonemptiness of the fibre.
General. -/
theorem mem_liveCoords {fib : Coord → Finset Γ} {α : Coord} :
    α ∈ liveCoords fib ↔ (fib α).Nonempty := by
  simp [liveCoords]

/-- **Aux F2.**  An isolated node has no live coordinate other than its witness.
General. -/
theorem liveCoords_subset_of_isolatedAt {fib : Coord → Finset Γ} {α : Coord}
    (h : IsolatedAt fib α) : liveCoords fib ⊆ {α} := by
  intro β hβ
  rw [mem_liveCoords] at hβ
  by_contra hne
  rw [Finset.mem_singleton] at hne
  rw [h β hne] at hβ
  exact absurd hβ (by simp)

/-- **`08:1004--1005`, PROVED.**  "By the coordinatewise uniqueness in
`lem:dense-routing`, an isolation node contains at most one routed object."  This
is the premise the banked `eq:isolation-capacity` carries as `huniq`; it is now a
consequence of the isolation *test*.  General. -/
theorem card_liveCoords_le_one_of_isolationNode {fib : Coord → Finset Γ}
    (h : IsIsolationNode fib) : (liveCoords fib).card ≤ 1 := by
  obtain ⟨α, hα⟩ := h
  calc (liveCoords fib).card ≤ ({α} : Finset Coord).card :=
        Finset.card_le_card (liveCoords_subset_of_isolatedAt hα)
    _ = 1 := Finset.card_singleton α

/-- **Aux F3 (the test is exact, not one-directional).**  Conversely, a node with
at most one live coordinate *is* an isolation node, provided the coordinate type
is inhabited -- which the frozen `[q_2]` and `[s]` are.  So `IsolatedAt` is not a
strengthening of the frozen sentence.  General. -/
theorem isolationNode_of_card_liveCoords_le_one [Nonempty Coord]
    {fib : Coord → Finset Γ} (h : (liveCoords fib).card ≤ 1) :
    IsIsolationNode fib := by
  classical
  rcases Finset.eq_empty_or_nonempty (liveCoords fib) with hemp | ⟨α, hα⟩
  · refine ⟨Classical.arbitrary Coord, fun β _ => ?_⟩
    by_contra hne
    have : β ∈ liveCoords fib := mem_liveCoords.2 (Finset.nonempty_iff_ne_empty.2 hne)
    rw [hemp] at this
    exact absurd this (by simp)
  · refine ⟨α, fun β hβ => ?_⟩
    by_contra hne
    have hmem : β ∈ liveCoords fib := mem_liveCoords.2 (Finset.nonempty_iff_ne_empty.2 hne)
    have hsub : ({α, β} : Finset Coord) ⊆ liveCoords fib := by
      intro γ hγ
      rcases Finset.mem_insert.1 hγ with rfl | hγ'
      · exact hα
      · rw [Finset.mem_singleton] at hγ'
        exact hγ' ▸ hmem
    have hcard : ({α, β} : Finset Coord).card = 2 :=
      Finset.card_pair (fun hc => hβ hc.symm)
    have := Finset.card_le_card hsub
    omega

omit [Fintype Coord] [DecidableEq Coord] in
/-- **Aux F4.**  The isolated coordinate is unique once it is live: two isolation
witnesses with a nonempty fibre coincide.  This is the frozen "leaves at most one
routed object there" in its sharp form.  General. -/
theorem isolatedAt_unique {fib : Coord → Finset Γ} {α β : Coord}
    (hα : IsolatedAt fib α) (hne : (fib β).Nonempty) : β = α := by
  by_contra hcon
  rw [hα β hcon] at hne
  exact absurd hne (by simp)

/-- **`08:983--985`, the frozen classification at the constructed test.**  The
tie-break ("If both descriptions hold at the same protocol node, classify it as a
coordinate-isolation node"), the disjointness and the exhaustiveness are the
banked `DenseWeightedCount` facts, consumed by pin at `iso := IsIsolationNode`;
no second classification is defined here.  General in the frontier index type and
the fibre assignment. -/
theorem frontier_classification_at_isolation_test {ι : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq Γ] (fib : ι → Coord → Finset Γ)
    (alice : ι → Prop) (v : ι) (hiso : IsIsolationNode (fib v)) (halice : alice v) :
    DenseWeightedCount.frontierClass (fun w => IsIsolationNode (fib w)) v
        = DenseWeightedCount.FrontierClass.isolation
      ∧ Disjoint
          (DenseWeightedCount.isolationNodes (fun w => IsIsolationNode (fib w)))
          (DenseWeightedCount.aliceNodes (fun w => IsIsolationNode (fib w)))
      ∧ DenseWeightedCount.isolationNodes (fun w => IsIsolationNode (fib w))
          ∪ DenseWeightedCount.aliceNodes (fun w => IsIsolationNode (fib w))
        = Finset.univ :=
  ⟨DenseWeightedCount.frontierClass_isolation_of_both _ alice v hiso halice,
    DenseWeightedCount.frontier_disjoint _, DenseWeightedCount.frontier_union _⟩

end Isolation

/-! ### Non-vacuity and the rejection probe for §7 -/

/-- The probe fibre assignment: three Stage-2 coordinates, only the middle one
live. -/
def probeFib : Slot 3 → Finset (Slot 2) :=
  fun α => if α = 1 then {0} else ∅

/-- The probe fibre assignment with **two** live coordinates. -/
def probeFibTwo : Slot 3 → Finset (Slot 2) :=
  fun α => if α = 0 ∨ α = 1 then {0} else ∅

/-- **Non-vacuity for §7 (the isolation test fires, and it is nondegenerate) --
NON-FIDELITY.**  At a three-coordinate probe with exactly one live fibre the
constructed test fires, the live set is the singleton, and the frozen
`huniq : h <= 1` is delivered.  The carrier is self-chosen and claims **no**
legality; it audits our encoding at a point the frozen paper never visits. -/
theorem isolation_probe_fires :
    IsolatedAt probeFib 1
      ∧ liveCoords probeFib = {1}
      ∧ (liveCoords probeFib).card ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · exact card_liveCoords_le_one_of_isolationNode ⟨1, by decide⟩

/-- **Rejection probe for §7 (the guard fires on an illegal node) -- no legality
claimed.**  A node with two live coordinate fibres is **not** a coordinate
isolation node under the constructed test, at any witness; so the test is not
satisfied by every assignment and the derived `huniq` is not free.  The values are
self-chosen and no legality is asserted. -/
theorem isolation_probe_rejects_two_live_fibres :
    ¬ IsIsolationNode probeFibTwo
      ∧ (liveCoords probeFibTwo).card = 2 := by
  refine ⟨?_, by decide⟩
  decide

/-- **Statement pole 3 (the isolation test is a real constraint).**  The
conclusion `h <= 1` of `card_liveCoords_le_one_of_isolationNode` is not automatic:
at the two-live-fibre probe the live count is `2`, so a node that fails the frozen
test genuinely violates the bound the banked `eq:isolation-capacity` consumes.
Hence the test is doing work and is not a decorative hypothesis. -/
theorem isolation_test_is_not_free :
    ¬ ((liveCoords probeFibTwo).card ≤ 1) := by
  decide

end EthInapproximability.ParameterizedNP.TerminalCertificateInputs
