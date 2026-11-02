import EthInapproximability.ParameterizedNP.RoutedCertificateConstruction

/-!
# Parameterized NP route: the retention supply, `09:1217--1236`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`,
  recomputed first-hand for this tranche).
* **The exact frozen lines traced here**, in print order:
  * **`09:1188--1191`, the retained matrix**: "Fix an arbitrary retained matrix
    `U' in [U]_{1, 1-delta_U, theta}`."  `[.]` is `def:bracket` (`03:167--173`,
    SHA-256 `5A321B8B3577BC9AFB5E2C172C7FA375D046D50A81D490BBB1293F01FE34F99F`):
    "the family `[M]_{p,x,z}` consists of the submatrices of `Int_p(M)` that
    retain at least `ceil(m x)` rows in every outer block and at least
    `ceil(n^p z)` columns."  Vendored as `NPCC.bracketGE`, whose row clause is
    `NPCC.IsEquipartitionedGE RC.1 univ (ceil (card X * x))`.  At the wrapper's
    own copy count `p = 1` that clause is what `bracket_retained_card_ge` reads.
  * **`09:105--109`**: "Let `q = 2^r` be the scale-alignment width and set
    `U = Int_q(N)`.  Write `m = |Rows(N)|`."  So the rows of `U` are
    `Fin q x Rows(N)` and the frozen "outer coordinate" of `09:1233--1235` is the
    first component.  Every `q`-vs-`2^r` substitution below is this line.
  * **`09:112--118`**, the reference block:
    "`R_G = {base} x Omega x [w_0] subseteq Rows(N)`, `G = N|_{R_G x Cols(N)}`,
    `m_G = |Rows(G)|`, `g = m_G/m = 91/92`."  Sections 1--6 keep `R_G` as an
    arbitrary frozen row set `RG : Finset Rw` with `m_G = RG.card`, so nothing
    there depends on the reservoir's shape.  Section 7 instantiates it at the
    **banked** carriers: `ScaleAlignOpening.refIncl` is the frozen inclusion,
    `ScaleAlignOpening.card_refRows` gives `m_G`, and the identity
    `g = m_G/m = 91/92` is **consumed** from
    `ScaleAlignOpening.referenceG_row_mass` -- it is neither re-derived here nor
    arranged by a choice of integers.
  * **`09:1217--1222`**, the reference-row geometry: "For `k = 0, ..., r`, put
    `A_0 = ceil(2 x_T m_G)`, `A_k = 2^k A_0`."  **Banked** as
    `DenseWrapperFrontier.initialRefRows` and
    `DenseWrapperFrontier.refRowFloor`; consumed here **by pin** and restated
    nowhere.  `x_T = 2^{-b_T}` is `08:166` (SHA-256
    `E893848CA8BE218C44274084A2172D171D514039A25644C2B57FDA8A85A23774`), banked
    as `DenseStageFourOpening.xTdepth`.  No numeral is assigned to `A_0`
    anywhere below: Section 5 fires the definitional chain
    `A_0 = initialRefRows (xTdepth b_T) m_G` and Section 7 *evaluates* it.
  * **`eq:wrapper-initial-survival` (`09:1224--1232`)**, the three row-survival
    gates.  **Banked verbatim** as
    `DenseWrapperFrontier.wrapperInitialSurvival`.  Only its **second** clause
    `q A_0 + delta_U q m <= m_G` is used below, and it is used as the frozen
    inequality itself, never as a bundle field.
  * **`09:1233--1235`**, the retention: "Even if every deleted row of `U` were
    concentrated in one nonexceptional outer coordinate, that coordinate would
    therefore retain at least `A_r = q A_0` reference rows."  Its real-valued
    core is the banked `DenseWrapperFrontier.retainedRefRows_ge`; what this
    module adds is the two ends the banked lemma does not have -- the *deleted
    row count* on its left, obtained from the bracket's own row clause
    (Section 2), and the *cardinality* `refRowFloor A0 r <= (R i).card` on its
    right, which is the form `FrontierIndexing.canonicalSystem` and
    `RoutedCertificateConstruction.completedSystem` demand (Section 4).
  * **`09:1235--1236`**, "Start one clean reference certificate in every
    coordinate outside `E_0`, each with weight one" -- banked as
    `FrontierIndexing.canonicalSystem`; the *coordinate supply* it needs is what
    Section 6 hands `completedSystem_frontier_nonempty`.
* **Cross-anchors opened first-hand in the frozen files for this tranche:**
  * `06-parameter-schedule.tex` (SHA-256
    `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`):
    `06:513--519` (`eq:q-deltaU`, `q = 2^{A_wrap L_P^2}`,
    `delta_U = eta_R/(16 q)`), `06:547` ("We also impose the finite gate
    `delta_U <= 1/200`"), `06:226--233` (`0 < eta_R <= eta_C/2 < tau < x_N`),
    `06:875--887` (the schedule's own restatement of the three survival gates,
    `eq:parameter-wrapper-survival-gates`: "At the same materialisation point,
    put `A_0 = ceil(2 x_T m_G)` and check the three first-wrapper survival
    inequalities ... they are evaluated only after the integer row counts
    `m, m_G` are known"), `06:918` (`q x_T <= 4/25025`), and -- opened
    first-hand again this round for the `F-1` repair -- `06:237--244`
    (`k_T = log_2(s/4)`, `b_T = 2^{j_{49}(k_T)}`, `x_T = 2^{-b_T}`) with
    `06:264--268` (`eq:hard-seed-width-gates`, "`log_2 s < b_T`") and `06:1695`
    (`b_T >= L^{20}/C_size`).
  * `08:158--167` (`x_N = 1/16`, `x_T = 2^{-b_T}`).
  * `09:1238--1266` (the routing rule, the stopping rules and
    `eq:wrapper-frontier-conservation`) -- **banked, not restated**.
  * `09:1367--1384` (the protected reservoirs) -- **not entered**; the
    reservoirs remain GAP-EXPOSED item 2 of the predecessor.
* **Cited external interfaces.**  `EXPANDER-001` has **no** Lean declaration by
  design and appears in no hypothesis of this module.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, directly or transitively: the single import is
  `RoutedCertificateConstruction`, whose ledger row records the same exclusion.
* **Proof status:** new.  Every declaration is either a transcription of one of
  the frozen displays above, a general property of one of those transcriptions,
  or one of the frozen block's own counting steps carried out in the kernel.
  No mathematics is added and no schedule inequality is asserted.

## Reader counterpart: NONE claimable, and why

`routes/parameterized-np/reader-facing/sections/` was searched first-hand this
tranche for "retain", "reference row", "deleted row" and "survival".  The 41-page
reader artifact carries **no** item stating `09:1217--1236`.

* `reader 02-preliminaries.tex:63--75` is the reader's account of the bracket
  family's row clause ("retain at least `ceil(m x)` rows in each outer block").
  It is already the cited reader counterpart of
  `AliceOnlyHdensSupply.lean:318`, and the READER-COUNTERPART rule forbids
  assigning one reader item to two declarations, so it is **not** reused here.
* `reader 03-parameterized-construction.tex:220--242` is a *Stage 1* extraction
  count, not the wrapper retention, and states a different inequality.
* `reader A-stage4-details.tex:370--399` is the only passage covering this
  material at all; it is unnumbered running prose, and `370--373` are already
  recorded as unclaimed prose by `WRAPPER-PROJECTION-COVERS-001`.

So no reader item is cited rather than one invented, and the absence is recorded
as a finding about the reader artifact.

## What this tranche lands, and what it does not

The predecessor `RoutedCertificateConstruction` records, as **GAP-EXPOSED item
1**, that "the retention `hR` is not produced": `completedSystem` takes
`hR : forall i, refRowFloor A0 r <= (R i).card` as an explicit binder, exactly as
`canonicalSystem` does, and *"Producing the row sets `R : Coord -> Finset X` of
the retained matrix `U'` from its bracket membership, and the natural number
inequality `refRowFloor A0 r <= (R i).card` from the real one, is a matrix-side
step this module does not take."*  Its prescription is *"build `R` from `RC.1`'s
equipartition clause in `bracketGE` and bridge `retainedRefRows_ge` to the
cardinality form."*  That is precisely and only what this module does:

1. `retainedRefRows` **is** that `R`, read off `RC.1`: at outer coordinate `i` it
   is the set of retained rows of `U'` that lie in the `i`-th copy of the frozen
   reference block `R_G`.  It is a `Finset` of the alleged protocol's own row
   type `{a // a in RC.1}`, which is the row type of
   `subgame (interlaceFun (wrapperU N r) 1) RC.1 RC.2`.
2. `deletedRows_card_le_of_bracket` is the frozen "every deleted row of `U`"
   budget, `|deleted| <= delta_U q m`, derived from the bracket's own row
   clause -- not assumed.
3. `refRowFloor_le_retainedRefRows` is the bridge: the banked
   `retainedRefRows_ge` (a statement in `ℝ`) plus the counting inequality
   `m_G <= |retained at i| + |deleted|` give the **natural-number** conclusion
   `refRowFloor A0 r <= (retainedRefRows RC.1 RG i).card`.
4. `retentionSupply` is `hR` itself, and `retentionSupply_at_paper_A0` is the
   same statement with `A_0` **evaluated through its defining display**
   `A_0 = ceil(2 x_T m_G)` rather than left as a free natural.
5. `completedSystem_readouts_of_retention` is the **first `hR`-free consumer**:
   all five readouts of the predecessor's Section 6 -- the Kraft bound, the
   frontier nonemptiness, the two residual-budget contradictions and the
   first-Bob transfer -- hold at the retained matrix with **no retention
   hypothesis on the caller's side**.

**What is deliberately absent.**  `eq:wrapper-u-dense` (`09:1188`,
`09:1780--1781`) is neither stated nor implied anywhere below, and **no route
completion is claimed.**  The remaining GAP-EXPOSED items of the predecessor are
untouched and stay open: the protected reservoirs (`09:1367--1384`,
`09:1418--1531`), `Scol`/`ell`/`bsel`/`certOpt`, and the two calls (M-a), (M-b).
`A:285--329`, the stopping argument of `thm:certified-localized-extension`, is
**not attempted** and is reached from nothing below.  `hDenseRung` is neither
discharged nor fed further.

The second survival gate `q A_0 + delta_U q m <= m_G` stays an **explicit
binder**, never a premise bundle and never a structure field: the frozen text
puts its discharge in the parameter schedule (`06:875--887`, "evaluated only
after the integer row counts `m, m_G` are known"), which is GAP-EXPOSED item 6 of
`DenseWrapperFrontier` and is not landed.  The first and third clauses of
`eq:wrapper-initial-survival` are **not** hypotheses of anything below, because
`09:1233--1235` uses only the second.

## The two licensed audit repairs applied here (`F-1`, `F-3`)

Both were recorded as carried findings by the `cc-t6a` round and are **applied**
below; nothing outside Section 7's audit point and Section 8's probe moved.

**Provenance of these bytes (read before trusting any earlier pin).**  The
`F-1`/`F-3` repair round was authored, judged CLEAR, and then lost its workflow
before any commit; the judged bytes themselves no longer exist anywhere.  What
survives is the parked worktree of `wip/cc-t6b-orphan-postjudge`, whose
`RetentionSupply.lean` is a **superset** of the judged file by roughly sixty
lines of comment prose, plausibly the record-only repairs the judge licensed but
*not* verifiable by diff against the lost bytes.  Those parked bytes are the
starting point of the present file, and they were re-certified here from the
frozen sources rather than inherited: every anchor quoted in this header was
re-opened in the release source, every arithmetic consequence of `F-1` and `F-3`
was re-derived, and two further comment-only defects the earlier round left --
a census that misdescribed its own partition (Section 7) and one surviving
`R-4`-class citation on the `DecidableEq` instance -- were repaired.  **No pin
recorded before this certification describes this file**, and none should be
carried forward as though it did.  No statement, binder, conclusion or proof
term differs from the parked bytes.

**`F-1`, the depth's frozen shape.**  `06:241` reads `b_T = 2^{j_{49}(k_T)}`, so
the frozen `b_T` is a power of two, and the retired audit depth `14` is not one.
The audit now runs at `b_T = 16 = 2^4` (`audit_bT_shape`).  The four consequences
named in the finding were re-checked first-hand before the change.  At the
retired hand-built `m_G = 637` they hold exactly as recorded:
`A_0 = ceil(2 * 2^{-16} * 637) = ceil(1274/65536) = 1`, `A_r = 2^1 * 1 = 2`,
`q x_T = 2 * 2^{-16} = 2^{-15} = 1/32768 <= 4/25025` (since `4 * 32768 = 131072
>= 25025`), and the gate `2*1 + (1/640)*2*644 = 2 + 2.0125 <= 637`.  Under `F-3`
the numeral `637` is retired with the hand-built carrier, so the audit no longer
*can* state `A_0 = 1`: `A_0` is carried as the expression
`initialRefRows (xTdepth 16) m_G` with `0 < A_0` proved
(`audit_initialRefRows_pos`) and `A_r = 2 A_0` proved (`audit_refRowFloor`), and
the two carrier-free checks survive as `audit_bT_shape` and `audit_q_xT`.
`06:1695` (`b_T >= L^{20}/C_size`) is still not consulted; `06:267`
(`log_2 s < b_T`) is consulted at exactly one point, Section 7's non-vacuity
witness, where `F.s = 64 < 2^16`; and no statement asserts legality at
`b_T = 16`, which remains one of Section 7's self-chosen values.

**`F-3`, the reference geometry from the banked accessors.**  The retired audit
built `m = 644 = 92*7` and `m_G = 637 = 91*7` by hand, so `g = m_G/m = 91/92` was
an arithmetic coincidence of two chosen integers.  Section 7 now takes the
ambient row carrier to be the frozen `Rows(N) = Cols(A) = ProtColsFrozen`
(`N = A^T` is `08:147`; the cardinality `|Cols(A)| = 184 M_0 S_0 D_0` is
`08:110--122`) and the reference block to be the image of the banked
`ScaleAlignOpening.refIncl` (`09:113--114`), so:

* `auditRefRows_card_eq` reads `m_G` off the built carrier through
  `refIncl_injective`, and `auditRefRows_card` evaluates it through the banked
  `card_refRows` to `m_G = 182 K` with `K = M_0 S_0 D_0`;
* `auditRefRows_row_mass` **consumes** `ScaleAlignOpening.referenceG_row_mass`:
  `g = m_G/m = 91/92` is now a theorem about the built objects, not a chosen
  coincidence, and `audit_row_counts` records the same identity integrally as
  `92 m_G = 91 m`;
* the survival gate is proved for **every** legal `(F, q_2, Y)` at once
  (`audit_gate_arith` in the common scale `K`, then `audit_gate`), so no numeral
  for `m` or `m_G` enters anywhere.

The audit is therefore strictly stronger than the retired one -- it is universally
quantified over the schedule's carriers instead of standing at one invented pair
-- but it is **still BEYOND-PAPER**, and the canonical-inhabitation obligation
below is unchanged: the *other* half of the paper's instance, the bracket member
`U'` at the materialized schedule, is still unbuilt.

## Aux-lemma battery (all proved)

`deletedRows_card_add` (retained + deleted partition the ambient rows),
`deletedRows_univ`, `deletedRows_antitone`, `refBlock_card` (each coordinate
carries exactly `m_G` reference rows), `mem_retainedRefRows`,
`retainedRefRows_card_eq` (round trip between the protocol's row type and the
ambient one), `retainedRefRows_mono`, `retainedRefRows_disjoint`; and, for the
banked geometry of Section 7, `auditRefRows_card_eq`, `audit_row_counts` and
`audit_gate_arith` (the gate as pure arithmetic in the common scale, general in
`K`).  `audit_point_nonvacuous` is the LANE-GATE-3 inhabitant of Section 7's own
binder set: everything there is universally quantified over `(F, q_2, Y)`, and
that quantification is exhibited as nonvacuous at a concrete slot binding whose
carriers are inhabited and whose deleted count and row floor are strictly
positive.  Being an existential witness it necessarily *fixes* that point, and
the point it fixes is **schedule-illegal** at `06:124`; Section 7's own census
records which values it fixes and how they depart.  It is a **non-fidelity**
probe and does not touch the deferred canonical-inhabitation obligation below.

## Record finding carried forward (not repaired here)

`DenseWrapperFrontier.wrapperInitialSurvival_tier2_instance` satisfies the
three-clause predicate at `m = survivalWidth r eta_R` and
`m_G = survivalRefWidth r eta_R g` with `g` left free.  At e.g. `r = 1`,
`eta_R = 1`, `g = 91/92` those come out as `m = 64` and `m_G = 73`, so that
witness point has `m_G > m` and does **not** satisfy the frozen identity
`g = m_G/m` of `09:117`.  The predicate itself does not mention `m_G <= m`, so
nothing banked is false; but the tier-2 point is therefore **not** reusable as a
legal `(m, m_G)` pair, which is why Section 7 works at the banked carriers
instead.  Repairing the banked witness belongs to a `DenseWrapperFrontier`
tranche, not this one.

## Canonical inhabitation: REGISTERED and DEFERRED

The paper's own instance of `retainedRefRows` is the retained matrix `U'` of
`09:1188--1191` at the schedule's own materialized `(q, m, m_G, x_T, delta_U,
theta)`.  Two halves of that instance are unbuilt:

* the materialization itself (`06:859--862`, "Construct the one indexed
  `(q_2,t_2,eps_2)`-balanced family `C_2`, then materialise `M_2, M_3`, the
  source rows, and all protected multiplicities.  Only now do we evaluate the
  integer cardinalities"), which is `MATERIALIZE-001` on the Lean side; and
* the schedule's discharge of `eq:parameter-wrapper-survival-gates`
  (`06:875--887`), which is GAP-EXPOSED item 6 of `DenseWrapperFrontier`.

The **first** half is now expressible and is used: Section 7's row carrier and
reference block are the banked `ProtColsFrozen` and `refIncl` image, so the
audit's `(m, m_G)` is the schedule's own pair up to the unbuilt materialization,
and `g = 91/92` is consumed from `referenceG_row_mass` rather than arranged.  The
**second** half -- the bracket member `U'` of `09:1188--1191` at the materialized
schedule -- is still unbuilt.

The canonical-inhabitation obligation for `retainedRefRows` is therefore
**registered and still deferred**: it is discharged when the materialization
lands, and is **never** satisfied by the probe of Section 7.  Section 7 is an
explicitly labelled **BEYOND-PAPER legality audit**: it claims no fidelity, and it
exists only to show that the hypothesis bundle of Sections 4--6 is satisfiable, at
values honouring the frozen identities tabulated in that section
(`g = m_G/m = 91/92` consumed, `delta_U = eta_R/(16q)`, `delta_U <= 1/200`,
`eta_R < x_N = 1/16`, `q = 2^r`, `b_T` a power of two, `q x_T <= 4/25025`,
`A_0 = ceil(2 x_T m_G)`), with a strictly positive deleted-row count and a
strictly positive row floor.  It does **not** honour every frozen constraint
bearing on its three remaining self-chosen values (`r`, `b_T`, `eta_R`), and does
not claim to: `06:241` fixes `b_T` from `k_T = log_2(s/4)` through the
unformalized `j_{49}`, and `06:267`/`06:1695` are not consulted.  Section 8 is a
rejection probe showing the survival gate is load-bearing.
-/

namespace EthInapproximability.ParameterizedNP.RetentionSupply

open NPCC
open Workspace.Types.Protocol
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.ScaleAlignOpening
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction

/-! ## §1  "every deleted row of `U`" (`09:1233`)

The frozen sentence quantifies over the rows of `U` that the retained matrix
`U'` drops.  That set is the complement of the bracket member's row set inside
the interlace's rows; nothing else about it is used. -/

section Deleted

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`09:1233`.**  The deleted rows of `U` at the retained row set `Rset`. -/
def deletedRows (Rset : Finset ι) : Finset ι := Finset.univ \ Rset

@[simp] theorem mem_deletedRows {Rset : Finset ι} {a : ι} :
    a ∈ deletedRows Rset ↔ a ∉ Rset := by
  simp [deletedRows]

/-- **Aux D1.**  Retained and deleted rows partition the ambient row set.
General. -/
theorem deletedRows_card_add (Rset : Finset ι) :
    (deletedRows Rset).card + Rset.card = Fintype.card ι := by
  rw [deletedRows, ← Finset.card_univ (α := ι)]
  exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)

/-- **Aux D2.**  Retaining everything deletes nothing.  General. -/
@[simp] theorem deletedRows_univ : deletedRows (Finset.univ : Finset ι) = ∅ := by
  simp [deletedRows]

/-- **Aux D3.**  Retaining more deletes less: the deleted set is antitone in the
retained set.  General. -/
theorem deletedRows_antitone {R₁ R₂ : Finset ι} (h : R₁ ⊆ R₂) :
    deletedRows R₂ ⊆ deletedRows R₁ := by
  intro a ha
  rw [mem_deletedRows] at ha ⊢
  exact fun hc => ha (h hc)

end Deleted

/-! ## §2  The deletion budget from the bracket (`09:1188--1191`, `03:167--173`)

`def:bracket` demands `ceil(m x)` retained rows in every outer block.  At the
wrapper's copy count `p = 1` there is one block, so the clause is a bound on the
whole retained row set, and the deleted rows are what is left over. -/

section Budget

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

omit [DecidableEq X] in
/-- **`03:167--173` at `p = 1`.**  The bracket's row clause, read as a lower
bound on the retained row count.  The clause is `IsEquipartitionedGE` over the
one block of the one-copy interlace, and a block filter is a subset of the row
set, so the frozen `ceil(m x)` bounds the whole of `RC.1`.  General. -/
theorem bracket_retained_card_ge {x y : ℝ}
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hRC : RC ∈ bracketGE X Y 1 x y) :
    ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ RC.1.card :=
  le_trans (hRC.1 0 (Finset.mem_univ _)) (Finset.card_le_card (Finset.filter_subset _ _))

/-- **`09:1233` with `09:1188--1191`.**  The frozen deletion budget: a member of
`[U]_{1, 1-delta_U, theta}` deletes at most `delta_U m_U` rows of `U`, where
`m_U` is the ambient row count of the one-copy interlace.  At the wrapper this
reads `|deleted| <= delta_U q m`, which is the left-hand input of
`DenseWrapperFrontier.retainedRefRows_ge`.  General in `X`, `Y` and `delta_U`. -/
theorem deletedRows_card_le_of_bracket {δU θ : ℝ}
    {RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y)}
    (hRC : RC ∈ bracketGE X Y 1 (1 - δU) θ) :
    ((deletedRows RC.1).card : ℝ) ≤ δU * (Fintype.card X : ℝ) := by
  have hcardι : Fintype.card (Fin 1 × X) = Fintype.card X := by simp
  have hadd := deletedRows_card_add RC.1
  have hge : ((⌈(Fintype.card X : ℝ) * (1 - δU)⌉₊ : ℕ) : ℝ) ≤ (RC.1.card : ℝ) := by
    exact_mod_cast bracket_retained_card_ge hRC
  have hceil : (Fintype.card X : ℝ) * (1 - δU) ≤ (RC.1.card : ℝ) :=
    le_trans (Nat.le_ceil _) hge
  have haddR : ((deletedRows RC.1).card : ℝ) + (RC.1.card : ℝ) = (Fintype.card X : ℝ) := by
    rw [← hcardι]
    exact_mod_cast hadd
  nlinarith [hceil, haddR]

end Budget

/-! ## §3  The reference rows in one outer coordinate (`09:105--118`, `09:1233--1235`)

`U = Int_q(N)` has rows `Fin q x Rows(N)` (`09:105--109`), and the frozen
reference block is `R_G subseteq Rows(N)` with `m_G = |R_G|` (`09:112--118`).  So
the reference rows of `U` in outer coordinate `i` are the `i`-th copy of `R_G`,
and the *retained* ones are those the bracket member keeps. -/

section RefRows

variable {Rw : Type*} [Fintype Rw] [DecidableEq Rw] {q : ℕ}

/-- **`09:105--118`.**  The reference rows of `U = Int_q(N)` in outer coordinate
`i`: the `i`-th copy of the frozen reference block `R_G`, inside the rows of the
one-copy interlace of `U`. -/
def refBlock (RG : Finset Rw) (i : Fin q) : Finset (Fin 1 × (Fin q × Rw)) :=
  Finset.univ.filter (fun a => a.2.1 = i ∧ a.2.2 ∈ RG)

/-- **Aux R1 (`09:116`, `m_G = |Rows(G)|` is per coordinate).**  Each outer
coordinate carries exactly `m_G` reference rows.  General. -/
theorem refBlock_card (RG : Finset Rw) (i : Fin q) : (refBlock RG i).card = RG.card := by
  have hinj : Function.Injective (fun x : Rw => ((0 : Fin 1), (i, x))) := by
    intro x y hxy
    simpa using hxy
  have himg : refBlock RG i = RG.image (fun x : Rw => ((0 : Fin 1), (i, x))) := by
    ext ⟨a₁, a₂, a₃⟩
    simp only [refBlock, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, h₃⟩
      exact ⟨a₃, h₃, Subsingleton.elim _ _, rfl, rfl⟩
    · rintro ⟨x, hx, -, h₂, h₃⟩
      subst h₂
      subst h₃
      exact ⟨rfl, hx⟩
  rw [himg, Finset.card_image_of_injective _ hinj]

/-- **`09:1233--1235`, the row sets the frozen argument places its certificates
on.**  `R i` is the set of *retained* reference rows in outer coordinate `i`,
living in the alleged protocol's own row type `{a // a in Rset}`.

This is the `R : Coord -> Finset X` that `FrontierIndexing.canonicalSystem` and
`RoutedCertificateConstruction.completedSystem` take, produced from the bracket
member rather than assumed. -/
def retainedRefRows (Rset : Finset (Fin 1 × (Fin q × Rw))) (RG : Finset Rw) (i : Fin q) :
    Finset {a // a ∈ Rset} :=
  Rset.attach.filter (fun a => a.val.2.1 = i ∧ a.val.2.2 ∈ RG)

omit [Fintype Rw] in
/-- **Aux R2 (membership).**  A retained row is a reference row of coordinate `i`
exactly when its outer coordinate is `i` and its inner row lies in `R_G`.
General. -/
@[simp] theorem mem_retainedRefRows {Rset : Finset (Fin 1 × (Fin q × Rw))}
    {RG : Finset Rw} {i : Fin q} {a : {a // a ∈ Rset}} :
    a ∈ retainedRefRows Rset RG i ↔ a.val.2.1 = i ∧ a.val.2.2 ∈ RG := by
  simp [retainedRefRows]

/-- **Aux R3 (round trip to the ambient row type).**  Counting retained
reference rows inside the protocol's row type is the same as intersecting the
retained row set with the coordinate's reference block.  General. -/
theorem retainedRefRows_card_eq (Rset : Finset (Fin 1 × (Fin q × Rw)))
    (RG : Finset Rw) (i : Fin q) :
    (retainedRefRows Rset RG i).card = (Rset ∩ refBlock RG i).card := by
  rw [← Finset.card_image_of_injective (retainedRefRows Rset RG i) Subtype.val_injective]
  congr 1
  ext a
  simp only [Finset.mem_image, mem_retainedRefRows, Finset.mem_inter, refBlock,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, ⟨hb₁, hb₂⟩, rfl⟩
    exact ⟨b.2, hb₁, hb₂⟩
  · rintro ⟨hmem, h₁, h₂⟩
    exact ⟨⟨a, hmem⟩, ⟨h₁, h₂⟩, rfl⟩

omit [Fintype Rw] in
/-- **Aux R4 (monotone in the reference block).**  Enlarging `R_G` can only
enlarge the retained reference rows.  General. -/
theorem retainedRefRows_mono (Rset : Finset (Fin 1 × (Fin q × Rw)))
    {RG RG' : Finset Rw} (h : RG ⊆ RG') (i : Fin q) :
    retainedRefRows Rset RG i ⊆ retainedRefRows Rset RG' i := by
  intro a ha
  rw [mem_retainedRefRows] at ha ⊢
  exact ⟨ha.1, h ha.2⟩

omit [Fintype Rw] in
/-- **Aux R5 (`09:1235--1236`, one certificate per coordinate).**  Distinct outer
coordinates carry disjoint reference-row sets -- the reason "one clean reference
certificate in every coordinate" is a family of *distinct* certificates.
General. -/
theorem retainedRefRows_disjoint (Rset : Finset (Fin 1 × (Fin q × Rw)))
    (RG : Finset Rw) {i j : Fin q} (hij : i ≠ j) :
    Disjoint (retainedRefRows Rset RG i) (retainedRefRows Rset RG j) := by
  rw [Finset.disjoint_left]
  intro a hi hj
  rw [mem_retainedRefRows] at hi hj
  exact hij (hi.1 ▸ hj.1 ▸ rfl)

/-- **`09:1233--1235`, the concentration step, as a count.**  "Even if every
deleted row of `U` were concentrated in one nonexceptional outer coordinate":
whatever the deletion pattern, a coordinate's `m_G` reference rows are either
retained there or deleted.  General. -/
theorem refCard_le_retained_add_deleted (Rset : Finset (Fin 1 × (Fin q × Rw)))
    (RG : Finset Rw) (i : Fin q) :
    RG.card ≤ (retainedRefRows Rset RG i).card + (deletedRows Rset).card := by
  rw [retainedRefRows_card_eq, ← refBlock_card RG i]
  have hsub : refBlock RG i ⊆ (Rset ∩ refBlock RG i) ∪ deletedRows Rset := by
    intro a ha
    by_cases h : a ∈ Rset
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, ha⟩)
    · exact Finset.mem_union_right _ (mem_deletedRows.mpr h)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

end RefRows

/-! ## §4  The bridge to the cardinality form (`09:1233--1235`)

`DenseWrapperFrontier.retainedRefRows_ge` is the frozen sentence's real-valued
core, `q A_0 <= m_G - deleted`, and takes both `deleted` and `m_G` as free reals.
Here `deleted` is the bracket's own deletion budget (§2) and `m_G` is the actual
reference-row count, so the conclusion becomes the **natural-number** inequality
`FrontierIndexing.canonicalSystem` demands. -/

section Bridge

variable {Rw : Type*} [Fintype Rw] [DecidableEq Rw]

/-- **`09:1233--1235` in the form the routed system consumes.**

At the wrapper width `q = 2^r` (`09:105`), from
* the bracket membership of the retained matrix `U'` (`09:1188--1191`), and
* the **second** clause of `eq:wrapper-initial-survival` (`09:1228`),
  `q A_0 + delta_U q m <= m_G`,

every outer coordinate retains at least `A_r = q A_0 = refRowFloor A_0 r`
reference rows.  The banked `DenseWrapperFrontier.retainedRefRows_ge` supplies
the real inequality and is not restated; `refRowFloor A_0 r = 2^r A_0` is the
banked `09:1221` and is not re-derived. -/
theorem refRowFloor_le_retainedRefRows {Cl : Type*} [Fintype Cl] {r A0 : ℕ} {δU θ : ℝ}
    {RC : Finset (Fin 1 × (Fin (2 ^ r) × Rw)) × Finset (Fin 1 → (Fin (2 ^ r) → Cl))}
    (RG : Finset Rw)
    (hRC : RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)
    (hgate : ((2 ^ r : ℕ) : ℝ) * (A0 : ℝ)
        + δU * ((2 ^ r : ℕ) : ℝ) * ((Fintype.card Rw : ℕ) : ℝ) ≤ ((RG.card : ℕ) : ℝ))
    (i : Fin (2 ^ r)) :
    refRowFloor A0 r ≤ (retainedRefRows RC.1 RG i).card := by
  have hcard : ((Fintype.card (Fin (2 ^ r) × Rw) : ℕ) : ℝ)
      = ((2 ^ r : ℕ) : ℝ) * ((Fintype.card Rw : ℕ) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hdel : ((deletedRows RC.1).card : ℝ)
      ≤ δU * ((2 ^ r : ℕ) : ℝ) * ((Fintype.card Rw : ℕ) : ℝ) := by
    have hb := deletedRows_card_le_of_bracket hRC
    rw [hcard] at hb
    linarith [hb]
  have hret := retainedRefRows_ge (q := 2 ^ r) (m := Fintype.card Rw) (mG := RG.card)
    (A0 := A0) (deltaU := δU) (deleted := ((deletedRows RC.1).card : ℝ)) hgate hdel
  have hcount : ((RG.card : ℕ) : ℝ)
      ≤ ((retainedRefRows RC.1 RG i).card : ℝ) + ((deletedRows RC.1).card : ℝ) := by
    exact_mod_cast refCard_le_retained_add_deleted RC.1 RG i
  have hfloor : ((refRowFloor A0 r : ℕ) : ℝ) = ((2 ^ r : ℕ) : ℝ) * (A0 : ℝ) := by
    rw [refRowFloor]
    push_cast
    ring
  have hfinal : ((refRowFloor A0 r : ℕ) : ℝ) ≤ ((retainedRefRows RC.1 RG i).card : ℝ) := by
    rw [hfloor]
    linarith
  exact_mod_cast hfinal

/-- **GAP-EXPOSED item 1 of `RoutedCertificateConstruction`, discharged.**

This is the retention `hR` that `FrontierIndexing.canonicalSystem` and
`RoutedCertificateConstruction.completedSystem` take as a binder, now *produced*
from the retained matrix's own bracket membership together with the second
survival gate.  `A_0` is still a free natural here; Section 5 fires the
definitional chain that fixes it. -/
theorem retentionSupply {Cl : Type*} [Fintype Cl] {r A0 : ℕ} {δU θ : ℝ}
    {RC : Finset (Fin 1 × (Fin (2 ^ r) × Rw)) × Finset (Fin 1 → (Fin (2 ^ r) → Cl))}
    (RG : Finset Rw)
    (hRC : RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)
    (hgate : ((2 ^ r : ℕ) : ℝ) * (A0 : ℝ)
        + δU * ((2 ^ r : ℕ) : ℝ) * ((Fintype.card Rw : ℕ) : ℝ) ≤ ((RG.card : ℕ) : ℝ)) :
    ∀ i : Fin (2 ^ r), refRowFloor A0 r ≤ (retainedRefRows RC.1 RG i).card :=
  fun i => refRowFloor_le_retainedRefRows RG hRC hgate i

end Bridge

/-! ## §5  `A_0` through its defining display (`09:1219`, `08:166`)

`09:1219` **defines** `A_0 = ceil(2 x_T m_G)` and `08:166` **defines**
`x_T = 2^{-b_T}`.  Neither is a free input, so the supply is fired at the value
the definitional chain produces -- the banked
`DenseWrapperFrontier.initialRefRows` evaluated at the banked
`DenseStageFourOpening.xTdepth` and at the actual reference-row count `m_G`.
No numeral is assigned. -/

section PaperA0

variable {Rw : Type*} [Fintype Rw] [DecidableEq Rw]

/-- **`09:1219` with `08:166`, fired.**  The retention supply at the paper's own
`A_0 = ceil(2 x_T m_G)`, `x_T = 2^{-b_T}`.  The reference-row count `m_G` is the
cardinality of the actual reference block, so both ends of the defining display
are the construction's own data. -/
theorem retentionSupply_at_paper_A0 {Cl : Type*} [Fintype Cl] {r bT : ℕ} {δU θ : ℝ}
    {RC : Finset (Fin 1 × (Fin (2 ^ r) × Rw)) × Finset (Fin 1 → (Fin (2 ^ r) → Cl))}
    (RG : Finset Rw)
    (hRC : RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)
    (hgate : ((2 ^ r : ℕ) : ℝ) * ((initialRefRows (xTdepth bT) RG.card : ℕ) : ℝ)
        + δU * ((2 ^ r : ℕ) : ℝ) * ((Fintype.card Rw : ℕ) : ℝ) ≤ ((RG.card : ℕ) : ℝ)) :
    ∀ i : Fin (2 ^ r),
      refRowFloor (initialRefRows (xTdepth bT) RG.card) r
        ≤ (retainedRefRows RC.1 RG i).card :=
  retentionSupply RG hRC hgate

end PaperA0

/-! ## §6  The first `hR`-free consumer (`09:1233--1266`, `09:1306--1343`)

All five readouts of `RoutedCertificateConstruction`'s Section 6 are stated over
an arbitrary alleged protocol but still carry the retention as a binder.  With
§4 in hand they hold at the retained matrix outright.  The coordinate the
frontier-nonemptiness readout needs is *supplied* here (`q = 2^r >= 1`), not
assumed. -/

section Consumer

variable {Rw : Type*} [Fintype Rw] [DecidableEq Rw]

/-- **`09:1233--1266` and `09:1306--1343` at the retained matrix, with no
retention hypothesis.**

The frozen frame of `09:1188--1193` fixes a retained matrix `U'` in the bracket
family and an alleged protocol `P` for it of cost at most `C+r-1`.  Every one of
the predecessor's five walked-system readouts is available at that frame:

1. `eq:wrapper-frontier-conservation`'s second clause (`09:1264`),
   `sum_v kappa_v <= q`;
2. `09:1235--1236`, the frontier is nonempty -- the started coordinate is
   supplied by `q = 2^r >= 1`, not assumed;
3. `09:1341--1343`, the final-node residual budget;
4. `09:1306--1308`, the first-Bob residual budget;
5. `09:1197--1198`, every walked first-Bob address is a first-Bob address of the
   **original** alleged protocol.

Nothing here asserts, implies, or approaches `eq:wrapper-u-dense`. -/
theorem completedSystem_readouts_of_retention {Cl : Type*} [Fintype Cl]
    {r A0 C : ℕ} {δU θ : ℝ}
    {RC : Finset (Fin 1 × (Fin (2 ^ r) × Rw)) × Finset (Fin 1 → (Fin (2 ^ r) → Cl))}
    (RG : Finset Rw)
    (hRC : RC ∈ bracketGE (Fin (2 ^ r) × Rw) (Fin (2 ^ r) → Cl) 1 (1 - δU) θ)
    (hgate : ((2 ^ r : ℕ) : ℝ) * (A0 : ℝ)
        + δU * ((2 ^ r : ℕ) : ℝ) * ((Fintype.card Rw : ℕ) : ℝ) ≤ ((RG.card : ℕ) : ℝ))
    (P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (hC : 1 ≤ C) (hcost : P.cost ≤ C + r - 1) :
    (∑ v : FrontierNode (completeNoBob r P) (retainedRefRows RC.1 RG) A0 r,
          stoppingCapacity r v.val.length ≤ 2 ^ r)
      ∧ (frontierRoutes (completeNoBob r P) (retainedRefRows RC.1 RG) A0 r).Nonempty
      ∧ (∀ v : FrontierNode (completeNoBob r P) (retainedRefRows RC.1 RG) A0 r,
          (completedSystem P (retentionSupply RG hRC hgate)).firstBob v = false →
            (descend (completeNoBob r P)
                ((completedSystem P (retentionSupply RG hRC hgate)).node v)).cost + r
              ≤ C + r - 1)
      ∧ (∀ v : FrontierNode (completeNoBob r P) (retainedRefRows RC.1 RG) A0 r,
          (completedSystem P (retentionSupply RG hRC hgate)).firstBob v = true →
            (descend (completeNoBob r P)
                ((completedSystem P (retentionSupply RG hRC hgate)).node v)).cost
              + ((completedSystem P (retentionSupply RG hRC hgate)).node v).length
              ≤ C + r - 1)
      ∧ (∀ v : FrontierNode (completeNoBob r P) (retainedRefRows RC.1 RG) A0 r,
          (completedSystem P (retentionSupply RG hRC hgate)).firstBob v = true →
            IsFirstBobNode P r
              ((completedSystem P (retentionSupply RG hRC hgate)).node v)) :=
  ⟨completedSystem_sum_capacity_le_width P (retentionSupply RG hRC hgate),
    completedSystem_frontier_nonempty (R := retainedRefRows RC.1 RG) (A0 := A0) P
      ⟨0, Nat.two_pow_pos r⟩,
    fun _ hv => completedSystem_final_residual_budget P (retentionSupply RG hRC hgate) hC hcost hv,
    fun _ hv =>
      completedSystem_firstBob_residual_budget P (retentionSupply RG hRC hgate) hC hcost hv,
    fun _ hv => completedSystem_firstBob_of_original P (retentionSupply RG hRC hgate) hv⟩

end Consumer

/-! ## §7  BEYOND-PAPER legality audit at the **banked** reference geometry
(claims **no** fidelity)

This section claims **no** legality for the frozen construction.  The paper's own
retained matrix `U'` is materialized in `06:859--887` and is not available in
Lean; the canonical-inhabitation obligation for `retainedRefRows` is registered
and deferred above and is **not** discharged here.

What is audited is that our encoding of §§2--6 is satisfiable, with a strictly
positive deleted-row count and a strictly positive row floor, at the **banked**
reference geometry of `09:112--118` -- *not* at a hand-picked pair of numerals.
The ambient row carrier is the frozen `Rows(N) = Cols(A) = ProtColsFrozen`
(the identity `N = A^T` is `08:147`; the cardinality `|Cols(A)| = 184 M_0 S_0 D_0`
is `08:110--122`) and the reference block is the image of the banked
`ScaleAlignOpening.refIncl`, so `m` and `m_G` are **read off the built carriers**
and the frozen `g = m_G/m = 91/92` of `09:117` is a **consumed theorem**
(`ScaleAlignOpening.referenceG_row_mass`), not an arithmetic coincidence of two
chosen integers:

| symbol | frozen source | audit value |
| --- | --- | --- |
| `q = 2^r` | `09:105` | `r = 1`, `q = 2` |
| `Rows(N) = Cols(A)` | `08:147`, `08:110--122` | banked `ProtColsFrozen F q_2 Y` |
| `R_G = {base} x Omega x [w_0]` | `09:113--114` | banked `refIncl` image |
| `m_G = card Rows(G)` | `09:116` | banked `card_refRows`, **evaluated** |
| `g = m_G/m = 91/92` | `09:117` | banked `referenceG_row_mass`, **consumed** |
| `0 < eta_R <= eta_C/2 < tau < x_N` | `06:228`, `06:132` | **DEPARTURE**: `1/20 > tau = 1/92` |
| `delta_U = eta_R/(16 q)` | `06:517` | **evaluated**: `auditDeltaU` |
| `delta_U <= 1/200` | `06:547` | checked by `auditEtaR_legal` |
| `b_T = 2^{j_{49}(k_T)}` | `06:241` | `b_T = 16 = 2^4`, shape checked |
| `x_T = 2^{-b_T}` | `08:166` | banked `xTdepth 16` |
| `q x_T <= 4/25025` | `06:918` | checked by `audit_q_xT` |
| `A_0 = ceil(2 x_T m_G)` | `09:1219` | **evaluated**: `initialRefRows` |
| `theta = delta/(16 Q)` | `06:533` | **left free** over `(0,1]`, but see below |

Nothing in the last six rows is assigned a numeral.  `auditDeltaU` evaluates
`06:517` at `auditEtaR` and `q = 2^1`; `A_0` is carried through the whole section
as the *expression* `initialRefRows (xTdepth 16) (auditRefRows F q_2 Y).card`,
with only its **positivity** and the identity `A_r = 2 A_0` proved, because at
the banked carriers `m_G` is not a numeral; `theta` stays universally quantified
over its frozen legal range, so the schedule's own value is covered by
instantiation.

**The column axis is not exercised, and `theta`'s freedom is therefore cheap.**
The audit fixes the column carrier at `Cl = Fin 1`, so the bracket's column type
`Fin (2^1) -> Fin 1` is a **singleton**.  `def:bracket`'s column clause
(`03:172`, `ceil(n^p z)` retained columns) then collapses to `ceil(theta) <= 1`,
i.e. to `theta <= 1` alone, and `audit_mem_bracket` discharges it by
`hθ₁` without ever touching `theta`'s lower guard.  So this audit exercises the
**row** clause only: no column-axis strength may be read into `audit_mem_bracket`
or into anything downstream of it, and the universal quantification over `theta`
buys nothing on the column side.

**What is still self-chosen, and why this is still BEYOND-PAPER.**  The census
below is complete for this section; it is in **three** parts, because the
section's declarations split into three kinds by what they quantify over.  (An
earlier draft of this census described the first two parts as one and called all
of them "quantified over `(F, q_2, Y)`"; that was false of the six carrier-free
declarations, and a census that certifies its own completeness must not
misdescribe its own partition.)

*The carrier-free arithmetic* -- `auditEtaR`, `auditDeltaU`, `auditEtaR_legal`,
`audit_bT_shape`, `audit_q_xT`, `audit_gate_arith` -- mentions `(F, q_2, Y)`
nowhere.  Five are closed; `audit_gate_arith` is universally quantified over the
common scale `K >= 1`.  These fix the wrapper width exponent `r = 1`, the depth
`b_T = 16` and the reference mass `eta_R = 1/20`.

* **`eta_R = 1/20` is schedule-illegal, and this is a departure, not an
  honoured identity.**  `06:228` reads in full `0 < eta_R <= eta_C/2 < tau < x_N`
  and `06:132` fixes `tau = 1/92`, so the frozen chain forces `eta_R < 1/92`.
  The audit's `1/20` exceeds `tau`.  `auditEtaR_legal` asserts only the weaker
  box `0 < eta_R < 1/16` (`08:164`) plus `delta_U <= 1/200` (`06:547`) and
  claims no legality; its name records a weaker certificate than the chain.
  **Consequence for the satisfiability evidence.**  Because `06:517` evaluates
  `delta_U = eta_R/(16 q)`, this audit runs at `delta_U = 1/640`, whereas a
  chain-legal `eta_R < 1/92` would force `delta_U < 1/2944`.  The slack is
  benign in direction -- a larger `delta_U` makes `audit_gate` *harder* (still
  proved for all `K >= 1`) and `audit_mem_bracket` *easier* -- but the audit's
  satisfiability at `delta_U = 1/640` does **not** transfer verbatim to the
  chain-legal `delta_U`: the row clause would then require `n >= 1472`, i.e.
  common scale `K >= 8`, where `audit_ambient_card_ge` supplies only `K >= 2`.
  A later tranche must not assume this audit already covers the legal
  `delta_U`.

*The carrier-quantified lemmas* -- `auditRefRows` through
`audit_readouts_available` -- are universally quantified over `(F, q_2, Y)` with
only the frozen guards (`0 < q_2` or `2 <= q_2`, and an inhabited seed carrier),
over the deleted ambient row `x_0`, and over `theta in (0,1]`.  They inherit
`r = 1`, `b_T = 16`, `eta_R = 1/20` from the first part and add exactly one
further choice: `audit_readouts_available` fixes `C = 1`.  The frozen frame runs
at `C >= 3` (`09:1302`); the statement asserts only `1 <= C`, which is the binder
`completedSystem_readouts_of_retention` actually takes.

`b_T = 16` now honours the frozen *shape* `b_T = 2^{j_{49}(k_T)}` of `06:241`
(`audit_bT_shape`) and the frozen `q x_T <= 4/25025` of `06:918` (`audit_q_xT`);
it is nonetheless self-chosen, because `06:241` fixes `b_T` from
`k_T = log_2(s/4)` through `j_{49}`, which is not formalized, and neither of the
first two parts constrains `F.s`.  `06:1695` (`b_T >= L^{20}/C_size`) is not
consulted anywhere in the module.

*The closing existential* `audit_point_nonvacuous` is different in kind: being a
non-vacuity witness it must **fix** a point, so the sentence "no statement below
fixes the schedule's own scale" would be false of it.  It fixes `F.a = 3`,
`F.s = 64`, `q_2 = 2`, `Y = Fin 1` and `theta = 1`.  Two of those departures are
worth naming, because the statement itself discloses neither:

* **`q_2 = 2` is schedule-illegal at `F.s = 64`.**  `06:124` fixes `q_2` as "the
  least power of two at least `12 s N_E`", which at `s = 64` is at least `768`.
  The theorem asserts only its own hypothesis `2 <= q_2` and claims no legality,
  but the point is one the schedule could never reach.
* **`06:266`/`06:267` are consulted there, and only there.**  That witness
  asserts `16 | (s/4)` and `log_2 s < b_T` as conclusions at `F.s = 64`,
  `b_T = 16`.  The third clause of `eq:hard-seed-width-gates`, `k_T >= m_HS`,
  quantifies over the unformalized `HSThreshold` and is not asserted; and since
  `06:124` is violated at the same point, clearing two of three checkable clauses
  is **not** a legality claim and must not be recorded as one.

Every declaration of this section is BEYOND-PAPER, and none asserts that its own
point is schedule-legal. -/

/-- Decidable equality on the frozen protected column carrier
`Cols(A) = ProtColsFrozen`.  The three-summand *shape* of `Cols(A)` is
`eq:protected-labelled-carriers` at `08:83--87`, not `08:110--122`, which is
`eq:protected-carrier-cardinalities` and gives only the two cardinalities; this
is the `R-4` citation class, repaired here at the one occurrence the round's
earlier sweep missed.  Spelled out because the nested
sum-of-products defeats the default instance search; it is nothing but the core
`Sum`/`Prod`/`Pi` instance chain, carries no mathematical content, and is
`local` so nothing downstream inherits it. -/
local instance instDecidableEqProtColsFrozen (F : FiniteSlots.Stage1SlotBinding)
    (q₂ : ℕ) (Y : Type*) [Fintype Y] [DecidableEq Y] :
    DecidableEq (ProtColsFrozen F q₂ Y) :=
  @instDecidableEqSum _ _ _ (@instDecidableEqSum _ _ _ _)

section Audit

/-- The audit's reference mass.  `eta_R` is one of the three values this section
chooses for itself, and it is a **disclosed departure** from the frozen chain,
not a value the chain permits.  `06:228` reads in full

    0 < eta_R <= eta_C/2 < tau < x_N,

and `06:132` fixes `tau = 1/92`, so the frozen constraint is `eta_R < 1/92`,
strictly stronger than the `eta_R < x_N = 1/16` of `08:164`.  This audit's
`eta_R = 1/20 = 0.05` **exceeds** `tau`, so it is schedule-illegal; the section
claims no legality for it (see the departures census in the §7 preamble).
`auditEtaR_legal` checks only the weaker box `0 < eta_R < 1/16` together with
the `delta_U` gate, and asserts nothing about the frozen chain. -/
noncomputable def auditEtaR : ℝ := 1 / 20

/-- **`eq:q-deltaU` (`06:517`) evaluated, not assigned.**
`delta_U = eta_R/(16 q)` at the audit's `eta_R` and at `q = 2^1`.  The numeral
`1/640` is nowhere written: it is what this definitional chain computes. -/
noncomputable def auditDeltaU : ℝ := auditEtaR / (16 * (2 : ℝ) ^ 1)

/-- A **strictly weaker box than the frozen chain**: this certifies only
`0 < eta_R < x_N = 1/16` (`08:164`) together with `delta_U <= 1/200` (`06:547`),
where `delta_U` is what the defining display `06:517` produces at this `eta_R`.

It does **not** certify the frozen chain `0 < eta_R <= eta_C/2 < tau < x_N` of
`06:228` with `tau = 1/92` (`06:132`), which this audit's `eta_R = 1/20`
violates.  Nothing here may be recorded as schedule legality for `eta_R`. -/
theorem auditEtaR_legal :
    0 < auditEtaR ∧ auditEtaR < 1 / 16 ∧ 0 < auditDeltaU ∧ auditDeltaU ≤ 1 / 200 := by
  refine ⟨by norm_num [auditEtaR], by norm_num [auditEtaR], ?_, ?_⟩ <;>
    norm_num [auditDeltaU, auditEtaR]

/-- **`06:241`, the frozen shape of `b_T`, honoured by the audit's depth.**
"`b_T = 2^{j_{49}(k_T)}`" makes `b_T` a power of two; the audit's `b_T = 16` is
`2^4`.  This records the shape check only -- the schedule's own `b_T` is fixed
from `k_T = log_2(s/4)` through `j_{49}`, which is not formalized, so `16` is
still a self-chosen depth.

As a *statement* this is a closed numeral identity: it mentions neither `b_T` nor
`xTdepth` nor any other object of this module, so it has no formal tie to the
audit point and must **not** be recorded, here or in the ledger, as a
verification that the audit depth satisfies `06:241`.  The substantive content of
the `F-1` repair is elsewhere -- that `xTdepth 16`, and never `xTdepth 14`, is
the depth every declaration of this section actually uses. -/
theorem audit_bT_shape : (16 : ℕ) = 2 ^ 4 := by norm_num

/-- **`06:918` at the audit's width and depth.**  "the bounds `lambda_T >= 99/100`,
`s <= q` and `q x_T <= 4/25025` imply these comparisons with slack": at `q = 2^1`
and `x_T = 2^{-16}` the frozen bound reads `2^{-15} <= 4/25025` and holds. -/
theorem audit_q_xT : ((2 ^ 1 : ℕ) : ℝ) * xTdepth 16 ≤ 4 / 25025 := by
  norm_num [xTdepth]

/-- **Aux A1 (the gate as pure arithmetic in the common scale).**  At the banked
carriers both row counts are multiples of one scale `K = M_0 S_0 D_0`:
`m_G = 182 K` and `m = 184 K` (`08:110--122` with `08:100`).  The **second**
clause of `eq:wrapper-initial-survival` (`09:1228`) at `q = 2^1`, `b_T = 16` and
the audit's `delta_U` is therefore an inequality in `K` alone, and it holds for
every `K >= 1` -- so the audit never needs a numeral for `m_G`.  General in
`K`. -/
theorem audit_gate_arith {K : ℕ} (hK : 1 ≤ K) :
    ((2 ^ 1 : ℕ) : ℝ) * ((initialRefRows (xTdepth 16) (182 * K) : ℕ) : ℝ)
        + auditDeltaU * ((2 ^ 1 : ℕ) : ℝ) * ((184 * K : ℕ) : ℝ)
      ≤ ((182 * K : ℕ) : ℝ) := by
  have hxT : xTdepth 16 = 1 / 65536 := by norm_num [xTdepth]
  have hceil : ((initialRefRows (xTdepth 16) (182 * K) : ℕ) : ℝ)
      < 2 * (1 / 65536) * ((182 * K : ℕ) : ℝ) + 1 := by
    rw [initialRefRows, hxT]
    exact Nat.ceil_lt_add_one (by positivity)
  have hKR : (1 : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hK
  have hδ : auditDeltaU = 1 / 640 := by norm_num [auditDeltaU, auditEtaR]
  rw [hδ]
  push_cast at hceil ⊢
  linarith

section BankedGeometry

variable (F : FiniteSlots.Stage1SlotBinding) (q₂ : ℕ) (Y : Type*) [Fintype Y]
  [DecidableEq Y]

/-- **`09:113--114` through the banked inclusion.**  The audit's reference block
`R_G = {base} x Omega x [w_0] subseteq Rows(N)`: the image of the base column
reservoir under `ScaleAlignOpening.refIncl`, inside the frozen protected column
carrier `Rows(N) = Cols(A) = ProtColsFrozen` (`N = A^T` is `08:147`; the
cardinality is `08:110--122`).  Neither carrier is built here; both are consumed
by pin. -/
def auditRefRows : Finset (ProtColsFrozen F q₂ Y) :=
  (Finset.univ : Finset (Omega F q₂ Y × Fin (wBaseF F q₂ Y))).image
    (refIncl (Om := Omega F q₂ Y) (Sg := SelCar F q₂ Y) (Dg := DiagCar F q₂ Y)
      (w₀ := wBaseF F q₂ Y) (wSg := wSelF F q₂ Y) (wD := wDiagF F q₂ Y))

/-- **Aux A2 (`09:116`).**  `m_G = card Rows(G)`: the banked
`ScaleAlignOpening.refIncl_injective` makes the reference block a faithful copy
of `Omega x [w_0]`, so its cardinality is that carrier's. -/
theorem auditRefRows_card_eq :
    (auditRefRows F q₂ Y).card = Fintype.card (Omega F q₂ Y × Fin (wBaseF F q₂ Y)) := by
  rw [auditRefRows, Finset.card_image_of_injective _ refIncl_injective, Finset.card_univ]

/-- **`09:116` evaluated through the banked `card_refRows`.**  `m_G = M_0 w_0`
with `w_0 = 182 S_0 D_0` (`08:100`, in the display `eq:protected-multiplicities`
at `08:98--109`), i.e. `m_G = 182 K` at the common scale `K = M_0 S_0 D_0`. -/
theorem auditRefRows_card :
    (auditRefRows F q₂ Y).card
      = 182 * (Fintype.card (Omega F q₂ Y) * Fintype.card (SelCar F q₂ Y) *
          Fintype.card (DiagCar F q₂ Y)) := by
  have hw : wBaseF F q₂ Y
      = 182 * Fintype.card (SelCar F q₂ Y) * Fintype.card (DiagCar F q₂ Y) := rfl
  rw [auditRefRows_card_eq, card_refRows, hw]
  ring

/-- **`09:117` CONSUMED, not arranged.**  `g = m_G/m = 91/92` at the audit's
carriers is the banked `ScaleAlignOpening.referenceG_row_mass`, whose numerator
is the reference carrier's cardinality and whose denominator is the cardinality
of the carrier the pinned protected matrix is defined on.  Nothing is chosen to
make the ratio come out: the two integers are read off the built objects. -/
theorem auditRefRows_row_mass (hq : 0 < q₂) (y₀ : Y) :
    (((auditRefRows F q₂ Y).card : ℕ) : ℚ)
        / ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℚ) = 91 / 92 := by
  rw [auditRefRows_card_eq]
  exact referenceG_row_mass F hq y₀

/-- **Aux A3 (`09:117` as an integer identity).**  The same frozen ratio without
division: `92 m_G = 91 m`.  This is what makes the audit's `(m, m_G)` a legal
pair, where the retired hand-built `(644, 637)` only happened to be one. -/
theorem audit_row_counts :
    92 * (auditRefRows F q₂ Y).card = 91 * Fintype.card (ProtColsFrozen F q₂ Y) := by
  rw [auditRefRows_card, card_ProtColsFrozen]
  ring

omit [DecidableEq Y] in
/-- The audit's common scale is positive at the frozen positivity guards of
`08:110--122` (`section8_col_counts_pos`), so `m_G > 0`. -/
theorem audit_scale_pos (hq : 0 < q₂) (y₀ : Y) :
    1 ≤ Fintype.card (Omega F q₂ Y) * Fintype.card (SelCar F q₂ Y) *
        Fintype.card (DiagCar F q₂ Y) := by
  obtain ⟨hM, hS, hD⟩ := section8_col_counts_pos F hq y₀
  exact Nat.mul_pos (Nat.mul_pos hM hS) hD

omit [DecidableEq Y] in
/-- The audit's common scale is at least `2` once the Stage-2 coordinate width
clears `2` -- `06:124` fixes `q_2` as a power of two at least `12 s N_E`, so this
is a consequence of the schedule rather than an extra demand.  It is what makes
the one-row deletion of `auditDeleted` fit inside the frozen budget
`delta_U q m`. -/
theorem audit_scale_two (hq : 2 ≤ q₂) (y₀ : Y) :
    2 ≤ Fintype.card (Omega F q₂ Y) * Fintype.card (SelCar F q₂ Y) *
        Fintype.card (DiagCar F q₂ Y) := by
  have hq0 : 0 < q₂ := lt_of_lt_of_le (by norm_num) hq
  obtain ⟨hM, hS, -⟩ := section8_col_counts_pos F hq0 y₀
  have hD2 : 2 ≤ Fintype.card (DiagCar F q₂ Y) := by
    have hcard : Fintype.card (DiagCar F q₂ Y)
        = q₂ * Fintype.card (StageOneInterlace.Stage1Cols F Y) := by
      simp [Fintype.card_prod]
    have hpos : 1 ≤ Fintype.card (StageOneInterlace.Stage1Cols F Y) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => y₀⟩
    rw [hcard]
    calc (2 : ℕ) = 2 * 1 := by norm_num
      _ ≤ q₂ * Fintype.card (StageOneInterlace.Stage1Cols F Y) := Nat.mul_le_mul hq hpos
  calc (2 : ℕ) = 1 * 1 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hM hS) hD2

omit [DecidableEq Y] in
/-- `m = card Rows(N) >= 368` at the audit's scale floor: the deletion of one row
is then strictly inside the frozen budget `delta_U q m`. -/
theorem audit_ambient_card_ge (hq : 2 ≤ q₂) (y₀ : Y) :
    368 ≤ Fintype.card (ProtColsFrozen F q₂ Y) := by
  rw [card_ProtColsFrozen]
  calc (368 : ℕ) = 184 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul_left _ (audit_scale_two F q₂ Y hq y₀)

/-- The audit's deleted row: one arbitrary row of `U = Int_q(N)`, so the deletion
budget of §2 is exercised at a strictly positive count. -/
def auditDeleted (x₀ : ProtColsFrozen F q₂ Y) :
    Finset (Fin 1 × (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y)) := {(0, 0, x₀)}

omit [DecidableEq Y] in
theorem auditDeleted_card (x₀ : ProtColsFrozen F q₂ Y) :
    (auditDeleted F q₂ Y x₀).card = 1 := by
  rw [auditDeleted]
  exact Finset.card_singleton _

/-- The audit's retained row set: the rows of `U` other than `auditDeleted`. -/
def auditRetained (x₀ : ProtColsFrozen F q₂ Y) :
    Finset (Fin 1 × (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y)) :=
  Finset.univ \ auditDeleted F q₂ Y x₀

theorem auditRetained_card (x₀ : ProtColsFrozen F q₂ Y) :
    (auditRetained F q₂ Y x₀).card = 2 * Fintype.card (ProtColsFrozen F q₂ Y) - 1 := by
  have hu : Fintype.card (Fin 1 × (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y))
      = 2 * Fintype.card (ProtColsFrozen F q₂ Y) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    norm_num
  have hadd := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (auditDeleted F q₂ Y x₀))
  rw [auditDeleted_card, Finset.card_univ, hu] at hadd
  rw [auditRetained]
  omega

theorem auditRetained_deleted (x₀ : ProtColsFrozen F q₂ Y) :
    deletedRows (auditRetained F q₂ Y x₀) = auditDeleted F q₂ Y x₀ := by
  rw [auditRetained, deletedRows]
  exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)

/-- The audit deletes a strictly positive number of rows, so the §2 budget is not
exercised vacuously. -/
theorem auditRetained_deleted_pos (x₀ : ProtColsFrozen F q₂ Y) :
    0 < (deletedRows (auditRetained F q₂ Y x₀)).card := by
  rw [auditRetained_deleted, auditDeleted_card]
  norm_num

/-- **`09:1219` with `08:166`, positive at the banked geometry.**
`A_0 = ceil(2 x_T m_G)` is strictly positive because `m_G > 0`; no numeral is
assigned to it, since at the banked carriers `m_G = 182 K` is not one. -/
theorem audit_initialRefRows_pos (hq : 0 < q₂) (y₀ : Y) :
    0 < initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card := by
  have hmG : 0 < (auditRefRows F q₂ Y).card := by
    rw [auditRefRows_card]
    exact Nat.mul_pos (by norm_num) (audit_scale_pos F q₂ Y hq y₀)
  have hmGR : (0 : ℝ) < ((auditRefRows F q₂ Y).card : ℝ) := by exact_mod_cast hmG
  rw [initialRefRows]
  refine Nat.ceil_pos.mpr ?_
  exact mul_pos (by norm_num [xTdepth]) hmGR

/-- **`09:1221` at the audit point.**  `A_r = 2^1 A_0 = 2 A_0`; with
`audit_initialRefRows_pos` this is strictly positive, so the produced retention
is a real demand and not the empty one. -/
theorem audit_refRowFloor :
    refRowFloor (initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card) 1
      = 2 * initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card := by
  rw [refRowFloor]
  norm_num

/-- The audit's bracket member, at the `delta_U` its own defining display
produces.  Any frozen column density `0 < theta <= 1` is admitted; `theta` is
left **free**, so the schedule's own `theta = delta/(16 Q)` (`06:533`) is covered
by instantiation and no numeral is assigned to it.  Both halves of
`def:bracket`'s side condition `theta in (0,1]` (`03:169`) are carried as
binders; the proof needs only the upper one.

**Row clause only.**  The column carrier fixed here is `Fin (2^1) -> Fin 1`, a
**singleton**, so `def:bracket`'s column clause (`03:172`, `ceil(n^p z)` retained
columns) collapses to `ceil(theta) <= 1`, i.e. to `hθ₁` alone.  This lemma
therefore exercises the **row** clause only, and no column-axis strength may be
read into it or into anything downstream. -/
theorem audit_mem_bracket (hq : 2 ≤ q₂) (y₀ : Y) (x₀ : ProtColsFrozen F q₂ Y)
    {θ : ℝ} (_hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ((auditRetained F q₂ Y x₀,
          (Finset.univ : Finset (Fin 1 → (Fin (2 ^ 1) → Fin 1))))
        : Finset (Fin 1 × (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y))
            × Finset (Fin 1 → (Fin (2 ^ 1) → Fin 1)))
      ∈ bracketGE (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y) (Fin (2 ^ 1) → Fin 1) 1
          (1 - auditDeltaU) θ := by
  have hn : 368 ≤ Fintype.card (ProtColsFrozen F q₂ Y) := audit_ambient_card_ge F q₂ Y hq y₀
  have hcardX : Fintype.card (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y)
      = 2 * Fintype.card (ProtColsFrozen F q₂ Y) := by
    simp [Fintype.card_prod]
  have hcardY : Fintype.card (Fin (2 ^ 1) → Fin 1) = 1 := by simp
  have hδ : auditDeltaU = 1 / 640 := by norm_num [auditDeltaU, auditEtaR]
  constructor
  · intro j _
    have hfilter :
        (((auditRetained F q₂ Y x₀).filter (fun a => a.1 = j)) : Finset _)
          = auditRetained F q₂ Y x₀ := by
      apply Finset.filter_true_of_mem
      intro a _
      exact Subsingleton.elim _ _
    rw [hfilter, auditRetained_card, hcardX]
    refine Nat.ceil_le.mpr ?_
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * Fintype.card (ProtColsFrozen F q₂ Y)), hδ]
    have hnR : (368 : ℝ) ≤ ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℝ) := by
      exact_mod_cast hn
    push_cast
    linarith
  · rw [Finset.card_univ, hcardY]
    have hcardU : Fintype.card (Fin 1 → (Fin (2 ^ 1) → Fin 1)) = 1 := by simp
    rw [hcardU]
    refine Nat.ceil_le.mpr ?_
    push_cast
    simpa using hθ₁

/-- The audit point's instance of the **second** survival gate (`09:1228`),
`q A_0 + delta_U q m <= m_G`, at `q = 2^1` and the banked `(m, m_G)`, with `A_0`
evaluated through `09:1219` and `delta_U` through `06:517`.  Both row counts are
rewritten to the common scale `K` and the inequality is then `audit_gate_arith`;
no numeral for `m` or `m_G` enters. -/
theorem audit_gate (hq : 0 < q₂) (y₀ : Y) :
    ((2 ^ 1 : ℕ) : ℝ)
        * ((initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card : ℕ) : ℝ)
        + auditDeltaU * ((2 ^ 1 : ℕ) : ℝ)
            * ((Fintype.card (ProtColsFrozen F q₂ Y) : ℕ) : ℝ)
      ≤ (((auditRefRows F q₂ Y).card : ℕ) : ℝ) := by
  rw [auditRefRows_card, card_ProtColsFrozen]
  exact audit_gate_arith (audit_scale_pos F q₂ Y hq y₀)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- the banked protected column carrier is a nested sum of products of function
-- types, so elaborating this single instantiation of `retentionSupply_at_paper_A0`
-- at it exceeds the default budget; the bump is elaboration cost only.
/-- **BEYOND-PAPER audit conclusion at the banked geometry.**  At the point
tabulated above the retention supply of §4--§5 fires, with

* a strictly positive deleted-row count (so §2's budget is used, not bypassed),
* a strictly positive row floor `A_r = 2 A_0`, and
* a retained reference-row count meeting it in **every** outer coordinate,

for **every** legal `(F, q_2, Y)` with `2 <= q_2` and an inhabited seed carrier,
and at **every** ambient row `x_0` the member deletes.

This is evidence about our encoding only.  It is **not** the paper's instance --
the retained matrix `U'` of `09:1188--1191` at the materialized schedule is still
unbuilt -- and it does **not** discharge the registered canonical-inhabitation
obligation. -/
theorem audit_retention_fires (hq : 2 ≤ q₂) (y₀ : Y) (x₀ : ProtColsFrozen F q₂ Y)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) :
    0 < (deletedRows (auditRetained F q₂ Y x₀)).card
      ∧ 0 < initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card
      ∧ refRowFloor (initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card) 1
          = 2 * initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card
      ∧ ∀ i : Fin (2 ^ 1),
          refRowFloor (initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card) 1
            ≤ (retainedRefRows (auditRetained F q₂ Y x₀) (auditRefRows F q₂ Y) i).card := by
  have hq0 : 0 < q₂ := lt_of_lt_of_le (by norm_num) hq
  refine ⟨auditRetained_deleted_pos F q₂ Y x₀, audit_initialRefRows_pos F q₂ Y hq0 y₀,
    audit_refRowFloor F q₂ Y, ?_⟩
  exact retentionSupply_at_paper_A0 (Cl := Fin 1) (bT := 16) (auditRefRows F q₂ Y)
    (audit_mem_bracket F q₂ Y hq y₀ x₀ hθ₀ hθ₁) (audit_gate F q₂ Y hq0 y₀)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- same cause as the previous declaration: the banked protected column carrier
-- makes this instantiation of the §6 consumer expensive to elaborate.
/-- **Hypothesis consistency of §6, exhibited rather than argued.**

The full binder bundle of `completedSystem_readouts_of_retention` -- bracket
membership, the second survival gate, an alleged protocol on the retained
matrix's own row and column types, `1 <= C`, and the frozen cost bound
`cost(P) <= C+r-1` of `09:1192` -- is **simultaneously satisfiable**, so none of
the five readouts is vacuously available and no pair of the hypotheses is
contradictory.  Two of the five are pulled through here to show the consumer
actually fires.

BEYOND-PAPER on both axes: the schedule point is the audit's, and the protocol is
a leaf rather than the alleged shallow protocol of `09:1192--1193` (which, by the
argument's own design, does not exist).  This claims **no** fidelity. -/
theorem audit_readouts_available (hq : 2 ≤ q₂) (y₀ : Y) (x₀ : ProtColsFrozen F q₂ Y)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ (C : ℕ) (P : Protocol {a // a ∈ auditRetained F q₂ Y x₀}
        {c // c ∈ (Finset.univ : Finset (Fin 1 → (Fin (2 ^ 1) → Fin 1)))} Bool),
      1 ≤ C ∧ P.cost ≤ C + 1 - 1
        ∧ (∑ v : FrontierNode (completeNoBob 1 P)
                (retainedRefRows (auditRetained F q₂ Y x₀) (auditRefRows F q₂ Y))
                (initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card) 1,
              stoppingCapacity 1 v.val.length ≤ 2 ^ 1)
        ∧ (frontierRoutes (completeNoBob 1 P)
              (retainedRefRows (auditRetained F q₂ Y x₀) (auditRefRows F q₂ Y))
              (initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card) 1).Nonempty := by
  have hq0 : 0 < q₂ := lt_of_lt_of_le (by norm_num) hq
  refine ⟨1, Protocol.leaf false, le_refl 1, by simp [Protocol.cost], ?_, ?_⟩
  · exact (completedSystem_readouts_of_retention (Cl := Fin 1) (auditRefRows F q₂ Y)
      (audit_mem_bracket F q₂ Y hq y₀ x₀ hθ₀ hθ₁) (audit_gate F q₂ Y hq0 y₀)
      (Protocol.leaf false) (le_refl 1) (by simp [Protocol.cost])).1
  · exact (completedSystem_readouts_of_retention (Cl := Fin 1) (auditRefRows F q₂ Y)
      (audit_mem_bracket F q₂ Y hq y₀ x₀ hθ₀ hθ₁) (audit_gate F q₂ Y hq0 y₀)
      (Protocol.leaf false) (le_refl 1) (by simp [Protocol.cost])).2.1

end BankedGeometry

set_option maxHeartbeats 1000000 in
-- one instantiation of the previous section at a concrete slot binding; the
-- banked protected column carrier makes it expensive to elaborate.
/-- **Non-vacuity of §7's own binder set (prior-campaign LANE-GATE 3).**

§7's lemmas are universally quantified over `(F, q_2, Y)`, so a reader is
entitled to ask whether that binder set is inhabited at all.  It is, at a
nondegenerate point: `F.a = 3` (the frozen floor `a >= 3`), `F.s = 64`,
`q_2 = 2`, `Y = Fin 1`, and an arbitrary ambient row `x_0`, which exists because
`audit_ambient_card_ge` forces at least `368` of them.  The three retention
conclusions of `audit_retention_fires` then hold at that point with a strictly
positive deleted-row count and a strictly positive floor, so §7 is not vacuously
true.

The point additionally clears the two *checkable* clauses of
`eq:hard-seed-width-gates` (`06:264--268`) at `b_T = 16`: `16 | (s/4)` since
`s/4 = 16`, and `log_2 s < b_T` since `s = 2^6 < 2^16`.  (Its third clause,
`k_T >= m_HS`, quantifies over the unformalized `HSThreshold`, and `06:237--244`
fixes `b_T` from `k_T` through the unformalized `j_{49}`, so this is still a
**BEYOND-PAPER** point and claims no fidelity.)

**The point is schedule-illegal, and clearing those two clauses is not a legality
claim.**  `06:124` fixes `q_2` as the least power of two at least `12 s N_E`, so
at `F.s = 64` a legal `q_2` is at least `768`; this witness takes `q_2 = 2`.
"Nondegenerate" above means only *not cardinality-trivial* -- inhabited carriers,
a strictly positive deleted count, a strictly positive row floor -- and the
theorem asserts nothing beyond its own hypothesis `2 <= q_2`.  This is a
non-vacuity probe for **our** binder set, never evidence about the schedule's own
point.  It fixes `theta = 1`, which §7's census records with the rest.

**Why no trivial witness serves.**  The fifth clause forces `A_0 > 0` and hence
`m_G > 0`, and the sixth then demands a *nonempty* retained reference block in
both outer coordinates; the §8 probe shows exactly that a point with an empty
reference block satisfies the bracket membership and still fails the sixth.  A
degenerate witness therefore cannot discharge this statement. -/
theorem audit_point_nonvacuous :
    ∃ (F : FiniteSlots.Stage1SlotBinding) (q₂ : ℕ) (x₀ : ProtColsFrozen F q₂ (Fin 1)),
      2 ≤ q₂ ∧ 16 ∣ (F.s / 4) ∧ F.s < 2 ^ 16
        ∧ 0 < (deletedRows (auditRetained F q₂ (Fin 1) x₀)).card
        ∧ 0 < initialRefRows (xTdepth 16) (auditRefRows F q₂ (Fin 1)).card
        ∧ ∀ i : Fin (2 ^ 1),
            refRowFloor (initialRefRows (xTdepth 16) (auditRefRows F q₂ (Fin 1)).card) 1
              ≤ (retainedRefRows (auditRetained F q₂ (Fin 1) x₀)
                  (auditRefRows F q₂ (Fin 1)) i).card := by
  refine ⟨⟨3, 64, le_refl 3, by norm_num⟩, 2, ?_⟩
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num)
    (audit_ambient_card_ge ⟨3, 64, le_refl 3, by norm_num⟩ 2 (Fin 1) (le_refl 2) 0))
  obtain ⟨hdel, hA0, -, hret⟩ :=
    audit_retention_fires ⟨3, 64, le_refl 3, by norm_num⟩ 2 (Fin 1) (le_refl 2) 0 x₀
      (θ := 1) one_pos le_rfl
  exact ⟨x₀, le_refl 2, by norm_num, by norm_num, hdel, hA0, hret⟩

end Audit

/-! ## §8  Rejection probe: the survival gate is load-bearing

This probe claims **no** legality either.  It shows that `hgate` cannot be
dropped from §4: at a legitimate bracket member with an empty reference block the
conclusion is false, so `refRowFloor_le_retainedRefRows` is not provable without
the second clause of `eq:wrapper-initial-survival`. -/

section Pole

variable (F : FiniteSlots.Stage1SlotBinding) (q₂ : ℕ) (Y : Type*) [Fintype Y]
  [DecidableEq Y]

/-- **Statement pole.**  With no reference rows at all the retention conclusion
fails outright, while the bracket membership still holds.  So the second survival
gate `q A_0 + delta_U q m <= m_G` -- which forces `m_G >= q A_0 > 0` -- is a real
hypothesis of §4 and not an ornament.

The trivial "witness" for the retention, namely the empty row family, is exactly
what this rules out: it satisfies every hypothesis except the gate and fails the
conclusion. -/
theorem retention_needs_gate (hq : 2 ≤ q₂) (y₀ : Y) (x₀ : ProtColsFrozen F q₂ Y)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ((auditRetained F q₂ Y x₀,
          (Finset.univ : Finset (Fin 1 → (Fin (2 ^ 1) → Fin 1))))
        : Finset (Fin 1 × (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y))
            × Finset (Fin 1 → (Fin (2 ^ 1) → Fin 1)))
        ∈ bracketGE (Fin (2 ^ 1) × ProtColsFrozen F q₂ Y) (Fin (2 ^ 1) → Fin 1) 1
            (1 - auditDeltaU) θ
      ∧ ¬ ∀ i : Fin (2 ^ 1),
          refRowFloor (initialRefRows (xTdepth 16) (auditRefRows F q₂ Y).card) 1
            ≤ (retainedRefRows (auditRetained F q₂ Y x₀)
                (∅ : Finset (ProtColsFrozen F q₂ Y)) i).card := by
  have hq0 : 0 < q₂ := lt_of_lt_of_le (by norm_num) hq
  refine ⟨audit_mem_bracket F q₂ Y hq y₀ x₀ hθ₀ hθ₁, ?_⟩
  intro h
  have h0 := h ⟨0, by norm_num⟩
  have hempty : retainedRefRows (auditRetained F q₂ Y x₀)
      (∅ : Finset (ProtColsFrozen F q₂ Y)) ⟨0, by norm_num⟩ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [mem_retainedRefRows] at ha
    exact absurd ha.2 (Finset.notMem_empty _)
  have hpos := audit_initialRefRows_pos F q₂ Y hq0 y₀
  rw [hempty, audit_refRowFloor] at h0
  simp only [Finset.card_empty] at h0
  omega

end Pole

end EthInapproximability.ParameterizedNP.RetentionSupply
