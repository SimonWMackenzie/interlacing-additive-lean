import EthInapproximability.ParameterizedNP.CertificateCarryingFold

/-!
# Parameterized NP route: the seed-anchored fold

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: **`SEED-ANCHORED-FOLD-001`**
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`), opened in the
same change as this module as the **application-site consumer** of the
certificate-carrying `NO` fold: it instantiates that fold at the paper's own
schedule `b_i = B(n) = E_2(n)` (frozen `12:360--361`), anchors the base slot to the
paper's own seed data, and attacks the one input that base still takes on trust,
`lem:full-cube-seed` at a requested depth `b >= 1`.

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source`.

**No route-completion claim is made or implied.**  The construction layer
(`STAGE1-001 .. WRAP-001`) and the machine layer (`MATERIALIZE-001`) are unlanded;
`ITER-001`'s canonical inhabitation stays REGISTERED AS DEFERRED; and the
robustness display of `lem:full-cube-seed` at `b >= 1` is **not** discharged here
(Part 2 and the GAP-EXPOSED list below say exactly what is and is not).

## What this row does to the standing conditional statuses

`CERTIFICATE-CARRYING-FOLD-001`'s `paperSeed_certifiedAt` stays **conditional**,
and `CANONICAL-BRACKET-INVARIANCE-001` GAP-EXPOSED 3 stays open: the antecedent is
still not asserted at `B(n)`.  What changes is the *size and the name* of what is
owed.  Before this row the whole certified pair
`CertifiedAt (seedMatrix (B n)) D_0 (B n)` was the hypothesis.  After it:

* the **first** display of `lem:full-cube-seed`, `comp F_b = a_seed + 1`
  (frozen `12:34--36`), is **proved outright at every requested depth**
  (`seedMatrix_D`) -- it was banked only at `b = 0` before;
* the **second** display, `Lambda_3(F_b,1,2^{-b},3/5) >= a_seed + 1`
  (frozen `12:38--41`), is reduced to **one named linear-algebra leg**, frozen
  `12:55--60` in the exact form the frozen proof states it -- "the restricted
  matrix has rank at least `|J| - b`" -- together with the one-output-indicator
  identification `12:69--70` that the leg is stated through (see GAP-EXPOSED 1),
  with every other clause of the frozen
  proof `12:55--76` discharged in the kernel: the rung arithmetic `12:60--67`
  (`seedRungFloor`), the nonconstancy step `12:69--72`
  (`nonconstant_of_rank_gt_one`), the guard `d >= 1` and the
  `cor:fixed-output-rank` application `12:72--76`
  (`fullCube_bracket_ge_of_rankFloor`), and the three-rung assembly through
  `def:lambda` (`seedMatrix_lambda_of_rankFloor`).

So `SEED-001`'s "still pending" sentence is narrowed, not closed, and the named
deferred range is now exactly frozen `12:55--60` together with `12:69--70`, at
`b >= 1`.

## Provenance

* **Autoformalization anchors (proof source).**
  `sections/12-iteration-specification.tex`
  (SHA-256 `a846bfced8bfab2df70b16b46eba8ebe244a0d2ec89b03fc7a00b2a8007160ac`):
  * The **application site**, lines **360--379**.  Line 360--361, "For the
    intended fixed-level application, set `b_i = B(n) = E_2(n)` for every `i`",
    is Part 1: the depth stream is a *constant* sequence obtained by evaluating
    the banked definitional chain `n -> ellN n -> envE 2 n`, never a binder and
    never a numeral (`M3`).  Line 363 fixes `R_0 = Can(F_{B(n)})`; lines 364--369
    fix `m_0`, `n_0`; line **370**, "`D_0 = Y_0 = comp F_{B(n)} = a_seed + 1`", is
    Part 3.
  * `sec:full-cube-seed`, lines **14--82**: the minimality rule `16--21`
    (`a_seed >= 3` least with `q_seed = 2^{a_seed} - 2 >= 64(b+1)`), the matrix
    `eq:full-cube-seed` (label 29, display 23--30), `lem:full-cube-seed`
    (label 32) with its two displays at **34--36** and **38--41**, and the frozen
    **proof legs** at **45--53** (the complexity display), **55--60** (the
    row-density span leg and the retained rank floor `|J| - b`), **60--64** (the
    rung column densities `|J|/q_seed >= (3/5)2^{-t}`), **65--68** (the arithmetic
    consequence `|J| - b > 2^{a_seed - t - 1}` from `q_seed >= 64(b+1)`),
    **69--72** (nonconstancy of the retained matrix), and **72--76**
    (`cor:fixed-output-rank` at `(beta,d) = (1,a_seed - t)`, guard `d >= 1` from
    `a_seed >= 3` and `t <= 2`, conclusion `a_seed + 1 - t`, "exactly the
    three-rung claim").  The `O(b+1)` side-length sentence `77--81` is **not**
    claimed here.
  * Frozen `12:569--577` (the schedule's own seed accessors at `b = B(n)`), which
    is the display the banked `PaddingAndClock.aSeed` traces; Part 3 proves the
    two accessors agree.
  * The `k = 0` reading, lines 320--323, and clause F2's binder order, lines
    201--204: the depth family is quantified before either promise condition, so
    instantiating it at the constant stream is a *specialization*, not a
    strengthening.
* `sections/13-iteration-assembly.tex`: `step:I-04`'s depth interface, lines
  **418--428**, "Since `beta_i = beta_{i+1} = B(n)`, the output certificate of
  level `i` has exactly the depth used as the input certificate of level `i+1`.
  No density-monotonicity conversion and no rounding of the exponent occurs at
  this interface" -- Part 1's `seedDepthStream_succ`; and lines **292--295**
  (the six public state slots) with **317--321** (the base state), whose `depth`
  slot Part 1 pins and whose `budgetD`/`budgetY` slots Part 3 pins.
* `sections/03-preliminaries.tex`: `cor:fixed-output-rank` (label line 67,
  statement 66--74), `def:lambda` (label 224, display 226--231), `def:robust-seed`
  (label 243, lines 243--251), the column density `y = 3/5` at 215--220, and
  `def:bracket`'s column clause (line 172).
* `sections/02-mechanical-contract.tex`: `conv:finite-slots` (lines 14--18) and
  the mechanical rules (the `M\arabic*` enumerate opens at line 74), in
  particular:
  * **M3**, "Constructed and derived objects are distinct" (lines 85--88) -- a
    derived quantity "is recomputed from the constructed object", which is why
    every schedule quantity below is evaluated through its defining display and
    never assigned a numeral;
  * **M5**, "Every finite choice is deterministic" (lines 95--99) -- "the least
    element in a stated deterministic order or a named terminating search", the
    licence the `Nat.find` reifications of `a_seed` rely on;
  * **M6**, "Ceilings are part of the statement" (lines 101--105) -- honoured by
    the `ceil` column threshold of `def:bracket` used in Parts 2--3;
  * **M2**, "The constructor does not contain a promise certificate"
    (lines 81--83), and **M4**, "Every construction has a frame condition"
    (lines 90--93) -- the rules under which no field or premise beyond the
    frozen ones is added.

* **Reader counterpart.**  **No declaration in this module claims a reader item.**
  The reader statement of the seed lemma, `05-iteration.tex`
  `lem:paper-full-cube-seed` (label line 27, statement lines 28--44), is
  **`SEED-001`'s reader item and is recorded there as "not assigned to any other
  row"**; this module advances that row's pending half and deliberately does not
  re-claim its reader item.  `05-iteration.tex:140` is `ITER-001`'s and is claimed
  by `CertificateCarryingFold.certificateCarryingNoFold`; reader lines 123--127
  (the two seed conditions) and 278--280 (the base envelope row) are navigation
  loci only and are claimed by nothing here.

* **Banked declarations consumed by pin, never restated.**
  * `CertificateCarryingFold.CertifiedAt`, `.certifiedAt_noReading_iff`,
    `.certificateCarryingNoFold`, `.certificateCarryingNoFold_fires`,
    `.paperSeed_certifiedAt`, `.LevelCertified`, `.OutputCertified`,
    `.probeConstChain`.
  * `CanonicalBracketInvariance.fullCubeSeed_noReading_transported`,
    `.fullCubeSeedRowOrder` -- the wiring target of Part 5.
  * `OneLevelCompletion.fullCube`, `.fullCube_D_eq`, `.fixedOutputRank`,
    `.indR`, `.indR_rank_le_one_of_const`, `.bracket_row_univ`, `.fin1_fun_ext`,
    `.SeedInterface`, `.cubeUnit`.
  * `FixedLevelCarriers.aSeed`, `.qSeed`, `.seedMatrix`, `.aSeed_spec`,
    `.aSeed_min`; `PaddingAndClock.aSeed`, `.aSeedExists`, `.aSeed_spec`;
    `IterationAssembly.depthB`, `.envE`, `.depthB_ge`;
    `SuccessorMajorant.seedState`; `DirectOutputLower.xOut`, `.xOut_le_one`;
    `IteratedCanonicalChaining.CanonicalChain`, `.Can`, `.paperSeedReindexed`;
    and `NPCC.bracketGE` / `.nonempty` / `.Dfamily` / `.subgame` / `.LambdaGE`
    with `Workspace.Types.Interlace.interlaceFun` through `LegacyNPCC.Core`.

## Non-vacuity, hypothesis consistency, and the statement poles

* **The depth stream is the paper's own instance**, not a synthetic one: it is the
  evaluated chain `n -> ellN n -> envE 2 n`, and `seedDepthStream_ge` shows it is
  `>= 512` at every legal `n`, hence inside `lem:full-cube-seed`'s frozen `b >= 1`
  range.  This is the canonical inhabitation required for Part 1.
* **The rank-floor premise of Part 2 is not empty-by-construction.**
  `fullCube_rankFloor_at_depth_zero` **proves** it, for every bracket member, at
  requested depth `0`; `seedLambda_rankFloor_fires` then runs the whole reduction
  on that discharged premise and reproduces the first rung of the banked
  `OneLevelCompletion.fullCubeSeed_lambda` from the general machinery.  Both are
  labelled **NON-FIDELITY** for the seed lemma itself: `12:16` fixes `b >= 1`, so
  `b = 0` is outside its frozen range and this is non-vacuity evidence for the
  premise, never an instance of the lemma.
* **Hypothesis consistency.**  No premise bundle below conjoins statements the
  frozen text separates.  Part 2's conditional carries exactly one added premise
  (the frozen rank floor), and that premise is satisfiable (previous item);
  Part 4's fold is `certificateCarryingNoFold` with the depth stream
  *specialized*, so its consistency is that theorem's, and
  `seedAnchoredNoFold_fires` re-runs the banked NON-FIDELITY probe at the
  specialized stream to show the specialization did not make it vacuous.
* **Statement pole for Part 2.**  The conditional is not an existential, so the
  pole is the weakening direction: dropping the depth from the row density -- i.e.
  proving the display at `x = 1` instead of `x = 2^{-b}` -- is the banked `b = 0`
  statement and is strictly weaker, which is precisely why `bracket_row_univ` is
  unavailable here and the span leg is needed.  Replacing the rank floor
  `|J| - b` by `|J|` would be an over-demand: it is false as soon as a row of the
  cube is dropped.

## GAP-EXPOSED

1. **The row-density span leg, frozen `12:55--60`, together with the
   one-output-indicator identification `12:69--70`, at every `b >= 1`.**  "It
   contains at least `2^{q_seed - b}` Boolean vectors, so its real linear span has
   dimension at least `q_seed - b` ... the restricted matrix has rank at least
   `|J| - b`."  These are the **only** clauses of the frozen proof `12:45--76` not
   in the kernel here, and they enter every conditional of Part 2 as the explicit
   named hypothesis `hrank`, never as an axiom and never as an opaque
   certificate.  The second fragment is included because `hrank` is stated
   directly about the *one-output indicator* `indR (subgame ...) true`, so it
   also absorbs "The one-output indicator of the retained matrix is the same
   zero--one matrix viewed over `R`, so its rank is at least `|J| - b`"
   (`12:69--70`); for a Boolean matrix at `beta = 1` that absorbed step is the
   identity on entries, but it is owed and is named here rather than silently
   folded in.  This is the same range `SEED-001` records as pending and
   `CERTIFICATE-CARRYING-FOLD-001` records as its GAP-EXPOSED 1.
2. **`paperSeed_certifiedAt` therefore stays conditional**, and no declaration
   here asserts a robustness certificate for the seed at the scheduled depth
   `B(n)`.  `paperSeed_certifiedAt_of_rankFloor` carries the leg of item 1 as a
   hypothesis all the way to `R_0`.
3. **Canonical inhabitation of the fold is REGISTERED AS DEFERRED**, inherited
   verbatim from `CERTIFICATE-CARRYING-FOLD-001` GAP-EXPOSED 2 and
   `ITERATED-CANONICAL-CHAINING-001` GAP-EXPOSED 3: the paper's own chain needs
   the unbuilt Stage-1--4 constructor chain.  `seedAnchoredNoFold_fires` is the
   banked NON-FIDELITY probe read at the specialized stream and does **not**
   discharge it.
4. **The `O(b+1)` side-length sentence of `lem:full-cube-seed` (frozen `12:42`,
   proof `12:77--81`) is not claimed.**  Nothing here asserts an asymptotic
   side-length bound for the seed.
5. **The base state's remaining slots are untouched.**  Part 3 pins the `depth`
   slot and the two budget slots of `13:317--321` against the seed's own evaluated
   data; the two logarithmic side-length slots and the scale list are
   `SUCCESSOR-MAJORANT-001`'s and are not re-derived.
6. **No route completion is claimed** (see the head of this file).
-/

namespace EthInapproximability.ParameterizedNP.SeedAnchoredFold

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.IteratedCanonicalChaining
open EthInapproximability.ParameterizedNP.CanonicalBracketInvariance
open EthInapproximability.ParameterizedNP.CertificateCarryingFold
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.DirectOutputLower

/-! ## Part 1: the frozen depth schedule `b_i = B(n) = E_2(n)` (`12:360--361`)

The frozen sentence assigns the *whole* depth family at once, by one equality to a
scheduled quantity.  It is therefore reified as a constant sequence obtained by
evaluating the banked chain `n -> ellN n -> envE 2 n -> depthB n`; no numeral is
assigned to a depth anywhere below (`M3`). -/

/-- **The frozen depth schedule** -- `12-iteration-specification.tex:360--361`,
"For the intended fixed-level application, set `b_i = B(n) = E_2(n)` for every
`i`".

The value is the banked `IterationAssembly.depthB n`, which is itself
`IterationAssembly.envE 2 n` by its own defining display
(`13-iteration-assembly.tex:11`); the level index is discarded because the frozen
sentence discards it.  This is a **defined** schedule quantity read through its
defining chain, never a free parameter of this module.

General in `n` and the level.  Claims no reader item. -/
def seedDepthStream (n : ℕ) : ℕ → ℕ := fun _ => IterationAssembly.depthB n

/-- **Aux 1 (readout).**  The stream is the scheduled depth at every index.
General in `n` and the level.  Claims no reader item. -/
theorem seedDepthStream_apply (n i : ℕ) :
    seedDepthStream n i = IterationAssembly.depthB n := rfl

/-- **Aux 2 (the defining display, one level deeper).**  `B(n) = E_2(n)`, so the
stream is the banked envelope at exponent `2` -- the frozen right-hand side of
`12:361`.  The `2` is the frozen envelope index of `13-iteration-assembly.tex:11`
and not a numeral of this module.

General in `n` and the level.  Claims no reader item. -/
theorem seedDepthStream_eq_envE (n i : ℕ) :
    seedDepthStream n i = IterationAssembly.envE 2 n := rfl

/-- **Aux 3 (the `step:I-04` depth interface).**
`13-iteration-assembly.tex:418--428`: "Since `beta_i = beta_{i+1} = B(n)`, the
output certificate of level `i` has exactly the depth used as the input
certificate of level `i+1`.  No density-monotonicity conversion and no rounding of
the exponent occurs at this interface."

Identity property of the stream: the outgoing depth of a level and the incoming
depth of its successor are the **same integer**, which is what lets the fold of
Part 4 read one sequence at `i` and at `i+1` rather than two.

General in `n` and the level.  Claims no reader item. -/
theorem seedDepthStream_succ (n i : ℕ) :
    seedDepthStream n (i + 1) = seedDepthStream n i := rfl

/-- **The base state's depth slot is the scheduled depth** --
`13-iteration-assembly.tex:292--295` (the six public slots) at the base state of
`:317--321`, against the frozen schedule of `12:360--361`.

The banked `SuccessorMajorant.seedState` carries `depth := IterationAssembly.depthB n`,
so `S_0.depth` **is** the stream, definitionally, at every level index.  Recorded
so that no consumer supplies a depth to the fold that the base state does not
carry.

General in `n`, the scale list and the level.  Claims no reader item. -/
theorem seedState_depth (n : ℕ) (scales : List ℕ) (i : ℕ) :
    (SuccessorMajorant.seedState n scales).depth = seedDepthStream n i := rfl

/-- **The scheduled depth is inside `lem:full-cube-seed`'s frozen range**
(LANE-GATE 3, the canonical-inhabitation half of Part 1).

`IterationAssembly.depthB_ge` consumed by pin: at every legal source size the
scheduled depth is at least `512`, hence at least `1`.  So the requested depth the
whole of Part 2 is stated at, `b = B(n)`, satisfies the frozen `b >= 1` of
`12:16` -- the seed lemma is being invoked *inside* its stated range, and the
depth-zero material of `SEED-001` is not what the application site needs.

General in `n >= 1` and the level.  Claims no reader item. -/
theorem seedDepthStream_ge (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    512 ≤ seedDepthStream n i ∧ 1 ≤ seedDepthStream n i :=
  IterationAssembly.depthB_ge n hn

/-! ## Part 2: `lem:full-cube-seed` at a requested depth `b >= 1`
(`12:32--43`, proof `12:45--76`)

The first display is proved outright.  The second is reduced to the single frozen
leg `12:55--60`; every other clause of the frozen proof is discharged in the
kernel below. -/

/-- **The first display of `lem:full-cube-seed`, at every requested depth** --
`12-iteration-specification.tex:34--36`, `comp F_b = a_seed + 1`.

The banked `OneLevelCompletion.fullCube_D_eq` needs the sandwich
`2^{a-1} < q <= 2^a`, and the frozen minimality rule `12:16--21` supplies it at
the *reified* accessors: `q_seed = 2^{a_seed} - 2` gives the upper bound
outright, and `a_seed >= 3` gives `2^{a_seed - 1} >= 4 > 2`, hence
`2^{a_seed} - 2 > 2^{a_seed - 1}`.  Both facts come from
`FixedLevelCarriers.aSeed_spec`, i.e. from the frozen rule itself; **no numeral is
assigned to `a_seed` or `q_seed`** (`M3`; the least-solution search itself is
licensed by `M5`, "Every finite choice is deterministic").

Before this declaration the route banked this display **only** at the
out-of-range `b = 0` (`OneLevelCompletion.fullCubeSeed_D`, at the evaluated
numerals `7` and `126`).  Here it holds at every `b`, in particular at the
scheduled `b = B(n)`.

General in the requested depth.  Claims no reader item (the reader statement is
`SEED-001`'s). -/
theorem seedMatrix_D (b : ℕ) :
    D (FixedLevelCarriers.seedMatrix b) = FixedLevelCarriers.aSeed b + 1 := by
  obtain ⟨h3, -⟩ := FixedLevelCarriers.aSeed_spec b
  have hsplit : 2 ^ (FixedLevelCarriers.aSeed b - 1) * 2 = 2 ^ FixedLevelCarriers.aSeed b := by
    rw [← pow_succ]
    congr 1
    omega
  have h4 : (4 : ℕ) ≤ 2 ^ (FixedLevelCarriers.aSeed b - 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (FixedLevelCarriers.aSeed b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine fullCube_D_eq (FixedLevelCarriers.qSeed b) (FixedLevelCarriers.aSeed b)
    (by omega) ?_ ?_
  · simp only [FixedLevelCarriers.qSeed]
    omega
  · simp only [FixedLevelCarriers.qSeed]
    omega

/-- **The rung arithmetic of the frozen proof** --
`12-iteration-specification.tex:60--67`.

At rung `t in {0,1,2}` the retained column set satisfies
`|J| / q_seed >= (3/5) 2^{-t}` (frozen 60--64), and the frozen sentence
"The choice `q_seed >= 64(b+1)` gives `|J| - b > 2^{a_seed - t - 1}`"
(frozen 65--67) is exactly this inequality, written without a truncated
subtraction.

The proof is the frozen one, evaluated: `2^{a_seed} = q_seed + 2` from the
minimality rule, so `2^{a_seed - t - 1} = (q_seed + 2) / 2^{t+1}`, and the claim
reduces to `40 b + 10 < q_seed`, which `64(b+1) <= q_seed` gives with room to
spare.  Both inputs are `FixedLevelCarriers.aSeed_spec`; nothing is assumed about
`b`.

General in the requested depth and the rung index.  Claims no reader item. -/
theorem seedRungFloor (b t : ℕ) (ht : t ≤ 2) :
    (b : ℝ) + 2 ^ (FixedLevelCarriers.aSeed b - t - 1)
      < (FixedLevelCarriers.qSeed b : ℝ) * ((3 / 5) / 2 ^ t) := by
  obtain ⟨h3, hq64⟩ := FixedLevelCarriers.aSeed_spec b
  have hpow8 : (8 : ℕ) ≤ 2 ^ FixedLevelCarriers.aSeed b := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ FixedLevelCarriers.aSeed b := Nat.pow_le_pow_right (by norm_num) h3
  have hq2 : (2 : ℕ) ^ FixedLevelCarriers.aSeed b = FixedLevelCarriers.qSeed b + 2 := by
    simp only [FixedLevelCarriers.qSeed]
    omega
  have hsplitN : (2 : ℕ) ^ (FixedLevelCarriers.aSeed b - t - 1) * 2 ^ (t + 1)
      = FixedLevelCarriers.qSeed b + 2 := by
    rw [← pow_add, ← hq2]
    congr 1
    omega
  have hsplit : (2 : ℝ) ^ (FixedLevelCarriers.aSeed b - t - 1) * 2 ^ (t + 1)
      = (FixedLevelCarriers.qSeed b : ℝ) + 2 := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hsplitN
  have hupos : (0 : ℝ) < 2 ^ t := by positivity
  have hu4 : (2 : ℝ) ^ t ≤ 4 := by
    calc (2 : ℝ) ^ t ≤ 2 ^ 2 := by
          exact pow_le_pow_right₀ (by norm_num) ht
      _ = 4 := by norm_num
  have hsucc : (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
  have hq : (64 : ℝ) * ((b : ℝ) + 1) ≤ (FixedLevelCarriers.qSeed b : ℝ) := by
    exact_mod_cast hq64
  have hbnn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hb4 : (b : ℝ) * 2 ^ t ≤ (b : ℝ) * 4 := by
    exact mul_le_mul_of_nonneg_left hu4 hbnn
  have hP : (2 : ℝ) ^ (FixedLevelCarriers.aSeed b - t - 1) * 2 ^ t * 2
      = (FixedLevelCarriers.qSeed b : ℝ) + 2 := by
    rw [hsucc] at hsplit
    linarith [hsplit]
  have key : ((b : ℝ) + 2 ^ (FixedLevelCarriers.aSeed b - t - 1)) * 2 ^ t
      < (FixedLevelCarriers.qSeed b : ℝ) * (3 / 5) := by
    have hexp : ((b : ℝ) + 2 ^ (FixedLevelCarriers.aSeed b - t - 1)) * 2 ^ t
        = (b : ℝ) * 2 ^ t + 2 ^ (FixedLevelCarriers.aSeed b - t - 1) * 2 ^ t := by ring
    rw [hexp]
    linarith [hb4, hP, hq]
  rw [← mul_div_assoc, lt_div_iff₀ hupos]
  linarith [key]

/-- **The nonconstancy step of the frozen proof** --
`12-iteration-specification.tex:69--72`; the quoted sentence "Since
`|J| - b > 2^{a_seed - t - 1} >= 1`, the retained matrix is nonconstant" begins
mid-line 70 and ends on line 72.

The frozen sentence derives nonconstancy *from* the rank floor, and so does this:
a constant matrix has a rank-one one-output indicator by the banked
`OneLevelCompletion.indR_rank_le_one_of_const` (which is
`03-preliminaries.tex:79--80`), so a rank exceeding `1` refutes constancy.  This
is why nonconstancy is **not** a hypothesis of the rung lemma below: making it one
would be a premise the frozen proof does not have.

General in both carriers, the matrix and the fixed output.  Claims no reader
item. -/
theorem nonconstant_of_rank_gt_one {X Y : Type*} [Fintype Y] (f : X → Y → Bool)
    (β : Bool) (h : 1 < (indR f β).rank) : ¬ ∃ c, ∀ x y, f x y = c := by
  rintro ⟨c, hc⟩
  have := indR_rank_le_one_of_const hc β
  omega

/-- **One rung of the frozen proof at an arbitrary requested depth** --
`12-iteration-specification.tex:60--76`.

This is the general-`b` form of the banked
`OneLevelCompletion.fullCube_bracket_ge`, which is stated at `x_out 0 = 1` only
because it uses `bracket_row_univ`.  Here the row density is the banked
`DirectOutputLower.xOut b` at an arbitrary `b`, and the clause the frozen
proof supplies by a span argument -- `12:55--60`, "the restricted matrix has rank
at least `|J| - b`" -- is the explicit hypothesis `hrank`, written without a
truncated subtraction.  Because `hrank` is stated about the one-output indicator
`indR (subgame ...) true`, it also absorbs the frozen identification `12:69--70`
("The one-output indicator of the retained matrix is the same zero--one matrix
viewed over `R`, so its rank is at least `|J| - b`"); both fragments are named
in GAP-EXPOSED 1.  Everything else is discharged:

* nonemptiness of the bracket family is taken **first**, from the vendored
  `NPCC.bracketGE.nonempty`, because `Dfamily` is a `Nat.sInf` and reports `0` on
  an empty family;
* the column clause of `def:bracket` (`03-preliminaries.tex:172`) turns `hthr`
  into `b + 2^{d-1} < |J|`, and with `hrank` into the frozen
  `2^{d-1} < rank_R(1_{M=1})`;
* nonconstancy is **derived** at that point (`nonconstant_of_rank_gt_one`),
  exactly as frozen 69--72 derives it;
* the conclusion is `cor:fixed-output-rank` through the banked
  `OneLevelCompletion.fixedOutputRank` at `beta = 1`, with the frozen guard
  `d >= 1` as its own hypothesis.

General in the width, the requested depth, the rung exponent and the column
density.  Claims no reader item. -/
theorem fullCube_bracket_ge_of_rankFloor (q b d : ℕ) (hd : 1 ≤ d) (y : ℝ)
    (hy1 : y ≤ 1)
    (hthr : b + 2 ^ (d - 1) < ⌈((Fintype.card (Fin q) : ℝ)) ^ (1 : ℕ) * y⌉₊)
    (hrank : ∀ RC ∈ bracketGE (Fin q → Bool) (Fin q) 1 (xOut b) y,
      (RC.2).card
        ≤ b + (indR (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2) true).rank) :
    d + 1 ≤ Dfamily (interlaceFun (fullCube q) 1)
      (bracketGE (Fin q → Bool) (Fin q) 1 (xOut b) y) := by
  classical
  have hx1 : xOut b ≤ 1 := xOut_le_one b
  have hXpos : 1 ≤ Fintype.card (Fin q → Bool) := Fintype.card_pos
  have hne : (bracketGE (Fin q → Bool) (Fin q) 1 (xOut b) y).Nonempty :=
    bracketGE.nonempty 1 (xOut b) y hx1 hy1 hXpos
  have hall : ∀ RC ∈ bracketGE (Fin q → Bool) (Fin q) 1 (xOut b) y,
      d + 1 ≤ D (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2) := by
    rintro ⟨R, C⟩ hRC
    have hcol : ⌈((Fintype.card (Fin q) : ℝ)) ^ (1 : ℕ) * y⌉₊ ≤ C.card := hRC.2
    have hCcard : b + 2 ^ (d - 1) < C.card := lt_of_lt_of_le hthr hcol
    have hr := hrank (R, C) hRC
    simp only at hr
    have hrank' : 2 ^ (d - 1) < (indR (subgame (interlaceFun (fullCube q) 1) R C) true).rank := by
      omega
    have hone : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
    have hnc := nonconstant_of_rank_gt_one
      (subgame (interlaceFun (fullCube q) 1) R C) true (by omega)
    exact fixedOutputRank _ true d hd hnc hrank'
  obtain ⟨RC0, hRC0⟩ := hne
  have hSne : {m : ℕ | ∃ RC ∈ bracketGE (Fin q → Bool) (Fin q) 1 (xOut b) y,
      m = D (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2)}.Nonempty :=
    ⟨_, RC0, hRC0, rfl⟩
  obtain ⟨RC1, hRC1, hEq⟩ := Nat.sInf_mem hSne
  change d + 1 ≤ sInf _
  rw [hEq]
  exact hall RC1 hRC1

/-- **The second display of `lem:full-cube-seed`, at every requested depth
`b >= 1`, conditional on the frozen span leg** --
`12-iteration-specification.tex:38--41`, proof legs `12:55--76`.

`def:lambda` (`03-preliminaries.tex:226--231`) takes the minimum over
`j in {0,1,2}` of `j + comp<M,1,x,y/2^j>`, so the three rungs are the column
densities `3/5`, `3/5/2`, `3/5/4` at offsets `0,1,2`; the frozen proof runs
`cor:fixed-output-rank` at `(beta,d) = (1, a_seed - t)` and gets
`a_seed + 1 - t`, "exactly the three-rung claim" (frozen 72--76).  Both moves are
made here through `fullCube_bracket_ge_of_rankFloor` and `seedRungFloor`, and the
guard `d >= 1` holds because `a_seed >= 3` and `t <= 2`.

**The single hypothesis is the frozen span leg `12:55--60`** at the three rung
densities, in the frozen form "the restricted matrix has rank at least `|J| - b`".
It is a named hypothesis, never an axiom; `fullCube_rankFloor_at_depth_zero`
below proves that it is satisfiable.

The requested depth binder `hb : 1 <= b` is the frozen `12:16` "Fix a requested
depth `b >= 1`".  It is carried even though the arithmetic does not need it,
because a consumer must not be able to read this declaration at a depth the frozen
subsection does not range over.

General in the requested depth.  Claims no reader item (the reader statement is
`SEED-001`'s). -/
theorem seedMatrix_lambda_of_rankFloor (b : ℕ) (hb : 1 ≤ b)
    (hrank : ∀ t : ℕ, t ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
        (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 2 ^ t),
        (RC.2).card
          ≤ b + (indR (subgame
              (interlaceFun (FixedLevelCarriers.seedMatrix b) 1) RC.1 RC.2) true).rank) :
    FixedLevelCarriers.aSeed b + 1
      ≤ LambdaGE (FixedLevelCarriers.seedMatrix b) 1 (xOut b) ((3 : ℝ) / 5) := by
  -- The frozen `b >= 1` binder of `12:16` is carried for scope, not for arithmetic.
  have _ : 0 < b := hb
  obtain ⟨h3, -⟩ := FixedLevelCarriers.aSeed_spec b
  have hceil : ∀ t : ℕ, t ≤ 2 →
      b + 2 ^ (FixedLevelCarriers.aSeed b - t - 1)
        < ⌈((Fintype.card (Fin (FixedLevelCarriers.qSeed b)) : ℝ)) ^ (1 : ℕ)
            * ((3 : ℝ) / 5 / 2 ^ t)⌉₊ := by
    intro t ht
    refine Nat.lt_ceil.mpr ?_
    have h := seedRungFloor b t ht
    rw [Fintype.card_fin]
    push_cast
    calc (b : ℝ) + 2 ^ (FixedLevelCarriers.aSeed b - t - 1)
        < (FixedLevelCarriers.qSeed b : ℝ) * ((3 / 5) / 2 ^ t) := h
      _ = (FixedLevelCarriers.qSeed b : ℝ) ^ (1 : ℕ) * (3 / 5 / 2 ^ t) := by
          rw [pow_one]
  have h0 : FixedLevelCarriers.aSeed b + 1
      ≤ Dfamily (interlaceFun (FixedLevelCarriers.seedMatrix b) 1)
        (bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
          (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5)) := by
    have hy : (3 : ℝ) / 5 / 2 ^ (0 : ℕ) = (3 : ℝ) / 5 := by norm_num
    have h := fullCube_bracket_ge_of_rankFloor (FixedLevelCarriers.qSeed b) b
      (FixedLevelCarriers.aSeed b) (by omega) ((3 : ℝ) / 5 / 2 ^ (0 : ℕ))
      (by rw [hy]; norm_num) (by simpa using hceil 0 (by omega))
      (by simpa using hrank 0 (by omega))
    rw [hy] at h
    simpa using h
  have h1 : FixedLevelCarriers.aSeed b
      ≤ Dfamily (interlaceFun (FixedLevelCarriers.seedMatrix b) 1)
        (bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
          (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 2)) := by
    have hy : (3 : ℝ) / 5 / 2 ^ (1 : ℕ) = (3 : ℝ) / 5 / 2 := by norm_num
    have h := fullCube_bracket_ge_of_rankFloor (FixedLevelCarriers.qSeed b) b
      (FixedLevelCarriers.aSeed b - 1) (by omega) ((3 : ℝ) / 5 / 2 ^ (1 : ℕ))
      (by rw [hy]; norm_num) (by simpa using hceil 1 (by omega))
      (by simpa using hrank 1 (by omega))
    rw [hy] at h
    have : FixedLevelCarriers.aSeed b - 1 + 1 = FixedLevelCarriers.aSeed b := by omega
    rw [this] at h
    exact h
  have h2 : FixedLevelCarriers.aSeed b - 1
      ≤ Dfamily (interlaceFun (FixedLevelCarriers.seedMatrix b) 1)
        (bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
          (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 4)) := by
    have hy : (3 : ℝ) / 5 / 2 ^ (2 : ℕ) = (3 : ℝ) / 5 / 4 := by norm_num
    have h := fullCube_bracket_ge_of_rankFloor (FixedLevelCarriers.qSeed b) b
      (FixedLevelCarriers.aSeed b - 2) (by omega) ((3 : ℝ) / 5 / 2 ^ (2 : ℕ))
      (by rw [hy]; norm_num) (by simpa using hceil 2 (by omega))
      (by simpa using hrank 2 (by omega))
    rw [hy] at h
    have : FixedLevelCarriers.aSeed b - 2 + 1 = FixedLevelCarriers.aSeed b - 1 := by omega
    rw [this] at h
    exact h
  unfold LambdaGE
  exact le_min h0 (le_min (by omega) (by omega))

/-- **The frozen `NO`-side pair for the seed, at every requested depth `b >= 1`,
conditional on the same single leg** -- `12:34--41` read as
`CertificateCarryingFold.CertifiedAt`.

The first conjunct is `seedMatrix_D`, proved outright; the second is
`seedMatrix_lambda_of_rankFloor`.  This is the object frozen `12:374--378` demands
at the base of the iteration, at the seed's own evaluated budget
`D_0 = a_seed + 1` (frozen `12:370`) rather than at a binder.

General in the requested depth.  Claims no reader item. -/
theorem seedMatrix_certifiedAt_of_rankFloor (b : ℕ) (hb : 1 ≤ b)
    (hrank : ∀ t : ℕ, t ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
        (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 2 ^ t),
        (RC.2).card
          ≤ b + (indR (subgame
              (interlaceFun (FixedLevelCarriers.seedMatrix b) 1) RC.1 RC.2) true).rank) :
    CertifiedAt (FixedLevelCarriers.seedMatrix b) (FixedLevelCarriers.aSeed b + 1) b :=
  ⟨seedMatrix_D b, seedMatrix_lambda_of_rankFloor b hb hrank⟩

/-- **Hypothesis consistency for Part 2's conditional: its conclusion is a
saturation, never an over-demand** (mandatory check, landed in the kernel).

The banked `CertificateCarryingFold.certifiedAt_saturates` -- itself
`StageThreeExactScale.LambdaGE_le_D` consumed by pin -- bounds `Lambda_3` above by
the ambient complexity, so the two displays of `lem:full-cube-seed` together force
`Lambda_3(F_b,1,2^{-b},3/5) = a_seed + 1` **exactly**.  Hence no `False` follows
from conjoining them: they are the two halves of one equality, exactly as frozen
`12:33--41` presents them ("The matrix `F_b` has ... and is robust at depth `b`"),
and not two independent demands that could exceed each other.

The row-carrier nonemptiness is discharged from `Fintype.card_pos` on
`{0,1}^{q_seed}`, not assumed.

General in the requested depth.  Claims no reader item. -/
theorem seedMatrix_certifiedAt_saturates (b : ℕ) (hb : 1 ≤ b)
    (hrank : ∀ t : ℕ, t ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
        (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 2 ^ t),
        (RC.2).card
          ≤ b + (indR (subgame
              (interlaceFun (FixedLevelCarriers.seedMatrix b) 1) RC.1 RC.2) true).rank) :
    LambdaGE (FixedLevelCarriers.seedMatrix b) 1 (xOut b) ((3 : ℝ) / 5)
      = FixedLevelCarriers.aSeed b + 1 :=
  certifiedAt_saturates (FixedLevelCarriers.seedMatrix b) Fintype.card_pos
    (seedMatrix_certifiedAt_of_rankFloor b hb hrank)

/-- **The premise of Part 2 quantifies over a non-empty family at every rung and
every requested depth** (LANE-GATE 3 disclosure).

`NPCC.bracketGE.nonempty` consumed by pin at the three frozen rung densities
`3/5`, `3/5/2`, `3/5/4` and at the banked row density `x_out b`.  So `hrank` is a
**genuine** premise -- it is never satisfied by an empty family -- and the only
evidence that it is satisfiable at all is `fullCube_rankFloor_at_depth_zero`, at
the out-of-range `b = 0`.  This is the honest statement of GAP-EXPOSED 1: at
`b >= 1` the premise is real, non-vacuous, and unproved here.

It is also what keeps the conclusion non-trivial: `Dfamily` is a `Nat.sInf` and
would report `0` on an empty family, so each rung bound is a genuine minimum.

The rung bound `t <= 2` is deliberately **not** imposed: the frozen densities are
`y/2^j` and nonemptiness holds at every one of them, so demanding the frozen rung
range here would be an over-strong hypothesis.

General in the requested depth and the rung index.  Claims no reader item. -/
theorem seedBracket_nonempty (b t : ℕ) :
    (bracketGE (Fin (FixedLevelCarriers.qSeed b) → Bool)
      (Fin (FixedLevelCarriers.qSeed b)) 1 (xOut b) ((3 : ℝ) / 5 / 2 ^ t)).Nonempty := by
  have hy1 : (3 : ℝ) / 5 / 2 ^ t ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have h0 : (0 : ℝ) < 2 ^ t := by positivity
    rw [div_le_one h0]
    linarith
  exact bracketGE.nonempty 1 (xOut b) ((3 : ℝ) / 5 / 2 ^ t) (xOut_le_one b) hy1
    Fintype.card_pos

/-! ## Part 3: the seed-anchored base state (`12:360--379`, `13:317--321`)

The base of the iteration is not a free record: frozen `12:363--370` fixes its
matrix, its two carriers and its two budgets by *equalities to seed data*.  Part 1
pinned the depth slot; this part pins the budget slots, which needs the two seed
accessors of the route to be shown equal. -/

/-- **The two banked seed accessors agree at the scheduled depth.**

`FixedLevelCarriers.aSeed` reifies the frozen minimality rule of `12:16--21` as a
function of the *requested depth*; `PaddingAndClock.aSeed` reifies the same rule
as the schedule reads it at `b = B(n)` (frozen `12:569--572`,
`13-iteration-assembly.tex:733--737`).  The two search predicates differ only by
whether `q_seed = 2^a - 2 >= 64(b+1)` is written with the frozen truncated
subtraction or additively, and for `a >= 3` -- which both predicates demand --
they are the same condition, so the two least solutions coincide.

This is the identification frozen `12:370` needs: the seed complexity the *lemma*
delivers, `a_seed(B(n)) + 1`, and the budget the *schedule* carries,
`a_seed(n) + 1`, are the same integer.  Both sides are evaluated through their
definitional chains; no numeral appears (`M3`), and the two least-solution
searches being compared are `M5` deterministic choices.

General in `n`.  Claims no reader item. -/
theorem aSeed_at_scheduled_depth (n : ℕ) :
    FixedLevelCarriers.aSeed (IterationAssembly.depthB n) = PaddingAndClock.aSeed n := by
  obtain ⟨h3, hsize⟩ := PaddingAndClock.aSeed_spec n
  obtain ⟨h3', hsize'⟩ := FixedLevelCarriers.aSeed_spec (IterationAssembly.depthB n)
  have hpow8 : (8 : ℕ) ≤ 2 ^ FixedLevelCarriers.aSeed (IterationAssembly.depthB n) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ FixedLevelCarriers.aSeed (IterationAssembly.depthB n) :=
          Nat.pow_le_pow_right (by norm_num) h3'
  have hq' : FixedLevelCarriers.qSeed (IterationAssembly.depthB n)
      = 2 ^ FixedLevelCarriers.aSeed (IterationAssembly.depthB n) - 2 := rfl
  refine le_antisymm ?_ ?_
  · exact FixedLevelCarriers.aSeed_min h3 (by omega)
  · rw [PaddingAndClock.aSeed]
    refine Nat.find_le ⟨h3', ?_⟩
    omega

/-- **The base state's two budget slots are the seed's own complexity** --
`12-iteration-specification.tex:370`, "`D_0 = Y_0 = comp F_{B(n)} = a_seed + 1`",
at the banked base state of `13-iteration-assembly.tex:317--321`.

Read strictly right to left, through the definitional chain
`n -> depthB n -> aSeed -> qSeed -> F_{B(n)} -> comp`: `seedMatrix_D` evaluates
`comp F_{B(n)}`, and `aSeed_at_scheduled_depth` identifies the schedule's own
`a_seed(n)` with the lemma's `a_seed(B(n))`.  So the two budget slots the banked
`SuccessorMajorant.seedState` carries are **not** an assignment -- they are the
evaluated seed complexity.

This closes the `D_0` half of the budget identity of frozen `12:370` at the base
index; the successor identity `D_{i+1} = D_i + H_i + 1` is
`ITERATED-CANONICAL-CHAINING-001`'s and is untouched.

General in `n` and the scale list.  Claims no reader item. -/
theorem seedState_budgets_are_seed_complexity (n : ℕ) (scales : List ℕ) :
    (SuccessorMajorant.seedState n scales).budgetD
        = D (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n)) ∧
      (SuccessorMajorant.seedState n scales).budgetY
        = D (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n)) := by
  have h : D (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n))
      = PaddingAndClock.aSeed n + 1 := by
    rw [seedMatrix_D, aSeed_at_scheduled_depth]
  exact ⟨h.symm, h.symm⟩

/-- **The frozen seed conditions on `R_0 = Can(F_{B(n)})`, at the evaluated budget
and conditional on the span leg alone** --
`12-iteration-specification.tex:360--379`, display lines 374--378.

`CertificateCarryingFold.paperSeed_certifiedAt` supplies the
`lem:canonical-reindexing-invariance` factor of frozen line 379 outright and takes
the `lem:full-cube-seed` factor as a hypothesis; that hypothesis is now
`seedMatrix_certifiedAt_of_rankFloor`, so the only thing still assumed on the way
to `R_0` is the frozen span leg `12:55--60`.  The requested depth is the scheduled
`B(n)`, which `seedDepthStream_ge` puts inside the frozen `b >= 1` range, and the
budget is the **evaluated** `a_seed(B(n)) + 1` rather than a binder.

General in `n >= 1`.  Claims no reader item. -/
theorem paperSeed_certifiedAt_of_rankFloor (n : ℕ) (hn : 1 ≤ n)
    (hrank : ∀ t : ℕ, t ≤ 2 →
      ∀ RC ∈ bracketGE (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n)) → Bool)
        (Fin (FixedLevelCarriers.qSeed (IterationAssembly.depthB n))) 1
        (xOut (IterationAssembly.depthB n)) ((3 : ℝ) / 5 / 2 ^ t),
        (RC.2).card
          ≤ IterationAssembly.depthB n
            + (indR (subgame (interlaceFun
                (FixedLevelCarriers.seedMatrix (IterationAssembly.depthB n)) 1)
                  RC.1 RC.2) true).rank) :
    CertifiedAt (paperSeedReindexed n)
      (FixedLevelCarriers.aSeed (IterationAssembly.depthB n) + 1)
      (IterationAssembly.depthB n) :=
  paperSeed_certifiedAt n (FixedLevelCarriers.aSeed (IterationAssembly.depthB n) + 1)
    (seedMatrix_certifiedAt_of_rankFloor (IterationAssembly.depthB n)
      (IterationAssembly.depthB_ge n hn).2 hrank)

/-! ## Part 4: the seed-anchored fold (`12:279--297` at the schedule of `12:360--361`)

The banked fold quantifies the depth family; the application site fixes it.  This
part is that specialization, and nothing else: no hypothesis is added, and the
conclusion is the frozen pair at the one scheduled depth. -/

/-- **The certificate-carrying `NO` fold at the paper's own depth schedule** --
`CertificateCarryingFold.certificateCarryingNoFold` (frozen `12:279--297`, proof
`12:341--350`) instantiated at `b_i = B(n)` for every `i` (frozen `12:360--361`).

Every level of the chain carries the frozen pair at the **same** scheduled depth
`B(n)`: this is the shape `step:I-04` (`13:418--428`) demands, "no
density-monotonicity conversion and no rounding of the exponent occurs at this
interface".  The banked fold is consumed by pin; nothing of its induction is
restated.

The base clause is the seed condition of frozen `12:285--290` read at `B(n)`,
which Part 3 supplies from the seed lemma when the span leg is available.

General in the specification, the chain, the budget stream, the source size, the
colouring statement, the level count and the level.  Claims no reader item (the
`k`-level reader item `05-iteration.tex:140` is claimed by the banked fold). -/
theorem seedAnchoredNoFold {S : FixedLevelCarriers.LevelCarrierSpec}
    (C : CanonicalChain S) (Dseq : ℕ → ℕ) (n : ℕ) (GapColouring : Prop)
    (hgap : GapColouring) (k : ℕ)
    (hbase : CertifiedAt (C.lev 0) (Dseq 0) (IterationAssembly.depthB n))
    (hstep : ∀ i, i < k → GapColouring →
      LevelCertified C Dseq (seedDepthStream n) i →
      OutputCertified C Dseq (seedDepthStream n) i)
    (j : ℕ) (hj : j ≤ k) :
    CertifiedAt (C.lev j) (Dseq j) (IterationAssembly.depthB n) :=
  certificateCarryingNoFold C Dseq (seedDepthStream n) GapColouring hgap k hbase hstep j hj

/-- **The fold's base in the shape the public record reads** --
`def:robust-seed` (`03-preliminaries.tex:243--251`), which carries the whole of
the predicate used here.

The base slot may be supplied as a `def:robust-seed` certificate rather than as
the raw pair, through the banked
`CertificateCarryingFold.certifiedAt_noReading_iff`.  The extra
`comp >= 1` conjunct of `def:robust-seed` is discarded on entry, exactly as the
frozen fold discards it: clause (iv) never uses it.

Frozen `12:381--382` -- "the next public record carries only the new matrix,
budgets, and depths" -- enumerates the record *fields* only.  It is **not** a
statement that the record carries a robust-seed certificate, and nothing in this
declaration rests on reading it that way.

General in the specification, the chain, the budget stream, the source size, the
`YES` slot, the colouring statement, the level count and the level.  Claims no
reader item. -/
theorem seedAnchoredNoFold_of_noReading {S : FixedLevelCarriers.LevelCarrierSpec}
    (C : CanonicalChain S) (Dseq : ℕ → ℕ) (n y : ℕ) (GapColouring : Prop)
    (hgap : GapColouring) (k : ℕ)
    (hbase : (SeedInterface.mk (C.lev 0) (Dseq 0) y (IterationAssembly.depthB n)).noReading)
    (hstep : ∀ i, i < k → GapColouring →
      LevelCertified C Dseq (seedDepthStream n) i →
      OutputCertified C Dseq (seedDepthStream n) i)
    (j : ℕ) (hj : j ≤ k) :
    CertifiedAt (C.lev j) (Dseq j) (IterationAssembly.depthB n) :=
  seedAnchoredNoFold C Dseq n GapColouring hgap k
    (((certifiedAt_noReading_iff (C.lev 0) (Dseq 0) y
      (IterationAssembly.depthB n)).1 hbase).1) hstep j hj

/-! ## Part 5: wiring, non-vacuity, and the deferred canonical inhabitation

`CANONICAL-BRACKET-INVARIANCE-001`'s unwired census names
`fullCubeSeed_noReading_transported` as awaiting a consumer.  It gets one here, in
an actual proof term.  Canonical inhabitation of the *fold* stays REGISTERED AS
DEFERRED (GAP-EXPOSED 3). -/

/-- **Aux 4 (round trip: a `def:robust-seed` certificate is a certified pair).**

`03-preliminaries.tex:243--251` field by field, through the banked
`CertificateCarryingFold.certifiedAt_noReading_iff` consumed by pin -- no
certificate predicate is declared in this module.  General in both carriers, the
matrix, the budget, the `YES` slot and the depth.  Claims no reader item. -/
theorem certifiedBase_of_noReading {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) (d y b : ℕ) (h : (SeedInterface.mk M d y b).noReading) :
    CertifiedAt M d b ∧ 1 ≤ d :=
  (certifiedAt_noReading_iff M d y b).1 h

/-- **The transported depth-zero seed certificate enters the fold's base slot**
(LANE-GATE 3; closes the `CANONICAL-BRACKET-INVARIANCE-001` wiring item).

`CanonicalBracketInvariance.fullCubeSeed_noReading_transported` runs the whole
three-conjunct `def:robust-seed` transport with every hypothesis discharged, at
the banked depth-zero inhabitant on `Can_{2^126,126}(F_0)` with the frozen
lexicographic row order of `12:96--97`.  Here it is **consumed in a proof term**,
producing the base-slot shape of Part 4: that endpoint is no longer awaiting a
consumer.

**Scope -- NON-FIDELITY for `lem:full-cube-seed`.**  The depth is `0`, and
`12:16` fixes `b >= 1`; this is an instance of `def:robust-seed` only, exactly as
that module records.  It shows the base slot of `seedAnchoredNoFold_of_noReading`
is inhabited at a nondegenerate scale (budget `8`, a `2^126`-row carrier), and it
does **not** supply the scheduled-depth base, which stays owed (GAP-EXPOSED 2).

Claims no reader item. -/
theorem fullCubeSeed_certifiedBase :
    CertifiedAt
      (@Can (Fin 126 → Bool) (Fin 126) Bool _ fullCubeSeedRowOrder _ _ (2 ^ 126) 126
        (by simp) (by simp) (fullCube 126)) 8 0 ∧ 1 ≤ 8 :=
  certifiedBase_of_noReading _ 8 8 0 fullCubeSeed_noReading_transported

/-- **The span leg is satisfiable: it holds outright at requested depth zero**
(LANE-GATE 3, the hypothesis-consistency witness for all of Part 2).

At `x_out 0 = 1` the row clause of `def:bracket` forces `R = univ` (the banked
`OneLevelCompletion.bracket_row_univ`), so the retained matrix still contains the
`|J|`-dimensional identity submatrix carried by the frozen unit rows
`cubeUnit` (frozen `12:47--49`), and its one-output indicator has rank at least
`|J|` -- the frozen `12:59--60` floor `|J| - b` at `b = 0`.  The rank witness is
the banked `OneLevelCompletion.fin1_fun_ext` reading of the one-slot column tuple
together with a left inverse over the reals.

**NON-FIDELITY for `lem:full-cube-seed`:** the frozen subsection ranges over
`b >= 1`, so this is evidence that the hypothesis bundle of
`fullCube_bracket_ge_of_rankFloor` is not empty-by-construction -- it is not an
instance of the seed lemma, and it does not discharge GAP-EXPOSED 1, whose whole
content is that at `b >= 1` the row set is *not* everything.

General in the width and the column density.  Claims no reader item. -/
theorem fullCube_rankFloor_at_depth_zero (q : ℕ) (y : ℝ)
    (RC : Finset (Fin 1 × (Fin q → Bool)) × Finset (Fin 1 → Fin q))
    (hRC : RC ∈ bracketGE (Fin q → Bool) (Fin q) 1 (xOut 0) y) :
    (RC.2).card
      ≤ 0 + (indR (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2) true).rank := by
  classical
  obtain ⟨R, C⟩ := RC
  have hRuniv : R = Finset.univ := bracket_row_univ hRC
  simp only [Nat.zero_add]
  set ρ : {c // c ∈ C} → {a // a ∈ R} :=
    fun c => ⟨(0, cubeUnit q (c.val 0)), by rw [hRuniv]; exact Finset.mem_univ _⟩ with hρ
  have hval : ∀ (c c' : {c // c ∈ C}),
      subgame (interlaceFun (fullCube q) 1) R C (ρ c) c'
        = decide (c'.val 0 = c.val 0) := by
    intro c c'
    rfl
  set A := indR (subgame (interlaceFun (fullCube q) 1) R C) true with hA
  set Sm : Matrix {c // c ∈ C} {a // a ∈ R} ℝ :=
    Matrix.of (fun c a => if a = ρ c then (1 : ℝ) else 0) with hSm
  have hmul : Sm * A = 1 := by
    ext c c'
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (ρ c)]
    · simp only [hSm, Matrix.of_apply, hA, indR, hval c c', Matrix.one_apply]
      by_cases h : c'.val 0 = c.val 0
      · have hcc : c = c' := Subtype.ext (fin1_fun_ext h).symm
        simp [h, hcc]
      · have hcc : c ≠ c' := by
          intro hEq; exact h (by rw [hEq])
        simp [h, hcc]
    · intro d _ hd; simp [hSm, hd]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 : (1 : Matrix {c // c ∈ C} {c // c ∈ C} ℝ).rank = C.card := by
    rw [Matrix.rank_one, Fintype.card_coe]
  calc C.card = (Sm * A).rank := by rw [hmul, h1]
    _ ≤ A.rank := Matrix.rank_mul_le_right _ _

/-- **The reduction of Part 2 runs end to end on a discharged premise**
(LANE-GATE 3 -- NON-FIDELITY).

`fullCube_bracket_ge_of_rankFloor` fired at `q = 126`, `b = 0`, `d = 7`, column
density `3/5`, with **every** hypothesis discharged: the rung threshold by the
frozen ceiling `⌈126 * 3/5⌉ = 76 > 64 = 2^6`, and the span leg by
`fullCube_rankFloor_at_depth_zero`.  The conclusion reproduces the first rung of
the banked `OneLevelCompletion.fullCubeSeed_lambda`, from the general machinery
rather than from the depth-zero-only argument, which is the consistency check that
the generalization did not weaken anything.

**NON-FIDELITY:** `b = 0` is outside `12:16`'s range; this is evidence about the
machinery, not an instance of `lem:full-cube-seed`.

Claims no reader item. -/
theorem seedLambda_rankFloor_fires :
    8 ≤ Dfamily (interlaceFun (fullCube 126) 1)
      (bracketGE (Fin 126 → Bool) (Fin 126) 1 (xOut 0) ((3 : ℝ) / 5)) := by
  have h := fullCube_bracket_ge_of_rankFloor 126 0 7 (by norm_num) ((3 : ℝ) / 5)
    (by norm_num) ?_ ?_
  · simpa using h
  · rw [Fintype.card_fin]
    exact Nat.lt_ceil.mpr (by norm_num)
  · intro RC hRC
    exact fullCube_rankFloor_at_depth_zero 126 ((3 : ℝ) / 5) RC hRC

/-- **The seed-anchored fold fires, with a non-empty per-level range --
NON-FIDELITY** (LANE-GATE 3).

`CertificateCarryingFold.certificateCarryingNoFold_fires` consumed by pin at the
**specialized** depth stream: the banked NON-FIDELITY probe chain satisfies every
hypothesis of the fold at `b_i = B(n)` for every `i`, at every level count `k` and
hence in particular at `k >= 1`, where the frozen family `0 <= i < k` is non-empty
and the step hypothesis genuinely fires.  So specializing the depth family did not
make the fold vacuous.

**It remains NON-FIDELITY**: the probe's certified budget is the constant `0`,
below the frozen entry floor `3 <= D` of `step:L-03`, and its level matrices are
constant.  Canonical inhabitation of the fold by the paper's own chain needs the
unbuilt Stage-1--4 constructor chain and stays REGISTERED AS DEFERRED
(GAP-EXPOSED 3).

General in the specification, the source size, the level count and the level.
Claims no reader item. -/
theorem seedAnchoredNoFold_fires (S : FixedLevelCarriers.LevelCarrierSpec)
    (n k j : ℕ) (hj : j ≤ k) :
    LevelCertified (probeConstChain S) (fun _ => 0) (seedDepthStream n) j :=
  certificateCarryingNoFold_fires S (seedDepthStream n) k j hj

end EthInapproximability.ParameterizedNP.SeedAnchoredFold
