import EthInapproximability.ParameterizedNP.FixedLevelCarriers

/-!
# Parameterized NP route: the dominant branch of `Q_0`, and the width growth it makes visible

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).
Ledger row: opened under **`SIZE-001`** (the width half of the size thread:
`SizePropagation.lean` owns the *logarithmic side-length* majorants, this module
owns the *outer interlace width* and the two carrier consequences it forces).
The three-branch shape of `Q_0` itself belongs to **`BRIDGE-ENTRY-001`** and the
carrier recurrence to **`ITER-001`**; both are **consumed by pin**, never
restated or re-derived here
(`routes/parameterized-np/autoformalization/OBLIGATION_LEDGER.md`).

All references are to the **frozen** release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`.

## The one fact this module lands

`06-parameter-schedule.tex`, `eq:Q-theta-choice` (label line 537), **display
lines 529--531**, opened and read first-hand this tranche:

```
Q_0 = \max\left\{ \frac{8\bout}{\delta\delta_U}, \frac8\delta, 16 \right\},
Q   = the least power of two at least Q_0,                         (06:529--532)
```

and the same schedule *composed with `eq:q-deltaU`* (`06:513--519`,
`delta_U = eta_R/(16 q)` at line 517), which the assembly section prints as one
display in `11-one-level-assembly.tex`, `step:L-11`, **lines 648--656**:

```
delta_U = eta_R/(16 q),
Q_0 = \max\{ 80\bout/\delta_U, 80, 16 \},   theta = 1/(160 Q).      (11:650--656)
```

At that composed point the maximum sits on its **first** branch,
`8 b_out/(delta delta_U)`, and the constant branches `8/delta = 80` and `16`
are inoperative.  Evaluating the branch through the definitional chain gives

```
Q_0 = 1280 b_out q / eta_R  >=  47 104 000 * b_out * q,
```

the inequality because the schedule's own ceiling `eta_R <= 1/36800`
(`ParameterSchedule.etaR_le_bound`, the first branch `mu_Sigma/100 = 1/18400`
of `eq:eta-choice` halved) is the *largest* value `eta_R` can take.  The
constant `47104000 = 1280 * 36800` is therefore **not an invented numeral**: it
is `8 * 10` (the `8/delta` numerator at the route's fixed `delta = 1/10`) times
`16` (the denominator of `eq:q-deltaU` line 517) times `36800`, each factor
read off a frozen display or a banked lemma about one.

Because `Q_0 <= Q < 2 Q_0` (`11:80` and `11:658--659`, banked as
`EntryGates.Q0_le_Qwidth` and `EntryGates.two_pow_pred_lt_Q0`), the same bound
holds for the **width** `Q` itself, and is two-sided.

## Why this is worth a module: width growth becomes visible

Before this tranche the only unconditional lower bound on the outer width in
Lean was the constant floor `16 <= Q_i` -- `FixedLevelCarriers.sixteen_le_Q`,
whose own docstring records the deficiency verbatim:

> "Conclusion 5 is the unconditional `Q_i >= 16` of aux 6, which is a *floor*:
> at the instance's own evaluated `delta_U` the schedule's
> `Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}` is far larger, and nothing
> here claims otherwise."

A constant floor is invisible to a size argument.  What is landed here is the
missing comparison `Q_i >= 47104000 * b_i * q_i`, i.e. **the outer interlace
width grows at least linearly in the inner one**, and the two consequences that
follow from it through the frozen carrier recurrence.

## The Sections 12--13 consequences that are landed

`12-iteration-specification.tex`, `thm:fixed-level-gap-size` (label line 192),
clause (ii), `eq:fixed-level-carriers` (label line 264, display lines 260--265):

```
m_{i+1} = (q_i m_{N,i})^{Q_i},      n_{i+1} = Q_i (n_{N,i})^{q_i}.  (12:261--263)
```

Combining the width bound with these two equations, at every level of every
specification whose tolerance is the schedule's own:

* the **row** carrier is at least `2^{47104000 b_i q_i}` -- the outer width sits
  in the exponent, so a linear width bound becomes an exponential carrier bound
  (`levelRowCarrier_growth`);
* since `q_i = 2^{A_wrap,i L_{P,i}^2}` (`eq:q-deltaU`, `06:515`), that is at
  least `2^{2^{A_wrap,i L_{P,i}^2}}`: the row carrier is **doubly exponential in
  the wrapper exponent** (`levelRowCarrier_doubly_exponential`);
* the **column** carrier is at least `47104000 b_i q_i`, because there `Q_i`
  multiplies rather than exponentiates (`levelColCarrier_growth`).  The
  asymmetry of the two frozen equations is thus visible as an asymmetry of the
  two bounds, which is the kernel content of `12:261` versus `12:263`.

## What is *not* landed from Section 13, and why

`13-iteration-assembly.tex`, `eq:iteration-successor-majorant` (label line 310,
display lines 307--308) bounds "every newly constructed auxiliary width other
than the numerical source width ... by `E_{16(c_r+1)}(n) = E_{c_{r+1}}(n)`", and
lines 311--313 add that only `q_{2,r+1}` is treated separately.  That is an
**upper** envelope on the same widths this module bounds from below.  It is a
statement about the envelope family `E_c`, whose realization is `EFFECTIVE-001`
and `SIZE-001`'s `iteratedSizeMajorant`, and it is **not claimed here** -- see
GAP-EXPOSED 2.  What *is* recorded is that the two directions are compatible:
`scheduleQwidth_sandwich` gives the frozen two-sided `Q_0 <= Q < 2 Q_0` at the
composed schedule point, so the lower bound landed here is not an unbounded one
and cannot contradict any upper envelope.

## Reader counterparts

The reader artifact of the same frozen release,
`routes/parameterized-np/reader-facing/sections/`, was opened first-hand this
tranche and every candidate item read in place.

**No reader item is claimed by this module, and the reason is recorded.**  The
reader displays `Q_0` exactly once, at `eq:bridge-Q0`
(`04-bridge.tex`, label line 92, display lines 88--93), and its least-power-of-two
sentence exactly once, at `04-bridge.tex:94`; both were read again this tranche
and both are already assigned, to `EntryGates.Q0` and to
`EntryGates.rQ`/`Qwidth`/`Qwidth_least` respectively, under `BRIDGE-ENTRY-001`.
Re-citing either would be the double assignment the reader-counterpart rule
forbids.  The reader **never** displays the composed schedule point: it does not
print `delta_U = eta_R/(16 q)` anywhere (its only occurrence of `eta_R` is
`A-stage4-details.tex:217`, a Stage-4 retained-density display), and it never
states that a branch of the maximum is the operative one.  The carrier
recurrence the consequences consume is the reader's
`eq:paper-exact-carrier-recurrence` (`05-iteration.tex`, label line 166), which
is `IterationAssembly.iterationCarrierStep`'s and is named here as **navigation
only**.

`05-iteration.tex:176` -- "The parameter theorem below proves that
`z(N_i), q_i, Q_i = n^{o(1)}` at every fixed level" -- is the nearest reader
sentence in subject matter.  It is **prose, not a display, and is deliberately
not cited as a statement**; it is also an *upper* estimate, whereas everything
below is a lower bound, and the two are consistent (`q_i` and `Q_i` are within a
constant-times-`b_i` factor of each other here, so an `n^{o(1)}` bound on one is
compatible with this bound on the other).

Crosswalk row: none added; this module rides `SIZE-001`'s existing row.

## Status and dependencies

* Proof status: **new (elementary)** throughout.  Every declaration is either a
  substitution of one frozen display into another, or a general property of such
  a substitution, or the frozen carrier recurrence applied to it.  No
  communication-complexity lemma is introduced, adapted, or re-proved, and no
  banked module is edited.
* Consumed by pin, never restated: `EntryGates.Q0`, `.Q0_eq_route`,
  `.Q0_second_le`, `.Q0_le_Qwidth`, `.two_pow_pred_lt_Q0`;
  `ParameterSchedule.deltaU`, `.deltaU_pos`, `.deltaU_lt_one`, `.etaR`,
  `.etaR_pos`, `.etaR_le_bound`, `.qWrap`, `.sScale`, `.uAux`, `.Apre`,
  `.P0sched`, `.LPwidth`, `.cSeed`, `.sScale_floor`, `.three_le_uAux`,
  `.hundredOne_le_of_cSeed_lt`; `IterationAssembly.carrierRowNext`,
  `.carrierColNext`, `.depthB`; `FixedLevelCarriers.LevelCarrierSpec`,
  `.two_le_q`, `.sixteen_le_Q`, `.paperSeedSpec`,
  `.paperSeedSpec_deltaU_at_own_inner_width`, `.seedAnchor_inside_frozen_range`.
* Imports: `EthInapproximability.ParameterizedNP.FixedLevelCarriers` only, hence
  `IterationAssembly`, `ParameterSchedule`, `EntryGates`, and
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not** imported, so the
  AGHP balanced-family axiom is not in scope, and there is no contact with
  `EXPANDER-001` (which by design has no Lean declaration).
* External adapters: none.  Nothing here is axiomatized; no new `axiom`, no
  opaque certificate.
* Axiom surface (Appendix D, and `#print axioms` in `tools/AxiomAudit.lean`): at
  most `propext`, `Classical.choice`, `Quot.sound`.

## Faithfulness notes (mechanical rules M1--M10)

* **No new structure is introduced.**  `ScheduleTolerance` is a `Prop`
  abbreviation for the single equation `delta_{U,i} = eta_R/(16 q_i)` that
  `eq:q-deltaU` line 517 displays, one per level -- not a bundle, and not a
  field on `LevelCarrierSpec` (adding it there would restate a derived
  telescope on a record the frozen hypothesis block F1--F2 does not carry it
  on).  Every deliverable takes it, and the depth guard `1 <= b_i`, as
  **explicit binders**.
* **DEFINED-vs-FREE.**  `delta_U` is DEFINED by `eq:q-deltaU` line 517 and is
  never assigned; `Q_0` is DEFINED by `eq:Q-theta-choice` line 529 and is never
  assigned; `Q` is DEFINED by line 532 and is never assigned; `eta_R` is DEFINED
  by `eq:eta-choice` (`06:212--217`) and enters only through the banked
  `etaR_le_bound`/`etaR_pos`.  The one arithmetic constant that appears,
  `47104000`, is the *value of a product of three frozen factors*, and is
  derived in the docstring of the lemma that introduces it rather than chosen.
  `s`, `delta_v(G)`, `zeta`, `b_out`, `q` stay symbolic exactly where the
  schedule layer itself leaves them symbolic.
* **The `16` branch.**  `Q0_sixteen_branch_never_operative` shows the third
  branch is inoperative *unconditionally* -- once the route's fixed
  `delta = 1/10` is substituted, `8/delta = 80 > 16`, so no hypothesis at all is
  needed.  This strictly strengthens the banked
  `EntryGates.Q0_gt_sixteen_of_route`, which carried three hypotheses; the
  banked lemma is not edited, and the strengthening is recorded here as an aux
  lemma rather than pushed back into `BRIDGE-ENTRY-001`'s module.
* **Trivial-witness pole.**  The one existential deliverable,
  `widthGrowth_hypotheses_consistent`, pins both witnesses by *equations to
  their defining chains* (`s = sScale B_s (uAux (Apre ...))`,
  `q = qWrap A_wrap (LPwidth (P0sched ...))`).  A "take something convenient"
  witness -- say `s = 64`, `q = 2` -- does not satisfy the statement, because
  those two equations are not satisfied by it; that is precisely why the
  statement is an existential over *pinned* values rather than a claim that some
  legal point exists.
* **Vacuous-hypothesis pole.**  `ScheduleTolerance` is not free:
  `widthGrowth_fails_at_free_tolerance` exhibits a `delta_U` inside the frozen
  legality range `0 < delta_U < 1` of `10-direct-bridge.tex:38` at which the
  growth conclusion is **false**.  So the conclusion genuinely uses the
  schedule's defining equation and not merely the bridge's legality range.
* Both widths stay distinct throughout: `q_i` is the inner scale-alignment width
  of `eq:q-deltaU` and `Q_i` the outer bridge width of `eq:Q-theta-choice`, and
  the two carrier consequences read them in the exchanged roles the frozen
  display prints.

## GAP-EXPOSED

1. **`Q_0`'s branch structure is used, not re-proved.**  `Q0_eq_route`
   (`BRIDGE-ENTRY-001`) supplies the identification of the operative branch at
   `1 <= b_out`, `0 < delta_U < 1`; this module supplies only the composition
   with `eq:q-deltaU` and the resulting growth.
2. **`eq:iteration-successor-majorant` (`13:307--313`) is not claimed.**  The
   upper envelope `E_{16(c_r+1)}(n)` on newly constructed auxiliary widths, the
   separate treatment of `q_{2,r+1} < 24 s_{r+1} |E(G)|`, and the entire
   envelope realization stay with `SIZE-001`'s `iteratedSizeMajorant` and
   `EFFECTIVE-001`.  Only the two-sided `Q_0 <= Q < 2 Q_0` of `11:658--659` is
   landed as the compatibility record.
3. **The pre-wrapper counts `m_{N,i}`, `n_{N,i}` remain binders.**  They are
   `|Rows(N_i)|`, `|Cols(N_i)|` for the unbuilt Stage-1--4 chain, so the
   carrier consequences below hold *at every legal value* of them, which is
   strictly stronger than a choice, and the canonical inhabitation of those two
   counts stays the deferred obligation `FixedLevelCarriers` GAP-EXPOSED 2
   registers.  Nothing here discharges it.
4. **No asymptotic statement is made.**  `q_i, Q_i = n^{o(1)}` (reader line 176,
   autoformalization `thm:effective-parameter-schedule`) is not claimed, in
   either direction.
5. **No route completion is claimed.**  The Stage-1-to-Stage-4 chain, the
   materialization, and the ETH consequence are untouched.
-/

namespace EthInapproximability.ParameterizedNP.DominantWidthBound

open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.ParameterSchedule
open EthInapproximability.ParameterizedNP.IterationAssembly
open EthInapproximability.ParameterizedNP.FixedLevelCarriers

/-! ## Part 1: the composed schedule point `11:648--656`

`eq:Q-theta-choice` (`06:529--531`) evaluated at the `delta_U` that
`eq:q-deltaU` (`06:517`) defines.  Every quantity is obtained by *evaluating*
the definitional chain `eta_C -> eta_R -> delta_U -> Q_0 -> Q`; nothing is
assigned. -/

/-- **Aux 1 (the `16` branch is inoperative, unconditionally).**

`eq:Q-theta-choice` (`06:529--531`) reads
`Q_0 = max{8 b_out/(delta delta_U), 8/delta, 16}`.  At the route's globally
fixed `delta = 1/10` (`10-direct-bridge.tex:37`, `03-preliminaries.tex:216--219`)
the *second* branch is already `8/delta = 80 > 16`, so the third branch never
attains the maximum -- for **every** `b_out` and **every** `delta_U`, with no
legality hypothesis whatever.

This strictly strengthens the banked `EntryGates.Q0_gt_sixteen_of_route`, which
needed `1 <= b_out` and `0 < delta_U < 1`.  The banked lemma is consumed
elsewhere unchanged and is not edited.  General. -/
theorem Q0_sixteen_branch_never_operative (bout : ℕ) (δU : ℝ) :
    (16 : ℝ) < Q0 bout δU := by
  have h80 : (8 : ℝ) / deltaFixed ≤ Q0 bout δU := Q0_second_le bout δU
  rw [deltaFixed_eq] at h80
  norm_num at h80
  linarith

/-- **The maximum sits on its first branch at the schedule's own tolerance.**

`06:529--531` composed with `06:517`, i.e. the display `11:650--654`.  At the
schedule's `delta_U = eta_R/(16 q)` -- positive by `etaR_pos` at the frozen side
conditions of `eq:eta-choice` (`06:212--217`), and below `1` by the banked
`deltaU_lt_one` -- the three-branch maximum of `eq:Q-theta-choice` **equals its
first branch**, written here in the frozen unevaluated symbols
`8 b_out/(delta delta_U)`.

So the operative branch is the one carrying the requested output depth and the
deletion tolerance, not either constant; a witness sitting on `8/delta` or on
`16` would be the degenerate inhabitant this excludes.  The branch structure
itself is the banked `EntryGates.Q0_eq_route` and is not re-derived. -/
theorem scheduleQ0_first_branch {bout s : ℕ} {dv zeta : ℝ} {q : ℕ}
    (hb : 1 ≤ bout) (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) :
    Q0 bout (deltaU (etaR s dv zeta) q)
      = 8 * (bout : ℝ) / (deltaFixed * deltaU (etaR s dv zeta) q) := by
  have hpos : 0 < deltaU (etaR s dv zeta) q :=
    deltaU_pos (etaR_pos hs hdv hz) hq
  have hlt : deltaU (etaR s dv zeta) q < 1 :=
    deltaU_lt_one (s := s) (dv := dv) (zeta := zeta) hq
  have hne : deltaU (etaR s dv zeta) q ≠ 0 := ne_of_gt hpos
  rw [Q0_eq_route hb hpos hlt, deltaFixed_eq]
  field_simp
  ring

/-- **The operative branch, evaluated through the definitional chain.**

Substituting `delta = 1/10` (`10-direct-bridge.tex:37`) and
`delta_U = eta_R/(16 q)` (`eq:q-deltaU`, `06:517`) into the first branch of
`eq:Q-theta-choice` (`06:529--531`) gives

```
Q_0 = 8 b_out / (delta * eta_R/(16 q)) = 1280 b_out q / eta_R.
```

The factor `1280 = 8 * 10 * 16` is the product of the frozen numerator `8`
(line 530), the reciprocal of the fixed `delta = 1/10`, and the denominator `16`
of `eq:q-deltaU` line 517.  Nothing is assigned: both `b_out` and `q` stay
symbolic and `eta_R` is the banked `eq:eta-choice` accessor. -/
theorem scheduleQ0_eq_evaluated {bout s : ℕ} {dv zeta : ℝ} {q : ℕ}
    (hb : 1 ≤ bout) (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) :
    Q0 bout (deltaU (etaR s dv zeta) q)
      = 1280 * (bout : ℝ) * (q : ℝ) / etaR s dv zeta := by
  have hpos : 0 < deltaU (etaR s dv zeta) q :=
    deltaU_pos (etaR_pos hs hdv hz) hq
  have hlt : deltaU (etaR s dv zeta) q < 1 :=
    deltaU_lt_one (s := s) (dv := dv) (zeta := zeta) hq
  have heR : etaR s dv zeta ≠ 0 := ne_of_gt (etaR_pos hs hdv hz)
  have hqR : ((q : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt this
  rw [Q0_eq_route hb hpos hlt, deltaU]
  field_simp
  ring

/-- **The dominant-branch width bound.**

The frozen ceiling `eta_R <= 1/36800` (`ParameterSchedule.etaR_le_bound`, the
first branch `mu_Sigma/100 = 1/18400` of `eq:eta-choice` `06:212--217` halved)
is the largest value `eta_R` can take, so the evaluated first branch of
`eq:Q-theta-choice` obeys

```
Q_0 = 1280 b_out q / eta_R >= 1280 * 36800 * b_out * q = 47104000 * b_out * q.
```

**The constant is derived, not chosen:** `47104000 = 1280 * 36800`, and `1280`
is itself `8 * 10 * 16` from `06:530`, `delta = 1/10`, and `06:517`.  This is the
comparison that makes the outer interlace width grow with the inner one; the
banked floor `Q_i >= 16` cannot see it. -/
theorem scheduleQ0_growth {bout s : ℕ} {dv zeta : ℝ} {q : ℕ}
    (hb : 1 ≤ bout) (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) :
    (47104000 : ℝ) * (bout : ℝ) * (q : ℝ)
      ≤ Q0 bout (deltaU (etaR s dv zeta) q) := by
  have heRpos : 0 < etaR s dv zeta := etaR_pos hs hdv hz
  have heRle : etaR s dv zeta ≤ 1 / 36800 := etaR_le_bound s dv zeta
  have hbR : (1 : ℝ) ≤ (bout : ℝ) := by exact_mod_cast hb
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hprod : (0 : ℝ) ≤ (bout : ℝ) * (q : ℝ) := by nlinarith
  rw [scheduleQ0_eq_evaluated hb hs hdv hz hq, le_div_iff₀ heRpos]
  nlinarith

/-- **The same bound on the width `Q` itself, in `ℕ`.**

`06:532`, "`Q` = the least power of two at least `Q_0`", banked as
`EntryGates.Q0_le_Qwidth`.  A width is a copy count, so the statement is an
inequality of natural numbers. -/
theorem scheduleQwidth_growth {bout s : ℕ} {dv zeta : ℝ} {q : ℕ}
    (hb : 1 ≤ bout) (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) :
    47104000 * bout * q ≤ Qwidth bout (deltaU (etaR s dv zeta) q) := by
  have hlow := scheduleQ0_growth hb hs hdv hz hq
  have hup := Q0_le_Qwidth bout (deltaU (etaR s dv zeta) q)
  have : ((47104000 * bout * q : ℕ) : ℝ)
      ≤ ((Qwidth bout (deltaU (etaR s dv zeta) q) : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **Aux 2 (the frozen two-sided sandwich, at the composed schedule point).**

`11-one-level-assembly.tex:80` and `11:658--659`: "`Q = 2^{r_Q}` is the least
power of two at least `Q_0`, so `Q_0 <= Q < 2 Q_0`."  Read at the schedule's own
`delta_U`, both sides become explicit:

```
1280 b_out q / eta_R  <=  Q  <  2560 b_out q / eta_R.
```

Recorded so that the lower bound above is visibly **not** an unbounded claim:
the width is pinned inside a factor-two window around the evaluated threshold,
which is what keeps it compatible with the upper envelope of
`eq:iteration-successor-majorant` (`13:307--313`, GAP-EXPOSED 2). -/
theorem scheduleQwidth_sandwich {bout s : ℕ} {dv zeta : ℝ} {q : ℕ}
    (hb : 1 ≤ bout) (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) :
    1280 * (bout : ℝ) * (q : ℝ) / etaR s dv zeta
        ≤ ((Qwidth bout (deltaU (etaR s dv zeta) q) : ℕ) : ℝ) ∧
      ((Qwidth bout (deltaU (etaR s dv zeta) q) : ℕ) : ℝ)
        < 2560 * (bout : ℝ) * (q : ℝ) / etaR s dv zeta := by
  have heval := scheduleQ0_eq_evaluated hb hs hdv hz hq
  have hlow := Q0_le_Qwidth bout (deltaU (etaR s dv zeta) q)
  have hhigh := two_pow_pred_lt_Q0 bout (deltaU (etaR s dv zeta) q)
  rw [heval] at hlow hhigh
  refine ⟨hlow, lt_of_lt_of_le hhigh (le_of_eq ?_)⟩
  ring

/-- **Aux 3 (a wider inner interlace forces a wider outer one).**

Monotonicity of the composed threshold in the scale-alignment width `q`.  The
two frozen displays pull in the same direction here: `eq:q-deltaU` line 517
makes `delta_U` shrink as `q` grows, and `eq:Q-theta-choice` line 530 makes
`Q_0` grow as `delta_U` shrinks (the banked `EntryGates.Q0_antitone_deltaU`).
General in both widths and in the source-side scalars. -/
theorem scheduleQ0_mono_width {bout s : ℕ} {dv zeta : ℝ} {q q' : ℕ}
    (hs : 3 < s) (hdv : 0 < dv) (hz : 0 < zeta) (hq : 0 < q) (h : q ≤ q') :
    Q0 bout (deltaU (etaR s dv zeta) q)
      ≤ Q0 bout (deltaU (etaR s dv zeta) q') := by
  have heRpos : 0 < etaR s dv zeta := etaR_pos hs hdv hz
  have hq' : 0 < q' := lt_of_lt_of_le hq h
  have hposq' : 0 < deltaU (etaR s dv zeta) q' := deltaU_pos heRpos hq'
  have hmono : deltaU (etaR s dv zeta) q' ≤ deltaU (etaR s dv zeta) q := by
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hqR' : (q : ℝ) ≤ (q' : ℝ) := by exact_mod_cast h
    rw [deltaU, deltaU]
    gcongr
  exact Q0_antitone_deltaU hposq' hmono

/-! ## Part 2: the level-indexed wiring, and the Sections 12--13 consequences

The banked `FixedLevelCarriers.LevelCarrierSpec` carries `delta_{U,i}` as a
*field*, because `thm:fixed-level-gap-size`'s hypothesis block F1--F2 records it
as public data.  The schedule's defining equation for that field is therefore an
**explicit premise** here, never a new record field. -/

/-- **The schedule's own tolerance, level by level** -- `eq:q-deltaU`
(`06-parameter-schedule.tex:513--519`), whose two equations
`q = 2^{A_wrap L_P^2}` (line 515) and `delta_U = eta_R/(16 q)` (line 517) are one
display read at the **same** width.

A `Prop` abbreviation for exactly that one equation at every level, with the
source scale `s` and the source-side scalars `delta_v(G)`, `zeta` of
`eq:eta-choice` (`06:212--217`) as explicit arguments.  It is deliberately
*not* a field of `LevelCarrierSpec`: the frozen hypothesis block quantifies the
public tolerance before the schedule is compiled, and a record field would
restate a derived telescope.  It is also not a bundle -- it is a single
equation. -/
def ScheduleTolerance (S : LevelCarrierSpec) (s : ℕ) (dv zeta : ℝ) : Prop :=
  ∀ i, S.dU i = deltaU (etaR s dv zeta) (S.q i)

/-- **Aux 4 (the premise is exactly one equation, per level).**

The unfolding, recorded so that no later proof needs to look inside the
definition.  General. -/
theorem scheduleTolerance_iff (S : LevelCarrierSpec) (s : ℕ) (dv zeta : ℝ) :
    ScheduleTolerance S s dv zeta
      ↔ ∀ i, S.dU i = deltaU (etaR s dv zeta) (S.q i) :=
  Iff.rfl

/-- **The outer width grows at least linearly in the inner width, at every
level.**

`eq:Q-theta-choice` (`06:529--532`) composed with `eq:q-deltaU` (`06:517`), read
at level `i` of a specification whose tolerance field is the schedule's own:

```
Q_i >= 47104000 * b_i * q_i.
```

The depth guard `1 <= b_i` is the frozen `b_out >= 1` of
`10-direct-bridge.tex:41` and appears as an explicit binder; the three side
conditions `3 < s`, `0 < delta_v(G)`, `0 < zeta` are `eq:eta-choice`'s own and
are not new demands.  General in the specification and the level. -/
theorem levelQ_growth (S : LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance S s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ S.bout i) :
    47104000 * S.bout i * S.q i ≤ S.Q i := by
  have hq : 0 < S.q i := by
    have := two_le_q S i
    omega
  have hQ : S.Q i = Qwidth (S.bout i) (deltaU (etaR s dv zeta) (S.q i)) := by
    change Qwidth (S.bout i) (S.dU i) = _
    rw [hsched i]
  rw [hQ]
  exact scheduleQwidth_growth hb hs hdv hz hq

/-- **Aux 5 (the outer width dominates the inner one).**

The immediate corollary `q_i <= Q_i`: at the schedule point the bridge width is
never smaller than the scale-alignment width.  Recorded because it is the form
the two carrier equations of `12:261--263` actually consume, and because it is
the qualitative statement the banked constant floor `Q_i >= 16` could not
supply.  General in the specification and the level. -/
theorem levelQ_dominates_q (S : LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance S s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ S.bout i) :
    S.q i ≤ S.Q i := by
  have hgrow := levelQ_growth S hsched hs hdv hz i hb
  have hstep : S.q i ≤ 47104000 * S.bout i * S.q i :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **Section 12 consequence, row half.**

`eq:fixed-level-carriers` (`12-iteration-specification.tex`, label line 264),
row equation at line 261: `m_{i+1} = (q_i m_{N,i})^{Q_i}`.  The outer width sits
in the **exponent**, so the linear width bound of `levelQ_growth` becomes an
exponential carrier bound:

```
m_{i+1} >= 2^{47104000 b_i q_i}.
```

The base estimate `q_i m_{N,i} >= 2` is the frozen realized-input invariant of
`02-mechanical-contract.tex:771--775`, discharged from the specification's own
guards by the banked `FixedLevelCarriers.two_le_q` and `one_le_mN`.  The
recorded pre-wrapper count `m_{N,i}` stays a binder (GAP-EXPOSED 3), so this
holds at every legal value of it.  General in the specification and the
level. -/
theorem levelRowCarrier_growth (S : LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance S s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ S.bout i) :
    2 ^ (47104000 * S.bout i * S.q i) ≤ S.rowCarrier (i + 1) := by
  have hgrow := levelQ_growth S hsched hs hdv hz i hb
  have hbase : 2 ≤ S.q i * S.mN i :=
    le_trans (two_le_q S i) (Nat.le_mul_of_pos_right _ (S.one_le_mN i))
  calc (2 : ℕ) ^ (47104000 * S.bout i * S.q i)
      ≤ 2 ^ S.Q i := Nat.pow_le_pow_right (by norm_num) hgrow
    _ ≤ (S.q i * S.mN i) ^ S.Q i := Nat.pow_le_pow_left hbase _
    _ = S.rowCarrier (i + 1) := rfl

/-- **Section 12 consequence, column half.**

`eq:fixed-level-carriers`, column equation at line 263:
`n_{i+1} = Q_i (n_{N,i})^{q_i}`.  Here the widths are in their **exchanged**
roles -- `Q_i` multiplies and `q_i` exponentiates -- so the same width bound
gives only a linear carrier bound:

```
n_{i+1} >= 47104000 b_i q_i.
```

The asymmetry between this and `levelRowCarrier_growth` is the kernel content of
the asymmetry between frozen lines 261 and 263; a transcription that read the
two widths in the same role on both sides could not produce it.  General in the
specification and the level. -/
theorem levelColCarrier_growth (S : LevelCarrierSpec) {s : ℕ} {dv zeta : ℝ}
    (hsched : ScheduleTolerance S s dv zeta) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ S.bout i) :
    47104000 * S.bout i * S.q i ≤ S.colCarrier (i + 1) := by
  have hgrow := levelQ_growth S hsched hs hdv hz i hb
  have hpow : 1 ≤ S.nN i ^ S.q i := Nat.one_le_pow _ _ (S.one_le_nN i)
  calc 47104000 * S.bout i * S.q i ≤ S.Q i := hgrow
    _ = S.Q i * 1 := (Nat.mul_one _).symm
    _ ≤ S.Q i * S.nN i ^ S.q i := Nat.mul_le_mul_left _ hpow
    _ = S.colCarrier (i + 1) := rfl

/-- **The row carrier is doubly exponential in the wrapper exponent.**

Substituting `q_i = 2^{A_wrap,i L_{P,i}^2}` (`eq:q-deltaU`, `06:515`) into the
row bound above, and discarding the constant and the depth factor, gives

```
m_{i+1} >= 2^{q_i} = 2^{2^{A_wrap,i L_{P,i}^2}}.
```

This is the shape the size argument needs to see: one level of the fold squares
the *logarithm* of the row side length into an exponent, so the carrier growth
is driven by the wrapper exponent `A_wrap L_P^2` and not by the constant floor
`16`.  `S.qExp i` is the banked `FixedLevelCarriers.innerExp`, i.e. the exponent
`A_wrap,i L_{P,i}^2` itself.  General in the specification and the level. -/
theorem levelRowCarrier_doubly_exponential (S : LevelCarrierSpec) {s : ℕ}
    {dv zeta : ℝ} (hsched : ScheduleTolerance S s dv zeta) (hs : 3 < s)
    (hdv : 0 < dv) (hz : 0 < zeta) (i : ℕ) (hb : 1 ≤ S.bout i) :
    2 ^ (2 ^ S.qExp i) ≤ S.rowCarrier (i + 1) := by
  have hrow := levelRowCarrier_growth S hsched hs hdv hz i hb
  have hqval : (2 : ℕ) ^ S.qExp i = S.q i := rfl
  have hstep : S.q i ≤ 47104000 * S.bout i * S.q i :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmono : (2 : ℕ) ^ S.q i ≤ 2 ^ (47104000 * S.bout i * S.q i) :=
    Nat.pow_le_pow_right (by norm_num) hstep
  rw [hqval]
  exact le_trans hmono hrow

/-! ## Part 3: canonical inhabitation -- the paper's own instance

The fidelity test is whether the paper's own specification satisfies the premise
and the conclusions, not whether some specification does.  The banked
`FixedLevelCarriers.paperSeedSpec` is the instance of the frozen application
site `12:360--368`, with `delta_{U,i}` obtained by *evaluating* `eq:q-deltaU` at
that instance's own inner width. -/

/-- **Canonical inhabitation of the premise (the paper's instance).**

`FixedLevelCarriers.paperSeedSpec` satisfies `ScheduleTolerance` at the same
source scale and source-side scalars, definitionally: its `dU` field *was*
obtained by evaluating `eq:q-deltaU` line 517 at its own inner width, which is
the banked `paperSeedSpec_deltaU_at_own_inner_width`.  A version of
`paperSeedSpec` with a free `dU` binder could not satisfy this. -/
theorem paperSeedSpec_scheduleTolerance (n C0 B0 Ccert s lq2 clU0 zR : ℕ)
    (dv zeta : ℝ) (mN nN : ℕ → ℕ) (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i) :
    ScheduleTolerance
      (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN)
      s dv zeta :=
  fun i =>
    paperSeedSpec_deltaU_at_own_inner_width n C0 B0 Ccert s lq2 clU0 zR dv zeta
      mN nN hmN hnN i

/-- **The width growth fires at the paper's own instance.**

Six conclusions about one inhabitant, at legal parameter values, with the
outgoing depth taken from the frozen application site rather than chosen:

1. the instance's requested depth is the frozen `b_i = B(n) = E_2(n)` of
   `12:360--368`, and `B(n) >= 512` for every `n >= 1` (banked
   `seedAnchor_inside_frozen_range`), so the depth guard `1 <= b_i` of
   `10-direct-bridge.tex:41` is **derived**, not assumed;
2. `eq:Q-theta-choice`'s maximum sits on its first branch,
   `8 b_i/(delta delta_{U,i})`, at the instance's own evaluated tolerance;
3. the `16` floor is strictly below it;
4. the outer width obeys `Q_i >= 47104000 * 512 * q_i` -- the bound the banked
   `Q_i >= 16` could not supply;
5. the row carrier obeys `m_{i+1} >= 2^{47104000 * 512 * q_i}`
   (`eq:fixed-level-carriers` row equation, `12:261`);
6. the column carrier obeys `n_{i+1} >= 47104000 * 512 * q_i`
   (column equation, `12:263`).

The free inputs left universally quantified are exactly those the frozen
schedule layer itself leaves symbolic -- the recorded coefficient table
`C_0, B_0`, the threshold inputs `C_cert, log_2 q_2, ceil(log_2 U_0), z_R`, the
source scale `s`, and `delta_v(G)`, `zeta` -- together with the two pre-wrapper
counts of the unbuilt Stage-4 chain (GAP-EXPOSED 3).  That is strictly stronger
than exhibiting one choice of them.

**Fidelity.**  Conclusion 1 is the paper's own level-zero data; conclusions 2--6
are evaluated through the definitional chain
`eta_C -> eta_R -> delta_U -> Q_0 -> Q -> carriers`, with no numeral assigned to
any quantity the frozen source defines. -/
theorem paperSeedSpec_widthGrowth_fires (n C0 B0 Ccert : ℕ) {s : ℕ}
    (lq2 clU0 zR : ℕ) {dv zeta : ℝ} (hn : 1 ≤ n) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (mN nN : ℕ → ℕ) (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i)
    (i : ℕ) :
    512 ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).bout i ∧
      Q0 ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).bout i)
          ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i)
        = 8 * (((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).bout i : ℕ) : ℝ)
            / (deltaFixed
                * (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i) ∧
      (16 : ℝ)
        < Q0 ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).bout i)
            ((paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).dU i) ∧
      47104000 * 512
          * (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).q i
        ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).Q i ∧
      2 ^ (47104000 * 512
            * (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).q i)
        ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).rowCarrier (i + 1) ∧
      47104000 * 512
          * (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).q i
        ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).colCarrier (i + 1) := by
  set S := paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN with hS
  have hsched : ScheduleTolerance S s dv zeta :=
    paperSeedSpec_scheduleTolerance n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN
  have hdepth : S.bout i = depthB n := rfl
  have h512 : 512 ≤ S.bout i := by
    rw [hdepth]
    exact (seedAnchor_inside_frozen_range n hn).2
  have hb : 1 ≤ S.bout i := by omega
  have hq : 0 < S.q i := by
    have := two_le_q S i
    omega
  have hdU : S.dU i = deltaU (etaR s dv zeta) (S.q i) := hsched i
  -- Conclusion 2: the operative branch, in the frozen unevaluated symbols.
  have hbranch : Q0 (S.bout i) (S.dU i)
      = 8 * ((S.bout i : ℕ) : ℝ) / (deltaFixed * S.dU i) := by
    rw [hdU]
    exact scheduleQ0_first_branch hb hs hdv hz hq
  -- Conclusion 4: the width bound, weakened to the frozen depth floor.
  have hgrow := levelQ_growth S hsched hs hdv hz i hb
  have hweak : 47104000 * 512 * S.q i ≤ 47104000 * S.bout i * S.q i := by
    have : 47104000 * 512 ≤ 47104000 * S.bout i := Nat.mul_le_mul_left _ h512
    exact Nat.mul_le_mul_right _ this
  refine ⟨h512, hbranch, Q0_sixteen_branch_never_operative _ _,
    le_trans hweak hgrow, ?_, ?_⟩
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) hweak)
      (levelRowCarrier_growth S hsched hs hdv hz i hb)
  · exact le_trans hweak (levelColCarrier_growth S hsched hs hdv hz i hb)

/-- **The doubly exponential row bound at the paper's own instance.**

`levelRowCarrier_doubly_exponential` read at `paperSeedSpec`, where the wrapper
exponent is the evaluated `A_wrap L_P^2` of the frozen chain rather than a
binder: `A_wrap` through the banked `IterationAssembly.awrap` at
`ParameterSchedule.cSeed`, and `L_P` through `ParameterSchedule.LPwidth` at
`ParameterSchedule.P0sched`. -/
theorem paperSeedSpec_rowCarrier_doubly_exponential (n C0 B0 Ccert : ℕ) {s : ℕ}
    (lq2 clU0 zR : ℕ) {dv zeta : ℝ} (hn : 1 ≤ n) (hs : 3 < s) (hdv : 0 < dv)
    (hz : 0 < zeta) (mN nN : ℕ → ℕ) (hmN : ∀ i, 1 ≤ mN i) (hnN : ∀ i, 1 ≤ nN i)
    (i : ℕ) :
    2 ^ (2 ^ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).qExp i)
      ≤ (paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN).rowCarrier (i + 1) := by
  set S := paperSeedSpec n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN with hS
  have hsched : ScheduleTolerance S s dv zeta :=
    paperSeedSpec_scheduleTolerance n C0 B0 Ccert s lq2 clU0 zR dv zeta mN nN hmN hnN
  have hdepth : S.bout i = depthB n := rfl
  have hb : 1 ≤ S.bout i := by
    rw [hdepth]
    exact (seedAnchor_inside_frozen_range n hn).1
  exact levelRowCarrier_doubly_exponential S hsched hs hdv hz i hb

/-! ## Part 4: the statement poles -/

/-- **Vacuous-hypothesis pole: `ScheduleTolerance` is load-bearing.**

`10-direct-bridge.tex:38` demands only `0 < delta_U < 1` of the bridge's
tolerance.  That range alone does **not** give the width growth: at the legal
`b_out = 1`, `delta_U = 1/2` the threshold is the constant `Q_0 = 160`, and the
conclusion `47104000 * b_out * q <= Q_0` already fails at the smallest legal
inner width `q = 2` (`q >= 2` is `02-mechanical-contract.tex:771--775`).

`delta_U = 1/2` is **not** a paper value and no legality is claimed for it: this
is a rejection probe, exhibiting that a tolerance inside line 38's range but
outside `eq:q-deltaU`'s defining equation breaks the conclusion.  So the
schedule's defining equation, not the bridge's legality range, is what the
growth bound uses. -/
theorem widthGrowth_fails_at_free_tolerance :
    Q0 1 (1 / 2) = 160 ∧ ¬ ((47104000 : ℝ) * 1 * 2 ≤ Q0 1 (1 / 2)) := by
  have hQ : Q0 1 (1 / 2) = 160 := by
    rw [Q0_eq_route (le_refl 1) (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hQ, ?_⟩
  rw [hQ]
  norm_num

/-- **Trivial-witness pole / hypothesis-consistency probe, at the *evaluated*
schedule point.**

The full hypothesis bundle of Part 1 is exhibited satisfiable in the kernel
*together with its conclusions*, so no `False` derives from it and the dominant
branch statement is not vacuous.

**Nothing here is a chosen numeral.**  Both witnesses are quantities the frozen
`sec:parameters` DEFINES, and each is pinned by an equation to the value its own
defining chain returns, evaluated in dependency order:

* `s = sScale B_s (uAux (Apre b_out B_pub z_R clog_2(|E|+2)))` is `eq:s-choice`
  (`06:109--121`) evaluated, with `3 < s` read off the chain through
  `three_le_uAux` and `sScale_floor` rather than assumed;
* `q = qWrap A_wrap (LPwidth (P0sched C_cert s log_2 q_2 ceil(log_2 U_0) z_R))`
  is `eq:q-deltaU` line 515 evaluated at the defined exponent `L_P = clog_2 P_0`
  of `06:471`.

Because both witnesses are pinned by those equations, a "take something
convenient" pair -- `s = 64`, `q = 2`, say -- does **not** satisfy this
statement; that is exactly why the existential quantifies over pinned values
rather than merely asserting that some legal point exists.  The remaining inputs
stay universally quantified with the frozen legality of their fields:
`1 <= B_s` (`06:56`), `1 <= b_out` (`10:41`), `c_seed < A_wrap` (`06:1671`),
and `0 < delta_v(G)`, `0 < zeta` (`eq:eta-choice`). -/
theorem widthGrowth_hypotheses_consistent
    {bout Bpub zR clE Bs Ccert lq2 clU0 Awrap : ℕ} {dv zeta : ℝ}
    (hBs : 1 ≤ Bs) (hbout : 1 ≤ bout) (hAwrap : cSeed < Awrap)
    (hdv : 0 < dv) (hz : 0 < zeta) :
    ∃ s q : ℕ,
      s = sScale Bs (uAux (Apre bout Bpub zR clE)) ∧
      q = qWrap Awrap (LPwidth (P0sched Ccert s lq2 clU0 zR)) ∧
      3 < s ∧ 0 < q ∧ 101 ≤ Awrap ∧
      Q0 bout (deltaU (etaR s dv zeta) q)
          = 8 * (bout : ℝ) / (deltaFixed * deltaU (etaR s dv zeta) q) ∧
      (47104000 : ℝ) * (bout : ℝ) * (q : ℝ) ≤ Q0 bout (deltaU (etaR s dv zeta) q) ∧
      47104000 * bout * q ≤ Qwidth bout (deltaU (etaR s dv zeta) q) := by
  have hfloor := sScale_floor hBs (three_le_uAux bout Bpub zR clE)
  refine ⟨sScale Bs (uAux (Apre bout Bpub zR clE)), _, rfl, rfl, hfloor.1,
    qWrap_pos _ _, hundredOne_le_of_cSeed_lt hAwrap, ?_, ?_, ?_⟩
  · exact scheduleQ0_first_branch hbout hfloor.1 hdv hz (qWrap_pos _ _)
  · exact scheduleQ0_growth hbout hfloor.1 hdv hz (qWrap_pos _ _)
  · exact scheduleQwidth_growth hbout hfloor.1 hdv hz (qWrap_pos _ _)

end EthInapproximability.ParameterizedNP.DominantWidthBound
