import EthInapproximability.ParameterizedNP.SplitFirstBobInstance

/-!
# Parameterized NP route: the large-capacity branch of `eq:wrapper-first-bob-light`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`)
  together with `sections/A-certified-stopping.tex`
  (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`).
* **The exact frozen lines traced here**, in print order:
  * `09:1250--1259`, the two stopping rules, `d_v`, `kappa_v = 2^{r-d_v}`, `W_v`,
    and "Every first-Bob node has `kappa_v >= 2`".
  * `09:1268--1269`, "Put `vartheta = 9/16`.  We first close any first-Bob node
    satisfying `W_v >= vartheta kappa_v`." -- the **shared** heavy condition,
    printed *before* the capacity split and therefore common to both branches.
  * `09:1269--1276`, **this tranche's target**: "When `kappa_v >= t_ref`, follow
    the denser Bob child and invoke the certified-scale reference stopping lemma
    on `G` with `r' = kappa_v/t_ref`, `a^sharp = 1`.  The other parameters are
    those of `Cref{sec:wrapper-low-rungs}`.  This gives residual complexity at
    least `C + log_2 kappa_v - 1`."
  * `09:1277--1306`, the complementary small-capacity branch
    (`2 <= kappa_v < t_ref`), consumed here **only** as the other half of the
    dichotomy; its ladder call is banked and is not re-proved.
  * `09:1279--1281`, "at a fixed node there is at most one descendant of each
    initial outer coordinate.  Hence the number of represented coordinates is at
    least `ceil(W_v)`" -- a property of the **routing**, banked general as
    `SplitFirstBobInstance.ceil_frontierWeight_le_card_representedCoords`.
  * `09:1306--1313`, the join sentence "Its lower bound is one more bit than the
    remaining child budget in the alleged protocol", and the conclusion
    `eq:wrapper-first-bob-light`, `W_v < vartheta kappa_v`.
  * `A:109--146`, `thm:certified-localized-extension` (the certified-scale
    reference stopping lemma), whose antecedents are traced clause by clause:
    `A:111--112` (`M` nonempty, `H >= 2`, `0 < x <= 1`), `A:113--116`
    (`eq:certified-base`), `A:117--118` (`t >= t_cert`, a power of two divisible
    by `16`, `t x <= 1`), `A:119--124` (`p_t = 9t/16`, `h_t`), `A:125`
    (`r, r'` positive powers of two with `r' <= r`, and `q = rt`), `A:126--128`
    (the exact full product, `eps = 0`), `A:128--129` (`h in (0,1]`,
    `a^sharp in {0,1}`), `A:130--137` (`eq:certified-E1`, `eq:certified-E2`),
    `A:138--141` (the restriction clauses) and `A:142--145` (the conclusion
    `H + log_2(r't)`).
  * `A:104--107`, "the notation `t_0(3/5)` means the single integer
    `t_cert`" -- consumed as the banked `WrapperLowRungs` discipline.
* **Cross-anchors opened first-hand for this tranche:** `09:105` (`q = 2^r`),
  `09:327` (`q/4 >= t_ref`, the exponent gate `k + 2 <= r`), `09:311--331` (the
  `a^sharp = 0` substitution of `sec:wrapper-low-rungs`, whose "other
  parameters" `09:1275` imports), `09:434--441` (the **defining** display of
  `u_kappa`, which the large branch never mentions), and `06:558--572`
  (`eq:tref-search`, `t_ref = 2^{k_ref}`) in `sections/06-parameter-schedule.tex`
  (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`).

## Reader counterpart: NONE claimable, re-verified first-hand this round

`routes/parameterized-np/reader-facing/sections/` was searched again for
`certified-scale`, `stopping lemma`, `large-capacity`, `first Bob`, `sharp`,
`t_ref`, `vartheta` and `9/16`; every hit was opened.  The only near miss is
`02-preliminaries.tex:512--526`, `cor:paper-localized-extension` -- the
**uncertified** Localized Extension, with no `t >= t_cert`, no `h_t` and no
`eq:certified-E1`/`eq:certified-E2`, and with the density hypothesis inherited
from `thm:paper-extension` (`02-preliminaries.tex:485--510`) in the *stronger*
shape `2^{-b} <= x_seed <= 1` rather than the frozen `A:112` shape `0 < x <= 1`.
Citing it for a declaration whose whole content is the **certified** endpoint at
`a^sharp = 1` would be a false counterpart, and it is in any case already
declined for the same reason in the banked `WRAPPER-LOW-RUNGS-001` row, so it is
declined here too and no reader item is claimed.  The reader artifact contains
no statement of `eq:wrapper-first-bob-light`, no `vartheta`, no first-Bob
frontier weight and no capacity dichotomy at all.

## What this tranche closes in the predecessor module

`SPLIT-FIRST-BOB-INSTANCE-001` GAP-EXPOSED item **(14)**: "the large-capacity
branch of `09:1269--1276` is not entered -- only `kappa_v < t_ref` is assembled,
and no declaration composes the certified-scale reference stopping lemma at
`r' = kappa_v/t_ref`, `a^sharp = 1` into the `hclosure` binder at
`kappa_v >= t_ref`."

Entered here by `largeCapacityExtension` (§2) and composed into the frontier
apparatus by `canonical_firstBobLight_largeCapacity` (§4).

GAP-EXPOSED item **(17)**: the owed quantified replacement for the middle clause
of `SplitFirstBobInstance.split_cleanCount_tradeoff_is_forced`.  Landed in §5 as
`cleanCount_tradeoff_is_forced_quantified`, which **supersedes** that clause
rather than deleting it: the predecessor's declaration is untouched and still
proves what it proved, and the strengthened statement is a new declaration in
this module.

## The branch-wise-vs-cover-entry decision (`F4`), made from the frozen text

The banked `SplitFirstBobInstance.canonical_firstBobLight_of_closure` carries the
closure of `09:1269--1306` at its **cover-entry condition**
`u_{kappa_v} <= #represented`, which is what `09:1287--1296` consumes on the
*small* branch.  The `cc-t4h` verify seat withdrew the claim that the large
branch also delivers that form.  Reading `09:1269--1276` again first-hand
settles it:

* the large branch runs from the shared heavy condition `W_v >= vartheta kappa_v`
  (`09:1268--1269`) straight to the endpoint call, and **mentions neither
  represented coordinates nor `u_kappa`**;
* `u_kappa` is defined at `09:434--441` and used at `09:1283`, both inside the
  small-capacity paragraph; the *large* branch's block count is `r' p_t`
  (`A:138`), which at `r' = kappa_v/t_ref`, `t = t_ref` is `9 kappa_v/16` -- not
  `u_{kappa_v}`.

So the closure is stated **branch-wise** (`canonical_firstBobLight_branchwise`,
§4): heavy-conditioned on `k <= ell_v`, cover-entry-conditioned on `ell_v < k`.
The frozen boundary `kappa_v = t_ref` (`ell_v = k`) is assigned to the **large**
branch exactly as `09:1269` assigns it, and the two guards are exhaustive and
disjoint (`branch_dichotomy_exhaustive_and_disjoint`).  Nothing here re-asserts
the withdrawn cover-entry claim for the large branch.

## Exponent discipline (`t_ref` is never a numeral)

`t_ref = 2^{k_ref}` (`06:558--572`, `eq:tref-search`) and `eq:tref-search` forces
`k_ref >= 2^19`, so **no small numeral is a legal `k_ref`** and `k` is universally
quantified throughout, exactly as in the banked `WrapperLowRungs`.  Consequently:

* the branch condition `kappa_v >= t_ref` is the exponent inequality `k <= ell_v`
  with `ell_v = r - d_v` (`largeBranch_tRef_le_capacity` records the equivalence);
* `r' = kappa_v/t_ref` is `2^{ell_v - k}`, whose natural subtraction is honest
  exactly inside the branch (`largeBranchExponents`); the guard is threaded, never
  dropped;
* `A:125`'s `r = q/t_ref = 2^{r - k}` reuses the section-`09` width `q = 2^r`
  (`09:105`).

## Two name collisions, kept apart deliberately

* **`q`.**  Section `09`'s `q` is the scale-alignment width `2^r` (`09:105`);
  Appendix A's `q` is `r t`, the number of outer blocks (`A:125`).  At the
  frozen substitution `t = t_ref = 2^k` and `r = 2^{r-k}` these agree
  numerically (`2^{r-k} . 2^k = 2^r`), which is why `hE1` below reads
  `H + log_2 q = (C-1) + r`; they are still different symbols and no statement
  conflates them.
* **`9/16`.**  `vartheta = 9/16` (`09:1268`) is a *weight* threshold;
  `p_t = 9t/16` (`A:120`) is a *block count*.  Same fraction, different roles.

## Where `EXPANDER-001` would enter, and why it does not

`thm:certified-localized-extension` is proved in the frozen paper through the
balanced-family input, whose Lean surface is `LegacyNPCC.Stage12` / `NPCC.Stage2`
(the cited AGHP axiom) -- deliberately **outside** this module's import closure.
The endpoint therefore appears as the **named hypothesis** `hLocEx`, in the exact
implication shape `A:109--146` prints, and never as an axiom or an opaque
certificate.  `EXPANDER-001` has no Lean declaration by design and appears in no
hypothesis of this module.  The only import is `SplitFirstBobInstance`, whose
ledger row records the same exclusion.

## Canonical inhabitation

This module defines **no `structure` and no `inductive`**, so it opens no new
canonical-inhabitation obligation; the frontier apparatus it consumes is the
banked `FrontierIndexing.canonicalSystem`, whose parametric legality statement
remains `FrontierIndexing.canonicalSystem_legal_instance`.

The paper's own application point for the large branch is the full wrapper
argument at the schedule's parameters, inside the `(C+r-1)`-bit contradiction
frame of `09:1188--1313`; the paper instantiates it at no numeral, and the
frozen `k_ref >= 2^19` puts every legal instance far outside anything that can be
computed by `decide`.  `largeBranch_never_reaches_the_audit_instance` records
first-hand *why* no live instance of the large branch is exhibited: any legal
`k >= 4` with `k <= ell_v <= r` needs `r >= 4`, while the banked audit instances
run at `r = 2`.  The deferred canonical-inhabitation obligation for the large
branch is registered in this module's ledger row and is discharged only when the
schedule-level construction lands -- never by a probe.

## Proof status

Every declaration has exactly one of **three** shapes:

1. a **general** property of the frozen exponent arithmetic, of the banked
   `frontierWeight`/`representedCoords`/`capacity` readouts, or of the endpoint
   interface (§1, §2, §3, §4);
2. a **statement pole** -- a rejection probe at self-chosen numerals, claiming no
   legality, showing that a guard or a conclusion is not free (§6);
3. a **BEYOND-PAPER AUDIT** hypothesis-consistency check at self-chosen numerals
   substituted for source-DEFINED quantities, carrying that label in its own
   docstring (§6).

**No mathematics is added.**  `eq:wrapper-u-dense` is asserted nowhere,
`hDenseRung` is neither discharged nor fed, and
`sec:wrapper-mass-redistribution` (`09:1512--1781`) stays DEFERRED in full.

## What is *not* claimed

* The endpoint `thm:certified-localized-extension` is **not** proved; it is the
  named binder `hLocEx`.
* The `A:139--140` clause "at least `ceil(r' t x m)` rows in each represented
  block" is carried **inside** `hLocEx`'s restriction data and is **not**
  modelled here.  §3 supplies only the *count* of represented blocks; unlike the
  banked `WrapperLowRungs.wrapperLowExtension`, whose `selCard` came from a
  density-filtered count and therefore carried the rows with it, the count
  supplied here is a plain census of represented coordinates.  Recorded as a new
  GAP-EXPOSED item rather than glossed.
* `hselect`, the projection/selection step `09:1287--1296`, remains the banked
  small branch's named binder and is untouched.
* No route completion is claimed, and no conclusion of `eq:wrapper-u-dense`
  is asserted.
-/

namespace EthInapproximability.ParameterizedNP.LargeCapacityBranch

open Finset
open NPCC
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.WrapperLowRungs
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing
open EthInapproximability.ParameterizedNP.FirstBobFrontierInstance
open EthInapproximability.ParameterizedNP.SplitFirstBobInstance

/-! ## §1  The exponent arithmetic of `09:1269--1276`

`kappa_v >= t_ref` with `t_ref = 2^k` (`06:569`) and `kappa_v = 2^{ell_v}`
(`09:1255`) is the exponent inequality `k <= ell_v`; the frozen ratio
`r' = kappa_v/t_ref` is then `2^{ell_v - k}`, and its natural subtraction is
honest exactly inside the branch.  Everything in this section is **general** in
`k`, `ell`, `r` and `C`. -/

section Arithmetic

/-- **`09:1269`, the branch condition as an exponent inequality.**

`t_ref <= kappa_v` iff `k <= ell_v`, at `t_ref = 2^k` (`06:558--572`) and
`kappa_v = 2^{ell_v}` (`09:1255`).  Recorded as an equivalence so that no later
statement has to choose between the two readings; `k` is never pinned. -/
theorem largeBranch_tRef_le_capacity (k ℓ : ℕ) :
    (2 : ℕ) ^ k ≤ 2 ^ ℓ ↔ k ≤ ℓ :=
  Nat.pow_le_pow_iff_right (by norm_num)

/-- **`A:125` at the `09:1272` substitution (`r' = kappa_v/t_ref`).**

"Let `r, r'` be positive powers of two with `r' <= r`, and put `q = rt`."  At
`t = t_ref = 2^k`, `r = q/t_ref = 2^{r-k}` and `r' = kappa_v/t_ref = 2^{ell-k}`:

* `(ell - k) + k = ell`, so the natural subtraction does not truncate -- this is
  exactly the branch condition `k <= ell` doing its work;
* `r'` is positive and `r' <= r`, using `ell <= r` (`ell_v = r - d_v`);
* `r' t = kappa_v`, the identity `A:143`'s `log_2(r't)` needs.

General. -/
theorem largeBranchExponents {k ℓ r : ℕ} (hkl : k ≤ ℓ) (hℓr : ℓ ≤ r) :
    (ℓ - k) + k = ℓ
      ∧ 0 < (2 : ℕ) ^ (ℓ - k)
      ∧ (2 : ℕ) ^ (ℓ - k) ≤ 2 ^ (r - k)
      ∧ (2 : ℕ) ^ (ℓ - k) * 2 ^ k = 2 ^ ℓ := by
  refine ⟨by omega, pow_pos (by norm_num) _, Nat.pow_le_pow_right (by norm_num) (by omega), ?_⟩
  rw [← pow_add]
  congr 1
  omega

/-- **`A:138--139` at the `09:1272` substitution: exactly `r' p_t` blocks.**

`r' p_{t_ref} = (kappa_v/t_ref)(9 t_ref/16) = 9 kappa_v/16`, exactly and without
rounding, because `t_ref` is a power of two divisible by `16` (`A:117--118`, in
exponent form `4 <= k`).  The identity is the banked
`DenseAliceClosure.extensionSelectedBlocks` -- the *same* substitution arithmetic
for the *same* inherited endpoint -- consumed by pin at
`(rho', k_2) = (ell - k, k)`; only the closing exponent rewrite is new.

Note that `9 kappa_v/16` is the count `A:138` demands and is **not**
`u_{kappa_v}`: the large branch never mentions the small-copy cover width.
General. -/
theorem largeBranchBlocks {k ℓ : ℕ} (hk : 4 ≤ k) (hkl : k ≤ ℓ) :
    2 ^ (ℓ - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ ℓ / 16 := by
  have hexp : ℓ - k + k = ℓ := by omega
  have h := DenseAliceClosure.extensionSelectedBlocks (ρ' := ℓ - k) (k₂ := k) hk
  rw [h, hexp]

/-- **`A:142--144` read at `09:1276`: the endpoint's output is the frozen rung.**

`H + log_2(r' t) = (C-1) + ell_v`, which is `09:1276`'s "residual complexity at
least `C + log_2 kappa_v - 1`" verbatim.  The identity is on exponents, so
nothing is recovered by `Nat.log`, and the natural subtraction is exact under the
frozen `C >= 3` of `09:240`.  General. -/
theorem largeBranchOutput {C ℓ : ℕ} (hC : 3 ≤ C) :
    (C - 1) + ℓ = C + ℓ - 1 ∧ (C + ℓ - 1) + 1 = C + ℓ := by
  refine ⟨by omega, by omega⟩

/-- **`09:1272` read literally: `r' = kappa_v/t_ref` is a quotient, and the
exponent form is that quotient.**

The frozen display writes a **division**, `r' = kappa_v/t_ref`.  Every statement
in this module instead carries the exponent `2^{ell_v - k}`, so the two readings
must be shown to agree rather than assumed to: inside the branch `k <= ell_v` the
natural quotient `2^{ell_v}/2^k` **is** `2^{ell_v - k}`, exactly (no rounding),
and multiplying back by `t_ref` recovers `kappa_v`.

This is the round trip that licenses the exponent discipline, and it is why the
branch guard may never be dropped: outside the branch the quotient is `0` while
the exponent expression is `1`.  General. -/
theorem largeBranchRatio_eq_quotient {k ℓ : ℕ} (hkl : k ≤ ℓ) :
    (2 : ℕ) ^ ℓ / 2 ^ k = 2 ^ (ℓ - k) ∧ ((2 : ℕ) ^ ℓ / 2 ^ k) * 2 ^ k = 2 ^ ℓ := by
  have hdiv : (2 : ℕ) ^ ℓ / 2 ^ k = 2 ^ (ℓ - k) := Nat.pow_div hkl (by norm_num)
  refine ⟨hdiv, ?_⟩
  rw [hdiv, ← pow_add]
  congr 1
  omega

/-- **Monotonicity of the frozen ratio `r' = kappa_v/t_ref` in the capacity.**

A deeper node has smaller capacity and hence a smaller `r'`; at the branch
boundary `ell = k` the ratio is `1`, the smallest positive power of two `A:125`
permits.  General. -/
theorem largeBranchRatio_mono {k ℓ ℓ' : ℕ} (hkl : k ≤ ℓ) (hℓ : ℓ ≤ ℓ') :
    (2 : ℕ) ^ (ℓ - k) ≤ 2 ^ (ℓ' - k) ∧ (2 : ℕ) ^ (k - k) = 1 := by
  refine ⟨Nat.pow_le_pow_right (by norm_num) (by omega), by simp⟩

end Arithmetic

/-! ## §2  The endpoint call of `09:1269--1276`, at `a^sharp = 1`

"When `kappa_v >= t_ref`, follow the denser Bob child and invoke the
certified-scale reference stopping lemma on `G` with `r' = kappa_v/t_ref`,
`a^sharp = 1`.  The other parameters are those of `Cref{sec:wrapper-low-rungs}`.
This gives residual complexity at least `C + log_2 kappa_v - 1`."

The banked `WrapperLowRungs.wrapperLowExtension` is the *same* endpoint at the
`09:311--331` substitution, whose parameters `09:1275` imports wholesale:
`M = G`, `H = C-1`, `x = x_T`, `t = t_ref = 2^k`, `r = q/t_ref = 2^{r-k}`,
`eps = 0`, `h = theta`, `y_* = 3/5`.  Exactly **two** things change here, and
both are read off `09:1272--1273`:

* `r'` becomes `kappa_v/t_ref = 2^{ell_v - k}` -- the low-rung block used
  `r' = kappa_j/t_ref` at `j <= 2` only, whereas `ell_v` ranges over the whole
  branch `k <= ell_v <= r`;
* `a^sharp` becomes `1`, so `A:141`'s column-density floor is `h 2^{-1}`, which
  is precisely the one-bit allowance for "follow the denser Bob child". -/

section Endpoint

/-- **`09:1269--1276`: the certified-scale reference stopping lemma applied at
`r' = kappa_v/t_ref`, `a^sharp = 1`.**

`thm:certified-localized-extension` (`A:109--146`) is the named binder `hLocEx`,
in the exact implication shape the frozen theorem has, with its antecedents
listed **in the order `A:109--146` prints them**.

Discharged here, from this block's own data:

* `H >= 2`, i.e. `2 <= C - 1`, from the frozen `C >= 3` of `09:240`;
* the guard `t x <= 1` (`A:118`), from `eq:wrapper-low-simple-gate` through the
  banked `simple_gate_forces_tRef_row_legality` -- note this is `t_ref x_T <= 1`
  and **not** `kappa_v x_T <= 1`, which on this branch may well fail
  (`largeBranch_needs_only_tRef_legality`);
* `r'` legality (`A:125`): positivity, `r' <= r` and `r' t = kappa_v`, from
  `largeBranchExponents` under the branch condition `k <= ell` and `ell <= r`;
* the represented-block identity `r' p_t = 9 kappa_v/16` (`A:138--139`,
  `largeBranchBlocks`);
* `eps = 0` (`A:126--128`, the exact full product) and `a^sharp = 1`
  (`A:128--129`, fixed by `09:1273`), passed as the literal forms the endpoint's
  branch selection needs;
* the output arithmetic `H + log_2(r't) = C + log_2 kappa_v - 1`
  (`largeBranchOutput`).

Left as named hypotheses, because they belong to `06` and not to this block:
`htcert` (`t_ref >= t_cert`, `A:117`), `hE1` and `hE2` (`eq:certified-E1`,
`eq:certified-E2`), all three discharged by `eq:tref-search` per `06:574--578`;
`hbase` (`eq:certified-base`, which **is** the second clause of the banked
`lem:wrapper-reference`); `hcol`, the projected column density at the denser Bob
child; `hcount`, the availability of `9 kappa_v/16` represented outer blocks; and
the carrier and parameter guards.

`hE1` is stated in its `t`-th-power form, as in the banked low-rung call: at
`eps = 0` the frozen `(h 2^{-(H+log_2 q)})^{1/t} >= y_*` is equivalent, for
nonnegative arguments, to `h 2^{-(H+log_2 q)} >= y_*^t`.  Its exponent is
`H + log_2 q = (C-1) + r` because Appendix A's `q = r t = 2^{r-k} . 2^k = 2^r`
is section `09`'s width `q = 2^r` (`09:105`) -- the two `q`'s are different
symbols that coincide at this substitution, and neither statement conflates them.

**Not modelled, recorded:** `A:139--140`, "at least `ceil(r' t x m)` rows in each
represented block", lives inside `hLocEx`'s restriction data.  `selCard` is a
bare count here, so nothing in this statement forces the counted blocks to carry
the row floor.

General in the member type, in its cost, in `C`, `r`, `k`, `ell`, and in the real
parameters `x_T`, `theta`, `colDens`. -/
theorem largeCapacityExtension {Mem : Type*} (memCost : Mem → ℕ) (mem : Mem)
    {C r k ℓ tcert selCard : ℕ} {xT θ colDens : ℝ}
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Gmat : Rw → Cl → Bool)
    (hk : 4 ≤ k) (hkl : k ≤ ℓ) (hℓr : ℓ ≤ r) (hq4 : k + 2 ≤ r) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    -- `A:138--139`, enough represented outer blocks: `9 kappa_v/16`
    (hcount : 9 * (((2 : ℕ) ^ ℓ : ℕ) : ℝ) / 16 ≤ (selCard : ℝ))
    -- `eq:certified-base` (`A:113--116`), the banked `lem:wrapper-reference`
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    -- `A:117`, the certified width floor; `eq:tref-search` (`06:558--572`)
    (htcert : tcert ≤ 2 ^ k)
    -- `eq:certified-E1` (`A:130--134`) at `eps = 0`, in `t`-th-power form
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    -- `eq:certified-E2` (`A:135--136`) at `eps = 0`, at the frozen `h_t`
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    -- `A:141` at `a^sharp = 1` (`09:1273`): the denser Bob child's column density
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hLocEx :
      -- `A:111`, `M` a nonempty Boolean matrix, and `H >= 2`
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      -- `A:112`, `0 < x <= 1` -- **strict** on the left, as the frozen theorem prints
      0 < xT → xT ≤ 1 →
      -- `A:113--116`, `eq:certified-base`
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      -- `A:117--118`, `t >= t_cert`, a power of two divisible by `16`, `t x <= 1`
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      -- `A:125`, `r, r'` positive powers of two with `r' <= r`, and `r' t = kappa_v`
      0 < (2 : ℕ) ^ (ℓ - k) →
      (2 : ℕ) ^ (ℓ - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ (ℓ - k) * 2 ^ k = 2 ^ ℓ →
      -- `A:126--128`, the exact full product: `eps = 0`
      (0 : ℝ) = 0 →
      -- `A:128--129`, `h in (0,1]` and `a^sharp = 1`
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      -- `eq:certified-E1`, `eq:certified-E2`
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      -- `A:138--139`, exactly `r' p_t` represented outer blocks, and enough of them
      2 ^ (ℓ - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ ℓ / 16 →
      9 * (((2 : ℕ) ^ ℓ : ℕ) : ℝ) / 16 ≤ (selCard : ℝ) →
      -- `A:142--144`, the conclusion `H + log_2(r' t)`
      (C - 1) + ℓ ≤ memCost mem) :
    C + ℓ ≤ 1 + memCost mem := by
  have hguard : ((2 : ℝ) ^ k) * xT ≤ 1 :=
    simple_gate_forces_tRef_row_legality hq4 (le_of_lt hxT0) hgate
  obtain ⟨-, hpos, hle, hmul⟩ := largeBranchExponents hkl hℓr
  have hblocks : 2 ^ (ℓ - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ ℓ / 16 := largeBranchBlocks hk hkl
  have hout := hLocEx hGne (by omega) hxT0 hxT1 hbase htcert hk hguard hpos hle hmul
    rfl hθ0 hθ1 hcol hE1 hE2 hblocks hcount
  omega

end Endpoint

/-! ## §3  The block count at a heavy first-Bob node (`09:1268--1269`, `09:1280--1281`)

`A:138` demands `r' p_t = 9 kappa_v/16` represented outer blocks.  The heavy
condition of `09:1268--1269` -- which is printed **before** the capacity split and
so belongs to both branches -- supplies exactly that count, through the routing
facts of `09:1278--1281`.  Nothing from the small-capacity paragraph is used:
`u_kappa` does not appear. -/

section BlockCount

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`09:1268--1269` with `09:1280--1281`: a heavy node represents `9 kappa_v/16`
outer coordinates.**

"We first close any first-Bob node satisfying `W_v >= vartheta kappa_v`" together
with "the number of represented coordinates is at least `ceil(W_v)`" gives
`#represented >= ceil(W_v) >= W_v >= 9 kappa_v/16`, which is the block count
`A:138` requires at `r' = kappa_v/t_ref`, `t = t_ref`.

The middle step is the banked, already-proved
`ceil_frontierWeight_le_card_representedCoords`, whose own inputs
(`09:1277--1280`: every certificate weighs at most `1`, and at most one
descendant of each initial coordinate reaches a fixed node) are routing
properties carrying no capacity hypothesis.  General in `P`, `Coord`, `R`, `A_0`,
`r` and the node; the first-Bob flag is not even needed, and is therefore not
assumed. -/
theorem heavy_blockCount_le_card_representedCoords (P : Protocol X Y Z)
    (R : Coord → Finset X) (A0 r : ℕ) (v : FrontierNode P R A0 r) {κ : ℝ}
    (hheavy : vartheta * κ ≤ frontierWeight P R A0 r v) :
    9 * κ / 16 ≤ ((representedCoords P R A0 r v).card : ℝ) := by
  have hceil : (⌈frontierWeight P R A0 r v⌉₊ : ℝ)
      ≤ ((representedCoords P R A0 r v).card : ℝ) := by
    exact_mod_cast ceil_frontierWeight_le_card_representedCoords P R A0 r v
  have hW : frontierWeight P R A0 r v ≤ (⌈frontierWeight P R A0 r v⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hv : vartheta * κ = 9 * κ / 16 := by rw [vartheta_val]; ring
  linarith [hheavy, hW, hceil, hv.symm.le, hv.le]

end BlockCount

/-! ## §4  The frozen dichotomy, joined (`09:1268--1313`)

`09:1268--1269` closes every heavy first-Bob node; `09:1269--1276` and
`09:1277--1306` are the two capacity branches of that single closure, and
`09:1306--1313` joins them into `eq:wrapper-first-bob-light`.  This section
states the closure **branch-wise**, which is the shape the frozen text has, and
then discharges the large branch against §2 and §3. -/

section Dichotomy

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] {Coord : Type} [Fintype Coord]

/-- **`eq:wrapper-first-bob-light` (`09:1309--1313`) with the closure stated
branch-wise -- the `F4`/GAP-14 decision.**

At a first-Bob node of `FrontierIndexing.canonicalSystem` the frozen conclusion
`W_v < vartheta kappa_v` follows from the budget of `09:1306--1308` and the two
frozen branches of the closure, each carried at **its own** entry condition:

* `hlarge` is `09:1269--1276`, at the branch condition `t_ref <= kappa_v`
  (exponent form `k <= ell_v`) and the **heavy** condition `W_v >= vartheta
  kappa_v` of `09:1268--1269`.  The frozen large branch mentions neither
  represented coordinates nor `u_kappa`, so it is *not* asked for the cover-entry
  form; that over-claim was withdrawn at the `cc-t4h` verify seat and is not
  revived here.
* `hsmall` is `09:1277--1306`, at the branch condition `kappa_v < t_ref`
  (exponent form `ell_v < k`) and the **cover-entry** condition
  `u_{kappa_v} <= #represented` of `09:1287--1289`, which is what that branch
  consumes.  Its antecedent is produced from the heavy condition by the banked,
  already-proved `heavy_firstBob_smallCopyWidth_le` (`09:1283`), so the small
  side still starts at the routing rather than at an assumed weight bound.

The two guards `k <= ell_v` and `ell_v < k` are exhaustive and disjoint, and the
boundary `kappa_v = t_ref` goes to the **large** branch, exactly as `09:1269`
assigns it (`branch_dichotomy_exhaustive_and_disjoint`).  This is strictly
stronger than the banked `canonical_firstBobLight_of_closure`, whose single
binder demanded the cover-entry form on **both** branches: any instance of that
theorem's binder yields both binders here.

General in `P`, `Coord`, `R`, `A_0`, `r`, `C`, `k` and the residual budget. -/
theorem canonical_firstBobLight_branchwise {P : Protocol X Y Z} {R : Coord → Finset X}
    {A0 r : ℕ} (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B k : ℕ}
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hlarge : k ≤ r - v.val.length →
      vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ)
        ≤ frontierWeight P R A0 r v →
      C + (r - v.val.length) - 1 ≤ B)
    (hsmall : r - v.val.length < k →
      smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
        ≤ (representedCoords P R A0 r v).card →
      C + (r - v.val.length) - 1 ≤ B) :
    frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  have hlt : v.val.length < r := ((canonicalSystem hcomp hR).firstBob_spec v hv).2.2
  have hcap : (canonicalSystem hcomp hR).toWrapperFrontier.capacity v
      = 2 ^ (r - v.val.length) := rfl
  have hcast : (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) = (2 : ℝ) ^ (r - v.val.length) := by
    push_cast; ring
  rw [hcap, hcast]
  refine wrapperFirstBobLight (C := C) (r := r) (d := v.val.length)
    (ℓ := r - v.val.length) (B := B) hC (by omega) (by omega) hbudget ?_
  intro hheavy
  have hheavy' : vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ)
      ≤ frontierWeight P R A0 r v := by rw [hcap, hcast]; exact hheavy
  rcases Nat.lt_or_ge (r - v.val.length) k with hbranch | hbranch
  · exact hsmall hbranch (heavy_firstBob_smallCopyWidth_le hcomp hR hv hheavy')
  · exact hlarge hbranch hheavy'

/-- **The large-capacity branch of `09:1269--1276`, composed into the frontier
apparatus -- GAP-14 discharged.**

At a first-Bob node with `kappa_v >= t_ref` -- exponent form `k <= ell_v` with
`t_ref = 2^k` (`06:569`) -- the `hlarge` binder of the preceding statement is
discharged against §2's endpoint call and §3's block count:

* `heavy_blockCount_le_card_representedCoords` turns the heavy condition into the
  `A:138` count `9 kappa_v/16 <= #represented`, using only `09:1268--1269` and
  the routing facts `09:1278--1281`;
* `largeCapacityExtension` is then the frozen call at `r' = kappa_v/t_ref`,
  `a^sharp = 1`, whose output `C + log_2 kappa_v - 1 <= B` is exactly what
  `09:1276` states for the selected Bob child.

The remaining binders are the ones §2 leaves named -- `hLocEx` (the endpoint
itself, where `EXPANDER-001` would enter and therefore stays a **named
hypothesis**), `hbase`, `htcert`, `hE1`, `hE2`, `hcol` -- together with the
small-capacity branch `hsmall`, which is untouched here and remains the banked
`canonical_firstBobLight_smallCapacity`'s business.

**Recorded, not glossed:** the represented blocks counted by §3 are not shown to
carry `A:139--140`'s per-block row floor; that clause lives inside `hLocEx`'s
restriction data.

General in the source carriers, in `C`, `r`, `k`, the residual budget and the
real parameters `x_T`, `theta`, `colDens`. -/
theorem canonical_firstBobLight_largeCapacity {Rw Cl : Type*} [Fintype Rw] [Fintype Cl]
    (Gmat : Rw → Cl → Bool) {P : Protocol X Y Z} {R : Coord → Finset X} {A0 r : ℕ}
    (hcomp : CompletedNoBob P r) (hR : ∀ i, refRowFloor A0 r ≤ (R i).card)
    {v : FrontierNode P R A0 r} {C B k tcert : ℕ} {xT θ colDens : ℝ}
    (hv : (canonicalSystem hcomp hR).firstBob v = true) (hC : 3 ≤ C)
    (hk : 4 ≤ k) (hq4 : k + 2 ≤ r)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hGne : 1 ≤ Fintype.card Rw)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hcol : θ / 2 ^ (1 : ℕ) ≤ colDens)
    (hbudget : B + (v.val.length + 1) ≤ C + r - 1)
    (hLocEx :
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      0 < xT → xT ≤ 1 →
      C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5) →
      tcert ≤ 2 ^ k →
      4 ≤ k →
      ((2 : ℝ) ^ k) * xT ≤ 1 →
      0 < (2 : ℕ) ^ ((r - v.val.length) - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) ≤ 2 ^ (r - k) →
      (2 : ℕ) ^ ((r - v.val.length) - k) * 2 ^ k = 2 ^ (r - v.val.length) →
      (0 : ℝ) = 0 →
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ colDens →
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      2 ^ ((r - v.val.length) - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ (r - v.val.length) / 16 →
      9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
        ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) →
      (C - 1) + (r - v.val.length) ≤ B)
    (hsmall : r - v.val.length < k →
      smallCopyWidth ((canonicalSystem hcomp hR).toWrapperFrontier.capacity v)
        ≤ (representedCoords P R A0 r v).card →
      C + (r - v.val.length) - 1 ≤ B) :
    frontierWeight P R A0 r v
      < vartheta * (((canonicalSystem hcomp hR).toWrapperFrontier.capacity v : ℕ) : ℝ) := by
  refine canonical_firstBobLight_branchwise hcomp hR hv hC hbudget ?_ hsmall
  intro hbranch hheavy
  have hcap : (canonicalSystem hcomp hR).toWrapperFrontier.capacity v
      = 2 ^ (r - v.val.length) := rfl
  have hcount : 9 * (((2 : ℕ) ^ (r - v.val.length) : ℕ) : ℝ) / 16
      ≤ (((representedCoords P R A0 r v).card : ℕ) : ℝ) := by
    refine heavy_blockCount_le_card_representedCoords P R A0 r v ?_
    rw [← hcap]
    exact hheavy
  have hend : C + (r - v.val.length) ≤ 1 + B :=
    largeCapacityExtension (Mem := ℕ) (fun n => n) B Gmat hk hbranch
      (Nat.sub_le _ _) hq4 hC hxT0 hxT1 hθ0 hθ1 hGne hgate hcount hbase htcert hE1 hE2 hcol
      hLocEx
  omega

/-- **Hypothesis consistency for `canonical_firstBobLight_branchwise` at the
banked split instance.**

The branch-wise theorem's full binder bundle -- the two frozen construction
inputs, the first-Bob flag, `C >= 3`, the remaining child budget of
`09:1306--1308`, and **both** branches of the closure -- is jointly satisfiable,
and the conclusion follows rather than `False`, at the banked live split instance
with the frozen minimum `C = 3` and residual budget `B = 0`.

Both branch binders hold because their antecedents fail, and each fails for a
*different* frozen reason, which is the honest reading:

* `hlarge`'s guard `k <= ell_v` fails: at `r = 2` the exposed first-Bob node has
  `ell_v = 1`, while any legal `k` satisfies `4 <= k` (`A:117--118`).  Taking
  `k = 4` -- the smallest exponent the divisibility clause permits, and still far
  below the true `k_ref` -- the guard reads `4 <= 1`.  This is
  `largeBranch_never_reaches_the_audit_instance` at the instance.
* `hsmall`'s cover-entry condition fails: the node is light, one coordinate is
  represented, and `u_2 = 2 > 1`, which is the banked
  `firstBobLight_closure_antecedent_is_not_automatic`.

**BEYOND-PAPER AUDIT.**  The instance's `r = 2`, `A_0 = 1` and row placement are
the banked audit assignments, and `k = 4` is ours; none of them is claimed legal.
It audits *our* branch-wise encoding at a point the paper never visits. -/
theorem branchwise_fires_at_split_instance :
    frontierWeight liveProtocol splitRows 1 2 splitBobNode
      < vartheta * ((splitSystem.toWrapperFrontier.capacity splitBobNode : ℕ) : ℝ) :=
  canonical_firstBobLight_branchwise live_hcomp split_hR (C := 3) (B := 0) (k := 4)
    (by decide) (by norm_num) (by decide)
    (fun h => absurd h (by decide))
    (fun _ hcov => absurd hcov (by decide))

end Dichotomy

/-! ## §5  GAP-EXPOSED item 17: the quantified coordinate-count clause

`SplitFirstBobInstance.split_cleanCount_tradeoff_is_forced`'s middle clause is
the instance-local arithmetic `(4 : R) - 2 < 3`, weaker than the quantified step
its own docstring argues.  The owed replacement is landed here; the predecessor
declaration is **untouched** and still proves what it proved, so this supersedes
rather than deletes. -/

section CleanCountGap

/-- **`eq:wrapper-clean-count` (`09:1352--1357`): the trade-off at `q = 4`,
quantified -- GAP-EXPOSED 17 discharged.**

The first conjunct of `eq:wrapper-clean-count`, `c >= q - e_0/(1-vartheta)`, is
informative only when its right-hand side is positive, which at `q = 4` (i.e.
`r = 2`, `09:105`) means `e_0 < 7/4`.  The **quantified** consequence -- the one
the predecessor's docstring argued but did not formalize -- is that at any such
`e_0` the audit instance's coordinate count `card Coord = 2` falls strictly short
of the demand `q - e_0 = 4 - e_0`, for **every** real `e_0` below the threshold
and not merely at the instance's own `e_0 = 2`.

Clause 1 is the threshold, unchanged from the predecessor and proved for every
real `e_0`; clause 2 is the owed quantified replacement; clause 3 records the
audit instance's coordinate count.  Together they say: at `r = 2` one may have
the first conjunct live or the half-weight column nonempty, never both.

The predecessor's `split_cleanCount_tradeoff_is_forced` is **not** modified, and
nothing else in either module consumes either pole. -/
theorem cleanCount_tradeoff_is_forced_quantified :
    (∀ e0 : ℝ, 0 < 4 - e0 / (1 - vartheta) → e0 < 7 / 4)
      ∧ (∀ e0 : ℝ, e0 < 7 / 4 → ((Fintype.card (Fin 2) : ℕ) : ℝ) < 4 - e0)
      ∧ Fintype.card (Fin 2) = 2 := by
  refine ⟨fun e0 h => ?_, fun e0 h => ?_, by norm_num⟩
  · rw [one_sub_vartheta] at h
    linarith
  · have hcard : ((Fintype.card (Fin 2) : ℕ) : ℝ) = 2 := by norm_num
    rw [hcard]
    linarith

end CleanCountGap

/-! ## §6  Statement poles and hypothesis consistency

A green build sees none of this. -/

section Poles

/-- **Statement pole: the frozen split is exhaustive and disjoint, with the
boundary going to the large branch.**

`09:1269` reads "When `kappa_v >= t_ref`" and `09:1276--1277` reads "When
`2 <= kappa_v < t_ref`" (the word "When" is the last token of `09:1276`, and the
inequality is `09:1277`), so the boundary `kappa_v = t_ref` belongs to the
*large* branch.  In exponent form that is `k <= ell_v` versus `ell_v < k`: every
node falls in exactly one branch, and no node falls in both.  This is what makes
`canonical_firstBobLight_branchwise` a faithful transcription of the frozen
dichotomy rather than a case analysis of our own choosing.

Contrast the banked `canonical_firstBobLight_smallCapacity`, whose `hsmall` is
the **non-strict** `ell_v <= k` -- a deliberate, recorded widening that admits
the boundary into the small branch as well.  The two are compatible (a widened
hypothesis only enlarges a burden), but only the strict form is the frozen
split. -/
theorem branch_dichotomy_exhaustive_and_disjoint (k ℓ : ℕ) :
    (k ≤ ℓ ∨ ℓ < k) ∧ ¬ (k ≤ ℓ ∧ ℓ < k) := by
  refine ⟨by omega, by omega⟩

/-- **Statement pole: the large branch needs only `t_ref x_T <= 1`, and the small
branch's legality genuinely fails there.**

`09:1304` verifies the small branch's legality by the chain
`kappa_v x_T <= t_ref x_T <= 1`, which needs `ell_v <= k`.  On the large branch
`ell_v >= k`, and the left-hand inequality is no longer available: the endpoint's
own guard is `A:118`'s `t x <= 1`, i.e. `t_ref x_T <= 1`, and that is all
`largeCapacityExtension` uses.

The probe below exhibits the separation at `k = 4`, `ell = 5`, `x_T = 1/16`:
`t_ref x_T = 1` holds while `kappa_v x_T = 2 > 1` fails.  **These numerals are
ours** and claim **no legality** -- no legal `k_ref` is as small as `4`
(`eq:tref-search` forces `k_ref >= 2^19`) and `x_T = 2^{-b_T}` is fixed by
`06:238--244` (the display of `x_T` itself is `06:243`).  This is a rejection
probe showing that the small branch's guard
would fire on large-branch input, not a claim about the schedule. -/
theorem largeBranch_needs_only_tRef_legality :
    ((2 : ℝ) ^ (4 : ℕ)) * (1 / 16) ≤ 1 ∧ ¬ (((2 : ℝ) ^ (5 : ℕ)) * (1 / 16) ≤ 1) := by
  refine ⟨by norm_num, by norm_num⟩

/-- **Statement pole: `a^sharp = 1` is strictly the denser-child allowance.**

`A:141` asks for column density at least `h 2^{-a^sharp}`.  The banked low-rung
call of `09:322` fixes `a^sharp = 0` and therefore demands the full `h`; the
large branch of `09:1273` fixes `a^sharp = 1` and demands `h/2`, which is exactly
the one-bit loss of "follow the denser Bob child" (`09:1270`).  The two demands
are genuinely different -- the `a^sharp = 1` form is strictly weaker at every
positive `h` -- so substituting one for the other would silently change which
statement is being invoked.  General in `h`. -/
theorem aSharp_one_is_the_denser_child_allowance {h : ℝ} (hh : 0 < h) :
    h / 2 ^ (1 : ℕ) = h / 2 ∧ h / 2 ^ (1 : ℕ) < h / 2 ^ (0 : ℕ) := by
  refine ⟨by norm_num, by norm_num; linarith⟩

/-- **Statement pole: the endpoint carries the bound; the conclusion is not free.**

Were `largeCapacityExtension`'s conclusion derivable from its arithmetic data
alone, `hLocEx` would be decoration.  It is not: at the frozen minimum `C = 3`
with `ell = 4` the conclusion `C + ell <= 1 + memCost` fails outright at a child
of cost `0`, and even at `memCost = 6` -- one bit short -- it still fails.  So the
`(C-1) + ell <= memCost` output of the endpoint is what supplies the bound.

`3 + 4 = 7 > 1 + 0` and `7 > 1 + 5`, while `7 <= 1 + 6` is the exact threshold
`(C-1) + ell = 6`. -/
theorem largeCapacityExtension_conclusion_is_not_free :
    ¬ ((3 : ℕ) + 4 ≤ 1 + 0) ∧ ¬ ((3 : ℕ) + 4 ≤ 1 + 5) ∧ (3 : ℕ) + 4 ≤ 1 + 6 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Statement pole: the large branch cannot reach the banked audit instances,
and why no live instance is exhibited.**

The banked live and split instances of `FirstBobFrontierInstance` and
`SplitFirstBobInstance` run at `r = 2`, where every first-Bob node has
`ell_v = r - d_v <= 2`.  The branch condition `k <= ell_v` together with the
frozen `A:117--118` divisibility `4 <= k` would force `4 <= ell_v <= r`, hence
`r >= 4`; and the real `eq:tref-search` bound `k_ref >= 2^19` puts the true
threshold astronomically higher.  So the large branch is **unreachable** at any
small instance that `decide` could settle, which is precisely why this module
exhibits no live instance of it and why the canonical-inhabitation obligation for
`09:1269--1276` is ledger-registered and deferred rather than probed.

Recorded as arithmetic: `4 <= k` and `k <= ell` and `ell <= 2` are jointly
contradictory. -/
theorem largeBranch_never_reaches_the_audit_instance (k ℓ : ℕ)
    (hk : 4 ≤ k) (hkl : k ≤ ℓ) : ¬ (ℓ ≤ 2) := by
  omega

/-- **Hypothesis consistency for `largeCapacityExtension`: the arithmetic and
gate binders are jointly satisfiable, and the endpoint's output genuinely
contradicts the remaining budget.**

**BEYOND-PAPER AUDIT.**  `r` is DEFINED by `06:515` (`q = 2^{A_wrap L_P^2}`) with
`09:105` (`q = 2^r`), `k` is DEFINED as `k_ref` by `06:558--569`
(`t_ref = 2^{k_ref}`, the least integer meeting `eq:tref-search`), and `C` is
DEFINED by the wrapper schedule.  The numerals `k = 4`, `ell = 4`, `r = 6`,
`C = 3`, `d_v = 2`, `B = 5` are **ours**: they audit *our encoding* of the gate
interaction at a point the paper never visits, and are strictly weaker evidence
than the paper's own application point.  Nothing here claims those numerals are
legal values of the schedule -- indeed `k = 4` is not, by `eq:tref-search`.

**Coverage, stated precisely.**  What is checked, clause by clause, is the
**arithmetic and gate** bundle of `largeCapacityExtension` together with the two
extra arithmetic binders `canonical_firstBobLight_largeCapacity` adds:
clause 1 is `hk` (`4 <= k`), clause 2 is `hkl` (`k <= ell_v`, which at `r = 6`,
`d_v = 2` is also that theorem's branch guard `k <= r - d_v`), clause 3 is `hℓr`
(`ell_v <= r`), clause 4 is `hq4` (`k + 2 <= r`, the `09:327` gate), clause 5 is
`hC` (`3 <= C`), clauses 6--9 are `hxT0`, `hxT1`, `hgate` and the banked gate
predicate, and clause 10 is `hbudget` (`B + (d_v + 1) <= C + r - 1`).  The real
parameter is `x_T = 1/(2^6 . 65536)`, the banked closed-form accessor
`WrapperLowRungs.wrapperLowRungGates_legal_instance` at `(k, r) = (4, 6)`,
consumed as an accessor and never as a numeral.  The **analytic** binders
`hbase`, `hE1`, `hE2`, `hcol`, `hGne` and the endpoint `hLocEx` are **not**
instantiated here: as the banked `wrapperLowExtension_fires_at_legal_tier` records
first-hand, `hE1` and `hE2` are in fact *unsatisfiable* at small `k`, which is
exactly why `eq:tref-search` forces `k_ref >= 2^19` and why `k` is quantified.
So full-bundle satisfiability is **not** exhibited and is not claimed.

The last clause is the join of `09:1306--1308`: the endpoint's output
`C + ell_v - 1 = 6` exceeds the residual budget `B = 5` by exactly one bit, while
the budget relation `B + (d_v + 1) <= C + r - 1` holds -- so the frozen
contradiction fires rather than the bundle being vacuously consistent. -/
theorem largeCapacity_arithmetic_binders_consistent :
    (4 : ℕ) ≤ 4 ∧ (4 : ℕ) ≤ 4 ∧ (4 : ℕ) ≤ 6 ∧ (4 : ℕ) + 2 ≤ 6 ∧ (3 : ℕ) ≤ 3
      ∧ (0 : ℝ) < 1 / ((2 : ℝ) ^ 6 * 65536)
      ∧ (1 : ℝ) / ((2 : ℝ) ^ 6 * 65536) ≤ 1
      ∧ ((2 : ℝ) ^ (6 : ℕ)) * (1 / ((2 : ℝ) ^ 6 * 65536)) ≤ 4 / 25025
      ∧ wrapperLowRungGates 6 (1 / ((2 : ℝ) ^ 6 * 65536))
      ∧ (5 : ℕ) + (2 + 1) ≤ 3 + 6 - 1
      ∧ ¬ ((3 : ℕ) + 4 - 1 ≤ 5) := by
  obtain ⟨hgates, hpos, hval⟩ := wrapperLowRungGates_legal_instance 4 6 (by norm_num)
    (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, hpos, ?_, ?_,
    hgates, by norm_num, by norm_num⟩
  · rw [div_le_one (by positivity)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 6]
  · rw [hval]; norm_num

end Poles

end EthInapproximability.ParameterizedNP.LargeCapacityBranch
