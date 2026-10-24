import EthInapproximability.ParameterizedNP.FirstWrapperAssembly

/-!
# Parameterized NP route: the `A:138--141` restriction datum

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/A-certified-stopping.tex`
  (SHA-256 `7F2ECC8EAAB2AAFD0BB2EFDF4E793330AAE2D864552C5FAC0AB91FCBB61EFC71`),
  together with `sections/06-parameter-schedule.tex`
  (SHA-256 `46A9AA59695357E5E2A42FA08537939A70F0D8421EB9CF1365AB42F8125B5FB9`),
  `sections/03-preliminaries.tex`
  (SHA-256 `5A321B8B3577BC9AFB5E2C172C7FA375D046D50A81D490BBB1293F01FE34F99F`)
  and `sections/09-first-wrapper.tex`
  (SHA-256 `8A54AAA6F0E60EAEB31AC1719CD696B169D5A845381FBD810A18A86C6B2A24E5`).
  All four hashes were recomputed first-hand this tranche.
* **The exact frozen lines traced here**, in print order:
  * `A:120` (`eq:certified-pt-ht`, whose label sits on `A:123`), `p_t = 9t/16`.
    This is the **defining display** of `p_t`; `certifiedPt` reifies it and no
    numeral is assigned anywhere in this module in its place.
  * `A:125`, "Let `r,r'` be positive powers of two with `r' <= r`, and put
    `q = rt`".
  * `A:128--129`, "fix `h in (0,1]` and `a^sharp in {0,1}`" -- the two parameters
    the column clause is stated over, carried as the structure fields `h_pos`,
    `h_le_one`, `aSharp_le_one`.
  * **`A:138--141`, this tranche's target.**  "Then every restriction of
    `Mhat` with exactly `r' p_t` represented outer blocks, at least
    `ceil(r' t x m)` rows in each represented block, and column density at least
    `h 2^{-a^sharp}`, has communication complexity at least `H + log_2(r' t)`."
    The three clauses become the three legality fields `block_count`,
    `row_floor`, `col_floor` of one structure over one restriction.
  * `A:142--145` (`eq:certified-E3`), the conclusion `H + log_2(r' t)`, which is
    deliberately **not** a field: `M1--M10` keep the desired complexity
    conclusion out of constructor data.  It stays where it was, in the endpoint
    hypothesis `hLocEx` of the banked call.
  * `A:285--304`, the stopping argument, whose state display
    `eq:certified-stopping-state` reads the same three quantities off the current
    rectangle ("blocks", "rows in each", "of the columns") -- the reading that
    fixes column density as a *fraction of the indexed columns*.
  * `03:295--304` (`def:relaxed-interlace`), the row set `[q] x X` and column set
    `[L]` of `Mhat`; this is what a restriction of `Mhat` is a sub-rectangle of,
    and is why the row datum is a `Finset (Blk x Row)` and the column datum a
    `Finset Col`.
  * `03:306--310`, the relaxed-to-classical transfer sentence, "retains at least
    `ceil(mx)` rows in each of at most `t` selected outer blocks and a fraction
    `h` of the indexed columns" -- the second confirmation that the column clause
    is a fraction of `[L]`.
  * `06:1102--1167` (`sec:extension-call-ledger`), the **Localized Extension call
    table**: the four uses in one level, all at `x = 2^{-b_1}`,
    `p_seed = 9t_2/16`, `r' = K/t_2`, with `|Q_s| = r' p_seed = 9K/16`
    (`06:1129`), the per-block row threshold `ceil(K 2^{-b_1} |C_1|)`
    (`06:1136--1137`) and the column density `h 2^{-a^sharp}` (`06:1138`).  This
    table is the DEFINED substitution the datum's parameters are read at; it is
    reproduced as a readout in `callTable_readout`.
  * `09:1269--1276`, the large-capacity branch call, `r' = kappa_v/t_ref`,
    `a^sharp = 1`, at which the adapters below are stated.

## Reader counterpart

`routes/parameterized-np/reader-facing/sections/02-preliminaries.tex`
(SHA-256 `11C43E154C937761D9EFB1172F8D433BE559F3D190D28742AC14B6C5A5D6FAFB`),
opened first-hand this tranche.

* **Claimed, for the structure and its row clause:** `02-preliminaries.tex:427--429`,
  "Say that a row set in `[q] x X` is `(Q,T)`-equipartitioned if it contains at
  least `T` rows in every block indexed by `Q`."  The sentence opens mid-line
  `427` (after "relaxation.") and closes at `429`; `426` belongs to the preceding
  sentence about the transfer statement.  That sentence is the reader's
  name for exactly the row-side datum encoded here, and it is the sentence the
  vendored `NPCC.IsEquipartitionedGE` (`vendor/npc-cc/NPCC/Defs.lean`,
  `def:equipartition-ge`) already implements; the row clause is therefore
  **consumed by pin** rather than restated.  A search of
  `reader-facing/sections/` for `equipartition` returns `02-preliminaries.tex`
  lines `428`, `459`, `505`, `520` only; line `428` is the definition and is
  claimed by no other declaration in `src/` (`453--465` is claimed by
  `CanonicalBracketInvariance`, and `512--526` is a declined near miss of
  `FirstWrapperAssembly`).
* **Declined, with the reason:** `02-preliminaries.tex:512--526`
  (`cor:paper-localized-extension`) prints the *same three-clause shape* -- "retains
  an `h2^{-a^sharp}`-fraction of its columns and its row set is
  `(Q, ceil(r' x_seed m))`-equipartitioned for a set `Q` of cardinality
  `r' p_seed`" -- but at an **uncertified row floor**: its row floor is
  `ceil(r' x_seed m)` where `A:139--140` has `ceil(r' t x m)`, and the two differ
  by the factor `t`.  That row floor is the whole of the distinction, and the
  decline rests on it alone.  The block count is *not* a second difference:
  `06:1111` reads `t = t_2, p_seed = 9t_2/16`, so `p_seed` **is** `p_{t_2}` in the
  sense of `A:120` and agrees with `certifiedPt t_2` exactly.  (Reader `505`, a
  different statement, prints `ceil(r x_seed m)` with `r` rather than `r'`.)
  **The paper wins**: every numeral in this module comes
  from `A:138--141` and `A:120`, and the reader corollary is recorded as a shape
  counterpart only.  It is not claimed here (it is also `FirstWrapperAssembly`'s
  declined near miss and remains declined).

## What this module is for

`LARGE-CAPACITY-BRANCH-001` and `FIRST-WRAPPER-ASSEMBLY-001` carry three
GAP-EXPOSED items of one species -- a source-DEFINED quantity of a concrete
object reified as an unconstrained free binder:

* **(18)** `hLocEx` omits `A:139--140`'s per-block row floor, because *nothing in
  the development models the restriction fed to `thm:certified-localized-extension`*;
* **(20)** `colDens` is a free real, pinned to no column density: `hcol : theta/2^1
  <= colDens` is met by `colDens := theta`;
* **(21)** `rowsPerBlock` is a free natural, pinned to no real represented block:
  the `A:139--140` antecedent is discharged unconditionally from `hrows`.

This module supplies the missing object.  `RestrictionDatum` is the restriction
itself -- a row set in `Blk x Row` and a column set in `Col` -- and its three
legality fields *are* the three frozen clauses.  `selCard`, `rowsPerBlock` and
`colDens` stop being binders and become **readouts of that object**, so at the
consumption site there is no longer anything for a caller to choose:

* `selCard` is `(representedBlocks rowSet).card`, forced to `r' p_t` by
  `block_count`;
* `rowsPerBlock` is the **minimum fibre size over the represented blocks**, and
  `row_floor` quantifies over *those same blocks* -- which is precisely the
  identification item (18) records as missing ("nothing here forces the *counted*
  blocks to be the *same* blocks `hrows` speaks about");
* `colDens` is `colSet.card / |Col|`, a genuine density of a genuine column set,
  and `col_floor` is a demand on it.

Two consequences are recorded as unit tests below and are the reason the defect
class dies rather than moving: `card_row_pos` and `card_col_pos`.  A datum
**forces its row and column carriers nonempty**, at the same place where the
free-binder encoding permitted the evacuating instantiation `m := 0`.

**Supersession, not mutation.**  No byte of `LargeCapacityBranch.lean`,
`FirstWrapperAssembly.lean` or any other banked module is touched.  The banked
declarations keep their statements, their proof terms and their pins, and are
consumed here by pin.  `largeCapacityExtension_ofDatum` is the datum-borne
re-expression of the endpoint call and supersedes both
`LargeCapacityBranch.largeCapacityExtension` (free `selCard`, free `colDens`) and
`FirstWrapperAssembly.largeCapacityExtension_rowFloor` (free `rowsPerBlock` plus
an `hrows` binder) at the consumption site: it has **no** `selCard`, `colDens` or
`rowsPerBlock` binder, **no** `hcount`, `hcol`, `hrows`, `hGne`, `hthetaO` or
`htheta1` binder -- all six are readouts or fields of the datum -- and its
`hLocEx` carries the `A:139--140` clause tied to the counted blocks.  Items (18),
(20) and (21) are closed together for this family; item (19) ("exactly" encoded
as "at least" at the banked sites) is **improved**: `block_count` is the literal
equality of `A:138`, and the banked "at least" shape is derived from it.

## Scope boundary (what is deliberately *not* a field)

The datum is the `A:138--141` **restriction clause bundle**, not the theorem.
The ambient guards of `A:111--137` -- `M` nonempty, `H >= 2`, `0 < x <= 1`,
`eq:certified-base`, `t >= t_cert`, `t` a power of two divisible by `16`,
`tx <= 1`, `r,r'` powers of two, the balanced family and `eps`, and
`eq:certified-E1`/`E2` -- stay where the frozen theorem puts them, as binders of
the endpoint call.  Putting `t >= t_cert` inside the datum would be a structure
demanding more than the clause bundle it encodes, and `eq:tref-search`
(`06:558--572`) forces `k_ref >= 2^19`, so it would also make every concrete
instance unreachable.  The one exception is deliberate and literal: `h_pos`,
`h_le_one` and `aSharp_le_one` are `A:128--129`, the conditions on the two
parameters the column clause is *stated over*, without which `col_floor` is not
the frozen clause.

## Canonical inhabitation: REGISTERED and DEFERRED

The paper's own instance of `A:138--141` is the restriction the wrapper branch
hands to the endpoint at `09:1269--1276` -- the branch-local support set `Q_s`
of `06:1126--1129` together with the denser Bob child's column set.  Building it
needs the wrapper's transcript-level construction, which is not formalized, and
`eq:tref-search` (`06:558--572`) forces `k_ref >= 2^19`, so no legal instance is
`decide`-computable.  The canonical-inhabitation obligation is therefore
**ledger-registered and deferred**, to be discharged when that construction
lands.  What is proved here instead, and is strictly stronger than a synthetic
probe:

* `nonempty_restrictionDatum`, a **general** realization theorem: the encoding is
  inhabited at *every* parameter tuple whose carriers are large enough, so it is
  not over-constrained;
* `datum_consistent_with_frozen_side_conditions`, which instantiates that
  theorem **at the frozen side conditions of the `09:1272` call itself**
  (`4 <= k <= l <= r`, `eq:wrapper-low-simple-gate`, `0 < theta <= 1`) over
  arbitrary carriers, and is the hypothesis-consistency discharge for the
  **datum component** of `largeCapacityExtension_ofDatum`'s bundle: that
  component is satisfiable wherever the frozen text applies it.  It says nothing
  about the joint satisfiability of `hbase`, `htcert`, `hE1` and `hE2`, which are
  the banked binders and are not touched here;
* `datum_consistent_at_frozen_carriers`, the same discharge run at the frozen
  carrier sizes: the block carrier is `[q]` with `q = rt = 2^r` at this
  substitution -- `A:125` together with the certified-lemma substitution display
  `09:316--323`, whose `r = q/t_ref` (`09:320`) makes `A:125`'s `q` **identically**
  the wrapper's own scale-alignment width `q = 2^r` of `09:105`, not a numerical
  coincidence -- and the column carrier is `[L]` of
  `def:relaxed-interlace` (`03:297--299`), kept **general in `1 <= L`** because
  on the `eps = 0` exact-full-product branch (`A:126--128`) `L = |Y|^q` is a
  source-DEFINED quantity that no numeral may stand in for.

`probeDatum` is a `decide`-checkable smoke instance and is labelled
**NON-FIDELITY / BEYOND-PAPER**: its `t = 16` respects `A:117`'s "power of two
divisible by 16" but violates `t >= t_cert`, and its `x = 2^{-4}` names a `b_1`
of ours.  It audits our encoding at a point the paper never visits and is
**not** a substitute for the deferred canonical instance.

## Axiom surface

`EthInapproximability.Prelude` imports `LegacyNPCC.Core` and `LegacyNPCC.Bridge`
only.  `LegacyNPCC.Stage12` is **not** imported, directly or transitively, by
this module, so nothing here reaches the cited AGHP balanced-family axiom.  No
new `axiom` is declared and no opaque certificate is introduced.
-/

namespace EthInapproximability.ParameterizedNP.RestrictionDatum

-- The module namespace and the structure it introduces deliberately carry the same
-- name (this module *is* the `A:138--141` datum), so `dupNamespace` fires on every
-- projection lemma; the duplication is intended, and renaming either half would
-- desynchronize the module name from the frozen clause bundle it encodes.
set_option linter.dupNamespace false

open Finset
open NPCC
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.LargeCapacityBranch
open EthInapproximability.ParameterizedNP.FirstWrapperAssembly

/-! ## §1  The three frozen quantities of `A:138--141`

Each of the three clauses names a quantity that the frozen text **defines**.
They are reified here as defs citing their own defining displays, so that every
later value is obtained by evaluating this chain rather than by assignment. -/

section Quantities

/-- **`p_t = 9t/16`, the frozen block-count scale (`eq:certified-pt-ht`, `A:120`).**

This is the defining display, read in `A:120` inside
`thm:certified-localized-extension`, *not* a use-site inequality: `A:117--118`
fixes `t` as a power of two divisible by `16`, so the natural division is exact
there and `sixteen_mul_certifiedPt` records that exactness as an identity.  The
paper's own call table writes the same quantity `p_seed = 9t_2/16`
(`06:1111`). -/
def certifiedPt (t : ℕ) : ℕ := 9 * t / 16

/-- **`ceil(r' t x m)`, the per-block row floor of `A:139--140`.**

`m` is the row count of the matrix `M` the endpoint is invoked on (`A:111`,
"Let `M` be a nonempty Boolean matrix with `m` rows"), so at every use below it
is formed at `Fintype.card Row` and never at a free natural.  The paper's call
table prints the same quantity as `ceil(K 2^{-b_1} |C_1|)` at `r' t = K`,
`x = 2^{-b_1}`, `m = |C_1|` (`06:1136--1137`). -/
noncomputable def certifiedRowFloor (r' t : ℕ) (x : ℝ) (m : ℕ) : ℕ :=
  ⌈((r' * t : ℕ) : ℝ) * x * (m : ℝ)⌉₊

/-- **`h 2^{-a^sharp}`, the column-density floor of `A:141`.**

Written as a division by `2 ^ a^sharp` so that it prints as the banked
consumption sites do (`theta / 2 ^ (1 : N)` at `a^sharp = 1`, `09:1273`;
`callThreeH e / 2 ^ (0 : N)` at `a^sharp = 0`). -/
noncomputable def certifiedColFloor (h : ℝ) (aSharp : ℕ) : ℝ := h / 2 ^ aSharp

/-- **The represented outer blocks of a restriction (`A:138`, `A:292`).**

`A:138` speaks of the *represented* outer blocks, and `A:292`'s stopping
argument calls the same blocks *active*: they are the blocks the restriction
still holds a row in.  For a restriction whose row set is `R subseteq Blk x Row`
that is the image of `R` under the block projection. -/
def representedBlocks {Blk Row : Type*} [DecidableEq Blk] (R : Finset (Blk × Row)) :
    Finset Blk :=
  R.image Prod.fst

@[simp] theorem mem_representedBlocks {Blk Row : Type*} [DecidableEq Blk]
    (R : Finset (Blk × Row)) (i : Blk) :
    i ∈ representedBlocks R ↔ ∃ z : Row, (i, z) ∈ R := by
  constructor
  · intro hi
    obtain ⟨p, hp, hp'⟩ := Finset.mem_image.1 hi
    exact ⟨p.2, by simpa [hp'] using (show (p.1, p.2) ∈ R by simpa using hp)⟩
  · rintro ⟨z, hz⟩
    exact Finset.mem_image.2 ⟨(i, z), hz, rfl⟩

/-- **`16 p_t = 9t` whenever `16 | t` (`A:117--118` with `A:120`).**

The exactness of the frozen natural division at the values `A:117--118` allows.
General in `t`. -/
theorem sixteen_mul_certifiedPt {t : ℕ} (h16 : 16 ∣ t) : 16 * certifiedPt t = 9 * t := by
  obtain ⟨c, rfl⟩ := h16
  have h : 9 * (16 * c) / 16 = 9 * c := by omega
  simp only [certifiedPt, h]
  ring

/-- **`16 | 2 ^ k` for `k >= 4`**, the divisibility `A:117--118` supplies at the
`09:1272` substitution `t = t_ref = 2^{k}` with `k >= k_ref >= 4`.  General. -/
theorem sixteen_dvd_two_pow {k : ℕ} (hk : 4 ≤ k) : 16 ∣ (2 : ℕ) ^ k := by
  refine ⟨2 ^ (k - 4), ?_⟩
  have : (2 : ℕ) ^ k = 2 ^ 4 * 2 ^ (k - 4) := by
    rw [← pow_add]
    congr 1
    omega
  simpa using this

/-- **`p_t > 0` at the frozen widths.**  With `16 | t` and `t > 0` the block-count
scale is positive, so `A:138`'s count is a positive demand.  General. -/
theorem certifiedPt_pos {t : ℕ} (h16 : 16 ∣ t) (ht : 0 < t) : 0 < certifiedPt t := by
  by_contra hc
  have hzero : certifiedPt t = 0 := by omega
  have := sixteen_mul_certifiedPt h16
  rw [hzero] at this
  omega

/-- **The row floor fits inside the row carrier when `r' t x <= 1`.**

`A:118`'s `tx <= 1` scaled to the call's `r' t`: if `(r' t) x <= 1` then
`ceil(r' t x m) <= m`, so `A:139--140` is a satisfiable demand and not a
cardinality contradiction.  This is the lemma that makes the realization theorem
of §4 apply at the frozen gate.  General. -/
theorem certifiedRowFloor_le {r' t m : ℕ} {x : ℝ}
    (hgate : ((r' * t : ℕ) : ℝ) * x ≤ 1) :
    certifiedRowFloor r' t x m ≤ m := by
  refine Nat.ceil_le.2 ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

end Quantities

/-! ## §2  The datum

One structure, one restriction, three legality fields that are the three frozen
clauses.  The row clause is the vendored `NPCC.IsEquipartitionedGE`
(`def:equipartition-ge`), consumed by pin. -/

section Datum

variable {Blk Row Col : Type*}

/-- **The `A:138--141` restriction clause bundle as one structure.**

A restriction of the relaxed interlace `Mhat` of `def:relaxed-interlace`
(`03:295--304`) is a sub-rectangle of its row set `[q] x X` and its column set
`[L]`; `rowSet` and `colSet` are that rectangle, with `Blk` the outer-block
index, `Row` the row carrier `X` of `M` (so `m = Fintype.card Row` by `A:111`)
and `Col` the indexed column set `[L]`.

The three fields after the parameter conditions are `A:138--141` verbatim:

1. `block_count` -- `A:138--139`, "exactly `r' p_t` represented outer blocks",
   as the **equality** the frozen text prints;
2. `row_floor` -- `A:139--140`, "at least `ceil(r' t x m)` rows in each
   represented block", quantified over the *same* `representedBlocks rowSet` the
   count is taken over;
3. `col_floor` -- `A:141`, "column density at least `h 2^{-a^sharp}`", the
   density being the fraction of the indexed columns retained (`03:306--310`,
   `A:301--302`).

`h_pos`, `h_le_one` and `aSharp_le_one` are `A:128--129` ("fix `h in (0,1]` and
`a^sharp in {0,1}`"), the conditions on the parameters clause 3 is stated over.

The conclusion `eq:certified-E3` is **not** a field: `M1--M10` keep the desired
complexity bound out of constructor data, and it remains where the frozen theorem
puts it, in the endpoint hypothesis of the call. -/
structure RestrictionDatum (Blk Row Col : Type*) [DecidableEq Blk] [Fintype Row] [Fintype Col]
    (r' t aSharp : ℕ) (x h : ℝ) where
  /-- The retained rows of the restriction, inside the interlace row set `[q] x X`. -/
  rowSet : Finset (Blk × Row)
  /-- The retained indexed columns of the restriction, inside `[L]`. -/
  colSet : Finset Col
  /-- `A:128`, `h in (0,1]`, left half. -/
  h_pos : 0 < h
  /-- `A:128`, `h in (0,1]`, right half. -/
  h_le_one : h ≤ 1
  /-- `A:129`, `a^sharp in {0,1}`. -/
  aSharp_le_one : aSharp ≤ 1
  /-- `A:138--139`: exactly `r' p_t` represented outer blocks. -/
  block_count : (representedBlocks rowSet).card = r' * certifiedPt t
  /-- `A:139--140`: at least `ceil(r' t x m)` rows in each represented block,
  with `m` at its defining value `Fintype.card Row` (`A:111`). -/
  row_floor : IsEquipartitionedGE rowSet (representedBlocks rowSet)
    (certifiedRowFloor r' t x (Fintype.card Row))
  /-- `A:141`: column density at least `h 2^{-a^sharp}`. -/
  col_floor : certifiedColFloor h aSharp ≤ (colSet.card : ℝ) / (Fintype.card Col : ℝ)

variable [DecidableEq Blk] [Fintype Row] [Fintype Col] {r' t aSharp : ℕ} {x h : ℝ}

namespace RestrictionDatum

/-- The fibre of the restriction over one outer block: the rows it retains there.
This is the quantity `NPCC.IsEquipartitionedGE` bounds. -/
def fibre (D : RestrictionDatum Blk Row Col r' t aSharp x h) (i : Blk) : Finset (Blk × Row) :=
  D.rowSet.filter (fun p => p.1 = i)

/-- **The `selCard` readout.**  `A:138`'s represented-block census, read off the
restriction instead of chosen: this is what the banked interfaces took as a free
natural binder. -/
def selCard (D : RestrictionDatum Blk Row Col r' t aSharp x h) : ℕ :=
  (representedBlocks D.rowSet).card

/-- **The `rowsPerBlock` readout.**  `A:139--140` speaks of the rows "in each
represented block", so the natural number a caller of the banked interface was
free to choose is here the **minimum fibre size over the represented blocks**.
The `else` branch is unreachable at every legal parameter tuple, by
`represented_nonempty`. -/
def rowsPerBlock (D : RestrictionDatum Blk Row Col r' t aSharp x h) : ℕ :=
  if hne : (representedBlocks D.rowSet).Nonempty then
    (representedBlocks D.rowSet).inf' hne (fun i => (D.fibre i).card)
  else 0

/-- **The `colDens` readout.**  `A:141`'s column density is the retained fraction
of the indexed columns (`03:306--310`, `A:301--302`), a real determined by the
restriction -- not, as in the banked interfaces, a free real that
`colDens := theta` satisfies. -/
noncomputable def colDens (D : RestrictionDatum Blk Row Col r' t aSharp x h) : ℝ :=
  (D.colSet.card : ℝ) / (Fintype.card Col : ℝ)

end RestrictionDatum

end Datum

/-! ## §3  Aux-lemma battery

Five general properties of the new structure, all proved.  The first three say
the three readouts are pinned by the fields; the last two are the non-degeneracy
telescope that kills the defect class rather than moving it. -/

section Battery

variable {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]
  {r' t aSharp : ℕ} {x h : ℝ}

namespace RestrictionDatum

/-- **Aux B1 (`selCard` is pinned, `A:138`).**  The census readout is exactly the
frozen count; nothing is left for a caller to choose.  General. -/
theorem selCard_eq (D : RestrictionDatum Blk Row Col r' t aSharp x h) :
    D.selCard = r' * certifiedPt t :=
  D.block_count

/-- **Aux B2 (the call table's `|Q_s| = 9K/16`, `06:1129`).**

At any width the frozen theorem allows (`16 | t`, `A:117--118`), the census
readout satisfies `16 |Q_s| = 9 K` with `K = r' t`.  This is the paper's own
exact output-size equation for the consuming branch, obtained by evaluating the
`p_t` chain rather than by assigning a value to it.  General. -/
theorem sixteen_mul_selCard (D : RestrictionDatum Blk Row Col r' t aSharp x h)
    (h16 : 16 ∣ t) : 16 * D.selCard = 9 * (r' * t) := by
  rw [D.selCard_eq, ← Nat.mul_assoc, Nat.mul_comm 16 r', Nat.mul_assoc,
    sixteen_mul_certifiedPt h16]
  ring

/-- **Aux B3 (the census as a real, `A:138` at the banked print shape).**  General. -/
theorem selCard_real (D : RestrictionDatum Blk Row Col r' t aSharp x h) (h16 : 16 ∣ t) :
    (D.selCard : ℝ) = 9 * ((r' * t : ℕ) : ℝ) / 16 := by
  have h := D.sixteen_mul_selCard h16
  have hcast : ((16 * D.selCard : ℕ) : ℝ) = ((9 * (r' * t) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast ⊢
  linarith

/-- **Aux B4 (the represented set is nonempty at every legal count).**

`A:138` demands `r' p_t` represented blocks and `A:125` makes `r'` positive,
while `certifiedPt_pos` makes `p_t` positive at the frozen widths, so the
represented set is never empty.  General in the positivity hypothesis. -/
theorem represented_nonempty (D : RestrictionDatum Blk Row Col r' t aSharp x h)
    (hpos : 0 < r' * certifiedPt t) : (representedBlocks D.rowSet).Nonempty := by
  rw [← Finset.card_pos, D.block_count]
  exact hpos

/-- **Aux B5 (`rowsPerBlock` is a genuine per-block minimum).**  Every represented
block carries at least the readout many rows.  General. -/
theorem rowsPerBlock_le_fibre (D : RestrictionDatum Blk Row Col r' t aSharp x h)
    {i : Blk} (hi : i ∈ representedBlocks D.rowSet) :
    D.rowsPerBlock ≤ (D.fibre i).card := by
  have hne : (representedBlocks D.rowSet).Nonempty := ⟨i, hi⟩
  simp only [rowsPerBlock, dif_pos hne]
  exact Finset.inf'_le _ hi

/-- **Aux B6 (`A:139--140` is a theorem about the readout, not an assumption).**

The banked interfaces had to *assume* `ceil(r' t x m) <= rowsPerBlock` of a free
natural.  Here it is proved of the readout, from `row_floor` alone.  General in
the positivity hypothesis. -/
theorem rowFloor_le_rowsPerBlock (D : RestrictionDatum Blk Row Col r' t aSharp x h)
    (hpos : 0 < r' * certifiedPt t) :
    certifiedRowFloor r' t x (Fintype.card Row) ≤ D.rowsPerBlock := by
  have hne : (representedBlocks D.rowSet).Nonempty := D.represented_nonempty hpos
  simp only [rowsPerBlock, dif_pos hne]
  refine Finset.le_inf' hne _ ?_
  intro i hi
  exact D.row_floor i hi

/-- **Aux B7 (`A:141` is a theorem about the readout).**  General. -/
theorem colFloor_le_colDens (D : RestrictionDatum Blk Row Col r' t aSharp x h) :
    certifiedColFloor h aSharp ≤ D.colDens :=
  D.col_floor

/-- **Aux B8 (the column readout is a density).**  A retained fraction of the
indexed columns never exceeds one -- a property no free real has, and the reason
`colDens := theta` is no longer available to a caller.  General. -/
theorem colDens_le_one (D : RestrictionDatum Blk Row Col r' t aSharp x h) :
    D.colDens ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card Col) with hc | hc
  · simp [colDens, hc]
  · have hle : (D.colSet.card : ℝ) ≤ (Fintype.card Col : ℝ) := by
      exact_mod_cast Finset.card_le_univ D.colSet
    have hpos : (0 : ℝ) < (Fintype.card Col : ℝ) := by exact_mod_cast hc
    rw [colDens, div_le_one hpos]
    exact hle

/-- **Aux B9 (non-degeneracy, row side): a datum forces a nonempty row carrier.**

This is the point of the whole encoding.  `A:111` says `M` is a *nonempty*
matrix with `m` rows, and the free-binder encoding permitted the evacuating
instantiation `m := 0` at which the row clause collapsed to a no-op.  A datum
cannot be built at `m = 0`: `block_count` forces a represented block, a
represented block holds a row, and a row lives in `Row`.  General in the
positivity hypothesis. -/
theorem card_row_pos (D : RestrictionDatum Blk Row Col r' t aSharp x h)
    (hpos : 0 < r' * certifiedPt t) : 0 < Fintype.card Row := by
  obtain ⟨i, hi⟩ := D.represented_nonempty hpos
  obtain ⟨z, _⟩ := (mem_representedBlocks D.rowSet i).1 hi
  exact Fintype.card_pos_iff.2 ⟨z⟩

/-- **Aux B10 (non-degeneracy, column side): a datum forces a nonempty column
carrier.**

`A:128`'s `h > 0` plus `A:141` is unsatisfiable over an empty indexed column set:
the density readout would be `0`.  So the column clause, like the row clause, is
a genuine demand at every instantiation.  General. -/
theorem card_col_pos (D : RestrictionDatum Blk Row Col r' t aSharp x h) :
    0 < Fintype.card Col := by
  by_contra hc
  have hzero : Fintype.card Col = 0 := by omega
  have hcol := D.col_floor
  rw [hzero] at hcol
  simp only [Nat.cast_zero, div_zero, certifiedColFloor] at hcol
  have hpos : 0 < h / 2 ^ aSharp := div_pos D.h_pos (by positivity)
  linarith

/-- **Aux B11 (the block census bounds the represented fibres).**  Each fibre
injects into the row carrier, so the per-block readout never exceeds `m`.  A
round-trip check that the readout lives on the right scale.  General. -/
theorem rowsPerBlock_le_card_row (D : RestrictionDatum Blk Row Col r' t aSharp x h)
    (hpos : 0 < r' * certifiedPt t) : D.rowsPerBlock ≤ Fintype.card Row := by
  obtain ⟨i, hi⟩ := D.represented_nonempty hpos
  refine le_trans (D.rowsPerBlock_le_fibre hi) ?_
  classical
  have hinj : Set.InjOn Prod.snd (D.fibre i : Set (Blk × Row)) := by
    intro p hp q hq hpq
    have hp' : p.1 = i := (Finset.mem_filter.1 hp).2
    have hq' : q.1 = i := (Finset.mem_filter.1 hq).2
    exact Prod.ext (by rw [hp', hq']) hpq
  have := Finset.card_le_card_of_injOn (f := Prod.snd) (t := (Finset.univ : Finset Row))
    (fun p _ => Finset.mem_univ _) hinj
  simpa using this

/-- **Aux B12 (statement pole, row side): the empty restriction is not a datum.**

`nonempty_restrictionDatum` and `datum_consistent_with_frozen_side_conditions`
are existential deliverables, so the trivial witness has to be excluded
explicitly.  It is, twice over and independently.  Here: an empty row set
represents no outer block, and `A:138` demands `r' p_t > 0` of them.  General in
the positivity hypothesis. -/
theorem rowSet_nonempty (D : RestrictionDatum Blk Row Col r' t aSharp x h)
    (hpos : 0 < r' * certifiedPt t) : D.rowSet.Nonempty := by
  obtain ⟨i, hi⟩ := D.represented_nonempty hpos
  obtain ⟨z, hz⟩ := (mem_representedBlocks D.rowSet i).1 hi
  exact ⟨(i, z), hz⟩

/-- **Aux B13 (statement pole, column side): the empty restriction is not a
datum.**

The second, independent exclusion of the trivial witness: an empty column set has
density `0`, and `A:128`'s `h > 0` makes `A:141` a strictly positive demand.  So
neither existential deliverable of §4 is met by the empty rectangle.  General. -/
theorem colSet_nonempty (D : RestrictionDatum Blk Row Col r' t aSharp x h) :
    D.colSet.Nonempty := by
  rw [← Finset.card_pos]
  by_contra hc
  have hzero : D.colSet.card = 0 := by omega
  have hcol := D.col_floor
  rw [hzero] at hcol
  simp only [Nat.cast_zero, zero_div, certifiedColFloor] at hcol
  have hpos : 0 < h / 2 ^ aSharp := div_pos D.h_pos (by positivity)
  linarith

/-- **Aux B14 (the Localized Extension call table, `06:1102--1167`).**

At the call table's substitution `r' t = K`, `x = 2^{-b_1}`, `m = |C_1|`, the
three readouts of the datum are the three quantities the table prints:
`|Q_s| = 9K/16` (`06:1129`), the per-block threshold `ceil(K 2^{-b_1} |C_1|)`
(`06:1136--1137`), and the column density `h 2^{-a^sharp}` (`06:1138`).  This is
a fidelity readout of the encoding at the paper's own application table, general
in `K`, `b_1`, the carriers, and the positivity hypothesis. -/
theorem callTable_readout {K : ℕ} {b₁ : ℕ}
    (D : RestrictionDatum Blk Row Col r' t aSharp ((2 : ℝ) ^ (-(b₁ : ℤ))) h)
    (h16 : 16 ∣ t) (hK : r' * t = K) (hpos : 0 < r' * certifiedPt t) :
    16 * D.selCard = 9 * K
      ∧ ⌈(K : ℝ) * (2 : ℝ) ^ (-(b₁ : ℤ)) * (Fintype.card Row : ℝ)⌉₊ ≤ D.rowsPerBlock
      ∧ h / 2 ^ aSharp ≤ D.colDens := by
  refine ⟨by rw [D.sixteen_mul_selCard h16, hK], ?_, D.colFloor_le_colDens⟩
  have hfloor := D.rowFloor_le_rowsPerBlock hpos
  rw [certifiedRowFloor, hK] at hfloor
  exact hfloor

end RestrictionDatum

end Battery

/-! ## §4  Realization: the encoding is inhabited, and inhabited where the paper
applies it

`nonempty_restrictionDatum` is general; `datum_consistent_with_frozen_side_conditions`
is its instance at the frozen side conditions of the `09:1272` call and is the
hypothesis-consistency discharge for §5's endpoint. -/

section Realization

/-- **General realization: the datum is inhabited whenever the carriers allow it.**

Given `A:128--129`'s parameter conditions, enough outer blocks for `A:138`'s
count, a row carrier large enough for `A:139--140`'s floor, and a nonempty
indexed column set, a restriction meeting all three frozen clauses exists.  The
witness is the rectangle `S x T` on a block set `S` of the exact frozen
cardinality and a row set `T` of the exact frozen floor, with all indexed columns
retained.

This is the anti-over-constraint test: the encoding excludes no parameter tuple
the clause bundle allows.  It is **not** the canonical-inhabitation witness --
see the module docstring; the paper's own restriction is registered and
deferred.

**Statement pole (why the trivial witness fails).**  On the column axis the
exclusion is unconditional: `colSet_nonempty` takes no hypothesis and shows an
empty column set has density `0` while `A:128`'s `h > 0` makes `A:141` strictly
positive.  On the row axis the exclusion is scoped to `0 < r' p_t`, which is
`rowSet_nonempty`'s own hypothesis `hpos`: there an empty row set represents no
outer block while `A:138` demands `r' p_t > 0` of them.  That scope costs
nothing, because `r' p_t = 0` is not a legal frozen configuration -- `A:125`
makes `r'` a *positive* power of two and `A:117` makes `t` a power of two
divisible by `16` with `t >= t_cert`, so `p_t > 0` -- and both consistency
theorems below carry `0 < 2^{l-k} p_{2^k}` as their first conjunct precisely so
that the regime the paper applies is on the scoped side.  The two exclusions are
independent, so at legal parameters the existential is not met by degeneracy on
either axis. -/
theorem nonempty_restrictionDatum {Blk Row Col : Type*} [Fintype Blk] [DecidableEq Blk]
    [Fintype Row] [Fintype Col] {r' t aSharp : ℕ} {x h : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hblk : r' * certifiedPt t ≤ Fintype.card Blk)
    (hrow : certifiedRowFloor r' t x (Fintype.card Row) ≤ Fintype.card Row)
    (hRow : 1 ≤ Fintype.card Row) (hCol : 1 ≤ Fintype.card Col) (ha : aSharp ≤ 1) :
    Nonempty (RestrictionDatum Blk Row Col r' t aSharp x h) := by
  classical
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset Blk))
      (n := r' * certifiedPt t) (by simpa using hblk)
  obtain ⟨T, -, hT⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset Row))
      (n := max 1 (certifiedRowFloor r' t x (Fintype.card Row)))
      (by simpa using max_le hRow hrow)
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hT]
    omega
  have hrep : representedBlocks (S ×ˢ T) = S := by
    ext i
    simp only [mem_representedBlocks, Finset.mem_product]
    constructor
    · rintro ⟨z, hz, -⟩
      exact hz
    · intro hi
      obtain ⟨z, hz⟩ := hTne
      exact ⟨z, hi, hz⟩
  have hfib : ∀ i ∈ S, ((S ×ˢ T).filter (fun p => p.1 = i)).card = T.card := by
    intro i hi
    have hset : (S ×ˢ T).filter (fun p => p.1 = i) = ({i} : Finset Blk) ×ˢ T := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by rw [h1]; exact hi, h2⟩, h1⟩
    rw [hset, Finset.card_product, Finset.card_singleton, one_mul]
  have hColpos : (0 : ℝ) < (Fintype.card Col : ℝ) := by exact_mod_cast hCol
  refine ⟨{ rowSet := S ×ˢ T
            colSet := (Finset.univ : Finset Col)
            h_pos := hh0
            h_le_one := hh1
            aSharp_le_one := ha
            block_count := by rw [hrep, hS]
            row_floor := ?_
            col_floor := ?_ }⟩
  · intro i hi
    rw [hrep] at hi
    rw [hfib i hi, hT]
    exact le_max_right _ _
  · have hcard : ((Finset.univ : Finset Col).card : ℝ) = (Fintype.card Col : ℝ) := by
      simp [Finset.card_univ]
    rw [certifiedColFloor, hcard, div_self (ne_of_gt hColpos)]
    have h2 : (1 : ℝ) ≤ 2 ^ aSharp := one_le_pow₀ (by norm_num)
    calc h / 2 ^ aSharp ≤ h / 1 := by
          exact div_le_div_of_nonneg_left (le_of_lt hh0) (by norm_num) h2
      _ = h := by ring
      _ ≤ 1 := hh1

/-- **Hypothesis consistency at the frozen side conditions of `09:1269--1276`.**

The endpoint of §5 conjoins a `RestrictionDatum` with the banked binders of
`LargeCapacityBranch.largeCapacityExtension`.  This theorem discharges the
**datum component** of that bundle -- and only that component: at
`4 <= k <= l <= r`, at `eq:wrapper-low-simple-gate`'s `2^r x_T <= 4/25025` (which
supplies `A:118`'s `t x <= 1` scaled to `r' t = 2^l`, via
`simple_gate_forces_tRef_row_legality`'s own regime), and at `A:128`'s
`0 < theta <= 1`, a datum exists at the `09:1272` substitution
`r' = 2^{l-k}`, `t = 2^k`, `a^sharp = 1`.  Nothing here bears on the joint
satisfiability of the banked `hbase`, `htcert`, `hE1`, `hE2` binders.

So `largeCapacityExtension_ofDatum` is nowhere vacuous for want of a datum.  The
first conjunct records that the demanded block count is **positive** at the same
regime, so the datum is not inhabited by an empty restriction.

**All three carriers stay abstract.**  The frozen block carrier is `[q]`,
`q = rt` (`A:125`), and the frozen column carrier is `[L]`
(`03:297--299`, `def:relaxed-interlace`), which on the `eps = 0`
exact-full-product branch selected here (`A:126--128`) is the source-DEFINED
`L = |Y|^q`.  Neither may be replaced by a numeral inside a statement that claims
legality, and a one-element column carrier would in addition evacuate `col_floor`
(at `|Col| = 1` and `colSet = univ` the clause reduces to `theta/2 <= 1`).  The
carrier demands are therefore carried as the binders `hblk`, `hRow`, `hCol`, and
`datum_consistent_at_frozen_carriers` below runs the discharge at the frozen
sizes.

General in the three carriers, in `k, l, r`, and in `x_T`, `theta`. -/
theorem datum_consistent_with_frozen_side_conditions
    {Blk Row Col : Type*} [Fintype Blk] [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {k ℓ r : ℕ} {xT θ : ℝ} (hk : 4 ≤ k) (hkl : k ≤ ℓ) (hℓr : ℓ ≤ r)
    (hblk : 2 ^ (ℓ - k) * certifiedPt (2 ^ k) ≤ Fintype.card Blk)
    (hRow : 1 ≤ Fintype.card Row) (hCol : 1 ≤ Fintype.card Col)
    (hxT0 : 0 < xT) (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < 2 ^ (ℓ - k) * certifiedPt (2 ^ k)
      ∧ Nonempty (RestrictionDatum Blk Row Col (2 ^ (ℓ - k)) (2 ^ k) 1 xT θ) := by
  have hmul : (2 : ℕ) ^ (ℓ - k) * 2 ^ k = 2 ^ ℓ := by
    rw [← pow_add]
    congr 1
    omega
  have hpowle : ((2 : ℝ) ^ ℓ) ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hℓr
  have hgateℓ : ((2 : ℝ) ^ ℓ) * xT ≤ 1 := by
    nlinarith [le_of_lt hxT0]
  have hcast : (((2 ^ (ℓ - k) * 2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ ℓ := by
    rw [hmul]; push_cast; ring
  refine ⟨Nat.mul_pos (pow_pos (by norm_num) _)
      (certifiedPt_pos (sixteen_dvd_two_pow hk) (pow_pos (by norm_num) _)), ?_⟩
  refine nonempty_restrictionDatum (Blk := Blk)
    (Row := Row) (Col := Col) hθ0 hθ1 hblk ?_ hRow hCol le_rfl
  refine certifiedRowFloor_le ?_
  rw [hcast]
  exact hgateℓ

/-- **The same discharge at the frozen carriers (`A:125`, `03:297--299`).**

`datum_consistent_with_frozen_side_conditions` keeps the carriers abstract; this
corollary runs it at the sizes the frozen text fixes for the `09:1272` call, so
the legality claim is *earned* rather than asserted:

* **block carrier `[q]`.**  `A:125` reads "Let `r,r'` be positive powers of two
  with `r' <= r`, and put `q = rt`".  The value of `A:125`'s `r` at this call is
  *fixed by the source*, not inferred: `09:316--323` is the certified-lemma
  substitution display for `sec:wrapper-low-rungs`, whose parameters the
  large-capacity branch inherits verbatim (`09:1275`, "The other parameters are
  those of \Cref{sec:wrapper-low-rungs}"), and it reads `r = q/t_ref` (`09:320`)
  alongside `eps = 0, h = theta` (`09:322`).  Substituting into `A:125` with
  `t = t_ref` gives
  `q_{A:125} = r . t = (q/t_ref) . t_ref = q_{09:105}` **identically**.  So the
  block carrier is `Fin (2^r)` for `09:105`'s scale-alignment width `q = 2^r`,
  and the agreement between the two occurrences of `q` is an identity forced by
  the substitution display, *not* a numerical coincidence between homonyms.
  (What genuinely is a name collision is `r`: `09:105` uses it as the exponent in
  `q = 2^r`, while `A:125`/`09:320` use it as the certified lemma's own binder,
  there assigned the value `q/t_ref`.  The Lean binder `r` is `09:105`'s
  exponent.)
* **column carrier `[L]`.**  `03:297--299` gives `Mhat` "row set `[q] x X`,
  column set `[L]`" for the indexed family
  `S = (y^{(1)}, ..., y^{(L)}) subseteq Y^q`.  On the `eps = 0` branch
  (`A:126--128`) `L = |Y|^q` is source-DEFINED, so it is kept **general in
  `1 <= L`**: assigning it a numeral here would be assigning a value to a defined
  quantity, and at `L = 1` the column clause would carry no content.

`hblk` is discharged, not re-assumed: with `4 <= k`, `sixteen_dvd_two_pow` and
`sixteen_mul_certifiedPt` give `p_{2^k} = 9 . 2^{k-4}` exactly, whence
`2^{l-k} . p_{2^k} = 9 . 2^{l-4} <= 16 . 2^{l-4} = 2^l <= 2^r` using
`4 <= k <= l <= r`.

The row carrier stays abstract: `A:111`'s `m = |Rows(M)|` is an input of the
endpoint call, not a size the `A:138--141` clause bundle fixes. -/
theorem datum_consistent_at_frozen_carriers {Row : Type*} [Fintype Row]
    {k ℓ r L : ℕ} {xT θ : ℝ} (hk : 4 ≤ k) (hkl : k ≤ ℓ) (hℓr : ℓ ≤ r)
    (hRow : 1 ≤ Fintype.card Row) (hL : 1 ≤ L)
    (hxT0 : 0 < xT) (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < 2 ^ (ℓ - k) * certifiedPt (2 ^ k)
      ∧ Nonempty (RestrictionDatum (Fin (2 ^ r)) Row (Fin L)
          (2 ^ (ℓ - k)) (2 ^ k) 1 xT θ) := by
  refine datum_consistent_with_frozen_side_conditions hk hkl hℓr ?_ hRow ?_ hxT0 hgate hθ0 hθ1
  · have hPt : certifiedPt (2 ^ k) = 9 * 2 ^ (k - 4) := by
      have hP : 16 * certifiedPt (2 ^ k) = 9 * 2 ^ k :=
        sixteen_mul_certifiedPt (sixteen_dvd_two_pow hk)
      have hsplit : (2 : ℕ) ^ k = 16 * 2 ^ (k - 4) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
        congr 1
        omega
      omega
    have hexp : (2 : ℕ) ^ (ℓ - k) * 2 ^ (k - 4) = 2 ^ (ℓ - 4) := by
      rw [← pow_add]
      congr 1
      omega
    have hstep : 2 ^ (ℓ - k) * certifiedPt (2 ^ k) = 9 * 2 ^ (ℓ - 4) := by
      rw [hPt, ← hexp]; ring
    have hℓ4 : (2 : ℕ) ^ 4 * 2 ^ (ℓ - 4) = 2 ^ ℓ := by
      rw [← pow_add]
      congr 1
      omega
    have hle : 9 * 2 ^ (ℓ - 4) ≤ (2 : ℕ) ^ ℓ := by
      calc 9 * 2 ^ (ℓ - 4) ≤ 16 * 2 ^ (ℓ - 4) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 ^ 4 * 2 ^ (ℓ - 4) := by norm_num
        _ = 2 ^ ℓ := hℓ4
    have hfin : (2 : ℕ) ^ ℓ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hℓr
    simpa [Fintype.card_fin, hstep] using le_trans hle hfin
  · simpa using hL

end Realization

/-! ## §5  The datum-borne endpoint call, and the three closed GAP items

The banked declarations are consumed by pin and are not edited.  What changes is
what a caller may choose. -/

section Endpoint

variable {X Y Z : Type*}

/-- **`A:138--139` at the `09:1272` substitution, read off the datum.**

The banked `hcount` binder, now a theorem: at `r' = 2^{l-k}`, `t = 2^k` the
census readout **equals** `9 . 2^l/16`, so the banked "at least" shape (item (19))
is derived from `A:138`'s literal equality rather than assumed alongside it.
General in the carriers, `k <= l`, `4 <= k`. -/
theorem hcount_ofDatum {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {k ℓ : ℕ} {xT θ : ℝ}
    (D : RestrictionDatum Blk Row Col (2 ^ (ℓ - k)) (2 ^ k) 1 xT θ)
    (hk : 4 ≤ k) (hkl : k ≤ ℓ) :
    9 * (((2 : ℕ) ^ ℓ : ℕ) : ℝ) / 16 ≤ (D.selCard : ℝ) := by
  have hmul : (2 : ℕ) ^ (ℓ - k) * 2 ^ k = 2 ^ ℓ := by
    rw [← pow_add]
    congr 1
    omega
  have h := D.selCard_real (sixteen_dvd_two_pow hk)
  rw [hmul] at h
  rw [h]

/-- **`A:141` at `a^sharp = 1` (`09:1273`), read off the datum.**

The banked `hcol` binder, now a theorem: the demand is on the restriction's own
column density, so item (20)'s evacuating instantiation `colDens := theta` is
not available.  General. -/
theorem hcol_ofDatum {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {r' t : ℕ} {xT θ : ℝ}
    (D : RestrictionDatum Blk Row Col r' t 1 xT θ) :
    θ / 2 ^ (1 : ℕ) ≤ D.colDens :=
  D.colFloor_le_colDens

/-- **`A:141` at `a^sharp = 0`, read off the datum.**

The other half of `A:129`'s two allowed values, which the call table uses at rows
(iii) and (iv) of `06:1147--1159` and which the banked
`WrapperProtectedEarly.ExtensionCallThree.column_density` prints as
`callThreeH e / 2 ^ (0 : N) <= colDens`.  General. -/
theorem hcol_ofDatum_zero {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {r' t : ℕ} {x hcol : ℝ}
    (D : RestrictionDatum Blk Row Col r' t 0 x hcol) :
    hcol / 2 ^ (0 : ℕ) ≤ D.colDens :=
  D.colFloor_le_colDens

/-- **`A:139--140` at the `09:1272` substitution, read off the datum.**

The `A:139--140` antecedent that `FirstWrapperAssembly.largeCapacityExtension_rowFloor`
had to discharge from the free binder `hrows`, here proved of the readout.
Item (21)'s "at `rowsPerBlock := refRowFloor ... ` it is literally a theorem"
no longer applies, because `rowsPerBlock` is not a value a caller supplies.
General in the carriers, `4 <= k <= l`. -/
theorem hrows_ofDatum {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {k ℓ : ℕ} {xT θ : ℝ}
    (D : RestrictionDatum Blk Row Col (2 ^ (ℓ - k)) (2 ^ k) 1 xT θ)
    (hk : 4 ≤ k) (hkl : k ≤ ℓ) :
    ⌈(2 : ℝ) ^ ℓ * xT * ((Fintype.card Row : ℕ) : ℝ)⌉₊ ≤ D.rowsPerBlock := by
  have hmul : (2 : ℕ) ^ (ℓ - k) * 2 ^ k = 2 ^ ℓ := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : 0 < (2 : ℕ) ^ (ℓ - k) * certifiedPt (2 ^ k) :=
    Nat.mul_pos (pow_pos (by norm_num) _)
      (certifiedPt_pos (sixteen_dvd_two_pow hk) (pow_pos (by norm_num) _))
  have hfloor := D.rowFloor_le_rowsPerBlock hpos
  rw [certifiedRowFloor, hmul] at hfloor
  have hc : (((2 : ℕ) ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by push_cast; ring
  rw [hc] at hfloor
  exact hfloor

/-- **`A:111`'s nonemptiness, read off the datum.**

The banked `hGne : 1 <= Fintype.card Rw` binder, now a theorem: a datum cannot
live over an empty row carrier.  General in the carriers, `4 <= k <= l`. -/
theorem hGne_ofDatum {Blk Row Col : Type*} [DecidableEq Blk] [Fintype Row] [Fintype Col]
    {k ℓ : ℕ} {xT θ : ℝ}
    (D : RestrictionDatum Blk Row Col (2 ^ (ℓ - k)) (2 ^ k) 1 xT θ)
    (hk : 4 ≤ k) : 1 ≤ Fintype.card Row := by
  have hpos : 0 < (2 : ℕ) ^ (ℓ - k) * certifiedPt (2 ^ k) :=
    Nat.mul_pos (pow_pos (by norm_num) _)
      (certifiedPt_pos (sixteen_dvd_two_pow hk) (pow_pos (by norm_num) _))
  exact D.card_row_pos hpos

/-- **The endpoint call of `09:1269--1276` borne by the restriction datum --
GAP-EXPOSED items (18), (20) and (21) closed together.**

The banked `LargeCapacityBranch.largeCapacityExtension` is consumed **by pin**;
no byte of it changes and its proof term is untouched.  What changes is the
caller's freedom:

* there is no `selCard` binder: the census is `D.selCard`, forced to `r' p_t`;
* there is no `colDens` binder: the density is `D.colDens`, a density of `D`'s
  own column set -- item **(20)** closed at this site;
* there is no `rowsPerBlock` binder and no `hrows` binder: the per-block count is
  `D.rowsPerBlock`, the minimum fibre over the **counted** blocks -- item **(21)**
  closed, and the identification item **(18)** records as missing ("nothing here
  forces the *counted* blocks to be the *same* blocks `hrows` speaks about")
  is now the quantifier of `D.row_floor` itself;
* `hLocEx` carries the `A:139--140` clause, discharged from `D` -- item **(18)**
  closed at this site;
* there is no `hGne`, `hthetaO` or `htheta1` binder: all three are readouts or
  fields of `D`.

The conclusion is the banked one, byte-identical: `C + l <= 1 + memCost mem`.
The `hLocEx` antecedent list is the banked list in the banked order, with the
`A:139--140` clause appended exactly where `largeCapacityExtension_rowFloor`
puts it; only the three restriction quantities are re-expressed.

Non-vacuity of the new hypothesis bundle is
`datum_consistent_with_frozen_side_conditions`.

General in the member type, its cost, `C`, `r`, `k`, `l`, `tcert`, the block and
column carriers of the restriction, and the real parameters `x_T`, `theta`. -/
theorem largeCapacityExtension_ofDatum {Mem : Type*} (memCost : Mem → ℕ) (mem : Mem)
    {C r k ℓ tcert : ℕ} {xT θ : ℝ}
    {Rw Cl : Type*} [Fintype Rw] [Fintype Cl] (Gmat : Rw → Cl → Bool)
    {Blk Col : Type*} [DecidableEq Blk] [Fintype Col]
    (D : RestrictionDatum Blk Rw Col (2 ^ (ℓ - k)) (2 ^ k) 1 xT θ)
    (hk : 4 ≤ k) (hkl : k ≤ ℓ) (hℓr : ℓ ≤ r) (hq4 : k + 2 ≤ r) (hC : 3 ≤ C)
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1)
    (hgate : ((2 : ℝ) ^ r) * xT ≤ 4 / 25025)
    (hbase : C - 1 ≤ LambdaGE Gmat 1 xT (3 / 5))
    (htcert : tcert ≤ 2 ^ k)
    (hE1 : (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)))
    (hE2 : HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)))
    (hLocEx :
      -- `A:111`, `M` a nonempty Boolean matrix, and `H >= 2`
      1 ≤ Fintype.card Rw →
      2 ≤ C - 1 →
      -- `A:112`, `0 < x <= 1`
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
      0 < θ → θ ≤ 1 → θ / 2 ^ (1 : ℕ) ≤ D.colDens →
      -- `eq:certified-E1`, `eq:certified-E2`
      (3 / 5 : ℝ) ^ (2 ^ k) ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + r)) →
      HardSeedFacade.hardSeedColumnDensity k ≤ θ * (2 : ℝ) ^ (-((C : ℝ) - 1 + k)) →
      -- `A:138--139`, exactly `r' p_t` represented outer blocks, and enough of them
      2 ^ (ℓ - k) * (9 * 2 ^ k / 16) = 9 * 2 ^ ℓ / 16 →
      9 * (((2 : ℕ) ^ ℓ : ℕ) : ℝ) / 16 ≤ (D.selCard : ℝ) →
      -- `A:139--140`, at least `ceil(r' t x m)` rows in each represented block,
      -- at `m = Fintype.card Rw` (`A:111`, `09:1270`), read off the datum
      ⌈(2 : ℝ) ^ ℓ * xT * ((Fintype.card Rw : ℕ) : ℝ)⌉₊ ≤ D.rowsPerBlock →
      -- `A:142--144`, the conclusion `H + log_2(r' t)`
      (C - 1) + ℓ ≤ memCost mem) :
    C + ℓ ≤ 1 + memCost mem := by
  have hfloor : ⌈(2 : ℝ) ^ ℓ * xT * ((Fintype.card Rw : ℕ) : ℝ)⌉₊ ≤ D.rowsPerBlock :=
    hrows_ofDatum D hk hkl
  exact largeCapacityExtension memCost mem Gmat hk hkl hℓr hq4 hC hxT0 hxT1
    D.h_pos D.h_le_one (hGne_ofDatum D hk) hgate (hcount_ofDatum D hk hkl) hbase htcert
    hE1 hE2 (hcol_ofDatum D)
    (fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 =>
      hLocEx h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hfloor)

end Endpoint

/-! ## §6  Statement poles and rejection probes

Every field is live-fired: a concrete configuration is exhibited at which it
**fails**, so none of the three clauses is decoration.  These probes claim no
legality -- their numerals are ours and only show a guard firing. -/

section Poles

/-- The smoke restriction: nine outer blocks, four rows retained in every one of
them, two of the four indexed columns retained.

**NON-FIDELITY / BEYOND-PAPER.**  `t = 16` is a power of two divisible by `16`
(`A:117`) but violates `t >= t_cert`, and `x = 2^{-4}` names a `b_1` of ours.
This audits our encoding at a point the paper never visits; the canonical
instance is registered and deferred (module docstring). -/
def probeRows : Finset (Fin 9 × Fin 4) := Finset.univ

/-- The retained indexed columns of the smoke restriction: exactly half of them,
so `A:141` holds with equality at `h = 1`, `a^sharp = 1`. -/
def probeCols : Finset (Fin 4) := {0, 1}

/-- `p_16 = 9`, by evaluating `eq:certified-pt-ht` rather than assigning it. -/
theorem certifiedPt_sixteen : certifiedPt 16 = 9 := by
  norm_num [certifiedPt]

/-- The smoke restriction's per-block row floor, evaluated through the defining
chain: `ceil(1 . 16 . 2^{-4} . 4) = 4`. -/
theorem probe_rowFloor : certifiedRowFloor 1 16 ((2 : ℝ) ^ (-(4 : ℤ))) 4 = 4 := by
  have h : (((1 * 16 : ℕ)) : ℝ) * (2 : ℝ) ^ (-(4 : ℤ)) * ((4 : ℕ) : ℝ) = 4 := by
    norm_num [zpow_neg]
  rw [certifiedRowFloor, h]
  simp

/-- **NON-FIDELITY smoke instance.**  All three `A:138--141` clauses hold on the
concrete restriction above: nine represented blocks (`= 1 . p_16`), four rows in
each (`= ceil(1 . 16 . 2^{-4} . 4)`), and column density `2/4 = 1/2`, which meets
`h 2^{-a^sharp} = 1/2` with equality.  Labelled **BEYOND-PAPER** as above. -/
def probeDatum :
    RestrictionDatum (Fin 9) (Fin 4) (Fin 4) 1 16 1 ((2 : ℝ) ^ (-(4 : ℤ))) 1 where
  rowSet := probeRows
  colSet := probeCols
  h_pos := by norm_num
  h_le_one := le_rfl
  aSharp_le_one := le_rfl
  block_count := by
    rw [certifiedPt_sixteen]
    decide
  row_floor := by
    have hcard : Fintype.card (Fin 4) = 4 := by simp
    rw [hcard, probe_rowFloor]
    change ∀ q ∈ representedBlocks probeRows,
      4 ≤ (probeRows.filter (fun p => p.1 = q)).card
    decide
  col_floor := by
    have hc : (probeCols.card : ℝ) = 2 := by norm_num [probeCols]
    have hu : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
    rw [certifiedColFloor, hc, hu]
    norm_num

/-- **Statement pole (`A:138`): the block-count field fires.**  A restriction
spread over only eight of the nine demanded blocks fails `block_count`, so the
field is not satisfied by every rectangle.  Rejection probe, claiming no
legality. -/
theorem block_count_rejects :
    (representedBlocks (Finset.univ : Finset (Fin 8 × Fin 4))).card ≠ 1 * certifiedPt 16 := by
  rw [certifiedPt_sixteen]
  decide

/-- **Statement pole (`A:139--140`): the row-floor field fires.**  Deleting a
single row from block `0` leaves that block represented but holding three rows,
one short of the floor `4`, and the field fails.  So `row_floor` is a demand on
the *counted* blocks, not a formality.  Rejection probe, claiming no legality. -/
theorem row_floor_rejects :
    ¬ IsEquipartitionedGE (probeRows.erase ((0 : Fin 9), (0 : Fin 4)))
        (representedBlocks (probeRows.erase ((0 : Fin 9), (0 : Fin 4)))) 4 := by
  intro hcon
  have hmem : (0 : Fin 9) ∈
      representedBlocks (probeRows.erase ((0 : Fin 9), (0 : Fin 4))) := by decide
  have := hcon 0 hmem
  revert this
  decide

/-- **Statement pole (`A:141`): the column-density field fires.**  Retaining one
of the four indexed columns gives density `1/4`, below the demanded
`h 2^{-a^sharp} = 1/2`, so the field fails.  Together with `colDens_le_one` this
is the exact content of item (20): a density can be too small, a free real cannot.
Rejection probe, claiming no legality. -/
theorem col_floor_rejects :
    ¬ certifiedColFloor (1 : ℝ) 1
        ≤ ((({0} : Finset (Fin 4)).card : ℝ) / (Fintype.card (Fin 4) : ℝ)) := by
  have hc : ((({0} : Finset (Fin 4)).card : ℝ)) = 1 := by norm_num
  have hu : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
  rw [certifiedColFloor, hc, hu]
  norm_num

/-- **Statement pole: the readouts of the smoke instance are the demanded values.**

A round-trip check on the three readouts at a point where all of them evaluate:
census `9`, per-block minimum `4`, density `1/2`.  If any readout drifted from
its field, this would stop compiling. -/
theorem probeDatum_readouts :
    probeDatum.selCard = 9 ∧ probeDatum.rowsPerBlock = 4 ∧ probeDatum.colDens = 1 / 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · have hmem : (0 : Fin 9) ∈ representedBlocks probeDatum.rowSet := by decide
      have hfib : (probeDatum.fibre 0).card = 4 := by decide
      exact le_of_le_of_eq (probeDatum.rowsPerBlock_le_fibre hmem) hfib
    · have hpos : 0 < 1 * certifiedPt 16 := by
        rw [certifiedPt_sixteen]
        norm_num
      have hfloor := probeDatum.rowFloor_le_rowsPerBlock hpos
      have hcard : Fintype.card (Fin 4) = 4 := by simp
      rw [hcard, probe_rowFloor] at hfloor
      exact hfloor
  · have hc : ((probeDatum.colSet.card : ℕ) : ℝ) = 2 := by norm_num [probeDatum, probeCols]
    have hu : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 4 := by simp
    rw [RestrictionDatum.colDens, hc, hu]
    norm_num

end Poles

end EthInapproximability.ParameterizedNP.RestrictionDatum
