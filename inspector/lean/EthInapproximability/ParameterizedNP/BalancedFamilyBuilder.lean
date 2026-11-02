import EthInapproximability.ParameterizedNP.PrimeWindow
import EthInapproximability.ParameterizedNP.IteratedCanonicalChaining
import EthInapproximability.ParameterizedNP.LevelStepConstruction

/-!
# Parameterized NP route: the balanced-family builder `A_bal` of `14:1749--1782`

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/`.  Every line cited below was opened first-hand
  in the frozen files this round:
  - **`14:1556--1565`, the machines frame.**  "There exist named total machines
    `A_bal` and `A_balEntry` in `M`.  For positive integers `q,t,m` with
    `q >= t >= 1`, their exact parsed-output equation is
    `parse^{q,t,m}_bal(out_M(A_bal, enc_M(q,t,m))) = (N, d_bal)`", where
    `14:1567--1570` fixes that "the dependent parser returns a structural
    `N in N_{>0}`, a descriptor `d_bal in {0,1}^*`, and records the context
    `(q,t,m,N)`", and `14:1570--1582` displays the entry equation
    `c_{d_bal}(l)(i) = parse_{[m]}(out_M(A_balEntry, enc_M(q,t,m,N,d_bal,l,i)))`
    for `l in [N]` and `i in [q]`.
  - **`14:1583--1594`, `eq:effective-balanced-builder`** -- "Their mathematical
    correctness theorem, not a proof object in the machine output, proves
    `1 <= t <= q`, `0 < N <= B_bal(q,t,m)`, `c_{d_bal} : [N] -> [m]^q`,
    `c_{d_bal}` is indexed `(q,t,1/(100t))`-balanced."  `14:1596--1597` adds
    "Repeated indices in `[N]` remain distinct even if their represented columns
    are equal."
  - **`14:1749--1763`, the builder algorithm.**  "On a parsed triple `(q,t,m)`
    satisfying `q >= t >= 1`, put `X = max{q, 1000mt^2, 2}`.  The builder scans
    the finite list `X, X+1, ..., 2X-1` in increasing order, testing each entry
    for primality by trial division.  If no entry is prime, it returns the
    reserved failure output.  By `lem:checked-prime-window`, a prime occurs in
    this list on every valid branch, so the builder stops at the first prime `p`
    with `X <= p < 2X`.  It sets `N = p^t` and writes the self-delimiting
    descriptor `d_bal = (poly-v1, p)`, together with `N`."  `14:1764--1766`:
    "The dependent parser checks the version tag, `X <= p < 2X`, primality of
    `p`, and `N = p^t`.  Thus the descriptor does not contain an expanded list
    of `Nq` values."
  - **`14:1768--1782`, the guarded accessor.**  "For `l in [N]`, the accessor
    computes the unique base-`p` digits `a_r(l) = floor(l/p^r) mod p`
    (`0 <= r < t`).  For `i in [q]`, it applies Horner's rule in `F_p` and
    returns" `eq:literal-balanced-accessor` (display `14:1774--1778`, `\label`
    at `14:1777`)
    `c_{d_bal}(l)(i) = (sum_{r=0}^{t-1} a_r(l) i^r mod p) mod m`;
    then `14:1779--1782` "All reductions use the least nonnegative residue.  The
    checks preceding `eq:literal-balanced-accessor`, including `l < N`, `i < q`,
    and `m > 0`, are performed before any division or remainder operation.  This
    is the promised machine `A_balEntry`."
  - **`14:1784--1810`, the balancedness content** -- distinct coordinates
    `i_1,...,i_r` with `r <= t` "remain distinct in `F_p` because `q <= p`"
    (`14:1785--1786`); the `r`-row Vandermonde map `F_p^t -> F_p^r` is
    surjective with every fibre of size `p^{t-r}` (`14:1788--1792`); each
    residue mod `m` has `floor(p/m)` or `ceil(p/m)` representatives, so each
    factor lies in `[1-m/p, 1+m/p]` (`14:1792--1798`); "Here `m/p <= 1/(1000t^2)`"
    (`14:1799`); Bernoulli gives `(1-m/p)^r >= 1 - rm/p >= 1 - 1/(100t)`
    (`14:1799--1802`) and the geometric tail gives
    `(1+m/p)^r <= 1/(1-rm/p) <= 1 + 2rm/p <= 1 + 1/(100t)` (`14:1803--1808`).
    `14:1810--1813` closes with `0 < N = p^t < (2X)^t = B_bal(q,t,m)`.
    **This half is LANDED in Part 8 (`cc-t7h`); see "What is landed, and
    exactly what remains".**
  - **`14:1621--1632`, the storage identification.**  "For every `0 <= i < k`,
    the public record `Public_i`, positive integers `q_{2,i} >= t_{2,i} >= 1`,
    and the literal output `(N_{2,i}, d_i)` of
    `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`, where `m_{1,i} = |Rows(M_1^{(i)})|`.  If
    `e_i : [m_{1,i}] -> Rows(M_1^{(i)})` is the canonical increasing
    equivalence, the family actually stored in the parameter record is
    `c_{2,i}(l)(r) = e_i(c_{d_i}(l)(r))`, `Pi_i = (K_*, N_{2,i}, c_{2,i})`."
  - `14:1521--1527`, `lem:checked-prime-window` ("For every natural number
    `X >= 2`, there is a prime `r` such that `X <= r < 2X`"), and its proof
    `14:1529--1543`, which names the route-level checked adapter
    `EthInapproximability.ParameterizedNP.primeWindow` in
    `src/EthInapproximability/ParameterizedNP/PrimeWindow.lean` **by path**.
    That is the interface this module consumes; it is a checked interface, so it
    is consumed and never re-proved.
  - `14:1742--1747`, the totality convention: "Each has a reserved failure
    output.  On a malformed input, a failed dependent-context check, or an
    out-of-range query, it writes that output and halts. ... This convention
    makes totality independent of the source promise."
  - `14:1669--1676`, which lists what the realization's correctness theorem
    proves, including "the literal builder bound
    `eq:literal-balanced-family-size`".
  - `02:176--198`, `def:effective-schedule-certificate`, whose lines `178--181`
    print `X_bal(q,t,m) = max{q,1000mt^2,2}` and whose
    `eq:balanced-family-envelope` (label `187`, display `183--188`) prints
    `B_bal(q,t,m) = (2 X_bal(q,t,m))^t`.  **Both are already banked** as
    `ScheduleMajorantResidue.xBal` and `ScheduleMajorantResidue.bBal` and are
    consumed by pin here; neither is re-reified.
  - `06:2124--2130`, `eq:literal-balanced-family-size`, banked as
    `ScheduleMajorantResidue.literalBalancedFamilySize`, consumed by pin.
  - `03:277--289`, `def:balanced-family` ("An indexed family
    `S = (y^{(1)},...,y^{(L)})` in `Y^q` is `(q,t,eps)`-balanced if, for every
    `J subseteq [q]` with `|J| <= t` and every pattern `a in Y^J`,
    `Pr[y|_J = a] in [(1-eps)/|Y|^{|J|}, (1+eps)/|Y|^{|J|}]`"), the predicate
    the staged half must land against.  Its Lean home is the **vendored**
    `NPCC.IsBalancedFamily` (`vendor/npc-cc/NPCC/Relaxed.lean:19`), which is
    frozen and is *not* re-reified here.
  - `05:172--190`, `def:level-parameters`, `Pi = (K, N_2, c_2)` with
    `N_2 in N_{>0}` structural, banked as `PublicRecords.LevelParams`.
  - `12:93--104`, the unique increasing equivalence `e_X : [|X|] -> X`, banked
    as `IteratedCanonicalChaining.canonEquiv`, consumed by pin as the `e_i` of
    `14:1626`.
  - `06:763--773`, `eq:t2-search` (`t_2 = 2^{k_2}` for the least `k_2` meeting
    three clauses) -- cited **negatively**, as the accessor that is *not* banked
    and that therefore blocks the level-step instantiation; see the staging
    section.
* **Reader counterpart: `lem:paper-explicit-balanced-family`** --
  `routes/parameterized-np/reader-facing/sections/C-effectivity-details.tex`,
  label line `32`, statement lines `31--38` and `43--46`, **proof lines
  `48--76`**.  Opened first-hand at the bytes.

  **The claim EXCLUDES the nested display `39--42`.**  Those four lines are
  `eq:paper-balanced-family-size` (label line `41`), a distinct labelled item
  owned **exclusively** by the banked `ScheduleMajorantResidue.bBal`.  Nesting
  one labelled display inside another labelled item does not license claiming
  both: this module claims the lemma and its proof *around* that display, never
  the display itself, and the statement interval is written split rather than as
  `31--46` for exactly that reason.

  **CORRECTION, made before return rather than left for the gate.**  The first
  pass of this round's sweep searched `reader-facing/` for
  `A_{\mathrm{bal}}`, `balEntry`, `d_{\mathrm{bal}}`, `poly-v1`,
  `X_{\mathrm{bal}}`, `Horner` and `a_r(`, and was about to record a *decline*
  on the strength of the first five returning zero.  They do return zero.  But
  `Horner` returns **one** hit and `a_r(` returns **two**, all inside the proof
  of `lem:paper-explicit-balanced-family`, and re-opening at those bytes shows
  the reader carries the whole builder after all: `:49--51` "Put
  `X = max{q,1000mt^2,2}`, and let `p` be the least prime at least `X`.  By
  `lem:paper-prime-window`, there is a prime `r_0` with `X <= r_0 < 2X`, so the
  minimality of `p` gives `p <= r_0 < 2X`"; `:52--56` the base-`p` coefficient
  order `a_r(l) = floor((l-1)/p^r) mod p` "(so `a_0` changes fastest)" (the
  parenthesis and the words "and set" are on `:56`, so the coefficient-order
  material closes there and the accessor display opens at `:57`);
  `:57--61` the accessor
  `c_l(j) = 1 + ((sum_{r<t} a_r(l)(j-1)^r mod p) mod m)`; `:62--69` the
  Vandermonde uniformity and the `floor(p/m)` / `ceil(p/m)` class sizes;
  `:69--70` `N = p^t < (2X)^t`; `:70--72` "Sequential prime search by trial
  division takes `X^{O(1)}` bit operations"; `:72--74` "Once `p` is in the
  descriptor, Horner evaluation and this base-`p` coefficient decoding are
  polynomial in their encoded inputs"; `:74--75` "Repeated indices remain
  distinct even if their represented tuples coincide."  A decline would have
  been simply false, and it is corrected here rather than shipped.

  **No item is claimed twice.**  The banked `ScheduleMajorantResidue.bBal`
  claims the *display* `eq:paper-balanced-family-size` (label line `41`,
  display lines `39--42`) and its docstring records that "no other line in the
  interval is claimed here".  This module claims the *lemma* `:32`, a distinct
  labelled item, on its statement lines `31--38` and `43--46` **with `39--42`
  carved out**, together with its proof lines `48--76`, which no Lean module
  claimed before this round (checked by fixed-string sweep of `src/**/*.lean`,
  the crosswalk and the ledger).  The carve-out is the whole of the difference
  between this and an overlapping claim, and it is written into the interval
  rather than left to the reader to infer.
* **The reader/autoformalization index transport, recorded because this is
  exactly where it bites.**  The reader is **one-based** and the
  autoformalization is **zero-based** (crosswalk preamble, `sigma_d(r) = r+1`).
  So the reader's `a_r(l) = floor((l-1)/p^r) mod p` and
  `c_l(j) = 1 + (... (j-1)^r ...)` are the *same* maps as the frozen
  `14:1770--1771` / `eq:literal-balanced-accessor` after `l_auto = l - 1`,
  `j_auto = j - 1` and `value_auto = value_reader - 1`.  This module transcribes
  the **autoformalization** (zero-based) form, per `conv:finite-slots`: `balDigit
  p l r = l / p^r % p` with no shift, and `balEntryVal` with no `1 +`.  The
  difference is a recorded transport, not a divergence, and it is the same
  one-based/zero-based shift the crosswalk row for this pair already carries.
  The reader's coefficient-order sentence "(so `a_0` changes fastest)" is the
  same convention `balDigit` implements, since `a_0 = l % p`.
* **One further reader item, deliberately NOT claimed here.**
  `lem:paper-prime-window` (`C-effectivity-details.tex`, label line `13`,
  statement `12--18`, proof `20--29`) is the reader's counterpart of
  `lem:checked-prime-window`, and its proof names
  `EthInapproximability.ParameterizedNP.primeWindow` by path -- so it belongs to
  that banked interface, which this module **consumes by pin and does not
  re-prove**.  `primeWindow_at_xBal` is the *instantiation* at `X = X_bal`, not
  the interface, and claiming the reader lemma for it would attach one reader
  item to a declaration that is not what the reader lemma states.  Recorded and
  refused, the same way the `cc-t7e` homonym mis-assignment was refused.

## What this module is, and the placement decision

`14:1749--1782` is a **construction**: it exhibits the two named total machines
that `14:1556--1565` asserts to exist, as literal finite algorithms.  This
module is that construction, in the shape the frozen proof gives it, together
with the storage identification `14:1621--1632` that consumes its output.

**Placement, decided against the frozen text.**  Three options were weighed.

1. `ScheduleMajorantResidue.lean`.  **Rejected.**  That module owns the
   *envelope* `X_bal` / `B_bal` of `02:176--198` -- a numerical majorant with no
   machine attached -- and its stated test is that each declaration is a
   schedule residue.  A prime scan, a descriptor type, a guarded accessor and a
   parameter-record constructor are none of those, and putting them there would
   force that module to import `PrimeWindow` and the level-step layer, which it
   deliberately does not see.
2. `StageTwoRelaxed.lean` (or `PublicRecords.lean`).  **Rejected.**  Both own
   the *consumer* side: `Pi = (K, N_2, c_2)` as a record, and the standing
   disposition -- stated in both, at `PublicRecords.LevelParams` and
   `StageTwoRelaxed.stageTwo_balancedness_is_not_a_field` -- that balancedness
   is not a field of `Pi`.  The builder is the producer of `N_2`, from a
   different section of the paper (`14`, not `05`/`07`), and folding it into the
   record layer would put a `sections/14` machine inside a `sections/05` type.
3. **A new module.  Chosen.**  It consumes `PrimeWindow` (the checked prime
   interface the frozen proof names by path), `ScheduleMajorantResidue` (the
   envelope, by pin, through `LevelStepConstruction`'s import closure),
   `IteratedCanonicalChaining` (the canonical increasing equivalence `e_i`, by
   pin) and `PublicRecords` (the record type `Pi`, by pin).  It restates nothing
   from any of them and adds no import to any banked module.

## The two candidate encodings, and why A was landed

The concept is novel on this route, so two encodings were built and ranked.

* **Candidate A (landed).**  The descriptor is a two-field record
  `BalDescriptor = (tag : String, p : Nat)` with the frozen literal
  `balVersionTag = "poly-v1"`; the parser is a decidable `Prop` with exactly the
  four frozen checks; the builder and the accessor are `Option`-valued, with
  `none` as the frozen *reserved failure output* of `14:1743--1745`.
* **Candidate B (rejected).**  The descriptor is the bare prime `p : Nat`, the
  builder is `Nat x Nat` and returns `(0,0)` on failure, and the accessor is
  `Nat`-valued returning `0` on an out-of-range query.

**Ranking.**  (i) *Aux lemmas proved*: A proves the four parser checks of
`14:1764--1765` as a single canonical-inhabitation lemma and proves four
independent guard-rejection lemmas; B cannot state the version-tag check at all
(there is no tag) and cannot state any rejection lemma, because its failure
value `0` is a **legal** accessor output (`0 in [m]` whenever `m > 0`), so
"the guard fired" is indistinguishable from "the entry is zero".  (ii)
*Faithfulness*: `14:1763` writes the descriptor as the pair `(poly-v1, p)`, and
`14:1764` says the parser "checks the version tag" -- a check B deletes; and
`14:1743--1745` reserves a failure output *distinct* from the success outputs,
which B conflates.  (iii) *Length*: B is about fifteen lines shorter and buys
that by deleting two frozen obligations.  A wins on all three, and B is recorded
here as refuted rather than merely unchosen.

Within A, one further decision: the descriptor's `tag` is a `String` and not a
one-constructor inductive.  A one-constructor tag makes the frozen "checks the
version tag" clause *unfalsifiable*, which is the statement-pole defect of a
guard that cannot fire.  With a `String` the check is a real check, and
`descriptor_wrong_tag_rejected` exhibits a descriptor that fails it.

## Fixed-interface discipline: what is consumed, and what is not restated

* `PrimeWindow.primeWindow` -- the checked adapter `14:1535--1539` names by
  path.  It is **consumed, never re-proved**: this module contains no second
  proof of Bertrand's postulate and no second prime-window statement.  Its one
  local wrapper, `primeWindow_at_xBal`, is the *instantiation* at `X = X_bal`,
  which is what the builder needs and what the interface does not itself say.
* `ScheduleMajorantResidue.xBal`, `.bBal`, `.two_le_xBal`,
  `.literalBalancedFamilySize` -- consumed by pin.  (`.bBal_pos` was listed here
  in the authored draft and is **withdrawn at the verify seat**: it occurs in no
  proof term of this module, so claiming it as consumed was false.)  **No second
  reification of
  `X_bal` or `B_bal` appears here**, and `two_le_xBal` is used, not restated.
* `IteratedCanonicalChaining.canonEquiv` -- the `e_i` of `14:1626`, consumed by
  pin.  This module introduces no second increasing equivalence and proves no
  second uniqueness lemma (`canonOrderEquiv_unique` is banked).
* **Mathlib overlap, disclosed rather than left implicit (`cc-t7h`, verify
  seat).**  `finZModEquiv` (Part 8) restates the underlying equivalence
  `Fin p ~= ZMod p` that Mathlib already supplies as `ZMod.finEquiv`
  (`Mathlib/Data/ZMod/Basic.lean:45`, there as a ring equivalence `≃+*`).  It is
  retained deliberately, and the reason is definitional rather than aesthetic:
  `ZMod.finEquiv` is defined by pattern match on its numeral argument
  (`| 0 => elim`, `| _ + 1 => .refl _`), so at the *abstract* prime
  `balPrime q t m` it is stuck and neither direction reduces to the `natCast` /
  `ZMod.val` maps this module needs.  The local version has those two maps as
  its literal `toFun`/`invFun`, which is what makes `balCoeffEquiv_apply`
  provable by `rfl`.  Mathlib's `finFunctionFinEquiv` *is* consumed by pin for
  the digit layer proper; only this last transport is local.
* `PublicRecords.LevelParams`, `.LevelConfig` -- consumed by pin.  The
  constructor `storedParams` *fills* that banked record; it does not define a
  new one, and it adds no field.
* `vendor/npc-cc` is untouched.  `NPCC.IsBalancedFamily`
  (`vendor/npc-cc/NPCC/Relaxed.lean:19`, the Lean home of `def:balanced-family`
  at `03:277--289`) is **consumed by pin** by Part 8 and is **not re-reified**:
  this module contains no second balanced-family predicate.  It needs no new
  import -- it is already in this module's import closure through
  `LevelStepConstruction` -- and the vendored file is not edited.  The one new
  general lemma about it, `isBalancedFamily_congr_equiv`, is the *value-carrier*
  transport, distinct from the vendored *coordinate* transport
  `NPCC.IsBalancedFamily.projection`, and it is proved here rather than added to
  the frozen vendor tree.  `LegacyNPCC.Stage12` is
  **not** adopted: its `NPCC.aghp_balanced_family_exists` is a cited-existence
  axiom, and the whole point of `sections/14` is that this family is built
  explicitly rather than cited.  No axiom is added by this module.

## What is landed, and exactly what remains

**Landed at `cc-t7g`:** the machines frame `14:1556--1565` (as the parsed-output
equation `balBuild_eq_some` and the entry equation `balEntry_at_builder_output`),
the builder `14:1749--1763` in full, the parser `14:1764--1765` in full, the
guarded accessor `14:1768--1782` in full, the two type clauses of
`eq:effective-balanced-builder` at `14:1587--1589` (`1 <= t <= q` as the
builder's own guard, `0 < N <= B_bal` as `balN_pos` / `balN_le_bBal`, and
`c_{d_bal} : [N] -> [m]^q` as the *type* of `balFamily`), the size clause
`14:1810--1813`, the builder bound `eq:literal-balanced-family-size` at the
actual output, the storage identification `14:1621--1632`, and **the two
arithmetic prerequisites the balancedness argument opens with**: `q <= p`
(`14:1785--1786`) and `m/p <= 1/(1000t^2)` (`14:1799`).

**Landed at `cc-t7h`, in Part 8 below:** the fourth clause of
`eq:effective-balanced-builder`, "`c_{d_bal}` is indexed
`(q,t,1/(100t))`-balanced" (`14:1591--1592`), by the frozen argument
`14:1784--1810`.  Its Lean statement is `balFamily_isBalanced`:

  `NPCC.IsBalancedFamily t (balFamily q t m hm) (1 / (100 * t))`

against the vendored predicate `vendor/npc-cc/NPCC/Relaxed.lean:19`, under
`1 <= t <= q` and `0 < m` -- exactly the shape the ledger row prescribed, with
no clause weakened and no hypothesis added.  The three layers the frozen proof
needs are `vandEval_surjective` + `card_vandEval_fiber` +
`card_vandEval_preimage_mul` (the `r`-row Vandermonde map `F_p^t -> F_p^r`,
surjective with equinumerous fibres, `14:1788--1792`), `residue_card_upper` +
`residue_card_lower` (the `floor(p/m)` / `ceil(p/m)` representative count,
`14:1792--1795`), and `balanced_ratio_bound` (Bernoulli and the geometric tail,
`14:1799--1808`), the last consuming the banked `m_le_balPrime_ratio` by pin.
`storedFamily_isBalanced` carries the clause across the storage identification
`14:1629--1631` to the family the Stage-2 consumer actually reads.  **Ledger row
`S5-BALANCED-FAMILY` is discharged on item (a), the balancedness clause, and on
that item only; the row itself stays OPEN** on item (b), the level-step
instantiation `A_bal(q_{2,i}, t_{2,i}, m_{1,i})` -- whose `eq:t2-search` half
lands at `cc-t7j` in Part 9 below and whose `(Public, K)` evaluation of
`L_h`, `H_max`, `k_2` and `t_2` lands at `cc-t7k` in Part 11, leaving the call
blocked on the structural row `4 t_2 <= q_2` (`06:835`) alone -- which `cc-t7l`
in Part 12 below *locates* rather than discharges: the row is item (v) of the
finite condition list `06:1197--1226` (`06:1219--1220`), discharged beyond a
threshold by `sec:effective-cutoff` (`06:1169--1177`), so the call stays
blocked here (**unchanged at `cc-t8b`/`cc-t8c`**: Part 13 adds an unconditional
NON-FIDELITY *storage-shape* probe of `14:1629--1632`, which supplies neither
the paper's data precondition `1 <= t_{2,i} <= q_{2,i}` of `14:1621--1622` nor
the guarded endpoint `balBuild_eq_some`, and therefore leaves item (b) exactly
where `cc-t7l` left it) -- and on item
(c), the three
phantom `lem:cited-balanced-family` comment sites in the banked
`Section5Admissibility.lean`.  Neither is this module's to close here.  Its
reader counterpart is the same lemma
this module already claims: `C-effectivity-details.tex:62--69`, "For every set of
at most `t` distinct coordinates, the Vandermonde map is uniform over `F_p` on
those coordinates ... the field elements whose residue modulo `m` is `a-1` form a
class of size either `floor(p/m)` or `ceil(p/m)` ... within a multiplicative
factor `1 +- 1/(100t)` of `m^{-r}`".  Those lines are inside the claimed interval
`48--76` and were therefore already attached to this module's claim; **no new
reader item is claimed and none was invented for this half.**

**Landed at `cc-t7j`/`cc-t7j-r1`/`cc-t7k`, in Parts 9, 10 and 11 below, and
stated as a TARGET rather than a discharge.**  The *level-step instantiation*
of `14:1621--1632` -- `A_bal(q_{2,i}, t_{2,i}, m_{1,i})` -- is **NOT
DISCHARGED**, and nothing below claims it is.  Parts 9 and 10 land the two
pieces of it that need no auxiliary depth `L_h`; Part 11 lands `L_h` itself,
and with it `H_max`, `k_2` and `t_2` at `(Public, K)`:

* **Part 9, consequences of the `eq:t2-search` search spec** (`06:763--773`),
  general in the three schedule inputs at the banked
  `ParameterSchedule.K2Pred` / `.k2` / `.t2` signature.  The two facts the
  consequences rest on are **banked and owned elsewhere**, each in exactly one
  place: `06:813`'s endpoint membership -- "all three clauses of `eq:t2-search`
  hold at the displayed tested endpoint" -- is
  `ParameterSchedule.k2Star_meets_search`, stated at `cc-t7j` where the display
  it verifies is reified, with `k2_le_star` rewired to consume it; and
  membership **at the accessor** (`Nat.sInf_mem` against that witness) is the
  already-banked `MassRedistributionTail.K2Pred_at_k2`, rewired at `cc-t7j-r1`
  to consume the same single owner.  Part 9 consumes both **by pin** and writes
  no second copy of either: the `cc-t7i` round's downstream duplicate of the
  `k2_le_star` proof body, and the `cc-t7j` draft's `k2_spec`, are **deleted,
  not wrapped**.
* **Part 10, the two arguments of the call that need no `L_h`:** the exactness
  receipt `lgQFor_eq` for the `log_2 q` slot of `eq:Hmax`, and the third
  builder argument `m_{1,i} = |Rows(M_1^{(i)})| = q_1 m_R` with its derived
  `m > 0` and `>= 6` floors.

* **Part 11, the auxiliary depth and the search it feeds** (`cc-t7k`): the
  terminal-uniform chain `theta -> k_ref -> e_0^max -> E_B -> E_T ->
  delta_term -> u_term` (`06:525--538`, `06:558--568`, `06:639--652`,
  `06:716--728`), the two depths `b_2` (`06:424`) and `b_T` (`06:241`), and
  then `v_max`, `L_h`, `H_max` (`eq:Hmax`, `06:756--759`), `k_2` and `t_2`
  (`eq:t2-search`, `06:763--770`) -- **all evaluated at `(Public, K)`**, all
  consuming banked reifications by pin, and none of them a free binder.

**What is deliberately NOT authored here, and why (corrected at `cc-t7k`).**
The earlier bytes of this header recorded that the second argument `t_{2,i}`
could not be derived, because one summand of `eq:Hmax` is the **source-defined**
auxiliary depth `L_h = max{b_2, b_T} + max{q, u_term} + 4` (`06:757`) and its
input `u_term` (`eq:terminal-uniform-bounds`, `06:726--728`) had no
`(Public, K)` accessor.  The *name* was indeed absent, but the inference drawn
from it -- that `k_ref`'s "own inputs are not derived at `(Public, K)` either"
-- was an **under-collection** of the frozen displays, of exactly the kind the
`cc-t7j` rule was minted for: `t_0(3/5)` is the fixed route constant
`Section5Admissibility.t0clogOf` (`A:104--107`), `mu_P` is a banked constant
living inside `ParameterSchedule.EB`, and `B_theta` and `L_theta` are
`06:718`/`06:535` at the already-derived `theta` and `Q`.  Part 11 supplies
the chain and evaluates `L_h`, so nothing in this module carries `L_h` as a
free binder any more -- the `cc-t7i` SP-2 defect is closed rather than
deferred.

What is **still** not authored is the `A_bal` call itself -- the paper's
*literal successful output* `(N_{2,i}, d_i)` of `14:1622--1624`: `06:830--831`
requires the schedule's own structural row `4 t_2 <= q_2`
(`eq:stage2-structural-gates`, the display `06:832--849`, this row at `06:835`)
*verified* "before constructing the balanced family", and no theorem on this
route concludes it at any `(P, K)`.

  (**Narrowed at `cc-t8b`, banked at `cc-t8c`.**  The second half of this
  sentence used to read "and no stored family or `Pi_i` record is written under
  any label".  Part 13 makes that half false and it is withdrawn: the banked
  `storedFamily` / `storedParams` are total given `0 < m`, so Part 13 writes a
  record of the storage *shape* of `14:1629--1632` -- explicitly labelled
  **NON-FIDELITY**, since `14:1621--1622` supplies those displays as data
  satisfying `1 <= t_{2,i} <= q_{2,i}` and Part 13 supplies no such fact.  The
  first half is **unchanged and still true**: `balBuild_eq_some` is applied
  nowhere, so the paper's literal successful call remains unauthored, and item
  (b) is not moved by Part 13.)

**Anchor corrected, and the deferral characterized, at `cc-t7l` (Part 12).**
The earlier bytes here attributed the deferral to `06:744--745`; that sentence
is about `eq:terminal-wrapper-gates`, a different display.  The correct anchor
for *this* row is `06:1219--1220`, item (v) of the finite condition list
`06:1197--1226` that `sec:effective-cutoff` (`06:1169--1177`) discharges beyond
a threshold.  Part 12 records, kernel-checked, that the row is not a theorem
over this development's *unrestricted* `(Public, K)` domain -- a fact about the
domain this encoding quantifies over, and **not** a refutation of the paper's
gate, which the paper states as a condition to *verify* and the reader prints
as a supposition (`reader-facing/sections/03-parameterized-construction.tex:72--73`,
"Suppose also that ... `4t_2 <= q_2` ...").  The remaining obligation on the
ledger row `S5-BALANCED-FAMILY-LEVELSTEP-001` is therefore the **cutoff
discharge** of the row at `sec:effective-cutoff` and the call that discharge
will license; registration is not discharge.  (**Unchanged at `cc-t8b`/`cc-t8c`.**
Part 13's storage-shape probe is not that call: it is unconditional precisely
because it drops the paper's data precondition, so it licenses nothing here.)

The reader independently confirms the ordering: its realization machine
(`C-effectivity-details.tex:93--100`) runs "the pre-family part of the compiler
far enough to compute `s_i, q_{2,i}`", then continues "the pre-family traversal
to compute `t_{2,i}`", and only then builds "the indexed Stage-2 family using
`lem:paper-explicit-balanced-family`".  So `t_{2,i}` is a compiler output on
both sides, never a free choice, and the missing Lean object is precisely that
compiler step -- of which Part 9 is the search half and Part 11 the `L_h`
half.  With both landed, what the compiler step still owes is only the
structural gate that licenses the family call.

## Non-vacuity and the statement poles

* **Canonical inhabitation (`14:1762--1765`).**  `balBuild_output_parses` is the
  paper's *own* descriptor passing the paper's *own* four parser checks, at
  every legal `(q,t,m)`.  It is not a synthetic inhabitant: the object is
  `balDescriptor q t m`, which is what `14:1763` writes, and the four
  conjuncts are the four checks `14:1764--1765` lists, in that order.
* **Non-degeneracy (`LANE-GATE 3`).**  `balFamily_not_constant` shows the built
  family takes two different values at the *same* coordinate, at every legal
  parameter triple with a non-degenerate value carrier.  This is the general
  form, proved abstractly: no numeral is instantiated, and no evaluation of the
  prime scan is required.  A constant family is the trivial witness that any
  "there exists a family" statement admits and that the balanced-family clause
  is designed to exclude; `PublicRecords.levelParams_admits_unbalanced_family`
  already banks that a constant family is a legal `Pi`, so exhibiting that this
  builder's output is **not** constant is exactly the missing half.
* **Why the trivial witness fails the existential.**  This module states one
  existential, `primeWindow_at_xBal`, and it is the frozen `14:1756--1758`
  sentence.  The trivial witness fails it because the conclusion pins the
  witness inside `[X_bal, 2 X_bal)`, an interval that excludes every `p < X_bal`
  and in particular excludes the small primes; no constant works, since
  `X_bal >= 1000 m t^2` grows without bound in the parameters.  Every other
  deliverable here is a named-def claim about the pinned construction rather
  than an existential, which is the disposition `STATEMENT POLES` prefers.
* **The guards fire.**  Four rejection probes (`balBuild_eq_none_of_*`,
  `balEntry_eq_none_of_*`) exhibit the reserved failure output on illegal input.
  They claim **no** legality and instantiate no parameter: each is universally
  quantified over the illegal region rather than evaluated at a chosen point.

## Numeral screen (every numeric literal in a declaration STATEMENT)

Proof bodies excluded, per the rule; definition bodies included, since a `def`'s
body *is* its statement.  `xBal`'s internal `1000` and `2` are inside the
*banked* `ScheduleMajorantResidue.xBal` and are that module's rows, not repeated
here.

**This table is PER-DECLARATION, not per-class.**  The authored draft grouped
declarations into thirteen classes, which left no way to check that a given
declaration's literals had all been seen; it is replaced here by one row per
declaration, over all 55.  The 34 declarations carrying at least one statement
literal are listed with their exact multiset, in declaration order; the
remaining 21 carry none and are enumerated at the end.

01. `primeWindow_at_xBal` -- `2`.  CANONICAL-FORM: the window multiplier of
    `14:1525` (`X <= r < 2X`) and `14:1758`.
07. `balPrime_lt_two_mul_xBal` -- `2`.  CANONICAL-FORM, `14:1758`.
08. `two_le_balPrime` -- `2`.  EVALUATED through the banked `xBal`: the third
    entry of `X_bal` at `02:181`.
10. `thousand_le_balPrime` -- `1000`, `2`.  EVALUATED through the banked
    `xBal`: the second entry `1000 m t^2` at `02:181`.
11. `m_le_balPrime_ratio` -- `0`, `1`, `1000`, `2`.  The `0` is the positivity
    floor (`14:1558`); `1`, `1000` and `2` are the canonical displayed
    expression of `14:1799`, "Here `m/p <= 1/(1000t^2)`".
13. `balN_pos` -- `0`.  CANONICAL-FORM, `14:1588` (`0 < N`) and `14:1568`
    (`N in N_{>0}`).
14. `one_lt_balN` -- `0`, `1`.  The `0` is the positivity floor `t >= 1`
    (`14:1558`).  **The conclusion literal `1` is EVALUATED, not
    CANONICAL-FORM**: it is derived from `p >= 2` (`two_le_balPrime`),
    `t >= 1`, and `N = p^t` (`14:1759--1761`).  Neither `14:1588` nor
    `14:1568` states it -- both give only `0 < N`, which is strictly weaker,
    so citing them for this literal would have been wrong.
15. `balN_lt_bBal` -- `0`.  Positivity floor `t >= 1`, `14:1558`.
16. `balN_le_bBal` -- `0`.  Positivity floor `t >= 1`, `14:1558`.
17. `builder_meets_code_envelope` -- `0`, `2`, `2`.  The `0` is the floor
    `14:1558`; both `2`s are the binary-logarithm base of `06:2124--2130`,
    which prints `clog_2`.
20. `BalDescriptor.Parses` -- `2`.  CANONICAL-FORM: the parser window of
    `14:1764` ("checks ... `X <= p < 2X`").
27. `balBuild` -- `0`, `1`.  Builder guard `0 < m` and `1 <= t`,
    `14:1557--1558` and `14:1750`.
28. `balBuild_eq_some` -- `0`, `1`.  Same guard, same anchors.
29. `balBuild_eq_none_of_m_zero` -- `0`.  The rejected value of the guard
    `0 < m`; rejection probe, claims no legality.
30. `balBuild_eq_none_of_t_zero` -- `0`.  The rejected value of the floor
    `t >= 1` (`14:1558`); rejection probe.
34. `balEntryVal_lt` -- `0`.  Accessor guard `m > 0`, `14:1781`.
35. `balEntry` -- `0`.  Accessor guard `m > 0`, `14:1781`.
36. `balEntry_eq_some` -- `0`.  Accessor guard `m > 0`, `14:1781`.
39. `balEntry_eq_none_of_m_zero` -- `0`.  The rejected value of that guard;
    rejection probe.
41. `balEntry_mem` -- `0`.  Accessor guard `m > 0`, `14:1781`.
42. `balFamily` -- `0`.  Accessor guard `m > 0`, `14:1781`.
43. `balFamily_val` -- `0`.  Accessor guard `m > 0`.
44. `balFamily_from_descriptor` -- `0`.  Accessor guard `m > 0`.
45. `balEntry_at_builder_output` -- `0`.  Accessor guard `m > 0`.
46. `balEntryVal_at_zero` -- `0`, `0`.  The floor `t >= 1`, and the zero-based
    first coordinate (`conv:finite-slots` with `14:1773`, `i in [q]`).
47. `balFamily_at_zero_coord` -- `0`, `0`, `0`, `0`.  Three guards (`m > 0`,
    `t >= 1`, `q >= 1`) and the zero-based first coordinate.
48. `balFamily_not_constant` -- `0`, `0`, `0`, `0`, `0`, `1`, `0`.  Three
    guards; then the index slots `0` and `1` and the coordinate `0`.  These
    are zero-based test coordinates under `conv:finite-slots`, **named rather
    than chosen**: any two distinct indices would do, and `one_lt_balN` is
    what makes the second one exist (`14:1596--1597` makes `[N]` an index
    set).
49. `storedFamily` -- `0`.  Accessor guard `m > 0`.
50. `storedParams` -- `0`.  Accessor guard `m > 0`.
51. `storedParams_K` -- `0`.  Accessor guard `m > 0`.
52. `storedParams_N₂` -- `0`.  Accessor guard `m > 0`.
53. `storedParams_c₂` -- `0`.  Accessor guard `m > 0`.
54. `storedParams_N₂_le_bBal` -- `0`, `0`, `0`.  The two guards, and the `0`
    of the conclusion's `0 < N_2` -- the structural positivity of `14:1568`
    and `02:521--524`.
55. `storedFamily_not_constant` -- `0`, `0`, `0`, `0`, `0`, `1`, `0`.  As row
    48, transported along `canonEquiv`.

The remaining **21 declarations carry no statement literal at all**:
`balPrimeExists`, `balPrime`, `xBal_le_balPrime`, `balPrime_prime`,
`balPrime_least`, `q_le_balPrime`, `balN`, `balVersionTag`, `BalDescriptor`,
its `Decidable` instance, `balDescriptor`, `balDescriptor_p`,
`balBuild_output_parses`, `descriptor_wrong_tag_rejected`,
`descriptor_wrong_size_rejected`, `balBuild_eq_none_of_q_lt_t`, `balDigit`,
`balEntryVal`, `balEntry_eq_none_of_index`, `balEntry_eq_none_of_coord`,
`balEntry_eq_none_of_bad_descriptor`.  In `balDigit` and `balEntryVal` the only
`0` is `Finset.range`'s implicit lower end, which is not a written literal
(`14:1770--1771`, `14:1774--1778`).

34 + 21 = 55, so every declaration is covered exactly once.  No occurrence is
unclassified, and no declaration statement contains a numeral standing where a
source-defined quantity belongs.  In particular `N`, `p`, `X`
and `B_bal` never appear as literals: each is the reified defining chain
`balN` / `balPrime` / `xBal` / `bBal`, evaluated in dependency order
`xBal -> balPrime -> balN -> balDescriptor -> balFamily`.

## Binder-provenance table (every FREE binder and every STRUCTURE field)

* `q` -- GENUINELY-FREE.  `14:1557--1558` quantifies the whole interface over
  "positive integers `q,t,m` with `q >= t >= 1`", and `14:1750` repeats it for
  the algorithm.  It is the builder's first input.
* `t` -- GENUINELY-FREE **at this site**, same anchors.  (It is source-defined
  at the *level-step call* `14:1624` as `t_{2,i}`; that call site is
  deliberately **not** declared here -- see the staging section above.)
* `m` -- GENUINELY-FREE at this site, same anchors.  (Source-defined at
  `14:1625` -- the row-cardinality formula `m_{1,i} = |Rows(M_1^{(i)})|` is on
  that line, `14:1626` being the `e_i` line; same disposition.)
* `K : LevelConfig` in `storedParams` -- GENUINELY-FREE.  `02:178--179`, "Fix
  one universal level configuration `K_*` of the type defined in
  `def:level-configuration`": the paper fixes it abstractly and assigns it no
  value, and `05:176` makes it a component of `Pi`.
* `X₁` with `[Fintype X₁] [LinearOrder X₁]` and `h : Fintype.card X₁ = m`, in
  `storedFamily` and `storedParams` -- GENUINELY-FREE carrier.  `14:1626`
  states the equivalence `e_i : [m_{1,i}] -> Rows(M_1^{(i)})` for the row
  carrier at its own cardinality, and `12:93--98` takes the carrier's canonical
  order as ambient (GAP-EXPOSED 2, already banked by `canonEquiv`).  The order
  is an *instance argument*, i.e. the banked disposition rather than a new
  choice: `canonOrderEquiv_unique` banks that any increasing equivalence is
  this one.
* `BalDescriptor.tag : String` -- frozen literal field.  `14:1763` writes the
  descriptor as `(poly-v1, p)`, and the tag slot is its first component; the
  value is pinned by `balVersionTag`, which is what `balDescriptor` always
  writes.  It is a field rather than a fixed constant precisely so that
  `14:1764`'s "checks the version tag" is a check that can fail.
* `BalDescriptor.p : ℕ` -- frozen data field, `14:1763`: the second component
  of `(poly-v1, p)`.  Its value at the builder's output is `balPrime`, i.e.
  **derived**, never assigned.
* `N` and `d`, the parser context of `BalDescriptor.Parses`, `balEntry` and the
  `balEntry_eq_*` family -- **CHECKED, not trusted free construction data.**
  `14:1569--1570` says the parser "records the context `(q,t,m,N)`", and
  `Parses` is what enforces the frozen equations on it: a caller may pass any
  `N` and any `d`, and the fifth conjunct `N = d.p ^ t` plus the tag, window and
  primality checks are what make the entry equation available.  So these are not
  free assignments of the DEFINED quantities `N = p^t` and `d_bal = (poly-v1,p)`
  -- at the builder's own output they are pinned to `balN` and `balDescriptor`
  by `balBuild_output_parses` and `balEntry_at_builder_output`.
* `l`, `i`, `r` -- source-quantified index, coordinate and coefficient
  positions: `l in [N]` and `i in [q]` at `14:1570--1571` and `14:1773`, and
  `0 <= r < t` at `14:1771`.  Zero-based per `conv:finite-slots`.  Every success
  interface carries the matching bound as a hypothesis (`hl`, `hi`), and the
  rejection probes quantify over the complementary region.
* `v` in `balEntry_mem` -- NOT free: pinned by the hypothesis
  `balEntry ... = some v`, so it is the accessor's own output value.
* the generic `p` in `balDigit`, `balEntryVal`, `balEntryVal_at_zero` and
  `balPrime_least` -- a **generic arithmetic abstraction**, deliberately not
  specialized: the digit and Horner layers are stated for any modulus so that
  the builder's consumers substitute the DEFINED `balPrime` at the call site
  (`balFamily`, `balFamily_at_zero_coord`), and `balPrime_least`'s `p` is a
  comparison candidate ranging over all primes above the base, which is what
  makes "the *first* prime" of `14:1758` a real minimality claim.  The
  existential `p` of `primeWindow_at_xBal` is the source existential of
  `14:1523--1525`.  In no case is a free `p` used as construction data.
* `s : String` in `descriptor_wrong_tag_rejected` -- **rejection-only**, ranging
  over the illegal region `s ≠ balVersionTag`.  It claims no legality and is
  never a candidate value for the frozen tag.
* proof binders `hm`, `ht`, `htq`, `hq`, `hl`, `hi`, `hp`, `hd`, `hs`, `hN`,
  `h` -- source guards (`0 < m`, `1 <= t <= q` of `14:1557--1558` and `14:1750`;
  `l < N`, `i < q`, `m > 0` of `14:1779--1781`) or ordinary proof evidence.
  None is a freely assigned source quantity.

Zero source-defined binders remain free.  No field restates a derived
telescope: `BalDescriptor` has exactly the two components `14:1763` prints, and
`N` is deliberately **not** a field of it (`14:1763` writes `N` "together with"
the descriptor, and the parser checks `N = p^t` as a relation *between* them,
which is `Parses`'s fifth conjunct).
-/

namespace EthInapproximability.ParameterizedNP.BalancedFamilyBuilder

open EthInapproximability.ParameterizedNP.PublicRecords
open EthInapproximability.ParameterizedNP.ScheduleMajorantResidue
open EthInapproximability.ParameterizedNP.IteratedCanonicalChaining

/-! ## Part 1: the prime scan (`14:1754--1758`) -/

/-- **The prime-window interface at the builder's own base** (`14:1756--1757`,
"By `lem:checked-prime-window`, a prime occurs in this list on every valid
branch").  This is the banked checked adapter
`EthInapproximability.ParameterizedNP.primeWindow` *instantiated* at
`X = X_bal(q,t,m)`, which is legal because the third entry of `X_bal`
(`02:181`) forces `X_bal >= 2`.  The interface itself is consumed, not
re-proved: there is no second Bertrand argument in this module.

This is the module's only existential.  The trivial witness fails it: the
conclusion confines the witness to `[X_bal, 2 X_bal)`, and `X_bal >= 1000 m t^2`
is unbounded in the parameters, so no fixed prime works. -/
theorem primeWindow_at_xBal (q t m : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ xBal q t m ≤ p ∧ p < 2 * xBal q t m :=
  primeWindow (xBal q t m) (two_le_xBal q t m)

/-- The scan's termination certificate, in the shape `Nat.find` consumes: the
list `X, X+1, ...` contains a prime.  Derived from `primeWindow_at_xBal` by
forgetting the upper end, which the scan re-derives as `balPrime_lt_two_mul_xBal`
below. -/
theorem balPrimeExists (q t m : ℕ) : ∃ p : ℕ, xBal q t m ≤ p ∧ Nat.Prime p := by
  obtain ⟨p, hp, hlo, _⟩ := primeWindow_at_xBal q t m
  exact ⟨p, hlo, hp⟩

/-- **`p`, the first prime the builder stops at** (`14:1754--1758`): "The builder
scans the finite list `X, X+1, ..., 2X-1` in increasing order, testing each entry
for primality ... so the builder stops at the first prime `p` with `X <= p < 2X`."

The scan is reified as `Nat.find` at the decidable predicate
"`>= X_bal` and prime", i.e. the *least* natural satisfying the scan's test --
which is exactly "the first entry of the increasing list that passes".  The
existence argument `Nat.find` consumes is the banked prime-window interface, so
this definition is total and computable, and **no `Classical` choice enters the
construction data**. -/
def balPrime (q t m : ℕ) : ℕ := Nat.find (balPrimeExists q t m)

/-- The scan's output is at least the base: `X <= p`. -/
theorem xBal_le_balPrime (q t m : ℕ) : xBal q t m ≤ balPrime q t m :=
  (Nat.find_spec (balPrimeExists q t m)).1

/-- The scan's output is prime -- the test each entry is put to (`14:1755`). -/
theorem balPrime_prime (q t m : ℕ) : Nat.Prime (balPrime q t m) :=
  (Nat.find_spec (balPrimeExists q t m)).2

/-- **"the *first* prime"** (`14:1758`): any prime at or above the base is at
least the scanned one, so the builder's output is the least such prime and the
scan is deterministic. -/
theorem balPrime_least {q t m p : ℕ} (hle : xBal q t m ≤ p) (hp : Nat.Prime p) :
    balPrime q t m ≤ p :=
  Nat.find_min' (balPrimeExists q t m) ⟨hle, hp⟩

/-- **The window is respected: `p < 2X`** (`14:1758`).  The scan never runs past
the end of the frozen list `X, ..., 2X-1`, because the prime-window interface
already puts a prime inside it and the scan stops at the first one. -/
theorem balPrime_lt_two_mul_xBal (q t m : ℕ) : balPrime q t m < 2 * xBal q t m := by
  obtain ⟨p, hp, hlo, hhi⟩ := primeWindow_at_xBal q t m
  exact lt_of_le_of_lt (balPrime_least hlo hp) hhi

/-- `2 <= p`, from the third entry of `X_bal` (`02:181`) through the scan. -/
theorem two_le_balPrime (q t m : ℕ) : 2 ≤ balPrime q t m :=
  le_trans (two_le_xBal q t m) (xBal_le_balPrime q t m)

/-- **`q <= p`** -- the first sentence of the balancedness argument
(`14:1785--1786`, "They remain distinct in `F_p` because `q <= p`"), obtained
from the first entry of `X_bal` (`02:181`) through the scan.  Landed now even
though the balancedness proof is staged, because it is the arithmetic content of
that sentence and is independent of the counting. -/
theorem q_le_balPrime (q t m : ℕ) : q ≤ balPrime q t m :=
  le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (xBal_le_balPrime q t m)

/-- **`1000 m t^2 <= p`**, from the second entry of `X_bal` (`02:181`) through
the scan.  This is the integer form of `14:1799`, "Here `m/p <= 1/(1000t^2)`". -/
theorem thousand_le_balPrime (q t m : ℕ) : 1000 * m * t ^ 2 ≤ balPrime q t m :=
  le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (xBal_le_balPrime q t m)

/-- **`m/p <= 1/(1000 t^2)`** -- `14:1799` verbatim, over the reals, which is the
form the Bernoulli and geometric estimates of `14:1799--1808` consume.  The
staged balancedness proof will consume this lemma; landing it now discharges the
one arithmetic step of `14:1784--1810` that needs nothing from the Vandermonde
counting. -/
theorem m_le_balPrime_ratio (q t m : ℕ) (ht : 0 < t) :
    (m : ℝ) / (balPrime q t m : ℝ) ≤ 1 / (1000 * (t : ℝ) ^ 2) := by
  have hp : (0 : ℝ) < (balPrime q t m : ℝ) := by
    have := two_le_balPrime q t m
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two this
  have ht' : (0 : ℝ) < 1000 * (t : ℝ) ^ 2 := by
    have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    positivity
  rw [div_le_div_iff₀ hp ht']
  have hnat : 1000 * m * t ^ 2 ≤ balPrime q t m := thousand_le_balPrime q t m
  have : ((1000 * m * t ^ 2 : ℕ) : ℝ) ≤ ((balPrime q t m : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at this
  nlinarith [this]

/-! ## Part 2: the family size `N = p^t` (`14:1759--1761`, `14:1810--1813`) -/

/-- **`N = p^t`** (`14:1759--1761`, "It sets `N = p^t`").  Evaluated through the
definitional chain `xBal -> balPrime -> balN`; no numeral is assigned. -/
def balN (q t m : ℕ) : ℕ := balPrime q t m ^ t

/-- **`0 < N`** -- the structural positivity of `14:1568` (`N in N_{>0}`) and the
first half of `14:1588`. -/
theorem balN_pos (q t m : ℕ) : 0 < balN q t m := by
  have h := two_le_balPrime q t m
  exact pow_pos (by omega) t

/-- `1 < N` whenever `t >= 1`, which is the builder's own guard.  Used by the
non-degeneracy lemma to name a second index. -/
theorem one_lt_balN (q t m : ℕ) (ht : 0 < t) : 1 < balN q t m :=
  Nat.one_lt_pow ht.ne' (two_le_balPrime q t m)

/-- **`N = p^t < (2X)^t = B_bal(q,t,m)`** -- `14:1810--1813`, strict at `14:1812`,
which this declaration OWNS (`R-17`: exact anchor, since the index does no span
subsumption).  `B_bal` is the banked `ScheduleMajorantResidue.bBal`, by pin. -/
theorem balN_lt_bBal (q t m : ℕ) (ht : 0 < t) : balN q t m < bBal q t m := by
  have h := balPrime_lt_two_mul_xBal q t m
  simpa [balN, bBal] using Nat.pow_lt_pow_left h ht.ne'

/-- **`0 < N <= B_bal(q,t,m)`** -- the second clause of
`eq:effective-balanced-builder` (`14:1588`), in the non-strict form that display
prints. -/
theorem balN_le_bBal (q t m : ℕ) (ht : 0 < t) : balN q t m ≤ bBal q t m :=
  (balN_lt_bBal q t m ht).le

/-- **The literal builder bound at the actual output** -- `14:1674--1675` lists
"the literal builder bound `eq:literal-balanced-family-size`" among what the
correctness theorem proves, and `06:2124--2130` is that display.  The banked
`ScheduleMajorantResidue.literalBalancedFamilySize` takes `N_2 <= B_bal` as a
hypothesis; the builder now *supplies* it, so the code envelope holds at the
built family size rather than at an assumed one.  The banked lemma is applied,
not restated. -/
theorem builder_meets_code_envelope (q t m : ℕ) (ht : 0 < t) :
    Nat.clog 2 (balN q t m) ≤ Nat.clog 2 (bBal q t m) :=
  literalBalancedFamilySize (balN_le_bBal q t m ht)

/-! ## Part 3: the descriptor and its parser (`14:1762--1766`) -/

/-- **The frozen version tag** `poly-v1` of `14:1763`, as a literal. -/
def balVersionTag : String := "poly-v1"

/-- **The self-delimiting descriptor `d_bal = (poly-v1, p)`** (`14:1762--1763`).

Exactly the two components the frozen line prints.  `N` is deliberately **not**
a component: `14:1763` writes the descriptor "together with `N`", and
`14:1764--1765` makes `N = p^t` a *check relating* them, which is `Parses`'s
fifth conjunct.  `14:1765--1766` records what this shape buys: "Thus the
descriptor does not contain an expanded list of `Nq` values" -- witnessed below
by `balFamily_from_descriptor`, which recovers every entry from these two
fields. -/
structure BalDescriptor where
  /-- The version tag; `14:1763` writes it `poly-v1`. -/
  tag : String
  /-- The prime the scan stopped at; `14:1763` writes it `p`. -/
  p : ℕ
deriving DecidableEq

/-- **The dependent parser** of `14:1764--1765`: "The dependent parser checks the
version tag, `X <= p < 2X`, primality of `p`, and `N = p^t`."  Four checks, in
the frozen order, over the recorded context `(q,t,m,N)` of `14:1569--1570`. -/
def BalDescriptor.Parses (d : BalDescriptor) (q t m N : ℕ) : Prop :=
  d.tag = balVersionTag ∧
    xBal q t m ≤ d.p ∧ d.p < 2 * xBal q t m ∧ Nat.Prime d.p ∧ N = d.p ^ t

instance (d : BalDescriptor) (q t m N : ℕ) : Decidable (d.Parses q t m N) := by
  unfold BalDescriptor.Parses
  infer_instance

/-- **The descriptor the builder writes** (`14:1762--1763`). -/
def balDescriptor (q t m : ℕ) : BalDescriptor :=
  { tag := balVersionTag, p := balPrime q t m }

/-- The descriptor's prime component is the scanned prime, definitionally. -/
theorem balDescriptor_p (q t m : ℕ) : (balDescriptor q t m).p = balPrime q t m := rfl

/-- **CANONICAL INHABITATION** (`14:1762--1765`).  The paper's *own* descriptor
passes the paper's *own* four parser checks, at every legal parameter triple.
This is not a synthetic inhabitant of `BalDescriptor`: the object is
`balDescriptor q t m`, the pair `14:1763` writes, and the four conjuncts are the
four checks `14:1764--1765` lists, in that order. -/
theorem balBuild_output_parses (q t m : ℕ) :
    (balDescriptor q t m).Parses q t m (balN q t m) :=
  ⟨rfl, xBal_le_balPrime q t m, balPrime_lt_two_mul_xBal q t m,
    balPrime_prime q t m, rfl⟩

/-- **The version-tag check is a real check** (`14:1764`).  A descriptor carrying
the correct prime but a different tag is rejected.  A rejection probe: it claims
no legality and instantiates no parameter, being universally quantified over the
illegal region `s ≠ poly-v1`. -/
theorem descriptor_wrong_tag_rejected (q t m : ℕ) (s : String)
    (hs : s ≠ balVersionTag) :
    ¬ (BalDescriptor.mk s (balPrime q t m)).Parses q t m (balN q t m) :=
  fun h => hs h.1

/-- **The size check is a real check** (`14:1765`, `N = p^t`).  A context whose
recorded `N` differs from `p^t` is rejected, whatever the descriptor. -/
theorem descriptor_wrong_size_rejected (q t m N : ℕ) (d : BalDescriptor)
    (hN : N ≠ d.p ^ t) : ¬ d.Parses q t m N :=
  fun h => hN h.2.2.2.2

/-! ## Part 4: the builder machine `A_bal` (`14:1556--1565`, `14:1742--1763`) -/

/-- **`A_bal`, as its parsed output** (`14:1560--1565`).  The frozen equation is
`parse^{q,t,m}_bal(out_M(A_bal, enc_M(q,t,m))) = (N, d_bal)`; this is that parsed
pair, with `14:1742--1747`'s *reserved failure output* modelled by `none`.

The guard is the frozen admissibility of the input triple: `14:1557--1558`
("positive integers `q,t,m` with `q >= t >= 1`") and `14:1750` ("On a parsed
triple `(q,t,m)` satisfying `q >= t >= 1`").  On a triple outside it the machine
"writes that output and halts", which makes totality independent of the source
promise -- so this is a total function of the triple, as `14:1556` requires. -/
def balBuild (q t m : ℕ) : Option (ℕ × BalDescriptor) :=
  if 0 < m ∧ 1 ≤ t ∧ t ≤ q then some (balN q t m, balDescriptor q t m) else none

/-- **The parsed-output equation on the success branch** (`14:1560--1565`). -/
theorem balBuild_eq_some {q t m : ℕ} (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q) :
    balBuild q t m = some (balN q t m, balDescriptor q t m) :=
  if_pos ⟨hm, ht, htq⟩

/-- Reserved failure output at `m = 0` -- a rejection probe (`14:1743--1745`). -/
theorem balBuild_eq_none_of_m_zero (q t : ℕ) : balBuild q t 0 = none :=
  if_neg (by simp)

/-- Reserved failure output at `t = 0`, i.e. below the frozen floor `t >= 1`
(`14:1558`) -- a rejection probe. -/
theorem balBuild_eq_none_of_t_zero (q m : ℕ) : balBuild q 0 m = none :=
  if_neg (by simp)

/-- Reserved failure output when `q < t`, i.e. against the frozen `q >= t`
(`14:1558`, `14:1750`) -- a rejection probe. -/
theorem balBuild_eq_none_of_q_lt_t {q t : ℕ} (m : ℕ) (h : q < t) :
    balBuild q t m = none :=
  if_neg fun hc => absurd hc.2.2 (not_le.mpr h)

/-! ## Part 5: the guarded accessor `A_balEntry` (`14:1768--1782`) -/

/-- **The base-`p` digits** `a_r(l) = floor(l / p^r) mod p` (`14:1769--1771`),
with the least nonnegative residue of `14:1779`. -/
def balDigit (p l r : ℕ) : ℕ := l / p ^ r % p

/-- **`eq:literal-balanced-accessor`** (`14:1774--1778`, `\label` at `14:1777`):
`c_{d_bal}(l)(i) = (sum_{r=0}^{t-1} a_r(l) i^r mod p) mod m`.

The frozen text says the machine "applies Horner's rule in `F_p`"; Horner is the
*algorithm*, and the displayed equation is its *value*, which is what the
correctness theorem quantifies over.  The value is reified here, in the frozen
order of reductions: the polynomial sum, then `mod p`, then `mod m`, all least
nonnegative residues (`14:1779`). -/
def balEntryVal (p t m l i : ℕ) : ℕ :=
  (∑ r ∈ Finset.range t, balDigit p l r * i ^ r) % p % m

/-- **`c_{d_bal}` lands in `[m]`** -- the third clause of
`eq:effective-balanced-builder` (`14:1589`, `c_{d_bal} : [N] -> [m]^q`) at the
value level.  Immediate from the final `mod m` of `14:1776`. -/
theorem balEntryVal_lt {m : ℕ} (hm : 0 < m) (p t l i : ℕ) : balEntryVal p t m l i < m :=
  Nat.mod_lt _ hm

/-- **`A_balEntry`, the guarded accessor** (`14:1768--1782`).

The guard is the frozen check list of `14:1779--1782`: the dependent-context
check of `14:1764--1765` (through `Parses`), then `l < N`, then `i < q`, then
`m > 0` -- "performed before any division or remainder operation", which is why
the arithmetic sits inside the `then` branch and nowhere else.  On a failed check
the machine writes the reserved failure output (`14:1743--1745`), modelled by
`none`; that value is *distinct* from every legal entry, which is the whole
reason the descriptor is not encoded as a bare numeral. -/
def balEntry (q t m N : ℕ) (d : BalDescriptor) (l i : ℕ) : Option ℕ :=
  if d.Parses q t m N ∧ l < N ∧ i < q ∧ 0 < m then some (balEntryVal d.p t m l i)
  else none

/-- The success branch of `A_balEntry` (`14:1774--1778`). -/
theorem balEntry_eq_some {q t m N : ℕ} {d : BalDescriptor} {l i : ℕ}
    (hd : d.Parses q t m N) (hl : l < N) (hi : i < q) (hm : 0 < m) :
    balEntry q t m N d l i = some (balEntryVal d.p t m l i) :=
  if_pos ⟨hd, hl, hi, hm⟩

/-- Guard probe: an out-of-range index `l >= N` returns the reserved failure
output (`14:1780`). -/
theorem balEntry_eq_none_of_index {q t m N : ℕ} {d : BalDescriptor} {l : ℕ} (i : ℕ)
    (h : N ≤ l) : balEntry q t m N d l i = none :=
  if_neg fun hc => absurd hc.2.1 (not_lt.mpr h)

/-- Guard probe: an out-of-range coordinate `i >= q` returns the reserved failure
output (`14:1780`). -/
theorem balEntry_eq_none_of_coord {q t m N : ℕ} {d : BalDescriptor} (l : ℕ) {i : ℕ}
    (h : q ≤ i) : balEntry q t m N d l i = none :=
  if_neg fun hc => absurd hc.2.2.1 (not_lt.mpr h)

/-- Guard probe: `m = 0` returns the reserved failure output, before any
remainder operation is attempted (`14:1781`). -/
theorem balEntry_eq_none_of_m_zero (q t N : ℕ) (d : BalDescriptor) (l i : ℕ) :
    balEntry q t 0 N d l i = none :=
  if_neg (by simp)

/-- Guard probe: a descriptor failing the dependent-context check is rejected
before the arithmetic (`14:1779--1781`). -/
theorem balEntry_eq_none_of_bad_descriptor {q t m N : ℕ} {d : BalDescriptor}
    (l i : ℕ) (h : ¬ d.Parses q t m N) : balEntry q t m N d l i = none :=
  if_neg fun hc => absurd hc.1 h

/-- Every value the accessor returns lies in `[m]` (`14:1589`). -/
theorem balEntry_mem {q t m N : ℕ} {d : BalDescriptor} {l i v : ℕ} (hm : 0 < m)
    (h : balEntry q t m N d l i = some v) : v < m := by
  unfold balEntry at h
  split at h
  · cases h
    exact balEntryVal_lt hm _ _ _ _
  · exact absurd h (by simp)

/-! ## Part 6: the typed family `c_{d_bal} : [N] -> [m]^q` (`14:1589`) -/

/-- **`c_{d_bal} : [N] -> [m]^q`** -- the third clause of
`eq:effective-balanced-builder` (`14:1589`), as a *type*, over the zero-based
slots of `conv:finite-slots`.  The values are the literal accessor
`eq:literal-balanced-accessor` at the scanned prime; the codomain proof is
`balEntryVal_lt`.

`14:1596--1597` ("Repeated indices in `[N]` remain distinct even if their
represented columns are equal") is structural here: the index type is `Fin N`,
so two indices are distinct as indices whatever their images.  That sentence is
already banked as `StageTwoRelaxed.stageTwo_repeated_columns_stay_distinct` and
is not restated. -/
def balFamily (q t m : ℕ) (hm : 0 < m) : Fin (balN q t m) → Fin q → Fin m :=
  fun l i => ⟨balEntryVal (balPrime q t m) t m (l : ℕ) (i : ℕ),
    balEntryVal_lt hm _ _ _ _⟩

/-- The typed family's underlying value is the literal accessor. -/
theorem balFamily_val (q t m : ℕ) (hm : 0 < m) (l : Fin (balN q t m)) (i : Fin q) :
    (balFamily q t m hm l i : ℕ) = balEntryVal (balPrime q t m) t m (l : ℕ) (i : ℕ) :=
  rfl

/-- **"the descriptor does not contain an expanded list of `Nq` values"**
(`14:1765--1766`).  Every one of the `N q` entries is recovered from the
descriptor's two fields together with the recorded context, so the two-field
record really is all the builder writes. -/
theorem balFamily_from_descriptor (q t m : ℕ) (hm : 0 < m)
    (l : Fin (balN q t m)) (i : Fin q) :
    (balFamily q t m hm l i : ℕ)
      = balEntryVal (balDescriptor q t m).p t m (l : ℕ) (i : ℕ) :=
  rfl

/-- **The entry equation of `14:1570--1582`**: the guarded machine
`A_balEntry`, run on the builder's own output context
`(q,t,m,N,d_bal,l,i)`, returns exactly the typed family's value at `(l,i)`.
This is the round trip between the machine layer and the mathematical family. -/
theorem balEntry_at_builder_output {q t m : ℕ} (hm : 0 < m)
    {l i : ℕ} (hl : l < balN q t m) (hi : i < q) :
    balEntry q t m (balN q t m) (balDescriptor q t m) l i
      = some ((balFamily q t m hm ⟨l, hl⟩ ⟨i, hi⟩ : Fin m) : ℕ) :=
  balEntry_eq_some (balBuild_output_parses q t m) hl hi hm

/-- The accessor evaluated at the first coordinate.  With `i = 0` every
monomial `a_r(l) i^r` with `r >= 1` vanishes and only the constant digit
`a_0(l) = l mod p` survives, so the entry is `l mod p mod m`.  General; used by
the non-degeneracy lemma below, and it is also the smallest nontrivial check
that the digit extraction and the polynomial evaluation were transcribed in the
right order. -/
theorem balEntryVal_at_zero (p t m l : ℕ) (ht : 0 < t) :
    balEntryVal p t m l 0 = l % p % m := by
  have h0 : (0 : ℕ) ∈ Finset.range t := Finset.mem_range.mpr ht
  have hsum : (∑ r ∈ Finset.range t, balDigit p l r * 0 ^ r)
      = balDigit p l 0 * 0 ^ 0 :=
    Finset.sum_eq_single_of_mem 0 h0 (by
      intro b _ hb
      simp [zero_pow hb])
  rw [balEntryVal, hsum]
  simp [balDigit, Nat.mod_mod_of_dvd]

/-- The typed family at the first coordinate. -/
theorem balFamily_at_zero_coord (q t m : ℕ) (hm : 0 < m) (ht : 0 < t) (hq : 0 < q)
    (l : Fin (balN q t m)) :
    (balFamily q t m hm l ⟨0, hq⟩ : ℕ) = (l : ℕ) % balPrime q t m % m := by
  rw [balFamily_val]
  exact balEntryVal_at_zero _ _ _ _ ht

/-- **NON-DEGENERACY (`LANE-GATE 3`).**  At every legal parameter triple with a
non-degenerate value carrier, the built family takes two different values at the
*same* coordinate: indices `0` and `1` disagree at coordinate `0`.

A constant family is the trivial witness that the balanced-family clause of
`14:1591--1592` exists to exclude, and
`PublicRecords.levelParams_admits_unbalanced_family` already banks that a
constant family is a perfectly legal `Pi`.  So the content here is that *this*
builder's output is not that witness.  The statement is general: no parameter is
instantiated and the prime scan is never evaluated. -/
theorem balFamily_not_constant (q t m : ℕ) [Nontrivial (Fin m)] (hm : 0 < m)
    (ht : 0 < t) (hq : 0 < q) :
    balFamily q t m hm ⟨0, balN_pos q t m⟩ ⟨0, hq⟩
      ≠ balFamily q t m hm ⟨1, one_lt_balN q t m ht⟩ ⟨0, hq⟩ := by
  have hm2 : 1 < m := by
    have := Fintype.one_lt_card (α := Fin m)
    simpa using this
  have hp2 : 2 ≤ balPrime q t m := two_le_balPrime q t m
  intro hcontra
  have hval : ((balFamily q t m hm ⟨0, balN_pos q t m⟩ ⟨0, hq⟩ : Fin m) : ℕ)
      = ((balFamily q t m hm ⟨1, one_lt_balN q t m ht⟩ ⟨0, hq⟩ : Fin m) : ℕ) := by
    rw [hcontra]
  rw [balFamily_at_zero_coord q t m hm ht hq,
    balFamily_at_zero_coord q t m hm ht hq] at hval
  have h1p : (1 : ℕ) % balPrime q t m = 1 := Nat.mod_eq_of_lt (by omega)
  have h1m : (1 : ℕ) % m = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [Nat.zero_mod, h1p, h1m] at hval
  omega

/-! ## Part 7: the storage identification (`14:1621--1632`) -/

/-- **`c_{2,i}(l)(r) = e_i(c_{d_i}(l)(r))`** -- the family "actually stored in
the parameter record" (`14:1629--1631`).

`e_i` is the canonical increasing equivalence `[m_{1,i}] -> Rows(M_1^{(i)})` of
`14:1626`, consumed by pin as the banked
`IteratedCanonicalChaining.canonEquiv` (`12:93--104`); `canonOrderEquiv_unique`
banks that it is the unique increasing one, so nothing here is a choice.  The
carrier is general, at its own cardinality, exactly as `14:1626` states it. -/
noncomputable def storedFamily (q t m : ℕ) (hm : 0 < m) (X₁ : Type*) [Fintype X₁]
    [LinearOrder X₁] (h : Fintype.card X₁ = m) :
    Fin (balN q t m) → Fin q → X₁ :=
  fun l r => canonEquiv X₁ h (balFamily q t m hm l r)

/-- **`Pi_i = (K_*, N_{2,i}, c_{2,i})`** -- `14:1632` verbatim, as the banked
record `PublicRecords.LevelParams` (`def:level-parameters`, `05:172--190`).

This is where `N_2`'s canonical chain closes: the record's `N_2` is no longer a
free positive integer but the literal output `balN` of the builder
`14:1749--1763`, and its structural positivity is `balN_pos`, i.e. *derived*
rather than assumed.  Nothing is added to the banked record and no field is
introduced. -/
noncomputable def storedParams (K : LevelConfig) (q t m : ℕ) (hm : 0 < m)
    (X₁ : Type*) [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m) :
    LevelParams X₁ q where
  K := K
  N₂ := balN q t m
  N₂pos := balN_pos q t m
  c₂ := storedFamily q t m hm X₁ h

/-- The stored record's configuration is the one it was built at (`14:1632`). -/
theorem storedParams_K (K : LevelConfig) (q t m : ℕ) (hm : 0 < m) (X₁ : Type*)
    [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m) :
    (storedParams K q t m hm X₁ h).K = K := rfl

/-- **`N_{2,i}` is the builder's literal output** (`14:1622--1624`, "the literal output
`(N_{2,i}, d_i)` of `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`").  The record field is
the evaluated definitional chain `xBal -> balPrime -> balN`, not an assigned
value. -/
theorem storedParams_N₂ (K : LevelConfig) (q t m : ℕ) (hm : 0 < m) (X₁ : Type*)
    [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m) :
    (storedParams K q t m hm X₁ h).N₂ = balN q t m := rfl

/-- The stored family is the reindexed accessor, definitionally (`14:1630`). -/
theorem storedParams_c₂ (K : LevelConfig) (q t m : ℕ) (hm : 0 < m) (X₁ : Type*)
    [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m)
    (l : Fin (balN q t m)) (r : Fin q) :
    (storedParams K q t m hm X₁ h).c₂ l r
      = canonEquiv X₁ h (balFamily q t m hm l r) := rfl

/-- **The builder's output is the size the record reports.**  Composed with
`balN_le_bBal`, this is the `02:521--524` / `06:2124--2130` envelope clause
`0 < N_2 <= B_bal(q_2,t_2,|Rows(M_1)|)` holding at the *stored* record rather
than at an assumed one. -/
theorem storedParams_N₂_le_bBal (K : LevelConfig) (q t m : ℕ) (hm : 0 < m)
    (X₁ : Type*) [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m)
    (ht : 0 < t) :
    0 < (storedParams K q t m hm X₁ h).N₂ ∧
      (storedParams K q t m hm X₁ h).N₂ ≤ bBal q t m :=
  ⟨balN_pos q t m, balN_le_bBal q t m ht⟩

/-- **NON-DEGENERACY of the stored record.**  The family actually stored in `Pi`
is not constant either: reindexing along an equivalence cannot collapse the two
values `balFamily_not_constant` separates.  This is the statement that keeps the
storage identification from being vacuous -- a constant stored family is a legal
`Pi` (`PublicRecords.levelParams_admits_unbalanced_family`), and the record this
constructor produces is not one. -/
theorem storedFamily_not_constant (q t m : ℕ) (hm : 0 < m) (ht : 0 < t) (hq : 0 < q)
    (X₁ : Type*) [Fintype X₁] [LinearOrder X₁] [Nontrivial X₁]
    (h : Fintype.card X₁ = m) :
    storedFamily q t m hm X₁ h ⟨0, balN_pos q t m⟩ ⟨0, hq⟩
      ≠ storedFamily q t m hm X₁ h ⟨1, one_lt_balN q t m ht⟩ ⟨0, hq⟩ := by
  have hcard : 1 < m := by
    rw [← h]
    exact Fintype.one_lt_card
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hcard
  intro hcontra
  exact balFamily_not_constant q t m hm ht hq ((canonEquiv X₁ h).injective hcontra)

/-! ## Part 8: the balancedness clause `14:1591--1592`, by the frozen argument
`14:1784--1810`

**Placement decision (`cc-t7h`), stated rather than assumed.**  This half is
*appended to this module* rather than given a new one.  Three facts decide it.
(i) The deferred ledger row `S5-BALANCED-FAMILY` names the exact statement
`NPCC.IsBalancedFamily t (balFamily q t m hm) (1 / (100 * t))`, and `balFamily`
is this module's own `def` -- a new module would have to import this one and
would state its single deliverable about an object it does not own.
(ii) The two arithmetic inputs the frozen argument opens with, `q <= p`
(`14:1785--1786`) and `m/p <= 1/(1000t^2)` (`14:1799`), were landed *here* at
`cc-t7g` explicitly as prerequisites for this proof; they are consumed BY PIN
below (`q_le_balPrime`, `m_le_balPrime_ratio`) and are not restated.
(iii) The frozen anchor is the *same proof paragraph*: `14:1749--1782` (already
traced here) and `14:1784--1810` are one uninterrupted proof of one theorem, and
splitting a single frozen paragraph across two Lean modules would put half a
proof on each side of an import boundary for no audience gain.  No new import is
added: `NPCC.IsBalancedFamily` and Mathlib's finite-field, polynomial and
`Finset`-counting surface are already in this module's import closure.

**What the frozen argument says, and what each layer below transcribes.**

* `14:1784--1786`: "take distinct coordinates `i_1,...,i_r`, where `r <= t`.
  They remain distinct in `F_p` because `q <= p`."  Below: the nodes `x` of the
  deliverable are the increasing enumeration of `J` cast into `ZMod p`, and
  `q_le_balPrime` (banked, consumed by pin) is exactly what makes that cast
  injective.
* `14:1786--1791`: "The corresponding `r`-row Vandermonde map
  `F_p^t -> F_p^r` is surjective, and every fibre has exactly `p^{t-r}`
  elements.  Hence the field evaluations are uniform on `F_p^r`."  Below:
  `vandEval` is that map, `vandEval_surjective` is the surjectivity, and
  `card_vandEval_fiber` is the uniformity.  **The fibre size `p^{t-r}` is not
  computed**, deliberately: `card_vandEval_preimage_mul` proves the identity
  `count * p^r = (prod of class sizes) * p^t`, in which the common fibre size
  cancels.  That is strictly what the counting needs, it avoids a natural
  subtraction `t - r`, and nothing downstream reads the fibre size.
* `14:1792--1795`: "For any residue modulo `m`, its number of representatives
  in `[p]` is either `floor(p/m)` or `ceil(p/m)`."  Below: `residue_card_upper`
  and `residue_card_lower` bound that count in the two-sided integer form
  `p - m <= m * n <= p + m`, which is the same statement cleared of division
  and is the form the real estimates consume.  The floor/ceiling pair is a
  *description* of that count; the two inequalities are its content.
* `14:1794--1798`: "Relative to `p/m`, each factor is therefore in
  `[1-m/p, 1+m/p]`", and `14:1799`, "Here `m/p <= 1/(1000t^2)`.  Below: the
  ratio is the banked `m_le_balPrime_ratio`, consumed by pin.
* `14:1799--1808`: Bernoulli `(1-m/p)^r >= 1 - rm/p >= 1 - 1/(100t)`, and the
  geometric tail `(1+m/p)^r <= 1/(1-rm/p) <= 1 + 2rm/p <= 1 + 1/(100t)`.
  Below: `balanced_ratio_bound`, in the frozen order -- Bernoulli through
  Mathlib's `one_add_mul_le_pow`, then the tail through
  `(1-x)^r (1+x)^r = (1-x^2)^r <= 1` together with the same Bernoulli bound,
  which is the division-free form of `(1+x)^r <= 1/(1-rx)`.
* `14:1809--1810`: "Multiplying the `r` representative counts proves the exact
  relative probability interval in `def:balanced-family`."  Below:
  `balFamily_isBalanced`, against the vendored predicate
  `NPCC.IsBalancedFamily` (`vendor/npc-cc/NPCC/Relaxed.lean:19`, the Lean home
  of `def:balanced-family` at `03:277--289`), which is **consumed and not
  re-reified**; `vendor/npc-cc` is untouched.

**Reader counterpart.**  `lem:paper-explicit-balanced-family`
(`routes/parameterized-np/reader-facing/sections/C-effectivity-details.tex`,
label line `32`, statement `31--38` and `43--46`, proof `48--76`) -- the same
item this module already claims, with the display `39--42` carved out.  The
lines this Part lands against are `:62--69`, opened first-hand: "For every set
of at most `t` distinct coordinates, the Vandermonde map is uniform over `F_p`
on those coordinates.  A reader symbol `a in [m] = {1,...,m}` represents the
zero-based residue `a-1`.  For each prescribed symbol, the field elements whose
residue modulo `m` is `a-1` form a class of size either `floor(p/m)` or
`ceil(p/m)`.  The choice of `p` therefore puts every prescribed pattern
probability within a multiplicative factor `1 +- 1/(100t)` of `m^{-r}`."  Those
lines are already inside the claimed interval `48--76`, so **no new reader item
is claimed and none is invented**; the module's existing reader row stands
unchanged except that its "still unaligned" tail is now discharged.  The reader
is one-based and prints the residue as `a-1`; this Part is zero-based per
`conv:finite-slots`, which is the same recorded transport the module's header
already carries for `balDigit` and `balEntryVal`, not a divergence.

**Statement pole.**  The deliverable is a named-def claim about the pinned
construction, not an existential, so there is no trivial witness to exclude at
the deliverable itself.  The *predicate* does allow a trivial witness --
a constant family -- and `constant_family_not_isBalanced` proves in one
declaration that the constant family fails this exact accuracy at every legal
`(q,t,m)` with a non-degenerate alphabet.  Together with the banked
`balFamily_not_constant`, and with
`PublicRecords.levelParams_admits_unbalanced_family` (which banks that a
constant family is nevertheless a legal `Pi`), that is the full statement-pole
account: the clause is a real constraint, and the built family meets it.

**Numeral screen for Part 8** (statement literals only; definition bodies
included).  `vandEval`, `finZModEquiv`, `balN_eq_pow`, `balCoeffEquiv`,
`balCoeffEquiv_apply`, `balEntryVal_eq_zmod_val`, `card_residue_zmod`,
`residue_card_upper`, `vandEval_add`, `vandEval_sub`,
`isBalancedFamily_congr_equiv` and the two instances carry **no** statement
literal.  The rest:

* `vandEval_zero` -- `0`, `0`.  CANONICAL-FORM: the additive identity of the
  source's own `F_p^t` and `F_p^r` (`14:1788--1790`).
* `vandEval_surjective` -- `0`.  The floor `t >= 1` of `14:1558`/`14:1750`.
* `card_vandEval_fiber` -- `0`.  CANONICAL-FORM, the `F_p^r` zero of
  `14:1790`; the base point of the fibre comparison.
* `card_vandEval_preimage_mul` -- `0`.  The floor `t >= 1`.
* `residue_card_lower` -- `0`.  The accessor guard `m > 0` of `14:1781`.
* `balanced_ratio_bound` -- `0`, `0`, `1`, `1000`, `2`, `1`, `1`, `100`.  The
  two `0`s are the guards `t >= 1` and `m > 0`; `1`, `1000` and `2` are the
  canonical displayed expression `m/p <= 1/(1000t^2)` of `14:1799`; the next
  `1` is the numerator of the reference value `1/m^r`, i.e. `m^{-r}`, the
  quantity `14:1809--1810` compares against; and `1` and `100` are the accuracy
  `1/(100t)` printed at `14:1592`.  (**Verify-seat correction, `cc-t7h`:** the
  authored row listed seven literals and omitted the `1/m^r` numerator.)
* `balFamily_isBalanced` -- `0`, `1`, `1`, `100`.  The guards `0 < m` and
  `1 <= t` (`14:1557--1558`), then the accuracy `1/(100t)` of `14:1592`.
* `storedFamily_isBalanced` -- `0`, `1`, `1`, `100`.  As the previous row; the
  family is the stored `c_{2,i}` of `14:1629--1631`.
* `constant_family_not_isBalanced` -- `0`, `0`, `1`, `1`, `100`.  The guards
  `t >= 1`, `q >= 1` and the non-degenerate alphabet `1 < m`, then the same
  accuracy `1/(100t)`.  This is a *rejection* statement: it claims no legality
  and instantiates no parameter.
* `balFamily_isBalanced_nondegenerate` -- `1`, `2`, `1`, `2`, `1`, `100`, `1`.
  (**Verify-seat correction, `cc-t7h`:** the authored row listed six literals
  and omitted the leading `1`, which is the `t` argument of
  `NPCC.IsBalancedFamily` itself, not part of the `balFamily` triple.)
  **BEYOND-PAPER AUDIT** (labelled as such in its own docstring): the triple
  `(q,t,m) = (2,1,2)` is a point the frozen paper never visits, chosen only to
  exhibit that the deliverable's hypothesis bundle is satisfiable at a
  non-degenerate alphabet.  It is strictly weaker evidence than the paper's own
  application point and is not a substitute for it.

**Binder-provenance table for Part 8.**

* `p` (generic sections) -- GENUINELY-FREE generic arithmetic abstraction, the
  same disposition the module's header already records for `balDigit`'s `p`:
  the Vandermonde and residue layers are stated for an arbitrary prime so that
  the deliverable substitutes the DEFINED `balPrime q t m` at the call site.
  In no generic lemma is a free `p` used as construction data.
* `t` -- GENUINELY-FREE, `14:1557--1558` ("positive integers `q,t,m` with
  `q >= t >= 1`") and `14:1750`.
* `r` -- GENUINELY-FREE at the generic sites, and it is the source's own `r`:
  `14:1784--1785` takes "distinct coordinates `i_1,...,i_r`, where `r <= t`",
  and `03:279--281` quantifies `def:balanced-family` over every `J ⊆ [q]` with
  `|J| <= t`.  At the deliverable it is **pinned** to `J.card`, never chosen.
* `x : Fin r → ZMod p` with `hx : Function.Injective x` -- the source's
  `i_1,...,i_r` and its "they remain distinct in `F_p`" (`14:1785--1786`),
  free in the generic lemmas.  At the deliverable it is **pinned** to the
  increasing enumeration `Finset.orderIsoOfFin` of `J`, cast into `ZMod p`;
  injectivity is derived from the banked `q_le_balPrime`, never assumed.
* `T : Fin r → Finset (ZMod p)` -- the prescribed residue classes of
  `14:1793--1794`, free in the counting lemma because that lemma is a pure
  fibre count.  At the deliverable it is **pinned** to
  `{v | v.val % m = a γ}`, i.e. the class of the prescribed pattern symbol.
* `c` (residue lemmas) -- the prescribed residue of `14:1793`; **pinned** at
  the call to `(a γ : ℕ)`, with `hc : c < m` supplied by `Fin.isLt`.
* `n : Fin r → ℕ` and `cnt` (`balanced_ratio_bound`) -- NOT free assignments:
  the lemma is the arithmetic core with its three inputs as explicit
  hypotheses, and at the single call site `n` is **pinned** to `(T j).card`
  and `cnt` to the filter cardinality by `card_vandEval_preimage_mul`.
* `Y`, `Z`, `φ` (`isBalancedFamily_congr_equiv`) -- a general value-carrier
  transport of the vendored predicate, distinct from the vendored
  `NPCC.IsBalancedFamily.projection` (which transports *coordinates* along an
  injection).  **Pinned** at `storedFamily_isBalanced` to the banked
  `canonEquiv`, i.e. the `e_i` of `14:1626`.
* `X₁` with `[Fintype X₁] [LinearOrder X₁]` and `h : Fintype.card X₁ = m` --
  the same GENUINELY-FREE row carrier the module's header already records for
  `storedFamily`, at its own cardinality per `14:1626`.
* `q`, `L`, `m`, `t`, `c₀` (`constant_family_not_isBalanced`) -- rejection-only
  binders, universally quantified over the region where the claim is a
  *refutation*.  They claim no legality.
* `J`, `a`, `γ`, `l`, `j`, `s` -- source-quantified: `J ⊆ [q]` with `|J| <= t`
  and the pattern `a` are `def:balanced-family`'s own quantifiers
  (`03:279--281`); `l in [N]`, `i in [q]` and `0 <= r < t` are
  `14:1570--1571`, `14:1773` and `14:1771`.  Zero-based per
  `conv:finite-slots`.

Zero source-defined binders remain free.  No new structure is introduced, so no
new field enters. -/

/-- `balPrime q t m` is nonzero, as an instance, so that `ZMod (balPrime q t m)`
is a `Fintype` in the counting below.  Derived from `two_le_balPrime`; no value
is assigned. -/
instance balPrimeNeZero (q t m : ℕ) : NeZero (balPrime q t m) :=
  ⟨by have := two_le_balPrime q t m; omega⟩

/-- `balPrime q t m` is prime, as an instance, so that `ZMod (balPrime q t m)`
is the field `F_p` the frozen argument works in (`14:1788--1790`).  This is the
banked `balPrime_prime` in instance position; it re-proves nothing. -/
instance balPrimeFact (q t m : ℕ) : Fact (Nat.Prime (balPrime q t m)) :=
  ⟨balPrime_prime q t m⟩

section Vandermonde

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- **The `r`-row Vandermonde map `F_p^t -> F_p^r`** of `14:1786--1790`.

At nodes `x_1,...,x_r` it sends a coefficient vector `a` to the vector of
evaluations `sum_{s<t} a_s x_j^s`.  This is the value of the same Horner
evaluation `eq:literal-balanced-accessor` performs, read inside `F_p` rather
than as a least nonnegative residue; `balEntryVal_eq_zmod_val` below is the
bridge between the two readings. -/
def vandEval {t r : ℕ} (x : Fin r → ZMod p) (a : Fin t → ZMod p) : Fin r → ZMod p :=
  fun j => ∑ s : Fin t, a s * x j ^ (s : ℕ)

/-- **Aux 1 (identity).**  The zero coefficient vector evaluates to zero at
every node. -/
theorem vandEval_zero {t r : ℕ} (x : Fin r → ZMod p) : vandEval (t := t) x 0 = 0 := by
  funext j
  simp [vandEval]

/-- **Aux 2 (additivity).**  The map is additive, which is what makes its fibres
cosets of a single set and hence equinumerous. -/
theorem vandEval_add {t r : ℕ} (x : Fin r → ZMod p) (a b : Fin t → ZMod p) :
    vandEval x (a + b) = vandEval x a + vandEval x b := by
  funext j
  simp only [vandEval, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- **Aux 2' (additivity, subtractive form).**  Used directly by the fibre
bijection below. -/
theorem vandEval_sub {t r : ℕ} (x : Fin r → ZMod p) (a b : Fin t → ZMod p) :
    vandEval x (a - b) = vandEval x a - vandEval x b := by
  funext j
  simp only [vandEval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **"The corresponding `r`-row Vandermonde map `F_p^t -> F_p^r` is
surjective"** (`14:1786--1791`), under the frozen side conditions `r <= t` and
"they remain distinct in `F_p`".

The proof is the classical one and is done through Mathlib's Lagrange
interpolation rather than a determinant: for prescribed values `y` at the `r`
distinct nodes, `Lagrange.interpolate` supplies a polynomial of degree `< r`,
hence `natDegree < t`, whose first `t` coefficients are a preimage.  That the
nodes are distinct is the hypothesis `hx`, which at the deliverable comes from
`q <= p` (`14:1785--1786`) and is not assumed there. -/
theorem vandEval_surjective {t r : ℕ} (ht : 0 < t) (hrt : r ≤ t)
    (x : Fin r → ZMod p) (hx : Function.Injective x) :
    Function.Surjective (vandEval (p := p) (t := t) x) := by
  classical
  intro y
  set P : Polynomial (ZMod p) :=
    Lagrange.interpolate (Finset.univ : Finset (Fin r)) x y with hPdef
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin r)) := Set.injOn_of_injective hx
  have hdeg : P.degree < ((Finset.univ : Finset (Fin r)).card : ℕ) :=
    Lagrange.degree_interpolate_lt (v := x) y hinj
  have hcard : (Finset.univ : Finset (Fin r)).card = r := by simp
  rw [hcard] at hdeg
  have hnat : P.natDegree < t := by
    by_cases h0 : P = 0
    · rw [h0]; simpa using ht
    · exact lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdeg) hrt
  refine ⟨fun s => P.coeff (s : ℕ), ?_⟩
  funext j
  have hev : P.eval (x j) = y j :=
    Lagrange.eval_interpolate_at_node (v := x) y hinj (Finset.mem_univ j)
  rw [← hev, Polynomial.eval_eq_sum_range' hnat]
  simp only [vandEval]
  exact Fin.sum_univ_eq_sum_range (fun k => P.coeff k * x j ^ k) t

/-- **"every fibre has exactly `p^{t-r}` elements"** (`14:1790--1791`), in the
form the counting actually uses: **all fibres are equinumerous**.

Translation from a surjective fibre to the fibre over `0` is `a ↦ a - a_0`,
which is a bijection by `vandEval_sub` and `vandEval_add`.  The frozen size
`p^{t-r}` is deliberately not computed: it cancels in
`card_vandEval_preimage_mul`, and computing it would introduce a natural
subtraction that the frozen argument never needs. -/
theorem card_vandEval_fiber {t r : ℕ} [NeZero p]
    (x : Fin r → ZMod p) (hsurj : Function.Surjective (vandEval (p := p) (t := t) x))
    (y : Fin r → ZMod p) :
    (Finset.univ.filter (fun a : Fin t → ZMod p => vandEval x a = y)).card
      = (Finset.univ.filter (fun a : Fin t → ZMod p => vandEval x a = 0)).card := by
  classical
  obtain ⟨a₀, ha₀⟩ := hsurj y
  refine Finset.card_nbij' (fun a => a - a₀) (fun b => b + a₀) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha ⊢
    rw [vandEval_sub, ha, ha₀, sub_self]
  · intro b hb
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hb ⊢
    rw [vandEval_add, hb, ha₀, zero_add]
  · intro a _; simp
  · intro b _; simp

/-- **"Hence the field evaluations are uniform on `F_p^r`"** (`14:1791--1792`),
as an exact integer identity.

For any prescribed sets `T_1,...,T_r` of admissible field values, the number of
coefficient vectors whose evaluations land in them satisfies
`count * p^r = (prod_j |T_j|) * p^t`.  This is "uniform" cleared of division:
dividing by `p^t` gives `count / p^t = (prod_j |T_j|) / p^r`, which is the
statement the probability interval consumes.  The common fibre size cancels and
is never named. -/
theorem card_vandEval_preimage_mul {t r : ℕ} [NeZero p] (ht : 0 < t) (hrt : r ≤ t)
    (x : Fin r → ZMod p) (hx : Function.Injective x) (T : Fin r → Finset (ZMod p)) :
    (Finset.univ.filter (fun a : Fin t → ZMod p => ∀ j, vandEval x a j ∈ T j)).card * p ^ r
      = (∏ j, (T j).card) * p ^ t := by
  classical
  have hsurj := vandEval_surjective (p := p) ht hrt x hx
  set F : ℕ := (Finset.univ.filter (fun a : Fin t → ZMod p => vandEval x a = 0)).card with hF
  set S : Finset (Fin r → ZMod p) := Fintype.piFinset T with hS
  have hcount :
      (Finset.univ.filter (fun a : Fin t → ZMod p => ∀ j, vandEval x a j ∈ T j)).card
        = S.card * F := by
    have hmaps : ∀ a ∈ Finset.univ.filter
        (fun a : Fin t → ZMod p => ∀ j, vandEval x a j ∈ T j), vandEval x a ∈ S := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact Fintype.mem_piFinset.mpr ha
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ y ∈ S,
        ((Finset.univ.filter (fun a : Fin t → ZMod p => ∀ j, vandEval x a j ∈ T j)).filter
          (fun a => vandEval x a = y)).card = F := by
      intro y hy
      have hset : ((Finset.univ.filter
            (fun a : Fin t → ZMod p => ∀ j, vandEval x a j ∈ T j)).filter
            (fun a => vandEval x a = y))
          = Finset.univ.filter (fun a : Fin t → ZMod p => vandEval x a = y) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          intro j
          rw [h]
          exact Fintype.mem_piFinset.mp hy j
      rw [hset, hF]
      exact card_vandEval_fiber (p := p) x hsurj y
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  have htotal : p ^ t = p ^ r * F := by
    have hmaps : ∀ a ∈ (Finset.univ : Finset (Fin t → ZMod p)),
        vandEval x a ∈ (Finset.univ : Finset (Fin r → ZMod p)) := by
      intro a _; exact Finset.mem_univ _
    have h1 : (Finset.univ : Finset (Fin t → ZMod p)).card = p ^ t := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have h2 : (Finset.univ : Finset (Fin r → ZMod p)).card = p ^ r := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have h3 := Finset.card_eq_sum_card_fiberwise hmaps
    have hfib : ∀ y ∈ (Finset.univ : Finset (Fin r → ZMod p)),
        ((Finset.univ : Finset (Fin t → ZMod p)).filter
          (fun a => vandEval x a = y)).card = F := by
      intro y _
      rw [hF]
      exact card_vandEval_fiber (p := p) x hsurj y
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, h2] at h3
    rw [← h1, h3]
  have hScard : S.card = ∏ j, (T j).card := by
    rw [hS, Fintype.card_piFinset]
  rw [hcount, hScard, htotal]
  ring

end Vandermonde

/-! ### The representative counts of `14:1792--1795` -/

/-- **"its number of representatives in `[p]` is either `floor(p/m)` or
`ceil(p/m)`"** (`14:1793--1795`), upper half, cleared of division:
`m * n <= p + m`, i.e. `n <= p/m + 1`.

Proved by injecting the class into `[(p-1)/m + 1]` along `v ↦ v / m`, which is
injective on a fixed residue class because `v = m (v / m) + v mod m`. -/
theorem residue_card_upper (p m c : ℕ) :
    m * (((Finset.range p).filter (fun v => v % m = c)).card) ≤ p + m := by
  classical
  have hle : ((Finset.range p).filter (fun v => v % m = c)).card ≤ (p - 1) / m + 1 := by
    have hc := Finset.card_le_card_of_injOn (f := fun v => v / m)
      (s := (Finset.range p).filter (fun v => v % m = c))
      (t := Finset.range ((p - 1) / m + 1)) ?_ ?_
    · simpa using hc
    · intro v hv
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hv
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : v ≤ p - 1))
    · intro v hv w hw hvw
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hv hw
      have hvw' : v / m = w / m := hvw
      have hv' : m * (v / m) + v % m = v := Nat.div_add_mod v m
      have hw' : m * (w / m) + w % m = w := Nat.div_add_mod w m
      have heq : m * (v / m) = m * (w / m) := by rw [hvw']
      omega
  have hdiv : m * ((p - 1) / m) ≤ p - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have h1 : m * (((Finset.range p).filter (fun v => v % m = c)).card)
      ≤ m * ((p - 1) / m + 1) := Nat.mul_le_mul_left m hle
  have h2 : m * ((p - 1) / m + 1) = m * ((p - 1) / m) + m := by ring
  omega

/-- **The same count** (`14:1793--1795`), lower half, cleared of division:
`p <= m * n + m`, i.e. `n >= p/m - 1`.

Proved by injecting `[(p-1-c)/m + 1]` into the class along `k ↦ c + m k`, which
lands inside `[p]` exactly because `m ((p-1-c)/m) <= p-1-c`. -/
theorem residue_card_lower (p m c : ℕ) (hm : 0 < m) (hc : c < m) (hcp : c < p) :
    p ≤ m * (((Finset.range p).filter (fun v => v % m = c)).card) + m := by
  classical
  have hge : (p - 1 - c) / m + 1 ≤ ((Finset.range p).filter (fun v => v % m = c)).card := by
    have hcc := Finset.card_le_card_of_injOn (f := fun k => c + m * k)
      (s := Finset.range ((p - 1 - c) / m + 1))
      (t := (Finset.range p).filter (fun v => v % m = c)) ?_ ?_
    · simpa using hcc
    · intro k hk
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      have hk' : k ≤ (p - 1 - c) / m := by omega
      have hmk : m * k ≤ m * ((p - 1 - c) / m) := Nat.mul_le_mul_left m hk'
      have hdiv : m * ((p - 1 - c) / m) ≤ p - 1 - c := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    · intro k1 _ k2 _ hk
      have hk' : c + m * k1 = c + m * k2 := hk
      have hmm : m * k1 = m * k2 := by omega
      exact Nat.eq_of_mul_eq_mul_left hm hmm
  have hmul : m * ((p - 1 - c) / m + 1)
      ≤ m * (((Finset.range p).filter (fun v => v % m = c)).card) := Nat.mul_le_mul_left m hge
  have hexp : m * ((p - 1 - c) / m + 1) = m * ((p - 1 - c) / m) + m := by ring
  have hdm : m * ((p - 1 - c) / m) + (p - 1 - c) % m = p - 1 - c := Nat.div_add_mod (p - 1 - c) m
  have hmod : (p - 1 - c) % m < m := Nat.mod_lt _ hm
  omega

/-- The residue class read inside `F_p` and the residue class read inside `[p]`
have the same cardinality -- the transport between the field side of
`14:1788--1792` and the "representatives in `[p]`" side of `14:1793--1794`.
The bijection is `ZMod.val`, i.e. the least nonnegative residue of `14:1779`. -/
theorem card_residue_zmod (p m c : ℕ) [NeZero p] :
    (Finset.univ.filter (fun v : ZMod p => v.val % m = c)).card
      = ((Finset.range p).filter (fun v => v % m = c)).card := by
  classical
  refine Finset.card_nbij' (fun v => v.val) (fun n => (n : ZMod p)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      Finset.mem_range] at hv ⊢
    exact ⟨ZMod.val_lt v, hv⟩
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      Finset.mem_range] at hn ⊢
    rw [ZMod.val_natCast_of_lt hn.1]
    exact hn.2
  · intro v _
    exact ZMod.natCast_rightInverse v
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
    exact ZMod.val_natCast_of_lt hn.1

/-! ### The two real estimates of `14:1796--1808` -/

/-- **The arithmetic core of `14:1795--1808`.**

Given the exact count identity `cnt * p^r = (prod_j n_j) * p^t`, the two-sided
representative bounds `p - m <= m n_j <= p + m` (the integer form of
"each factor is in `[1-m/p, 1+m/p]`", `14:1796--1798`), and the frozen ratio
`m/p <= 1/(1000t^2)` (`14:1799`), the prescribed pattern probability lies within
`1 +- 1/(100t)` of `m^{-r}`.

The proof follows the frozen order.  Bernoulli (`14:1799--1802`) gives
`(1-x)^r >= 1 - rx >= 1 - 1/(100t)` through Mathlib's `one_add_mul_le_pow` at
`a = -x`.  The geometric tail (`14:1803--1808`) is taken in the division-free
form the frozen chain `(1+x)^r <= 1/(1-rx) <= 1 + 2rx` is equivalent to:
`(1-x)^r (1+x)^r = (1-x^2)^r <= 1` together with `(1-x)^r >= 1 - rx > 0` gives
`(1+x)^r (1-rx) <= 1 <= (1+2rx)(1-rx)`, and `1 - rx > 0` cancels.  Finally
`2rx <= 2/(1000t) <= 1/(100t)`.  Multiplying the `r` representative counts
(`14:1809--1810`) is `Finset.prod_le_prod` against the constant families
`(p-m)` and `(p+m)`. -/
theorem balanced_ratio_bound {p m r t cnt : ℕ} {n : Fin r → ℕ}
    (ht : 0 < t) (hrt : r ≤ t) (hm : 0 < m) (hmp : m ≤ p)
    (hxle : (m : ℝ) / (p : ℝ) ≤ 1 / (1000 * (t : ℝ) ^ 2))
    (hlow : ∀ j, p ≤ m * n j + m) (hhigh : ∀ j, m * n j ≤ p + m)
    (hcnt : cnt * p ^ r = (∏ j, n j) * p ^ t) :
    |(cnt : ℝ) / (p : ℝ) ^ t - 1 / (m : ℝ) ^ r|
      ≤ (1 / (100 * (t : ℝ))) / (m : ℝ) ^ r := by
  have hpn : 0 < p := lt_of_lt_of_le hm hmp
  have hP : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpn
  have hM : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hT : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hT0 : (0:ℝ) < (t:ℝ) := by linarith
  set X : ℝ := (m:ℝ) / (p:ℝ) with hX
  have hX0 : 0 ≤ X := le_of_lt (div_pos hM hP)
  have hXsmall : X ≤ 1 / 1000 := by
    have h1 : (1:ℝ) / (1000 * (t:ℝ)^2) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ (by nlinarith : (0:ℝ) < 1000 * (t:ℝ)^2) (by norm_num : (0:ℝ) < 1000)]
      nlinarith
    linarith [hxle, h1]
  have hrT : (r:ℝ) ≤ (t:ℝ) := by exact_mod_cast hrt
  set W : ℝ := (r:ℝ) * X with hW
  have hW0 : 0 ≤ W := mul_nonneg (Nat.cast_nonneg r) hX0
  have hWb : W ≤ 1 / (1000 * (t:ℝ)) := by
    have h1 : W ≤ (t:ℝ) * (1 / (1000 * (t:ℝ)^2)) := by
      rw [hW]
      exact mul_le_mul hrT hxle hX0 (by linarith)
    have h2 : (t:ℝ) * (1 / (1000 * (t:ℝ)^2)) = 1 / (1000 * (t:ℝ)) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hWs : W ≤ 1 / 1000 := by
    have h : (1:ℝ) / (1000 * (t:ℝ)) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 1000 * (t:ℝ)) (by norm_num : (0:ℝ) < 1000)]
      linarith
    linarith
  have hWeps : W ≤ 1 / (100 * (t:ℝ)) := by
    have h : (1:ℝ) / (1000 * (t:ℝ)) ≤ 1 / (100 * (t:ℝ)) := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 1000 * (t:ℝ))
        (by linarith : (0:ℝ) < 100 * (t:ℝ))]
      linarith
    linarith
  have hW2eps : 2 * W ≤ 1 / (100 * (t:ℝ)) := by
    have h1 : 2 * W ≤ 2 * (1 / (1000 * (t:ℝ))) := by linarith
    have e1 : 2 * (1 / (1000 * (t:ℝ))) = 1 / (500 * (t:ℝ)) := by
      field_simp
      norm_num
    have h2 : (1:ℝ) / (500 * (t:ℝ)) ≤ 1 / (100 * (t:ℝ)) := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 500 * (t:ℝ))
        (by linarith : (0:ℝ) < 100 * (t:ℝ))]
      linarith
    linarith [h1, h2, e1.le, e1.ge]
  have hprodM : (∏ j, ((m:ℝ) * (n j : ℝ))) = (m:ℝ)^r * ∏ j, (n j : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hlowR : ∀ j : Fin r, (p:ℝ) - (m:ℝ) ≤ (m:ℝ) * (n j : ℝ) := by
    intro j
    have h := hlow j
    have h' : ((p:ℕ) : ℝ) ≤ ((m * n j + m : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hhighR : ∀ j : Fin r, (m:ℝ) * (n j : ℝ) ≤ (p:ℝ) + (m:ℝ) := by
    intro j
    have h := hhigh j
    have h' : ((m * n j : ℕ) : ℝ) ≤ ((p + m : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hpm0 : (0:ℝ) ≤ (p:ℝ) - (m:ℝ) := by
    have : ((m:ℕ):ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast hmp
    linarith
  have hprodlow : ((p:ℝ) - (m:ℝ))^r ≤ ∏ j, ((m:ℝ) * (n j : ℝ)) := by
    calc ((p:ℝ) - (m:ℝ))^r = ∏ _j : Fin r, ((p:ℝ) - (m:ℝ)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j, ((m:ℝ) * (n j : ℝ)) :=
          Finset.prod_le_prod (fun _ _ => hpm0) (fun j _ => hlowR j)
  have hprodhigh : ∏ j, ((m:ℝ) * (n j : ℝ)) ≤ ((p:ℝ) + (m:ℝ))^r := by
    calc ∏ j, ((m:ℝ) * (n j : ℝ)) ≤ ∏ _j : Fin r, ((p:ℝ) + (m:ℝ)) :=
          Finset.prod_le_prod (fun _ _ => mul_nonneg (le_of_lt hM) (Nat.cast_nonneg _))
            (fun j _ => hhighR j)
      _ = ((p:ℝ) + (m:ℝ))^r := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfac1 : (p:ℝ) - (m:ℝ) = (p:ℝ) * (1 - X) := by
    rw [hX]; field_simp
  have hfac2 : (p:ℝ) + (m:ℝ) = (p:ℝ) * (1 + X) := by
    rw [hX]; field_simp
  have hbern : 1 - W ≤ (1 - X)^r := by
    have h := one_add_mul_le_pow (a := -X) (by linarith) r
    have he : (1 : ℝ) + (r:ℝ) * (-X) = 1 - W := by rw [hW]; ring
    have he2 : (1 : ℝ) + -X = 1 - X := by ring
    rw [he, he2] at h
    exact h
  have hupper : (1 + X)^r ≤ 1 + 2 * W := by
    have hu0 : (0:ℝ) ≤ (1 + X)^r := by positivity
    have hmul1 : (1 - X)^r * (1 + X)^r ≤ 1 := by
      rw [← mul_pow]
      have h0 : (0:ℝ) ≤ (1 - X) * (1 + X) := by nlinarith [hX0, hXsmall]
      have h1 : (1 - X) * (1 + X) ≤ 1 := by nlinarith [sq_nonneg X]
      exact pow_le_one₀ h0 h1
    have hstep1 : (1 + X)^r * (1 - W) ≤ 1 := by
      calc (1 + X)^r * (1 - W) ≤ (1 + X)^r * (1 - X)^r :=
            mul_le_mul_of_nonneg_left hbern hu0
        _ = (1 - X)^r * (1 + X)^r := by ring
        _ ≤ 1 := hmul1
    have hstep2 : (1:ℝ) ≤ (1 + 2 * W) * (1 - W) := by
      have h := mul_nonneg hW0 (by linarith : (0:ℝ) ≤ 1 - 2 * W)
      nlinarith [h]
    have hW1 : (0:ℝ) < 1 - W := by linarith
    have hstep3 : (1 + X)^r * (1 - W) ≤ (1 + 2 * W) * (1 - W) := by linarith
    exact le_of_mul_le_mul_right hstep3 hW1
  have hpr : (0:ℝ) < (p:ℝ)^r := by positivity
  have hpt : (0:ℝ) < (p:ℝ)^t := by positivity
  have hmr : (0:ℝ) < (m:ℝ)^r := by positivity
  have hcntR : (cnt:ℝ) * (p:ℝ)^r = (∏ j, (n j:ℝ)) * (p:ℝ)^t := by
    have h : ((cnt * p ^ r : ℕ) : ℝ) = (((∏ j, n j) * p ^ t : ℕ) : ℝ) := by exact_mod_cast hcnt
    push_cast at h
    exact h
  have hratio : (cnt:ℝ) / (p:ℝ)^t = (∏ j, (n j:ℝ)) / (p:ℝ)^r := by
    rw [div_eq_div_iff (ne_of_gt hpt) (ne_of_gt hpr)]
    linarith [hcntR]
  have hA : (1 - 1/(100*(t:ℝ))) / (m:ℝ)^r ≤ (∏ j, (n j:ℝ)) / (p:ℝ)^r := by
    rw [div_le_div_iff₀ hmr hpr]
    have h1 : (1 - 1/(100*(t:ℝ))) * (p:ℝ)^r ≤ ((p:ℝ) - (m:ℝ))^r := by
      rw [hfac1, mul_pow]
      have hb : 1 - 1/(100*(t:ℝ)) ≤ (1 - X)^r := by linarith [hbern, hWeps]
      calc (1 - 1/(100*(t:ℝ))) * (p:ℝ)^r = (p:ℝ)^r * (1 - 1/(100*(t:ℝ))) := by ring
        _ ≤ (p:ℝ)^r * (1 - X)^r := mul_le_mul_of_nonneg_left hb (le_of_lt hpr)
    have h2 : ((p:ℝ) - (m:ℝ))^r ≤ (m:ℝ)^r * ∏ j, (n j:ℝ) := by
      rw [← hprodM]; exact hprodlow
    calc (1 - 1/(100*(t:ℝ))) * (p:ℝ)^r ≤ ((p:ℝ) - (m:ℝ))^r := h1
      _ ≤ (m:ℝ)^r * ∏ j, (n j:ℝ) := h2
      _ = (∏ j, (n j:ℝ)) * (m:ℝ)^r := by ring
  have hB : (∏ j, (n j:ℝ)) / (p:ℝ)^r ≤ (1 + 1/(100*(t:ℝ))) / (m:ℝ)^r := by
    rw [div_le_div_iff₀ hpr hmr]
    have h1 : ((p:ℝ) + (m:ℝ))^r ≤ (1 + 1/(100*(t:ℝ))) * (p:ℝ)^r := by
      rw [hfac2, mul_pow]
      have hb : (1 + X)^r ≤ 1 + 1/(100*(t:ℝ)) := by linarith [hupper, hW2eps]
      calc (p:ℝ)^r * (1 + X)^r ≤ (p:ℝ)^r * (1 + 1/(100*(t:ℝ))) :=
            mul_le_mul_of_nonneg_left hb (le_of_lt hpr)
        _ = (1 + 1/(100*(t:ℝ))) * (p:ℝ)^r := by ring
    have h2 : (m:ℝ)^r * ∏ j, (n j:ℝ) ≤ ((p:ℝ) + (m:ℝ))^r := by
      rw [← hprodM]; exact hprodhigh
    calc (∏ j, (n j:ℝ)) * (m:ℝ)^r = (m:ℝ)^r * ∏ j, (n j:ℝ) := by ring
      _ ≤ ((p:ℝ) + (m:ℝ))^r := h2
      _ ≤ (1 + 1/(100*(t:ℝ))) * (p:ℝ)^r := h1
  rw [hratio, abs_le]
  have hsplit1 : (1 - 1/(100*(t:ℝ))) / (m:ℝ)^r
      = 1 / (m:ℝ)^r - (1/(100*(t:ℝ))) / (m:ℝ)^r := by ring
  have hsplit2 : (1 + 1/(100*(t:ℝ))) / (m:ℝ)^r
      = 1 / (m:ℝ)^r + (1/(100*(t:ℝ))) / (m:ℝ)^r := by ring
  rw [hsplit1] at hA
  rw [hsplit2] at hB
  constructor <;> linarith

/-! ### The digit transport of `14:1769--1771` -/

/-- `[p] ≃ F_p`, by the least nonnegative residue of `14:1779`.  A transport,
not a construction: no choice enters and nothing about the builder is asserted
here. -/
def finZModEquiv (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun i := ((i : ℕ) : ZMod p)
  invFun v := ⟨v.val, ZMod.val_lt v⟩
  left_inv i := by ext; exact ZMod.val_natCast_of_lt i.isLt
  right_inv v := ZMod.natCast_rightInverse v

/-- The definitional unfolding of `balN` (`14:1759--1761`, "It sets `N = p^t`").
It is `rfl` and carries no content; it exists only so that the digit equivalence
and the cast below have a name to rewrite with. -/
theorem balN_eq_pow (q t m : ℕ) : balN q t m = balPrime q t m ^ t := rfl

/-- **"the accessor computes the unique base-`p` digits"** (`14:1768--1771`), as
an *equivalence* `[N] ≃ F_p^t`.

Uniqueness of the base-`p` expansion is exactly what makes the digit map a
bijection, and that bijection is what turns the count over indices `l in [N]`
into the count over coefficient vectors the Vandermonde argument performs.  It
is Mathlib's `finFunctionFinEquiv` (whose inverse is literally
`l ↦ l / p^r % p`, i.e. `balDigit`) composed with the least-residue transport
`finZModEquiv`; no second digit reification is introduced. -/
def balCoeffEquiv (q t m : ℕ) :
    Fin (balN q t m) ≃ (Fin t → ZMod (balPrime q t m)) :=
  ((finCongr (balN_eq_pow q t m)).trans
      (finFunctionFinEquiv (m := balPrime q t m) (n := t)).symm).trans
    (Equiv.piCongrRight fun _ => finZModEquiv (balPrime q t m))

/-- The digit equivalence is the module's own `balDigit` (`14:1770--1771`),
read in `F_p`.  Definitional, which is the point: no new digit convention is
introduced and `a_0` still changes fastest. -/
theorem balCoeffEquiv_apply (q t m : ℕ) (l : Fin (balN q t m)) (s : Fin t) :
    balCoeffEquiv q t m l s
      = ((balDigit (balPrime q t m) (l : ℕ) (s : ℕ) : ℕ) : ZMod (balPrime q t m)) := rfl

/-- **`eq:literal-balanced-accessor` read inside `F_p`** (`14:1774--1778` with
`14:1779`).  The frozen display first reduces the integer Horner sum mod `p`,
then mod `m`; the inner reduction is exactly `ZMod.val` of the corresponding
field element, so the accessor value is `(field evaluation).val % m`.  This is
the bridge between the machine layer and the Vandermonde layer, and it is an
equation, not a redefinition. -/
theorem balEntryVal_eq_zmod_val (p t m l i : ℕ) [NeZero p] :
    balEntryVal p t m l i
      = ((∑ s : Fin t, ((balDigit p l (s : ℕ) : ℕ) : ZMod p)
            * ((i : ℕ) : ZMod p) ^ (s : ℕ)) : ZMod p).val % m := by
  have hcast : ((∑ r ∈ Finset.range t, balDigit p l r * i ^ r : ℕ) : ZMod p)
      = ∑ s : Fin t, ((balDigit p l (s : ℕ) : ℕ) : ZMod p) * ((i : ℕ) : ZMod p) ^ (s : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k => ((balDigit p l k : ℕ) : ZMod p) * ((i : ℕ) : ZMod p) ^ k) t]
    push_cast
    rfl
  rw [balEntryVal, ← hcast, ZMod.val_natCast]

/-! ### The clause itself -/

/-- **THE DELIVERABLE: the fourth clause of `eq:effective-balanced-builder`**
(`14:1591--1592`), "`c_{d_bal}` is indexed `(q,t,1/(100t))`-balanced", proved by
the frozen argument `14:1784--1810`.

This is the **canonical inhabitation** of `NPCC.IsBalancedFamily` for this
route: the family is not some family exhibited to show the predicate is
satisfiable, it is the paper's own `c_{d_bal}` -- the output of the builder
`14:1749--1763` evaluated by the accessor `14:1768--1782` -- at every legal
parameter triple `q >= t >= 1`, `m > 0` (`14:1557--1558`).  This declaration
discharges **item (a)** of ledger row `S5-BALANCED-FAMILY` -- the balancedness
clause -- and item (a) alone: the row remains **OPEN** on item (b), the
level-step instantiation at `A_bal(q_{2,i}, t_{2,i}, m_{1,i})` (whose derived
`t_2` accessor for `eq:t2-search`, `06:763--773`, lands at `cc-t7k` in Part
11, and the call stays blocked on the structural row `4 t_2 <= q_2` of
`06:835`, which `cc-t7l` in Part 12 places at its paper anchor -- item (v) of
`06:1197--1226`, discharged at `sec:effective-cutoff` -- rather than
discharging), and on item (c), the
three phantom `lem:cited-balanced-family` comment sites in the banked
`Section5Admissibility.lean`.

The proof assembles the frozen paragraph in its own order.  Fix `J` with
`|J| <= t` and a pattern `a`.  Enumerate `J` increasingly as `i_1 < ... < i_r`
(`Finset.orderIsoOfFin`); the banked `q_le_balPrime` makes their images in `F_p`
distinct, which is `14:1785--1786`.  The digit equivalence `balCoeffEquiv`
identifies `[N]` with `F_p^t`, and `balEntryVal_eq_zmod_val` identifies the
accessor's value with `(vandEval ...).val % m`, so the counted set becomes a
`vandEval` preimage of prescribed residue classes.  `card_vandEval_preimage_mul`
evaluates that count exactly (`14:1786--1792`), `residue_card_upper` and
`residue_card_lower` bound each class size (`14:1793--1795`), and
`balanced_ratio_bound` -- consuming the banked `m_le_balPrime_ratio` for
`14:1799` -- closes with Bernoulli and the geometric tail (`14:1799--1808`).

No axiom is added: the closure is `propext`, `Classical.choice`, `Quot.sound`
only, and `Classical.choice` enters through Mathlib's Lagrange/`Finset`
machinery, not through any project interface.  `LegacyNPCC.Stage12` and its
cited-existence axiom `NPCC.aghp_balanced_family_exists` are **not** adopted:
the whole point of `sections/14` is that this family is built and its
balancedness proved, not cited. -/
theorem balFamily_isBalanced (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q) :
    NPCC.IsBalancedFamily t (balFamily q t m hm) (1 / (100 * (t : ℝ))) := by
  refine ⟨balN_pos q t m, ?_⟩
  intro J hJ a
  have hqp : q ≤ balPrime q t m := q_le_balPrime q t m
  have hmp : m ≤ balPrime q t m := by
    have h := thousand_le_balPrime q t m
    have ht2 : 1 ≤ t ^ 2 := Nat.one_le_pow 2 t ht
    nlinarith [h, ht2, hm]
  have hrt : J.card ≤ t := hJ
  let oi := J.orderIsoOfFin (rfl : J.card = J.card)
  let e : Fin J.card → Fin q := fun j => ((oi j : { x // x ∈ J }) : Fin q)
  have hemem : ∀ j : Fin J.card, e j ∈ J := fun j => (oi j).2
  have heinj : Function.Injective e := by
    intro j₁ j₂ h
    exact oi.injective (Subtype.ext h)
  have hesurj : ∀ γ ∈ J, ∃ j : Fin J.card, e j = γ := by
    intro γ hγ
    exact ⟨oi.symm ⟨γ, hγ⟩, by simp [e]⟩
  let x : Fin J.card → ZMod (balPrime q t m) :=
    fun j => (((e j : Fin q) : ℕ) : ZMod (balPrime q t m))
  have hxinj : Function.Injective x := by
    intro j₁ j₂ h
    have h1 : ((e j₁ : Fin q) : ℕ) < balPrime q t m := lt_of_lt_of_le (e j₁).isLt hqp
    have h2 : ((e j₂ : Fin q) : ℕ) < balPrime q t m := lt_of_lt_of_le (e j₂).isLt hqp
    have hv : ((e j₁ : Fin q) : ℕ) = ((e j₂ : Fin q) : ℕ) := by
      rw [← ZMod.val_natCast_of_lt h1, ← ZMod.val_natCast_of_lt h2]
      exact congrArg ZMod.val h
    exact heinj (Fin.ext hv)
  let T : Fin J.card → Finset (ZMod (balPrime q t m)) :=
    fun j => Finset.univ.filter (fun v => v.val % m = ((a (e j) : Fin m) : ℕ))
  have hval : ∀ (l : Fin (balN q t m)) (j : Fin J.card),
      (vandEval x (balCoeffEquiv q t m l) j).val % m
        = ((balFamily q t m hm l (e j) : Fin m) : ℕ) := by
    intro l j
    have hsum : vandEval x (balCoeffEquiv q t m l) j
        = ∑ s : Fin t, ((balDigit (balPrime q t m) (l : ℕ) (s : ℕ) : ℕ) : ZMod (balPrime q t m))
            * ((((e j : Fin q) : ℕ) : ℕ) : ZMod (balPrime q t m)) ^ (s : ℕ) :=
      Finset.sum_congr rfl (fun s _ => by rw [balCoeffEquiv_apply])
    rw [hsum, balFamily_val, balEntryVal_eq_zmod_val]
  have hcard :
      (Finset.univ.filter
        (fun l : Fin (balN q t m) => ∀ γ ∈ J, balFamily q t m hm l γ = a γ)).card
      = (Finset.univ.filter
        (fun c : Fin t → ZMod (balPrime q t m) => ∀ j, vandEval x c j ∈ T j)).card := by
    refine Finset.card_equiv (balCoeffEquiv q t m) ?_
    intro l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j
      have hj := h (e j) (hemem j)
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hval l j, hj]
    · intro h γ hγ
      obtain ⟨j, hj⟩ := hesurj γ hγ
      subst hj
      have hmem := h j
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rw [hval l j] at hmem
      exact Fin.ext hmem
  have hkey := card_vandEval_preimage_mul (p := balPrime q t m) (t := t) (r := J.card)
    ht hrt x hxinj T
  have hnlow : ∀ j, balPrime q t m ≤ m * (T j).card + m := by
    intro j
    rw [show (T j).card
        = ((Finset.range (balPrime q t m)).filter
            (fun v => v % m = ((a (e j) : Fin m) : ℕ))).card from
      card_residue_zmod _ _ _]
    exact residue_card_lower _ _ _ hm (a (e j)).isLt
      (lt_of_lt_of_le (a (e j)).isLt hmp)
  have hnhigh : ∀ j, m * (T j).card ≤ balPrime q t m + m := by
    intro j
    rw [show (T j).card
        = ((Finset.range (balPrime q t m)).filter
            (fun v => v % m = ((a (e j) : Fin m) : ℕ))).card from
      card_residue_zmod _ _ _]
    exact residue_card_upper _ _ _
  have hfinal := balanced_ratio_bound (n := fun j => (T j).card) ht hrt hm hmp
    (m_le_balPrime_ratio q t m ht) hnlow hnhigh hkey
  have hNR : ((balN q t m : ℕ) : ℝ) = ((balPrime q t m : ℕ) : ℝ) ^ t := by
    rw [balN_eq_pow]; push_cast; ring
  simp only [Fintype.card_fin]
  rw [hcard, hNR]
  exact hfinal

/-- Balancedness is preserved by relabelling the *value* carrier along an
equivalence.  This is the value-side companion of the vendored
`NPCC.IsBalancedFamily.projection`, which relabels *coordinates* along an
injection; neither is a restatement of the other, and the vendored file is not
touched.  It exists here because `14:1629--1631` stores `c_{2,i} = e_i ∘ c_{d_i}`
rather than `c_{d_i}` itself. -/
theorem isBalancedFamily_congr_equiv {Y Z : Type*} [DecidableEq Y] [Fintype Y]
    [DecidableEq Z] [Fintype Z] {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (φ : Y ≃ Z) (h : NPCC.IsBalancedFamily t S ε) :
    NPCC.IsBalancedFamily t (fun l i => φ (S l i)) ε := by
  refine ⟨h.1, ?_⟩
  intro J hJ a
  have hcard : (Fintype.card Z : ℝ) = (Fintype.card Y : ℝ) := by
    rw [Fintype.card_congr φ]
  have hset : (Finset.univ.filter (fun l : Fin L => ∀ γ ∈ J, φ (S l γ) = a γ))
      = (Finset.univ.filter (fun l : Fin L => ∀ γ ∈ J, S l γ = φ.symm (a γ))) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hh γ hγ
      exact (Equiv.eq_symm_apply φ).mpr (hh γ hγ)
    · intro hh γ hγ
      rw [hh γ hγ, Equiv.apply_symm_apply]
  rw [hset, hcard]
  exact h.2 J hJ (fun γ => φ.symm (a γ))

/-- **The family actually stored in the parameter record is balanced**
(`14:1621--1632` composed with `14:1591--1592`).

`14:1629--1631` stores `c_{2,i}(l)(r) = e_i(c_{d_i}(l)(r))`, not `c_{d_i}`, and
it is the stored family that the Stage-2 consumer reads
(`StageTwoRelaxed.stageTwoTwoDepthCertificate`, whose `hbal` binder is exactly
`NPCC.IsBalancedFamily W.t₂ Pr.c₂ ε₂`).  So the clause has to hold *there*, and
it does: `e_i` is the banked `canonEquiv`, an equivalence, and balancedness
transports along it with the same accuracy. -/
theorem storedFamily_isBalanced (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q)
    (X₁ : Type*) [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m) :
    NPCC.IsBalancedFamily t (storedFamily q t m hm X₁ h) (1 / (100 * (t : ℝ))) :=
  isBalancedFamily_congr_equiv (canonEquiv X₁ h) (balFamily_isBalanced q t m hm ht htq)

/-- **STATEMENT POLE: the clause excludes the trivial witness.**

A constant family is the family any bare "there is an indexed family in `[m]^q`"
statement admits, and `PublicRecords.levelParams_admits_unbalanced_family` banks
that it is a perfectly legal `Pi`.  It is **not** `(q,t,1/(100t))`-balanced at
any legal parameter triple with a non-degenerate alphabet: the singleton
coordinate set `{0}` and a pattern symbol other than the constant one are met by
no index at all, so the prescribed probability is `0` rather than within
`1 +- 1/(100t)` of `1/m`.  Taken with `balFamily_isBalanced` and the banked
`balFamily_not_constant`, this is the whole non-vacuity account for the clause:
the predicate is a real constraint, and the built family satisfies it.

This declaration claims **no** legality: it is universally quantified over the
region where the statement is a refutation, and instantiates no parameter. -/
theorem constant_family_not_isBalanced {q L m t : ℕ} (ht : 0 < t) (hq : 0 < q)
    (hm : 1 < m) (c₀ : Fin m) :
    ¬ NPCC.IsBalancedFamily t (fun (_ : Fin L) (_ : Fin q) => c₀)
        (1 / (100 * (t : ℝ))) := by
  intro h
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨c₁, hc₁⟩ := exists_ne c₀
  have hJ : ({⟨0, hq⟩} : Finset (Fin q)).card ≤ t := by
    rw [Finset.card_singleton]; exact ht
  have hb := h.2 {⟨0, hq⟩} hJ (fun _ => c₁)
  have hfilter : (Finset.univ.filter
      (fun l : Fin L => ∀ γ ∈ ({⟨0, hq⟩} : Finset (Fin q)), c₀ = c₁)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro l _ hcon
    exact hc₁ (hcon ⟨0, hq⟩ (Finset.mem_singleton_self _)).symm
  rw [hfilter, Finset.card_singleton] at hb
  have hmR : (0:ℝ) < (m:ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have htR : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  simp only [Nat.cast_zero, zero_div, Fintype.card_fin, pow_one, zero_sub, abs_neg] at hb
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(m:ℝ))] at hb
  rw [div_le_div_iff₀ hmR hmR] at hb
  have hlt : (1:ℝ)/(100*(t:ℝ)) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  nlinarith [hb, hlt, hmR]

/-- **BEYOND-PAPER AUDIT.**  The deliverable's hypothesis bundle is satisfiable
at a non-degenerate alphabet: `(q,t,m) = (2,1,2)` meets `q >= t >= 1` and
`m > 0` with `m >= 2`, so `balFamily_isBalanced` is not vacuously quantified.

The triple is **self-chosen** and the frozen paper never visits it -- it audits
OUR encoding at a point the source does not name, which is strictly weaker
evidence than the paper's own application point and is not a substitute for it.
The paper's application point is `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`
(`14:1624--1625`).  It is **still not reached**, though for a strictly smaller
reason than before: `cc-t7j` lands the `eq:t2-search` spec (Part 9) and the
third builder argument `m_{1,i}` (Part 10), and `cc-t7k` lands all three
arguments' inputs -- `L_h`, `H_max`, `k_2` and `t_2` at `(Public, K)` (Part
11) -- so what remains is not a missing quantity but a missing *permission*:
`06:830--831` requires the structural row `4 t_2 <= q_2` (`06:835`) verified
before the family is constructed, and no theorem on this route concludes it.
`cc-t7l` (Part 12) shows that no theorem on this route *can* conclude it at
every `(Public, K)` of the unrestricted Lean domain, and locates the paper's own
discharge at `sec:effective-cutoff` (item (v), `06:1219--1220`); the level-step
call is therefore still not made.  That obligation is registered on
`S5-BALANCED-FAMILY-LEVELSTEP-001` and is not discharged here, so this audit
theorem remains the abstract-parameter probe it always was and is not a
substitute for the paper's application point. -/
theorem balFamily_isBalanced_nondegenerate :
    NPCC.IsBalancedFamily 1 (balFamily 2 1 2 (by norm_num))
      (1 / (100 * ((1 : ℕ) : ℝ))) :=
  balFamily_isBalanced 2 1 2 (by norm_num) (le_refl 1) (by norm_num)

/-! ## Part 9: the `eq:t2-search` search spec (`06:763--773`), usable at the
paper's own tested endpoint `eq:k2-tested-endpoint` (`06:774--780`)

**What is new here, and what is consumed by pin.**  The *reifications* of
`eq:t2-search` and of its endpoint record are banked in `ParameterSchedule`
Section 9 and are **not** repeated: `ParameterSchedule.K2Pred` (the three
clauses, `06:766--769`), `ParameterSchedule.k2` (the least integer, `06:763`),
`ParameterSchedule.t2` (`t_2 = 2^{k_2}`, `06:770`),
`ParameterSchedule.k2Floor` (`K_0 = max{4, 2^19, m_HS}`, `06:766`/`06:776`),
`ParameterSchedule.zEndpoint` (`z`, `06:777`),
`ParameterSchedule.k2Star` (`k_2^* = K_0 + 10000 z^2`, `06:778`),
`ParameterSchedule.j49` (`eq:j49-search-data`, `06:92--97`),
`ParameterSchedule.k2_le_star` (`06:813--814`) and, new at `cc-t7j` in that
same banked module, `ParameterSchedule.k2Star_meets_search` (`06:813`, the
endpoint membership).  Two further banked theorems are consumed by pin below
and likewise not repeated: `MassRedistributionTail.K2Pred_at_k2` (the three
clauses **at the accessor**, `06:763--771`) and
`WrapperMassRedistribution.k2_floors_of_K2Pred` (the branches of the frozen
floor `06:766` read off the predicate).  **No second copy of any of those
displays or proofs is written below.**

**What was already banked, and what was not** (`cc-t7j-r1`, correcting the
`cc-t7j` park's own header; Sol findings F-1/F-2/F-3).  The park's header
asserted that "the banked Section 9 did not carry the search's spec" and that
`06:781--812` had no owner outside `ParameterSchedule`.  **Both claims were
false on those bytes.**  `MassRedistributionTail` already owned *two* of the
three facts: `K2Pred_at_k2Star` (endpoint membership) and `K2Pred_at_k2`
(membership at the accessor, by `Nat.sInf_mem`), and `Section5Admissibility`
already recorded that it consumed the second.  The park's `k2Star_meets_search`
and `k2_spec` were therefore not new statements but second owners of banked
ones, at universe `0` and modulo the namespace qualifier -- invisible to a
short-name check, which is why the rule minted at `cc-t7j` is that dedup
screening compares **statements** across the transitive import closure, up to
namespace and universe, not declaration heads.

**The architecture that actually holds on these bytes.**  Endpoint membership
(`06:813`) is owned once, upstream, by `ParameterSchedule.k2Star_meets_search`,
where the displays it verifies are reified.  `ParameterSchedule.k2_le_star`
derives `06:813--814` from it by `Nat.sInf_le`;
`MassRedistributionTail.K2Pred_at_k2` derives membership at the accessor from
it by `Nat.sInf_mem`; the duplicates in `MassRedistributionTail` and in the
`cc-t7j` draft of this module are **DELETED, not wrapped**.  Every declaration
below consumes those two banked theorems by pin, and nothing of `06:781--812`
or of `Nat.sInf_mem` at the search is re-derived in this module.

**One universe, not a family.**  `k2Floor` reads the banked
`HardSeedFacade.mHS`, which is universe polymorphic; `02:799--806` fixes
`m_HS` **once** ("It is selected once and hardwired into the finite code of
`A_cert`"), and the banked `MechanicalCompilerResidue` block on `T` and `B_s`
records that reading it under a fresh universe binder would expose a *family*
of naturals where the frozen paragraph fixes a single value.  Every
declaration below therefore reads the search at the single universe this
route's carriers inhabit, `Type` (`conv:finite-slots`), and carries no
universe binder at all.

**Generality, and what the three binders are.**  Part 9 is general in
`(L_h, B_cap, H_max)` at exactly the banked `ParameterSchedule.K2Pred` / `.k2`
/ `.t2` signature -- it is the spec of that reified display and nothing more.
It makes **no** claim about the level step, exhibits no `(Public, K)` value for
any of the three, and in particular does not assert that any of them has been
derived at the paper's scheduled point.  Part 9 is unchanged by `cc-t7k`: the
`(Public, K)` values it is general in are supplied *downstream*, in Part 11,
which applies these same statements to `LhFor`, `bCapFor` and `HmaxFor` and
discharges the `hshape` premise there rather than here.

No reader counterpart: the 41-page reader artifact prints no parameter
schedule, and in particular no `t_2` search -- its realization machine only
records that the compiler "continues the pre-family traversal to compute
`t_{2,i}`" (`C-effectivity-details.tex:93--100`), which is a statement about
ordering, not the display.  None of the declarations of Part 9 or Part 10
claims a reader item. -/

/-- **`06:817--819`: the search terminates, on checked data.**

"This exact integer search terminates" (`06:819`), because the tested endpoint
is a witness: `06:817--818`, "Termination and the returned endpoint bound are
therefore checked data, not inferred from the word *least*."  The witness is
the paper's own `k_2^*` supplied by the banked
`ParameterSchedule.k2Star_meets_search`, and nothing else is exhibited.

**Statement pole.**  The trivial witness fails this existential: the first
clause of `K2Pred` is `k >= K_0 = max{4, 2^19, m_HS}`, which already excludes
every `k < 2^19`, and the second, `2^k >= 2 H_max`, is unbounded in `H_max`, so
no constant natural inhabits it either.  General.  PROVED. -/
theorem k2Exists {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    ∃ k : ℕ, ParameterSchedule.K2Pred.{0} Lh Bcap Hmax k :=
  ⟨_, ParameterSchedule.k2Star_meets_search.{0} hshape⟩

/-! **Membership at the accessor is NOT stated here** (`cc-t7j-r1`).

The `cc-t7j` park carried a theorem `k2_spec` asserting
`K2Pred Lh Bcap Hmax (k2 Lh Bcap Hmax)`.  Sol's gate (finding F-2, agreed
first-hand) found it to be the reachable banked
`MassRedistributionTail.K2Pred_at_k2` at universe `0` -- same statement, same
`Nat.sInf_mem` proof -- and `MassRedistributionTail` is in this module's
transitive import closure.  So it is **deleted, not renamed and not wrapped**,
and every projection below consumes `MassRedistributionTail.K2Pred_at_k2.{0}`
by pin.  Its own proof in turn consumes the single upstream owner of the
endpoint membership, `ParameterSchedule.k2Star_meets_search`, so `06:781--813`
is proved exactly once on the route. -/

/-- **Aux T0 (the accessor is LEAST).**  `06:763`, "Let `k_2` be the least
integer satisfying": nothing below it meets the three clauses, so the frozen
word "least" is carried and not weakened.  This needs no nonemptiness
hypothesis -- below an empty search `k_2 = 0` and there is nothing under it.
General.  PROVED. -/
theorem k2_min {Lh Bcap Hmax k : ℕ}
    (h : k < ParameterSchedule.k2.{0} Lh Bcap Hmax) :
    ¬ ParameterSchedule.K2Pred.{0} Lh Bcap Hmax k := by
  intro hk
  have hle : sInf {j : ℕ | ParameterSchedule.K2Pred.{0} Lh Bcap Hmax j} ≤ k :=
    Nat.sInf_le hk
  exact absurd hle (not_le.mpr h)

/-- **First clause at the accessor** (`06:766`): `k_2 >= max{4, 2^19, m_HS}`,
hence in particular `k_2 >= 4`.  The `4` is the display's own first branch, not
a chosen bound.

Both banked interfaces are consumed by pin and neither is restated: the
membership is `MassRedistributionTail.K2Pred_at_k2`, and the reading-off of the
frozen floor's branches is `WrapperMassRedistribution.k2_floors_of_K2Pred`
(`cc-t7j-r1`, Sol's prescribed wiring).  General.  PROVED. -/
theorem four_le_k2 {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    4 ≤ ParameterSchedule.k2.{0} Lh Bcap Hmax :=
  (WrapperMassRedistribution.k2_floors_of_K2Pred.{0}
    (MassRedistributionTail.K2Pred_at_k2.{0} hshape)).1

/-- **Aux T1 (`t_2` is a positive power of two).**  `06:770` sets
`t_2 = 2^{k_2}`, so positivity is unconditional -- it does not depend on the
search being nonempty.  General.  PROVED. -/
theorem t2_pos (Lh Bcap Hmax : ℕ) : 0 < ParameterSchedule.t2.{0} Lh Bcap Hmax := by
  simp only [ParameterSchedule.t2]
  exact pow_pos (by norm_num) _

/-- **`06:824`: the search "makes `t_2` divisible by `16`".**

The frozen sentence, derived rather than assumed: `k_2 >= 4` is the first
clause of `eq:t2-search` at its own accessor -- `four_le_k2` above, which now
routes through the banked floor theorem (`cc-t7j-r1`) -- and `t_2 = 2^{k_2}`.
General.  PROVED. -/
theorem sixteen_dvd_t2 {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    16 ∣ ParameterSchedule.t2.{0} Lh Bcap Hmax := by
  have h4 := four_le_k2 hshape
  simp only [ParameterSchedule.t2]
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16]
  exact pow_dvd_pow 2 h4

/-- **Second clause at the accessor, read in `t_2`** (`06:767`):
`t_2 = 2^{k_2} >= 2 H_max`.  This is the sense in which the single Stage-2
width covers the shared Localized-Extension budget of `eq:Hmax`.  The second
projection of the banked `MassRedistributionTail.K2Pred_at_k2`, consumed by pin
(`cc-t7j-r1`).  General.  PROVED. -/
theorem two_mul_Hmax_le_t2 {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    2 * Hmax ≤ ParameterSchedule.t2.{0} Lh Bcap Hmax :=
  (MassRedistributionTail.K2Pred_at_k2.{0} hshape).2.1

/-- **Third clause at the accessor** (`06:768--769`):
`2^{j_49(k_2)} >= L_h + B_cap + k_2 + 4`, the hard-seed clause of
`eq:t2-search`.  The third projection of the banked
`MassRedistributionTail.K2Pred_at_k2`, consumed by pin (`cc-t7j-r1`).  General.
PROVED. -/
theorem hardSeed_clause_at_k2 {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    Lh + Bcap + ParameterSchedule.k2.{0} Lh Bcap Hmax + 4
      ≤ 2 ^ ParameterSchedule.j49 (ParameterSchedule.k2.{0} Lh Bcap Hmax) :=
  (MassRedistributionTail.K2Pred_at_k2.{0} hshape).2.2

/-- **`06:813--814` in `t_2`: the returned endpoint bound.**  "least-search
minimality gives `k_2 <= k_2^*`", hence `t_2 <= 2^{k_2^*}`, which is the
integer content of the checked growth statement `eq:t2-growth`
(`06:820--823`).  The banked `ParameterSchedule.k2_le_star` is consumed by pin;
nothing of its proof is repeated.  General.  PROVED. -/
theorem t2_le_two_pow_k2Star {Lh Bcap Hmax : ℕ} (hshape : Lh + Bcap ≤ Hmax) :
    ParameterSchedule.t2.{0} Lh Bcap Hmax ≤ 2 ^ ParameterSchedule.k2Star.{0} Hmax := by
  simp only [ParameterSchedule.t2]
  exact Nat.pow_le_pow_right (by norm_num) (ParameterSchedule.k2_le_star.{0} hshape)

/-- **Aux T2 (monotone in the shared width threshold).**  Only the second
clause of `eq:t2-search` reads `H_max`, and it reads it as a lower bound, so
raising `H_max` can only raise the least admissible `k_2`.  The
larger-threshold predicate is the banked `MassRedistributionTail.K2Pred_at_k2`,
consumed by pin (`cc-t7j-r1`).  General; the hypothesis is the shape premise at
the larger threshold.  PROVED. -/
theorem k2_mono {Lh Bcap Hmax Hmax' : ℕ} (h : Hmax ≤ Hmax')
    (hshape' : Lh + Bcap ≤ Hmax') :
    ParameterSchedule.k2.{0} Lh Bcap Hmax ≤ ParameterSchedule.k2.{0} Lh Bcap Hmax' := by
  refine Nat.sInf_le ?_
  obtain ⟨h1, h2, h3⟩ := MassRedistributionTail.K2Pred_at_k2.{0} hshape'
  exact ⟨h1, le_trans (Nat.mul_le_mul_left 2 h) h2, h3⟩

/-- **Aux T3 (round trip: `t_2` determines `k_2`).**  `06:770` sets
`t_2 = 2^{k_2}`, so the integer base-two logarithm recovers the exponent
exactly and no information is lost by storing the width rather than the
exponent.  General, and unconditional.  PROVED. -/
theorem log_two_t2 (Lh Bcap Hmax : ℕ) :
    Nat.log 2 (ParameterSchedule.t2.{0} Lh Bcap Hmax)
      = ParameterSchedule.k2.{0} Lh Bcap Hmax := by
  simp only [ParameterSchedule.t2]
  exact Nat.log_pow (by norm_num) _

/-! ## Part 10: the two arguments of `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`
(`14:1621--1632`) that are derivable at `(Public, K)` today

`14:1621--1625` records, for every level `0 <= i < k`, "positive integers
`q_{2,i} >= t_{2,i} >= 1`, and the literal output `(N_{2,i}, d_i)` of
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})`, where `m_{1,i} = |Rows(M_1^{(i)})|`".  Of
those three arguments:

* `q_{2,i}` is the banked `LevelStepConstruction.q2For` (`05:329--332`) --
  already derived, nothing owed, and nothing restated here;
* `m_{1,i} = |Rows(M_1^{(i)})|` is `Fintype.card (StepRowsOne P K)`, the
  cardinality of the banked Stage-1 row carrier `Rows(M_1) = [q_1] x Rows(R)`
  (`eq:stage1-universes-and-value`, `07:144`).  **This part evaluates it**
  (`stepRowsOne_card`), and derives the builder's own `m > 0` guard
  (`14:1781`) rather than assuming it;
* `t_{2,i}` is **not derived in Part 10**; it is derived in **Part 11**
  (`cc-t7k`), as `eq:t2-search` evaluated at `eq:Hmax` (`06:754--762`) through
  the auxiliary depth `L_h = max{b_2, b_T} + max{q, u_term} + 4` (`06:757`)
  and the terminal-uniform chain behind `u_term`.  The `cc-t7i`/`cc-t7j` bytes
  of this bullet recorded that `u_term` "has no `(Public, K)` accessor anywhere
  on this route" and that `k_ref`'s own inputs "`t_0(3/5)`, `mu_P`, `B_theta`,
  `L_theta` are not derived at `(Public, K)` either".  The second half is
  **refuted** and is corrected in the Part-11 block docstring, with each of the
  four traced to its banked owner; the first half was true of the name only,
  and Part 11 supplies it.

**Part 10 itself authors no `(Public, K)`-facing `H_max`, `k_2`, `t_2` or
`A_bal` call**, and neither does Part 11 author a call, a stored family or a
`Pi_i` record -- not under a helper label, not under a NON-FIDELITY label, not
at all.  (This sentence is about Parts 10 and 11 and stays true of them.  Part
13, added at `cc-t8b` and banked at `cc-t8c`, *does* write a `Pi_i`-shaped
record, explicitly under a NON-FIDELITY label and without the paper's data
precondition; it is not a call.)  What blocks the call after `cc-t7k` is no
longer a missing quantity
but the schedule's own structural row `4 t_2 <= q_2`
(`eq:stage2-structural-gates`, `06:835`), which `06:830--831` requires verified
*before* constructing the family and which no theorem on this route concludes.
(The earlier bytes cited `06:744--745` for the row's eventual validity;
corrected at `cc-t7l` -- that sentence is about `eq:terminal-wrapper-gates`.
This row's placement is item (v) of `06:1197--1226`, at `06:1219--1220`,
discharged by `sec:effective-cutoff`, `06:1169--1177`.)  That
residue is REGISTERED on `S5-BALANCED-FAMILY-LEVELSTEP-001`.  Item (b) of
`S5-BALANCED-FAMILY` is **NOT DISCHARGED**, and no canonical-inhabitation or
level-step balanced-family credit is claimed by anything below.

What Part 10 does land is the one further slot of `eq:Hmax` that is settled
independently of `L_h` -- the exactness of its `log_2 q` summand
(`lgQFor_eq`) -- together with the `m_{1,i}` argument above.  Both are
receipts about banked `(Public, K)` accessors, neither mentions `L_h`, and
neither asserts that `eq:Hmax` has been evaluated.

## Fixed-interface discipline for Parts 9 and 10

* `ParameterSchedule` Section 9 -- `K2Pred`, `k2`, `t2`, `k2Star`, `j49`,
  `k2Star_meets_search`, `k2_le_star`, `qWrap_eq_two_pow` -- all
  **consumed by pin**, each in at least one proof term below.  No second copy
  of `eq:t2-search`, `eq:k2-tested-endpoint`, `eq:k2-j49-candidate`,
  `eq:k2-fixed-growth-lemma` or `eq:Hmax` is written here.
  `ParameterSchedule.k2Floor` is **not** named in any proof term here
  (`cc-t7j-r1`, Sol's prescribed correction; measured at zero
  comment-stripped occurrences by both gate seats): this module reaches the
  branches of `06:766`'s floor **indirectly**, through the banked
  `WrapperMassRedistribution.k2_floors_of_K2Pred`, which reads them off the
  predicate -- see `four_le_k2`.  `ParameterSchedule.HmaxSched`, `.LhSched`
  and `.vMax` are not consumed in Parts 9 or 10; they are consumed **by pin**
  in Part 11, which is where `eq:Hmax` is evaluated, and **no second defining
  implementation** of any of the three is introduced anywhere in this module.
  That narrower claim is the accurate one, and is stated narrowly on purpose:
  `LhFor_eq_display` does restate `06:757`'s right-hand side, but as a `rfl`
  receipt read back off `LhSched`, which is a receipt and not a competing
  definition.
* `MassRedistributionTail.K2Pred_at_k2` -- **consumed by pin** (`cc-t7j-r1`),
  in `four_le_k2`, `two_mul_Hmax_le_t2`, `hardSeed_clause_at_k2` and `k2_mono`.
  It is the banked owner of membership at the accessor; this module states no
  theorem with that statement, at universe `0` or any other.
* `WrapperMassRedistribution.k2_floors_of_K2Pred` -- **consumed by pin**
  (`cc-t7j-r1`), in `four_le_k2`.  The branches of `06:766`'s floor are read
  off the predicate there, never re-derived here.
* `LevelStepConstruction` -- `qFor`, `LPFor`, `stage1BindingFor`,
  `StepRowsOne` -- consumed by pin.  None is restated, and no new `(Public, K)`
  accessor duplicating one of its twenty-five is introduced: `q_1` is read as
  the banked field-derived `FiniteSlots.Stage1SlotBinding.q₁` at
  `stage1BindingFor P K` rather than as a second `q1Stage1` application.
* `FiniteSlots.Stage1SlotBinding.six_le_q₁` and
  `PublicRecords.LevelPublicInput.mRpos` -- consumed by pin; both are what make
  the value carrier non-degenerate, so no cardinality is assumed.

## Numeral screen for Parts 9 and 10

Statement literals only; definition bodies are included, since a `def`'s body
*is* its statement (Parts 9 and 10 introduce no `def` at all this round).  The
universe index `.{0}` is a **universe level, not a numeric literal**; it is
classified once, here, against `02:799--806` (`m_HS` "is selected once and
hardwired into the finite code of `A_cert`"), which is why every declaration
reads the search at one universe rather than as a family.  The `4` and `2^19`
of `K_0` are **inside** the banked `k2Floor` reification and are that module's
rows.

Fourteen rows for the fourteen declarations Parts 9 and 10 introduce.  The
`cc-t7j` park had fifteen; its
`k2_spec` is deleted at `cc-t7j-r1` as a duplicate of banked
`MassRedistributionTail.K2Pred_at_k2`, and the table is renumbered rather than
left with a hole.

01. `k2Exists` -- none.
02. `k2_min` -- none.
03. `four_le_k2` -- `4`.  CANONICAL-FORM: the first branch of
    `K_0 = max{4, 2^19, m_HS}` (`06:766`, named `K_0` at `06:776`).
04. `t2_pos` -- `0`.  CANONICAL-FORM: positivity of `t_2 = 2^{k_2}`
    (`06:770`).
05. `sixteen_dvd_t2` -- `16`.  CANONICAL-FORM: `06:824`, "makes `t_2`
    divisible by `16`".
06. `two_mul_Hmax_le_t2` -- `2`.  CANONICAL-FORM: the second clause
    `2^{k_2} >= 2 H_max` (`06:767`).
07. `hardSeed_clause_at_k2` -- `2`, `4`.  CANONICAL-FORM: the third clause
    `2^{j_49(k_2)} >= L_h + B_cap + k_2 + 4` (`06:768--769`) -- the `2` is that
    display's own base and the `4` its own additive margin.
08. `t2_le_two_pow_k2Star` -- `2`.  CANONICAL-FORM: the base of `2^{k_2^*}`,
    `06:770` composed with `06:813--814`.
09. `k2_mono` -- none.
10. `log_two_t2` -- `2`.  CANONICAL-FORM: the base of `log_2` in
    `t_2 = 2^{k_2}` (`06:770`).
11. `lgQFor_eq` -- `2`, `2`.  The first is the `log_2` base of the third
    summand of `eq:Hmax` (`06:759`); the second is the square in
    `q = 2^{A_wrap L_P^2}` (`06:515`), which is the banked `qWrap`'s own
    exponent.
12. `stepRowsOne_card` -- none.
13. `six_le_stepRowsOne_card` -- `6`.  EVALUATED: `q_1 = 2^a - 2` (`06:315`)
    at the frozen floor `a >= 3` of the banked `Stage1SlotBinding`, i.e. its
    own `six_le_q₁`.  It is not a chosen bound.
14. `stepRowsOne_card_pos` -- `0`.  The builder's accessor guard `m > 0`
    (`14:1781`).

Every occurrence is classified; none stands where a source-defined quantity
belongs.  In particular `k_2`, `t_2`, `k_2^*`, `z`, `K_0`, `H_max`, `q_2`,
`q_1`, `B_cap`, `r_2` and `N_2` never appear as literals.

## Binder-provenance table for Parts 9 and 10

Parts 9 and 10 introduce **no structure, no field and no `def`**, so every row
below is a binder.

* `Lh`, `Bcap`, `Hmax` in Part 9 -- the reified search display's **own inputs**,
  at the banked signature of `ParameterSchedule.K2Pred` / `.k2` / `.t2`
  (`06:763--773`, which quantifies the search over exactly these three).  Part
  9 is general in them exactly as that banked module is, and this is
  fixed-interface consumption, not a free choice: **no Part-9 declaration
  claims a value for any of the three, and none claims evaluation at
  `(Public, K)`.**  `L_h` is SOURCE-DEFINED at `06:757`, and its evaluation is
  Part 11's `LhFor`: Part 9 does not perform it and does not presuppose it, so
  the generality of these three binders is the banked display's own and not a
  free choice standing in for a value.
* `k` in `k2_min` -- a comparison candidate ranging strictly below the
  accessor.  It is what makes `06:763`'s "least" a real minimality claim, and
  it is never a candidate *value* for `k_2`.
* `Hmax'` in `k2_mono` -- a second threshold, comparison only.
* `P : LevelPublicInput V E` -- GENUINELY-FREE.  `05:174` fixes `Public`
  abstractly and `05:320` makes it the procedure's first input.
* `K : LevelConfig` -- GENUINELY-FREE.  `02:178--179`, "Fix one universal level
  configuration `K_*` ...": the paper fixes it abstractly and assigns it no
  value.
* `V`, `E` with their `Fintype`/`DecidableEq` instances -- GENUINELY-FREE
  carriers of the guarded source (`05:36--37`).
* `hshape : Lh + Bcap <= Hmax` -- not a quantity but `06:808`'s own inequality,
  supplied as the banked `ParameterSchedule.k2Star_meets_search`'s own
  hypothesis.  Part 9 does not discharge it, because discharging it means
  evaluating `eq:Hmax`; Part 11 evaluates `eq:Hmax` and discharges it there
  (`HmaxFor_shape`), which is what makes that part's search facts
  unconditional.

Zero source-defined quantities are *assigned* anywhere in Parts 9 or 10, and
`L_h` is carried only at the banked display's own signature, never as an input
of a `(Public, K)` accessor.

## Statement poles and hypothesis consistency

* **The one existential is `k2Exists`, and the trivial witness fails it** --
  see its docstring: the first clause excludes every `k < 2^19` and the second
  is unbounded in `H_max`, so no constant natural inhabits the predicate.  The
  witness exhibited is the paper's own `k_2^*` and nothing else.
* **Every other deliverable is a named-def claim about a pinned banked
  construction**, which is the disposition `STATEMENT POLES` prefers.
* **Hypothesis consistency.**  Every Part-9 hypothesis bundle is the single
  inequality `L_h + B_cap <= H_max`, which is satisfiable (take
  `H_max = L_h + B_cap`), and Part 10's declarations carry no hypothesis at
  all beyond the banked carriers' own fields.  No conditional shell is
  introduced: in particular **Parts 9--11** state no theorem whose hypothesis
  is `t_2 <= q_2` or `4 t_2 <= q_2`, because no `(P, K)` at which either holds
  is exhibited anywhere on this route (the `cc-t7i` SP-3 finding, honoured by
  omission rather than by a label).

  **Extended, not weakened, at `cc-t7l` (Part 12).**  Part 12 states no such
  theorem either, and no declaration anywhere in this module carries the row in
  hypothesis position.  What Part 12 adds is the *reason* the omission is
  permanent on this domain: the row is not derivable at an arbitrary
  `(Public, K)` here, and the paper discharges it elsewhere -- at
  `sec:effective-cutoff`, as item (v) of `06:1197--1226`. -/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **Receipt: the `log_2 q` slot of `eq:Hmax` (`06:759`) is exact.**  `06:515`
prints `q = 2^{A_wrap L_P^2}`, so `q` is a power of two and the integer
base-two logarithm returns the exponent with no rounding -- the same
disposition the banked `LevelStepConstruction.lsFor` records for `log_2 s` at
`06:432`.  This is a statement about the banked `qFor` accessor alone; it does
**not** evaluate `eq:Hmax`, which Part 11 does.  It is what certifies that
Part 11's `lqFor` -- the third summand of `06:759` and the fourth argument of
`06:565` -- is the exact base-two logarithm and not a rounded one.  General in
the two carriers, the public record and the configuration.  PROVED. -/
theorem lgQFor_eq (P : LevelPublicInput V E) (K : LevelConfig) :
    Nat.log 2 (LevelStepConstruction.qFor P K)
      = K.Awrap * (LevelStepConstruction.LPFor P K) ^ 2 := by
  simp only [LevelStepConstruction.qFor, ParameterSchedule.qWrap_eq_two_pow]
  exact Nat.log_pow (by norm_num) _

/-- **`m_{1,i} = |Rows(M_1^{(i)})|`** (`14:1625`) computed at the banked
Stage-1 row carrier `Rows(M_1) = [q_1] x Rows(R)`
(`eq:stage1-universes-and-value`, `07:144`): the cardinality is
`q_1 * m_R`.  Nothing is assumed about the two factors; both are the
schedule's own.  This is the **third** argument of
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})`.

  (**Reason corrected at `cc-t8b`, banked at `cc-t8c`.**  The `cc-t7j` bytes
  added "the call itself is not made in this module, because its second argument
  is not derived (see the Part-10 header)".  The *conclusion* still holds -- the
  paper's literal successful call is not made anywhere in this module -- but the
  *reason* given was already stale when it was written and is withdrawn:
  `cc-t7k` derives `t_{2,i}` as `t2For` in Part 11.  What actually blocks the
  call is the structural row `4 t_2 <= q_2` of `06:835`, exactly as Part 12
  records.)  PROVED. -/
theorem stepRowsOne_card (P : LevelPublicInput V E) (K : LevelConfig) :
    Fintype.card (LevelStepConstruction.StepRowsOne P K)
      = (LevelStepConstruction.stage1BindingFor P K).q₁ * P.mR := by
  simp [LevelStepConstruction.StepRowsOne, StageOneInterlace.Stage1Rows,
    FiniteSlots.Slot]

/-- **The builder's third argument is at least `6`.**  `q_1 = 2^a - 2 >= 6` is
the banked `FiniteSlots.Stage1SlotBinding.six_le_q₁` (from the frozen `a >= 3`),
and `m_R > 0` is `P3`'s own field (`05:36--37`).  This is what makes the value
carrier non-degenerate at the level step, so the eventual non-vacuity of the
balanced family will be *derived* rather than assumed.  PROVED. -/
theorem six_le_stepRowsOne_card (P : LevelPublicInput V E) (K : LevelConfig) :
    6 ≤ Fintype.card (LevelStepConstruction.StepRowsOne P K) := by
  rw [stepRowsOne_card]
  calc (6 : ℕ) ≤ (LevelStepConstruction.stage1BindingFor P K).q₁ :=
        (LevelStepConstruction.stage1BindingFor P K).six_le_q₁
    _ ≤ (LevelStepConstruction.stage1BindingFor P K).q₁ * P.mR :=
        Nat.le_mul_of_pos_right _ P.mRpos

/-- The builder's `m > 0` guard (`14:1781`) at the level step's third argument,
derived rather than assumed.  PROVED. -/
theorem stepRowsOne_card_pos (P : LevelPublicInput V E) (K : LevelConfig) :
    0 < Fintype.card (LevelStepConstruction.StepRowsOne P K) :=
  lt_of_lt_of_le (by norm_num) (six_le_stepRowsOne_card P K)

/-! ## Part 11: the terminal-uniform chain, `u_term`, and the **evaluated**
`L_h` at `(Public, K)` (`eq:terminal-uniform-bounds` `06:716--731`,
`eq:Hmax` `06:754--762`)

### Ownership adjudication first (the `cc-t7j` lesson, executed through the index)

`06:757` is `L_h = max{b_2, b_T} + max{q, u_term} + 4`.  Before writing a
single byte this round, the two candidates the surface index lists for that
line were opened and read:

* **`ParameterSchedule.LhSched` (`:1422`) is the DISPLAY OWNER.**  It is
  `LhSched b2 bT q uterm = max b2 bT + max q uterm + 4`, i.e. `06:757` reified
  as a function of its own four inputs.  Every `L_h` below is that function
  applied to evaluated arguments; **no second defining implementation of any
  banked schedule function is introduced in this module.**

  That is the accurate claim, and it is deliberately narrower than "no second
  copy of the display body is written", which would be false.  The body does
  appear again, twice and by design: `LhFor_eq_display` restates `06:757`'s
  right-hand side as a `rfl` receipt read back off `LhSched`, and `lqFor`
  spells the exponent `A_wrap L_P^2` of `06:515` directly.  The second of
  those is recorded here as the **accepted canonical representation** of
  `log_2 q` -- the same representation the banked
  `Section5Admissibility.lqOf` uses, no distinct display-owner definition of
  `log_2 q` existing, and the one Part 10's `lgQFor_eq` certifies exact.
  Neither is a competing definition of a banked function.
* **`Section5Admissibility.LhOf` (`:895`) is the STORED-WIDTH EVALUATION.**  It
  evaluates the same display on a `ScheduleContext`, whose third field is the
  legacy `StageTwoWidths` record.  Two of its four arguments -- `q` through
  `qOf -> LPOf -> P0Of -> lq2Of = C.W.r_2`, and `u_term` through
  `uTermOf -> deltaTermOf -> ETOf -> e0maxOf -> krefOf -> CcertOf -> lq2Of`
  -- read that stored field.  So `LhOf` is a *legitimate* evaluation of `06:757`
  on the stored presentation, and it is **not** the paper's own domain:
  `proc:level-step` has exactly two inputs (`05:320`) and `def:level-parameters`
  says the parameter record has "no stored width ... fields" (`05:188--189`).

The chain is therefore **already banked, and is REWIRED here rather than
re-reified**: this part adds the `(Public, K)` presentation of the same
displays -- the `Of`/`At` versus `For` split that `LevelStepConstruction`
Part 1 already carries for `B_pub, z_R, A_pre, u, s, delta_v, zeta, eta_R,
ceil(log_2 U_0), q_2, r_2, A_*, a, log_2 s, B_cap, C_cert, P_0, L_P, q,
delta_U, Q` -- and carries it the rest of the way, to `u_term` and `L_h`.
`ParameterSchedule.LhSched`, `.vMax`, `.HmaxSched`, `.k2`, `.t2`,
`.theta`, `.Ltheta`, `.kref`, `.e0maxSched`, `.EB`, `.ET`, `.deltaTerm`,
`.uTerm`, `.etaC`, `ScheduleTemplateResidue.b2`, `.bT`,
`WrapperProtectedEarly.Btheta`, `.Lq` are all **consumed by pin**; not one of
them is restated.

### What this REFUTES in the `cc-t7i`/`cc-t7j` Part-10 header (corrected above)

Those rounds recorded that `u_term` "has **no** `(Public, K)` accessor anywhere
on this route", and further that `k_ref`'s own inputs "`t_0(3/5)`, `mu_P`,
`B_theta`, `L_theta` are not derived at `(Public, K)` either".  Read against
the frozen displays and the banked surface, the second half is an
**under-collection** of exactly the kind the `cc-t7j` rule was minted for, and
it is corrected here:

* `t_0(3/5)` is the **fixed route constant** `Section5Admissibility.t0clogOf`
  (`A:104--107`, "`t_0(3/5)` means the single integer `t_cert`"): it takes no
  context at all;
* `mu_P` is a banked constant of `WRAPPER-PROTECTED-EARLY-001` and appears only
  *inside* `ParameterSchedule.EB`;
* `B_theta = B_pair` (`06:718`) is `WrapperProtectedEarly.Btheta` at `theta`,
  and `L_theta = clog_2(1/theta)` (`06:535`) is `WrapperProtectedEarly`'s
  sibling `ParameterSchedule.Ltheta` at `Q` -- and `theta` and `Q` are
  `eq:Q-theta-choice` (`06:525--538`) at the **already derived** `Q_0`, whose
  `(Public, K)` accessor is the banked `LevelStepConstruction.QFor`;
* the remaining inputs of `eq:tref-search` (`06:558--572`) are `c_seed` (a
  `LevelConfig` field), `L_P` (`LevelStepConstruction.LPFor`), `C_cert`
  (`.CcertFor`) and `log_2 q` (the exponent of `.qFor`, exact by `lgQFor_eq`
  in Part 10).

So every input of the chain `k_ref -> e_0^max -> E_B -> E_T -> delta_term ->
u_term` is derivable at `(Public, K)` today, and the only thing missing was the
chain itself.  The **first** half of the old claim was literally true and
stays true as a statement about names: before this round no `uTermFor` existed.
It is the *inference* from that to "`L_h` cannot be evaluated" that was wrong.

### Why these are not duplicates of the banked context accessors

For all but two of the displays below, the banked context accessor computes a
**different value** from the accessor defined here, because it reads the stored
`log_2 q_2 = C.W.r_2` where this chain reads the derived `r2For`.  A receipt of
the Part-1c form `XFor P K = XOf (ctxAt P K W)` would therefore be **FALSE**
for `theta, L_theta, log_2 q, k_ref, e_0^max, E_B, E_T, delta_term, u_term,
b_2, v_max, L_h, H_max, k_2, t_2`, and none is claimed.  The exact two whose
inputs are **independent of the stored width record `W`** -- `eta_C`
(`06:206--211`, whose inputs are the derived source scale `s` *and* the public
density `delta_v(G)`, neither of them a `W` field) and `b_T` (`06:241`, whose
only input is `s`) -- **do** coincide definitionally, and each carries its
Part-1c receipt below.  `W`-independence, not "`s`-only", is the common
property, and the distinction is not cosmetic: `eta_C` is not a function of
`s` alone, since `06:209` reads `nu_V delta_v(G)/16`.  `W`-independence is
also exactly what the two `rfl` receipts certify, because each is stated at an
arbitrary `W`.  For the
remainder the receipts are stated at the deepest banked *derived* context
accessor that exists (`MechanicalCompilerResidue.QAt`, `.LPAt`, `.CcertAt`,
`.q1At`, all of which read `DerivedWidths.r2At`), or, where the derived chain
runs past the banked surface entirely, as the pin itself: which banked
reification, at which arguments, in the display's own print order.  Every
receipt is `rfl`, and each holds at an arbitrary stored record `W`, so the
receipts also say that the value does not depend on `W`.

The two coincidences are exactly where they must be, and the asymmetry is the
whole content of the migration; it is recorded rather than papered over.

### What is still NOT discharged, and stays registered

Landing `t_2` at `(Public, K)` supplies the **second** argument of
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})` (`14:1621--1632`); Part 10 already supplies
the third and `LevelStepConstruction.q2For` the first.  The call is
nonetheless **not made here nor anywhere below**, and no stored family, `Pi_i`
record or canonical-inhabitation credit is claimed, because `06:830--831`
requires the structural row `4 t_2 <= q_2` (`eq:stage2-structural-gates`, the
display `06:832--849`, this row at `06:835`) to be *verified* "before
constructing the balanced family", and no theorem on this route concludes it at
any `(P, K)`.  That is the `cc-t7i` SP-3 finding, honoured by omission again.

**Anchor corrected at `cc-t7l` (Part 12).**  The earlier bytes here cited
`06:744--745`; that sentence is about `eq:terminal-wrapper-gates`, a different
display.  For *this* row the paper's own placement is `06:1219--1220` -- item
(v) of the finite condition list `06:1197--1226` that `sec:effective-cutoff`
(`06:1169--1177`) discharges beyond a threshold.  Part 12 also records, as a
kernel-checked fact about this development's unrestricted `(Public, K)` domain
and not as a claim about the paper, that the row is not derivable there.  The
remainder of `S5-BALANCED-FAMILY-LEVELSTEP-001` is therefore: **the cutoff
discharge of the row**, and the call that discharge will license.  The `L_h`
half of that row is discharged by this part.

One further residual is recorded rather than crossed: the defining property of
`u_term` (`06:726--728`, "`u_term delta_term >= 8s`") is the banked
`ParameterSchedule.uTerm_spec` at a *positive* terminal density, and
`0 < delta_term` needs `0 < eta_R`, whose sole banked owner is
`Section5Admissibility.etaROf_pos` -- stated at a `ScheduleContext`, and built
from `dvOf_pos`/`zetaOf_pos`, which have no display-domain owners.  Re-deriving
them at `(Public, K)` would duplicate two banked proof bodies, so the positive
form is **not** stated here; migrating `dvOf_pos`/`zetaOf_pos` to the display
domain is its own rewiring and is REGISTERED, not attempted.  What *is* proved
below without any positivity is `uTermFor_pos`: `u_term` is a power of two, so
the chain never degenerates to `0`.

### Canonical inhabitation

This part introduces **no structure and no new type** -- every declaration
returns `ℕ` or `ℝ` -- so there is no synthetic-inhabitant question to answer.
The values are total at `(Public, K)`, and the line that fixes that pair as
the schedule's own domain is `05:104--106`: "For fixed `(Public, K)`, the
equations of `\Cref{sec:parameters}` are a deterministic straight-line program
up to the balanced-family choice."  That is the citation for the domain, and
the only one.

`05:320` is a **different** statement and is deliberately not cited for it.
It is `proc:level-step`'s precondition, and its two inputs are
`(Public, Pi)` -- a public input and a *typed parameter record* -- with
`Pi = (K, N_2, c_2)` by `def:level-parameters` (`05:174--180`).  So `05:320`
supplies `Public` as the procedure's first input, and the fact that no
admissibility proof is an input; it does **not** say that the schedule's
second input is `K`.  Conflating the two would substitute a record for a
configuration.  No numeral is assigned to any source-defined quantity anywhere
below.

### Reader counterparts

**None claimed** -- and the sweep behind that is recorded exactly, because the
first wording of this block was overbroad.  A fixed-string sweep of the 41-page
reader artifact's own source confirms that it prints **no** `theta`, `L_theta`,
`k_ref`, `e_0^max`, `E_B`, `E_T`, `delta_term`, `u_term`, `v_max`, `L_h`,
`H_max` or `k_2` anywhere; its only Section-6-adjacent displays (`q`, `Q`,
`q_2`, `b_2`) are already claimed by `PublicRecords`, `GuardedSourceSlab` and
`ScheduleTemplateResidue`.  **Four** of the symbols this part evaluates **do**
occur in the reader, and the blanket "prints no parameter schedule" was wrong
about them: `b_2`, already accounted for in the previous sentence as
`ScheduleTemplateResidue.b2`'s claim on `03:276--279`, together with the three
itemized below.  Each is itemized instead:

* **`b_T` -- the reader prints the formulas, inside a larger display.**
  `03-parameterized-construction.tex:64--67` prints the same `b_T` and `x_T`
  formulas as frozen `06:239--243`
  (`b_T = 2^{j_{49}(k_T)}, x_T = 2^{-b_T}`), but the two display environments
  are **not** coextensive: the reader's display additionally prints
  `b_1 = 2^{j_{49}(a-2)}`, which frozen `06:239--243` does not.  It is not
  unclaimed and it is not claimed here: the reader display `03:64--67` is
  already claimed by **`SCHEDULE-001` / `ParameterSchedule.j49`**
  (`ParameterSchedule.lean:131--136`), and
  `ScheduleTemplateResidue.lean:129--134` records that ownership expressly.  It
  is **not** claimed by `ScheduleTemplateResidue.bT`, whose own docstring
  (`:731--732`) says `j49` is "*not* redefined here" -- that module consumes the
  banked primitive by pin rather than claiming the reader display.  (The
  reader's sibling `b_2` display `03:276--279` *is* claimed by
  `ScheduleTemplateResidue.b2`; that parallel does **not** extend to `b_T`, and
  reasoning by analogy from it was the source of an earlier inaccurate
  attribution here.)  `bTFor`'s own header says so.
* **`t_2` -- present, but never as this part's display.**  It occurs
  repeatedly in reader `03`, always as a *hypothesis parameter* of the
  balanced-family lemma (`03:72--77`: `q_2, t_2` powers of two, `16 | t_2`,
  `4 t_2 <= q_2`, `t_2 <= 2^{b_1}`), never as `eq:t2-search`'s least-search
  definition.  So `t2For` genuinely has no reader counterpart.
* **`eta_C` -- present, but never as this part's display.**  It occurs twice
  (`A-stage4-details.tex:217, 220`) as a *referenced* public tolerance, not as
  the `eq:eta-choice` display.  So `etaCFor` has no reader counterpart either.

No declaration of Part 11 claims a reader item, and no reader item is claimed
twice.  Per the repository contract every declaration below carries its own
`Reader counterpart` line in its own header comment -- the seventeen `def`s,
the seven pin receipts and the seven aux lemmas alike; this block statement
summarizes them and does not stand in for them.

### Numeral screen for Part 11 (every numeric literal in a declaration statement)

Definition bodies are included, since a `def`'s body *is* its statement.  The
universe index `.{0}` is a universe level, not a numeric literal; it is fixed
once for the same reason Part 9 fixes it (`02:799--806`, `m_HS` "is selected
once and hardwired into the finite code of `A_cert`").

01. `etaCFor` -- none.
02. `thetaFor` -- none (`c_theta` and the `2Q` are inside the banked `theta`).
03. `LthetaFor` -- none (the `160 Q` of `06:539` is inside the banked
    `Ltheta`).
04. `lqFor` -- `2`.  CANONICAL-FORM: the square in `q = 2^{A_wrap L_P^2}`
    (`06:515`), the same exponent shape the banked `qWrap` carries and that
    Part 10's `lgQFor_eq` certifies exact.
05. `krefFor` -- none (`2^19`, the two `2^{...}` clauses and `t_ref = 2^{k_ref}`
    are inside the banked `kref`).
06. `e0maxFor` -- none (the three cover bases and the displayed arithmetic are
    inside the banked `e0maxSched`).
07. `EBFor` -- none (`512`, `mu_P` and `1 - vartheta` are inside the banked
    `EB`).
08. `ETFor` -- none.
09. `deltaTermFor` -- none (`8 mu_P max{1, E_T}` is inside the banked
    `deltaTerm`).
10. `uTermFor` -- none (`8s` is inside the banked `uTerm`).
11. `bTFor` -- none (`2^{j_49(k_T)}` and `s/4` are inside the banked `bT`).
12. `b2For` -- none (`32` and the `clog_2` base are inside the banked `b2`).
13. `vMaxFor` -- none (the branch `2` of `06:756` is inside the banked `vMax`).
14. `LhFor` -- none (the two maxima and the additive `4` of `06:757` are inside
    the banked `LhSched`).
15. `HmaxFor` -- none (`8 q_1` and the `+ 10` of `06:759` are inside the banked
    `HmaxSched`).
16. `k2For`, 17. `t2For` -- none.
18. `etaCFor_pin`, 19. `bTFor_pin`, 20. `b2For_pin` -- none.
21. `thetaLthetaFor_pins` -- none.
22. `lqKrefFor_pins` -- `2`.  CANONICAL-FORM: the same square of `06:515` as
    row 04.
23. `terminalBounds_pins` -- none.
24. `HmaxSearchFor_pins` -- none.
25. `uTermFor_pos` -- `0`.  CANONICAL-FORM: `u_term` is "the least power of
    two with ..." (`06:727--728`), and a power of two is positive.
26. `LhFor_eq_display` -- `4`.  CANONICAL-FORM: the additive margin printed in
    `06:757` itself, which this receipt reads back off the banked `LhSched`.
27. `uTermFor_le_LhFor` -- none.
28. `ten_add_qFor_le_LhFor` -- `10`.  EVALUATED: `6 + 4`, where `6` is the
    `LevelConfig` floor `c_b >= 6` of `06:56--62` reaching `b_2` through the
    banked `ScheduleTemplateResidue.six_le_b2`, and `4` is `06:757`'s own
    additive margin.  It is not a chosen bound.
29. `HmaxFor_shape` -- none.
30. `K2Pred_at_k2For` -- none.
31. `mHS_le_k2For` -- none.

Every occurrence is classified, and none stands where a source-defined quantity
belongs.  In particular `L_h`, `u_term`, `b_2`, `b_T`, `q`, `Q`, `theta`,
`L_theta`, `k_ref`, `e_0^max`, `E_B`, `E_T`, `delta_term`, `H_max`, `k_2`,
`t_2`, `q_1`, `q_2`, `B_cap` and `C_cert` never appear as literals.

### Binder-provenance table for Part 11

Part 11 introduces **no structure and no field**, so every row is a binder.
There are exactly four kinds, and **zero source-defined quantities remain
free** -- which is the point of the round, since `L_h` was the free binder the
`cc-t7i` gate confirmed.

* `P : LevelPublicInput V E` -- GENUINELY-FREE.  `05:174` fixes `Public`
  abstractly and `05:320` makes it the procedure's first input.
* `K : LevelConfig` -- GENUINELY-FREE.  `02:178--179`, "Fix one universal level
  configuration `K_*` ...": the paper fixes it abstractly and assigns it no
  value.
* `V`, `E` with their `Fintype`/`DecidableEq` instances -- GENUINELY-FREE
  carriers of the guarded source (`05:36--37`).
* `W : StageTwoRelaxed.StageTwoWidths` in the five receipts that mention it --
  a **universally quantified** stored record occurring on the receipt's own
  right-hand side (never in a definition, and never with a chosen value).  It
  is the Part-1c device: because the left-hand side has no `W` and the two
  sides are equal for every `W`, the receipt *says* that the banked context
  presentation's value at that display is independent of the stored record.
  No `W`-binder below is unused in its conclusion.

`L_h`, `u_term`, `b_2`, `b_T`, `theta`, `L_theta`, `k_ref`, `e_0^max`, `E_B`,
`E_T`, `delta_term`, `v_max`, `H_max`, `k_2` and `t_2` are all SOURCE-DEFINED
and every one of them is now an **evaluated accessor** rather than a binder.
Part 9's three binders `(L_h, B_cap, H_max)` stay exactly as they were -- they
are the banked search display's own inputs -- and Part 11 supplies the values
Part 9 was general in, without changing a byte of it. -/

/-- **`eta_C`** (`eq:eta-choice`, first line, `06:206--211`) at the paper's own
two inputs, consumed by pin from the banked `ParameterSchedule.etaC` at the
derived source scale and the public record's own density.  This is the first of
the two displays in this part whose inputs are **independent of the stored
width record `W`** -- here the source scale `s` and the public density
`delta_v(G)` of `06:209`, neither of them a `W` field -- so it agrees with the
banked context accessor definitionally (`etaCFor_pin`).  It is *not* an
`s`-only display: `delta_v(G)` is a second, genuine input.  Reader counterpart:
none -- `eta_C` occurs in the reader only as a referenced public tolerance
(`A-stage4-details.tex:217, 220`), never as this display. -/
noncomputable def etaCFor (P : LevelPublicInput V E) (K : LevelConfig) : ℝ :=
  ParameterSchedule.etaC (LevelStepConstruction.sFor P K)
    (LevelStepConstruction.dvFor P)

/-- **`theta = c_theta/(2Q)`** (`eq:Q-theta-choice`, display line `06:533`) at
`(Public, K)`, consumed by pin from the banked `ParameterSchedule.theta` at the
banked derived bridge width `LevelStepConstruction.QFor`.  No reader
counterpart. -/
noncomputable def thetaFor (P : LevelPublicInput V E) (K : LevelConfig) : ℝ :=
  ParameterSchedule.theta (LevelStepConstruction.QFor P K)

/-- **`L_theta = clog_2(1/theta)`** (`eq:Q-theta-choice`, display line
`06:535`) at `(Public, K)`, consumed by pin from the banked
`ParameterSchedule.Ltheta`, which is that ceiling logarithm read at the natural
argument `1/theta = 160 Q` of `06:539`.  No reader counterpart. -/
noncomputable def LthetaFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.Ltheta (LevelStepConstruction.QFor P K)

/-- **`log_2 q = A_wrap L_P^2`** (`eq:q-deltaU`, display line `06:515`) at
`(Public, K)`: the exponent of the banked `qFor`, which Part 10's `lgQFor_eq`
certifies is exactly `Nat.log 2 (qFor P K)` because `06:515` makes `q` a power
of two.  It is the fourth argument of `eq:tref-search` (`06:565`) and the third
summand of `eq:Hmax` (`06:759`).  No reader counterpart. -/
noncomputable def lqFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  K.Awrap * LevelStepConstruction.LPFor P K ^ 2

/-- **`k_ref`** (`eq:tref-search`, `06:558--568`) at `(Public, K)`: the least
integer satisfying the frozen three-clause search, consumed by pin from the
banked `ParameterSchedule.kref`.

Its six arguments are, in the display's own order: the configuration field
`c_seed` (`06:562`), the derived `L_P` (`06:562`), the fixed route constant
`clog_2(t_0(3/5))` of `06:563` -- the banked `Section5Admissibility.t0clogOf`,
which `A:104--107` fixes as "the single integer `t_cert`" and which takes no
context -- the derived `C_cert` (`06:565`, `06:567`), `log_2 q` (`06:565`) and
`L_theta` (`06:565`, `06:567`).  No numeral is assigned to any of them.  No
reader counterpart. -/
noncomputable def krefFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.kref K.cseed (LevelStepConstruction.LPFor P K)
    Section5Admissibility.t0clogOf (LevelStepConstruction.CcertFor P K)
    (lqFor P K) (LthetaFor P K)

/-- **`e_0^max`** (`eq:cover-bounds`, display `06:639--652`) at `(Public, K)`,
consumed by pin from the banked `ParameterSchedule.e0maxSched`, which carries
the three least searches at the three frozen bases `18/25`, `1 - eta_C` and
`99/100` and the displayed arithmetic at `t_ref = 2^{k_ref}`.  The schedule's
contribution is the choice of the bases and of `k_ref`, and both are supplied
here from the derived chain.  No reader counterpart. -/
noncomputable def e0maxFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.e0maxSched (thetaFor P K) (etaCFor P K) (krefFor P K)

/-- **`E_B`** (`eq:terminal-uniform-bounds`, display lines `06:720--722`) at
`(Public, K)`, consumed by pin from the banked `ParameterSchedule.EB`.  Its
`B_theta` slot is `06:718`'s `B_theta = B_pair` -- the banked
`WrapperProtectedEarly.Btheta` at this chain's own `theta`, identified with the
pair cover number by the banked `ParameterSchedule.schedule_Btheta_eq_Bpair` --
and its `L_q` slot is `06:719`'s `L_q = ceil(log_2(2q)) + 1`, the banked
`WrapperProtectedEarly.Lq` at the derived first-wrapper width.  `mu_P`,
`vartheta = 9/16` and the frozen ceiling live inside `EB`.  No reader
counterpart. -/
noncomputable def EBFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.EB (WrapperProtectedEarly.Btheta (thetaFor P K))
    (WrapperProtectedEarly.Lq (LevelStepConstruction.qFor P K))
    (LevelStepConstruction.sFor P K) (e0maxFor P K)
    (LevelStepConstruction.etaRFor P K)

/-- **`E_T = ceil(e_0^max/(1 - vartheta)) + E_B`**
(`eq:terminal-uniform-bounds`, display line `06:723`) at `(Public, K)`,
consumed by pin from the banked `ParameterSchedule.ET`.  No reader
counterpart. -/
noncomputable def ETFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.ET (e0maxFor P K) (EBFor P K)

/-- **`delta_term = eta_R/(8 mu_P max{1, E_T})`**
(`eq:terminal-uniform-bounds`, display lines `06:724--725`) at `(Public, K)`,
consumed by pin from the banked `ParameterSchedule.deltaTerm`, whose frozen
`max{1, .}` keeps the density defined at `E_T = 0`.  No reader counterpart. -/
noncomputable def deltaTermFor (P : LevelPublicInput V E) (K : LevelConfig) :
    ℝ :=
  ParameterSchedule.deltaTerm (LevelStepConstruction.etaRFor P K) (ETFor P K)

/-- **`u_term`**, "the least power of two with `u_term delta_term >= 8s`"
(`eq:terminal-uniform-bounds`, display lines `06:726--728`) at `(Public, K)`,
consumed by pin from the banked `ParameterSchedule.uTerm`.

This is the accessor whose absence blocked `eq:Hmax` for five rounds, and the
one the Part-10 header recorded as having "no `(Public, K)` accessor anywhere
on this route".  It has one now, and it is the paper's own closed form -- the
banked least-power-of-two-above-the-floor primitive at the derived terminal
density -- not a numeral shortcut of it.  No reader counterpart. -/
noncomputable def uTermFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.uTerm (LevelStepConstruction.sFor P K) (deltaTermFor P K)

/-- **`b_T = 2^{j_49(k_T)}`** (`06:241`, the second name of the auxiliary
Stage-3 depth array `06:237--243`) at `(Public, K)`, consumed by pin from the
banked `ScheduleTemplateResidue.bT`, which carries `k_T = log_2(s/4)` of
`06:239` inside it.  This is the second of the two displays in this part whose
inputs are **independent of the stored width record `W`** -- here the source
scale `s` alone -- so it agrees with the banked context accessor
definitionally (`bTFor_pin`).

Reader counterpart: none claimed here, and the earlier flat "no reader
counterpart" was inaccurate.  The reader **does** print these formulas, at
`03-parameterized-construction.tex:64--67`: the same `b_T` and `x_T` formulas
as frozen `06:239--243` (`b_T = 2^{j_{49}(k_T)}, x_T = 2^{-b_T}`), inside the
reader's larger display, which additionally prints `b_1 = 2^{j_{49}(a-2)}`.
That reader display is already claimed by **`SCHEDULE-001` /
`ParameterSchedule.j49`** (`ParameterSchedule.lean:131--136`), as
`ScheduleTemplateResidue.lean:129--134` expressly records -- **not** by
`ScheduleTemplateResidue.bT`, which consumes `j49` by pin and does not claim
the display.  So nothing is claimed twice, and nothing is left unowned. -/
noncomputable def bTFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ScheduleTemplateResidue.bT (LevelStepConstruction.sFor P K)

/-- **`b_2 = ceil(log_2(32 s q_1 m_R)) + c_b`** (`eq:b2-choice`, display line
`06:424`) at `(Public, K)`, consumed by pin from the banked
`ScheduleTemplateResidue.b2`.

`m_R = |Rows(R)|` is the public record's own field (`06:422`, "Writing
`m_R = |Rows(R)|`"), `q_1` is the banked field-derived
`FiniteSlots.Stage1SlotBinding.q₁` at `stage1BindingFor P K` -- the same
reading Part 10 uses, so no second `q1Stage1` application is introduced -- and
`c_b` is the configuration field of `06:56--62`.  `06:429` records that `b_2`
"is fixed before `t_2`", which is exactly the order this part evaluates in.  No
reader counterpart: the reader's `03-parameterized-construction.tex:276--279`
display is already claimed by the banked `ScheduleTemplateResidue.b2`. -/
noncomputable def b2For (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ScheduleTemplateResidue.b2 (LevelStepConstruction.sFor P K)
    (LevelStepConstruction.stage1BindingFor P K).q₁ P.mR K.cb

/-- **`v_max = max{2, q, u_term}`** (`eq:Hmax`, display line `06:756`) at
`(Public, K)`, consumed by pin from the banked `ParameterSchedule.vMax`: the
shared Localized-Extension alphabet floor of the level, now evaluated rather
than carried.  No reader counterpart. -/
noncomputable def vMaxFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.vMax (LevelStepConstruction.qFor P K) (uTermFor P K)

/-- **`L_h = max{b_2, b_T} + max{q, u_term} + 4`** (`eq:Hmax`, display line
`06:757`) at `(Public, K)` -- **the target of this round**, consumed by pin
from the display owner `ParameterSchedule.LhSched` and applied to four
evaluated arguments, none of them free.

`06:752--753` is the sentence that makes this the right domain: "All uses of
Localized Extension in a level share one physical balanced family.  To choose
it, put ...".  A level is a `(Public, K)`, so `L_h` is a function of
`(Public, K)`; carrying it as a free binder -- the `cc-t7i` SP-2 defect -- or
pinning only two of its four arguments -- the `cc-t6w-r1` half-migration defect
-- are both avoided here by evaluating all four.  No reader counterpart. -/
noncomputable def LhFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.LhSched (b2For P K) (bTFor P K)
    (LevelStepConstruction.qFor P K) (uTermFor P K)

/-- **`H_max = L_h + 8 q_1 + log_2 q + log_2 q_2 + B_cap + 10`** (`eq:Hmax`,
display lines `06:758--759`) at `(Public, K)`, consumed by pin from the banked
`ParameterSchedule.HmaxSched` with the six frozen summands in print order.

Its `log_2 q_2` slot holds the **derived** `LevelStepConstruction.r2For`, not a
stored exponent -- the seam `cc-t6x-r2` closed upstream, kept closed here.  No
reader counterpart. -/
noncomputable def HmaxFor (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.HmaxSched (LhFor P K)
    (LevelStepConstruction.stage1BindingFor P K).q₁ (lqFor P K)
    (LevelStepConstruction.r2For P K) (LevelStepConstruction.bCapFor P K)

/-- **`k_2`** (`eq:t2-search`, `06:763--769`) at `(Public, K)`: the least
integer satisfying the frozen three clauses, consumed by pin from the banked
least search `ParameterSchedule.k2` at this chain's own `L_h`, `B_cap` and
`H_max`.  Read at the single universe `Type` this route's carriers inhabit, for
the reason Part 9 records (`02:799--806`).  No reader counterpart. -/
noncomputable def k2For (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.k2.{0} (LhFor P K) (LevelStepConstruction.bCapFor P K)
    (HmaxFor P K)

/-- **`t_2 = 2^{k_2}`** (`eq:t2-search`, display line `06:770`) at
`(Public, K)`, consumed by pin from the banked `ParameterSchedule.t2`.

This is the **second argument** of `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`
(`14:1621--1625`), the one Part 10 recorded as not derived.  It is derived now.
The call is still not made: `06:830--831` requires the structural row
`4 t_2 <= q_2` (`06:835`) verified first, and no theorem on this route
concludes it -- Part 12 shows none can, at this domain, and places the paper's
discharge at `sec:effective-cutoff`.  See the block docstring.  No reader
counterpart. -/
noncomputable def t2For (P : LevelPublicInput V E) (K : LevelConfig) : ℕ :=
  ParameterSchedule.t2.{0} (LhFor P K) (LevelStepConstruction.bCapFor P K)
    (HmaxFor P K)

/-! ### Part 11.1: the pin receipts

Each receipt names the banked reification the accessor is, and the arguments it
is applied to, in the frozen display's own print order.  The two whose inputs
are **independent of the stored width record `W`** (`eta_C` and `b_T` -- not
"`s`-only": `eta_C` also reads `delta_v(G)`) are stated against the banked
**context** accessor at an arbitrary stored record, in the Part-1c form, and
that arbitrary `W` is precisely what makes them say `W`-independence; the rest
are stated at the deepest banked
**derived** context accessor available, or as the pin itself where the derived
chain runs past the banked surface.  All are `rfl`. -/

/-- **Receipt (`eq:eta-choice`, `06:206--211`).**  `eta_C` at `(Public, K)` is
the banked context accessor at every stored width record: its inputs are the
source scale and the public density, and neither reads `W`.  Reader
counterpart: none.  PROVED by `rfl`. -/
theorem etaCFor_pin (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    etaCFor P K = Section5Admissibility.etaCOf (LevelStepConstruction.ctxAt P K W) :=
  rfl

/-- **Receipt (`06:241`).**  `b_T` at `(Public, K)` is the banked context
accessor at every stored width record: its only input is the source scale.
Reader counterpart: none -- the reader's own display carrying `b_T`
(`03:64--67`) is claimed by `SCHEDULE-001` / `ParameterSchedule.j49`
(`ParameterSchedule.lean:131--136`), not by this receipt and not by
`ScheduleTemplateResidue.bT`.  PROVED by `rfl`. -/
theorem bTFor_pin (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    bTFor P K = Section5Admissibility.bTOf (LevelStepConstruction.ctxAt P K W) :=
  rfl

/-- **Receipt (`eq:b2-choice`, `06:424`).**  `b_2` at `(Public, K)` is the
banked display `ScheduleTemplateResidue.b2` at the banked source scale and the
banked **derived** `q_1` of `MechanicalCompilerResidue.q1At`, whose own
exponent reads `DerivedWidths.r2At`.  Stating it against
`Section5Admissibility.b2Of` would be **false**, because that accessor's `q_1`
runs through the stored `lq2Of C = C.W.r_2`.  Reader counterpart: none -- the
reader's `b_2` display (`03:276--279`) is claimed by the banked
`ScheduleTemplateResidue.b2`, not by this receipt.  PROVED by `rfl`. -/
theorem b2For_pin (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    b2For P K
      = ScheduleTemplateResidue.b2
          (Section5Admissibility.sOf (LevelStepConstruction.ctxAt P K W))
          (MechanicalCompilerResidue.q1At (LevelStepConstruction.ctxAt P K W))
          P.mR K.cb :=
  rfl

/-- **Receipt (`eq:Q-theta-choice`, `06:533` and `06:535`).**  Both names of
the second half of that display are the banked reifications at the banked
**derived** bridge width `MechanicalCompilerResidue.QAt`, at every stored width
record -- so neither depends on `W`.  Reader counterpart: none.  PROVED by
`rfl`. -/
theorem thetaLthetaFor_pins (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    thetaFor P K
        = ParameterSchedule.theta
            (MechanicalCompilerResidue.QAt (LevelStepConstruction.ctxAt P K W))
      ∧ LthetaFor P K
        = ParameterSchedule.Ltheta
            (MechanicalCompilerResidue.QAt (LevelStepConstruction.ctxAt P K W)) :=
  ⟨rfl, rfl⟩

/-- **Receipt (`eq:q-deltaU` `06:515`, and `eq:tref-search` `06:558--568`).**
`log_2 q` is the exponent of the banked derived `L_P`
(`MechanicalCompilerResidue.LPAt`), and `k_ref` is the banked search at the
configuration's `c_seed`, that same derived `L_P`, the fixed constant
`clog_2(t_0(3/5))`, the banked derived `C_cert`
(`MechanicalCompilerResidue.CcertAt`), `log_2 q` and `L_theta` -- the six
inputs of `06:561--567` in print order, at every stored width record.  Reader
counterpart: none.  PROVED by `rfl`. -/
theorem lqKrefFor_pins (P : LevelPublicInput V E) (K : LevelConfig)
    (W : StageTwoRelaxed.StageTwoWidths) :
    lqFor P K
        = K.Awrap
            * MechanicalCompilerResidue.LPAt (LevelStepConstruction.ctxAt P K W) ^ 2
      ∧ krefFor P K
        = ParameterSchedule.kref K.cseed
            (MechanicalCompilerResidue.LPAt (LevelStepConstruction.ctxAt P K W))
            Section5Admissibility.t0clogOf
            (MechanicalCompilerResidue.CcertAt (LevelStepConstruction.ctxAt P K W))
            (lqFor P K) (LthetaFor P K) :=
  ⟨rfl, rfl⟩

/-- **Receipt (`eq:cover-bounds` `06:639--652` and `eq:terminal-uniform-bounds`
`06:716--728`).**  The five names this part evaluates from those two displays
are the five banked reifications, at the arguments the displays print, in their
own order: `e_0^max` at `(theta, eta_C, k_ref)`; `E_B` at
`(B_theta, L_q, s, e_0^max, eta_R)`; `E_T` at `(e_0^max, E_B)`; `delta_term` at
`(eta_R, E_T)`; `u_term` at `(s, delta_term)`.

No banked context accessor is available on the right-hand side for any of
them -- the banked derived chain stops at `QAt` -- and a receipt against the
stored-chain accessors `e0maxOf`, `EBOf`, `ETOf`, `deltaTermOf`, `uTermOf`
would be **false**, since each of those reads `C.W.r_2` through `k_ref` and
`theta`.  What this receipt certifies is the pin: this module introduces no
second defining implementation of either display's banked reification.  Reader
counterpart: none.  PROVED by `rfl`. -/
theorem terminalBounds_pins (P : LevelPublicInput V E) (K : LevelConfig) :
    e0maxFor P K
        = ParameterSchedule.e0maxSched (thetaFor P K) (etaCFor P K) (krefFor P K)
      ∧ EBFor P K
        = ParameterSchedule.EB (WrapperProtectedEarly.Btheta (thetaFor P K))
            (WrapperProtectedEarly.Lq (LevelStepConstruction.qFor P K))
            (LevelStepConstruction.sFor P K) (e0maxFor P K)
            (LevelStepConstruction.etaRFor P K)
      ∧ ETFor P K = ParameterSchedule.ET (e0maxFor P K) (EBFor P K)
      ∧ deltaTermFor P K
        = ParameterSchedule.deltaTerm (LevelStepConstruction.etaRFor P K)
            (ETFor P K)
      ∧ uTermFor P K
        = ParameterSchedule.uTerm (LevelStepConstruction.sFor P K)
            (deltaTermFor P K) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Receipt (`eq:Hmax` `06:756--759` and `eq:t2-search` `06:763--770`).**
The five names this part evaluates from those two displays are the five banked
reifications at the evaluated chain: `v_max` at `(q, u_term)`; `L_h` at
`(b_2, b_T, q, u_term)`; `H_max` at `(L_h, q_1, log_2 q, log_2 q_2, B_cap)`;
and `k_2`, `t_2` at `(L_h, B_cap, H_max)`.  The `log_2 q_2` slot holds the
banked **derived** `LevelStepConstruction.r2For` and never a stored exponent.
Reader counterpart: none.  PROVED by `rfl`. -/
theorem HmaxSearchFor_pins (P : LevelPublicInput V E) (K : LevelConfig) :
    vMaxFor P K
        = ParameterSchedule.vMax (LevelStepConstruction.qFor P K) (uTermFor P K)
      ∧ LhFor P K
        = ParameterSchedule.LhSched (b2For P K) (bTFor P K)
            (LevelStepConstruction.qFor P K) (uTermFor P K)
      ∧ HmaxFor P K
        = ParameterSchedule.HmaxSched (LhFor P K)
            (LevelStepConstruction.stage1BindingFor P K).q₁ (lqFor P K)
            (LevelStepConstruction.r2For P K) (LevelStepConstruction.bCapFor P K)
      ∧ k2For P K
        = ParameterSchedule.k2.{0} (LhFor P K)
            (LevelStepConstruction.bCapFor P K) (HmaxFor P K)
      ∧ t2For P K
        = ParameterSchedule.t2.{0} (LhFor P K)
            (LevelStepConstruction.bCapFor P K) (HmaxFor P K) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Part 11.2: the aux-lemma battery -/

/-- **Aux 11.1 (the terminal donor width never degenerates).**  `0 < u_term` at
every `(Public, K)`, with no side condition at all: `06:727--728` says
`u_term` is a *power of two*, and the banked `uTerm` is that power of two, so
positivity is a fact about the display's shape rather than about the terminal
density.

This is the non-degeneracy the whole chain rests on: a `u_term` collapsing to
`0` would make `max{q, u_term}` -- and with it `L_h` and `H_max` -- silently
ignore the terminal branch of `06:757`.  General in the two carriers, the
public record and the configuration.  Reader counterpart: none.  PROVED. -/
theorem uTermFor_pos (P : LevelPublicInput V E) (K : LevelConfig) :
    0 < uTermFor P K := by
  rw [uTermFor, ParameterSchedule.uTerm, ParameterSchedule.leastPowTwoGe]
  positivity

/-- **Aux 11.2 (`06:757` read back, literally).**  The evaluated `L_h` is the
frozen sum of two maxima and the displayed additive margin, at the four
evaluated arguments -- the receipt that this round *evaluates* the display
rather than approximating it.  It is a `rfl` read-back off the banked
`LhSched`, not a second defining implementation of it.  General.  Reader
counterpart: none.  PROVED by `rfl`. -/
theorem LhFor_eq_display (P : LevelPublicInput V E) (K : LevelConfig) :
    LhFor P K
      = max (b2For P K) (bTFor P K)
          + max (LevelStepConstruction.qFor P K) (uTermFor P K) + 4 :=
  rfl

/-- **Aux 11.3 (the terminal branch of `06:757` really is carried).**
`u_term <= L_h` at every `(Public, K)`.  The banked `Section5Admissibility`
projections of this display are the two *depth* branches (`bTOf_le_LhOf`,
`b2Of_le_LhOf`); the two *width* branches are stated here for the first time,
and on the derived chain rather than the stored one.

**The arithmetic is not re-derived here.**  `06:756--757`'s "the two carriers
stay apart" is owned by the banked `ParameterSchedule.vMax_le_LhSched`
(`:1451`), and this proof consumes that owner **by pin**: `u_term` reaches
`v_max` by the right component of `06:756`'s outer maximum (`le_max_right`),
and the banked projection carries `v_max` the rest of the way to `L_h` at this
part's own four evaluated arguments.  Unfolding `LhSched` locally and closing
by `omega` would restate arithmetic that already has one owner, which is the
fixed-interface defect; the specialization is in the *statement* only.
General.  Reader counterpart: none.  PROVED. -/
theorem uTermFor_le_LhFor (P : LevelPublicInput V E) (K : LevelConfig) :
    uTermFor P K ≤ LhFor P K :=
  le_trans (le_max_right _ _)
    (ParameterSchedule.vMax_le_LhSched (b2For P K) (bTFor P K)
      (LevelStepConstruction.qFor P K) (uTermFor P K))

/-- **Aux 11.4 (the auxiliary depth strictly dominates the wrapper width, by a
derived margin).**  `q + 10 <= L_h` at every `(Public, K)`.

The `10` is `6 + 4`, and both halves are the source's own: `6` is the
`LevelConfig` floor `c_b >= 6` of `06:56--62` reaching `b_2` through the banked
`ScheduleTemplateResidue.six_le_b2`, and `4` is the additive margin printed in
`06:757` itself.  Nothing is chosen.  This is the LANE-GATE-3 non-degeneracy
statement for the evaluated depth: it rules out the reading in which `L_h`
collapses onto `max{q, u_term}` and the Stage-2 depth contributes nothing.
General.  Reader counterpart: none.  PROVED. -/
theorem ten_add_qFor_le_LhFor (P : LevelPublicInput V E) (K : LevelConfig) :
    LevelStepConstruction.qFor P K + 10 ≤ LhFor P K := by
  have hb2 : 6 ≤ b2For P K :=
    ScheduleTemplateResidue.six_le_b2 K.cbge (LevelStepConstruction.sFor P K)
      (LevelStepConstruction.stage1BindingFor P K).q₁ P.mR
  rw [LhFor, ParameterSchedule.LhSched]
  omega

/-- **Aux 11.5 (`06:808`'s shape inequality, DISCHARGED at the scheduled
point).**  `L_h + B_cap <= H_max` at every `(Public, K)`, read off the shape of
`eq:Hmax` through the banked `ParameterSchedule.Hmax_ge_Lh_add_Bcap`.

This is the hypothesis Part 9 carries as the free premise `hshape`, because
Part 9 is general in three unevaluated inputs and cannot discharge it there.
Once `eq:Hmax` is evaluated it is a theorem, and the two lemmas below are the
first unconditional instances of `eq:t2-search` on the paper's own domain.
General.  Reader counterpart: none.  PROVED. -/
theorem HmaxFor_shape (P : LevelPublicInput V E) (K : LevelConfig) :
    LhFor P K + LevelStepConstruction.bCapFor P K ≤ HmaxFor P K :=
  ParameterSchedule.Hmax_ge_Lh_add_Bcap _ _ _ _ _

/-- **Aux 11.6 (`eq:t2-search` holds AT the evaluated `k_2`, unconditionally).**
All three clauses of `06:766--769` hold at `k_2(Public, K)`, with no hypothesis.

This is **not** the banked `Section5Admissibility.DerivedWidths.K2Pred_at_k2At`
and not `MassRedistributionTail.K2Pred_at_k2`: the first is stated at `LhOf`,
`bCapOf` and `HmaxAt`, i.e. at the stored-width reading of `L_h`, and the
second is the general implication this proof consumes by pin.  The statement
here is about the derived chain, and the two agree only when the stored width
is coherent -- which is not assumed anywhere in this module.  General.  Reader
counterpart: none.  PROVED. -/
theorem K2Pred_at_k2For (P : LevelPublicInput V E) (K : LevelConfig) :
    ParameterSchedule.K2Pred.{0} (LhFor P K)
      (LevelStepConstruction.bCapFor P K) (HmaxFor P K) (k2For P K) :=
  MassRedistributionTail.K2Pred_at_k2.{0} (HmaxFor_shape P K)

/-- **Aux 11.7 (`06:766`, third branch, at the evaluated `k_2`).**
`m_HS <= k_2(Public, K)`, unconditionally.

`07:281` prints the inequality itself -- that line reads `k_2 >= m_{HS}` and
`t_2 <= 2^{b_1}`, and nothing else -- so the inequality is correctly sourced
there.  It prints **no gloss** on the clause, and none is quoted here: the
sentence that follows is this module's own explanatory prose.  What the clause
buys, read against the surrounding gate list, is that the General Hard Seed
call at exponent `k_2` is in range; on the paper's own domain that is now a
theorem of the evaluated chain rather than a gate, and it is what a later
`A_bal(q_2, t_2, m_1)` call will need.  Consumed by pin from the banked
`MassRedistributionTail.mHS_le_k2`, whose hypothesis is Aux 11.5.  General.
Reader counterpart: none.  PROVED. -/
theorem mHS_le_k2For (P : LevelPublicInput V E) (K : LevelConfig) :
    HardSeedFacade.mHS.{0} ≤ k2For P K :=
  MassRedistributionTail.mHS_le_k2.{0} (HmaxFor_shape P K)

/-! ## Part 12: the Stage-2 structural row `4 t_2 <= q_2`
(`eq:stage2-structural-gates`) -- WHERE THE PAPER DISCHARGES IT, AND WHY THIS
DEVELOPMENT'S UNRESTRICTED DOMAIN CANNOT

### The frozen interval, read line by line this round

The display is `06:832--849`; its `\label{eq:stage2-structural-gates}` is at
`06:848`.  `06:830--831` is the sentence "Before constructing the balanced
family, verify the following structural conditions:"; `06:834` is the display's
first row `t_2 >= 8 q_1`; and `06:835` is the row this part is about,
`4 t_2 <= q_2`.  The verb is *verify*, not *derive*, and the interval carries no
proof.  (The earlier drafts of this module labelled `06:830--835` the "whole
interval"; it is not -- it covers the verify sentence and two of the display's
thirteen rows.)

Both quantities in the row are already banked, so the row can be read at the
evaluated chain with nothing free:

* `t_2 = 2^{k_2}` (`eq:t2-search`, `06:763--770`) is Part 11's `t2For`, at the
  one-owner `k_2`/`t_2` surface -- `ParameterSchedule.k2` / `.t2` applied to the
  evaluated `(L_h, B_cap, H_max)`.
* `q_2` is `LevelStepConstruction.q2For`, the **derived-width** accessor
  `GuardedSourceSlab.q2 P.G (sFor P K)`, the least power of two at least
  `12 s |E|` of `04:389--391`.  No stored width record is read below.

### Where the paper discharges the row: `sec:effective-cutoff`, item (v)

`06:1197--1226` is the paragraph "A finite list of conditions", and item (v) of
that list (`06:1219--1220`) is "the structural, physical, low-rung, Extension,
and separation gates `eq:stage2-structural-gates`--`eq:stage3-separation-gates`".
That list is the input to `sec:effective-cutoff` (`06:1169--1177`), which finds
one threshold beyond which every listed condition holds and emits the
certificate of `def:effective-schedule-certificate`.  The row is therefore an
*eventually true* cutoff condition, and the paper's own instance of it is
**cutoff-generated**: the frozen text never instantiates the row at an
explicitly displayed `(Public, K)`.

The reader source says the same independently.  At
`reader-facing/sections/03-parameterized-construction.tex:72--73` it prints
"`q_2, t_2` are powers of two, `16 | t_2`, `4 t_2 <= q_2`, and
`t_2 <= 2^{b_1}`" -- governed by "Suppose also that" on the preceding line.  The
reader states the row as a **supposition**, not as a derived identity.

**Nothing in this part refutes the paper's gate, and no declaration below claims
to.**

### What this development can say, and what it cannot

This module's `(Public, K)` domain is unrestricted: `LevelPublicInput` carries
no lower bound on the source and `LevelConfig` none on the scale.  Over that
domain the row is not derivable, because two frozen facts collide:

1. **A floor on `t_2` that no input can lower.**  `06:766`'s first clause is
   `k_2 >= max{4, 2^{19}, m_HS}`, banked as `ParameterSchedule.k2Floor`, so
   `t_2 = 2^{k_2}` is bounded below by an absolute constant at *every*
   `(Public, K)`.
2. **A ceiling on `q_2` that the source alone controls.**  `q_2` is the least
   power of two at least `12 s |E|` (`04:389--391`), bounded by public source
   data with no floor anywhere in `LevelPublicInput`.

The two theorems below record that collision, at the campaign's own banked
synthetic witnesses.  They are **BEYOND-PAPER audits of this encoding's
quantification**, strictly weaker evidence than the paper's application point
and no substitute for it.

### Consequences for the ledger rows -- status, not forecast

* **Item (b) of `S5-BALANCED-FAMILY`** (the level-step instantiation
  `A_bal(q_{2,i}, t_{2,i}, m_{1,i})` of `14:1621--1632`) stays **OPEN**.
* **Item (iii) of `S5-BALANCED-FAMILY-LEVELSTEP-001`** stays **OPEN**.
* The blocking obligation is **registered, not discharged**: the cutoff
  discharge of `eq:stage2-structural-gates` at `sec:effective-cutoff`
  (`06:1169--1177`), reached as item (v) of `06:1197--1226` (`06:1219--1220`),
  whose machinery -- `thm:eff-ledger` and `def:effective-schedule-certificate`
  -- is not formalized on this route.  The **canonical inhabitation** of the row
  is therefore canonical-DEFERRED behind that machinery; no synthetic instance
  discharges it, and the two negative theorems below certainly do not.
* Unchanged by this part, and **partly superseded at `cc-t8b`/`cc-t8c`**: at
  `cc-t7l` the storage step `Pi_i = (K_*, N_{2,i}, c_{2,i})` of `14:1626--1632`
  still needed a canonical linear order on `Rows(M_1^{(i)})` for the increasing
  equivalence `e_i`, because `storedParams`/`storedFamily` above ask for
  `[LinearOrder X_1]` and `LevelStepConstruction.StepRowsOne` carried no such
  instance.  `LevelStepConstruction` Part 8 now supplies exactly that order
  (`12:96`, `14:167`, `04:393`), so **that one missing input is closed**.  It
  changes nothing about this part's subject: the structural row is still not
  derivable here, the paper's literal successful `A_bal` call is still not made,
  and the *balancedness* clause at the level step is still not stated.  Part 13
  below builds only an unconditional **NON-FIDELITY storage-shape probe**.

### What this part deliberately does NOT contain

**No declaration in this module carries `4 t_2 <= q_2` or `t_2 <= q_2` in
hypothesis position** -- here, in any earlier part, **or in Part 13**.  A
hypothesis with no inhabitant exhibited anywhere in the repository is a
conditional shell, so the level-step `A_bal` call, the `q >= t` guard extraction
it would need, `balBuild_eq_some` and `storedFamily_isBalanced` at the
level-step arguments, and the source-count and `k_2`-floor threshold estimates
that would consume the row are **not authored**.  They become authorable exactly
when the cutoff discharge above lands.  Below, the row occurs only under
negation.

  (**Scope note added at `cc-t8b`, banked at `cc-t8c`.**  Part 13 does not
  weaken this paragraph.  It authors the *unguarded* pieces only -- `balN`,
  `balFamily` and `balDescriptor` at the three level-step arguments, through the
  banked `storedFamily`/`storedParams`, which are total given `0 < m` alone --
  and it is labelled **NON-FIDELITY** for precisely the reason this paragraph
  gives: the paper attaches `1 <= t_{2,i} <= q_{2,i}` to those very displays at
  `14:1621--1622`, and this route cannot supply it at any `(Public, K)`.)

No new structure, predicate, axiom or `Prop` abbreviation of the row is
introduced: the one gate-predicate owner on this route is the banked
`Section5Admissibility.WidthGateCore`, whose third conjunct is this row at the
*context* accessors `t2At`/`q2At`, and a second predicate would be a second
owner of one display.  For the record, `eps_2 = 1/(100 t_2)` is set at `06:852`
(`06:850` is the words "Now set", `06:851` opens the equation); no declaration
below asserts it. -/

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY -- the negative pole.**  The frozen row
`4 t_2 <= q_2` (`06:835`) fails at a legal `(Public, K)` of *this development's*
unrestricted domain: the campaign's own banked synthetic witnesses
`PublicRecords.publicInputYes` (`K_3`, `gamma = 1/6`, `Delta = 3`, `D = 3`,
`Y = 0`, `b_0 = bout = 1`, `m_R = n_R = 2`) and `PublicRecords.levelConfigMin`
(`c_b = 6` exactly, `B_s = 1`).

**NON-FIDELITY.**  Neither witness is the paper's object.  The paper's instance
of this row is cutoff-generated at `sec:effective-cutoff` (`06:1169--1177`, via
item (v) of `06:1197--1226`) and needs machinery this route has not built, so
this theorem audits OUR quantification at a point the frozen source never
visits.  It is not a statement about the paper's gate and does not refute it:
the paper states the row as a condition to *verify* (`06:830--831`).

Every field of both witnesses is discharged in `PublicRecords`, including the
promise-independent `SourceCommon` at real degree data, so the pair is legal
here -- no value is chosen by this module and both objects are banked.

The evaluation is a chain of upper bounds, never an assignment: `A_pre <= 240`
from its five branches at this record (`06:111--115`), hence `u <= 3`
(`06:116--117`), hence `s = 2^{B_s u^2} <= 2^9` at `B_s = 1` (`06:118` through
the banked `ParameterSchedule.sScale_eq_pow`), hence `12 s |E| = 12 s * 3 <=
2^{15}` and so `q_2 <= 2^{15}` by the banked `GuardedSourceSlab.q2_le_of_le` --
the "least power of two" minimality of `04:391`, not a computed value of `q_2`.
Against that, `k_2 >= 2^{19}` (`06:766`) gives `4 t_2 >= 2^{16}`.

Reader counterpart: **not claimed.**  The reader does print this row, at
`reader-facing/sections/03-parameterized-construction.tex:72--73`, but under
"Suppose also that" -- as a supposition, never as a stated result -- so there is
no reader item for this theorem to discharge and none is assigned to it.  The
citation is recorded because it corroborates the framing above.  PROVED. -/
theorem not_fourT2LeQ2_at_publicInputYes :
    ¬ 4 * t2For publicInputYes levelConfigMin
        ≤ LevelStepConstruction.q2For publicInputYes levelConfigMin := by
  intro hrow
  have hs : LevelStepConstruction.sFor publicInputYes levelConfigMin ≤ 2 ^ 9 := by
    have hu : LevelStepConstruction.uAuxFor publicInputYes ≤ 3 := by
      unfold LevelStepConstruction.uAuxFor ParameterSchedule.uAux
      have hA : LevelStepConstruction.ApreFor publicInputYes ≤ 240 := by
        unfold LevelStepConstruction.ApreFor ParameterSchedule.Apre
          LevelStepConstruction.BpubFor LevelStepConstruction.zRFor
          LevelStepConstruction.clEFor ScheduleTemplateResidue.Bpub
          ScheduleTemplateResidue.zRpub
        have h1 : Nat.clog 2 2 ≤ 1 := Nat.clog_le_of_le_pow (by norm_num)
        have h2 : Nat.clog 2 (Fintype.card (Fin 3) + 2) ≤ 3 := by
          simp only [Fintype.card_fin]
          exact Nat.clog_le_of_le_pow (by norm_num)
        simp only [publicInputYes]
        omega
      have hinner : Nat.clog 2 (LevelStepConstruction.ApreFor publicInputYes + 16) ≤ 8 :=
        Nat.clog_le_of_le_pow (by omega)
      exact le_trans (Nat.clog_mono_right 2 hinner)
        (Nat.clog_le_of_le_pow (by norm_num))
    rw [LevelStepConstruction.sFor, ParameterSchedule.sScale_eq_pow]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have hb : levelConfigMin.Bs = 1 := rfl
    rw [hb, one_mul]
    calc LevelStepConstruction.uAuxFor publicInputYes ^ 2 ≤ 3 ^ 2 :=
          Nat.pow_le_pow_left hu 2
      _ = 9 := by norm_num
  have hq : LevelStepConstruction.q2For publicInputYes levelConfigMin ≤ 2 ^ 15 := by
    refine GuardedSourceSlab.q2_le_of_le publicInputYes.G _ ?_
    have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
    rw [hcard]
    calc 12 * LevelStepConstruction.sFor publicInputYes levelConfigMin * 3
        ≤ 12 * 2 ^ 9 * 3 :=
          Nat.mul_le_mul_right 3 (Nat.mul_le_mul_left 12 hs)
      _ ≤ 2 ^ 15 := by norm_num
  have hk : 2 ^ 19 ≤ k2For publicInputYes levelConfigMin :=
    (WrapperMassRedistribution.k2_floors_of_K2Pred.{0}
      (K2Pred_at_k2For publicInputYes levelConfigMin)).2.1
  have hk14 : 14 ≤ k2For publicInputYes levelConfigMin :=
    le_trans (by norm_num) hk
  have ht : t2For publicInputYes levelConfigMin
      = 2 ^ k2For publicInputYes levelConfigMin := rfl
  have hlow : (2 : ℕ) ^ 16 ≤ 4 * t2For publicInputYes levelConfigMin := by
    rw [ht]
    calc (2 : ℕ) ^ 16 = 4 * 2 ^ 14 := by norm_num
      _ ≤ 4 * 2 ^ k2For publicInputYes levelConfigMin :=
          Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) hk14)
  have hbad : (2 : ℕ) ^ 16 ≤ 2 ^ 15 := le_trans hlow (le_trans hrow hq)
  norm_num at hbad

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY -- the `cc-t7l` charter target, stated
and disposed of.**  No theorem of this development asserts the frozen row
`4 t_2 <= q_2` at every carrier pair and every `(Public, K)`: the universal
statement already fails at the banked witness above.

**Generalized over the carriers.**  `V` and `E` are quantified at the single
universe `Type` this route's carriers inhabit (the convention Part 9 records,
`02:799--806`); the instantiation to `Fin 3` occurs only inside the proof term,
never in this statement.

**Why the negation is not vacuous.**  `¬ ∀ ...` would be cheap if the quantified
domain were empty.  It is not: `PublicRecords.publicInputYes` and
`PublicRecords.levelConfigMin` inhabit it, and the proof is a genuine
counterexample rather than a vacuity argument.

**NON-FIDELITY.**  This is a fact about the domain *this encoding* quantifies
over, recorded so that no later round inherits the `cc-t7l` charter's target as
a certified premise (the `cc-t7i` rule).  It is not a claim about the paper:
`06:830--831`'s verb is *verify*, and `eq:stage2-structural-gates` is item (v)
of the finite condition list `06:1197--1226` (`06:1219--1220`) that
`sec:effective-cutoff` (`06:1169--1177`) discharges beyond a threshold.  The
paper's gate stands; what fails is only the reading of it as a universal
`(Public, K)` identity of this unrestricted domain.

Reader counterpart: **not claimed** -- see the previous theorem; the reader's
`03:72--73` prints the row as a supposition and is assigned to no declaration.
PROVED. -/
theorem fourT2LeQ2_not_schedule_theorem :
    ¬ ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
        (P : LevelPublicInput V E) (K : LevelConfig),
        4 * t2For P K ≤ LevelStepConstruction.q2For P K :=
  fun h => not_fourT2LeQ2_at_publicInputYes (h (Fin 3) (Fin 3) publicInputYes levelConfigMin)

/-- **NON-DEGENERACY of the RAW level-step family (`LANE-GATE 3`).**  The family
`balFamily` returns at the level step's own three arguments is not constant: it
takes two different values at coordinate `0`.

**Scope, narrowed.**  This says nothing about the guarded builder `balBuild`
succeeding at those arguments, and nothing about the level-step `A_bal` call
being licensed: `balFamily` is total given `0 < m`, and the call itself is
**not** made in this module (it waits on the cutoff discharge of `06:835`
recorded in the block docstring above).  What is stated here is exactly the raw
family's nonconstancy.

**No gate hypothesis is carried**, deliberately: nonconstancy needs only
`t_2 > 0`, `q_2 > 0` and a two-element value carrier, all three theorems of the
evaluated chain.  Conjoining the frozen row would be a conclusion-unused binder
(the `cc-t7e` `D9` defect) and would build a conditional shell besides.

The value carrier is non-degenerate for a *derived* reason and not by
assumption -- `six_le_stepRowsOne_card` of Part 10 gives
`|Rows(M_1^{(i)})| = q_1 m_R >= 6` from the frozen `q_1 = 2^a - 2 >= 6` and
`P3`'s `m_R > 0` -- and the width is positive by the banked
`LevelStepConstruction.q2For_pos`.  This is the statement that keeps any future
level-step instantiation from being met by the trivial constant family which
`PublicRecords.levelParams_admits_unbalanced_family` shows is otherwise a legal
stored family.

Consumed by pin from Part 8's `balFamily_not_constant`; what is new is that
every side condition of that banked statement is discharged from the derived
`(Public, K)` chain rather than assumed.  General in the two carriers, the
public record and the configuration.

Reader counterpart: **not claimed.**  The reader's balanced-family item
`lem:paper-explicit-balanced-family` (`C-effectivity-details.tex:31--38`,
`43--46`, `48--76`) is already assigned to Part 8's `balFamily_isBalanced` and is
**not** re-assigned here -- one reader item, one declaration -- and the reader
prints no nonconstancy clause of its own.  PROVED. -/
theorem balFamily_at_levelStep_not_constant (P : LevelPublicInput V E)
    (K : LevelConfig) :
    balFamily (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))
        (stepRowsOne_card_pos P K)
        ⟨0, balN_pos _ _ _⟩ ⟨0, LevelStepConstruction.q2For_pos P K⟩
      ≠ balFamily (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))
        (stepRowsOne_card_pos P K)
        ⟨1, one_lt_balN _ _ _ (t2_pos _ _ _)⟩
        ⟨0, LevelStepConstruction.q2For_pos P K⟩ := by
  have hnt : Nontrivial (Fin (Fintype.card (LevelStepConstruction.StepRowsOne P K))) :=
    Fin.nontrivial_iff_two_le.mpr (le_trans (by norm_num) (six_le_stepRowsOne_card P K))
  exact balFamily_not_constant _ _ _ (stepRowsOne_card_pos P K)
    (t2_pos _ _ _) (LevelStepConstruction.q2For_pos P K)

/-! ## Part 13: the level-step **storage shape** of
`Pi_i = (K_*, N_{2,i}, c_{2,i})` (`14:1621--1632`) -- a NON-FIDELITY probe

**Round marker (true lineage), added this round.**  Part 13 was authored at
`cc-t8b` under the wrong lineage label `cc-t7ab` and with an eleven-declaration
surface (three definitions and eight theorems).  That tranche's gate returned
`REVISE` on ten of the eleven as concrete specializations of banked owners, and
a supplementary pass (finding `F12`) ruled the part's **fidelity attribution
false**.  Part 13 is re-authored here at `cc-t8c` as **two** declarations plus
anonymous readout evidence, and relabelled.  Every `cc-t7ab` marker this part
and its record notes carried is corrected to the true lineage
`cc-t8b`-authored / `cc-t8c`-banked; no count is inherited from any earlier
report -- the markers were recounted at the bytes this round.

### The frozen paragraph, re-read line by line this round

`thm:effective-materialization` item (b) is `14:1621--1635`.  Its exact words:

* `14:1621--1622` -- "For every `0 <= i < k`, the public record `Public_i`,
  **positive integers `q_{2,i} >= t_{2,i} >= 1`**, and the literal output"
* `14:1623--1625` -- "`(N_{2,i}, d_i)` of `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`,
  where `m_{1,i} = |Rows(M_1^{(i)})|`."
* `14:1625--1628` -- "If `e_i : [m_{1,i}] -> Rows(M_1^{(i)})` is the canonical
  increasing equivalence, the family actually stored in the parameter record
  is"
* `14:1629--1633` -- the two displays
  `c_{2,i}(l)(r) = e_i(c_{d_i}(l)(r))` and `Pi_i = (K_*, N_{2,i}, c_{2,i})`.

`14:1634--1635` (`T_i = LevelStep(Public_i, Pi_i)`) is a *different* display,
owned by `LevelStepConstruction.levelStep`, and no declaration below applies it.

### `F12`, transcribed VERBATIM from the supplementary gate of `cc-t8b`

The `cc-t8b` bytes labelled this part a *fidelity* instance of the storage
display.  That attribution is struck.  The ruling, quoted rather than
paraphrased:

> "**Canonical inhabitation / NON-FIDELITY.** `stepStoredFamily`,
> `stepStoredParams`, and `stepLevelParamsFor` instantiate the total Part-7
> constructors at the route's unrestricted `(Public, K)` accessors.  They
> reproduce only the shape of the storage displays `14:1629--1632`; they are not
> the paper's instance, because item (b) supplies those displays as data
> satisfying `1 <= t_{2,i} <= q_{2,i}`, and that precondition is neither proved
> here nor true at the banked legal witness pair.  The three definitions and the
> six storage/descriptor readouts over them are therefore **NON-FIDELITY
> synthetic storage-shape probes**.  The two `stepRowsOneEquiv_*` theorems
> remain faithful facts about the canonical increasing equivalence, but they do
> not license the builder call.  The paper's literal successful `A_bal` output
> and canonical `Pi_i` remain DEFERRED behind item (ii).
> `LevelStepConstruction.levelParamsFor_exists` remains NON-FIDELITY and is not
> superseded."

**As executed at `cc-t8c`.**  The main gate pass independently ruled
`stepStoredFamily` and `stepStoredParams` duplicate names for the banked
`storedFamily` / `storedParams`, and the six storage/descriptor readouts and the
two `stepRowsOneEquiv_*` theorems concrete specializations of banked general
theorems.  Both rulings are executed together, so the quoted paragraph's three
definitions are now **one**: all ten of those declarations are **deleted**, and
`stepLevelParamsFor` is rewired to apply the banked owners directly.  The
`NON-FIDELITY` label attaches to `stepLevelParamsFor` and to the anonymous
readout evidence below; the two order facts the quotation preserves as faithful
are consumed from their banked owners `canonOrderEquiv_unique` /
`canonEquiv_strictMono` and are re-published under no name here.

### The three arguments, each pinned to its owner -- nothing is chosen

* `q_{2,i}` -- `LevelStepConstruction.q2For P K`, the derived width of
  `05:329--332` / `04:389--391`.  Banked; consumed by pin.
* `t_{2,i}` -- `t2For P K`, Part 11's evaluation of `eq:t2-search`
  (`06:763--770`) through `eq:Hmax` (`06:754--762`) and the terminal-uniform
  chain.  Banked in this module; consumed by pin.  It is **not** a free binder
  and **not** a numeral.
* `m_{1,i} = |Rows(M_1^{(i)})|` -- `Fintype.card (LevelStepConstruction.StepRowsOne P K)`,
  evaluated by Part 10's `stepRowsOne_card` and made positive by
  `stepRowsOne_card_pos` (`14:1781`'s `m > 0` guard, derived).
* `e_i` -- `IteratedCanonicalChaining.canonEquiv` at the carrier's own canonical
  order, which is `LevelStepConstruction.CanonicalRowOrder.stepRowsOneOrder`
  (`12:96` / `14:167` / `04:393`).  That module promotes it nowhere; the
  promotion below is a section-scoped `attribute [local instance]` **confined to
  this part** and reaching no third module.
* `K_*` -- the configuration argument of the banked `storedParams`.

### THE LEGAL-WITNESS TENSION, REGISTERED AS EVIDENCE -- not resolved here

`14:1621--1622` supplies `q_{2,i} >= t_{2,i} >= 1` as **data of item (b)**, and
`14:1587` reprints it inside `eq:effective-balanced-builder` as `1 <= t <= q`.
Nothing below proves it, and nothing below carries it as a hypothesis.  Two
facts already banked in Part 12 are what make this a registered tension rather
than a gap someone could close by trying harder:

* `not_fourT2LeQ2_at_publicInputYes` -- the schedule's structural row
  `4 t_2 <= q_2` (`eq:stage2-structural-gates`, `06:835`), which is what would
  supply `1 <= t_2 <= q_2` at the level step, is **provably false** at this
  route's own banked legal witness pair; and
* `fourT2LeQ2_not_schedule_theorem` -- it is therefore not a theorem over this
  development's unrestricted `(Public, K)` domain at all.

That is a fact about the **quantification domain**, not a refutation of the
paper's gate: `06:830--831` states the row as a condition to *verify before*
constructing the family, and its discharge is item (v) of the finite condition
list `06:1197--1226` (at `06:1219--1220`), beyond the threshold of
`sec:effective-cutoff` (`06:1169--1177`).  Until that cutoff discharge lands,
**the route has no legal `(Public, K)` at which the paper's own precondition
holds**, so no declaration here may be read as instantiating item (b).  This
paragraph is the registration of that standing question as **evidence**; it is
not an answer to it, no legal schedule witness is smuggled in below, and the
`t_2` accessor obligation of ledger row `S5-BALANCED-FAMILY-LEVELSTEP-001`
stays **OPEN**.

### WHAT IS AND IS NOT CLAIMED

**Claimed.**  The storage *shape* of `14:1629--1632` is a total construction at
the route's unrestricted `(Public, K)`: the banked `storedFamily` /
`storedParams` need `0 < m` alone, so the record below is unconditional and
carries **no gate hypothesis of any kind**.

**NOT claimed, and deliberately absent.**

1. **That this is the paper's `Pi_i`.**  It is not -- see `F12` above.  The
   paper's literal successful `A_bal` output and its canonical `Pi_i` are
   **DEFERRED behind item (ii)**.
2. **Balancedness at the level step.**  `storedFamily_isBalanced` needs
   `1 <= t_2 <= q_2`.  **No declaration below carries `4 t_2 <= q_2` or
   `t_2 <= q_2` in hypothesis position**, and `storedFamily_isBalanced` is not
   instantiated here under any label.
3. **The guarded machine succeeding.**  `balBuild_eq_some` needs the same
   `t <= q`, so `A_bal(q_{2,i}, t_{2,i}, m_{1,i}) = some (N_{2,i}, d_i)` is
   **not** stated, at any generality, under any label.
4. **Admissibility.**  `Admissible(Public_i, Pi_i, T_i)` (`14:1671`) is
   not stated, implied, or approached.

**Ledger status this part changes, and the status it does not.**  Item (iii) of
`S5-BALANCED-FAMILY-LEVELSTEP-001` had two residuals: the missing linear order
on `Rows(M_1^{(i)})`, and the `A_bal` call with the canonical `Pi_i`.  Only the
**first** is closed, by `LevelStepConstruction` Part 8.  **The call residual of
item (iii) is NOT discharged** -- the `cc-t8b` claims that item (iii)'s
schedulable remainder "is authored" and that both residuals are "closed" are
**withdrawn here and in the ledger row**.  Item (ii) (the structural row) is
**UNCHANGED and OPEN**, the `t_2` accessor obligation stays **OPEN**, and **item
(b) of `S5-BALANCED-FAMILY` is NOT discharged**.  Registration is not discharge,
and a storage *shape* without the paper's data precondition is not the paper's
storage step.

**Canonical inhabitation, and how it is evidenced.**  The canonical instance of
the storage display is **canonical-DEFERRED behind item (ii)** and is registered,
not satisfied, by anything below.  The readouts that would ordinarily witness
non-degeneracy are supplied as **anonymous `example`s**: under the fixed-interface
rule every one of them is a concrete specialization of a banked general theorem,
so minting a name for it would republish banked content, while dropping it
altogether would leave the probe unevidenced.  The route's convention resolves
that tension by evidencing inhabitation **without minting a name** -- the
`example`s type-check as part of the module and are cited from the ledger row by
`file:line`, and they own no statement.  `LevelStepConstruction.levelParamsFor_exists`
keeps its own NON-FIDELITY label and is **not** superseded by anything here.

Reader counterpart: **not claimed.**  The reader's balanced-family item
`lem:paper-explicit-balanced-family` is already assigned to this module's Part 8
`balFamily_isBalanced` -- one reader item, one declaration -- and the reader
prints no storage display: its `03:71--77` puts the whole Stage-2 family under
"Suppose also that", and `C-effectivity-details.tex:7--8` is appendix-preamble
prose, which this route never cites as a statement.  Both lines were opened
first-hand this round in the pinned release copy. -/

section LevelStepStorage

attribute [local instance] LevelStepConstruction.CanonicalRowOrder.stepRowsOneOrder

/-- **NON-FIDELITY storage-shape probe of `Pi_i = (K_*, N_{2,i}, c_{2,i})`**
(`14:1632`), at the route's own unrestricted `(Public, K)`, in the paper-facing
form `def:level-parameters` (`05:172--190`) where `K` is a *field* and the
codomain of `c_2` is computed from it.

**Not the paper's instance**, and labelled so per finding `F12`: `14:1621--1622`
supplies the storage displays as data satisfying `1 <= t_{2,i} <= q_{2,i}`, this
declaration supplies no such fact, and that precondition is provably false at
this route's banked legal witness pair (see the block docstring's registered
tension).  What is reproduced is the *shape* of `14:1629--1632` and nothing more.

**Rewired at `cc-t8c` to the banked owners, by pin.**  The `cc-t8b` bytes routed
this definition through two module-local aliases `stepStoredFamily` /
`stepStoredParams`; both are deleted as second names for the route's sole
reifications.  The body is now one application of the banked
`PublicRecords`-valued `storedParams` (`:1052`), transported by the banked
`LevelStepConstruction.LevelParamsFor.equivFibre`, with the fibre coherence
supplied by the banked `storedParams_K` (`:1061`).  No family, record,
descriptor or accessor is built here.  General in the two carriers, the public
record and the configuration. -/
noncomputable def stepLevelParamsFor (P : LevelPublicInput V E) (K : LevelConfig) :
    LevelStepConstruction.LevelParamsFor P :=
  (LevelStepConstruction.LevelParamsFor.equivFibre P).symm
    ⟨K,
      ⟨storedParams K (LevelStepConstruction.q2For P K) (t2For P K)
          (Fintype.card (LevelStepConstruction.StepRowsOne P K))
          (stepRowsOne_card_pos P K) (LevelStepConstruction.StepRowsOne P K) rfl,
        storedParams_K K _ _ _ (stepRowsOne_card_pos P K) _ rfl⟩⟩

/-- **The probe's configuration is the one it was built at** -- `14:1632`'s
`K_*` slot, read off the *paper-facing* record rather than off the banked fibre.

Genuinely fresh, and the only named readout this part keeps: the banked
`storedParams_K` is a statement about `PublicRecords.LevelParams`, whereas this
is a statement about `LevelStepConstruction.LevelParamsFor` **after** transport
along `equivFibre.symm`, which no banked theorem covers.  (The `cc-t8b` bytes
conjoined the banked `storedParams_K` here; that conjunct is removed.)

Non-degenerate in the sense that matters for a transport receipt: `equivFibre`'s
backward map could have landed the fibre index rather than the record's own
field, and this is the kernel evidence that it did not.  General in the public
record and the configuration.  PROVED. -/
theorem stepLevelParamsFor_K (P : LevelPublicInput V E) (K : LevelConfig) :
    (stepLevelParamsFor P K).K = K := rfl

/-! ### Anonymous readout evidence (no statement owner is minted)

Each `example` below is a concrete specialization of a banked general theorem at
this part's three arguments.  Under the fixed-interface rule none of them may
own a name; they are kept as *evidence* that the probe is non-degenerate and
that its fields are the evaluated definitional chain rather than assigned
values, and they are cited from ledger row `S5-BALANCED-FAMILY-LEVELSTEP-001` by
`file:line`.  All of them are NON-FIDELITY together with the probe: none
supplies `1 <= t_{2,i} <= q_{2,i}`. -/

-- `N_{2,i}` is the builder's literal output `balN` (`14:1622--1624`), i.e. the
-- evaluated chain `xBal -> balPrime -> balN`, not a value assigned to the
-- record.  Banked owner: `storedParams_N₂` (`:1069`).
example (P : LevelPublicInput V E) (K : LevelConfig) :
    (stepLevelParamsFor P K).N₂
      = balN (LevelStepConstruction.q2For P K) (t2For P K)
          (Fintype.card (LevelStepConstruction.StepRowsOne P K)) :=
  storedParams_N₂ K _ _ _ (stepRowsOne_card_pos P K) _ rfl

-- `c_{2,i}(l)(r) = e_i(c_{d_i}(l)(r))` (`14:1630`), with `e_i` the banked
-- `canonEquiv` at the canonical lexicographic order of `Rows(M_1^{(i)})`.
-- Banked owner: `storedParams_c₂` (`:1074`).
example (P : LevelPublicInput V E) (K : LevelConfig)
    (l : Fin (balN (LevelStepConstruction.q2For P K) (t2For P K)
          (Fintype.card (LevelStepConstruction.StepRowsOne P K))))
    (r : Fin (LevelStepConstruction.q2For P K)) :
    (storedParams K (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))
        (stepRowsOne_card_pos P K) (LevelStepConstruction.StepRowsOne P K) rfl).c₂ l r
      = canonEquiv (LevelStepConstruction.StepRowsOne P K) rfl
          (balFamily (LevelStepConstruction.q2For P K) (t2For P K)
            (Fintype.card (LevelStepConstruction.StepRowsOne P K))
            (stepRowsOne_card_pos P K) l r) :=
  storedParams_c₂ K _ _ _ (stepRowsOne_card_pos P K) _ rfl l r

-- The size clause `0 < N <= B_bal(q,t,m)` of `eq:effective-balanced-builder`
-- (`14:1588`) at the *stored* record.  Its one side condition `0 < t_2` is Part
-- 9's derived `t2_pos`, and in particular **not** the barred row
-- `4 t_2 <= q_2`.  Banked owner: `storedParams_N₂_le_bBal` (`:1084`).
example (P : LevelPublicInput V E) (K : LevelConfig) :
    0 < (stepLevelParamsFor P K).N₂ ∧
      (stepLevelParamsFor P K).N₂
        ≤ bBal (LevelStepConstruction.q2For P K) (t2For P K)
            (Fintype.card (LevelStepConstruction.StepRowsOne P K)) :=
  storedParams_N₂_le_bBal K _ _ _ (stepRowsOne_card_pos P K) _ rfl (t2_pos _ _ _)

-- NON-DEGENERACY (`LANE-GATE 3`): the family the probe stores is not constant,
-- so the shape is not met by the trivial constant witness that
-- `PublicRecords.levelParams_admits_unbalanced_family` shows is otherwise a
-- legal stored family.  Every side condition is derived: `t2_pos` (Part 9),
-- `LevelStepConstruction.q2For_pos`, and `six_le_stepRowsOne_card` (Part 10,
-- `m_{1,i} = q_1 m_R >= 6`).  Banked owner: `storedFamily_not_constant`
-- (`:1097`).
example (P : LevelPublicInput V E) (K : LevelConfig) :
    storedFamily (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))
        (stepRowsOne_card_pos P K) (LevelStepConstruction.StepRowsOne P K) rfl
        ⟨0, balN_pos _ _ _⟩ ⟨0, LevelStepConstruction.q2For_pos P K⟩
      ≠ storedFamily (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))
        (stepRowsOne_card_pos P K) (LevelStepConstruction.StepRowsOne P K) rfl
        ⟨1, one_lt_balN _ _ _ (t2_pos _ _ _)⟩
        ⟨0, LevelStepConstruction.q2For_pos P K⟩ := by
  haveI : Nontrivial (LevelStepConstruction.StepRowsOne P K) :=
    Fintype.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le (by norm_num) (six_le_stepRowsOne_card P K))
  exact storedFamily_not_constant (LevelStepConstruction.q2For P K) (t2For P K)
    (Fintype.card (LevelStepConstruction.StepRowsOne P K))
    (stepRowsOne_card_pos P K) (t2_pos _ _ _)
    (LevelStepConstruction.q2For_pos P K)
    (LevelStepConstruction.StepRowsOne P K) rfl

-- `e_i` is not an additional choice (`12:103--104`) at this carrier: every
-- increasing equivalence `[m_{1,i}] -> Rows(M_1^{(i)})` *is* the canonical one.
-- Banked owner: `IteratedCanonicalChaining.canonOrderEquiv_unique`.
example (P : LevelPublicInput V E) (K : LevelConfig)
    (e : @OrderIso (Fin (Fintype.card (LevelStepConstruction.StepRowsOne P K)))
          (LevelStepConstruction.StepRowsOne P K) _
          (LevelStepConstruction.CanonicalRowOrder.stepRowsOneOrder P
            K).toPartialOrder.toPreorder.toLE) :
    e = canonOrderEquiv (LevelStepConstruction.StepRowsOne P K) rfl :=
  canonOrderEquiv_unique rfl e

-- `e_i` is increasing (`12:99`) for the Part-8 order, named through
-- `stepRowsOneLt` rather than by `<` notation (bare `<` at this carrier is
-- Mathlib's pointwise product order).  Banked owner: `canonEquiv_strictMono`.
example (P : LevelPublicInput V E) (K : LevelConfig)
    {u v : Fin (Fintype.card (LevelStepConstruction.StepRowsOne P K))} (h : u < v) :
    LevelStepConstruction.CanonicalRowOrder.stepRowsOneLt P K
      (canonEquiv (LevelStepConstruction.StepRowsOne P K) rfl u)
      (canonEquiv (LevelStepConstruction.StepRowsOne P K) rfl v) :=
  canonEquiv_strictMono rfl h

-- The unconditional half of the descriptor clause `14:1567--1570`: the
-- descriptor the builder emits at these three arguments parses against the
-- recorded context.  `balBuild_output_parses` is unconditional, whereas
-- `balBuild_eq_some` needs `t <= q` and is applied nowhere in this part.
example (P : LevelPublicInput V E) (K : LevelConfig) :
    (balDescriptor (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))).Parses
      (LevelStepConstruction.q2For P K) (t2For P K)
      (Fintype.card (LevelStepConstruction.StepRowsOne P K))
      (balN (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))) :=
  balBuild_output_parses _ _ _

end LevelStepStorage

/-! ## Part 14: `eq:effective-balanced-builder` **at the machine's own output**,
and the exact bare-guard BLOCK for item (b) of `thm:effective-materialization`

**Charter of this part (`cc-t8r` lane 3, `[opus-direct]`).**  Trace the paper's
OWN builder as a *statement layer* over the banked surface of Parts 1--13, and
where the paper's build leaves a step unconstructed, **register the gap as a
kernel-checked fact rather than bridging it**.  Zero new axioms; zero expander
interfaces (`EXPANDER-001` has no Lean declaration by design and none is added
here); `LegacyNPCC.Stage12` is not adopted.

### The frozen lines, re-read first-hand this round

* **`14:1556--1565`** -- "There exist named total machines `A_bal` and
  `A_balEntry` in `M`.  For positive integers `q,t,m` with `q >= t >= 1`, their
  exact parsed-output equation is
  `parse^{q,t,m}_bal(out_M(A_bal, enc_M(q,t,m))) = (N, d_bal)`."
* **`14:1570--1582`** -- the accessor equation
  `c_{d_bal}(l)(i) = parse_{[m]}(out_M(A_balEntry, enc_M(q,t,m,N,d_bal,l,i)))`
  for `l in [N]`, `i in [q]`.
* **`14:1583--1595`, `eq:effective-balanced-builder`** -- "Their mathematical
  correctness theorem, not a proof object in the machine output, proves
  `1 <= t <= q`, `0 < N <= B_bal(q,t,m)`, `c_{d_bal} : [N] -> [m]^q`,
  `c_{d_bal}` is indexed `(q,t,1/(100t))`-balanced."
* **`02:183--188`, `eq:balanced-family-envelope`** --
  `B_bal(q,t,m) = (2 X_bal(q,t,m))^t` with `X_bal(q,t,m) = max{q,1000mt^2,2}`
  (`02:180--182`).  Reified once, in `ScheduleMajorantResidue.xBal` / `.bBal`,
  and consumed here **by pin**; no second envelope is written.
* **`14:1621--1635`, item (b) of `thm:effective-materialization`** -- "For every
  `0 <= i < k`, the public record `Public_i`, **positive integers
  `q_{2,i} >= t_{2,i} >= 1`**, and the literal output `(N_{2,i}, d_i)` of
  `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`, where `m_{1,i} = |Rows(M_1^{(i)})|`", then
  the two storage displays `c_{2,i}(l)(r) = e_i(c_{d_i}(l)(r))` and
  `Pi_i = (K_*, N_{2,i}, c_{2,i})` (`14:1629--1633`).
* **`06:830--831` / `06:835`** -- "Before constructing the balanced family,
  verify the following structural conditions:", whose second row is
  `4 t_2 <= q_2` (`eq:stage2-structural-gates`, `\label` at `06:848`).
* **`06:859--861`** -- "Construct the one indexed `(q_2,t_2,eps_2)`-balanced
  family `C_2`, then materialise `M_2, M_3`, the source rows, and all protected
  multiplicities."  The construction is thus *ordered after* the verification of
  `06:830--831`, which is the whole content of the block below.

### Cross-anchors this part records (as record notes, not as declarations)

* **`11:224--226`** -- "The family `C_2` is the single indexed
  `(q_2,t_2,eps_2)`-balanced family chosen in `sec:parameter-stage2`."  The word
  *single* is what `entryEq_determines_balFamily` makes precise on the builder
  side: once the descriptor is the builder's own output, the family is not
  merely *some* family meeting the accessor equation -- it is the unique one.
  The schedule-side choice of `C_2` at the level step is a different claim and
  is **not** made here.
* **`15:36--40`** -- the evidence table's balanced-family row: "The
  polynomial-evaluation builder and bounded envelope in
  `eq:balanced-family-envelope`, `thm:effective-materialization`. / The
  inherited facade also exposes an AGHP existence theorem. / **The deterministic
  builder and accessor are not implemented in Lean.**"  That last cell was
  written before this route existed and is **superseded for the builder and the
  accessor** by Parts 1--8 (`balBuild`, `balEntry`, `balFamily_isBalanced`); it
  is **not** superseded for the level-step call, which stays open below.  This
  is a record note about a frozen status cell, not a claim about the frozen
  mathematics.
* **`D:36--42`** -- "the concrete legacy declarations `NPCC.M1_robust`,
  `NPCC.M2_column_loss_resilient`, `NPCC.M2_hard_seed`, and the two concrete
  `NPCC.M2_robust` endpoints additionally depend on
  `NPCC.aghp_balanced_family_exists`.  A required reboot bridge has no axiom
  surface yet; completing one requires a proof, not a new axiom."  Part 14 adds
  **no** axiom and imports **no** `LegacyNPCC.Stage12` facade: every declaration
  below closes over `propext`, `Classical.choice`, `Quot.sound` only.  The
  builder's own existential input is the checked `primeWindow` adapter of Part 1,
  never the AGHP existence axiom -- which is exactly the distinction `D:41--42`
  draws.

### What this part claims, and what it refuses to claim

**Claimed (14.A, 14.B), at the paper's own free positive integers `q,t,m`.**
`14:1557--1558` states the builder interface for *every* triple with
`q >= t >= 1`; that is the quantification the paper itself uses, and it is the
quantification below.  The deliverable `effectiveBalancedBuilder` is the
four-clause display `eq:effective-balanced-builder` together with the two
machine equations `14:1560--1565` and `14:1570--1582`, assembled as one
statement about the builder's own output.  **No banked owner is restated**: each
clause is discharged by applying its owner (`balBuild_eq_some`,
`balEntry_at_builder_output`, `balN_pos`, `balN_le_bBal`,
`balFamily_isBalanced`), and the *new* content is the assembly itself plus the
inversion `balBuild_eq_some_iff`, which no banked declaration states and which
is what makes "the literal output `(N_{2,i}, d_i)`" of `14:1623` a well-posed
phrase.

**Refused (14.C), and refused deliberately.**  Nothing below states, implies or
approaches the **level-step** call `A_bal(q_{2,i}, t_{2,i}, m_{1,i})` at this
route's `(Public, K)` accessors, in success form or in conditional form.  The
standing bar recorded at `EffectiveCutoffCertificate.lean` (item 7 of its
`cc-t7s-r3` block, "any restatement of the level-step `A_bal` call in
conditional form, under any name, at any module") is **honoured**: no
declaration below carries `t2For P K <= q2For P K` or `4 * t2For P K <= q2For P K`
in hypothesis position, at any generality.  What 14.C does instead is turn the
block into a *positive, kernel-checked* fact.

### Why 14.C is new evidence rather than a re-run of Part 12

Part 12 banks two negatives about the **4x structural** row
(`not_fourT2LeQ2_at_publicInputYes`, `fourT2LeQ2_not_schedule_theorem`).  Those
do **not** settle the builder's own guard: `balBuild_eq_some`'s third
hypothesis is the **bare ordering `t <= q`** of `14:1557--1558`, and
`¬ (4 t_2 <= q_2)` does not give `¬ (t_2 <= q_2)`.  So until this round the
route had no receipt for the guard that actually blocks item (b) -- the ledger
row `S5-BALANCED-FAMILY-LEVELSTEP-001` records exactly that (its `cc-t8p`
empty-roster ruling), and records that the bare-guard probe existed only as an
unbanked scratch file needing "its own commission, ledger registration and
explicit NON-FIDELITY label".  This part is that commission, and
`not_t2ForLeQ2For_at_publicInputYes` is that receipt, banked.

`balBuild_eq_none_at_publicInputYes` then states the consequence directly: at
this route's own level-step arguments, evaluated at the campaign's banked legal
witness pair, **the paper's builder returns the reserved failure output of
`14:1743--1745`.**  That is the BLOCK, in the kernel, instead of in prose.

**NON-FIDELITY / BEYOND-PAPER, and what the receipts do NOT say.**  Both 14.C
receipts are audits of *this encoding's quantification domain* at a point the
frozen source never visits.  They do **not** refute `06:835`: the paper's verb
at `06:830` is *verify*, the row is item (v) of the finite condition list
`06:1197--1226` (at `06:1219--1220`), and `sec:effective-cutoff`
(`06:1169--1177`) supplies the threshold beyond which it holds.  They also do
**not** establish failure at every `(P, K)`: the universal form
`t2LeQ2_not_schedule_theorem` is exactly as strong as its witness, and the
stronger reading "the builder can never be applied at the accessors" is
**unsupported and is not asserted here**.  The correct and narrower conclusion is
the one the ledger row now carries: no unconditional accessor-level success
statement is authorable today, and the paper's canonical legal instance is
cutoff-generated behind `PARAM-001`.

### Ledger status this part changes, and the status it does not

* **Item (b) of `S5-BALANCED-FAMILY` stays OPEN.**  Registration is not
  discharge.  Nothing below is the paper's level-step instance.
* **`S5-BALANCED-FAMILY-LEVELSTEP-001` stays OPEN**, with its bare-guard
  residual now *evidenced in Lean* rather than carried as a scratch receipt.
* Canonical inhabitation of the level-step call stays **canonical-DEFERRED**
  behind the cutoff machinery of `06:1169--1226` and `PARAM-001`.
* For 14.A/14.B the canonical inhabitant **is the paper's own object**: the
  family `c_{d_bal}` built by `14:1749--1763` and read by `14:1768--1782`, at
  every triple the paper's own interface admits.  The hypothesis bundle
  `0 < m`, `1 <= t`, `t <= q` is satisfiable and non-degenerate -- the banked
  BEYOND-PAPER audit `balFamily_isBalanced_nondegenerate` exhibits it, and is
  **consumed as that evidence rather than re-authored**.

### Fixed-interface discipline for Part 14

Consumed **by pin**, never restated: `balBuild`, `balBuild_eq_some`,
`balBuild_eq_none_of_q_lt_t`, `balEntry`, `balEntry_at_builder_output`,
`balFamily`, `balFamily_isBalanced`, `balN_pos`, `balN_le_bBal`, `storedParams`,
`storedParams_K`, `storedParams_N₂`, `storedFamily_isBalanced`,
`ScheduleMajorantResidue.bBal`, `LevelStepConstruction.q2For` / `.StepRowsOne`,
Part 11's `t2For` / `k2For` / `K2Pred_at_k2For`,
`WrapperMassRedistribution.k2_floors_of_K2Pred`, `GuardedSourceSlab.q2_le_of_le`,
`ParameterSchedule.sScale_eq_pow`, `NPCC.IsBalancedFamily`.  No second
descriptor, accessor, family, envelope or gate predicate is introduced, and none
of the ten names barred at `cc-t8c` is revived under any spelling.

**Disclosed overlap.**  `q2For_le_at_publicInputYes` extracts, as a named lemma,
the `q_2 <= 2^15` chain that Part 12's `not_fourT2LeQ2_at_publicInputYes` runs
inline.  The banked theorem is deliberately left **byte-identical**: rewriting a
banked proof to route through a new helper is outside an authoring lane's
licence, so the two proofs coincide on that chain and this sentence is the
disclosure rather than a silent duplication.

### Import direction (verified this round, not asserted)

Every cross-module name below is reached through an import this module already
declares.  `BalancedFamilyBuilder.lean:3` is
`import EthInapproximability.ParameterizedNP.LevelStepConstruction` (importer
`BalancedFamilyBuilder`, importee `LevelStepConstruction`), which is what makes
`LevelStepConstruction.q2For` and `.StepRowsOne` pinnable here;
`PublicRecords`, `ScheduleMajorantResidue`, `ParameterSchedule`,
`GuardedSourceSlab`, `WrapperMassRedistribution` and the vendored `NPCC` facade
arrive transitively through the same line and through
`BalancedFamilyBuilder.lean:1--2`, and every one of them is already named in
Parts 1--13 of this file.  **No new import is added, and no name is pinned from
a module upstream of this one's requirements.** -/

/-! ### Part 14.A: the builder's output, inverted (general aux battery) -/

/-- **AUX (round trip): the parsed-output equation, both ways** (`14:1560--1565`
with the guard of `14:1557--1558`).

The banked `balBuild_eq_some` is the forward half only, and the three banked
`none` probes cover three individual guard failures.  What is new here is the
**inversion**: a successful run of `A_bal` *determines* both components of its
output and *recovers* the frozen admissibility of the input triple.  That is
what makes `14:1623`'s phrase "the literal output `(N_{2,i}, d_i)`" well posed --
"the" is a definite description, and this is its uniqueness half -- and it is
what lets every consumer below take the paper's data condition
`1 <= t_{2,i} <= q_{2,i}` (`14:1621--1622`, `14:1587`) *out of* the success
hypothesis instead of assuming it separately.

General in `q, t, m, N, d`; no parameter is instantiated and the prime scan is
never evaluated.  Reader counterpart: **not claimed** -- the reader's one
balanced-family item `lem:paper-explicit-balanced-family`
(`C-effectivity-details.tex:31--38`, `43--46`, proof `48--76`, opened first-hand
this round in the pinned release copy) is already assigned to Part 8's
`balFamily_isBalanced`, and the reader prints no parsed-output equation of its
own.  PROVED. -/
theorem balBuild_eq_some_iff {q t m N : ℕ} {d : BalDescriptor} :
    balBuild q t m = some (N, d)
      ↔ (0 < m ∧ 1 ≤ t ∧ t ≤ q) ∧ N = balN q t m ∧ d = balDescriptor q t m := by
  constructor
  · intro hb
    unfold balBuild at hb
    split at hb
    · rename_i hg
      have h2 := Option.some.inj hb
      exact ⟨hg, (congrArg Prod.fst h2).symm, (congrArg Prod.snd h2).symm⟩
    · exact absurd hb (by simp)
  · rintro ⟨⟨hm, ht, htq⟩, rfl, rfl⟩
    exact balBuild_eq_some hm ht htq

/-- **AUX (monotonicity): success is upward closed in the coordinate width**
(`14:1557--1558`, "positive integers `q,t,m` with `q >= t >= 1`").

If the builder succeeds at `(q,t,m)` it succeeds at every wider `(q',t,m)`, since
`t <= q <= q'` is the only clause of the guard that mentions `q`.  Two things
this lemma is careful **not** to say.  First, the *output* is not preserved:
`X_bal` depends on `q` through its first branch, so the scanned prime, `N` and
the descriptor all move -- which is why the conclusion is stated at
`balN q' t m` / `balDescriptor q' t m` rather than at `(N, d)`.  Second, it says
nothing about any particular `q'`; in particular it is **not** applied to any
`(Public, K)` accessor anywhere below.

This is the general shape of the level-step obstruction (`06:835` is a *lower*
bound on `q_2` relative to `t_2`), recorded at the paper's own free integers so
that no round mistakes the obstruction for a defect of the builder.  General in
`q, q', t, m, N, d`.  Reader counterpart: **not claimed** (see the previous
declaration).  PROVED. -/
theorem balBuild_some_mono_q {q q' t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d)) (hq : q ≤ q') :
    balBuild q' t m = some (balN q' t m, balDescriptor q' t m) := by
  obtain ⟨⟨hm, ht, htq⟩, _, _⟩ := balBuild_eq_some_iff.mp hout
  exact balBuild_eq_some hm ht (le_trans htq hq)

/-- **AUX (uniqueness / STATEMENT POLE): the accessor equation pins the family.**

`14:1570--1582` *defines* `c_{d_bal}` by the accessor machine, and `11:224--226`
calls the resulting object "**the single** indexed `(q_2,t_2,eps_2)`-balanced
family".  This is the builder-side content of that definite article: any family
whose entries are the outputs of `A_balEntry` on the builder's own output
context is **equal** to the banked `balFamily` -- not merely equal in
distribution, and not merely balanced too.

**Why this is the statement pole for `effectiveBalancedBuilder` below.**  That
deliverable is an existential over `(N, d, c)`.  A bare existential of an indexed
family in `[m]^q` is met by the constant family -- `PublicRecords`
`levelParams_admits_unbalanced_family` banks that a constant family is a
perfectly legal stored family, and Part 8's `constant_family_not_isBalanced`
banks that it fails the accuracy clause.  This lemma closes the other escape:
even ignoring the accuracy clause, the accessor equation alone leaves exactly one
candidate for `c`, so the existential is a definite description of the paper's
object rather than a claim that *some* family exists.

General in `q, t, m` and in the candidate family `c`.  Reader counterpart:
**not claimed** -- `lem:paper-explicit-balanced-family` is assigned to Part 8 and
the reader states no uniqueness clause; its `C-effectivity-details.tex:74--75`
("Repeated indices remain distinct even if their represented tuples coincide")
is a distinctness sentence about *indices*, already banked as
`StageTwoRelaxed.stageTwo_repeated_columns_stay_distinct`, and is a different
statement.  PROVED. -/
theorem entryEq_determines_balFamily {q t m : ℕ} (hm : 0 < m)
    {c : Fin (balN q t m) → Fin q → Fin m}
    (hc : ∀ (l : Fin (balN q t m)) (i : Fin q),
        balEntry q t m (balN q t m) (balDescriptor q t m) (l : ℕ) (i : ℕ)
          = some ((c l i : ℕ))) :
    c = balFamily q t m hm := by
  funext l i
  have h := hc l i
  rw [balEntry_at_builder_output hm l.isLt i.isLt] at h
  have h2 : ((balFamily q t m hm ⟨(l : ℕ), l.isLt⟩ ⟨(i : ℕ), i.isLt⟩ : Fin m) : ℕ)
      = ((c l i : Fin m) : ℕ) := Option.some.inj h
  simp only [Fin.eta] at h2
  exact Fin.val_injective h2.symm

/-! ### Part 14.B: `eq:effective-balanced-builder` at the builder's own output -/

/-- **THE DELIVERABLE OF PART 14** -- `eq:effective-balanced-builder`
(`14:1585--1595`) together with the parsed-output equation `14:1560--1565` and
the accessor equation `14:1570--1582`, stated as one theorem about the machine's
own output, at the paper's own quantification (`14:1557--1558`, "For positive
integers `q,t,m` with `q >= t >= 1`").

The four frozen clauses, in the frozen order:

* `1 <= t <= q` (`14:1587`) -- carried into the conclusion, because the paper's
  correctness theorem *asserts* it of the objects it produces;
* `0 < N <= B_bal(q,t,m)` (`14:1588`) -- with `B_bal` the banked
  `eq:balanced-family-envelope` (`02:183--188`), consumed by pin;
* `c_{d_bal} : [N] -> [m]^q` (`14:1589`) -- the *type* of the produced `c`, over
  the zero-based slots of `conv:finite-slots`;
* `c_{d_bal}` indexed `(q, t, 1/(100t))`-balanced (`14:1591--1592`) -- the
  vendored predicate `NPCC.IsBalancedFamily`, at the frozen accuracy.

**Why this is not a restatement of a derived telescope.**  Every clause has a
banked owner and each is *applied* here, not repeated; what no banked
declaration states is the display itself -- the conjunction, at one output pair,
under the machine equations that make that pair the paper's `(N, d_bal)`.  The
route ledger names this as item (4) of the `S5-BALANCED-FAMILY` retarget, and
before this round item (4) had no single Lean statement.

**STATEMENT POLE (why the trivial witness fails).**  The existential is over
`(N, d, c)`.  The trivial candidate -- `c` constant -- fails twice over: it is
excluded by the accuracy clause (Part 8's `constant_family_not_isBalanced`, at
any legal triple with `1 < m`), and it is excluded *before* the accuracy clause
by `entryEq_determines_balFamily`, which shows the accessor equation already
determines `c` uniquely.  Likewise `N` and `d` cannot be chosen: they are pinned
by `balBuild q t m = some (N, d)` through `balBuild_eq_some_iff`.

**Canonical inhabitation.**  The witness is the paper's own object, not a
synthetic one: `N = p^t` for the scanned prime of `14:1754--1758`, `d` the frozen
`(poly-v1, p)` descriptor of `14:1762--1763`, and `c` the literal Horner accessor
of `eq:literal-balanced-accessor` (`14:1774--1778`).  Non-degeneracy of the
hypothesis bundle is the banked BEYOND-PAPER audit
`balFamily_isBalanced_nondegenerate`, consumed as evidence and **not**
re-authored; no new triple of numerals is chosen here.

**SCOPE, stated so no later round inherits more than is proved.**  This theorem
is about **free positive integers**, exactly as `14:1557--1558` is.  It says
nothing whatever about the *level step*: it does not instantiate `q`, `t` or `m`
at any `(Public, K)` accessor, it does not state or imply
`A_bal(q_{2,i}, t_{2,i}, m_{1,i}) = some (N_{2,i}, d_i)`, and it discharges
**neither** item (b) of `S5-BALANCED-FAMILY` **nor** any item of
`S5-BALANCED-FAMILY-LEVELSTEP-001`.  Part 14.C is the reason.

General in `q, t, m`.  Reader counterpart: **not claimed** -- the reader's
`lem:paper-explicit-balanced-family` is a single item already assigned to Part
8's `balFamily_isBalanced`, and this route assigns one reader item to one
declaration.  PROVED. -/
theorem effectiveBalancedBuilder {q t m : ℕ} (hm : 0 < m) (ht : 1 ≤ t)
    (htq : t ≤ q) :
    ∃ (N : ℕ) (d : BalDescriptor) (c : Fin N → Fin q → Fin m),
      balBuild q t m = some (N, d) ∧
      (∀ (l : Fin N) (i : Fin q),
          balEntry q t m N d (l : ℕ) (i : ℕ) = some ((c l i : ℕ))) ∧
      1 ≤ t ∧ t ≤ q ∧ 0 < N ∧ N ≤ bBal q t m ∧
      NPCC.IsBalancedFamily t c (1 / (100 * (t : ℝ))) := by
  refine ⟨balN q t m, balDescriptor q t m, balFamily q t m hm,
    balBuild_eq_some hm ht htq, ?_, ht, htq, balN_pos q t m,
    balN_le_bBal q t m (by omega), balFamily_isBalanced q t m hm ht htq⟩
  intro l i
  simpa using balEntry_at_builder_output hm l.isLt i.isLt

/-- **The storage step of item (b) `14:1626--1633`, welded to the machine
output.**

`14:1622--1624` says the record holds "the literal output `(N_{2,i}, d_i)` of
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})`".  Part 7's banked `storedParams` builds the
record from the *evaluated definitional chain* `xBal -> balPrime -> balN`; what
was missing on this route -- the atlas records it as "`balBuild_eq_some` is
applied nowhere" -- is the weld saying that this chain **is** the machine's
output, i.e. that the record's `N_2` is literally the `N` the machine returned.
That weld is the first conclusion below.

The other two conclusions record that everything item (b) asserts about `Pi_i`
follows from the **single** fact that the machine succeeded: the guard
`0 < m` is *recovered* rather than assumed (through `balBuild_eq_some_iff`), the
configuration slot `K_*` of `14:1632` is the one the record was built at, and
the balancedness of the stored family `c_{2,i}` of `14:1630` -- the banked
`storedFamily_isBalanced`, applied -- needs no further hypothesis.

**SCOPE.**  General in `q, t, m, N, d, K` and in the value carrier `X_1` at its
own cardinality, exactly as `14:1626` states it.  **This is not the level-step
instance**: there is no `Public`, no `(Public, K)` accessor, and no claim that
any particular triple satisfies the antecedent.  It does not discharge item (b)
of `S5-BALANCED-FAMILY`; it supplies the general storage lemma that a future
legal instantiation will consume once `PARAM-001` produces one.

**No gate hypothesis is carried**, deliberately: the antecedent is the machine's
own success, which is inhabited at every legal triple, and **not** an accessor
inequality with no inhabitant.  Nothing here is a conditional shell.

Reader counterpart: **not claimed.**  The reader prints no storage display --
`03-parameterized-construction.tex:71--77` puts the whole Stage-2 family under
"Suppose also that", and `C-effectivity-details.tex:98--100` mentions building
the family only inside a numbered list of machine operations, which this route
never cites as a statement.  Both intervals were opened first-hand this round in
the pinned release copy.  PROVED. -/
theorem storedParams_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d)) (K : LevelConfig)
    (X₁ : Type*) [Fintype X₁] [LinearOrder X₁] (hcard : Fintype.card X₁ = m) :
    ∃ hm : 0 < m,
      (storedParams K q t m hm X₁ hcard).N₂ = N ∧
      (storedParams K q t m hm X₁ hcard).K = K ∧
      NPCC.IsBalancedFamily t (storedParams K q t m hm X₁ hcard).c₂
        (1 / (100 * (t : ℝ))) := by
  obtain ⟨⟨hm, ht, htq⟩, hN, _⟩ := balBuild_eq_some_iff.mp hout
  refine ⟨hm, ?_, storedParams_K K q t m hm X₁ hcard, ?_⟩
  · rw [storedParams_N₂]; exact hN.symm
  · exact storedFamily_isBalanced q t m hm ht htq X₁ hcard

/-! ### Part 14.C: the BLOCK -- the bare `t <= q` guard at the level-step
arguments, registered as kernel-checked fact -/

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY -- the width ceiling at the banked
witness pair.**

`q_2 <= 2^15` at `PublicRecords.publicInputYes` (`K_3`, `gamma = 1/6`,
`Delta = 3`, `D = 3`, `Y = 0`, `b_0 = bout = 1`, `m_R = n_R = 2`) and
`PublicRecords.levelConfigMin` (`c_b = 6` exactly, `B_s = 1`).  Every step is an
*upper bound on a chain*, never an assignment: `A_pre <= 240` from its five
branches at this record (`06:111--115`), hence `u <= 3` (`06:116--117`), hence
`s = 2^{B_s u^2} <= 2^9` at `B_s = 1` (`06:118` through the banked
`ParameterSchedule.sScale_eq_pow`), hence `12 s |E| = 12 s * 3 <= 2^{15}` and so
`q_2 <= 2^{15}` by the banked `GuardedSourceSlab.q2_le_of_le` -- the "least power
of two" minimality of `04:391`, not a computed value of `q_2`.

**BEYOND-PAPER AUDIT.**  Both witnesses are the campaign's own banked synthetic
objects; the frozen source never visits this point, and the two numerals in the
statement (`2` and its exponent `15`) are this audit's own ceiling, not a
schedule quantity.  No fidelity credit of any kind attaches.

**Disclosed overlap** (see the block docstring): this chain is run inline inside
Part 12's banked `not_fourT2LeQ2_at_publicInputYes`, which is deliberately left
byte-identical rather than rewritten to route through this lemma.

Reader counterpart: **not claimed** -- the reader prints no width ceiling at any
witness.  PROVED. -/
theorem q2For_le_at_publicInputYes :
    LevelStepConstruction.q2For publicInputYes levelConfigMin ≤ 2 ^ 15 := by
  have hs : LevelStepConstruction.sFor publicInputYes levelConfigMin ≤ 2 ^ 9 := by
    have hu : LevelStepConstruction.uAuxFor publicInputYes ≤ 3 := by
      unfold LevelStepConstruction.uAuxFor ParameterSchedule.uAux
      have hA : LevelStepConstruction.ApreFor publicInputYes ≤ 240 := by
        unfold LevelStepConstruction.ApreFor ParameterSchedule.Apre
          LevelStepConstruction.BpubFor LevelStepConstruction.zRFor
          LevelStepConstruction.clEFor ScheduleTemplateResidue.Bpub
          ScheduleTemplateResidue.zRpub
        have h1 : Nat.clog 2 2 ≤ 1 := Nat.clog_le_of_le_pow (by norm_num)
        have h2 : Nat.clog 2 (Fintype.card (Fin 3) + 2) ≤ 3 := by
          simp only [Fintype.card_fin]
          exact Nat.clog_le_of_le_pow (by norm_num)
        simp only [publicInputYes]
        omega
      have hinner : Nat.clog 2 (LevelStepConstruction.ApreFor publicInputYes + 16) ≤ 8 :=
        Nat.clog_le_of_le_pow (by omega)
      exact le_trans (Nat.clog_mono_right 2 hinner)
        (Nat.clog_le_of_le_pow (by norm_num))
    rw [LevelStepConstruction.sFor, ParameterSchedule.sScale_eq_pow]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have hb : levelConfigMin.Bs = 1 := rfl
    rw [hb, one_mul]
    calc LevelStepConstruction.uAuxFor publicInputYes ^ 2 ≤ 3 ^ 2 :=
          Nat.pow_le_pow_left hu 2
      _ = 9 := by norm_num
  refine GuardedSourceSlab.q2_le_of_le publicInputYes.G _ ?_
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  rw [hcard]
  calc 12 * LevelStepConstruction.sFor publicInputYes levelConfigMin * 3
      ≤ 12 * 2 ^ 9 * 3 :=
        Nat.mul_le_mul_right 3 (Nat.mul_le_mul_left 12 hs)
    _ ≤ 2 ^ 15 := by norm_num

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY -- THE BARE GUARD, which is what
actually blocks item (b).**

`balBuild_eq_some`'s third hypothesis is the **bare ordering** `t <= q` that the
paper's own builder interface states at `14:1557--1558` ("For positive integers
`q,t,m` with `q >= t >= 1`") and supplies as *data* at `14:1621--1622`
("positive integers `q_{2,i} >= t_{2,i} >= 1`").  Part 12's two banked negatives
concern the **4x structural** row `4 t_2 <= q_2` of `eq:stage2-structural-gates`
(`06:835`), and `¬ (4 t_2 <= q_2)` does **not** entail `¬ (t_2 <= q_2)` -- so
before this round the route had no receipt for the guard the builder actually
asks for.  This is that receipt.

The evaluation is again a chain, with nothing assigned: `q_2 <= 2^{15}` is
`q2For_le_at_publicInputYes`, while `k_2 >= 2^{19}` (`06:766`, through the banked
`WrapperMassRedistribution.k2_floors_of_K2Pred` at
`K2Pred_at_k2For`) and `t_2 = 2^{k_2}` (`06:770`) give `t_2 >= 2^{16}`.

**BEYOND-PAPER AUDIT / NON-FIDELITY.**  This audits *this development's*
unrestricted `(Public, K)` domain at the campaign's own banked witnesses.  It is
**not** a statement about the paper and does not refute `06:835`: the frozen verb
at `06:830` is *verify*, the row is item (v) of the finite condition list
`06:1197--1226` (at `06:1219--1220`), and its discharge is the threshold of
`sec:effective-cutoff` (`06:1169--1177`), whose machinery this route has not
built.  It also does **not** claim failure at every `(P, K)`.

Reader counterpart: **not claimed** -- the reader prints `4t_2 <= q_2` at
`03-parameterized-construction.tex:73` under the "Suppose also that" of `:71`, as
a supposition and never as a stated result, so there is no reader item for the
declaration below to discharge and none is assigned.  PROVED. -/
theorem not_t2ForLeQ2For_at_publicInputYes :
    ¬ t2For publicInputYes levelConfigMin
        ≤ LevelStepConstruction.q2For publicInputYes levelConfigMin := by
  intro hrow
  have hk : 2 ^ 19 ≤ k2For publicInputYes levelConfigMin :=
    (WrapperMassRedistribution.k2_floors_of_K2Pred.{0}
      (K2Pred_at_k2For publicInputYes levelConfigMin)).2.1
  have hk16 : 16 ≤ k2For publicInputYes levelConfigMin :=
    le_trans (by norm_num) hk
  have ht : t2For publicInputYes levelConfigMin
      = 2 ^ k2For publicInputYes levelConfigMin := rfl
  have hlow : (2 : ℕ) ^ 16 ≤ t2For publicInputYes levelConfigMin := by
    rw [ht]
    exact Nat.pow_le_pow_right (by norm_num) hk16
  have hbad : (2 : ℕ) ^ 16 ≤ 2 ^ 15 :=
    le_trans hlow (le_trans hrow q2For_le_at_publicInputYes)
  norm_num at hbad

/-- **BEYOND-PAPER AUDIT / NON-FIDELITY -- the universal form.**  No theorem of
this development asserts the builder's own guard `t_2 <= q_2` at every carrier
pair and every `(Public, K)`: the universal statement already fails at the banked
witness above.  This is the exact sibling of Part 12's
`fourT2LeQ2_not_schedule_theorem` one step sharper, at the bare ordering rather
than at the `4x` row.

**Generalized over the carriers.**  `V` and `E` are quantified at the single
universe `Type` this route's carriers inhabit (the convention Part 9 records,
`02:799--806`); the instantiation to `Fin 3` occurs only inside the proof term,
never in this statement.

**Why the negation is not vacuous.**  `¬ ∀ ...` would be cheap if the quantified
domain were empty.  It is not: `PublicRecords.publicInputYes` and
`PublicRecords.levelConfigMin` inhabit it, and the proof is a genuine
counterexample rather than a vacuity argument.

**SCOPE, narrowed deliberately.**  This refutes the *universal accessor
theorem*.  It does **not** establish failure at every `(P, K)`, and it does
**not** refute the paper's eventual cutoff-generated legal instances.  The
correct conclusion is only that no unconditional accessor-level success theorem
is authorable today.

Reader counterpart: **not claimed** -- see the previous declaration.  PROVED. -/
theorem t2LeQ2_not_schedule_theorem :
    ¬ ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
        (P : LevelPublicInput V E) (K : LevelConfig),
        t2For P K ≤ LevelStepConstruction.q2For P K :=
  fun h => not_t2ForLeQ2For_at_publicInputYes (h (Fin 3) (Fin 3) publicInputYes levelConfigMin)

/-- **THE BLOCK, IN THE KERNEL** -- `A_bal`, called at this route's own
level-step arguments and evaluated at the campaign's banked legal witness pair,
returns the **reserved failure output** of `14:1743--1745`.

The three arguments are exactly item (b)'s (`14:1621--1625`), each pinned to its
banked owner and none chosen here: `q_{2,i}` is
`LevelStepConstruction.q2For` (`05:329--332` / `04:389--391`), `t_{2,i}` is Part
11's `t2For` (`eq:t2-search` `06:763--770` through `eq:Hmax` `06:754--762`), and
`m_{1,i} = |Rows(M_1^{(i)})|` is `Fintype.card (LevelStepConstruction.StepRowsOne)`
(Part 10).  The proof is the banked rejection probe
`balBuild_eq_none_of_q_lt_t` applied to the bare-guard receipt above.

**This is the honest form of the gap: BLOCK, not bridge.**  The alternative
shapes were all refused.  A success theorem is false here.  A *conditional*
success theorem carrying `t2For P K <= q2For P K` in hypothesis position is the
barred fifth generation of a class deleted four times on this route (recorded at
`EffectiveCutoffCertificate.lean`, item 7 of its `cc-t7s-r3` block), because that
hypothesis has no inhabitant anywhere in the repository.  What is authorable and
true is this: the call, made where this route can make it, fails -- and it fails
for the reason `06:830--831` names, namely that the structural verification
which must precede the construction has not been performed, because the machinery
that performs it (`sec:effective-cutoff` `06:1169--1177`, reached as item (v) of
`06:1197--1226` at `06:1219--1220`; `PARAM-001`) is not built.

**BEYOND-PAPER AUDIT / NON-FIDELITY.**  The witness pair is ours, not the
paper's; the paper's own instance of item (b) is cutoff-generated and remains
**canonical-DEFERRED**.  Item (b) of `S5-BALANCED-FAMILY` and every open item of
`S5-BALANCED-FAMILY-LEVELSTEP-001` are **UNCHANGED and OPEN**: this theorem
registers the blocker, and registration is not discharge.

Reader counterpart: **not claimed** -- the reader states the governing row as a
supposition (`03-parameterized-construction.tex:71--73`) and prints no failure
branch of the builder.  PROVED. -/
theorem balBuild_eq_none_at_publicInputYes :
    balBuild (LevelStepConstruction.q2For publicInputYes levelConfigMin)
        (t2For publicInputYes levelConfigMin)
        (Fintype.card
          (LevelStepConstruction.StepRowsOne publicInputYes levelConfigMin))
      = none :=
  balBuild_eq_none_of_q_lt_t _ (not_le.mp not_t2ForLeQ2For_at_publicInputYes)


/-! ## Part 15: the balanced-family **materialization spine** --
`06:859--861`'s "construct ... then materialise", from the builder's own output
to the trace field of `14:1634--1635`

**Charter of this part (`cc-t8s` lane 2, `[opus-direct]`).**  Part 14 landed
`eq:effective-balanced-builder` at the machine's own output and recorded, in the
kernel, why the *level-step* call of item (b) is blocked.  This part takes the
next statement layer of the paper's own builder: what `06:859--861` calls for
*after* the family is built.

### The frozen ordering, read first-hand this round

`06:850--861`, in the frozen release source, sets

  `eps_2 = 1/(100 t_2)`,
  `eps_prod = max{(1+eps_2)^{t_2} - 1, 1 - (1-eps_2)^{t_2}} < 1/50`
  (`eq:epsilon-product`, label `06:857`)

and then says, verbatim at `06:859--861`:

  "Construct the one indexed `(q_2,t_2,eps_2)`-balanced family `C_2`, then
  materialise `M_2, M_3`, the source rows, and all protected multiplicities.
  Only now do we evaluate the integer cardinalities `lambda_T, m_T, a_min` and
  the remaining ceiling terms."

`sections/14`'s realization clause (b) spells the same order out as data.
`14:1621--1625`: "For every `0 <= i < k`, the public record `Public_i`, positive
integers `q_{2,i} >= t_{2,i} >= 1`, and the literal output `(N_{2,i}, d_i)` of
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})`, where `m_{1,i} = |Rows(M_1^{(i)})|`."
`14:1626--1632`: "If `e_i : [m_{1,i}] -> Rows(M_1^{(i)})` is the canonical
increasing equivalence, the family actually stored in the parameter record is
`c_{2,i}(l)(r) = e_i(c_{d_i}(l)(r))`, `Pi_i = (K_*, N_{2,i}, c_{2,i})`."
`14:1634--1635`: "The trace field is literally
`T_i = LevelStep(Public_i, Pi_i)`."

So the spine is one chain: **builder output -> stored family `c_{2,i}` ->
record `Pi_i` -> materialised `M_2`, `M_3` -> trace field `T_i`.**  Parts 6, 7
and 14 own the first three links.  What had no owner before this part is the
**fourth**: `06:859--860`'s "then materialise `M_2, M_3`" *at the builder's own
family*, i.e. the equations that show the materialised Stage-2 and Stage-3
objects read the literal Horner accessor `eq:literal-balanced-accessor`
(`14:1774--1778`) through the canonical increasing equivalence, with nothing
free left between them.

Index-verified openings this part addresses (`docs/BANKED_SURFACE_INDEX.md`,
opened first-hand): `14:1621--1635`, `14:1623--1625`, `14:1625--1628`,
`14:1626--1632`, `14:1629--1633`, `14:1634--1635` and `06:857--860` each read
*(no declaration owner)*.

### The frame, and why it is the paper's own

`14:1557--1558` quantifies the whole builder interface over **free positive
integers** `q, t, m` with `q >= t >= 1`, and `14:1626` states the storage step at
a general carrier at its own cardinality.  This part stays exactly there.  Two
consequences, both deliberate:

* The paper's data condition `1 <= t_{2,i} <= q_{2,i}` (`14:1621--1622`) is
  **recovered from the machine's success** through Part 14's
  `balBuild_eq_some_iff`, never assumed as a bare accessor ordering.  The
  antecedent `balBuild q t m = some (N, d)` is inhabited at every legal triple
  (`balBuild_eq_some`), so nothing below is a conditional shell.
* **The level-step `A_bal` call is NOT authored here, in success form or in
  conditional form, under any name.**  That class has been deleted four times on
  this route (`EffectiveCutoffCertificate`, item 7 of its `cc-t7s-r3` block) and
  Part 14.C banks the reason in the kernel: at the campaign's own witness pair
  the builder returns the reserved failure output
  (`balBuild_eq_none_at_publicInputYes`).  The spine's endpoint at the level step
  is therefore reached only through Part 13's **NON-FIDELITY storage-shape
  probe**, and only as anonymous `example`s carrying that same label.

### ALREADY-OWNED, consumed by pin and never restated

* The Stage-2 value clause at a *free* family: `PublicRecords.levelTrace_M₂_apply`
  (`T.M₂ (alpha,gamma) l = T.M₁ (Pr.c₂ l alpha) gamma`),
  `StageTwoRelaxed.stageTwo_eq_stageOne_at_family`, and
  `LevelStepConstruction.levelStep_steps_are_banked` /
  `.levelStep_M₃_resolves_to_source` (`07:225--226`, `07:497`, `08:262--263`).
  **Disclosed relation:** the two materialisation lemmas below are *not* those
  statements.  Each resolves **two further layers** that no banked declaration
  crosses -- the storage identification `14:1629--1631` and the literal accessor
  `eq:literal-balanced-accessor` -- so their right-hand sides carry the base-`p`
  Horner value itself, not a free `Pr.c₂`.  Nothing owned is re-proved: the two
  constructor steps `Section5Admissibility.stepMTwo` / `.stepMThree` are consumed
  by pin, the equivalence is the banked `IteratedCanonicalChaining.canonEquiv`,
  and the family is Part 6's `balFamily`.
* Part 14's `balBuild_eq_some_iff`, `storedParams_at_balBuild_output`,
  `effectiveBalancedBuilder`; Part 7's `storedFamily`, `storedParams`,
  `storedParams_K`, `storedParams_N₂`, `storedFamily_isBalanced`,
  `storedFamily_not_constant`; Part 8's `balFamily_isBalanced` and the
  BEYOND-PAPER `balFamily_isBalanced_nondegenerate`; Part 2's `balN_le_bBal`;
  `ScheduleMajorantResidue.bBal`.  **No second descriptor, accessor, family,
  record, envelope or gate predicate is introduced, this part adds no `def` and
  no `structure` at all, and none of the ten names barred at `cc-t8c` is revived
  under any spelling.**

### Import direction (verified this round, not asserted)

`Section5Admissibility.stepMTwo` (`Section5Admissibility.lean:1939`) and
`.stepMThree` (`:1914`) are reached without a new import:
`BalancedFamilyBuilder.lean:3` imports `LevelStepConstruction`,
`LevelStepConstruction.lean:1` imports `MechanicalCompilerResidue`, and
`MechanicalCompilerResidue.lean:12` imports `Section5Admissibility`.  Importer,
importee and import line are named for each hop; the direction is
consumer-downstream throughout and **no import line is added to this module**.

### Statement-numeral screen (this part's own occurrences)

* `100` in `1 / (100 * (t : ℝ))` -- CANONICAL-FORM, the frozen accuracy
  `1/(100t)` of `eq:effective-balanced-builder` (`14:1591--1592`), carried
  verbatim from the banked `storedFamily_isBalanced`.
* `0` and `1` as the two `Fin` index literals in the separation lemma -- these
  are the least two zero-based slots of `conv:finite-slots` (`02:14--18`), the
  same pair the banked `storedFamily_not_constant` / `balFamily_not_constant`
  separate, and their bounds are the *derived* `balN_pos` and `one_lt_balN`, not
  assigned values.  EVALUATED through those defining chains.

No other numeric literal occurs in any statement of this part.

### Binder provenance

* `q, t, m` -- GENUINELY-FREE at `14:1557--1558`, which quantifies the whole
  builder interface over them; the ruling of ledger row
  `S5-BALANCED-FAMILY-BUILDER-001`, unchanged.
* `N, d` -- **not free in substance**: they are the machine's output, pinned by
  the hypothesis `balBuild q t m = some (N, d)` through `balBuild_eq_some_iff`,
  which is exactly how `14:1623` supplies them ("the literal output
  `(N_{2,i}, d_i)`").
* `X₁` with `Fintype.card X₁ = m` -- GENUINELY-FREE at `14:1626`, which states
  the increasing equivalence at a general carrier at its own cardinality; the
  ruling `storedFamily` already carries.
* `C₁`, `M₁` -- GENUINELY-FREE here for the reason the banked
  `Section5Admissibility.stepMTwo` records at its own binders: "`M₁` is the
  Stage-1 matrix, an input because `L2` is unbuilt", and this is the general
  constructor step, not a paper-facing endpoint.
* `s` -- GENUINELY-FREE here on the same banked ruling, stated at
  `Section5Admissibility.stepMThree`: "Both binders are GENUINELY-FREE *here*
  and pinned at the call site ... `s` is instantiated only at
  `partialTailAssembler`".  This part instantiates it nowhere.
* `K : LevelConfig` -- GENUINELY-FREE at `05:176`, the record's own first field
  (`def:level-parameters`); the ruling `LevelStepConstruction.LevelParamsFor`
  carries.
* `hsep` (the separation hypothesis of the pole lemma) -- an explicit binder, not
  a bundle: it says only that `M₁` distinguishes two given rows.

**Zero source-defined quantity enters as a free binder.**  In particular `q_2`,
`t_2` and `m_1` do **not** appear as binders anywhere in this part: at the level
step they are `LevelStepConstruction.q2For`, Part 11's `t2For` and
`Fintype.card (LevelStepConstruction.StepRowsOne ...)`, and this part reaches
them only inside Part 13's probe, through that probe's own banked applications.

### What this part does NOT claim

* It does **not** discharge item (b) of `S5-BALANCED-FAMILY`, nor any open item
  of `S5-BALANCED-FAMILY-LEVELSTEP-001`.  Both stay **OPEN**; the canonical
  inhabitation of the level-step call stays canonical-DEFERRED behind the cutoff
  machinery of `06:1169--1226` and `PARAM-001`.  Registration is not discharge.
* It states no gate of `eq:stage2-structural-gates` (`06:835`) and carries
  neither `4 t_2 <= q_2` nor `t_2 <= q_2` in hypothesis position, here or
  anywhere.
* It reaches **no** expander interface: `EXPANDER-001` has no Lean declaration by
  design, and the vendored cited-existence `NPCC.aghp_balanced_family_exists` is
  deliberately not adopted -- the whole point of `sections/14` is that this family
  is built.  **Zero new axioms.**
* It says nothing about `eps_prod` beyond quoting `06:851--858` above: that
  display is owned by `Section5Admissibility.epsProd` / `.epsProd_lt_fiftieth`
  and is consumed by pin, not restated.
* `MATERIALIZE-001`'s machine layer (`A_realize`, `A_entry`, `A_materialize`,
  codecs, padding maps) stays bucket-(c) DEFERRED: this part is the mathematical
  statement layer only.
* `06:861--873`'s "Only now do we evaluate `lambda_T, m_T, a_min`" and
  `eq:physical-stage4-gates` are **not** stated here; they are the materialised
  *gate* layer, whose carriers are
  `Section5Admissibility.PhysicalStage4Gates` and
  `EffectiveCutoffCertificate.MaterializedStageTwoFamily`, both consumed by pin
  by their own owners and neither re-authored.

### Canonical inhabitation

For the general layer the canonical inhabitant **is the paper's own object**:
the family built by `14:1749--1763` and read by `14:1768--1782`, at every triple
the builder's own interface admits, stored by `14:1629--1631` along the canonical
increasing equivalence.  The antecedent of the deliverable is inhabited at every
legal triple, witnessed below by an anonymous `example` over `balBuild_eq_some`;
non-degeneracy of the hypothesis bundle is the banked BEYOND-PAPER audit
`balFamily_isBalanced_nondegenerate`, **consumed as that evidence and not
re-authored**.  For the *level-step* layer there is no canonical inhabitant on
this route, which is why every level-step readout below is an anonymous
`example` over Part 13's NON-FIDELITY probe and carries that label.

Reader counterpart: **not claimed**, for the reason Part 14 records and which was
re-verified first-hand this round in the pinned release copy
(`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/reader-facing`).
The reader's one balanced-family item `lem:paper-explicit-balanced-family`
(`C-effectivity-details.tex:31--46`, proof `48--76`) is already assigned to Part
8's `balFamily_isBalanced`, and this route assigns one reader item to one
declaration.  The nearest reader sentence to this part's subject is
`C-effectivity-details.tex:98--100` ("build the indexed Stage--2 family using
`lem:paper-explicit-balanced-family`, resume the post-family compiler checks with
its returned cardinality, and form `M_2, M_3, B`") -- but that is item 3 of a
numbered list of *machine operations* inside prose, which this route never cites
as a statement, exactly as Part 13 and Part 14 recorded.  The reader's Stage-2
family itself is printed under "Suppose also that"
(`03-parameterized-construction.tex:71--77`), a supposition, never a stated
result. -/

/-! ### Part 15.A: "then materialise `M_2, M_3`" at the builder's own family -/

/-- **AUX 1 (`06:859--860` at the builder's output): the materialised Stage-2
entry is the literal Horner accessor, read through `e_i`.**

`Section5Admissibility.stepMTwo` is `L3`'s derived half, the frozen Stage-2 value
clause `M_2((alpha,gamma), l) = M_1(c^{(l)}(alpha), gamma)` (`07:225--226`),
consumed by pin.  What is new is the *composite*: instantiate its family binder
at the family `14:1629--1631` actually stores, `c_{2,i} = e_i o c_{d_i}`, and the
right-hand side resolves all the way down to
`eq:literal-balanced-accessor` (`14:1774--1778`) --
`(sum_{r<t} a_r(l) alpha^r mod p) mod m` at the scanned prime of
`14:1754--1758` -- transported into the row carrier by the banked canonical
increasing equivalence of `14:1626`.

**Why this is not a restatement.**  `PublicRecords.levelTrace_M₂_apply` and
`StageTwoRelaxed.stageTwo_eq_stageOne_at_family` state the same clause at a
*free* `Pr.c₂`; no banked declaration crosses either the storage identification
or the accessor, so no banked declaration has this right-hand side.  This is the
first statement on the route in which the materialised Stage-2 object and the
builder's arithmetic appear in the same equation.

General in `q, t, m`, in the row carrier at its own cardinality, in the Stage-1
column carrier and matrix, and in all three indices.  No parameter is
instantiated and the prime scan is never evaluated.  Reader counterpart: **not
claimed** (see the block docstring).  PROVED. -/
theorem storedFamily_materialises_M₂ (q t m : ℕ) (hm : 0 < m) (X₁ : Type*)
    [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m)
    {C₁ : Type*} (M₁ : X₁ → C₁ → Bool)
    (α : Fin q) (γ : C₁) (l : Fin (balN q t m)) :
    Section5Admissibility.stepMTwo M₁ (storedFamily q t m hm X₁ h) (α, γ) l
      = M₁ (canonEquiv X₁ h
              ⟨balEntryVal (balPrime q t m) t m (l : ℕ) (α : ℕ),
               balEntryVal_lt hm (balPrime q t m) t (l : ℕ) (α : ℕ)⟩) γ :=
  rfl

/-- **AUX 2 (`06:859--860`, second object): the materialised Stage-3 entry
resolves to the same accessor value at the selected coordinate.**

`Section5Admissibility.stepMThree` is `L4`, `M_3 = Int_s(M_2^T)` (`07:495--497`,
`08:262--263`), consumed by pin.  Composed with AUX 1 it says that the Stage-3
entry at `(i, l)` against a column tuple `x` is the Stage-1 entry at the row the
builder's accessor names for the `i`-th selected coordinate -- so the whole
`06:859--860` materialisation of both objects is a function of the builder's
output and nothing else.

**Disclosed relation.**  `LevelStepConstruction.levelStep_M₃_resolves_to_source`
resolves the *constructed trace's* `M_3` to the public seed `P.R` at a **free**
`Pr.c₂`; this lemma resolves the *general* constructor step at the **builder's
own stored family**, at a general Stage-1 matrix.  Neither implies the other and
neither is restated.

General in `q, t, m`, the two carriers, the Stage-1 matrix, the scale, and all
three indices.  Reader counterpart: **not claimed**.  PROVED. -/
theorem storedFamily_materialises_M₃ (q t m : ℕ) (hm : 0 < m) (X₁ : Type*)
    [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m)
    {C₁ : Type*} (M₁ : X₁ → C₁ → Bool) (s : ℕ)
    (i : Fin s) (l : Fin (balN q t m)) (x : Fin s → Fin q × C₁) :
    Section5Admissibility.stepMThree
        (Section5Admissibility.stepMTwo M₁ (storedFamily q t m hm X₁ h)) s (i, l) x
      = M₁ (canonEquiv X₁ h
              ⟨balEntryVal (balPrime q t m) t m (l : ℕ) ((x i).1 : ℕ),
               balEntryVal_lt hm (balPrime q t m) t (l : ℕ) ((x i).1 : ℕ)⟩)
          (x i).2 :=
  rfl

/-- **AUX 3 (STATEMENT POLE / non-vacuity): the materialisation genuinely reads
the constructed family.**

The two equations above would be equally true of a *constant* stored family, and
`PublicRecords.levelParams_admits_unbalanced_family` banks that a constant family
is a perfectly legal `Pi`.  This lemma closes that escape on the materialised
side: whenever the Stage-1 matrix separates two rows at all, the materialised
Stage-2 object separates the builder's first two indices.  So `06:859--860`'s
"construct ... then materialise" is not a vacuous composition -- the constructed
family is visible in `M_2`.

The two separated rows are the banked `storedFamily_not_constant`'s, and the two
index literals are the least two zero-based slots of `conv:finite-slots` with
their *derived* bounds `balN_pos` and `one_lt_balN`; no value is chosen here.

General in `q, t, m`, both carriers and the Stage-1 matrix.  Reader counterpart:
**not claimed**.  PROVED. -/
theorem storedFamily_materialises_M₂_separates (q t m : ℕ) (hm : 0 < m)
    (ht : 0 < t) (hq : 0 < q) (X₁ : Type*) [Fintype X₁] [LinearOrder X₁]
    [Nontrivial X₁] (h : Fintype.card X₁ = m)
    {C₁ : Type*} (M₁ : X₁ → C₁ → Bool)
    (hsep : ∀ u v : X₁, u ≠ v → ∃ γ : C₁, M₁ u γ ≠ M₁ v γ) :
    ∃ γ : C₁,
      Section5Admissibility.stepMTwo M₁ (storedFamily q t m hm X₁ h)
          (⟨0, hq⟩, γ) ⟨0, balN_pos q t m⟩
        ≠ Section5Admissibility.stepMTwo M₁ (storedFamily q t m hm X₁ h)
          (⟨0, hq⟩, γ) ⟨1, one_lt_balN q t m ht⟩ :=
  hsep _ _ (storedFamily_not_constant q t m hm ht hq X₁ h)

/-- **AUX 4 (round trip): the storage step is undone by the same equivalence.**

`14:1629--1631` stores `c_{2,i} = e_i o c_{d_i}`, and `12:98--104` says `e_i` is
an *equivalence* determined by the carrier.  So the stored family loses nothing:
applying `e_i^{-1}` returns the builder's own `[m]`-valued family exactly.  This
is what makes the two materialisation equations above statements about the
builder rather than about the reindexing, and it is the identity law behind
`isBalancedFamily_congr_equiv`'s transport.

General in `q, t, m`, the carrier at its own cardinality, and both indices.
Reader counterpart: **not claimed**.  PROVED. -/
theorem storedFamily_canonEquiv_symm (q t m : ℕ) (hm : 0 < m) (X₁ : Type*)
    [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m)
    (l : Fin (balN q t m)) (r : Fin q) :
    (canonEquiv X₁ h).symm (storedFamily q t m hm X₁ h l r)
      = balFamily q t m hm l r :=
  (canonEquiv X₁ h).symm_apply_apply _

/-! ### Part 15.B: the deliverable -- one statement for the spine
`14:1621--1633` composed with `06:859--860` -/

/-- **THE DELIVERABLE OF PART 15** -- the materialization spine: from a single
successful run of `A_bal` to the record `Pi` of `14:1632` and the materialised
`M_2, M_3` of `06:859--860`, in the frozen order, at the paper's own free
quantification (`14:1557--1558`).

The six conclusions, in the frozen order of `14:1621--1633` and `06:859--860`:

* `Pi.K = K_*` (`14:1632`) -- the configuration slot is the one the record was
  built at;
* `Pi.N_2 = N` (`14:1622--1624`) -- the record's family size **is** the literal
  output of the machine, not an assigned value; this is Part 14's weld, applied;
* `N <= B_bal(q,t,m)` (`14:1588`) -- the **non-strict** envelope clause at the
  machine's own output; the strict display's owner is `balN_lt_bBal` (`R-17`);
* `c_2` is indexed `(q, t, 1/(100t))`-balanced (`14:1591--1592` transported by
  `14:1629--1631`) -- the clause holds where the Stage-2 consumer reads it;
* the materialised `M_2` entry equation (`06:859--860` through
  `07:225--226`), resolved to `eq:literal-balanced-accessor`;
* the materialised `M_3` entry equation (`06:859--860` through
  `07:495--497`), likewise resolved.

**Every hypothesis of the paper's data condition is recovered, none assumed.**
The single antecedent is the machine's own success.  `0 < m`, `1 <= t` and
`t <= q` -- i.e. `14:1621--1622`'s "positive integers `q_{2,i} >= t_{2,i} >= 1`"
-- come *out* of it through Part 14's `balBuild_eq_some_iff`.  No gate, no
accessor inequality and no uninhabited premise appears.

**STATEMENT POLE.**  The only bound variable is the *proof* `hm : 0 < m`, which
is proof-irrelevant, so there is no witness a trivial inhabitant could supply:
this is a named-def claim about the pinned construction, and every object it
speaks of is the banked `storedParams` / `storedFamily` at the arguments the
antecedent fixes.  The three data slots a reader might expect to be existential
are pinned instead: `N` and `d` by `balBuild_eq_some_iff`, and `c_2` by Part 14's
`entryEq_determines_balFamily` together with the storage equivalence's
injectivity.  Where the conclusion could still have been met vacuously -- the two
materialisation equations, which a constant stored family also satisfies --
`storedFamily_materialises_M₂_separates` shows it is not.

**SCOPE.**  Free positive integers and a free carrier, exactly as
`14:1557--1558` and `14:1626` are.  It instantiates `q`, `t`, `m` at no
`(Public, K)` accessor, asserts nothing about
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})`, and discharges **neither** item (b) of
`S5-BALANCED-FAMILY` **nor** any item of `S5-BALANCED-FAMILY-LEVELSTEP-001`.
Part 14.C is the reason and is unchanged by this part.

General in `q, t, m, N, d, K`, the row carrier at its own cardinality, the
Stage-1 column carrier and matrix, and the scale.  Reader counterpart: **not
claimed** (see the block docstring).  PROVED. -/
theorem materializationSpine_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d)) (K : LevelConfig)
    (X₁ : Type*) [Fintype X₁] [LinearOrder X₁] (hcard : Fintype.card X₁ = m)
    {C₁ : Type*} (M₁ : X₁ → C₁ → Bool) (s : ℕ) :
    ∃ hm : 0 < m,
      (storedParams K q t m hm X₁ hcard).K = K ∧
      (storedParams K q t m hm X₁ hcard).N₂ = N ∧
      N ≤ bBal q t m ∧
      NPCC.IsBalancedFamily t (storedFamily q t m hm X₁ hcard)
        (1 / (100 * (t : ℝ))) ∧
      (∀ (α : Fin q) (γ : C₁) (l : Fin (balN q t m)),
          Section5Admissibility.stepMTwo M₁ (storedFamily q t m hm X₁ hcard)
              (α, γ) l
            = M₁ (canonEquiv X₁ hcard
                    ⟨balEntryVal (balPrime q t m) t m (l : ℕ) (α : ℕ),
                     balEntryVal_lt hm (balPrime q t m) t (l : ℕ) (α : ℕ)⟩) γ) ∧
      (∀ (i : Fin s) (l : Fin (balN q t m)) (x : Fin s → Fin q × C₁),
          Section5Admissibility.stepMThree
              (Section5Admissibility.stepMTwo M₁ (storedFamily q t m hm X₁ hcard))
              s (i, l) x
            = M₁ (canonEquiv X₁ hcard
                    ⟨balEntryVal (balPrime q t m) t m (l : ℕ) ((x i).1 : ℕ),
                     balEntryVal_lt hm (balPrime q t m) t (l : ℕ) ((x i).1 : ℕ)⟩)
                (x i).2) := by
  obtain ⟨⟨hm, ht, htq⟩, hN, _⟩ := balBuild_eq_some_iff.mp hout
  refine ⟨hm, storedParams_K K q t m hm X₁ hcard, ?_, ?_,
    storedFamily_isBalanced q t m hm ht htq X₁ hcard,
    fun α γ l => storedFamily_materialises_M₂ q t m hm X₁ hcard M₁ α γ l,
    fun i l x => storedFamily_materialises_M₃ q t m hm X₁ hcard M₁ s i l x⟩
  · rw [storedParams_N₂]; exact hN.symm
  · rw [hN]; exact balN_le_bBal q t m ht

/-! ### Part 15.C: the spine's endpoint `14:1634--1635`, at Part 13's
NON-FIDELITY probe

`14:1634--1635` reads "The trace field is literally
`T_i = LevelStep(Public_i, Pi_i)`."  On this route the only `Pi` typed at the
level step's own carrier and width is Part 13's **NON-FIDELITY storage-shape
probe** `stepLevelParamsFor`, which supplies none of `14:1621--1622`'s data
precondition -- and Part 14.C banks, in the kernel, that the paper's own
successful call is unavailable here.  So the endpoint is recorded exactly as Part
13 records its own readouts: **anonymous `example`s**, minting no name, carrying
the probe's NON-FIDELITY label, and cited from the ledger by `file:line`.  None
of them is fidelity evidence and none discharges anything.

The first `example` is different in kind: it is the **canonical-inhabitation
receipt for Part 15.A/15.B's antecedent**, and it *is* the paper's own object. -/

-- CANONICAL INHABITATION of the deliverable's antecedent: at every triple the
-- builder's own interface admits (`14:1557--1558`), the machine succeeds and
-- returns the paper's own `(N, d_bal)` -- `N = p^t` for the scanned prime of
-- `14:1754--1758` and the frozen `(poly-v1, p)` descriptor of `14:1762--1763`.
-- Banked owner: `balBuild_eq_some` (`:857`).  Non-degeneracy of the bundle is
-- the banked BEYOND-PAPER `balFamily_isBalanced_nondegenerate` (`:2020`),
-- consumed as that evidence and not re-authored.
example (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q) :
    balBuild q t m = some (balN q t m, balDescriptor q t m) :=
  balBuild_eq_some hm ht htq

section MaterializationSpineEndpoint

attribute [local instance] LevelStepConstruction.CanonicalRowOrder.stepRowsOneOrder

-- NON-FIDELITY (Part 13's probe): `14:1634--1635`'s trace field, materialised.
-- The trace's Stage-2 object at `T_i = LevelStep(Public_i, Pi_i)` reads the
-- probe's stored family through the Stage-1 matrix of the same `(Public, K)`.
-- Banked owners: `LevelStepConstruction.levelStep` (`:1426`) and
-- `PublicRecords.levelTrace_M₂_apply`, at Part 13's `stepLevelParamsFor`.
example (P : LevelPublicInput V E) (K : LevelConfig)
    (α : Fin (LevelStepConstruction.q2For P K))
    (γ : LevelStepConstruction.StepColsOne P K)
    (l : Fin (stepLevelParamsFor P K).N₂) :
    (LevelStepConstruction.levelStep P (stepLevelParamsFor P K)).M₂ (α, γ) l
      = LevelStepConstruction.stageOneFor P K
          ((stepLevelParamsFor P K).c₂ l α) γ :=
  rfl

-- NON-FIDELITY (Part 13's probe): the same trace field, resolved one layer
-- further -- the probe's stored family IS the builder's family reindexed by the
-- canonical increasing equivalence of `14:1626`, so the trace's Stage-2 entry is
-- the literal Horner accessor `eq:literal-balanced-accessor` at the level step's
-- three arguments.  This is the spine's endpoint display, at the only `Pi` this
-- route can type -- and it is *not* the paper's instance.
-- Banked owner: `storedParams_c₂` (`:1091`), at Part 13's probe.
example (P : LevelPublicInput V E) (K : LevelConfig)
    (α : Fin (LevelStepConstruction.q2For P K))
    (γ : LevelStepConstruction.StepColsOne P K)
    (l : Fin (balN (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K)))) :
    (LevelStepConstruction.levelStep P (stepLevelParamsFor P K)).M₂ (α, γ) l
      = LevelStepConstruction.stageOneFor P K
          (canonEquiv (LevelStepConstruction.StepRowsOne P K) rfl
            (balFamily (LevelStepConstruction.q2For P K) (t2For P K)
              (Fintype.card (LevelStepConstruction.StepRowsOne P K))
              (stepRowsOne_card_pos P K) l α)) γ :=
  rfl

-- NON-FIDELITY (Part 13's probe): `06:859--860`'s second materialised object at
-- the same trace field.  `M_3 = Int_s(M_2^T)` at the level step's own scale
-- `s = sFor P K`, with the same accessor value at the selected coordinate.
-- Banked owner: `LevelStepConstruction.levelStep_steps_are_banked` (`:1508`),
-- composed with this part's `storedFamily_materialises_M₃`.
example (P : LevelPublicInput V E) (K : LevelConfig)
    (i : Fin (LevelStepConstruction.sFor P K))
    (l : Fin (balN (LevelStepConstruction.q2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))))
    (x : Fin (LevelStepConstruction.sFor P K) →
      Fin (LevelStepConstruction.q2For P K) × LevelStepConstruction.StepColsOne P K) :
    (LevelStepConstruction.levelStep P (stepLevelParamsFor P K)).M₃ (i, l) x
      = LevelStepConstruction.stageOneFor P K
          (canonEquiv (LevelStepConstruction.StepRowsOne P K) rfl
            (balFamily (LevelStepConstruction.q2For P K) (t2For P K)
              (Fintype.card (LevelStepConstruction.StepRowsOne P K))
              (stepRowsOne_card_pos P K) l (x i).1)) (x i).2 :=
  rfl

end MaterializationSpineEndpoint

/-! ## Part 16: `06:861--862`'s **"Only now do we evaluate the integer
cardinalities `lambda_T, m_T, a_min`"** -- the evaluation point, at the
builder's own output

**Charter of this part (`cc-t8t` lane 2, `[opus-direct]`).**  Part 15 took the
`06:859--860` clause "construct the one indexed `(q_2,t_2,eps_2)`-balanced family
`C_2`, then materialise `M_2, M_3`" and landed the two *entry* equations at the
builder's own family.  This part takes the **next clause of the same frozen
sentence** -- the one Part 15 explicitly declined -- namely `06:861--862`:

  "... and all protected multiplicities.  **Only now do we evaluate the integer
  cardinalities `lambda_T, m_T, a_min` and the remaining ceiling terms.**"

The mathematical content of "only now" is a **dependency claim**: those integer
cardinalities are read off the *materialised* Stage-2 object, and the only thing
the balanced-family builder contributes to them is the family size `N_2`.  This
part states that dependency at the machine's own literal output.

### The frozen lines, read first-hand this round

Opened in the frozen release named by `routes/parameterized-np/CURRENT_VERSION`
(`versions/2026-08-02-iteration-cexc-repair/source/autoformalization/sections`):

* `06:851--858`, `eq:epsilon-product` (`\begin{equation}` at `06:851`,
  `eps_2 = 1/(100 t_2)` at `06:852`, the `eps_prod` rows at `06:854--856`,
  `\label` at `06:857`).
* `06:859--862`, the ordered sentence quoted above.  `06:863--873` is
  `eq:physical-stage4-gates`, which this part does **not** state.
* `06:966--967`, inside `eq:stage3-carrier-lower-bound` (`\label` at `06:968`).
  The chain spans **two** lines, not one: `06:966` is
  "`|Cols(M_2)| = N_2 >= m_1^{t_2}`" and `06:967` is
  "`>= 2^{t_2} >= q_2^2 >= 144 s^2 >= 9216 s >= 2 s`".  **Only the leftmost
  equality `|Cols(M_2)| = N_2`, on `06:966`, is taken here**; the chain to its
  right is BLOCKED below.
* `06:979`: "Indeed `m_3 = N_2`, `s <= q`, and `q x_T <= 4/25025`", the paper's
  own evaluation of the Stage-3 row count, whose derivation is `08:262--263`
  (`S_2 = M_2^T`, `m_3 = |Rows(S_2)|`) composed with `06:966`.
* `06:996`: "every Stage-3 template bin is `T_p = {p} x Cols(M_2)`, so
  `|T_p| = N_2`".
* `06:1000--1002`, `eq:physical-template-bin-proof` (`\label` at `06:1003`):
  "`m_T = (u_0 + u_temp)|T_p| = (u_0 + u_temp) N_2 >= N_2 >= 9216 s >= 100`".
  **Only the first equality is taken here**; the rest is BLOCKED below.
* `06:146--147`: "`X_0 = T_raw + S_raw`, `S_raw = V_raw + B_raw`".
* `06:151--154`, `eq:lambda-template-exact` (`\label` at `06:155`):
  "`lambda_T = (1 - 2^{-20}) T_raw/(T_raw + S_raw) + 2^{-21}`".
* `06:170--171`: "`T_raw = s|C_2|` and `S_raw = N_src|Rows(R)|`".
* `09:380`: "`rho_pair = 99/100`", and `09:382--383`:
  "`a_min = (rho_pair + lambda_T^2 - 1)/lambda_T^2`".  The two displays sit on
  **different** lines of the same `gathered` block (`09:378--385`); the banked
  `Section5Admissibility.aMinOf` cites the wider span `09:381--384`.
* `14:1557--1558` (the builder's own free quantification) and `14:1623`
  ("the literal output `(N_{2,i}, d_i)`"), unchanged from Parts 14 and 15.

Index-verified opening this part addresses (`docs/BANKED_SURFACE_INDEX.md`,
opened first-hand): **`06:861--873` reads *(no declaration owner)* with module
doc `BalancedFamilyBuilder`** -- i.e. it is Part 15's own recorded deferral.
This part closes the *evaluation-point* half of it and leaves the *gate* half
blocked, explicitly, below.

### ALREADY-OWNED, consumed by pin and never restated

* `Section5Admissibility.mThreeOf` (`m_3 = N_2`, `06:979`), `.TrawOf`
  (`T_raw = s N_2`, `06:170`), `.SrawOf` (`06:171`), `.lambdaTOf`
  (`eq:lambda-template-exact`), `.aMinOf` (`09:382--383`), `.templateBinCount`
  (`m_T = (u_0+u_temp) N_2`, `06:999--1004`) -- **all six are banked `def`s that
  already take `N_2` as an argument**, which is precisely why "only now do we
  evaluate" is expressible without a single new definition.  This part adds
  **no `def`, no `structure`, no `abbrev`, no instance and no import**.
* `SchedulePhysicalResidue.templateBin_card` (`06:996`, `|T_p| = |Cols|` at a
  free slot type and column carrier) -- consumed by pin, never re-proved.  The
  route's `|T_p|` lemma exists exactly once and it is that one.
* `DenseStageFourOpening.uBase` / `.uTemp` (`eq:protected-multiplicities`,
  `08:103--104`) -- named, never restated.
* Parts 2, 6, 7, 14 and 15 of this module: `balN`, `one_lt_balN`,
  `balN_lt_bBal`, `balBuild_eq_some`, `balBuild_eq_some_iff`, `storedFamily`,
  `storedFamily_isBalanced`, `balDescriptor`.  **None of the ten names barred at
  `cc-t8c` is revived under any spelling.**
* `StageTwoRelaxed.epsTwo` (`eps_2 = 1/(100 t_2)`, `06:852`),
  `StageTwoWidths.t₂_pos` / `.t₂_lt_q₂` -- consumed by pin in the two anonymous
  `example`s only.  `Section5Admissibility.epsProd` / `.epsProd_lt_fiftieth`
  (the `eps_prod < 1/50` half of `eq:epsilon-product`) is **not** restated here,
  exactly as Part 15 recorded.

### Import direction (verified this round, not asserted)

Every cross-module pin below is reached without adding an import line.  Each hop
names importer, importee and the import line's `file:line`:

* `Section5Admissibility.*`: `BalancedFamilyBuilder.lean:3` imports
  `LevelStepConstruction`; `LevelStepConstruction.lean:1` imports
  `MechanicalCompilerResidue`; `MechanicalCompilerResidue.lean:12` imports
  `Section5Admissibility`.
* `DenseStageFourOpening.*`: the same three hops, then
  `Section5Admissibility.lean:4` imports `DenseStageFourOpening`.
* `SchedulePhysicalResidue.*`: `BalancedFamilyBuilder.lean:3` imports
  `LevelStepConstruction`; `LevelStepConstruction.lean:1` imports
  `MechanicalCompilerResidue`; `MechanicalCompilerResidue.lean:3` imports
  `SchedulePhysicalResidue`.
* `StageTwoRelaxed.*`: the first two hops, then
  `MechanicalCompilerResidue.lean:8` imports `StageTwoRelaxed`.

The direction is consumer-downstream throughout.  `LevelStepMaterialisation` and
`EffectiveCutoffCertificate` are **absent** from this module's 124-module import
closure (computed first-hand this round), so nothing of theirs is pinned, and no
statement below is expressible in terms of their carriers.

### BLOCK, not bridge -- the four gaps registered rather than crossed

Each of these is a frozen line *adjacent to* one this part states, and each is
left explicitly unproved with its blocking reason named.  None is weakened,
none is assumed, and no hypothesis bundle smuggles one in.

1. **`eq:stage3-carrier-lower-bound`'s chain `N_2 >= m_1^{t_2} >= ... >= 9216 s`
   (`06:966--967`)** is NOT stated.  The paper derives it from balancedness *at
   the level-step arguments* (`06:955--962`), i.e. from the call
   `A_bal(q_{2,i}, t_{2,i}, m_{1,i})` that **Part 14.C banks as unavailable on
   this route**: at the campaign's own witness pair the builder returns the
   reserved failure output (`balBuild_eq_none_at_publicInputYes`), because
   `06:830--831` requires the structural row `4 t_2 <= q_2` (`06:835`) to be
   verified first and no theorem here concludes it at any `(P, K)`.  BLOCK.
2. **`06:1002`'s `m_T >= N_2 >= 9216 s >= 100`** is NOT stated.  Its owner is
   `SchedulePhysicalResidue.physicalTemplateBin`, whose hypothesis is literally
   `9216 * s <= N₂` -- i.e. item 1.  Restating it here at weaker hypotheses
   would be the duplicate-with-a-hole defect.  BLOCK.
3. **`eq:physical-stage4-gates` (`06:863--873`)** -- the seven rows
   `lambda_T >= 99/100`, `2 s x_T <= 1/100`, `m_T >= 100`, ... -- is NOT stated.
   Its carrier is the banked `Section5Admissibility.PhysicalStage4Gates`, and
   `eq:template-source-ratio` / `eq:lambda-template-window` (`06:163--176`,
   the `99/100 <= lambda_T <= 1 - 2^{-21}` window) rest on the same
   `|C_2| >= (q_1|Rows(R)|)^{t_2}/(1+eps_2)` as item 1.  BLOCK.
4. **`MATERIALIZE-001`'s machine layer** (`A_realize`, `A_entry`,
   `A_materialize`, the codecs and padding maps of `14:1600--1620`) stays
   bucket-(c) DEFERRED.  This part is the mathematical statement layer only.

Consequently this part discharges **neither** item (b) of `S5-BALANCED-FAMILY`
**nor** any item of `S5-BALANCED-FAMILY-LEVELSTEP-001`; both stay OPEN, and the
canonical inhabitation of the level-step call stays canonical-DEFERRED behind
the cutoff machinery of `06:1169--1226` and `PARAM-001`.  Registration is not
discharge.  It reaches **no** expander interface: `EXPANDER-001` has no Lean
declaration by design, `NPCC.aghp_balanced_family_exists` is deliberately not
adopted, `LegacyNPCC.Stage12` is absent from the import closure, and **zero new
axioms** are introduced.

### Statement-numeral screen (this part's own occurrences)

Handled per occurrence in the lane report; every literal in a statement below is
either a CANONICAL-FORM constant of `eq:lambda-template-exact` (`06:151--154`),
the CANONICAL-FORM `rho_pair = 99/100` of `09:380` carried inside the `a_min`
quotient of `09:382--383` (`cc-t8t` r1), or the EVALUATED degeneracy floor `1`
of the deliverable's third conjunct, whose defining chain is
`two_le_balPrime -> one_lt_balN` (`cc-t8t` r2: the floor is discharged from the
banked owner directly, the intermediate window lemma having been deleted).
No numeral is assigned to a source-defined quantity anywhere in this part.

### Binder provenance

* `q, t, m` -- GENUINELY-FREE at `14:1557--1558`; the standing ruling of
  `S5-BALANCED-FAMILY-BUILDER-001`, unchanged.
* `N, d` -- **not free in substance**: the machine's output, pinned by the single
  antecedent `balBuild q t m = some (N, d)` through `balBuild_eq_some_iff`,
  exactly as `14:1623` supplies them.
* `C : Section5Admissibility.ScheduleContext V E` -- GENUINELY-FREE, the ruling
  the banked accessors already carry (`EffectiveCutoffCertificate.lean:1586`,
  "`05:320`, a public input ..."); `s = sOf C`, `S_raw = SrawOf C` and
  `lambda_T = lambdaTOf C` are that context's own evaluated accessors and are
  never re-derived here.
* `X₀, T₀, V₀, B₀` -- GENUINELY-FREE, the ruling
  `Section5Admissibility.templateBinCount` already carries at `08:104`:
  "`X_0` stays a **separate argument**, exactly as `08:104` writes it".
* `Slot`, `p` -- GENUINELY-FREE, the ruling `SchedulePhysicalResidue.templateBin_card`
  already carries ("general in the slot type and the column carrier"), and
  `06:996` quantifies over "every Stage-3 template bin `T_p`".

**Zero source-defined quantity enters as a free binder.**  In particular `N_2`,
`m_3`, `T_raw`, `lambda_T`, `a_min` and `m_T` appear only as the banked
accessors applied to the machine's own output; none of them is a binder.

### Canonical inhabitation

The antecedent's canonical inhabitant is again the paper's own object -- the
machine's success at every triple `14:1557--1558` admits -- and it is receipted
in Part 15 by `balBuild_eq_some`.  **This part adds no sharper inhabitation
receipt** (`cc-t8t` r1, Sol finding 11).  Its first anonymous `example`
universally quantifies the `StageTwoWidths` record, so it exhibits no inhabitant
of the paper's scheduled width record; it is a *conditional specialization* of
banked `balBuild_eq_some`, showing only that **given any** such record -- whose
field `four_t₂_le_q₂` *is* the frozen `4 t_2 <= q_2` of
`eq:stage2-balance-ceilings` -- the ordering `q_2 >= t_2 >= 1` of
`14:1621--1622` is derived from the record rather than assumed, and the builder
then succeeds at `(q_2, t_2, m)` for every `0 < m`.  It stays an anonymous
`example`: this route evidences instantiations by `example`, never by a new
name.  It is **not** a discharge of item (b): a `StageTwoWidths` record
*carries* the gate as a supposition, whereas item (b) needs it *concluded* at
the schedule's own derived `q2For`/`t2For`, which Part 14.C shows fails there.

Reader counterpart: **not claimed**, for the reason Parts 13, 14 and 15 record
and which was re-verified first-hand this round in the pinned release copy.  The
reader's single balanced-family item `lem:paper-explicit-balanced-family`
(`C-effectivity-details.tex:31--46`) is already assigned to Part 8's
`balFamily_isBalanced`, and this route assigns one reader item to one
declaration; the reader prints no `lambda_T`, `m_T`, `a_min` or `m_3` at all
(case-sensitive sweeps of `routes/parameterized-np/reader-facing/` return zero
for each). -/

/-! ### Part 16.A: the two cardinalities the materialised Stage-2 object exposes
(`06:966`, `06:979`, `06:996`) -/

/-- **AUX 1 (`06:966` and `06:979` at the machine's own output): the materialised
Stage-2 column carrier is counted by the literal builder output, and `m_3` is
that count.**

Part 15 materialises `M_2` as
`Section5Admissibility.stepMTwo M₁ (storedFamily q t m hm X₁ h)`, whose **second**
index type -- `Cols(M_2)` -- is `Fin (balN q t m)`.  `06:966` states
`|Cols(M_2)| = N_2`; the first conjunct is that equation with `N_2` resolved to
the machine's literal output `N` of `14:1623`.  `06:979` then states
`m_3 = N_2`, derived at `08:262--263` from `S_2 = M_2^T` and
`m_3 = |Rows(S_2)|`; the second conjunct is that equation at the same point.

**Why this is not a restatement.**  `Section5Admissibility.mThreeOf_eq_display`
states `m_3 = N_2` at a *free* `N₂`, and `storedParams_N₂` states
`Pi.N_2 = balN q t m` at the *record*.  Neither crosses the machine's success
hypothesis, and no banked declaration mentions both `balBuild` and `mThreeOf`.
This is the first statement on the route in which the Stage-3 row count and the
builder's own output appear in the same equation.

General in `q, t, m, N, d`.  Reader counterpart: **not claimed** (see the block
docstring).  PROVED. -/
theorem materialisedStageTwoColumns_card {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d)) :
    Fintype.card (Fin (balN q t m)) = N ∧
      Section5Admissibility.mThreeOf N = Fintype.card (Fin (balN q t m)) := by
  obtain ⟨_, hN, _⟩ := balBuild_eq_some_iff.mp hout
  refine ⟨by rw [Fintype.card_fin, hN], ?_⟩
  simp only [Fintype.card_fin, Section5Admissibility.mThreeOf]
  exact hN

/-- **AUX 2 (`06:996` at the machine's own output): the Stage-3 template bin is
counted by the literal builder output.**

`06:996` reads "every Stage-3 template bin is `T_p = {p} x Cols(M_2)`, so
`|T_p| = N_2`".  The route's single reification of that count is
`SchedulePhysicalResidue.templateBin_card`, general in the slot type and the
column carrier; it is **consumed by pin here and not re-proved**.  What is new is
the composite: the column carrier is Part 15's materialised `Cols(M_2)`, so the
bin is counted by the machine's literal output `N`.

General in `q, t, m, N, d`, the slot type and the slot.  Reader counterpart:
**not claimed**.  PROVED. -/
theorem templateBin_card_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d)) {Slot : Type*} (p : Slot) :
    (({p} : Finset Slot) ×ˢ (Finset.univ : Finset (Fin (balN q t m)))).card = N := by
  obtain ⟨_, hN, _⟩ := balBuild_eq_some_iff.mp hout
  rw [SchedulePhysicalResidue.templateBin_card p, Fintype.card_fin]
  exact hN.symm

/-! ### Part 16.B: the three named cardinalities of `06:862`, evaluated -/

/-- **AUX 3 (`06:1000` at the machine's own output): the protected multiplicity
`m_T` is evaluated on the bin the builder's family spans.**

`eq:physical-template-bin-proof` (`06:1000--1002`, `\label` `06:1003`) opens with
`m_T = (u_0 + u_temp)|T_p|`.  The two multiplicities are the banked
`DenseStageFourOpening.uBase` / `.uTemp` of `eq:protected-multiplicities`
(`08:103--104`), and `m_T` itself is the banked
`Section5Admissibility.templateBinCount`; neither is re-reified.  This states
that first equality with `|T_p|` resolved, through AUX 2, to the count of the
builder's own materialised column carrier.

**BLOCK, not bridge.**  The rest of the display -- `= (u_0+u_temp)N_2 >= N_2
>= 9216 s >= 100` -- is deliberately absent; see item 2 of the block docstring.

General in `q, t, m, N, d`, the four raw reservoir counts, the slot type and the
slot.  Reader counterpart: **not claimed**.  PROVED. -/
theorem templateBinCount_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d)) (X₀ T₀ V₀ B₀ : ℕ)
    {Slot : Type*} (p : Slot) :
    Section5Admissibility.templateBinCount X₀ T₀ V₀ B₀ N
      = (DenseStageFourOpening.uBase T₀ V₀ B₀
            + DenseStageFourOpening.uTemp X₀ V₀ B₀)
          * (({p} : Finset Slot) ×ˢ (Finset.univ : Finset (Fin (balN q t m)))).card := by
  rw [templateBin_card_at_balBuild_output hout p]
  rfl

/-- **AUX 4 (`06:170` at the machine's own output): the raw template block
`T_raw = s|C_2|` is `s` times the literal builder output.**

`06:170` reads "`T_raw = s|C_2|`".  `T_raw` is the banked
`Section5Admissibility.TrawOf` and `s` its context's own `sOf` (`eq:s-choice`,
`06:118`); neither is re-reified.  What is new is `|C_2|`: at a successful run
of `A_bal` the Stage-2 family is the builder's, so `|C_2|` is the count of the
materialised column carrier of AUX 1, i.e. the literal output `N`.

General in `q, t, m, N, d` and the schedule context.  Reader counterpart: **not
claimed**.  PROVED. -/
theorem TrawOf_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d))
    (C : Section5Admissibility.ScheduleContext V E) :
    Section5Admissibility.TrawOf C N
      = Section5Admissibility.sOf C * Fintype.card (Fin (balN q t m)) := by
  obtain ⟨_, hN, _⟩ := balBuild_eq_some_iff.mp hout
  rw [Fintype.card_fin, ← hN]
  rfl

/-- **AUX 5 (`eq:lambda-template-exact` at the machine's own output): `lambda_T`
resolved through `06:146--147` and `06:170` to the builder's output.**

`06:151--154` fixes
`lambda_T = (1 - 2^{-20}) T_raw/(T_raw + S_raw) + 2^{-21}`, and `06:170--171`
fixes `T_raw = s|C_2|`, `S_raw = N_src|Rows(R)|`.  This is that display with its
numerator and its first denominator summand resolved all the way down to the
machine's literal output; `S_raw` stays the banked `SrawOf`, which the builder
does not touch.  It is exactly what `06:861--862` means by "only now do we
evaluate `lambda_T`": the value is a function of the constructed family's size,
so it cannot be evaluated before the family is built.

**BLOCK, not bridge.**  The *window* `99/100 <= lambda_T <= 1 - 2^{-21}`
(`eq:lambda-template-window`, `06:172--176`) is deliberately absent; see item 3
of the block docstring.

General in `q, t, m, N, d` and the schedule context.  Reader counterpart: **not
claimed**.  PROVED. -/
theorem lambdaTOf_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d))
    (C : Section5Admissibility.ScheduleContext V E) :
    Section5Admissibility.lambdaTOf C N
      = (1 - 1 / 2 ^ 20)
            * ((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
            / (((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
                + (Section5Admissibility.SrawOf C : ℝ))
          + 1 / 2 ^ 21 := by
  obtain ⟨_, hN, _⟩ := balBuild_eq_some_iff.mp hout
  subst hN
  rfl

/- **Aux 6 was DELETED by the `cc-t8t` `r2` repair.**  The `r1` module offered
`materialisedCardinalities_window`, whose conclusion under the single antecedent
`balBuild q t m = some (N, d)` was

    1 < Section5Admissibility.mThreeOf N  and  Section5Admissibility.mThreeOf N < bBal q t m,

as the statement pole of this part, reading the nondegeneracy floor and the
frozen envelope `14:1811--1813` (strict on `14:1812`) at the machine's own
output.  The gate ruled it a **specialization-level duplicate**: the single
antecedent forces `N = balN q t m` through the banked `balBuild_eq_some_iff`,
`Section5Admissibility.mThreeOf` is the definitional identity
(`Section5Admissibility.lean:2266`), and the conclusion is then *exactly* the
banked pair `⟨one_lt_balN q t m ht, balN_lt_bBal q t m ht⟩` -- a two-line term
that typechecks at the specialized conclusion.  A named wrapper over that pair
has no fresh direction, and the gate further ruled that retaining it as an
anonymous receipt "adds no useful receipt beyond the already-accepted probe".

**The mathematics is unchanged and is not withdrawn.**  The floor and the
envelope remain conjuncts 3 and 4 of the Part-16 deliverable below, which now
discharges them **directly from the three primary owners** `balBuild_eq_some_iff`,
`one_lt_balN` and `balN_lt_bBal`, with no intermediate name.  The upper bound
stays **STRICT** because the frozen display is strict: `14:1812` reads
`0<N=p^t<(2X)^t=B_{\mathrm{bal}}(q,t,m).`, and the route's primary owner is
`balN_lt_bBal` (`:757`), of which `balN_le_bBal` (`:764`) is literally
`(balN_lt_bBal q t m ht).le` -- the derived, weaker spelling, which is therefore
*not* the one consumed (`cc-t8t` r1 Opus finding F-3, vindicated by the `r1`
gate).

**Barred by the `cc-t8t` `r2` repair (permanent; never re-mint under any
spelling).**  The name `materialisedCardinalities_window` is retired.  A window
statement over `m_3` may return only if it acquires content the banked pair does
not already have at this specialization -- and then under a different name. -/

/-! ### Part 16.C: the deliverable -- `06:861--862`'s evaluation point, in one
statement -/

/-- **THE DELIVERABLE OF PART 16** -- "Only now do we evaluate the integer
cardinalities `lambda_T, m_T, a_min`" (`06:861--862`), at a single successful run
of `A_bal`, in the frozen order of the sentence.

The seven conclusions:

* `|Cols(M_2)| = N` (`06:966`) -- the materialised Stage-2 column carrier of Part
  15 is counted by the machine's literal output of `14:1623`;
* `m_3 = |Cols(M_2)|` (`06:979` through `08:262--263`);
* `1 < m_3` and `m_3 < B_bal(q,t,m)` (`14:1811--1813`, strict on `14:1812`) --
  the nondegeneracy pole and the envelope, at the same point;
* `T_raw = s|Cols(M_2)|` (`06:170`);
* `lambda_T` at the resolved display (`eq:lambda-template-exact`, `06:151--154`,
  with `06:146--147` and `06:170`);
* `a_min` at the frozen quotient of `09:382--383` with its `rho_pair = 99/100`
  of `09:380` and with `lambda_T` **substituted by the resolved expression the
  preceding conjunct supplies** -- i.e. the value, not a congruence;
* `m_T = (u_0 + u_temp)|T_p|` (`eq:physical-template-bin-proof`, `06:1000`),
  on the bin `T_p = {p} x Cols(M_2)` of `06:996`.

**Conjuncts 3 and 4 consume the three primary owners directly** (`cc-t8t` r2).
The `r1` proof routed them through a named intermediate,
`materialisedCardinalities_window`, which the gate ruled a specialization-level
duplicate of `balBuild_eq_some_iff`, `one_lt_balN` and `balN_lt_bBal`; that name
is deleted and permanently barred (see the deletion note between AUX 5 and this
section).
**The statement below is unchanged by that repair** -- only its proof is -- and
the envelope stays strict, at the strict frozen display `14:1812` and its primary
owner `balN_lt_bBal` (`:757`).  No replacement wrapper is introduced.

**The `a_min` conjunct is an evaluation, not a congruence** (`cc-t8t` r1, Sol
finding F-2).  Its earlier spelling
`aMinOf C N = aMinOf C (Fintype.card (Fin (balN q t m)))` followed from the
first conjunct by `rw` alone and evaluated nothing; the conjunct below prints
the quotient at the resolved `lambda_T`, so `06:862`'s third named cardinality
genuinely lands.

**Every hypothesis of the paper's data condition is recovered, none assumed.**
The single antecedent about the builder is the machine's own success; `0 < m`,
`1 <= t` and `t <= q` -- `14:1621--1622`'s "positive integers
`q_{2,i} >= t_{2,i} >= 1`" -- come *out* of it through `balBuild_eq_some_iff`.
No gate of `eq:stage2-structural-gates` or `eq:physical-stage4-gates` appears in
hypothesis position, here or anywhere in this part.

**STATEMENT POLE.**  There is no bound variable in the conclusion at all -- it is
a conjunction of equations and two inequalities about the pinned construction, so
there is no witness a trivial inhabitant could supply.  Where a conclusion could
still have been met degenerately -- the six equations, which a one-column family
would also satisfy while emptying `eq:physical-m3-ceiling-proof` -- the third and
fourth conjuncts show it is not: `1 < m_3 < B_bal(q,t,m)`.

**SCOPE.**  Free positive integers, a free schedule context, free raw reservoir
counts and a free slot, exactly as `14:1557--1558`, the banked accessors and
`06:996` are.  It instantiates `q, t, m` at no `(Public, K)` accessor, asserts
nothing about `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`, states none of the four blocked
items above, and discharges **neither** item (b) of `S5-BALANCED-FAMILY` **nor**
any item of `S5-BALANCED-FAMILY-LEVELSTEP-001`.  Part 14.C is the reason and is
unchanged by this part.

General in `q, t, m, N, d`, the schedule context, the four raw reservoir counts,
the slot type and the slot.  Reader counterpart: **not claimed** (see the block
docstring).  PROVED. -/
theorem evaluatedCardinalities_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d))
    (C : Section5Admissibility.ScheduleContext V E) (X₀ T₀ V₀ B₀ : ℕ)
    {Slot : Type*} (p : Slot) :
    Fintype.card (Fin (balN q t m)) = N ∧
      Section5Admissibility.mThreeOf N = Fintype.card (Fin (balN q t m)) ∧
      1 < Section5Admissibility.mThreeOf N ∧
      Section5Admissibility.mThreeOf N < bBal q t m ∧
      Section5Admissibility.TrawOf C N
          = Section5Admissibility.sOf C * Fintype.card (Fin (balN q t m)) ∧
      Section5Admissibility.lambdaTOf C N
          = (1 - 1 / 2 ^ 20)
                * ((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
                / (((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
                    + (Section5Admissibility.SrawOf C : ℝ))
              + 1 / 2 ^ 21 ∧
      Section5Admissibility.aMinOf C N
          = (99 / 100
                + ((1 - 1 / 2 ^ 20)
                        * ((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
                        / (((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
                            + (Section5Admissibility.SrawOf C : ℝ))
                      + 1 / 2 ^ 21) ^ 2 - 1)
              / ((1 - 1 / 2 ^ 20)
                      * ((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
                      / (((Section5Admissibility.sOf C * balN q t m : ℕ) : ℝ)
                          + (Section5Admissibility.SrawOf C : ℝ))
                    + 1 / 2 ^ 21) ^ 2 ∧
      Section5Admissibility.templateBinCount X₀ T₀ V₀ B₀ N
          = (DenseStageFourOpening.uBase T₀ V₀ B₀
                + DenseStageFourOpening.uTemp X₀ V₀ B₀)
              * (({p} : Finset Slot)
                  ×ˢ (Finset.univ : Finset (Fin (balN q t m)))).card := by
  obtain ⟨⟨_, ht, _⟩, hN, _⟩ := balBuild_eq_some_iff.mp hout
  subst hN
  obtain ⟨hcols, hthree⟩ := materialisedStageTwoColumns_card hout
  refine ⟨hcols, hthree, one_lt_balN q t m ht, balN_lt_bBal q t m ht,
    TrawOf_at_balBuild_output hout C, lambdaTOf_at_balBuild_output hout C, ?_,
    templateBinCount_at_balBuild_output hout X₀ T₀ V₀ B₀ p⟩
  simp only [Section5Admissibility.aMinOf, lambdaTOf_at_balBuild_output hout C]

/-! ### Part 16.D: the two receipts

The first is the conditional width-record specialization described in the block
docstring -- **not** an inhabitation receipt, since its record is assumed; the
second reads the builder's delivered accuracy against the schedule's own name
for it.  Both are anonymous `example`s: each is an instantiation of a banked
general theorem at assumed arguments, and this route evidences instantiations by
`example`, never by a new name. -/

-- CONDITIONAL SPECIALIZATION -- deliberately NOT called canonical inhabitation
-- (`cc-t8t` r1, Sol finding 11).  `W : StageTwoWidths` here is **universally
-- quantified and assumed**, so this example exhibits no inhabitant of the
-- paper's scheduled width record and adds nothing to Part 15's inhabitation
-- receipt; the earlier "at the paper's own Stage-2 width record" reading is
-- withdrawn.  What it does show is conditional: *given any* record whose field
-- `four_t₂_le_q₂` is the frozen `4 t_2 <= q_2` of
-- `eq:stage2-balance-ceilings` (`07:280`), the data condition
-- `q_2 >= t_2 >= 1` of `14:1621--1622` is DERIVED from the record rather than
-- assumed separately, and the builder then succeeds at `(q_2, t_2, m)` for
-- every `0 < m`.  Banked owners: `balBuild_eq_some` (`:857`),
-- `StageTwoRelaxed.StageTwoWidths.t₂_pos` and `.t₂_lt_q₂`.
-- This is NOT a discharge of item (b): a width record *carries* the gate as a
-- supposition, while item (b) needs it *concluded* at the schedule's own derived
-- `q2For`/`t2For`, where Part 14.C banks that it fails.
example (W : StageTwoRelaxed.StageTwoWidths) (m : ℕ) (hm : 0 < m) :
    balBuild W.q₂ W.t₂ m
      = some (balN W.q₂ W.t₂ m, balDescriptor W.q₂ W.t₂ m) :=
  balBuild_eq_some hm W.t₂_pos (le_of_lt W.t₂_lt_q₂)

-- `06:859--860`'s "the one indexed `(q_2,t_2,eps_2)`-balanced family `C_2`",
-- read at the schedule's own name for the accuracy: `eps_2 = 1/(100 t_2)` is
-- `eq:epsilon-product`'s first row (`06:852`), reified as
-- `StageTwoRelaxed.epsTwo`, and it is *definitionally* the accuracy the banked
-- `storedFamily_isBalanced` (`:1951`) delivers at `t = t_2`.  This is the
-- hypothesis shape that `OneLevelStepCase`'s own `hbal` binder takes.
-- The `eps_prod < 1/50` half of `eq:epsilon-product` is the banked
-- `Section5Admissibility.epsProd_lt_fiftieth` and is deliberately not restated.
example (W : StageTwoRelaxed.StageTwoWidths) (m : ℕ) (hm : 0 < m) (X₁ : Type*)
    [Fintype X₁] [LinearOrder X₁] (h : Fintype.card X₁ = m) :
    NPCC.IsBalancedFamily W.t₂ (storedFamily W.q₂ W.t₂ m hm X₁ h)
      (StageTwoRelaxed.epsTwo W) :=
  storedFamily_isBalanced W.q₂ W.t₂ m hm W.t₂_pos (le_of_lt W.t₂_lt_q₂) X₁ h

/-! ## Part 17: `06:955--966`'s **balancedness-derived carrier lower bound**, at
the builder's own output -- the head link `N_2 >= m_1^{t_2}`, supplied

**Charter of this part (`cc-t8v` lane 2, `[opus-direct]`, ledger row
`S5-BALANCED-FAMILY-BUILDER-001`).**  Parts 15 and 16 walked the frozen sentence
`06:859--862` from "construct ... then materialise" to "only now do we evaluate
`lambda_T, m_T, a_min`".  Part 16 stated the *leftmost equality* of
`eq:stage3-carrier-lower-bound`, `|Cols(M_2)| = N_2` (`06:966`), and **blocked
the whole inequality chain to its right** on the ground that the paper derives it
"from balancedness *at the level-step arguments*", i.e. from the call
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})` that Part 14.C banks as unavailable on this
route.

**That block is now measured and split, first-hand, at exactly one link.**
Reading `06:955--967` again in the frozen release, the chain has two independent
halves and only the second is level-step-bound:

* the **head link** `N_2 >= m_1^{t_2}` (`06:966`, left of the first `>=`) is
  derived at `06:957--964` from *indexed balancedness alone*: "Since `eps_2<1`
  and `q_2 >= t_2`, fix any `t_2` coordinates.  For every pattern on those
  coordinates, indexed balancedness gives ... `>= (1-eps_2)/m_1^{t_2} > 0`.
  Thus every one of the `m_1^{t_2}` patterns occurs, and hence ..."  Every input
  of that derivation -- the accuracy, the coordinate count, the row count -- is
  delivered by `eq:effective-balanced-builder` at the *builder's own* free
  quantification `14:1557--1558`.  **It needs no schedule fact and no level-step
  instantiation**, and this part lands it;
* the **tail** `>= 2^{t_2} >= q_2^2 >= 144 s^2 >= 9216 s >= 2 s` (`06:967`) rests
  on the four arrangements `06:970--975` supplies (`m_1 = q_1 m_R >= 2`,
  `t_2 >= 2 H_max >= 2 log_2 q_2`, `q_2 >= 12 s|E| >= 12 s`, `64 | s`).  Those
  are schedule facts about `q_2` and `s`, not about the builder, and they stay
  **BLOCK** here; their banked owner is
  `SchedulePhysicalResidue.stageThreeCarrierLowerBound`, which takes the head
  link as a hypothesis and proves the tail from exactly those four facts.

So Part 16's block item 1 is not withdrawn; it is **sharpened**: the head link
was never level-step-bound, and the tail still is.  Part 16's own text stands
unedited, and this part records the split rather than rewriting it.

### The frozen lines, read first-hand this round

Opened in the frozen release named by `routes/parameterized-np/CURRENT_VERSION`
(`versions/2026-08-02-iteration-cexc-repair/source/autoformalization/sections`),
re-opened for this tranche rather than inherited:

* `06:955--956`: "One last carrier estimate must come from balancedness itself,
  rather than from an `n`-cutoff.  Put `m_1 = |Rows(M_1)|`."
* `06:956--958`: "Since `eps_2 < 1` and `q_2 >= t_2`, fix any `t_2` coordinates.
  For every pattern on those coordinates, indexed balancedness gives".
* `06:959--963`, the unnumbered relative-frequency display (`\[` at `06:959`,
  content `06:960--962`, `\]` at `06:963`):
  `#{l : the chosen coordinates of c^{(l)} realize that pattern}/N_2
   >= (1-eps_2)/m_1^{t_2} > 0`.
* `06:964`: "Thus every one of the `m_1^{t_2}` patterns occurs, and hence".
* `06:965--969`, `eq:stage3-carrier-lower-bound` (`\label` at `06:968`), whose
  `06:966` line is `|Cols(M_2)| = N_2 >= m_1^{t_2}` and whose `06:967` line is
  the tail chain.  **Only the head link is taken here.**
* `06:970--975`, the four supplied arrangements -- **not taken here**.
* `06:850--857`, `eq:epsilon-product`, whose first row is `eps_2 = 1/(100 t_2)`;
  this is the accuracy the frozen side condition `eps_2 < 1` is read against.
* `14:1585--1595`, `eq:effective-balanced-builder`, whose fourth clause
  (`14:1591--1592`) is "`c_{d_bal}` is indexed `(q,t,1/(100t))`-balanced" and
  whose first clause (`14:1587`) is `1 <= t <= q`; and `14:1556--1558`, the
  builder's own free quantification over positive integers `q,t,m` with
  `q >= t >= 1`.
* `14:1623`, "the literal output `(N_{2,i}, d_i)`", and `14:1626`'s canonical
  increasing equivalence at a general carrier -- unchanged from Parts 14--16.

### The gap this part actually closes -- a measured supply gap

`SchedulePhysicalResidue` owns the counting half as three general theorems, and
**before this part the premise that drives all three had no supplier anywhere in
the tree.**  Re-measured this round over `src/**/*.lean` on the bytes as they
stand at this tranche's baseline: `carrierCard_ge_patternCount`,
`all_patterns_occur` and `patternDensity_pos` occur outside their own module in
**prose only** (`EffectiveCutoffCertificate.lean:568`, `:571`; the enum
constructor `ItemVDisplay.stageThreeCarrierLowerBound` there is a classifier tag,
not the theorem), and are **applied by no declaration on the route**.

**Correction, measured on these bytes (`cc-t8v` `r0` finding F-3).**  An earlier
draft of this paragraph claimed that `NPCC.IsBalancedFamily` occurs in the
statement of no declaration outside this module.  **That claim is false and is
withdrawn.**  The comment-stripped sweep over `src/**/*.lean` finds it in the
statements of six other modules -- `AmbientWidthReadout` (`:1161`, `:1217`,
`:1288`), `OneLevelStepCase` (`:1127`), `StageTwoRelaxed` (`:1639`, `:2002`,
`:2454`), `TerminalCallBundleSupply` (`:507`, `:620`), `TerminalLocalizedCall`
(`:564`, `:614`, `:669`, `:1148`) and `TerminalTwoStream` (`:1796--1797`,
`:1817`, `:1868`, `:1907`, `:2011--2012`, `:2945`, `:2953`, `:3312--3313`).
**This creates no declaration duplication and does not weaken the supply gap.**
Every one of those occurrences is either the predicate in *hypothesis* position
(an assumed balanced family fed to a readout, a localized call or a Stage-2
relaxation) or a closure/probe lemma about the predicate itself (restriction
along a reindexing, accuracy monotonicity, the bijective and constant-family
poles).  **None of them concludes a density inequality, and none of them derives
anything from the predicate in the direction `06:960--962` uses**; the gap
below is stated over that direction, not over the predicate's mere occurrence.
Their `hdens` premise --

    r <= (#{c : pat c = p} : R) / (Fintype.card Cols : R)   for every pattern p

-- is `06:960--962` itself, and no banked declaration derives it from
`NPCC.IsBalancedFamily`.  That is the wirable endpoint, and Part 17.A supplies
it: `balanced_pattern_density` produces exactly that inequality from the frozen
predicate, and the two consequences below are then *applications of the banked
owners*, not second proofs of them.

### ALREADY-OWNED, consumed by pin and never restated

* `SchedulePhysicalResidue.patternDensity_pos` (`:1198`, `06:962`) -- the strict
  positivity of the frozen frequency; consumed, never re-derived.
* `SchedulePhysicalResidue.all_patterns_occur` (`:1209`, `06:959--964`) --
  "every one of the `m_1^{t_2}` patterns occurs"; consumed by
  `balanced_realizes_every_pattern`, whose body is one application of it.
* `SchedulePhysicalResidue.carrierCard_ge_patternCount` (`:1230`, `06:966`) --
  the head link at a free pattern map; consumed by `balanced_card_pow_le`, whose
  body is one application of it after the equivalence transport.
* `SchedulePhysicalResidue.stageThreeCarrierLowerBound` (`:1269`, `06:970--975`)
  and `.stageThreeCarrierLowerBound_at_scheduledScale` (`:1304`) -- the tail,
  **not restated and not instantiated here**; composing them with the head link
  is deliberately left to a future commissioned tranche, so that no free `s` or
  `q_2` can enter this part in any position.
* `NPCC.IsBalancedFamily` (`vendor/npc-cc/NPCC/Relaxed.lean:19`) -- the balanced
  family predicate.  **No second predicate, and `IsBalancedFamily.projection` is
  not used**: the frozen argument fixes coordinates by an injection into the
  ambient width, which is what the `e : Fin t -> Fin q` binder below is.
* Parts 2, 6, 7, 8 and 14 of this module: `balN` (`:741`), `balFamily` (`:964`),
  `balFamily_isBalanced` (`:1831`), `balBuild_eq_some_iff` (`:4028`),
  `balBuild_eq_some` (`:857`).  **None of the ten names barred at `cc-t8c` is
  revived under any spelling, and `materialisedCardinalities_window`, retired at
  `cc-t8t` `r2`, is not re-minted under this or any other name** -- nothing below
  is a window statement over `m_3`.
* This part adds **no `def`, no `structure`, no `abbrev`, no instance and no
  import**, and it introduces **zero axioms**.  It reaches **no** expander
  interface: `EXPANDER-001` has no Lean declaration by design and stays an
  undecided ask, `NPCC.aghp_balanced_family_exists` is deliberately not adopted,
  and `LegacyNPCC.Stage12` is absent from this module's import closure.

### Import direction (verified this round, not asserted)

The one cross-module family pinned below is reached without adding an import
line; each hop names importer, importee and the import line's `file:line`:

* `SchedulePhysicalResidue.*`: `BalancedFamilyBuilder.lean:3` imports
  `LevelStepConstruction`; `LevelStepConstruction.lean:1` imports
  `MechanicalCompilerResidue`; `MechanicalCompilerResidue.lean:3` imports
  `SchedulePhysicalResidue`.  The direction is consumer-downstream throughout.

`LevelStepMaterialisation` and `EffectiveCutoffCertificate` remain **absent**
from this module's import closure, so nothing of theirs is pinned.

### BLOCK, not bridge -- the gaps registered rather than crossed

1. **The tail of `eq:stage3-carrier-lower-bound` (`06:967`)** --
   `>= 2^{t_2} >= q_2^2 >= 144 s^2 >= 9216 s >= 2 s` -- is NOT stated at this
   frame.  It needs `06:970--975`'s four arrangements, which are facts about the
   schedule's `q_2` and its **source-defined** scale `s` (`eq:s-choice`,
   `06:118`, reified as `ParameterSchedule.sScale`).  Restating it here would
   have to reintroduce a free `s` and a free `q_2` in a paper-facing statement,
   which is the recorded DEFINED-versus-FREE defect that
   `docs/atlas/SchedulePhysicalResidue.md` bars.  BLOCK.
2. **`eq:physical-stage4-gates` (`06:863--873`) and
   `eq:physical-m3-ceiling-proof` (`06:981--989`)** are NOT stated.  Their owners
   are `Section5Admissibility.PhysicalStage4Gates` and
   `SchedulePhysicalResidue.physicalM3Ceiling`(`Gate`), whose own hypothesis is
   `9216 * s <= m_3`, i.e. item 1.  BLOCK, exactly as Part 16 recorded.
3. **The level-step instantiation `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`** stays
   unavailable: `balBuild_eq_none_at_publicInputYes` banks, in the kernel, that
   at the campaign's own witness pair the builder returns the reserved failure
   output, because `06:830--831` requires `4 t_2 <= q_2` (`06:835`) verified
   first and no theorem here concludes it at any `(P, K)`.  Consequently this
   part discharges **neither** item (b) of `S5-BALANCED-FAMILY` **nor** any item
   of `S5-BALANCED-FAMILY-LEVELSTEP-001`; both stay OPEN and the canonical
   inhabitation of the level-step call stays canonical-DEFERRED behind the cutoff
   machinery of `06:1169--1226` and `PARAM-001`.  Registration is not discharge.
4. **`MATERIALIZE-001`'s machine layer** (`A_realize`, `A_entry`,
   `A_materialize`, the codecs and padding maps of `14:1600--1620`) stays
   bucket-(c) DEFERRED.  This part is the mathematical statement layer only.
5. **Record item `R-17` is NOT touched here.**  This part is append-only over
   Parts 1--16; the Part-15 docstring, the atlas card and
   `docs/BANKED_SURFACE_INDEX.md` keep their current bytes, and the R-17 repair
   sequence stays OPEN as a record-surface rider outside this delta.

### Statement-numeral screen (this part's own occurrences)

Every numeric literal in a statement below is one of: the CANONICAL-FORM
`1 - eps_2` numerator and the `eps_2 < 1` side condition of `06:957--962`; the
CANONICAL-FORM accuracy `1/(100 t)` of `14:1591--1592`, which is
`eq:epsilon-product`'s `eps_2 = 1/(100 t_2)` (`06:852`) at the builder's own
free `t`; the CANONICAL-FORM floor `1 <= t` of `14:1587`; or a **BEYOND-PAPER
AUDIT** literal inside `balanced_card_pow_le_needs_accuracy`, the rejection
probe, whose own docstring carries that label and which claims no legality at its
values.  No numeral is assigned to a source-defined quantity anywhere in this
part.  The occurrence-by-occurrence table, one row per literal with its exact
`file:line`, is produced by this tranche's own authoring lane report.

### Binder provenance

* `q, t, m` -- GENUINELY-FREE at `14:1557--1558`; the standing ruling of
  `S5-BALANCED-FAMILY-BUILDER-001`, unchanged.
* `N, d` -- **not free in substance**: the machine's output, pinned by the single
  antecedent `balBuild q t m = some (N, d)` through `balBuild_eq_some_iff`,
  exactly as `14:1623` supplies them.
* `Y, L, S, eps` (Part 17.A) -- GENUINELY-FREE: `06:957--964` argues from the
  *predicate* `def:balanced-columns` and from nothing else, so the general layer
  quantifies over the same data `NPCC.IsBalancedFamily` does; the accuracy is a
  binder there for the same reason the vendored predicate takes it as one.
* `e : Fin t -> Fin q` with `he : Function.Injective e` -- GENUINELY-FREE at
  `06:957`, "fix **any** `t_2` coordinates"; the injection is what "any `t_2`
  coordinates" means, and no particular choice is made.
* `y0 : Y` (Part 17.A, AUX 1) -- GENUINELY-FREE: it is the default value used to
  extend a pattern on the chosen coordinates to the total function the frozen
  predicate quantifies over ("patterns are quantified as total functions read
  only on `J`", `NPCC/Relaxed.lean:16--17`).  It never reaches the conclusion.
* `p : Fin t -> Y`, `P : Fin t -> Fin m` -- GENUINELY-FREE at `06:958`, "for
  every pattern on those coordinates".

**Zero source-defined quantity enters as a free binder.**  In particular `s`,
`q_2`, `t_2`, `m_1`, `N_2` and `m_3` appear **nowhere as binders in this part**:
the accuracy is the builder's own `1/(100 t)` display rather than a free real,
and the row count in the exponent is the builder's own argument `m`.  The
occurrence-by-occurrence binder table with `file:line` rows is produced by this
tranche's own authoring lane report.

### Canonical inhabitation

The antecedent's canonical inhabitant is again the paper's own object -- the
machine's success at every triple `14:1557--1558` admits -- and it is receipted
in Part 15 by `balBuild_eq_some`, consumed here and **not re-authored**; this
part adds no sharper inhabitation receipt, exactly as `cc-t8t` `r1` ruled for
Part 16.  For the *general* layer of Part 17.A the canonical inhabitant is the
builder's own family: `balFamily_isBalanced` is an instance of
`NPCC.IsBalancedFamily` at the paper's own accuracy and is fed to the general
lemmas below through `balN_pow_le`, so the general statements are not vacuous
shells.  For the *level-step* layer there is still no canonical inhabitant on
this route, which is why nothing below is stated at `q2For` / `t2For`.

Reader counterpart: **not claimed**, checked at both polarities this round in the
pinned release copy (`versions/2026-08-02-iteration-cexc-repair/source/`
`reader-facing`).  The nearest positive sentence is
`03-parameterized-construction.tex:477--480`: "Write `N_2=|L_2|` and
`m_1=|Rows(M_1)|`.  Since `eps_2<1`, balancedness on any `t_2` coordinates makes
every one of the `m_1^{t_2}` patterns occur, so `N_2 >= m_1^{t_2}`."  That states
the same fact, but it is **unlabelled prose inside the proof of the reader's
`eq:paper-M3-gates`**, not a numbered item -- and this route never cites prose as
a statement (the ruling Parts 13--16 record).  Two further divergences make the
assignment wrong even as a courtesy: the reader's chain continues
`N_2 >= 2^{t_2} >= q_2^2 >= 2s` (`:485`), three links shorter than `06:967`, and
it is read at the depth `b_2` rather than the physical `b_T`.  The negative
polarity was checked at `04-bridge.tex:152--182`, the reader's
`cor:one-level-amplifier`: it carries the one-level budgets and the exact carrier
equations and says nothing about balancedness or about a carrier lower bound, so
it is not a counterpart either.  The reader's single balanced-family item
`lem:paper-explicit-balanced-family` remains assigned to Part 8's
`balFamily_isBalanced`, and this route assigns one reader item to one
declaration. -/

/-! ### Part 17.A: the general supply layer -- `06:957--964` from the predicate
alone -/

/-- **AUX 1 (`06:960--962`): indexed balancedness gives every pattern on any
chosen `t` coordinates the frozen relative frequency `(1-eps)/|Y|^t`.**

This is the frozen display of `06:959--963` verbatim, at the predicate
`NPCC.IsBalancedFamily` and nothing else: `06:957` says "fix **any** `t_2`
coordinates", which is the injection `e` with `he`; `06:958` says "for every
pattern on those coordinates", which is `p`; and the conclusion is the frozen
left-hand side over the frozen right-hand side.

**This is the supply gap.**  The route's three banked counting theorems
(`SchedulePhysicalResidue.patternDensity_pos`, `.all_patterns_occur`,
`.carrierCard_ge_patternCount`) all consume a density premise of exactly this
shape, and on the bytes as they stand at this tranche's baseline -- measured over
`src/**/*.lean` -- no declaration anywhere derives it from
`NPCC.IsBalancedFamily`, and the two consequence theorems are applied nowhere on
the route.  Nothing is re-proved here: the vendored predicate's own two-sided
bound is read once, in the direction `06:962` uses.

The default value `y0` only extends the pattern on the chosen coordinates to the
total function the vendored predicate quantifies over; it does not occur in the
conclusion.

General in the value carrier, the family, the width, the index count, the
coordinate count, the accuracy, the injection and the pattern.  Reader
counterpart: **not claimed** (see the block docstring).  PROVED. -/
theorem balanced_pattern_density {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hbal : NPCC.IsBalancedFamily t S ε)
    (e : Fin t → Fin q) (he : Function.Injective e) (y₀ : Y) (p : Fin t → Y) :
    (1 - ε) / (Fintype.card Y : ℝ) ^ t
      ≤ ((Finset.univ.filter (fun j : Fin L => (fun i => S j (e i)) = p)).card : ℝ)
          / (L : ℝ) := by
  classical
  have hJcard : (Finset.image e Finset.univ).card = t := by
    rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin]
  have hae : ∀ i : Fin t, Function.extend e p (fun _ => y₀) (e i) = p i := fun i =>
    he.extend_apply p (fun _ => y₀) i
  have hb := hbal.2 (Finset.image e Finset.univ) (le_of_eq hJcard)
      (Function.extend e p (fun _ => y₀))
  rw [hJcard] at hb
  have hsets :
      (Finset.univ.filter (fun j : Fin L =>
          ∀ γ ∈ Finset.image e Finset.univ, S j γ = Function.extend e p (fun _ => y₀) γ))
        = (Finset.univ.filter (fun j : Fin L => (fun i => S j (e i)) = p)) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · intro h
      funext i
      have hmem : e i ∈ Finset.image e Finset.univ :=
        Finset.mem_image_of_mem _ (Finset.mem_univ i)
      rw [h _ hmem, hae i]
    · intro h γ hγ
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hγ
      rw [hae i, ← h]
  rw [hsets] at hb
  have h1 := (abs_le.mp hb).1
  rw [sub_div]
  linarith

/-- **AUX 2 (`06:964`): "Thus every one of the `m_1^{t_2}` patterns occurs."**

At accuracy below `1` -- the frozen side condition `eps_2 < 1` of `06:957` --
every pattern on the chosen coordinates is realized by some index of the family.
The body is **one application of the banked
`SchedulePhysicalResidue.all_patterns_occur`** to the density AUX 1 now supplies;
that theorem is consumed by pin and not re-proved.

**The coordinates are ANY `t` of the `q`, not the first `t`** (`cc-t8v` `r0`
finding F-5).  `06:957` says "fix **any** `t_2` coordinates", and the reader says
the same at `03-parameterized-construction.tex:477--480` ("balancedness on any
`t_2` coordinates"); an earlier draft hardcoded `Fin.castLE htq`, i.e. the first
`t` coordinates, which silently dropped that source binder.  The choice is now
the arbitrary injection `e` with `he : Function.Injective e` -- exactly the
binder AUX 1 already carries -- and no particular choice is made anywhere.

The degenerate branch `t = 0` is discharged from the predicate's own carried fact
`0 < L`, not from a chosen value; the empty-pattern statement is then vacuous in
the frozen sense (there are no coordinates to read).

General in the value carrier, the family, both widths, the accuracy, the
injection and the pattern.  Reader counterpart: **not claimed**.  PROVED. -/
theorem balanced_realizes_every_pattern {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hbal : NPCC.IsBalancedFamily t S ε) (hε : ε < 1)
    (e : Fin t → Fin q) (he : Function.Injective e)
    (p : Fin t → Y) :
    ∃ j : Fin L, ∀ i : Fin t, S j (e i) = p i := by
  classical
  rcases Nat.eq_zero_or_pos t with ht0 | ht
  · subst ht0
    exact ⟨⟨0, hbal.1⟩, fun i => i.elim0⟩
  · have hy : Y := p ⟨0, ht⟩
    have hcY : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr ⟨hy⟩
    have hr : 0 < (1 - ε) / ((Fintype.card Y : ℝ) ^ t) :=
      SchedulePhysicalResidue.patternDensity_pos hε hcY
    have hdens : ∀ P : Fin t → Y,
        (1 - ε) / (Fintype.card Y : ℝ) ^ t
          ≤ ((Finset.univ.filter
                (fun j : Fin L => (fun i => S j (e i)) = P)).card : ℝ)
              / (Fintype.card (Fin L) : ℝ) := by
      intro P
      have := balanced_pattern_density hbal e he hy P
      simpa using this
    have hsurj : Function.Surjective (fun (j : Fin L) (i : Fin t) => S j (e i)) :=
      SchedulePhysicalResidue.all_patterns_occur _ hr hdens
    obtain ⟨j, hj⟩ := hsurj p
    exact ⟨j, fun i => congrFun hj i⟩

/-- **AUX 3 (`06:966`, the head link `N_2 >= m_1^{t_2}`) at a general balanced
family.**

"and hence `|Cols(M_2)| = N_2 >= m_1^{t_2}`": the index count of an indexed
`(q,t,eps)`-balanced family with `eps < 1` and `t <= q` is at least `|Y|^t`.
The body is **one application of the banked
`SchedulePhysicalResidue.carrierCard_ge_patternCount`** to the density AUX 1
supplies, after transporting the value carrier along `Fintype.equivFin` so that
the banked theorem's frozen pattern type `Fin t -> Fin m_1` is met exactly; the
banked theorem is consumed by pin and its counting argument is not rebuilt.

**Why the empty branch is not a hole.**  If `Y` is empty the frozen argument has
nothing to say, and the statement is discharged from the predicate's own carried
`0 < L`: the coordinate count must then be `0` (otherwise the family itself would
inhabit `Y`), and `|Y|^0 = 1 <= L`.  No value is chosen.

**This is the head link only.**  The tail `06:967` is BLOCK; see item 1 of the
block docstring.

General in the value carrier, the family, both widths and the accuracy.  Reader
counterpart: **not claimed**.  PROVED. -/
theorem balanced_card_pow_le {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hbal : NPCC.IsBalancedFamily t S ε) (hε : ε < 1) (htq : t ≤ q) :
    Fintype.card Y ^ t ≤ L := by
  classical
  have he : Function.Injective (Fin.castLE htq) := by
    intro i₁ i₂ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  rcases isEmpty_or_nonempty Y with hY | hY
  · rcases Nat.eq_zero_or_pos t with ht0 | ht
    · subst ht0; simpa using hbal.1
    · exact (hY.false (S ⟨0, hbal.1⟩ ⟨0, lt_of_lt_of_le ht htq⟩)).elim
  · obtain ⟨y₀⟩ := hY
    have hcY : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr ⟨y₀⟩
    have hr : 0 < (1 - ε) / ((Fintype.card Y : ℝ) ^ t) :=
      SchedulePhysicalResidue.patternDensity_pos hε hcY
    have hdens : ∀ P : Fin t → Fin (Fintype.card Y),
        (1 - ε) / (Fintype.card Y : ℝ) ^ t
          ≤ ((Finset.univ.filter
                (fun j : Fin L =>
                  (fun i => (Fintype.equivFin Y) (S j (Fin.castLE htq i))) = P)).card : ℝ)
              / (Fintype.card (Fin L) : ℝ) := by
      intro P
      have hbase := balanced_pattern_density hbal (Fin.castLE htq) he y₀
        (fun i => (Fintype.equivFin Y).symm (P i))
      have hsets :
          (Finset.univ.filter (fun j : Fin L =>
              (fun i => S j (Fin.castLE htq i)) = fun i => (Fintype.equivFin Y).symm (P i)))
            = (Finset.univ.filter (fun j : Fin L =>
                (fun i => (Fintype.equivFin Y) (S j (Fin.castLE htq i))) = P)) := by
        apply Finset.filter_congr
        intro j _
        constructor
        · intro h
          funext i
          rw [congrFun h i, Equiv.apply_symm_apply]
        · intro h
          funext i
          rw [← congrFun h i, Equiv.symm_apply_apply]
      rw [hsets] at hbase
      simpa using hbase
    have hmain := SchedulePhysicalResidue.carrierCard_ge_patternCount
      (Cols := Fin L) (Fintype.card Y) t
      (fun j i => (Fintype.equivFin Y) (S j (Fin.castLE htq i))) hr hdens
    simpa using hmain

/-! ### Part 17.B: the frozen accuracy meets the frozen side condition, and the
head link at the builder's own family -/

/-- **AUX 4: the builder's delivered accuracy satisfies `06:957`'s side
condition.**

`eq:effective-balanced-builder` delivers accuracy `1/(100t)` (`14:1591--1592`) --
the builder's own free-`t` printing of `eq:epsilon-product`'s
`eps_2 = 1/(100 t_2)` (`06:852`) -- and the carrier estimate of `06:955--966`
opens by requiring `eps_2 < 1` (`06:957`).  Those two displays live in different
sections and nothing on the route connects them; this is that connection, at the
builder's own frozen floor `1 <= t` (`14:1587`).  It is a **cross-section bridge,
not a wrapper**: no banked declaration states any bound on `1/(100t)` at a free
`t` (`SchedulePhysicalResidue.epsTwo_le_hundredth` states `eps_2 <= 1/100` at the
*derived* Stage-2 accessor, a different quantity at a different frame).

General in the coordinate count.  Reader counterpart: **not claimed**.
PROVED. -/
theorem balAccuracy_lt_one (t : ℕ) (ht : 1 ≤ t) : 1 / (100 * (t : ℝ)) < 1 := by
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  rw [div_lt_one (by linarith)]
  linarith

/-- **AUX 5 (`06:966`'s head link at the builder's own family): `m^t <= N`.**

The builder's family is indexed `(q,t,1/(100t))`-balanced (`14:1591--1592`,
banked as `balFamily_isBalanced`) and its accuracy clears `06:957` by AUX 4, so
AUX 3 applies at the builder's own free quantification: the family size the
machine returns is at least `m^t`.  This is `06:966` read at `m_1 = m`,
`t_2 = t`, `N_2 = N`, i.e. at exactly the arguments
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})` would be called with -- **without** making
that call, which stays unavailable (item 3 of the block docstring).

This is also where the general layer of Part 17.A receives its canonical
inhabitant: `balFamily_isBalanced` is the paper's own instance of
`NPCC.IsBalancedFamily`, so AUX 3 is applied at the paper's object and not only
at a synthetic one.

General in `q, t, m`.  Reader counterpart: **not claimed**.  PROVED. -/
theorem balN_pow_le (q t m : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (htq : t ≤ q) :
    m ^ t ≤ balN q t m := by
  have h := balanced_card_pow_le (balFamily_isBalanced q t m hm ht htq)
    (balAccuracy_lt_one t ht) htq
  simpa using h

/-- **AUX 6 (STATEMENT POLE for AUX 3) -- BEYOND-PAPER AUDIT, a rejection probe:
`06:957`'s side condition `eps_2 < 1` is not decoration.**

AUX 3 would be an over-strong reading of `06:964--966` if the frozen side
condition could be dropped, and a green build cannot see that.  This probe
settles it in the kernel: at accuracy exactly `1` the vendored predicate still
holds for a single-index constant family over a two-element value carrier, while
the conclusion `|Y|^t <= L` fails there.  So the hypothesis is load-bearing and
AUX 3 is not a strengthening of the paper.

**BEYOND-PAPER AUDIT.**  The values are chosen by this lane, not read from the
frozen source, and the probe therefore **claims no legality**: it audits our
encoding at a point the paper never visits and is strictly weaker evidence than
any statement at the paper's own application point.  It is not an inhabitation
receipt, it discharges nothing, and it is cited only as the pole of AUX 3.

PROVED. -/
theorem balanced_card_pow_le_needs_accuracy :
    NPCC.IsBalancedFamily 1 (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 2)) 1
      ∧ ¬ (Fintype.card (Fin 2) ^ 1 ≤ 1) := by
  refine ⟨⟨Nat.one_pos, ?_⟩, by simp⟩
  intro J hJ a
  have hJcases : ∀ K : Finset (Fin 1), K = (∅ : Finset (Fin 1)) ∨ K = ({0} : Finset (Fin 1)) := by
    decide
  rcases hJcases J with rfl | rfl
  · simp
  · by_cases h : a 0 = 0
    · rw [Finset.filter_true_of_mem (by
        intro j _ γ hγ
        obtain rfl := Finset.mem_singleton.mp hγ
        exact h.symm)]
      have hgoal : |(1 : ℝ) - 2⁻¹| ≤ 2⁻¹ := abs_le.mpr ⟨by norm_num, by norm_num⟩
      simpa using hgoal
    · rw [Finset.filter_false_of_mem (by
        intro j _ hcon
        exact h (hcon 0 (by simp)).symm)]
      simp

/-! ### Part 17.C: the deliverable -- `06:955--966`'s head link at a single
successful run of `A_bal` -/

/-- **THE DELIVERABLE OF PART 17** -- the balancedness-derived carrier lower
bound of `06:955--966`, at a single successful run of `A_bal`, in the frozen
order of the passage.

The two conclusions:

* `m^t <= N` (`06:966`, left of the first `>=`, derived through `06:957--964`) --
  the machine's literal output of `14:1623` is at least the number of patterns on
  any `t` of its `q` coordinates;
* every one of the `m^t` patterns occurs (`06:964`) -- for **any** injection `e`
  of `t` coordinates into the `q` available ones, and each pattern on those
  coordinates, there is an index of the builder's own family realizing it.

**The realization conjunct quantifies the coordinates, it does not choose them**
(`cc-t8v` `r0` finding F-5).  `06:957` fixes "**any** `t_2` coordinates" and the
reader repeats that at `03-parameterized-construction.tex:477--480`
("balancedness on any `t_2` coordinates"); the `cc-t8u` draft read the *first*
`t` coordinates via `Fin.castLE htq`, which dropped that source binder and made
the conjunct weaker than the passage it cites.  The injection `e` and its
`Function.Injective` witness are therefore bound inside the conjunct, where the
paper binds them, and the first conjunct -- which mentions no coordinates -- is
left untouched.

**Exactly one canonical inequality is carried.**  The `cc-t8u` draft of this
statement also spelled the same bound at `Fintype.card (Fin (balN q t m))` and at
`Section5Admissibility.mThreeOf N`; under `hout` those are the identical
inequality through `N = balN q t m`, `Fintype.card_fin` and the identity
accessor, and both repetitions are **deliberately deleted** here per the `cc-t8u`
judge's verdict 15.  Downstream consumers that need the bound at the materialised
Stage-2 column carrier or at `m_3` obtain it by rewriting with Part 16's own
`materialisedStageTwoColumns_card`, which is that identification's banked owner.

**Every hypothesis of the paper's data condition is recovered, none assumed.**
The single antecedent is the machine's own success.  The proof recovers `0 < m`,
`1 <= t`, and `t <= q` (`14:1621--1622`) from `balBuild_eq_some_iff`.  The
conclusion exports `0 < m` and `t <= q`; `1 <= t` is consumed internally by
`balN_pow_le`, `balFamily_isBalanced`, and `balAccuracy_lt_one`.  The exported
`t <= q` is spelled `_htq` because after the F-5 generalization the realization
conjunct fixes its coordinates by an arbitrary injection rather than by
`Fin.castLE`, so nothing downstream mentions it; the underscore records that it
is deliberately unconsumed, **not** dropped -- `∃ (_htq : t <= q), Q` still
asserts `t <= q`, and it is exported so a consumer can read the width comparison
off this statement alone.  No gate
of
`eq:stage2-structural-gates` or `eq:physical-stage4-gates` appears in hypothesis
position, here or anywhere in this part.

**STATEMENT POLE.**  The second conjunct is a genuine existential and the trivial
witness fails it: a witness that ignored the pattern -- one index `l` serving
every `p` -- would force all `m^t` patterns to agree along `e`, which is refuted
as soon as two patterns differ, i.e. at every `1 < m` with `0 < t` and every
injection `e`.  That conjunct is also what separates this statement from
anything a *constant* stored family satisfies:
`PublicRecords.levelParams_admits_unbalanced_family` banks that a constant family
is a legal `Pi`, and a constant family realizes exactly one pattern, so it fails
the conjunct at the same inputs while satisfying no bound of the first conjunct
beyond `1 <= N`.  The first conjunct is an inequality about the pinned
construction with no bound variable at all, so no trivial inhabitant arises
there.

**SCOPE.**  Free positive integers, exactly as `14:1557--1558` is.  It
instantiates `q, t, m` at no `(Public, K)` accessor, asserts nothing about
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})`, states none of the five blocked items above,
and discharges **neither** item (b) of `S5-BALANCED-FAMILY` **nor** any item of
`S5-BALANCED-FAMILY-LEVELSTEP-001`.

General in `q, t, m, N, d` and in the coordinate injection.  Reader counterpart:
**not claimed** (see the block docstring).  PROVED. -/
theorem carrierLowerBound_at_balBuild_output {q t m N : ℕ} {d : BalDescriptor}
    (hout : balBuild q t m = some (N, d)) :
    ∃ (hm : 0 < m) (_htq : t ≤ q),
      m ^ t ≤ N ∧
      ∀ (e : Fin t → Fin q), Function.Injective e →
        ∀ p : Fin t → Fin m, ∃ l : Fin (balN q t m),
          ∀ i : Fin t, balFamily q t m hm l (e i) = p i := by
  obtain ⟨⟨hm, ht, htq⟩, hN, _⟩ := balBuild_eq_some_iff.mp hout
  subst hN
  refine ⟨hm, htq, balN_pow_le q t m hm ht htq, ?_⟩
  intro e he p
  exact balanced_realizes_every_pattern (balFamily_isBalanced q t m hm ht htq)
    (balAccuracy_lt_one t ht) e he p

/-! ## Part 18: the four **arrangement supplies** of `06:970--975` at the level
schedule's own `s`, `q_2`, `t_2` and `m_1` -- the inputs the banked carrier tail
of `eq:stage3-carrier-lower-bound` (`06:967`) requires

**Charter of this part (`cc-t8w` lane 1, restored at `cc-t8w` r1 under the gate's
per-declaration verdict map, `[opus-direct]`, ledger row
`S5-BALANCED-FAMILY-BUILDER-001`).**  Part 17 landed the **head link**
`N_2 >= m_1^{t_2}` of `06:966` and recorded, as its block item 1, that the
**tail** `>= 2^{t_2} >= q_2^2 >= 144 s^2 >= 9216 s >= 2 s` of `06:967` stayed
unbridged, because bridging it needs the four arrangements `06:970--975`
supplies and those are facts about the schedule's `q_2` and its source-defined
scale `s`.

**This part lands the arrangement supplies, and NOT the bridge.**  The
composition theorem that would apply the banked tail
`SchedulePhysicalResidue.stageThreeCarrierLowerBound` at a successful run of
`A_bal` was authored at `cc-t8w` r0 and **ruled a fidelity defect at the gate**:
it carried the builder's coordinate width `q` as a free binder, whereas the
paper's own application point is `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`
(`14:1621--1625`), i.e. at `q = q_2`.  The gate's ruling is that a theorem
deliberately moved away from that identification cannot be credited as the
paper's carrier chain.  **No such theorem is present below**, in any form, and
the composition is registered as an **OPEN fidelity arc** (see BLOCK/OPEN item 1),
not as a discharged obligation.  What is below is exactly the four arrangement
supplies and their two audit poles, each of which the gate ruled CLEAR on its own
statement.

**Nothing here is a second proof of anything banked.**  Part 18 adds no `def`,
no `structure`, no `abbrev`, no instance, no import and no axiom; it is a pure
append over Parts 1--17, and every one of Parts 1--17's bytes is untouched.

### The frozen lines, read first-hand this round

Opened in the frozen release named by `routes/parameterized-np/CURRENT_VERSION`
(`versions/2026-08-02-iteration-cexc-repair/source/autoformalization/sections`).
Two line ranges carried an **off-by-one** at `cc-t8w` r0 and are corrected here
against the frozen bytes: the `m_1 >= 2` sentence begins at `06:970` (`06:969` is
`\end{equation}`), and the `eq:t2-search`/`eq:Hmax` sentence begins at `06:972`
(`06:971` closes the preceding sentence).  Every other range below was re-read
this round and stands.

* `06:965--969`, `eq:stage3-carrier-lower-bound` (`\label` at `06:968`):
  `|Cols(M_2)| = N_2 >= m_1^{t_2} >= 2^{t_2} >= q_2^2 >= 144 s^2 >= 9216 s >= 2 s`.
  `06:966` is the head link (Part 17); `06:967` is the tail this part supplies
  inputs for.
* `06:970--971`: "Here `m_1 = q_1 m_R >= 2` follows from the incoming carrier
  envelope and the Stage-1 constructor equation".
* `06:972--973`: "`eq:t2-search` and `eq:Hmax` give `t_2 >= 2 H_max >=
  2 log_2 q_2`".
* `06:973--974`: "and the guarded source gives `q_2 >= 12 s |E| >= 12 s`".
* `06:974--975`: "The penultimate comparison uses `64 | s`, hence `s >= 64`."
* `06:122--125`, the defining display of the width: "Thus `s` is a public power
  of two.  The source theorem then fixes `q_2 = the least power of two at least
  `12 s N_E`."  (`04-guarded-source.tex:386--391`,
  `def:guarded-source-constructor`, is the same display at its own home; the
  Lean owner `GuardedSourceSlab.q2` cites it.)
* `06:110--120`, `eq:s-choice`: `A_pre`, `u = clog_2(clog_2(A_pre+16))`,
  `s = 2^{ceil(B_s u^2)}`.
* `07:143--145`, `eq:stage1-universes-and-value`: `Rows(M_1) = [q_1] x Rows(R)`
  -- the Stage-1 constructor equation `06:969` names.
* `06:315`, `eq:stage1-scales`: `q_1 = 2^a - 2`.
* `05:36--37`: `m_R, n_R in N_{>0}`.

### THE TWO GENUINE LOOKUPS, RESOLVED (not registered)

The tranche charter names two facts of `06:969--974` whose supply had to be
found in the frozen source rather than assumed.  **Both resolve**, from the
*defining* displays and not from the consuming sentences (`USE-AS-DEFINITION`
is barred: `06:974`'s "`q_2 >= 12 s |E|`" is a *use*, and the definition is
`06:124` / `04:389--391`):

1. **`12 s <= q_2` -- RESOLVED.**  `06:124` *defines* `q_2` as the least power
   of two at least `12 s N_E`, which is the banked `GuardedSourceSlab.q2`, and
   `GuardedSourceSlab.card_le_q2` is that display's own consequence
   `12 s |E| <= q_2`.  The remaining step `12 s |E| >= 12 s` is `|E| >= 1`,
   which is **not** an invented edge-count axiom: it is the frozen field
   `EndpointGraph.card_edge_pos` of the guarded source's own type.  AUX 18.1.
2. **`2 <= m_1` -- RESOLVED, and ALREADY OWNED.**  `06:970--971` derives it
   from the incoming carrier envelope (`m_R >= 1`, `05:36--37`) and the Stage-1
   constructor equation (`07:144`, `Rows(M_1) = [q_1] x Rows(R)`), through
   `q_1 = 2^a - 2` (`06:315`) at the frozen `a >= 3`.  That derivation is
   **already banked in this module** as Part 10's `six_le_stepRowsOne_card`
   (`m_1 >= 6`, itself proved from `Stage1SlotBinding.six_le_q₁` and
   `LevelPublicInput.mRpos`), so `2 <= m_1` needs **no declaration of its own**
   here -- a named `two_le_stepRowsOne_card` would be a restatement of a banked
   theorem, which this route bars.  It is the first of the banked tail's four
   arrangement slots and is available **by pin** to the future composition arc;
   nothing below consumes it.

Neither lookup is registered BLOCK.  The frozen paper's route is stronger than
`06:970`'s own justification needs on the second one (`m_1 >= 6`, not merely
`>= 2`), and the excess is a fact of the banked chain, not a strengthening of
the paper.

### ALREADY-OWNED, consumed by pin and never restated

* `SchedulePhysicalResidue.stageThreeCarrierLowerBound` (`:1269`,
  `06:967` with `06:970--975`) -- **the tail**.  It is **NOT applied anywhere in
  this part**: the composition that would apply it is the OPEN fidelity arc of
  BLOCK/OPEN item 1.  It is named here only to identify which banked slots
  AUX 18.1--18.3 supply.  Its counting half (`patternDensity_pos` `:1198`,
  `all_patterns_occur` `:1209`, `carrierCard_ge_patternCount` `:1230`) is
  reached only through Part 17 and is not touched here.
* `SchedulePhysicalResidue.sq_le_two_pow_of_Hmax` (`:1250`, `06:972--973`) --
  the schedule-arrangement half, applied once, in AUX 18.2.  **Consumed BY
  PIN**; its `H_max`-dominance argument is not repeated.
* `Section5Admissibility.sOf_floor` (`:926`, `06:975`'s `64 | s` and the
  `eq:s-choice` floor) -- the banked owner of the fourth arrangement slot.  It
  is **not consumed below** (the composition that needed it is not restored) and
  it is **not** re-exported as a local `sFor_floor`: the `cc-t7c-r3` gate's
  standing ruling, recorded at `LevelStepConstruction.lean:1000--1005`, is
  "prove it inline from `sScale_floor`; do not introduce a replacement
  `sFor_floor`", and **no declaration below states an `s`-floor**.  When the
  composition arc lands it will reach this owner at
  `LevelStepConstruction.ctxAt P K W` through the `rfl` receipt
  `LevelStepConstruction.sFor_eq_sOf` (`:875`), whose `W` slot may be filled by
  `StageTwoRelaxed.widthsWitness` **only because the receipt is universally
  quantified in `W` and its conclusion is `W`-free**.  No property of that
  record is used below, and none of its (NON-FIDELITY, illustrative) values
  reaches any statement in this part.
* `GuardedSourceSlab.card_le_q2` (`:423`) and
  `GuardedSourceGraph.EndpointGraph.card_edge_pos` (`:306`) -- lookup 1.
* `StageTwoRelaxed.clog_q₂Of` (`:3013`) -- `clog_2 q_2 = r_2` at the derived
  width, the seam `sq_le_two_pow_of_Hmax`'s fourth `H_max` slot needs.
* This module's own Part 9/10/11 surface: `t2_pos` (`:2155`),
  `two_mul_Hmax_le_t2` (`:2178`), `six_le_stepRowsOne_card` (`:2466`, reserved
  for the composition arc, not consumed below), `stepRowsOne_card_pos` (`:2476`),
  `HmaxFor_shape` (`:3187`), `balN_pow_le` (`:5878`, Part 17), `balBuild_eq_some`.
* `LevelStepConstruction.sFor` / `.q2For` / `.r2For` / `.bCapFor` /
  `.stage1BindingFor` / `.StepRowsOne` -- the level schedule's own evaluated
  accessors; none is re-derived.

### Import direction (verified this round, not asserted)

Every cross-module name pinned below is reached with **zero import additions**;
each hop names importer, importee and the import line's `file:line`:

* `BalancedFamilyBuilder.lean:3` imports
  `EthInapproximability.ParameterizedNP.LevelStepConstruction`;
* `LevelStepConstruction.lean:1` imports
  `EthInapproximability.ParameterizedNP.MechanicalCompilerResidue`;
* `MechanicalCompilerResidue.lean:3` imports
  `EthInapproximability.ParameterizedNP.SchedulePhysicalResidue`;
* `SchedulePhysicalResidue.lean:5` imports
  `EthInapproximability.ParameterizedNP.Section5Admissibility`, and
  `SchedulePhysicalResidue.lean:4` imports
  `EthInapproximability.ParameterizedNP.StageTwoRelaxed`.

The direction is consumer-downstream at every hop: this module is strictly
downstream of all four pinned owners, so no banked module is edited and no
upstream name is pinned from a downstream home.  `GuardedSourceSlab` and
`GuardedSourceGraph` are reached through the same chain
(`Section5Admissibility.lean:1--5` closure).  `LevelStepMaterialisation` and
`EffectiveCutoffCertificate` remain **absent** from this module's closure.

### BLOCK / OPEN -- what this part does not do

1. **The composition of `06:966` with `06:967` is NOT landed, and the builder's
   coordinate width `q` is NOT identified with `q_2`.**  The paper's call is
   `A_bal(q_{2,i}, t_{2,i}, m_{1,i})` (`14:1621--1625`), so at the paper's
   application point the family's width *is* `q_2`.  The `cc-t8w` r0 gate ruled
   that a composition theorem stated at a *free* width is a **fidelity defect,
   not an acceptable BLOCK registration**, because it cannot be credited as the
   paper's carrier chain.  Making the paper's identification instead would put
   `t2For P K <= LevelStepConstruction.q2For P K` in hypothesis position, which
   is **false at this route's own banked witness pair** --
   `not_t2ForLeQ2For_at_publicInputYes` and `balBuild_eq_none_at_publicInputYes`
   (Part 14) bank exactly that -- and is the **barred fifth generation** of a
   hypothesis class deleted four times on this route (recorded at
   `EffectiveCutoffCertificate.lean`, item 7 of its `cc-t7s-r3` block).

   **NON-FIDELITY caveat -- this is not a claim against the frozen paper.**
   Carried forward verbatim in substance from the banked owner
   `fourT2LeQ2_not_schedule_theorem` (`:3438--3445`): `06:830--831`'s verb is
   *verify*, and `eq:stage2-structural-gates` is item (v) of the finite condition
   list `06:1197--1226` (`06:1219--1220`) that `sec:effective-cutoff`
   (`06:1169--1177`) discharges beyond a threshold.  **The paper's `q_2 >= t_2`
   gate stands.**  What is false is only the reading of that gate as a universal
   `(Public, K)` identity over this encoding's *unrestricted* domain -- a domain
   the paper never quantifies over, because it works beyond the cutoff.  This
   route declines to *assume* the gate at an unrestricted domain while the
   cutoff machinery (`PARAM-001` / `sec:effective-cutoff`) is unbuilt; that is a
   gap in this route, not a defect in the paper.  So the
   composition is **real mathematics that this route has not done**: it is
   registered as an **OPEN fidelity arc** needing its own commissioned tranche,
   and it is discharged nowhere.  Item (b) of `S5-BALANCED-FAMILY` and every open
   item of `S5-BALANCED-FAMILY-LEVELSTEP-001` are **UNCHANGED and OPEN**.
2. **`|Cols(M_2)| = N_2`, the leftmost equality of `06:966`,** is Part 16's and
   is not restated; no statement below is read at the machine's literal output
   `N` of `14:1623` at all -- reaching that output is item 1's arc.
3. **`eq:physical-stage4-gates` (`06:863--873`) and
   `eq:physical-m3-ceiling-proof` (`06:981--989`)** are still NOT stated here.
   Their owners are `Section5Admissibility.PhysicalStage4Gates` and
   `SchedulePhysicalResidue.physicalM3Ceiling`(`Gate`).  Supplying the
   `9216 * s <= m_3` premise those owners want would need the composition of
   item 1 first, and then the `m_3 = N_2` identification (`06:979`) at a level
   trace, which lives outside this module.  BLOCK, **not** narrowed by this part.
4. **`MATERIALIZE-001`'s machine layer** stays bucket-(c) DEFERRED.
5. **Record item `R-17` is NOT touched here.**  This part is append-only over
   Parts 1--17.

### Statement-numeral screen (this part's own occurrences)

Every numeric literal in a statement below is CANONICAL-FORM at a cited frozen
display -- `12` from `06:124`'s `12 s N_E`; the exponent `2` of `q_2^2` and the
base `2` of `2^{t_2}` from `06:967`'s printed chain; the base `2` of `clog_2`
from `eq:s-choice`'s powers of two -- or carries an explicit **BEYOND-PAPER
AUDIT** label in its own declaration docstring (AUX 18.5, the rejection pole,
whose `1` and `0` are this lane's and claim no legality).  The chain constants
`144`, `9216` and the final `2 s` of `06:967` appear in **no statement below**:
they occurred only in the composition theorem of BLOCK/OPEN item 1, which is not
restored.  No numeral stands where a source-defined quantity belongs: `s`, `q_2`,
`t_2`, `m_1` are `LevelStepConstruction.sFor`, `.q2For`, this module's `t2For`,
and `Fintype.card (LevelStepConstruction.StepRowsOne P K)` at every occurrence.
The occurrence-by-occurrence table, one row per literal with its exact
`file:line`, is in this tranche's lane report.

### Binder provenance

* `P : LevelPublicInput V E`, `K : LevelConfig` -- GENUINELY-FREE: `05:13--52`
  and `06:56--69` quantify the level's public record and universal
  configuration, and `proc:level-step` runs at an arbitrary pair.
* `q` (AUX 18.3 only) -- GENUINELY-FREE at `14:1557--1558` ("positive integers
  `q,t,m` with `q >= t >= 1`"); see BLOCK/OPEN item 1 for why it is *not* pinned
  to `q_2`, and why supplying the `hpat` slot at a free width is admissible here
  while *composing* at a free width was not.
* `V`, `E` -- the ambient vertex and edge carriers of the guarded source.

**Zero source-defined quantity enters as a free binder.**  `s`, `q_2`, `t_2`,
`m_1` and `N_2` appear nowhere as binders in this part.  The
occurrence-by-occurrence binder table is in this tranche's lane report.

### Canonical inhabitation

**Not settled by this part, and not claimed.**  No statement below is a
conditional on a builder output, so none of them is a vacuous shell: AUX 18.1,
18.2 and 18.4 are unconditional at every `(Public, K)`, AUX 18.3 carries only the
builder's own frozen guard `t_2 <= q`, and AUX 18.5 is closed.  AUX 18.4 exhibits
a successful run of `A_bal` unconditionally, but it fills the free `q` with `t_2`
rather than with the paper's `q_2`, so it is labelled **NON-FIDELITY /
BEYOND-PAPER AUDIT**: its output is *not* the `A_bal(q_{2,i}, t_{2,i}, m_{1,i})`
output of `14:1621--1625`, and it settles **no** canonical non-vacuity for the
composition arc of BLOCK/OPEN item 1.  The paper's own instance of the call is
cutoff-generated and stays **canonical-DEFERRED** behind `sec:effective-cutoff`
(`06:1169--1177`, item (v) at `06:1219--1220`) and `PARAM-001`.  Registration is
not discharge.

Reader counterpart: **not claimed**, checked at both polarities this round in
the pinned release copy (`versions/2026-08-02-iteration-cexc-repair/source/`
`reader-facing`).  The nearest positive text is
`03-parameterized-construction.tex:477--485`, but it is **unlabelled prose
inside the proof of `eq:paper-M3-gates`**, its chain is three links shorter
than `06:967` (`N_2 >= 2^{t_2} >= q_2^2 >= 2s`), and it is read at the depth
`b_2` rather than the physical `b_T` -- the same three divergences Part 17
recorded; this route never cites prose as a statement.  The negative polarity
was checked at `04-bridge.tex:152--182` (`cor:one-level-amplifier`), which
carries the one-level budgets and the exact carrier equations and says nothing
about a carrier lower bound. -/

/-- **AUX 18.1 (LOOKUP 1 of `06:973--974`, resolved at the defining display):
`12 s <= q_2` at the level schedule.**

`06:124` *defines* `q_2` as "the least power of two at least `12 s N_E`"
(`04:386--391`, `def:guarded-source-constructor`, at its own home), banked as
`GuardedSourceSlab.q2`; `GuardedSourceSlab.card_le_q2` is that display's own
consequence `12 s |E| <= q_2`.  The frozen sentence `06:974` then reads
`q_2 >= 12 s |E| >= 12 s`, and the second link is `|E| >= 1`, which is the
guarded source type's own field `EndpointGraph.card_edge_pos` -- **not** an
invented edge-count assumption.  `s` is `LevelStepConstruction.sFor`, the
evaluated `eq:s-choice`; no numeral is assigned to it.

This is the third of the four arrangements `06:970--975` supplies, and the one
the banked tail takes as `hq₂`.

General in the two carriers, the public record and the configuration.  Reader
counterpart: **not claimed**.  PROVED. -/
theorem twelve_sFor_le_q2For (P : LevelPublicInput V E) (K : LevelConfig) :
    12 * LevelStepConstruction.sFor P K ≤ LevelStepConstruction.q2For P K := by
  have hE : 0 < Fintype.card E := P.G.card_edge_pos
  have hbase : 12 * LevelStepConstruction.sFor P K * 1
      ≤ 12 * LevelStepConstruction.sFor P K * Fintype.card E :=
    Nat.mul_le_mul_left _ hE
  have hq := GuardedSourceSlab.card_le_q2 P.G (LevelStepConstruction.sFor P K)
  have hq' : 12 * LevelStepConstruction.sFor P K * Fintype.card E
      ≤ LevelStepConstruction.q2For P K := hq
  omega

/-- **AUX 18.2 (`06:972--973` at the evaluated chain, hypothesis DISCHARGED):
`q_2^2 <= 2^{t_2}`.**

The frozen sentence is "`eq:t2-search` and `eq:Hmax` give
`t_2 >= 2 H_max >= 2 log_2 q_2`", whose integer content is `q_2^2 <= 2^{t_2}`.
The banked owner of that implication is
`SchedulePhysicalResidue.sq_le_two_pow_of_Hmax` (`:1250`), **consumed by pin**
here: nothing of its `H_max`-dominance argument is repeated.  What this lemma
adds is that on the level schedule's own domain the owner's hypothesis
`2 H_max <= t_2` is **not a hypothesis at all** -- Part 11's `HmaxFor_shape`
and Part 9's `two_mul_Hmax_le_t2` discharge it -- so the conclusion is
unconditional at every `(Public, K)`.

The one seam is the owner's fourth `H_max` slot, which is spelled
`clog_2 q_2` while `HmaxFor` carries the derived `r_2`; they agree because
`q_2` is a power of two, which is the banked `StageTwoRelaxed.clog_q₂Of`,
consumed by pin.  No real logarithm is evaluated anywhere.

This is the second of the four arrangements `06:970--975` supplies, and the one
the banked tail takes as `hq₂sq`.

General in the two carriers, the public record and the configuration.  Reader
counterpart: **not claimed**.  PROVED. -/
theorem q2For_sq_le_two_pow_t2For (P : LevelPublicInput V E) (K : LevelConfig) :
    LevelStepConstruction.q2For P K ^ 2 ≤ 2 ^ t2For P K := by
  have hclog : Nat.clog 2 (LevelStepConstruction.q2For P K)
      = LevelStepConstruction.r2For P K :=
    StageTwoRelaxed.clog_q₂Of P.G (LevelStepConstruction.sFor P K)
  have ht : 2 * ParameterSchedule.HmaxSched (LhFor P K)
        (LevelStepConstruction.stage1BindingFor P K).q₁ (lqFor P K)
        (Nat.clog 2 (LevelStepConstruction.q2For P K))
        (LevelStepConstruction.bCapFor P K)
      ≤ t2For P K := by
    rw [hclog]
    exact two_mul_Hmax_le_t2 (HmaxFor_shape P K)
  exact SchedulePhysicalResidue.sq_le_two_pow_of_Hmax
    (LevelStepConstruction.q2For P K) (LhFor P K)
    (LevelStepConstruction.stage1BindingFor P K).q₁ (lqFor P K)
    (LevelStepConstruction.bCapFor P K) (t2For P K) ht

/-- **AUX 18.3 (the `06:966` head link at the level step's own second and third
arguments): `m_1^{t_2} <= N`.**

Part 17's `balN_pow_le` is general in `(q, t, m)`; this is that head link at
the two arguments `14:1621--1625` fixes -- `t_{2,i}` is Part 11's `t2For` and
`m_{1,i} = |Rows(M_1^{(i)})|` is Part 10's
`Fintype.card (LevelStepConstruction.StepRowsOne P K)` -- with both of the
builder's guards **discharged** rather than assumed: `m_1 > 0` is Part 10's
`stepRowsOne_card_pos` and `t_2 >= 1` is Part 9's `t2_pos`, both consumed by
pin.

**The remaining binder `htq : t_2 <= q` is the block, kept explicit.**  It is
*not* `t2For P K <= q2For P K`: `q` is the builder's own free coordinate width
of `14:1557--1558`, and the level-step identification `q = q_2` is BLOCK/OPEN
item 1 of the part docstring.  Making that substitution here would produce the
barred hypothesis, false at this route's own banked witness pair -- false over
this encoding's unrestricted domain, *not* a denial of the frozen paper's gate
(see the NON-FIDELITY caveat in BLOCK/OPEN item 1 of the part docstring).

This is the `hpat` slot the banked tail takes.  Supplying that slot is what this
part lands; **applying** the tail to it is the OPEN fidelity arc of BLOCK/OPEN
item 1 and happens nowhere below.

General in the two carriers, the public record, the configuration and the
coordinate width.  Reader counterpart: **not claimed**.  PROVED. -/
theorem stepRowsOne_pow_le_balN (P : LevelPublicInput V E) (K : LevelConfig)
    {q : ℕ} (htq : t2For P K ≤ q) :
    Fintype.card (LevelStepConstruction.StepRowsOne P K) ^ t2For P K
      ≤ balN q (t2For P K)
          (Fintype.card (LevelStepConstruction.StepRowsOne P K)) :=
  balN_pow_le q (t2For P K)
    (Fintype.card (LevelStepConstruction.StepRowsOne P K))
    (stepRowsOne_card_pos P K)
    (t2_pos (LhFor P K) (LevelStepConstruction.bCapFor P K) (HmaxFor P K))
    htq

/-- **AUX 18.4 -- NON-FIDELITY / BEYOND-PAPER AUDIT: `A_bal` returns a parsed
output at every `(Public, K)` when its coordinate width is filled with `t_2`.**

At the coordinate width `q = t_2` the builder's three frozen guards
(`14:1557--1558`, `14:1750`) all hold unconditionally -- `m_1 > 0` by Part 10,
`t_2 >= 1` by Part 9, `t_2 <= t_2` reflexively -- so the machine returns its
parsed output at *every* public record and configuration.  That is the whole of
what this receipt says.

**NON-FIDELITY / BEYOND-PAPER AUDIT** (`cc-t8w` gate record item 4, recorded
here in the words the gate used).  The coordinate width `q = t_2` is **this
lane's**, not the paper's: at the paper's application point the width is `q_2`
(`14:1621--1625`), and the output exhibited here is therefore **not** the
`A_bal(q_{2,i}, t_{2,i}, m_{1,i})` output of that display.  So this receipt
**claims no legality**, **settles no canonical non-vacuity** for the composition
arc of BLOCK/OPEN item 1, discharges nothing, and is strictly weaker evidence
than any statement at the paper's own application point.  It is not cited by any
statement or proof term in this part.

General in the two carriers, the public record and the configuration.  Reader
counterpart: **not claimed**.  PROVED. -/
theorem balBuild_at_t2For_width_eq_some (P : LevelPublicInput V E)
    (K : LevelConfig) :
    balBuild (t2For P K) (t2For P K)
        (Fintype.card (LevelStepConstruction.StepRowsOne P K))
      = some (balN (t2For P K) (t2For P K)
            (Fintype.card (LevelStepConstruction.StepRowsOne P K)),
          balDescriptor (t2For P K) (t2For P K)
            (Fintype.card (LevelStepConstruction.StepRowsOne P K))) :=
  balBuild_eq_some (stepRowsOne_card_pos P K)
    (t2_pos (LhFor P K) (LevelStepConstruction.bCapFor P K) (HmaxFor P K))
    (le_refl _)

/-- **AUX 18.5 (STATEMENT POLE for AUX 18.1) -- BEYOND-PAPER AUDIT, a rejection
probe: `06:974`'s second link really does need `N_E >= 1`.**

AUX 18.1 reads `q_2 >= 12 s |E| >= 12 s`, and the second link is the only place
the guarded source's edge count enters.  A green build cannot see whether that
input is load-bearing.  This probe settles it on the defining display itself
(`06:124`, `q_2 = least power of two at least 12 s N_E`): evaluated at
`N_E = 0` the display returns `2^{clog_2 0} = 1`, which is **below** `12 s`
already at `s = 1`.  So `|E| >= 1` is not decoration, and AUX 18.1 is not a
strengthening of the paper -- it is the paper's own chain with its own input.

**BEYOND-PAPER AUDIT.**  The values `s = 1` and `N_E = 0` are chosen by this
lane, and no `EndpointGraph` realizes the second one (`card_edge_pos` is a
field of the type).  The probe therefore **claims no legality**: it audits our
encoding at a point the paper never visits, is not an inhabitation receipt, and
discharges nothing.

Closed -- no binder, hence no instantiation can make it vacuous.  Reader
counterpart: **not claimed**.  PROVED. -/
theorem twelveScale_le_leastPowTwo_needs_positive_edge_count :
    2 ^ Nat.clog 2 (12 * 1 * 0) < 12 * 1 := by
  norm_num

end EthInapproximability.ParameterizedNP.BalancedFamilyBuilder
