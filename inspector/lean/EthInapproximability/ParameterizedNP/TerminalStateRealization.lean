import EthInapproximability.ParameterizedNP.TwoStreamState
import EthInapproximability.ParameterizedNP.RawLowProfileBody

/-!
# Parameterized NP route: the owner--donor realization of a terminal state

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/09-first-wrapper.tex`, **lines 658--833** --
  `lem:terminal-state-realization`, "Owner--donor realization of a terminal
  state", opening immediately after `def:two-stream-state` (whose last line
  `09:657` the predecessor module `TwoStreamState` discharges) and stopping
  immediately before `lem:terminal-two-stream` (`09:834`).  The anchors traced
  here, in the order the frozen block prints them:
  * `09:658--704`, the statement: the completed scale-alignment protocol `P`,
    the specified final Alice-frontier node `v`, the surviving rectangle
    `Z = extract(U, X_Z, Y_Z)`, the **distinct** outer coordinates `i`, `j`,
    and the three assumption clauses
    * **(a)** `09:671--682`: for some `R_f in {R_Sigma, R_D}`,
      `|X_Z cap ({i} x R_G)|/|R_G| >= 1 - eps` and
      `|X_Z cap ({j} x R_f)|/|R_f| >= delta'`, with `0 <= eps < 1` and
      `0 < delta' <= 1`;
    * **(b)** `09:683--694`: `i` outside the singleton projection cover and
      `(i,j)` outside the pair projection cover, so every ordinary Stage-3 bin
      at `i` has quotient row density at least `tau_0 = 2 s x_T` (`09:686`);
      the `sec:wrapper-projection-covers` averaging selects ordered bins
      `p_o, p_f` whose support
      `P_* subseteq pi_{i,j}(Y_Z) cap (Y_{T,p_o} x Y_{T,p_f})` satisfies
      `|P_*|/m_T^2 >= a_min` (`09:694`);
    * **(c)** `09:695--700`: the ordinary and protected duplications are
      uniform on every `[q_2] x C_1`-fibre, the pair-family transfer is applied
      to the actual support `P_*`, its loss is at most `(1 + eps_2)^2`, and
      `(a_min - tau_0)/(1 + eps_2)^2 >= 49/64` (`09:699`);
    with conclusion `09:702--703`: "Then `Z` is an `(eps, delta')`-two-stream
    terminal state in the sense of `def:two-stream-state`";
  * `09:706--723`, the two label-forgetting maps `omega_o, omega_f` leaving a
    raw column `c = (xi, j) in Omega` with `j : [s] -> J_2`, the **tuple
    coordinate selectors** `rho_{p_o}(c) = j(p_o)`, `rho_{p_f}(c) = j(p_f)`
    (`09:713--718`), the images `E_o, E_f`, their fibres `O_alpha, F_alpha`, and
    the least surviving representatives `iota_o, iota_f`;
  * `09:725--739`, the exact fibre degrees
    `d_G = w_0 |K_R| |J_2|^{s-1}`, `d_Sigma = w_Sigma |J_2|^{s-1}`,
    `d_D = w_D` -- "These positive equal-fibre counts prove **regularity**
    rather than merely surjectivity" -- feeding `eq:regular-density-transfer`
    (`09:80--84`);
  * `09:739--760`, the two transferred averages
    `(1/q_2) sum_alpha |O_alpha|/|C_1| >= 1 - eps` and
    `(1/q_2) sum_alpha |F_alpha|/|C_1| >= delta'`, and the disjointness of the
    two physical representative streams -- "This proves clause (i)";
  * `09:762--766`, the outer-coordinate projection `pi_{i,j}`, the ambient
    denominator `m_T^2`, the least preimage section `sigma_*`, and the
    duplication-forgetting maps `zeta_p`;
  * `09:768--802`, the two template maps
    `eq:terminal-realization-ordinary-template-map` (label **`09:783`**) and
    `eq:terminal-realization-foreign-template-map` (label **`09:786`**), both
    instances of `eq:raw-stage4-template-value` (`07:558`), together with the
    full physical chain
    `U((h, N-row(c)), y) = N(N-row(c), y(h)) = A(y(h), A-col(c)) = B((p,z), c)`
    at `h = i` or `j` (`09:790--795`) -- landing on
    `eq:terminal-state-ordinary-entry` and `eq:terminal-state-foreign-entry`;
  * `09:804--817`, the ordinary Stage-3 restriction
    `extract(Interlace(S_2, s), bigcup_p {p} x R_p, K_ord)` obtained by
    "forgetting the raw-column prefix", with
    `|K_ord|/|Cols(S_2)|^s >= 1 - eps` from the physical density in (a) and
    `|R_p| >= ceil(tau_0 |Rows(S_2)|)` from the singleton cover conclusion in
    (b) -- "This proves clauses (iii) and (iv)";
  * `09:819--831`, the universal clause (v): every `P' subseteq P_*` losing
    fewer than `tau_0 m_T^2` pairs has physical density greater than
    `a_min - tau_0`, forgetting uniform labels does not decrease indexed
    density, and the resulting classical two-copy restriction has density at
    least `(a_min - tau_0)/(1 + eps_2)^2 >= 49/64`; "Taking `P' = P_*` proves
    clause (ii) without spending the later routing loss."

## The conclusion is the **banked** predicate at the **actual** schedule values

`terminalStateRealization` concludes
`TwoStreamState.TwoStreamState` -- the banked `def:two-stream-state`
(`TwoStreamState.lean`, SHA-256
`1DD7EAF859765FEC9D99FCBFED3841E581EA41E09E5150FD0E9B2B08BA378530`), all **45**
fields, consumed by pin and nowhere restated.  Its five real parameters are
**not** free-instantiated:

* `lambda_T` is the construction's own template density
  `templateDensity YT = ScaleAlignOpening.lambdaTemplate (bigcup_p Y_{T,p})`,
  i.e. the frozen `lambda_T = |Y_T|/|Y|` of `09:367--371` read off the very
  template bins the hypotheses quantify over -- **not** a fresh real.  The same
  expression occurs in hypothesis (b), in hypothesis (c) and in the conclusion,
  so no instantiation can make the two frozen gates vacuous;
* `eps_2` and `x_T` are the schedule's balancedness error and Stage-3 seed
  depth; they occur only inside `tauZero s xT = 2 s x_T` (`09:376`, banked) and
  `(1 + eps_2)^2`, identically in hypotheses (b)/(c), in the row-count clause
  and in the conclusion.  The banked
  `TwoStreamState.terminalSelectorData_needs_eps2` exhibits parameters
  at which hypothesis (c) fails, so the bundle is not satisfiable at arbitrary
  `eps_2`;
* `eps` and `delta'` are the lemma's genuine universals, exactly as `09:682`
  prints them.

`rho_p` is likewise never free: the conclusion is stated at
`rho := fun p o => tup o p`, the frozen tuple-coordinate selector of
`09:713--718`, where `tup` is the raw column's `j : [s] -> J_2` component.  A
free `rho` would make clause (i) a statement about an unrelated readout.

## What is a hypothesis, and what is **proved**

Twenty-six of the forty-five fields are **derived** inside this module; the rest
are the frozen assumption clauses and the construction data the frozen proof
names but does not build here.  Derived, with their frozen lines:

* `rows_nonempty`, `cols_nonempty` (`09:488` via `09:682`/`09:694`): the guards
  `delta' > 0` and `a_min > 0` force both sides of the rectangle to be
  inhabited -- neither is assumed;
* `iotaOrd`, `iotaFor`, `iotaOrd_mem`, `iotaOrd_section`, `iotaFor_mem`,
  `iotaFor_section` (`09:721--723`): "Choose the least surviving representative
  of each image point" -- a selection from image membership, built by
  `imageSection`;
* `ordinary_density`, `foreign_density` (`09:739--756`): the frozen density
  transfer, twice, through the regular tuple readout and then through the bin
  evaluation, with `meanFibreDensity_eq_card_div` supplying the frozen
  identification of `(1/q_2) sum_alpha |O_alpha|/|C_1|` with `|E_o|/|J_2|`;
* `sigmaStar`, `sigmaStar_mem`, `sigmaStar_section` (`09:764--765`): "Choose the
  least preimage in `Y_Z` of each pair in `P_*`";
* `ordinary_entry`, `foreign_entry` (`09:768--802`): the two template maps
  `09:783`/`09:786`, each derived from the physical value equation and the
  Stage-2 value equation, **both** through the template-**row** formula and
  never through a source-row formula;
* `Kord`, `Kord_density`, `selCol`, `selCol_mem`, `selCol_inj`,
  `selRow_inj`, `selector_entry` (`09:804--817`): `K_ord` is the *image* of the
  surviving ordinary rows under "forget the raw-column prefix", so its frozen
  density really is transferred from (a) rather than posited; the two
  injectivities and the entry preservation follow;
* `uniform_transfer` (`09:819--828`): the universal clause (v), proved by the
  regular density transfer through `zeta_{p_o} x zeta_{p_f}` (degree `d_T^2`)
  after the arithmetic `|P'|/m_T^2 > a_min - tau_0`.

Frozen assumption clauses carried as **explicit binders** (never a premise
bundle): `hProtected` (`09:672`), `hEpsNonneg`/`hEpsLtOne`/`hDeltaPos`/
`hDeltaLeOne` (`09:682`), `hOrdDensity`/`hForDensity` (`09:674--681`),
`hRegG`/`hRegF` (`09:695--696` and `09:725--739`), `hPstarTyped`/`hPstarProj`/
`hPairDensity` (`09:689--694`), `hRbinCard` (`09:685--686`, `09:813--814`),
`hSelectorGate` (`09:697--700`).  Construction data the frozen proof names:
`htemplate_card` and `hbins` (`09:367--369`), `htemplate_regular`
(`09:565--568`, "uniform template-row duplication"), `hStwo` (the Stage-2 value
equation, banked as `StageTwoRelaxed.stageTwo_apply`), `hNval` (`09:790--795`
composed with `eq:raw-stage4-template-value`), and the Stage-3 row section
`selRow` with `hSelRowMem`/`hSelRowTyped`/`hSelDist` (`09:628--632`,
`09:814--816`).

## Owner/donor apparatus: consumed as **output**, never as premise

Per the tranche planner's first-hand ruling, read again here against
`09:706--832`: the frozen proof cites `eq:regular-density-transfer` (`09:83`),
the `sec:wrapper-projection-covers` averaging (inside hypothesis (b)),
`eq:raw-stage4-template-value` (`07:558`), the checked relaxed-to-classical
transfer, and `def:two-stream-state`.  **No Section-8 owner/donor record occurs
as a premise anywhere in the statement or the proof.**  Accordingly
`DenseSourceOwners.SelectedBranchData` and `OwnerAssignment` appear in no
hypothesis, `DenseRoutingInvariant.RoutedToken` and
`DenseWeightedFrontier.WeightedFrontierInput` are barred outright, and the
`DenseAliceClosure` gate-evidence and rejected-candidate declarations are not
imported into any statement.  The Section-8 bank enters only through already
banked *outputs* at the citation sites: `WrapperProjectionCovers.tauZero`,
`.rhoPair`, `.aMin`, `.wrapperTemplateGates`, and
`ScaleAlignOpening.lambdaTemplate`.

## What is deliberately **not** introduced (`M1`--`M10`, frozen Section 2)

* No complexity or robustness conclusion is a constructor field: the two new
  non-propositional definitions are `RegularOn` (a finite fibre-count predicate
  on a map restricted to a finite reservoir) and `imageSection` (a finite
  selection function).  Neither mentions a protocol, a promise certificate, or
  a cost.
* `templateDensity` is a *density*, `= |Y_T|/|Y|`, and is proved equal to
  `s m_T/|Y|` on disjoint bins (`templateDensity_eq_of_disjoint`); it restates
  nothing banked -- `ScaleAlignOpening.lambdaTemplate` is applied, not copied.
* The frozen exact fibre degrees `d_G`, `d_Sigma`, `d_D` of `09:727--733` are
  carried at **the level each reservoir actually supports**, and this is a
  substantive reading of `09:734--738`, not a stylistic choice:
  * the **ordinary** reservoir is assumed regular at the *tuple* level,
    `RegularOn RG (fun r => tup (omg r)) dOrd`.  That is exactly `09:734--736`,
    "in the base reservoir one freely chooses `xi in K_R`, the other `s-1`
    entries of `j`, and the repetition label": fixing the whole tuple still
    leaves `w_0 |K_R|` rows, uniformly, over *every* tuple.  The per-bin degree
    `d_G = w_0 |K_R| |J_2|^{s-1}` is then **derived** by composing with the bin
    evaluation, whose regularity is proved (`evalFibre_card_congr`), not
    assumed.  The tuple level is needed because `K_ord` (`09:804`) is built from
    the ordinary rows alone;
  * the **foreign** reservoir is assumed regular only at the *per-bin* level,
    `RegularOn Rf (fun r => tup (omg r) pFor) dFor`, which is the frozen display
    `d_Sigma`, `d_D` verbatim.  Assuming it at the tuple level would be an
    **over-strong hypothesis that the construction falsifies**: `09:737--738`
    says that in the diagonal reservoir "the map is bijective before its
    repetition label is added", i.e. `d_D = w_D` with no `|J_2|^{s-1}` factor,
    so `D_diag` carries only the *constant* tuples and its tuple readout is not
    surjective onto `[s] -> J_2` once `s >= 2`.  A tuple-level hypothesis would
    therefore be unsatisfiable in the `R_f = R_D` branch of `09:672` and would
    silently empty half the lemma.
* Nothing in this module discharges or narrows `hDenseRung`.

## Coverage limits

This tranche lands `lem:terminal-state-realization` (`09:658--833`) and nothing
beyond it.  `lem:terminal-two-stream` (`09:834--1183`) is **GAP-EXPOSED** and is
the one remaining slice of this block; the further ranges `09:1184--1366`,
`09:1367--1511`, `09:1512--1781` stay GAP-EXPOSED as recorded by the
predecessor.  `lem:certified-row-ladder` (`A:148--162`) has no Lean declaration
and none is created.  `EXPANDER-001` occurs in no hypothesis: `eps_2` enters as
a bare real whose *size* the banked gate constrains, and `LegacyNPCC.Stage12` is
not in the import chain, so no opt-in ledger note is required.  **No route
completion is claimed.**

## Reader counterparts

Frozen release, `reader-facing/sections/A-stage4-details.tex`, opened first-hand
for this round.  **No reader item is claimed by any declaration in this
module.**  The reader mentions this block's content in exactly one place, lines
`373--384`, and that text sits *inside the proof* of
`thm:adapted-stage4-profile`: "At the frontier, associate every surviving
ordinary outer copy with a protected donor copy ... After selecting one template
bin for each stream, the template-row identity ... realizes the ordinary stream
in one copy and the tagged ordinary--protected pair in two copies."  That is
prose, not a numbered or displayed statement, and the reader-counterpart
discipline bars citing prose as a statement.  The one numbered display it
references, `eq:paper-B-template`, is **already assigned** to
`RawStageFour.rawStageFour_template`, and no reader item may carry two
assignments; it is therefore not reclaimed here.  Searched first-hand across the
whole reader artifact: `a_min`, `m_T`, `Y_{T,p}`, `tau_0` in this sense, `E_o`,
`K_ord` and the constant `49/64` occur **nowhere**, so the frozen quantities
this module realizes have no reader counterpart at all.  Every declaration below
therefore carries its autoformalization anchor alone.  The reader's own sentence
at `396--399` -- the owner--donor count "is expanded line by line in the
ultra-explicit companion" -- names exactly the frozen `09:658--833` traced here.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A` the `RegularOn` predicate, general (5): `regularOn_univ_iff_isFibreBounded`,
  `RegularOn.card_eq`, `RegularOn.card_le_mul_image`, `regularOn_density_transfer`,
  `regularOn_prod`.
* `B` the bin evaluation, general (3): `evalFibre_card_congr`,
  `evalFibre_card_pos`, `isFibreBounded_evalAt`.
* `C` the frozen averaged density, general (2): `meanFibreDensity_eq_card_div`,
  `meanFibreDensity_le_one`.
* `D` the least-representative selection, general (3): `imageSection_spec`,
  `imageSection_mem`, `imageSection_apply`.
* `E` the template density, general (2): `templateDensity_eq`,
  `templateDensity_eq_of_disjoint`.
* `F` the clause-(v) provenance encoding, general (5):
  `hasFamilyProvenance_iff_subset`, `HasFamilyProvenance.mono`,
  `hasFamilyProvenance_card_le`, `hasFamilyProvenance_pstar_nonempty`,
  `hasFamilyProvenance_univ_iff`.
That is **20 general battery entries proved**, with `0` unproved, alongside the
principal deliverable (`terminal_state_realization`), its witnessing record
(`terminalStateRealization`), **two statement poles**
(`kord_witness_is_nonempty`, `diagonalTupleReadout_not_regular`), the Section-8
**smoke** readouts at the inherited `s = 1` carriers, and the Section-9
**schedule-legal** LANE-GATE 3 witness.

## Repair r1: the additive witness-coverage fix

The statement gate of the first round accepted every anchor of
`terminal_state_realization` and rejected the tranche on **witness coverage**:
its only inhabitant sat at `s = 1` (excluded by `07:445--447`), at
`lambda_T = 1` (excluded by `08:82--92` with `08:126--129`), and in the
`R_f = R_Sigma` leg of `09:672` alone, so `hbins` was discharged by
`Subsingleton.elim` and never exercised.  The repair is **purely additive** --
no closed statement of the eighteen aux lemmas, of the principal deliverable, or
of its witnessing record was changed:

* **Section 9 is new**: a second, schedule-legal inhabitant at `s = 2 = 2^1`,
  with two genuinely disjoint template bins (so `hbins` is a real proof and the
  derivation of `selRow_inj` runs on it), at `lambda_T = 9/10 < 1` over a column
  carrier that reproduces the source blocks of `eq:protected-labelled-carriers`,
  and firing in **both** branches of `09:672` -- the diagonal branch through the
  per-bin `hRegF` that `diagonalTupleReadout_not_regular` shows is the only
  satisfiable form there, now re-derived at the actual reservoir
  (`terminalStateRealization_fires_in_diagonal_branch`);
* **Section 8 is renamed, not deleted**: the inherited `s = 1` carriers stay as a
  second parameter point but every name now says *smoke*, and
  `smokeRealization_hypotheses_hold` no longer claims schedule legality;
* `terminalRealization_needs_eps2` is **removed** in favour of the banked
  `TwoStreamState.terminalSelectorData_needs_eps2`, which it duplicated verbatim
  (fixed-interface discipline);
* `probeRealization_conclusions_fire`'s second conjunct, formerly the vacuous
  `exists Q, Q.Nonempty`, was rewritten to read off an exact cardinality.  **That
  fix was itself defective and is superseded by `r2` below.**

The banked `TwoStreamState.probeState` remains inhabited only at `s = 1`; that
is a defect of the **predecessor** module, is recorded as owed to its own
tranche, and is not repaired here -- `TwoStreamState.lean` is untouched.

## Repair r2: the two-declaration **statement** repair

The `r1` statement gate returned `66 CLEAR / 2 REVISE / 0 BLOCK`.  The two
rejections were `probeRealization_conclusions_fire` and
`schedRealization_conclusions_fire`, and the defect was **vacuity of the type**,
not of the proof.  After comment stripping the `r1` statements were

  `(0 < Fintype.card ProbeCl) and (exists Q : Finset (L_2 x L_2), Q.card = 4)`
  `(0 < Fintype.card SchedCl) and (exists Q : Finset (L_2 x L_2), Q.card = 9)`

-- closed statements mentioning **no `TwoStreamState` record at all**.  Since
`ProbeLtwo = Bool` and `SchedLtwo = Slot 3`, the two products have exactly `4`
and `9` elements, so `Finset.univ` discharges each existential outright and the
gate seat kernel-checked both as `<by decide, <Finset.univ, by decide>>` with no
record in scope.  The forcing argument lived entirely in the proof term.

The `r2` repair, exactly as the gate prescribed:

* both theorems now take the realized record `st` as an **explicit binder**, so
  the `TwoStreamState` is in the type;
* the conclusion retains the **provenance** conjunct that
  `TwoStreamState.fixedBin_of_uniform` already returns and that `r1` discarded
  with `obtain <Q, -, hQ>`: every `z in Q` is `(zeta_{p_o} y_1, zeta_{p_f} y_2)`
  for an actual `y in st.Pstar`, at the record's own `st.pOrd`, `st.pFor`.  `Q`
  is therefore selector data *about the record*, not a free-standing subset of a
  small carrier;
* the free-standing `0 < Fintype.card _` conjuncts are **dropped**: they are
  carrier arithmetic and were never consequences of the record;
* the adversarial probe now fails **by type** -- `<Finset.univ, by decide>` does
  not elaborate against either restated statement ("Expected type must not
  contain free variables"), and with the elaborator's own `+revert` hint it
  fails to synthesize `Decidable`, because the goal quantifies over `st`;
* two **use-site companions** fill the binder at the module's own named
  constructions, so neither restated theorem is hypothetical:
  `probeRealization_conclusions_fire_at_smoke_state` at `smokeRealization_state`
  and `schedRealization_conclusions_fire_at_schedState` at `schedState`, the
  latter left generic in `R_f` so it covers **both** branches of `09:672` at
  once;
* Section 10 adds the general `familyShadow` / `HasFamilyProvenance` encoding
  with its five-lemma battery, and the two forcing corollaries
  `probeRealization_forces_full_shadow`, `schedRealization_forces_full_shadow`,
  which read the payoff off the restated statements: for *every* record at
  either parameter point the shadow of `st.Pstar` is the **whole** family-index
  square, so `st.Pstar` carries at least `4`, resp. `9`, physical pairs.

The `r2` change touches these declarations and nothing else: the 66 `CLEAR`
declarations of `r1` are byte-identical, and `TwoStreamState.lean` remains
untouched at its consumption pin.

## Consumption bar carried from the `r1` gate memo (paragraph E)

The Section-9 witness is a **legality witness only**.  At `s = 2`,
`lambda_T = 9/10`, `x_T = 1/200` it satisfies clauses (a), (b), (c) of
`09:670--701` -- which is all `lem:terminal-state-realization` imports -- but it
**fails two atomic clauses** of the banked `eq:wrapper-template-gates`
(`09:387--395`): `99/100 <= lambda_T` fails at `9/10`, and `tau_0 <= 1/100`
fails at `tauZero 2 (1/200) = 1/50`.  Consequently:

* `schedRealization_hypotheses_are_legal`,
  `terminalStateRealization_fires_at_schedule_values`,
  `terminalStateRealization_fires_in_diagonal_branch`,
  `schedRealization_conclusions_fire` and its companions certify legality of
  **this lemma's** hypotheses at a schedule-legal `s`.  **No downstream
  declaration may consume any of them as certifying
  `wrapperTemplateGates`**, and none does: `hSelectorGate` is discharged
  directly at the witness numerals by `norm_num` rather than through
  `terminalSelectorData_of_gates`, and `wrapperTemplateGates` occurs in no
  Section-9 statement;
* **no route parameter may be read out of the Section-9 numerals.**  They are
  tier 2: `m_T = 9` is far below the `06:703` floor and `q_2 = 2` sits below
  `eq:stage2-structural-gates`.  Meeting `99/100 <= lambda_T` with
  `lambda_T < 1` at `s = 2` forces `|Y| >= 200`, `m_T >= 99` and `|P_*| >= 9702`
  typed pairs, beyond any `decide`-checkable carrier; what is certified here is
  the **qualitative** legality the frozen source demands.
-/

namespace EthInapproximability.ParameterizedNP.TerminalStateRealization

open Finset
open Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.WrapperProjectionCovers
open EthInapproximability.ParameterizedNP.TwoStreamState

/-! ## Section 1  `RegularOn`: `def:fibre-bounded` restricted to a reservoir

`09:725--739` applies `eq:regular-density-transfer` to the maps **from the three
physical reservoirs** `R_G`, `R_Sigma`, `R_D` -- not from the whole row carrier
of `N`.  The banked `RawLowProfileBody.IsFibreBounded` is a predicate on a map
out of a whole `Fintype`; the frozen application needs the same counting
relative to a `Finset`.  `RegularOn` is that relativization, and
`regularOn_univ_iff_isFibreBounded` records that it agrees with the banked
notion where the banked notion applies, so nothing banked is restated. -/

/-- **`09:63--66` relativized to a reservoir.**  `phi` is *regular of degree `d`
on `R`* when every fibre of `phi` **inside `R`** has exactly `d` elements.  At
`R = univ` this is the banked `IsFibreBounded phi d d`; the frozen degrees
`d_G = w_0 |K_R| |J_2|^{s-1}`, `d_Sigma = w_Sigma |J_2|^{s-1}`, `d_D = w_D`
(`09:727--733`) are of exactly this shape, being counts inside one reservoir. -/
def RegularOn {A B : Type*} [DecidableEq B] (R : Finset A) (φ : A → B) (d : ℕ) : Prop :=
  ∀ b : B, (R.filter fun a => φ a = b).card = d

/-- **Aux A1 (the relativization is faithful).**  On the full carrier,
`RegularOn` is the banked `IsFibreBounded` at equal bounds.  This is the check
that Section 1 generalizes the banked notion instead of drifting from it.
General. -/
theorem regularOn_univ_iff_isFibreBounded {A B : Type*} [Fintype A] [DecidableEq B]
    {φ : A → B} {d : ℕ} :
    RegularOn (Finset.univ : Finset A) φ d ↔ RawLowProfileBody.IsFibreBounded φ d d := by
  constructor
  · intro h b
    exact ⟨le_of_eq (h b).symm, le_of_eq (h b)⟩
  · intro h b
    exact le_antisymm (h b).2 (h b).1

/-- **Aux A2 (`09:91`, "Summing the lower fibre bound over `B`").**  A regular
map of degree `d` on `R` forces `|R| = d |B|`.  General. -/
theorem RegularOn.card_eq {A B : Type*} [Fintype B] [DecidableEq B] {R : Finset A}
    {φ : A → B} {d : ℕ} (h : RegularOn R φ d) : R.card = d * Fintype.card B := by
  classical
  have hfib : R.card = ∑ b ∈ (Finset.univ : Finset B), (R.filter fun a => φ a = b).card :=
    Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (φ a))
  rw [hfib, Finset.sum_congr rfl (fun b _ => h b), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm]

/-- **Aux A3 (`09:90`, "Every element of `S` lies in a fibre above `phi(S)`").**
For `S` inside the reservoir, `|S| <= d |phi(S)|`.  General. -/
theorem RegularOn.card_le_mul_image {A B : Type*} [DecidableEq B] {R : Finset A}
    {φ : A → B} {d : ℕ} (h : RegularOn R φ d) {S : Finset A} (hS : S ⊆ R) :
    S.card ≤ d * (S.image φ).card := by
  classical
  have hsum : S.card = ∑ b ∈ S.image φ, (S.filter fun a => φ a = b).card :=
    Finset.card_eq_sum_card_image φ S
  calc S.card = ∑ b ∈ S.image φ, (S.filter fun a => φ a = b).card := hsum
    _ ≤ ∑ _b ∈ S.image φ, d := by
        refine Finset.sum_le_sum ?_
        intro b _
        refine le_of_le_of_eq (Finset.card_le_card ?_) (h b)
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨hS ha.1, ha.2⟩
    _ = (S.image φ).card * d := by simp [Finset.sum_const, mul_comm]
    _ = d * (S.image φ).card := by ring

/-- **`eq:regular-density-transfer` (`09:80--84`) on a reservoir.**

"Applying `eq:regular-density-transfer` to the surviving subsets gives
`|E_o|/|J_2| >= |X_o|/|R_G|`, `|E_f|/|J_2| >= |X_f|/|R_f|`" (`09:739--747`).
This is that step with `A` restricted to the reservoir `R`: for `S subseteq R`,
`|S|/|R| <= |phi(S)|/|B|`.  General in both carriers and in `S`. -/
theorem regularOn_density_transfer {A B : Type*} [Fintype B] [DecidableEq B]
    {R : Finset A} {φ : A → B} {d : ℕ} (h : RegularOn R φ d) (hd : 0 < d)
    {S : Finset A} (hS : S ⊆ R) :
    (S.card : ℝ) / (R.card : ℝ) ≤ ((S.image φ).card : ℝ) / (Fintype.card B : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card B) with hB | hB
  · have hR : R.card = 0 := by rw [h.card_eq, hB, Nat.mul_zero]
    have hS0 : S.card = 0 := Nat.le_zero.mp (hR ▸ Finset.card_le_card hS)
    simp [hR, hS0, hB]
  · have hRcard : R.card = d * Fintype.card B := h.card_eq
    have hRpos : 0 < R.card := by rw [hRcard]; exact Nat.mul_pos hd hB
    have hRposR : (0 : ℝ) < (R.card : ℝ) := by exact_mod_cast hRpos
    have hBposR : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast hB
    rw [div_le_div_iff₀ hRposR hBposR]
    have hkey : S.card * Fintype.card B ≤ (S.image φ).card * R.card := by
      have h1 := h.card_le_mul_image hS
      calc S.card * Fintype.card B ≤ (d * (S.image φ).card) * Fintype.card B :=
            Nat.mul_le_mul_right _ h1
        _ = (S.image φ).card * (d * Fintype.card B) := by ring
        _ = (S.image φ).card * R.card := by rw [hRcard]
    exact_mod_cast hkey

/-- **Aux A4 (`09:85--86`/`09:568`, "The product of maps regular of degrees
`d_1, d_2` is regular of degree `d_1 d_2`").**  Stated for two reservoirs, which
is the form `09:821--823` needs when the two duplication quotients
`zeta_{p_o}, zeta_{p_f}` are applied to the two factors of `P_*`.  General. -/
theorem regularOn_prod {A A' B B' : Type*} [DecidableEq B] [DecidableEq B']
    {R : Finset A} {R' : Finset A'} {φ : A → B} {ψ : A' → B'} {d e : ℕ}
    (h : RegularOn R φ d) (h' : RegularOn R' ψ e) :
    RegularOn (R ×ˢ R') (fun y => (φ y.1, ψ y.2)) (d * e) := by
  classical
  intro b
  have hsplit : (R ×ˢ R').filter (fun y => (φ y.1, ψ y.2) = b)
      = (R.filter fun a => φ a = b.1) ×ˢ (R'.filter fun a => ψ a = b.2) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_product, Prod.ext_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [hsplit, Finset.card_product, h b.1, h' b.2]

/-! ## Section 2  The bin evaluation `rho_p` is regular

`09:713--718` reads one tuple coordinate out of the raw column: `rho_p(c) = j(p)`
where `j : [s] -> J_2`.  The frozen per-bin degrees of `09:727--733` all carry
the factor `|J_2|^{s-1}`, which is exactly the fibre of this evaluation.  Rather
than assume that factor, it is proved here: the evaluation at `p` has fibres of
one common size, so it is regular in the banked sense and
`RawLowProfileBody.regular_density_transfer` applies to it directly. -/

/-- **Aux B1.**  All fibres of "evaluate at the bin `p`" have the same size.
Proved by the update bijection, not assumed.  General. -/
theorem evalFibre_card_congr {B : Type*} [Fintype B] [DecidableEq B] {s : ℕ}
    (p : Slot s) (c c' : B) :
    (Finset.univ.filter fun f : Slot s → B => f p = c).card
      = (Finset.univ.filter fun f : Slot s → B => f p = c').card := by
  classical
  refine Finset.card_nbij' (fun f => Function.update f p c') (fun g => Function.update g p c)
    ?_ ?_ ?_ ?_
  · intro f _
    simp
  · intro g _
    simp
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf
    change Function.update (Function.update f p c') p c = f
    rw [Function.update_idem, ← hf, Function.update_eq_self]
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg
    change Function.update (Function.update g p c) p c' = g
    rw [Function.update_idem, ← hg, Function.update_eq_self]

/-- **Aux B2 (the degree is positive).**  The constant tuple witnesses the fibre,
so the evaluation degree is nonzero -- which is what `09:738` insists on
("positive equal-fibre counts").  General. -/
theorem evalFibre_card_pos {B : Type*} [Fintype B] [DecidableEq B] {s : ℕ}
    (p : Slot s) (c : B) :
    0 < (Finset.univ.filter fun f : Slot s → B => f p = c).card := by
  classical
  refine Finset.card_pos.mpr ⟨fun _ => c, ?_⟩
  simp

/-- **Aux B3.**  "Evaluate at the bin `p`" is regular in the **banked** sense, so
`RawLowProfileBody.regular_density_transfer` -- the banked
`eq:regular-density-transfer` -- applies to it verbatim.  General. -/
theorem isFibreBounded_evalAt {B : Type*} [Fintype B] [DecidableEq B] {s : ℕ}
    (p : Slot s) (c₀ : B) :
    RawLowProfileBody.IsFibreBounded (fun f : Slot s → B => f p)
      ((Finset.univ.filter fun f : Slot s → B => f p = c₀).card)
      ((Finset.univ.filter fun f : Slot s → B => f p = c₀).card) := by
  intro b
  rw [evalFibre_card_congr p b c₀]
  exact ⟨le_refl _, le_refl _⟩

/-! ## Section 3  The frozen averaged density is a plain image density

`09:748--756`: "Since `J_2 = [q_2] x C_1`, the two left-hand sides are exactly
the averages `(1/q_2) sum_alpha |O_alpha|/|C_1|`."  That sentence is the bridge
between the transfer conclusion `|E|/|J_2|` and the banked
`meanFibreDensity`, and it is proved here rather than assumed. -/

/-- **Aux C1 (`09:748--756`).**  The banked `meanFibreDensity E` is exactly
`|E|/|J_2|` at `J_2 = [q_2] x C_1`.  No positivity is needed: at a degenerate
width both sides are `0`.  General. -/
theorem meanFibreDensity_eq_card_div {Cone : Type*} [Fintype Cone] [DecidableEq Cone]
    {q₂ : ℕ} (E : Finset (Slot q₂ × Cone)) :
    meanFibreDensity E = (E.card : ℝ) / (Fintype.card (Slot q₂ × Cone) : ℝ) := by
  classical
  have hfibre : ∀ α : Slot q₂, (colFibre E α).card = (E.filter fun x => x.1 = α).card := by
    intro α
    unfold colFibre
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy
  have hsum : ∑ α : Slot q₂, (colFibre E α).card = E.card := by
    have hfw : E.card = ∑ α ∈ (Finset.univ : Finset (Slot q₂)),
        (E.filter fun x => x.1 = α).card :=
      Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ x.1)
    rw [hfw]
    exact Finset.sum_congr rfl (fun α _ => hfibre α)
  have hsumR : ∑ α : Slot q₂, ((colFibre E α).card : ℝ) = (E.card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsum
  unfold meanFibreDensity fibreDensity
  rw [← Finset.sum_div, hsumR, div_mul_div_comm, one_mul]
  congr 1
  have hcard : Fintype.card (Slot q₂ × Cone) = q₂ * Fintype.card Cone := by
    simp [Fintype.card_prod]
  rw [hcard]
  push_cast
  ring

/-- **Aux C2 (the averaged density is a density).**  `meanFibreDensity E <= 1`,
so neither frozen bound of `09:751--755` can be met by an out-of-range value.
General. -/
theorem meanFibreDensity_le_one {Cone : Type*} [Fintype Cone] [DecidableEq Cone]
    {q₂ : ℕ} (E : Finset (Slot q₂ × Cone)) : meanFibreDensity E ≤ 1 := by
  rw [meanFibreDensity_eq_card_div]
  rcases Nat.eq_zero_or_pos (Fintype.card (Slot q₂ × Cone)) with h | h
  · simp [h]
  · have hpos : (0 : ℝ) < (Fintype.card (Slot q₂ × Cone) : ℝ) := by exact_mod_cast h
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_univ E

/-! ## Section 4  "Choose the least surviving representative"

`09:721--723` and `09:764--765` both make a selection from image membership.
One finite selection function serves all three: `iota_o`, `iota_f` and
`sigma_*`. -/

/-- **`09:721--723`/`09:764--765`.**  A section of `phi` over `S`: on a point of
`phi(S)` it returns a preimage inside `S`, and elsewhere an arbitrary point of
the (inhabited) carrier.  This is a finite selection, carrying no protocol and
no bound. -/
noncomputable def imageSection {A B : Type*} (hA : Nonempty A) (S : Finset A) (φ : A → B)
    (b : B) : A :=
  @dite A (∃ a, a ∈ S ∧ φ a = b) (Classical.dec _) (fun h => h.choose) (fun _ => hA.some)

/-- **Aux D1.**  On the image, the selection is a genuine section landing in `S`.
General. -/
theorem imageSection_spec {A B : Type*} {hA : Nonempty A} {S : Finset A} {φ : A → B}
    {b : B} (hb : ∃ a, a ∈ S ∧ φ a = b) :
    imageSection hA S φ b ∈ S ∧ φ (imageSection hA S φ b) = b := by
  unfold imageSection
  rw [dif_pos hb]
  exact hb.choose_spec

/-- **Aux D2.**  The membership half, phrased at `Finset.image` -- the form
`iotaOrd_mem`, `iotaFor_mem` and `sigmaStar_mem` consume.  General. -/
theorem imageSection_mem {A B : Type*} [DecidableEq B] {hA : Nonempty A} {S : Finset A}
    {φ : A → B} {b : B} (hb : b ∈ S.image φ) : imageSection hA S φ b ∈ S :=
  (imageSection_spec (Finset.mem_image.mp hb)).1

/-- **Aux D3.**  The section half, phrased at `Finset.image` -- the form
`iotaOrd_section`, `iotaFor_section` and `sigmaStar_section` consume.
General. -/
theorem imageSection_apply {A B : Type*} [DecidableEq B] {hA : Nonempty A} {S : Finset A}
    {φ : A → B} {b : B} (hb : b ∈ S.image φ) : φ (imageSection hA S φ b) = b :=
  (imageSection_spec (Finset.mem_image.mp hb)).2

/-! ## Section 5  The construction's own `lambda_T`

`09:367--371`: `Y_T = bigsqcup_{p in [s]} Y_{T,p}`, `|Y_{T,p}| = m_T`,
`lambda_T = |Y_T|/|Y|`.  The realization lemma is stated at **this** number and
not at a fresh real, which is what stops the two frozen gates from being
vacuously dischargeable. -/

/-- **`09:367--371`.**  `lambda_T = |Y_T|/|Y|` at `Y_T = bigcup_{p in [s]}
Y_{T,p}` and `Y = Cols(N)`.  The banked `ScaleAlignOpening.lambdaTemplate` is
*applied*, never restated. -/
noncomputable def templateDensity {Cl : Type*} [Fintype Cl] [DecidableEq Cl] {s : ℕ}
    (YT : Slot s → Finset Cl) : ℝ :=
  ScaleAlignOpening.lambdaTemplate (Finset.univ.biUnion YT)

/-- **Aux E1.**  The defining quotient, exposed so consumers need not unfold two
layers.  General. -/
theorem templateDensity_eq {Cl : Type*} [Fintype Cl] [DecidableEq Cl] {s : ℕ}
    (YT : Slot s → Finset Cl) :
    templateDensity YT = ((Finset.univ.biUnion YT).card : ℝ) / (Fintype.card Cl : ℝ) := rfl

/-- **Aux E2 (`09:367--369`, the disjoint union bites).**  On disjoint bins of
common size `m_T` the frozen `lambda_T` is exactly `s m_T/|Y|`.  This is the
check that `templateDensity` is the frozen constant and not an unrelated ratio.
General. -/
theorem templateDensity_eq_of_disjoint {Cl : Type*} [Fintype Cl] [DecidableEq Cl] {s mT : ℕ}
    (YT : Slot s → Finset Cl) (hdisj : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (hcard : ∀ p : Slot s, (YT p).card = mT) :
    templateDensity YT = ((s : ℝ) * (mT : ℝ)) / (Fintype.card Cl : ℝ) := by
  classical
  have hbi : (Finset.univ.biUnion YT).card = s * mT := by
    rw [Finset.card_biUnion (fun p _ p' _ h => hdisj p p' h),
      Finset.sum_congr rfl (fun p _ => hcard p), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [templateDensity_eq, hbi]
  push_cast
  ring

/-! ## Section 6  `lem:terminal-state-realization` (`09:658--833`)

The ambient data are explicit binders, exactly as the frozen statement carries
them: the lemma is a statement *about* the surviving rectangle at a specified
frontier node, relative to a construction it does not build.  Hypotheses
`(a)`--`(c)` are the frozen clauses; the remaining binders are the construction
facts the frozen proof names by their own anchors. -/

variable {Rw Cl Om Cone Ltwo Rone : Type*}
variable [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  [Fintype Cone] [DecidableEq Cone] [Fintype Ltwo] [DecidableEq Ltwo]

set_option maxHeartbeats 1000000 in
-- The realization discharges forty-five fields in one elaboration, twenty-six of them
-- proved on the spot; the default heartbeat budget does not cover a declaration of
-- that size, and splitting it would break the one-frozen-lemma-one-declaration rule.
/-- **`lem:terminal-state-realization` (`09:658--704`), transcribed and proved.**

"Let `P` be the completed scale-alignment protocol under analysis, let `v` be a
specified final Alice-frontier node of its routed execution, and let
`Z = extract(U, X_Z, Y_Z)` be the surviving rectangle at `v`.  Fix distinct
outer coordinates `i` and `j`.  Assume (a), (b), (c).  Then `Z` is an
`(eps, delta')`-two-stream terminal state in the sense of
`def:two-stream-state`."

The conclusion is the **banked** structure at the construction's own
`lambda_T = templateDensity YT` (`09:367--371`) and at the frozen tuple-selector
`rho_p(c) = j(p)` (`09:713--718`); `eps` and `delta'` are the only genuine
universals of the frozen statement.  All forty-five fields are discharged;
twenty-six are proved from the hypotheses rather than assumed.

The frozen conclusion is an assertion *about* `Z`, so the deliverable is
`Prop`-valued; `terminalStateRealization` below is the witnessing record.

**Why the trivial witness fails the existential.**  A `TwoStreamState` record
cannot be produced by picking empty or default data: `foreign_density` with
`delta' > 0` forces the foreign row stream to be inhabited (banked
`foreign_stream_nonempty`), `Kord_density` with `eps < 1` forces the clause-(iv)
column set to be inhabited (`kord_witness_is_nonempty`), `uniform_transfer` must
return a nonempty `Q` (banked `uniform_transfer_witness_is_nonempty`), and
`selector_gate` fails outright at an unscheduled `eps_2` (the banked
`TwoStreamState.terminalSelectorData_needs_eps2`, consumed by pin).  So the
conclusion is not dischargeable by a default record, and the content of this
declaration is the construction of the real one. -/
theorem terminal_state_realization
    {q s q₂ mT dT dOrd dFor : ℕ}
    {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool} {cFam : Ltwo → Slot q₂ → Rone}
    {Stwo : Ltwo → Slot q₂ × Cone → Bool}
    {RG RSig RD Rf : Finset Rw} {omg : Rw → Om} {tup : Om → Slot s → Slot q₂ × Cone}
    {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
    {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)}
    {eps2 xT ε δ' : ℝ}
    (i j : Slot q) (pOrd pFor : Slot s) (Pstar : Finset (Cl × Cl))
    (Rbin : Slot s → Finset Ltwo) (selRow : Slot s × Ltwo → (Slot q → Cl))
    -- `09:666--667`: "Fix **distinct** outer coordinates `i` and `j`."
    (hOuter : i ≠ j)
    -- `09:367--369`: `Y_T = bigsqcup_p Y_{T,p}` with `|Y_{T,p}| = m_T`.
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    -- `09:565--568`/`09:765--766`: `zeta_p` forgets the **uniform** template-row
    -- duplication labels, so it is regular of degree `d_T`.
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    -- the Stage-2 value equation `S_2(z, (alpha, gamma)) = M(gamma, c^{(z)}(alpha))`.
    (hStwo : ∀ (l : Ltwo) (e : Slot q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    -- `09:788--795` composed with `eq:raw-stage4-template-value` (`07:558`): on a
    -- template column of bin `p` the physical entry is the template-row value.
    (hNval : ∀ (p : Slot s) (y : Cl), y ∈ YT p → ∀ r : Rw,
      Nmat r y = Stwo (zeta p y) (tup (omg r) p))
    -- (a) `09:671--682`.
    (hProtected : Rf = RSig ∨ Rf = RD)
    (hEpsNonneg : 0 ≤ ε) (hEpsLtOne : ε < 1) (hDeltaPos : 0 < δ') (hDeltaLeOne : δ' ≤ 1)
    (hOrdDensity : 1 - ε ≤ ((streamRows XZ i RG).card : ℝ) / (RG.card : ℝ))
    (hForDensity : δ' ≤ ((streamRows XZ j Rf).card : ℝ) / (Rf.card : ℝ))
    -- (c) first clause `09:695--696` at the frozen degrees `09:727--733`.
    (hRegG : RegularOn RG (fun r => tup (omg r)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : RegularOn Rf (fun r => tup (omg r) pFor) dFor) (hdFor : 0 < dFor)
    -- (b) `09:683--694`.
    (hPstarTyped : ∀ y ∈ Pstar, y.1 ∈ YT pOrd ∧ y.2 ∈ YT pFor)
    (hPstarProj : ∀ y ∈ Pstar, ∃ w ∈ YZ, w i = y.1 ∧ w j = y.2)
    (hPairDensity : aMin rhoPair (templateDensity YT) ≤ (Pstar.card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin p).card)
    -- `09:628--632`/`09:814--816`: the Stage-3 row section and its distinguished bin.
    (hSelRowMem : ∀ p : Slot s, ∀ l ∈ Rbin p, selRow (p, l) ∈ YZ)
    (hSelRowTyped : ∀ p : Slot s, ∀ l ∈ Rbin p,
      selRow (p, l) i ∈ YT p ∧ zeta p (selRow (p, l) i) = l)
    (hSelDist : ∀ l ∈ Rbin pOrd, ∃ y ∈ Pstar, selRow (pOrd, l) i = y.1)
    -- (c) remainder `09:697--700`.
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2) :
    Nonempty (TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD omg
      (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT ε δ') := by
  classical
  -- ## Positivity of the widths and of the block constants.
  have hspos : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) pOrd.isLt
  have hτpos : 0 < tauZero s xT := tauZero_pos hspos hxT
  have hone2 : (0 : ℝ) < (1 + eps2) ^ 2 := by positivity
  have hone2ge : (1 : ℝ) ≤ (1 + eps2) ^ 2 := by nlinarith
  have haMinGap : 0 < aMin rhoPair (templateDensity YT) - tauZero s xT := by
    rw [le_div_iff₀ hone2] at hSelectorGate
    nlinarith
  have haMinPos : 0 < aMin rhoPair (templateDensity YT) := by linarith
  -- ## The two row streams are inhabited (`09:488` from `09:674--681`).
  have hOrdPos : (0 : ℝ) < 1 - ε := by linarith
  have hXoNe : (streamRows XZ i RG).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    rw [hcon] at hOrdDensity
    simp at hOrdDensity
    linarith
  have hXfNe : (streamRows XZ j Rf).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    rw [hcon] at hForDensity
    simp at hForDensity
    linarith
  obtain ⟨x0, hx0⟩ := hXoNe
  obtain ⟨x1, hx1⟩ := hXfNe
  have hneRw : Nonempty (Slot q × Rw) := ⟨x0⟩
  have hXZne : XZ.Nonempty := ⟨x0, (mem_streamRows.mp hx0).1⟩
  -- ## `P_*` is inhabited, hence so are `Cl` and `Y_Z`.
  have hPstarNe : Pstar.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    rw [hcon] at hPairDensity
    simp at hPairDensity
    linarith
  obtain ⟨y0, hy0⟩ := hPstarNe
  have hneCl : Nonempty Cl := ⟨y0.1⟩
  have hneFun : Nonempty (Slot q → Cl) := ⟨fun _ => y0.1⟩
  obtain ⟨w0, hw0, -⟩ := hPstarProj y0 hy0
  have hYZne : YZ.Nonempty := ⟨w0, hw0⟩
  -- ## `m_T` and `d_T` are positive (`09:369` against `09:565--568`).
  have hmTpos : 0 < mT := by
    have : y0.1 ∈ YT pOrd := (hPstarTyped y0 hy0).1
    have hne : (YT pOrd).Nonempty := ⟨y0.1, this⟩
    rw [← htemplate_card pOrd]
    exact Finset.card_pos.mpr hne
  have hmTeq : mT = dT * Fintype.card Ltwo := by
    rw [← htemplate_card pOrd]
    exact (htemplate_regular pOrd).card_eq
  have hdTpos : 0 < dT := by
    rcases Nat.eq_zero_or_pos dT with h | h
    · exfalso; rw [h, Nat.zero_mul] at hmTeq; omega
    · exact h
  have hmTposR : (0 : ℝ) < (mT : ℝ) := by exact_mod_cast hmTpos
  -- ## `K_ord` and the two bin images (`09:804--812`, `09:719--720`).
  set Kord : Finset (Slot s → Slot q₂ × Cone) :=
    (streamRows XZ i RG).image (fun x => tup (omg x.2)) with hKordDef
  have hsndOrd : ((streamRows XZ i RG).image Prod.snd) ⊆ RG := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    exact (mem_streamRows.mp hx).2.2
  have hsndFor : ((streamRows XZ j Rf).image Prod.snd) ⊆ Rf := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    exact (mem_streamRows.mp hx).2.2
  have hsndCardOrd : ((streamRows XZ i RG).image Prod.snd).card = (streamRows XZ i RG).card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_streamRows] at ha hb
    exact Prod.ext (ha.2.1.trans hb.2.1.symm) hab
  have hsndCardFor : ((streamRows XZ j Rf).image Prod.snd).card = (streamRows XZ j Rf).card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_streamRows] at ha hb
    exact Prod.ext (ha.2.1.trans hb.2.1.symm) hab
  have hKordImg : ((streamRows XZ i RG).image Prod.snd).image (fun r => tup (omg r)) = Kord := by
    rw [hKordDef, Finset.image_image]
    rfl
  -- The frozen `|Cols(S_2)|^s` is the cardinality of the tuple carrier.
  have hcardTuple : Fintype.card (Slot s → Slot q₂ × Cone)
      = (Fintype.card (Slot q₂ × Cone)) ^ s := by
    simp
  have hcardTupleR : ((Fintype.card (Slot s → Slot q₂ × Cone) : ℕ) : ℝ)
      = (Fintype.card (Slot q₂ × Cone) : ℝ) ^ s := by
    rw [hcardTuple]
    push_cast
    ring
  -- ## Step 1: the tuple-level transfer (`09:739--747` at `09:804`).
  have hKordDensity :
      1 - ε ≤ (Kord.card : ℝ) / (Fintype.card (Slot q₂ × Cone) : ℝ) ^ s := by
    have htr := regularOn_density_transfer hRegG hdOrd hsndOrd
    rw [hKordImg, hsndCardOrd, hcardTupleR] at htr
    exact le_trans hOrdDensity htr
  -- ## Step 2: the bin-evaluation transfer (`09:748--756`).
  have hc0 : Slot q₂ × Cone := tup (omg x0.2) pOrd
  have hTupPos : 0 < Fintype.card (Slot s → Slot q₂ × Cone) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => hc0⟩
  have hEvalOrd : meanFibreDensity (streamImage omg (fun p o => tup o p) pOrd XZ i RG)
      = (Kord.image (fun k => k pOrd)).card / (Fintype.card (Slot q₂ × Cone) : ℝ) := by
    have hEq : streamImage omg (fun p o => tup o p) pOrd XZ i RG
        = Kord.image (fun k => k pOrd) := by
      rw [hKordDef, Finset.image_image]
      rfl
    rw [hEq, meanFibreDensity_eq_card_div]
  have hOrdMean : 1 - ε ≤ meanFibreDensity (streamImage omg (fun p o => tup o p) pOrd XZ i RG) := by
    have hstep := RawLowProfileBody.regular_density_transfer
      (isFibreBounded_evalAt (B := Slot q₂ × Cone) pOrd hc0) (evalFibre_card_pos pOrd hc0)
      hTupPos Kord
    rw [hEvalOrd]
    refine le_trans ?_ hstep
    rw [hcardTupleR]
    exact hKordDensity
  -- ## Step 3: the foreign stream transfers in **one** step, at the frozen per-bin degree
  -- `d_Sigma = w_Sigma |J_2|^{s-1}` / `d_D = w_D` of `09:730--733`.
  have hForMean : δ' ≤ meanFibreDensity (streamImage omg (fun p o => tup o p) pFor XZ j Rf) := by
    have htr := regularOn_density_transfer hRegF hdFor hsndFor
    rw [hsndCardFor] at htr
    have hEq : ((streamRows XZ j Rf).image Prod.snd).image (fun r => tup (omg r) pFor)
        = streamImage omg (fun p o => tup o p) pFor XZ j Rf := by
      rw [Finset.image_image]
      rfl
    rw [hEq] at htr
    rw [meanFibreDensity_eq_card_div]
    exact le_trans hForDensity htr
  -- ## The three least-representative selections (`09:721--723`, `09:764--765`).
  set iotaO : Slot q₂ × Cone → Slot q × Rw :=
    imageSection hneRw (streamRows XZ i RG) (fun x => tup (omg x.2) pOrd) with hiotaODef
  set iotaF : Slot q₂ × Cone → Slot q × Rw :=
    imageSection hneRw (streamRows XZ j Rf) (fun x => tup (omg x.2) pFor) with hiotaFDef
  set sigmaS : Cl × Cl → (Slot q → Cl) :=
    imageSection hneFun YZ (fun w => (w i, w j)) with hsigmaSDef
  set selC : (Slot s → Slot q₂ × Cone) → Slot q × Rw :=
    imageSection hneRw (streamRows XZ i RG) (fun x => tup (omg x.2)) with hselCDef
  have hiotaO_mem : ∀ e ∈ streamImage omg (fun p o => tup o p) pOrd XZ i RG,
      iotaO e ∈ streamRows XZ i RG := by
    intro e he
    exact imageSection_mem (hA := hneRw) he
  have hiotaO_sec : ∀ e ∈ streamImage omg (fun p o => tup o p) pOrd XZ i RG,
      tup (omg (iotaO e).2) pOrd = e := by
    intro e he
    exact imageSection_apply (hA := hneRw) he
  have hiotaF_mem : ∀ e ∈ streamImage omg (fun p o => tup o p) pFor XZ j Rf,
      iotaF e ∈ streamRows XZ j Rf := by
    intro e he
    exact imageSection_mem (hA := hneRw) he
  have hiotaF_sec : ∀ e ∈ streamImage omg (fun p o => tup o p) pFor XZ j Rf,
      tup (omg (iotaF e).2) pFor = e := by
    intro e he
    exact imageSection_apply (hA := hneRw) he
  have hsigmaMem : ∀ y ∈ Pstar, sigmaS y ∈ YZ := by
    intro y hy
    obtain ⟨w, hw, hw1, hw2⟩ := hPstarProj y hy
    refine imageSection_mem (hA := hneFun) (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
    rw [hw1, hw2]
  have hsigmaSec : ∀ y ∈ Pstar, sigmaS y i = y.1 ∧ sigmaS y j = y.2 := by
    intro y hy
    obtain ⟨w, hw, hw1, hw2⟩ := hPstarProj y hy
    have hmem : y ∈ YZ.image (fun w => (w i, w j)) :=
      Finset.mem_image.mpr ⟨w, hw, by rw [hw1, hw2]⟩
    have := imageSection_apply (hA := hneFun) hmem
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hselC_mem : ∀ k ∈ Kord, selC k ∈ streamRows XZ i RG := by
    intro k hk
    rw [hKordDef] at hk
    exact imageSection_mem (hA := hneRw) hk
  have hselC_sec : ∀ k ∈ Kord, tup (omg (selC k).2) = k := by
    intro k hk
    rw [hKordDef] at hk
    exact imageSection_apply (hA := hneRw) hk
  -- ## The physical entry equations (`09:768--802`).
  have hentryOrd : ∀ e ∈ streamImage omg (fun p o => tup o p) pOrd XZ i RG, ∀ y ∈ Pstar,
      interlaceFun Nmat q (iotaO e) (sigmaS y) = Mmat e.2 (cFam (zeta pOrd y.1) e.1) := by
    intro e he y hy
    have hrow := mem_streamRows.mp (hiotaO_mem e he)
    have hval := hNval pOrd y.1 (hPstarTyped y hy).1 (iotaO e).2
    rw [interlaceFun, hrow.2.1, (hsigmaSec y hy).1, hval, hiotaO_sec e he, hStwo]
  have hentryFor : ∀ e ∈ streamImage omg (fun p o => tup o p) pFor XZ j Rf, ∀ y ∈ Pstar,
      interlaceFun Nmat q (iotaF e) (sigmaS y) = Mmat e.2 (cFam (zeta pFor y.2) e.1) := by
    intro e he y hy
    have hrow := mem_streamRows.mp (hiotaF_mem e he)
    have hval := hNval pFor y.2 (hPstarTyped y hy).2 (iotaF e).2
    rw [interlaceFun, hrow.2.1, (hsigmaSec y hy).2, hval, hiotaF_sec e he, hStwo]
  -- ## The Stage-3 selector restriction (`09:804--817`).
  have hselRowInj : ∀ p p' : Slot s, ∀ l ∈ Rbin p, ∀ l' ∈ Rbin p',
      selRow (p, l) = selRow (p', l') → (p, l) = (p', l') := by
    intro p p' l hl l' hl' heq
    obtain ⟨hmem, hz⟩ := hSelRowTyped p l hl
    obtain ⟨hmem', hz'⟩ := hSelRowTyped p' l' hl'
    have hsame : selRow (p, l) i = selRow (p', l') i := by rw [heq]
    have hpp : p = p' := by
      by_contra hcon
      have := Finset.disjoint_left.mp (hbins p p' hcon) hmem
      exact this (hsame ▸ hmem')
    subst hpp
    have : l = l' := by rw [← hz, ← hz', hsame]
    subst this
    rfl
  have hselCInj : ∀ k ∈ Kord, ∀ k' ∈ Kord, selC k = selC k' → k = k' := by
    intro k hk k' hk' heq
    rw [← hselC_sec k hk, ← hselC_sec k' hk', heq]
  have hselEntry : ∀ p : Slot s, ∀ l ∈ Rbin p, ∀ k ∈ Kord,
      interlaceFun Stwo s (p, l) k = interlaceFun Nmat q (selC k) (selRow (p, l)) := by
    intro p l hl k hk
    obtain ⟨hmem, hz⟩ := hSelRowTyped p l hl
    have hrow := mem_streamRows.mp (hselC_mem k hk)
    rw [interlaceFun, interlaceFun, hrow.2.1, hNval p (selRow (p, l) i) hmem (selC k).2,
      hselC_sec k hk, hz]
  -- ## Clause (v) (`09:819--828`).
  have hUniform : ∀ P' ⊆ Pstar,
      ((Pstar \ P').card : ℝ) / (mT : ℝ) ^ 2 < tauZero s xT →
        ∃ Q : Finset (Ltwo × Ltwo),
          (∀ z ∈ Q, ∃ y ∈ P', zeta pOrd y.1 = z.1 ∧ zeta pFor y.2 = z.2) ∧
          (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2
            ≤ (Q.card : ℝ) / (Fintype.card Ltwo : ℝ) ^ 2 := by
    intro P' hsub hloss
    refine ⟨P'.image (fun y => (zeta pOrd y.1, zeta pFor y.2)), ?_, ?_⟩
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
      exact ⟨y, hy, by rw [← hyz], by rw [← hyz]⟩
    · -- physical density of `P'` in the fixed-bin ambient carrier
      have hcards : P'.card + (Pstar \ P').card = Pstar.card := by
        rw [add_comm]
        exact Finset.card_sdiff_add_card_eq_card hsub
      have hcardsR : (P'.card : ℝ) + ((Pstar \ P').card : ℝ) = (Pstar.card : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcards
      have hP'dens : aMin rhoPair (templateDensity YT) - tauZero s xT
          ≤ (P'.card : ℝ) / (mT : ℝ) ^ 2 := by
        have hsq : (0 : ℝ) < (mT : ℝ) ^ 2 := by positivity
        rw [div_lt_iff₀ hsq] at hloss
        rw [le_div_iff₀ hsq]
        rw [le_div_iff₀ hsq] at hPairDensity
        linarith
      -- forgetting the uniform labels does not decrease indexed density
      have hprodReg : RegularOn ((YT pOrd) ×ˢ (YT pFor))
          (fun y : Cl × Cl => (zeta pOrd y.1, zeta pFor y.2)) (dT * dT) :=
        regularOn_prod (htemplate_regular pOrd) (htemplate_regular pFor)
      have hP'sub : P' ⊆ (YT pOrd) ×ˢ (YT pFor) := by
        intro y hy
        obtain ⟨h1, h2⟩ := hPstarTyped y (hsub hy)
        exact Finset.mem_product.mpr ⟨h1, h2⟩
      have htr := regularOn_density_transfer hprodReg (Nat.mul_pos hdTpos hdTpos) hP'sub
      have hprodCard : ((YT pOrd) ×ˢ (YT pFor)).card = mT * mT := by
        rw [Finset.card_product, htemplate_card pOrd, htemplate_card pFor]
      have hLcard : (Fintype.card (Ltwo × Ltwo) : ℝ) = (Fintype.card Ltwo : ℝ) ^ 2 := by
        rw [Fintype.card_prod]
        push_cast
        ring
      rw [hprodCard, hLcard] at htr
      have hmm : ((mT * mT : ℕ) : ℝ) = (mT : ℝ) ^ 2 := by push_cast; ring
      rw [hmm] at htr
      have hchain : (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2
          ≤ aMin rhoPair (templateDensity YT) - tauZero s xT := by
        rw [div_le_iff₀ hone2]
        nlinarith
      exact le_trans hchain (le_trans hP'dens htr)
  -- ## All forty-five fields.
  refine ⟨?_⟩
  exact
    { rows_nonempty := hXZne
      cols_nonempty := hYZne
      eps_nonneg := hEpsNonneg
      eps_lt_one := hEpsLtOne
      delta_pos := hDeltaPos
      delta_le_one := hDeltaLeOne
      iOrd := i
      iFor := j
      outer_distinct := hOuter
      Rfor := Rf
      protected_reservoir := hProtected
      pOrd := pOrd
      pFor := pFor
      iotaOrd := iotaO
      iotaFor := iotaF
      iotaOrd_mem := hiotaO_mem
      iotaOrd_section := hiotaO_sec
      iotaFor_mem := hiotaF_mem
      iotaFor_section := hiotaF_sec
      ordinary_density := hOrdMean
      foreign_density := hForMean
      Pstar := Pstar
      Pstar_typed := hPstarTyped
      sigmaStar := sigmaS
      sigmaStar_mem := hsigmaMem
      sigmaStar_section := hsigmaSec
      template_card := htemplate_card
      physical_pair_density := hPairDensity
      template_regular := fun p z => htemplate_regular p z
      ordinary_entry := hentryOrd
      foreign_entry := hentryFor
      Rbin := Rbin
      Kord := Kord
      selRow := selRow
      selCol := selC
      selRow_mem := hSelRowMem
      selCol_mem := hselC_mem
      selRow_inj := hselRowInj
      selCol_inj := hselCInj
      selector_entry := hselEntry
      Kord_density := hKordDensity
      Rbin_card := hRbinCard
      sel_distinguished := hSelDist
      uniform_transfer := hUniform
      selector_gate := hSelectorGate }

/-! ## Section 7  Statement poles

A green build sees neither of these. -/

/-- **Statement pole (the clause-(iv) column set is not the trivial witness).**
The frozen `|K_ord|/|Cols(S_2)|^s >= 1 - eps` with `eps < 1` forces `K_ord` to be
**nonempty**, so `K_ord = empty` -- the one candidate that costs nothing to
produce -- is refuted, and the Stage-3 restriction of clause (iv) is not
vacuously satisfiable.  General. -/
theorem kord_witness_is_nonempty {Cone : Type*} [Fintype Cone]
    {s q₂ : ℕ} {ε : ℝ} (K : Finset (Slot s → Slot q₂ × Cone)) (hε : ε < 1)
    (h : 1 - ε ≤ (K.card : ℝ) / (Fintype.card (Slot q₂ × Cone) : ℝ) ^ s) :
    K.Nonempty := by
  rcases Finset.eq_empty_or_nonempty K with hK | hK
  · exfalso
    rw [hK] at h
    simp only [Finset.card_empty, Nat.cast_zero, zero_div] at h
    linarith
  · exact hK

/-- **Statement pole (the foreign hypothesis sits at the level `09:737--738`
supports, and could not sit higher).**

The frozen diagonal degree is `d_D = w_D`, with **no** `|J_2|^{s-1}` factor,
because "in the diagonal reservoir the map is bijective before its repetition
label is added": the diagonal reservoir carries only the *constant* tuples.  The
two-element model below is exactly that shape at `s = 2`.  Its **per-bin**
readout is regular of degree `1`, so the hypothesis this module actually makes is
satisfiable; its **tuple** readout is regular of *no* positive degree, because
the fibre over a non-constant tuple is empty.  So stating the foreign-stream
hypothesis at the tuple level -- which would have made the ordinary and foreign
sides look pleasingly symmetric -- would have emptied the `R_f = R_D` branch of
`09:672` while typechecking perfectly. -/
theorem diagonalTupleReadout_not_regular :
    (∀ p : Slot 2, RegularOn (Finset.univ : Finset Bool)
        (fun b : Bool => (fun _ : Slot 2 => b) p) 1)
      ∧ ∀ d : ℕ, ¬ (0 < d ∧ RegularOn (Finset.univ : Finset Bool)
        (fun b : Bool => (fun _ : Slot 2 => b)) d) := by
  refine ⟨?_, ?_⟩
  · unfold RegularOn
    decide
  · rintro d ⟨hd, h⟩
    have h0 := h ![true, false]
    have hz : (Finset.univ.filter
        fun b : Bool => (fun _ : Slot 2 => b) = ![true, false]).card = 0 := by decide
    rw [hz] at h0
    omega

/-- **The witnessing record of `09:702--703`.**  "All data in
`def:two-stream-state` have now been realized" (`09:830--831`): the frozen
proof's closing sentence, read as the record itself rather than as its
existence.  Definitionally the chosen witness of `terminal_state_realization`;
noncomputable because the frozen "least representative" choices are made by
classical selection. -/
noncomputable def terminalStateRealization
    {q s q₂ mT dT dOrd dFor : ℕ}
    {Nmat : Rw → Cl → Bool} {Mmat : Cone → Rone → Bool} {cFam : Ltwo → Slot q₂ → Rone}
    {Stwo : Ltwo → Slot q₂ × Cone → Bool}
    {RG RSig RD Rf : Finset Rw} {omg : Rw → Om} {tup : Om → Slot s → Slot q₂ × Cone}
    {YT : Slot s → Finset Cl} {zeta : Slot s → Cl → Ltwo}
    {XZ : Finset (Slot q × Rw)} {YZ : Finset (Slot q → Cl)}
    {eps2 xT ε δ' : ℝ}
    (i j : Slot q) (pOrd pFor : Slot s) (Pstar : Finset (Cl × Cl))
    (Rbin : Slot s → Finset Ltwo) (selRow : Slot s × Ltwo → (Slot q → Cl))
    (hOuter : i ≠ j)
    (hbins : ∀ p p' : Slot s, p ≠ p' → Disjoint (YT p) (YT p'))
    (htemplate_card : ∀ p : Slot s, (YT p).card = mT)
    (htemplate_regular : ∀ p : Slot s, RegularOn (YT p) (zeta p) dT)
    (hStwo : ∀ (l : Ltwo) (e : Slot q₂ × Cone), Stwo l e = Mmat e.2 (cFam l e.1))
    (hNval : ∀ (p : Slot s) (y : Cl), y ∈ YT p → ∀ r : Rw,
      Nmat r y = Stwo (zeta p y) (tup (omg r) p))
    (hProtected : Rf = RSig ∨ Rf = RD)
    (hEpsNonneg : 0 ≤ ε) (hEpsLtOne : ε < 1) (hDeltaPos : 0 < δ') (hDeltaLeOne : δ' ≤ 1)
    (hOrdDensity : 1 - ε ≤ ((streamRows XZ i RG).card : ℝ) / (RG.card : ℝ))
    (hForDensity : δ' ≤ ((streamRows XZ j Rf).card : ℝ) / (Rf.card : ℝ))
    (hRegG : RegularOn RG (fun r => tup (omg r)) dOrd) (hdOrd : 0 < dOrd)
    (hRegF : RegularOn Rf (fun r => tup (omg r) pFor) dFor) (hdFor : 0 < dFor)
    (hPstarTyped : ∀ y ∈ Pstar, y.1 ∈ YT pOrd ∧ y.2 ∈ YT pFor)
    (hPstarProj : ∀ y ∈ Pstar, ∃ w ∈ YZ, w i = y.1 ∧ w j = y.2)
    (hPairDensity : aMin rhoPair (templateDensity YT) ≤ (Pstar.card : ℝ) / (mT : ℝ) ^ 2)
    (hRbinCard : ∀ p : Slot s, ⌈tauZero s xT * (Fintype.card Ltwo : ℝ)⌉₊ ≤ (Rbin p).card)
    (hSelRowMem : ∀ p : Slot s, ∀ l ∈ Rbin p, selRow (p, l) ∈ YZ)
    (hSelRowTyped : ∀ p : Slot s, ∀ l ∈ Rbin p,
      selRow (p, l) i ∈ YT p ∧ zeta p (selRow (p, l) i) = l)
    (hSelDist : ∀ l ∈ Rbin pOrd, ∃ y ∈ Pstar, selRow (pOrd, l) i = y.1)
    (hEps2 : 0 ≤ eps2) (hxT : 0 < xT)
    (hSelectorGate :
      49 / 64 ≤ (aMin rhoPair (templateDensity YT) - tauZero s xT) / (1 + eps2) ^ 2) :
    TwoStreamState q s q₂ mT dT Nmat Mmat cFam Stwo RG RSig RD omg
      (fun p o => tup o p) YT zeta XZ YZ (templateDensity YT) eps2 xT ε δ' :=
  (terminal_state_realization i j pOrd pFor Pstar Rbin selRow hOuter hbins htemplate_card
    htemplate_regular hStwo hNval hProtected hEpsNonneg hEpsLtOne hDeltaPos hDeltaLeOne
    hOrdDensity hForDensity hRegG hdOrd hRegF hdFor hPstarTyped hPstarProj hPairDensity
    hRbinCard hSelRowMem hSelRowTyped hSelDist hEps2 hxT hSelectorGate).some

/-! ## Section 8  The inherited **smoke** carriers (`s = 1`) -- NOT the legality witness

The carriers are the banked `TwoStreamState` probe carriers, consumed by pin:
`q = 2`, `s = 1`, `q_2 = 2`, `m_T = 12`, `d_T = 6`, reals `eps_2 = 1/100`,
`x_T = 1/200`, `eps = 1/4`, `delta' = 1/2`, and `lambda_T` now **computed** from
the bins rather than posited -- `probeTemplateDensity` shows the construction's
own `templateDensity` is exactly the `1` the banked probe carries, so the
realization lemma is fired at the same numerals `probeState_is_legal` certifies.

**This section is a smoke check only, and says so in every name.**  Two of its
values sit outside the frozen construction and it must therefore never be read
as a legality certificate:

* `s = 1` is **not a schedule value**.  `07:445--447` fixes `s = 2^{w_s}` with
  `1 <= w_s <= b_2` (restated `07:500--501`), so `s >= 2` wherever `s` occurs.
  At `s = 1` the bin carrier `Slot 1` is a `Subsingleton`, so `hbins` is
  discharged by `Subsingleton.elim`, `p_o = p_f` is forced, and the Stage-3
  selector `<S_2>^s` collapses to `S_2`;
* `lambda_T = 1` is **construction-impossible**.  `Y = Cols(N) = Rows(A)` carries
  the positive `{src-v} x W_V x [u_V]` and `{src-b} x W_B x [u_B]` blocks of
  `eq:protected-labelled-carriers` (`08:82--92`) at row masses `2^{-22}` each
  (`08:126--129`), so `lambda_T < 1` strictly.

The schedule-legal witness that LANE-GATE 3 actually rests on is **Section 9**,
at `s = 2`, `lambda_T = 9/10 < 1`, and **both** branches of `09:672`.  What this
section still contributes is genuine: it exercises the lemma at a second,
independent parameter point, and its readouts below are tight.

Nondegeneracy is checked, not asserted:

* both hypothesis (a) densities are met **with equality** (`3/4 = 1 - eps` and
  `1/2 = delta'`), so neither is slack;
* the foreign stream is routed from the genuine selector reservoir `R_Sigma`,
  at an outer coordinate **distinct** from the ordinary one;
* the two tuple readouts are regular of positive degree `1` on their reservoirs,
  which is the frozen "positive equal-fibre counts" and not mere surjectivity;
* `|P_*| = 143` of `m_T^2 = 144` is the least cardinality meeting
  `eq:terminal-physical-pair-density` at `a_min = 99/100`;
* the derived `K_ord` is a **proper**, nonempty subset of the tuple carrier
  (`probeRealization_kord_is_proper`), so clause (iv) is not discharged by the
  whole carrier;
* `tau_0` sits at the gate boundary `1/100`, so the derived clause (v) is
  exercised at proper subsets of `P_*`.

Tier 2, not a schedule instance: `m_T = 12` is far below the `06:703` floor and
`q_2 = 2` below `eq:stage2-structural-gates`; **no route parameter may be read
out of it**. -/

/-- The probe's raw-column tuple readout: at `s = 1` the raw column carries a
single `J_2` entry, so `j : [1] -> J_2` is the constant tuple.  The frozen
`rho_p(c) = j(p)` (`09:713--718`) then reduces to the banked `probeRho`. -/
def probeTup : ProbeOm → Slot 1 → Slot 2 × ProbeCone := fun o _ => o

/-- **The frozen selector at the probe is the banked one.**  `rho_p(c) = j(p)`
at `probeTup` is definitionally `probeRho`, so the realization lemma concludes a
state at exactly the banked probe's parameters. -/
theorem probeRho_eq : (fun p o => probeTup o p) = probeRho := rfl

/-- **The construction's own `lambda_T` at the probe.**  The single template bin
is the whole column carrier, so `lambda_T = |Y_T|/|Y| = 12/12 = 1` -- the number
the banked `probeState` carries, now **computed** from the bins rather than
supplied. -/
theorem probeTemplateDensity : templateDensity probeYT = 1 := by
  have hbi : (Finset.univ.biUnion probeYT) = (Finset.univ : Finset ProbeCl) := by
    ext c
    simp [probeYT]
  rw [templateDensity_eq, hbi]
  have hc : Fintype.card ProbeCl = 12 := by decide
  rw [Finset.card_univ, hc]
  norm_num

/-- **Every hypothesis of `terminalStateRealization` holds at the smoke
carriers.**  The frozen clauses (a), (b) and (c) are exhibited simultaneously,
so no `False` is derivable from the bundle at this parameter point.

The name deliberately claims **no schedule legality**: these values include
`s = 1`, which `07:445--447` excludes, and the tuple-level regularity certified
here for `probeRSig` is at `s = 1` indistinguishable from the per-bin form, so it
certifies nothing about the distinction `hRegF` turns on.  Schedule legality is
`schedRealization_hypotheses_are_legal` in Section 9. -/
theorem smokeRealization_hypotheses_hold :
    ((0 : Slot 2) ≠ (1 : Slot 2))
      ∧ (∀ p : Slot 1, (probeYT p).card = 12)
      ∧ (∀ p : Slot 1, RegularOn (probeYT p) (probeZeta p) 6)
      ∧ RegularOn probeRG (fun r => probeTup (probeOmg r)) 1
      ∧ RegularOn probeRSig (fun r => probeTup (probeOmg r)) 1
      ∧ (1 - (1 : ℝ) / 4 ≤ ((streamRows probeXZ 0 probeRG).card : ℝ) / (probeRG.card : ℝ))
      ∧ ((1 : ℝ) / 2 ≤ ((streamRows probeXZ 1 probeRSig).card : ℝ) / (probeRSig.card : ℝ)) := by
  refine ⟨by decide, by decide, by unfold RegularOn; decide, by unfold RegularOn; decide,
    by unfold RegularOn; decide, ?_, ?_⟩
  · have h1 : (streamRows probeXZ 0 probeRG).card = 3 := by decide
    have h2 : probeRG.card = 4 := by decide
    rw [h1, h2]
    norm_num
  · have h1 : (streamRows probeXZ 1 probeRSig).card = 2 := by decide
    have h2 : probeRSig.card = 4 := by decide
    rw [h1, h2]
    norm_num

/-- **The realization lemma fires at the smoke carriers, as a record.**

Every hypothesis of `terminalStateRealization` is discharged at the banked probe
carriers, and the value is the banked `TwoStreamState` at exactly the parameters
`probeState_is_legal` certifies.  Landing the **record** rather than only its
`Nonempty` shadow is what lets `probeRealization_conclusions_fire` push the
banked `fixedBin_of_uniform` through it.

Smoke check only: `s = 1` and `lambda_T = 1` are outside the construction (see
the Section 8 preamble).  The schedule-legal firing is `schedState` in
Section 9. -/
noncomputable def smokeRealization_state :
    TwoStreamState 2 1 2 12 6 probeN probeM probeC probeS probeRG probeRSig
      probeRD probeOmg probeRho probeYT probeZeta probeXZ probeYZ
      (templateDensity probeYT) (1 / 100) (1 / 200) (1 / 4) (1 / 2) :=
  have hgate : 49 / 64 ≤
      (aMin rhoPair (templateDensity probeYT) - tauZero 1 (1 / 200 : ℝ))
        / (1 + (1 / 100 : ℝ)) ^ 2 := by
    rw [probeTemplateDensity]
    exact terminalSelectorData_of_gates probeState_is_legal
  terminalStateRealization
    (Nmat := probeN) (Mmat := probeM) (cFam := probeC) (Stwo := probeS)
    (RG := probeRG) (RSig := probeRSig) (RD := probeRD) (Rf := probeRSig)
    (omg := probeOmg) (tup := probeTup) (YT := probeYT) (zeta := probeZeta)
    (XZ := probeXZ) (YZ := probeYZ) (eps2 := 1 / 100) (xT := 1 / 200)
    (ε := 1 / 4) (δ' := 1 / 2) (dOrd := 1) (dFor := 1) (mT := 12) (dT := 6)
    (i := 0) (j := 1) (pOrd := 0) (pFor := 0)
    (Pstar := probePstar) (Rbin := fun _ => (Finset.univ : Finset ProbeLtwo))
    (selRow := probeSelRow)
    (hOuter := by decide)
    (hbins := by intro p p' h; exact absurd (Subsingleton.elim p p') h)
    (htemplate_card := by decide)
    (htemplate_regular := by unfold RegularOn; decide)
    (hStwo := by intro l e; rfl)
    (hNval := by intro p y _ r; rfl)
    (hProtected := Or.inl rfl)
    (hEpsNonneg := by norm_num) (hEpsLtOne := by norm_num)
    (hDeltaPos := by norm_num) (hDeltaLeOne := by norm_num)
    (hOrdDensity := by
      have h1 : (streamRows probeXZ 0 probeRG).card = 3 := by decide
      have h2 : probeRG.card = 4 := by decide
      rw [h1, h2]; norm_num)
    (hForDensity := by
      have h1 : (streamRows probeXZ 1 probeRSig).card = 2 := by decide
      have h2 : probeRSig.card = 4 := by decide
      rw [h1, h2]; norm_num)
    (hRegG := by unfold RegularOn; decide) (hdOrd := by norm_num)
    (hRegF := by unfold RegularOn; decide) (hdFor := by norm_num)
    (hPstarTyped := by intro y _; exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (hPstarProj := by
      intro y hy
      refine ⟨probeSigmaStar y, ?_, ?_, ?_⟩
      · simp only [probeYZ, Finset.mem_filter, Finset.mem_univ, true_and, probeSigmaStar]
        simpa using hy
      · simp [probeSigmaStar]
      · simp [probeSigmaStar])
    (hPairDensity := by
      rw [probeTemplateDensity, probePstar_card]
      unfold aMin rhoPair
      norm_num)
    (hRbinCard := by
      intro p
      have hceil : ⌈tauZero 1 (1 / 200 : ℝ) * ((Fintype.card ProbeLtwo : ℕ) : ℝ)⌉₊ ≤ 1 := by
        rw [probe_tauZero]
        refine Nat.ceil_le.mpr ?_
        norm_num
      have hRb : (2 : ℕ) ≤ (Finset.univ : Finset ProbeLtwo).card := by decide
      change ⌈tauZero 1 (1 / 200 : ℝ) * (Fintype.card ProbeLtwo : ℝ)⌉₊
        ≤ (Finset.univ : Finset ProbeLtwo).card
      omega)
    (hSelRowMem := by decide)
    (hSelRowTyped := by
      intro p l _
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [probeSelRow, probeZeta])
    (hSelDist := by
      intro l _
      refine ⟨((0, (l, 0)), (0, (true, 1))), ?_, ?_⟩
      · simp only [probePstar, Finset.mem_erase, Finset.mem_univ, and_true]
        intro hcon
        have := congrArg (fun z => z.2.2.2) hcon
        simp at this
      · simp [probeSelRow])
    (hEps2 := by norm_num) (hxT := by norm_num)
    (hSelectorGate := hgate)

/-- **The realization lemma fires at the smoke carriers.**  The `Nonempty`
shadow of `smokeRealization_state`, at the banked probe's own numerals.

Smoke check only -- not the tranche's legality witness; see
`terminalStateRealization_fires_at_schedule_values` (Section 9). -/
theorem terminalStateRealization_fires_at_smoke_carriers :
    Nonempty (TwoStreamState 2 1 2 12 6 probeN probeM probeC probeS probeRG probeRSig
      probeRD probeOmg probeRho probeYT probeZeta probeXZ probeYZ 1 (1 / 100)
      (1 / 200) (1 / 4) (1 / 2)) := by
  have h := smokeRealization_state
  rw [probeTemplateDensity] at h
  exact ⟨h⟩

/-- **Non-vacuity readout: both hypothesis-(a) densities are tight at the
probe.**  The ordinary stream keeps exactly `3` of the `4` base rows and the
foreign stream exactly `2` of the `4` selector rows, so `1 - eps` and `delta'`
are met with equality and neither tolerance could be lowered. -/
theorem probeRealization_streams_are_tight :
    (streamRows probeXZ 0 probeRG).card = 3
      ∧ (streamRows probeXZ 1 probeRSig).card = 2
      ∧ probeRG.card = 4 ∧ probeRSig.card = 4
      ∧ Disjoint (streamRows probeXZ 0 probeRG) (streamRows probeXZ 1 probeRSig) :=
  ⟨by decide, by decide, by decide, by decide, streamRows_disjoint (by decide) _ _⟩

/-- **Non-vacuity readout: the derived `K_ord` is proper and nonempty.**  The
clause-(iv) column set built by the proof -- the image of the surviving ordinary
rows under "forget the raw-column prefix" (`09:804`) -- has `3` of the `4` tuple
columns at the probe.  So it is neither empty (the trivial witness refuted by
`kord_witness_is_nonempty`) nor the whole carrier, and its frozen density
`3/4 = 1 - eps` is met exactly. -/
theorem probeRealization_kord_is_proper :
    ((streamRows probeXZ 0 probeRG).image (fun x => probeTup (probeOmg x.2))).card = 3
      ∧ Fintype.card (Slot 1 → Slot 2 × ProbeCone) = 4 := by
  refine ⟨by decide, by decide⟩

/-- **Hypothesis consistency, made kernel-visible (the `cc-t1p` rule), read off
the realized record.**  The realized `TwoStreamState` is *in the type*: the
theorem takes the record as a binder, and its conclusion is a fact about that
record's own selector data.  The banked `fixedBin_of_uniform` -- clause (v) at
`P' = P_*`, `09:650` -- returns a classical two-copy restriction
`Q subseteq L_2 x L_2` together with the **provenance** that every `z in Q` is
the `zeta`-image of an actual pair in `st.Pstar`, and both halves are retained
here.  `Q` is therefore not a free-standing subset of a four-element carrier:
it is the family-index shadow of the record's own physical pair support, at the
record's own ordered bins `st.pOrd`, `st.pFor`.

`|Q| = 4` is a genuine consequence and not a shape check.  At the smoke numerals
the transferred bound is
`(a_min - tau_0)/(1 + eps_2)^2 = (99/100 - 1/100)/(101/100)^2 = 9800/10201`, so
`|Q|/|L_2|^2 = |Q|/4 >= 9800/10201 > 3/4` forces `|Q| >= 4`, and `|Q| <= 4`
because `L_2 x L_2` has four elements.

*Why the trivial witness fails.*  `Q = Finset.univ` has card `4` outright, but
it cannot discharge the provenance conjunct: with `st` a bound variable nothing
is known about `st.Pstar`, so `∀ z ∈ univ, ∃ y ∈ st.Pstar, ...` is not
decidable and not derivable -- for the empty-`Pstar` reading of the binder it is
outright false.  The earlier form of this readout (a closed
`∃ Q : Finset (ProbeLtwo × ProbeLtwo), Q.card = 4`, with no record in the type)
*was* discharged by `⟨Finset.univ, by decide⟩`; that form is what this
restatement replaces. -/
theorem probeRealization_conclusions_fire
    (st : TwoStreamState 2 1 2 12 6 probeN probeM probeC probeS probeRG probeRSig
      probeRD probeOmg probeRho probeYT probeZeta probeXZ probeYZ 1 (1 / 100)
      (1 / 200) (1 / 4) (1 / 2)) :
    ∃ Q : Finset (ProbeLtwo × ProbeLtwo), Q.card = 4
      ∧ (∀ z ∈ Q, ∃ y ∈ st.Pstar,
          probeZeta st.pOrd y.1 = z.1 ∧ probeZeta st.pFor y.2 = z.2) := by
  have hτ : (0 : ℝ) < tauZero 1 (1 / 200 : ℝ) := by
    rw [probe_tauZero]; norm_num
  obtain ⟨Q, hprov, hQ⟩ := fixedBin_of_uniform st hτ
  refine ⟨Q, ?_, hprov⟩
  rw [probe_tauZero] at hQ
  have hcL : Fintype.card ProbeLtwo = 2 := by decide
  rw [hcL] at hQ
  have hle : Q.card ≤ 4 := by
    have hu := Finset.card_le_univ Q
    have hcu : Fintype.card (ProbeLtwo × ProbeLtwo) = 4 := by decide
    omega
  have hge : 4 ≤ Q.card := by
    by_contra hcon
    have h3 : (Q.card : ℝ) ≤ 3 := by
      exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le hcon)
    unfold aMin rhoPair at hQ
    norm_num at hQ
    linarith
  omega

/-- **The readout fires at the pinned smoke construction.**  The use-site
companion of `probeRealization_conclusions_fire`: the record binder is filled by
the module's own `smokeRealization_state`, so the statement is a claim about a
*named* construction rather than a hypothetical.  This is what makes the
universally quantified form non-vacuous -- its hypothesis type is inhabited, and
`terminalStateRealization_fires_at_smoke_carriers` exhibits the same inhabitant
after `probeTemplateDensity` normalizes `lambda_T` to `1`.

Smoke check only.  The legality witness is the Section 9 companion. -/
theorem probeRealization_conclusions_fire_at_smoke_state :
    ∃ Q : Finset (ProbeLtwo × ProbeLtwo), Q.card = 4
      ∧ (∀ z ∈ Q, ∃ y ∈ smokeRealization_state.Pstar,
          probeZeta smokeRealization_state.pOrd y.1 = z.1
            ∧ probeZeta smokeRealization_state.pFor y.2 = z.2) := by
  have hτ : (0 : ℝ) < tauZero 1 (1 / 200 : ℝ) := by
    rw [probe_tauZero]; norm_num
  obtain ⟨Q, hprov, hQ⟩ := fixedBin_of_uniform smokeRealization_state hτ
  refine ⟨Q, ?_, hprov⟩
  rw [probeTemplateDensity, probe_tauZero] at hQ
  have hcL : Fintype.card ProbeLtwo = 2 := by decide
  rw [hcL] at hQ
  have hle : Q.card ≤ 4 := by
    have hu := Finset.card_le_univ Q
    have hcu : Fintype.card (ProbeLtwo × ProbeLtwo) = 4 := by decide
    omega
  have hge : 4 ≤ Q.card := by
    by_contra hcon
    have h3 : (Q.card : ℝ) ≤ 3 := by
      exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le hcon)
    unfold aMin rhoPair at hQ
    norm_num at hQ
    linarith
  omega

/-! ## Section 9  LANE-GATE 3: the schedule-legal firing witness

This is the tranche's legality witness.  Everything Section 8 could not reach is
reached here, at values the frozen construction actually admits.

**`s = 2` is a schedule value.**  `07:445--447` fixes `s = 2^{w_s}` with
`1 <= w_s <= b_2` (restated `07:500--501`); `s = 2 = 2^1` is the least such
value.  Consequences that Section 8 leaves untested and that are tested here:

* the two template bins `Y_{T,0}` and `Y_{T,1}` of `09:367--369` are **genuinely
  disjoint and both nonempty** (`schedBins`, `schedBins_are_nondegenerate`), so
  `hbins` is a real proof and not `Subsingleton.elim`.  Its only consumer --
  the derivation of the banked `selRow_inj` field inside
  `terminal_state_realization` -- therefore runs on real disjointness;
  `schedBins_are_nondegenerate` exhibits the separation it produces
  (`selRow (0, l) != selRow (1, l')` for **all** `l`, `l'`);
* the ordered bin pair of `09:687--694` is genuinely ordered: `p_o = 0` and
  `p_f = 1` are **distinct**, so `P_* subseteq Y_{T,0} x Y_{T,1}` is a cross-bin
  support rather than a square inside one bin;
* the Stage-3 selector `<S_2>^s` of `09:627` does not collapse: the tuple carrier
  `[s] -> J_2` has `16` elements, not `4`.

**`lambda_T = 9/10 < 1` is honest.**  `Y = Cols(N) = Rows(A)` of `09:364--371`
carries, besides the template block, the `{src-v} x W_V x [u_V]` and
`{src-b} x W_B x [u_B]` blocks of `eq:protected-labelled-carriers` (`08:82--92`)
at positive row masses `2^{-22}` each (`08:126--129`).  The column carrier `SCl`
below reproduces exactly that shape -- a template block `[s] x L_2 x [d_T]`
**plus** a two-element source block -- and the source columns are the ones on
which `schedN` does *not* follow `eq:raw-stage4-template-value`, matching
`eq:raw-stage4-source-value` (`07:560--567`).  So `lambda_T = 18/20 = 9/10`, and
the `lambda_T`-correction in `a_min = (rho_pair + lambda_T^2 - 1)/lambda_T^2` is
visibly active: `a_min = 80/81`, not the `99/100` that `lambda_T = 1` returns.

**Both branches of `09:672` are witnessed.**  `R_f in {R_Sigma, R_D}` is a
genuine disjunction and each leg is fired separately:
`terminalStateRealization_fires_at_schedule_values` takes `R_f = R_Sigma`
(`Or.inl`) and `terminalStateRealization_fires_in_diagonal_branch` takes
`R_f = R_D` (`Or.inr`).  The two are not relabellings of each other: the frozen
degrees `d_Sigma = w_Sigma |J_2|^{s-1} = 4` and `d_D = w_D = 1` of `09:730--733`
differ, and `schedRD` reproduces `09:737--738` literally -- it carries **only the
constant tuples**, so its tuple-level readout is regular of *no* positive degree
while its per-bin readout is regular of degree `1`.  Each firing theorem carries
that asymmetry in its own statement, so neither can be derived from the other by
`exact`.  This is `diagonalTupleReadout_not_regular` re-fired at the reservoir
the lemma is actually applied to, at the `s = 2` where the obstruction bites.

**Nondegeneracy is checked, not asserted.**  Both hypothesis-(a) densities are
met with **equality** in both branches (`12/16 = 3/4 = 1 - eps`, `8/16 = 1/2` and
`2/4 = 1/2`, both `= delta'`); `|P_*| = 80` of `m_T^2 = 81` is the **least**
cardinality meeting `eq:terminal-physical-pair-density` at `a_min = 80/81`, so
`P_*` is a proper subset of the typed square; the derived `K_ord` is a proper
nonempty subset (`12` of `16`); `tau_0 m_T^2 = 81/50 > 1`, so clause (v) is
exercised at proper subsets of `P_*`; and `Y_Z` is a proper subset of the column
carrier, so `sigmaStar_mem` and `selRow_mem` are not vacuous.

**Tier 2, not a schedule instance.**  `m_T = 9` is far below the `06:703` floor
and `q_2 = 2` sits below `eq:stage2-structural-gates`; the numerals here are the
smallest at which every *structural* feature of the frozen block is present, and
**no route parameter may be read out of them**.  In particular `lambda_T = 9/10`
is below the `99/100` of `eq:wrapper-template-gates` -- the banked gate bundle is
therefore **not** claimed here, and the frozen `hSelectorGate` is discharged
directly at these numerals
(`(80/81 - 1/50)/(101/100)^2 = 39190000/41314050 >= 49/64`) rather than through
`terminalSelectorData_of_gates`.  Meeting `99/100 <= lambda_T` together with
`lambda_T < 1` would force `|Y| >= 100` and hence `|P_*| >= 9701` typed pairs,
which no kernel-checkable finite carrier can carry; the qualitative legality the
frozen source demands (`lambda_T < 1`, source blocks present) is what is
certified here. -/

/-- `C_1`, the Stage-1 column alphabet of the schedule-legal witness. -/
abbrev SchedCone : Type := Bool

/-- `L_2`, the Stage-2 family-index carrier.  Three elements, so `m_T = 9`. -/
abbrev SchedLtwo : Type := Slot 3

/-- `Rows(M_1)`, the Stage-1 row carrier. -/
abbrev SchedRone : Type := Bool

/-- `J_2 = [q_2] x C_1` at `q_2 = 2`: four elements (`07:528`). -/
abbrev SchedJtwo : Type := Slot 2 × SchedCone

/-- `Omega`, the raw Stage-4 column carrier.  At `s = 2` a raw column carries a
genuine **tuple** `j : [s] -> J_2` (`09:706--718`), so `|Omega| = 4^2 = 16`. -/
abbrev SchedOm : Type := Slot 2 → SchedJtwo

/-- `Rows(N)`: the reservoir tag (`0` for `R_G`, `1` for `R_Sigma`, `2` for
`R_D`) over one underlying `Omega`. -/
abbrev SchedRw : Type := Slot 3 × SchedOm

/-- `Cols(N) = Rows(A)` (`09:775`, `08:82--92`): the template block
`[s] x L_2 x [d_T]` of `09:367--369` **plus** the two source columns standing for
`{src-v} x W_V x [u_V]` and `{src-b} x W_B x [u_B]`.  So `|Y| = 18 + 2 = 20`,
`m_T = 9`, `d_T = 3`, and `lambda_T = 18/20 = 9/10 < 1` as `08:126--129`
forces. -/
abbrev SchedCl : Type := (Slot 2 × SchedLtwo × Slot 3) ⊕ Bool

/-- `M = M_1^T`: the equality matrix, which is not constant. -/
def schedM : SchedCone → SchedRone → Bool := fun γ r => decide (γ = r)

/-- `c^{(z)}(alpha)`: a family depending genuinely on both the index `z` and the
coordinate `alpha`.  No injectivity is asserted, matching `09:801--802`. -/
def schedC : SchedLtwo → Slot 2 → SchedRone := fun z α => decide ((z.val + α.val) % 2 = 0)

/-- `S_2 = M_2^T` at the same family: `S_2(z, (alpha, gamma)) =
M(gamma, c^{(z)}(alpha))`, the banked `StageTwoRelaxed.stageTwo_apply` value
equation (`07:222--227`). -/
def schedS : SchedLtwo → SchedJtwo → Bool := fun z j => schedM j.2 (schedC z j.1)

/-- `N`.  On a **template** column of bin `p` the entry is the template-row value
`eq:raw-stage4-template-value` (`07:557`) read at the tuple coordinate `p`; on a
**source** column it is not, matching `eq:raw-stage4-source-value`
(`07:560--567`).  That asymmetry is what makes the source block a genuine
non-template block and `lambda_T` genuinely `< 1`. -/
def schedN : SchedRw → SchedCl → Bool :=
  fun r c =>
    Sum.elim (fun b : Slot 2 × SchedLtwo × Slot 3 => schedS b.2.1 (r.2 b.1)) (fun t => t) c

/-- `R_G`, the base reservoir: every tuple, so the **tuple**-level readout is
regular of degree `1` (`09:734--736`). -/
def schedRG : Finset SchedRw := Finset.univ.filter (fun r => r.1 = 0)

/-- `R_Sigma`, the selector reservoir: every tuple, so the **per-bin** readout is
regular of degree `|J_2|^{s-1} = 4`, the frozen `d_Sigma` of `09:731`. -/
def schedRSig : Finset SchedRw := Finset.univ.filter (fun r => r.1 = 1)

/-- `R_D`, the diagonal reservoir.  `09:737--738`: "in the diagonal reservoir the
map is bijective before its repetition label is added" -- it carries only the
**constant** tuples `d_{alpha,gamma}(p) = (alpha, gamma)` (`08:50--52`), so
`d_D = w_D = 1` with no `|J_2|^{s-1}` factor. -/
def schedRD : Finset SchedRw := Finset.univ.filter (fun r => r.1 = 2 ∧ r.2 1 = r.2 0)

/-- `omega`: forget the reservoir tag (`09:706--712`). -/
def schedOmg : SchedRw → SchedOm := Prod.snd

/-- The raw column's tuple component `j : [s] -> J_2` (`09:713--718`). -/
def schedTup : SchedOm → Slot 2 → SchedJtwo := fun o => o

/-- `rho_p(c) = j(p)`, the frozen tuple-coordinate selector of `09:713--718`. -/
def schedRho : Slot 2 → SchedOm → SchedJtwo := fun p o => o p

/-- The bin of a column: `some p` on the template block, `none` on the source
block.  This is what makes `Y_{T,p}` a decidable finite bin. -/
def schedBin : SchedCl → Option (Slot 2) :=
  fun c => Sum.elim (fun b : Slot 2 × SchedLtwo × Slot 3 => some b.1) (fun _ => none) c

/-- `Y_{T,p}` (`09:367--369`), `|Y_{T,p}| = m_T = 9` for both `p in [2]`, and the
two bins are disjoint. -/
def schedYT : Slot 2 → Finset SchedCl := fun p => Finset.univ.filter (fun c => schedBin c = some p)

/-- `zeta_p`: forget the uniform template-duplication label (`09:565--568`),
regular of degree `d_T = 3` on each bin. -/
def schedZeta : Slot 2 → SchedCl → SchedLtwo :=
  fun _ c => Sum.elim (fun b : Slot 2 × SchedLtwo × Slot 3 => b.2.1) (fun _ => 0) c

/-- `X_Z`: the surviving row set.  At the ordinary coordinate `i = 0` it keeps
`12` of the `16` base rows (`= 1 - eps` exactly); at the foreign coordinate
`j = 1` it keeps `8` of the `16` selector rows and `2` of the `4` diagonal rows
(`= delta'` exactly in **both** branches). -/
def schedXZ : Finset (Slot 2 × SchedRw) := Finset.univ.filter (fun x =>
    (x.1 = 0 ∧ x.2.1 = 0 → x.2.2 0 ≠ (1, true)) ∧
    (x.1 = 1 ∧ x.2.1 = 1 → (x.2.2 1).2 = false) ∧
    (x.1 = 1 ∧ x.2.1 = 2 → (x.2.2 1).2 = false))

/-- `P_*` (`09:689--694`): the **cross-bin** typed square `Y_{T,0} x Y_{T,1}`
minus one pair.  `80` is the least cardinality meeting
`eq:terminal-physical-pair-density` at `a_min = 80/81`, since `79/81 < 80/81`. -/
def schedPstar : Finset (SchedCl × SchedCl) :=
  ((schedYT 0) ×ˢ (schedYT 1)).erase (Sum.inl (0, 0, 0), Sum.inl (1, 0, 0))

/-- `Y_Z`: a **proper** subset of the column carrier, so `sigmaStar_mem` and
`selRow_mem` are genuine obligations rather than vacuous ones. -/
def schedYZ : Finset (Slot 2 → SchedCl) := Finset.univ.filter (fun w => w 0 ≠ Sum.inr true)

/-- The Stage-3 row section (`09:628--632`, `09:814--816`): bin `p` and family
index `l` are routed to a column whose ordinary coordinate lies in
`Y_{T,p}` with `zeta_p` value `l`.  Because the two bins are disjoint, this map
is injective across bins -- which is exactly what `selRow_inj` needs and what
`s = 1` could not test. -/
def schedSelRow : Slot 2 × SchedLtwo → (Slot 2 → SchedCl) :=
  fun pl => ![Sum.inl (pl.1, pl.2, 0), Sum.inl (1, 1, 0)]

/-- **The frozen selector is the tuple coordinate readout.**  `rho_p(c) = j(p)`
at `schedTup` is definitionally `schedRho`, so the realization lemma concludes a
state at the frozen readout and not at an unrelated one. -/
theorem schedRho_eq : (fun p o => schedTup o p) = schedRho := rfl

/-- **`lambda_T = 9/10`, and in particular `lambda_T < 1`.**  `09:367--371` read
off the actual bins: `|Y_T| = 18`, `|Y| = 20`.  The strict inequality is the
whole point -- `08:82--92` with `08:126--129` forbids `lambda_T = 1`. -/
theorem schedTemplateDensity : templateDensity schedYT = 9 / 10 := by
  have hbi : (Finset.univ.biUnion schedYT).card = 18 := by decide
  have hc : Fintype.card SchedCl = 20 := by decide
  rw [templateDensity_eq, hbi, hc]
  norm_num

/-- **`09:367--369`: the template bins are genuinely disjoint.**  Proved from the
bin tag, not from a `Subsingleton` collapse. -/
theorem schedBins : ∀ p p' : Slot 2, p ≠ p' → Disjoint (schedYT p) (schedYT p') := by
  intro p p' h
  refine Finset.disjoint_left.mpr ?_
  intro c hc hc'
  rw [schedYT, Finset.mem_filter] at hc hc'
  exact h (Option.some_injective _ (hc.2.symm.trans hc'.2))

/-- **`eq:raw-stage4-template-value` (`07:557`) at the witness.**  On a template
column of bin `p` the physical entry is the template-row value at the tuple
coordinate `p`.  The hypothesis `y in Y_{T,p}` is what pins the bin: the source
columns are excluded exactly as `07:560--567` requires. -/
theorem schedNval : ∀ (p : Slot 2) (y : SchedCl), y ∈ schedYT p → ∀ r : SchedRw,
    schedN r y = schedS (schedZeta p y) (schedTup (schedOmg r) p) := by
  intro p y hy r
  rw [schedYT, Finset.mem_filter] at hy
  cases y with
  | inl b =>
      have hb : b.1 = p := Option.some_injective _ hy.2
      subst hb
      rfl
  | inr t => exact absurd hy.2 (by simp [schedBin])

/-- **The realization lemma fires at schedule-legal values, as a record.**

Every hypothesis of `terminalStateRealization` is discharged at `s = 2`,
`lambda_T = 9/10`, `m_T = 9`, `d_T = 3`, `q = q_2 = 2`, `eps = 1/4`,
`delta' = 1/2`, `eps_2 = 1/100`, `x_T = 1/200`.  The foreign reservoir is left as
a parameter carrying only the frozen `09:672` disjunction and the **per-bin**
regularity of `09:730--733`, so the same record construction serves both branches
and neither is a relabelling of the other. -/
noncomputable def schedState (Rf : Finset SchedRw) (hProt : Rf = schedRSig ∨ Rf = schedRD)
    (dFor : ℕ) (hdFor : 0 < dFor)
    (hRegF : RegularOn Rf (fun r => schedTup (schedOmg r) 1) dFor)
    (hFor : (1 : ℝ) / 2 ≤ ((streamRows schedXZ 1 Rf).card : ℝ) / (Rf.card : ℝ)) :
    TwoStreamState 2 2 2 9 3 schedN schedM schedC schedS schedRG schedRSig
      schedRD schedOmg schedRho schedYT schedZeta schedXZ schedYZ
      (templateDensity schedYT) (1 / 100) (1 / 200) (1 / 4) (1 / 2) :=
  terminalStateRealization
    (Nmat := schedN) (Mmat := schedM) (cFam := schedC) (Stwo := schedS)
    (RG := schedRG) (RSig := schedRSig) (RD := schedRD) (Rf := Rf)
    (omg := schedOmg) (tup := schedTup) (YT := schedYT) (zeta := schedZeta)
    (XZ := schedXZ) (YZ := schedYZ) (eps2 := 1 / 100) (xT := 1 / 200)
    (ε := 1 / 4) (δ' := 1 / 2) (dOrd := 1) (dFor := dFor) (mT := 9) (dT := 3)
    (i := 0) (j := 1) (pOrd := 0) (pFor := 1)
    (Pstar := schedPstar) (Rbin := fun _ => (Finset.univ : Finset SchedLtwo))
    (selRow := schedSelRow)
    (hOuter := by decide)
    (hbins := schedBins)
    (htemplate_card := by decide)
    (htemplate_regular := by unfold RegularOn; decide)
    (hStwo := by intro l e; rfl)
    (hNval := schedNval)
    (hProtected := hProt)
    (hEpsNonneg := by norm_num) (hEpsLtOne := by norm_num)
    (hDeltaPos := by norm_num) (hDeltaLeOne := by norm_num)
    (hOrdDensity := by
      have h1 : (streamRows schedXZ 0 schedRG).card = 12 := by decide
      have h2 : schedRG.card = 16 := by decide
      rw [h1, h2]; norm_num)
    (hForDensity := hFor)
    (hRegG := by unfold RegularOn; decide) (hdOrd := by norm_num)
    (hRegF := hRegF) (hdFor := hdFor)
    (hPstarTyped := by
      intro y hy
      exact Finset.mem_product.mp (Finset.mem_of_mem_erase hy))
    (hPstarProj := by
      intro y hy
      have hty := Finset.mem_product.mp (Finset.mem_of_mem_erase hy)
      refine ⟨![y.1, y.2], ?_, ?_, ?_⟩
      · rw [schedYZ, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 := hty.1
        rw [schedYT, Finset.mem_filter] at h1
        simp only [Matrix.cons_val_zero]
        intro hcon
        rw [hcon] at h1
        simp [schedBin] at h1
      · simp
      · simp)
    (hPairDensity := by
      have hc : schedPstar.card = 80 := by decide
      rw [schedTemplateDensity, hc]
      unfold aMin rhoPair
      norm_num)
    (hRbinCard := by
      intro p
      have hceil : ⌈tauZero 2 (1 / 200 : ℝ) * ((Fintype.card SchedLtwo : ℕ) : ℝ)⌉₊ ≤ 1 := by
        have hc : Fintype.card SchedLtwo = 3 := by decide
        rw [hc]
        refine Nat.ceil_le.mpr ?_
        unfold tauZero
        norm_num
      have hRb : (3 : ℕ) = (Finset.univ : Finset SchedLtwo).card := by decide
      change ⌈tauZero 2 (1 / 200 : ℝ) * (Fintype.card SchedLtwo : ℝ)⌉₊
        ≤ (Finset.univ : Finset SchedLtwo).card
      omega)
    (hSelRowMem := by
      intro p l _
      rw [schedYZ, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [schedSelRow])
    (hSelRowTyped := by
      intro p l _
      refine ⟨?_, ?_⟩
      · rw [schedYT, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simp [schedSelRow, schedBin]⟩
      · simp [schedSelRow, schedZeta])
    (hSelDist := by
      intro l _
      refine ⟨(Sum.inl (0, l, 0), Sum.inl (1, 1, 0)), ?_, ?_⟩
      · rw [schedPstar, Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro hcon
          have := congrArg Prod.snd hcon
          simp at this
        · refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · rw [schedYT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
          · rw [schedYT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
      · simp [schedSelRow])
    (hEps2 := by norm_num) (hxT := by norm_num)
    (hSelectorGate := by
      rw [schedTemplateDensity]
      unfold aMin rhoPair tauZero
      norm_num)

/-- **Every hypothesis of `terminalStateRealization` holds at schedule-legal
values.**  Unlike Section 8's smoke check this name *does* claim legality, and
each conjunct is a value the frozen construction admits:

* the bin carrier is `Slot 2`, i.e. `s = 2 = 2^1`, the least schedule value
  `07:445--447` admits -- visible in the statement's own type -- and the two bins
  are disjoint, both nonempty, and both of size `m_T = 9`;
* `lambda_T = 9/10 < 1`, as `08:82--92` with `08:126--129` forces;
* the ordered bins `p_o = 0` and `p_f = 1` are **distinct**;
* the ordinary reservoir is tuple-level regular (`09:734--736`) and the
  **foreign** reservoir is per-bin regular in **both** branches of `09:672`, at
  the frozen degrees `d_Sigma = 4` and `d_D = 1` of `09:730--733`;
* both hypothesis-(a) densities hold, in both branches. -/
theorem schedRealization_hypotheses_are_legal :
    ((0 : Slot 2) ≠ (1 : Slot 2))
      ∧ Disjoint (schedYT 0) (schedYT 1)
      ∧ (∀ p : Slot 2, (schedYT p).card = 9)
      ∧ templateDensity schedYT < 1
      ∧ (∀ p : Slot 2, RegularOn (schedYT p) (schedZeta p) 3)
      ∧ RegularOn schedRG (fun r => schedTup (schedOmg r)) 1
      ∧ RegularOn schedRSig (fun r => schedTup (schedOmg r) 1) 4
      ∧ RegularOn schedRD (fun r => schedTup (schedOmg r) 1) 1
      ∧ (1 - (1 : ℝ) / 4 ≤ ((streamRows schedXZ 0 schedRG).card : ℝ) / (schedRG.card : ℝ))
      ∧ ((1 : ℝ) / 2 ≤ ((streamRows schedXZ 1 schedRSig).card : ℝ) / (schedRSig.card : ℝ))
      ∧ ((1 : ℝ) / 2 ≤ ((streamRows schedXZ 1 schedRD).card : ℝ) / (schedRD.card : ℝ)) := by
  refine ⟨by decide, schedBins 0 1 (by decide), by decide, ?_, by
    unfold RegularOn; decide, by unfold RegularOn; decide, by unfold RegularOn; decide,
    by unfold RegularOn; decide, ?_, ?_, ?_⟩
  · rw [schedTemplateDensity]; norm_num
  · have h1 : (streamRows schedXZ 0 schedRG).card = 12 := by decide
    have h2 : schedRG.card = 16 := by decide
    rw [h1, h2]; norm_num
  · have h1 : (streamRows schedXZ 1 schedRSig).card = 8 := by decide
    have h2 : schedRSig.card = 16 := by decide
    rw [h1, h2]; norm_num
  · have h1 : (streamRows schedXZ 1 schedRD).card = 2 := by decide
    have h2 : schedRD.card = 4 := by decide
    rw [h1, h2]; norm_num

/-- **LANE-GATE 3, the `R_f = R_Sigma` branch of `09:672`.**

The realization lemma fires at schedule-legal values with the foreign stream
routed from the **selector** reservoir.  The first conjunct records what
distinguishes this branch: on `R_Sigma` the tuple-level readout *is* regular
(degree `1`), so the per-bin degree `d_Sigma = 4` of `09:731` arises by composing
with the bin evaluation rather than by an obstruction.

The conclusion is not dischargeable by a default record -- see the "why the
trivial witness fails" note on `terminal_state_realization`. -/
theorem terminalStateRealization_fires_at_schedule_values :
    RegularOn schedRSig (fun r => schedTup (schedOmg r)) 1
      ∧ Nonempty (TwoStreamState 2 2 2 9 3 schedN schedM schedC schedS schedRG schedRSig
        schedRD schedOmg schedRho schedYT schedZeta schedXZ schedYZ (9 / 10)
        (1 / 100) (1 / 200) (1 / 4) (1 / 2)) := by
  refine ⟨by unfold RegularOn; decide, ?_⟩
  have h := schedState schedRSig (Or.inl rfl) 4 (by norm_num)
    (by unfold RegularOn; decide)
    (by
      have h1 : (streamRows schedXZ 1 schedRSig).card = 8 := by decide
      have h2 : schedRSig.card = 16 := by decide
      rw [h1, h2]; norm_num)
  rw [schedTemplateDensity] at h
  exact ⟨h⟩

/-- **LANE-GATE 3, the `R_f = R_D` branch of `09:672`.**

The realization lemma fires at schedule-legal values with the foreign stream
routed from the **diagonal** reservoir, i.e. `Or.inr` of the frozen disjunction.

The first conjunct is why this branch is not a relabelling of the selector one
and why `hRegF` had to be stated per-bin: `09:737--738` gives `R_D` only the
constant tuples, so at `s = 2` its **tuple**-level readout is regular of no
positive degree at all -- the fibre over a non-constant tuple is empty.  A
tuple-level foreign hypothesis would therefore have typechecked perfectly and
emptied this half of `09:672`.  The second conjunct is the per-bin form that *is*
satisfiable here, at the frozen `d_D = w_D = 1` of `09:733`. -/
theorem terminalStateRealization_fires_in_diagonal_branch :
    (∀ d : ℕ, ¬ (0 < d ∧ RegularOn schedRD (fun r => schedTup (schedOmg r)) d))
      ∧ RegularOn schedRD (fun r => schedTup (schedOmg r) 1) 1
      ∧ Nonempty (TwoStreamState 2 2 2 9 3 schedN schedM schedC schedS schedRG schedRSig
        schedRD schedOmg schedRho schedYT schedZeta schedXZ schedYZ (9 / 10)
        (1 / 100) (1 / 200) (1 / 4) (1 / 2)) := by
  refine ⟨?_, by unfold RegularOn; decide, ?_⟩
  · rintro d ⟨hd, h⟩
    have h0 := h ![(0, true), (1, false)]
    have hz : (schedRD.filter
        fun r => schedTup (schedOmg r) = ![(0, true), (1, false)]).card = 0 := by decide
    rw [hz] at h0
    omega
  · have h := schedState schedRD (Or.inr rfl) 1 (by norm_num)
      (by unfold RegularOn; decide)
      (by
        have h1 : (streamRows schedXZ 1 schedRD).card = 2 := by decide
        have h2 : schedRD.card = 4 := by decide
        rw [h1, h2]; norm_num)
    rw [schedTemplateDensity] at h
    exact ⟨h⟩

/-- **Non-vacuity readout: `hbins` is a real proof and its consumer is
exercised.**  The two template bins are disjoint and both nonempty, and the
separation this produces is exhibited: the Stage-3 row section maps the two bins
to **disjoint** column families, so the derivation of the banked `selRow_inj`
inside `terminal_state_realization` genuinely runs on `hbins` rather than on a
`Subsingleton` collapse.  At `s = 1` every conjunct below is either trivial or
false. -/
theorem schedBins_are_nondegenerate :
    Disjoint (schedYT 0) (schedYT 1)
      ∧ (schedYT 0).Nonempty ∧ (schedYT 1).Nonempty
      ∧ ∀ l l' : SchedLtwo, schedSelRow (0, l) ≠ schedSelRow (1, l') := by
  refine ⟨schedBins 0 1 (by decide), by decide, by decide, ?_⟩
  intro l l' hcon
  have := congrFun hcon 0
  simp [schedSelRow] at this

/-- **Non-vacuity readout: hypothesis (a) is tight in both branches.**  The
ordinary stream keeps exactly `12` of the `16` base rows, the selector stream
exactly `8` of `16`, and the diagonal stream exactly `2` of `4`.  So `1 - eps`
and `delta'` are met with **equality** everywhere and no tolerance is slack; the
two physical streams are disjoint by `09:534`. -/
theorem schedRealization_streams_are_tight :
    (streamRows schedXZ 0 schedRG).card = 12
      ∧ (streamRows schedXZ 1 schedRSig).card = 8
      ∧ (streamRows schedXZ 1 schedRD).card = 2
      ∧ schedRG.card = 16 ∧ schedRSig.card = 16 ∧ schedRD.card = 4
      ∧ Disjoint (streamRows schedXZ 0 schedRG) (streamRows schedXZ 1 schedRSig)
      ∧ Disjoint (streamRows schedXZ 0 schedRG) (streamRows schedXZ 1 schedRD) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    streamRows_disjoint (by decide) _ _, streamRows_disjoint (by decide) _ _⟩

/-- **Non-vacuity readout: the derived `K_ord` is proper and nonempty, and the
Stage-3 selector does not collapse.**  The clause-(iv) column set built by the
proof (`09:804`) has `12` of the `16` tuples, so it is neither empty -- the
trivial witness refuted by `kord_witness_is_nonempty` -- nor the whole carrier,
and its frozen density `12/16 = 3/4 = 1 - eps` is met exactly.  The tuple carrier
having `16 = |J_2|^s` elements rather than `4` is what `s = 2` buys: at `s = 1`
the frozen `<S_2>^s` of `09:627` collapses to `S_2`. -/
theorem schedRealization_kord_is_proper :
    ((streamRows schedXZ 0 schedRG).image (fun x => schedTup (schedOmg x.2))).card = 12
      ∧ Fintype.card (Slot 2 → Slot 2 × SchedCone) = 16 := by
  refine ⟨by decide, by decide⟩

/-- **Non-vacuity readout: `lambda_T` is honest and `a_min` is genuinely
corrected.**  The source block is nonempty -- the two columns standing for the
`{src-v}` and `{src-b}` blocks of `08:82--92` -- so `lambda_T = 9/10 < 1` as
`08:126--129` forces, and the `lambda_T`-correction in
`a_min = (rho_pair + lambda_T^2 - 1)/lambda_T^2` is visibly active: `a_min` is
`80/81`, strictly below the `99/100` that the construction-impossible
`lambda_T = 1` returns.  `|P_*| = 80` is then the **least** cardinality meeting
`eq:terminal-physical-pair-density`, since `79/81 < 80/81`; so `P_*` is a proper
subset of the typed square and the frozen bound is not slack. -/
theorem schedRealization_lambda_is_honest :
    (Finset.univ.filter fun c : SchedCl => schedBin c = none).card = 2
      ∧ templateDensity schedYT = 9 / 10
      ∧ templateDensity schedYT < 1
      ∧ aMin rhoPair (9 / 10 : ℝ) = 80 / 81
      ∧ aMin rhoPair (9 / 10 : ℝ) < aMin rhoPair (1 : ℝ)
      ∧ schedPstar.card = 80
      ∧ ¬ (aMin rhoPair (9 / 10 : ℝ) ≤ (79 : ℝ) / (9 : ℝ) ^ 2) := by
  refine ⟨by decide, schedTemplateDensity, ?_, ?_, ?_, by decide, ?_⟩
  · rw [schedTemplateDensity]; norm_num
  · unfold aMin rhoPair; norm_num
  · unfold aMin rhoPair; norm_num
  · unfold aMin rhoPair; norm_num

/-- **Hypothesis consistency at schedule-legal values, made kernel-visible (the
`cc-t1p` rule), read off the realized record.**  The realized `TwoStreamState`
at `s = 2`, `lambda_T = 9/10 < 1` is *in the type*: the theorem takes the record
as a binder and its conclusion is a fact about that record's own selector data.
The banked `fixedBin_of_uniform` -- clause (v) at `P' = P_*`, `09:650` --
returns a classical two-copy restriction `Q subseteq L_2 x L_2` together with
the **provenance** that every `z in Q` is the `zeta`-image of an actual pair in
`st.Pstar`, at the record's own ordered bins `st.pOrd`, `st.pFor`; both halves
are retained here, so `Q` is the family-index shadow of the record's physical
pair support and not a free-standing subset of a nine-element carrier.

`|Q| = 9` is a genuine consequence, not a shape check:
`|Q|/|L_2|^2 = |Q|/9 >= (80/81 - 1/50)/(101/100)^2 = 39190000/41314050` forces
`|Q| >= 9`, and `|Q| <= 9` because `L_2 x L_2` has nine elements.

*Why the trivial witness fails.*  `Q = Finset.univ` has card `9` outright, but
it cannot discharge the provenance conjunct: with `st` a bound variable nothing
is known about `st.Pstar`, so `∀ z ∈ univ, ∃ y ∈ st.Pstar, ...` is neither
decidable nor derivable.  The earlier form of this readout (a closed
`∃ Q : Finset (SchedLtwo × SchedLtwo), Q.card = 9`, with no record in the type)
*was* discharged by `⟨Finset.univ, by decide⟩`; that form is what this
restatement replaces.

**Consumption bar.**  This is a readout of `lem:terminal-state-realization`'s
own clause (v) at a *legality* witness.  It does **not** certify
`eq:wrapper-template-gates` (`09:387--395`), which these numerals fail, and no
downstream declaration may consume it as if it did. -/
theorem schedRealization_conclusions_fire
    (st : TwoStreamState 2 2 2 9 3 schedN schedM schedC schedS schedRG schedRSig
      schedRD schedOmg schedRho schedYT schedZeta schedXZ schedYZ (9 / 10)
      (1 / 100) (1 / 200) (1 / 4) (1 / 2)) :
    ∃ Q : Finset (SchedLtwo × SchedLtwo), Q.card = 9
      ∧ (∀ z ∈ Q, ∃ y ∈ st.Pstar,
          schedZeta st.pOrd y.1 = z.1 ∧ schedZeta st.pFor y.2 = z.2) := by
  have hτ : (0 : ℝ) < tauZero 2 (1 / 200 : ℝ) := by unfold tauZero; norm_num
  obtain ⟨Q, hprov, hQ⟩ := fixedBin_of_uniform st hτ
  refine ⟨Q, ?_, hprov⟩
  have hc : Fintype.card SchedLtwo = 3 := by decide
  rw [hc] at hQ
  have hle : Q.card ≤ 9 := by
    have hu := Finset.card_le_univ Q
    have hcu : Fintype.card (SchedLtwo × SchedLtwo) = 9 := by decide
    omega
  have hge : 9 ≤ Q.card := by
    by_contra hcon
    have h8 : (Q.card : ℝ) ≤ 8 := by
      exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le hcon)
    unfold aMin rhoPair tauZero at hQ
    norm_num at hQ
    linarith
  omega

/-- **The readout fires at the pinned schedule-legal construction, in both
branches of `09:672` at once.**  The use-site companion of
`schedRealization_conclusions_fire`: the record binder is filled by the module's
own `schedState`, left generic in the protected reservoir `R_f`, so the single
statement covers `R_f = R_Sigma` (`Or.inl`, `d_Sigma = 4`) and `R_f = R_D`
(`Or.inr`, `d_D = 1`) simultaneously -- exactly the frozen disjunction.  This is
what makes the universally quantified form non-vacuous: the hypothesis type is
inhabited, and `terminalStateRealization_fires_at_schedule_values` and
`terminalStateRealization_fires_in_diagonal_branch` exhibit the two inhabitants.

**Consumption bar** as on `schedRealization_conclusions_fire`: a legality
readout of clause (v), never a certificate of `eq:wrapper-template-gates`. -/
theorem schedRealization_conclusions_fire_at_schedState
    (Rf : Finset SchedRw) (hProt : Rf = schedRSig ∨ Rf = schedRD)
    (dFor : ℕ) (hdFor : 0 < dFor)
    (hRegF : RegularOn Rf (fun r => schedTup (schedOmg r) 1) dFor)
    (hFor : (1 : ℝ) / 2 ≤ ((streamRows schedXZ 1 Rf).card : ℝ) / (Rf.card : ℝ)) :
    ∃ Q : Finset (SchedLtwo × SchedLtwo), Q.card = 9
      ∧ (∀ z ∈ Q, ∃ y ∈ (schedState Rf hProt dFor hdFor hRegF hFor).Pstar,
          schedZeta (schedState Rf hProt dFor hdFor hRegF hFor).pOrd y.1 = z.1
            ∧ schedZeta (schedState Rf hProt dFor hdFor hRegF hFor).pFor y.2 = z.2) := by
  have hτ : (0 : ℝ) < tauZero 2 (1 / 200 : ℝ) := by unfold tauZero; norm_num
  obtain ⟨Q, hprov, hQ⟩ :=
    fixedBin_of_uniform (schedState Rf hProt dFor hdFor hRegF hFor) hτ
  refine ⟨Q, ?_, hprov⟩
  rw [schedTemplateDensity] at hQ
  have hc : Fintype.card SchedLtwo = 3 := by decide
  rw [hc] at hQ
  have hle : Q.card ≤ 9 := by
    have hu := Finset.card_le_univ Q
    have hcu : Fintype.card (SchedLtwo × SchedLtwo) = 9 := by decide
    omega
  have hge : 9 ≤ Q.card := by
    by_contra hcon
    have h8 : (Q.card : ℝ) ≤ 8 := by
      exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le hcon)
    unfold aMin rhoPair tauZero at hQ
    norm_num at hQ
    linarith
  omega

/-! ## Section 10  The provenance encoding, and what the restated readouts force

The `r2` statement repair turns on one object: the **family-index shadow** of a
record's own physical pair support,

  `familyShadow zeta_o zeta_f P_* = { (zeta_o y_1, zeta_f y_2) : y in P_* }`,

which is exactly the target of the `09:645--650` clause-(v) restriction.  The
provenance conjunct that `TwoStreamState.fixedBin_of_uniform` returns says
precisely that `Q` lands in that shadow -- `hasFamilyProvenance_iff_subset` is
that identity, and it is what makes the restated fire theorems statements about
the record rather than about a two- or three-element carrier.

The battery below is **general in every parameter** (any column and family-index
carriers, any `zeta` maps, any support): it is a test of the encoding, not of
the witnesses.  The two forcing corollaries then read the payoff off the
restated theorems: at both parameter points the shadow is the **whole**
`L_2 x L_2`, so the record's own `P_*` has at least `m_T`-many, resp. `9`-many,
distinct family-index pairs.  A record with an empty or small `P_*` cannot
satisfy the conclusion, which is what the pre-repair form failed to say. -/

/-- **The family-index shadow of a physical pair support** (`09:645--650`).
`zeta_p` forgets the Stage-3 duplication label (`09:766`), so a physical pair
`(y_1, y_2) in P_*` casts the family-index pair `(zeta_o y_1, zeta_f y_2)`.
Derived data only: no density, complexity, or robustness conclusion is built
into it (mechanical rule M4). -/
def familyShadow {Cl Ltwo : Type*} [DecidableEq Ltwo]
    (zetaOrd zetaFor : Cl → Ltwo) (Pstar : Finset (Cl × Cl)) :
    Finset (Ltwo × Ltwo) :=
  Pstar.image (fun y => (zetaOrd y.1, zetaFor y.2))

/-- **The provenance predicate carried by clause (v).**  Verbatim the conjunct
`TwoStreamState.fixedBin_of_uniform` returns: every family-index pair in `Q`
comes from an actual physical pair of the support.  Stated as a plain
proposition over explicit binders -- never a bundle field, and never a
restatement of a derived telescope. -/
def HasFamilyProvenance {Cl Ltwo : Type*}
    (zetaOrd zetaFor : Cl → Ltwo) (Pstar : Finset (Cl × Cl))
    (Q : Finset (Ltwo × Ltwo)) : Prop :=
  ∀ z ∈ Q, ∃ y ∈ Pstar, zetaOrd y.1 = z.1 ∧ zetaFor y.2 = z.2

/-- **Aux F1 (round trip, general).**  Provenance is exactly containment in the
shadow.  This is the identity that licenses reading the restated fire theorems
as claims about `st.Pstar`. -/
theorem hasFamilyProvenance_iff_subset {Cl Ltwo : Type*} [DecidableEq Ltwo]
    {zetaOrd zetaFor : Cl → Ltwo} {Pstar : Finset (Cl × Cl)}
    {Q : Finset (Ltwo × Ltwo)} :
    HasFamilyProvenance zetaOrd zetaFor Pstar Q
      ↔ Q ⊆ familyShadow zetaOrd zetaFor Pstar := by
  constructor
  · intro h z hz
    obtain ⟨y, hy, h1, h2⟩ := h z hz
    refine Finset.mem_image.mpr ⟨y, hy, ?_⟩
    exact Prod.ext h1 h2
  · intro h z hz
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp (h hz)
    exact ⟨y, hy, congrArg Prod.fst hyz, congrArg Prod.snd hyz⟩

/-- **Aux F2 (monotonicity, general).**  Provenance is downward closed in `Q`:
shrinking the restriction never invents a new physical source. -/
theorem HasFamilyProvenance.mono {Cl Ltwo : Type*}
    {zetaOrd zetaFor : Cl → Ltwo} {Pstar : Finset (Cl × Cl)}
    {Q Q' : Finset (Ltwo × Ltwo)}
    (h : HasFamilyProvenance zetaOrd zetaFor Pstar Q) (hsub : Q' ⊆ Q) :
    HasFamilyProvenance zetaOrd zetaFor Pstar Q' :=
  fun _ hz => h _ (hsub hz)

/-- **Aux F3 (the cardinality bridge, general).**  A provenance-carrying `Q`
bounds the shadow, hence the support itself, from below.  This is why a
cardinality claim about `Q` is now a claim about the record. -/
theorem hasFamilyProvenance_card_le {Cl Ltwo : Type*} [DecidableEq Ltwo]
    {zetaOrd zetaFor : Cl → Ltwo} {Pstar : Finset (Cl × Cl)}
    {Q : Finset (Ltwo × Ltwo)}
    (h : HasFamilyProvenance zetaOrd zetaFor Pstar Q) :
    Q.card ≤ (familyShadow zetaOrd zetaFor Pstar).card ∧ Q.card ≤ Pstar.card := by
  have hsub := hasFamilyProvenance_iff_subset.mp h
  have h1 := Finset.card_le_card hsub
  have h2 : (familyShadow zetaOrd zetaFor Pstar).card ≤ Pstar.card :=
    Finset.card_image_le
  exact ⟨h1, le_trans h1 h2⟩

/-- **Aux F4 (non-vacuity, general).**  A nonempty provenance-carrying `Q`
forces a nonempty support.  Contrapositive: over an empty `P_*` the only
provenance-carrying restriction is empty -- so `Q = Finset.univ` at a nonempty
family-index carrier is *false*, not merely unprovable, for such a record. -/
theorem hasFamilyProvenance_pstar_nonempty {Cl Ltwo : Type*}
    {zetaOrd zetaFor : Cl → Ltwo} {Pstar : Finset (Cl × Cl)}
    {Q : Finset (Ltwo × Ltwo)}
    (h : HasFamilyProvenance zetaOrd zetaFor Pstar Q) (hQ : Q.Nonempty) :
    Pstar.Nonempty := by
  obtain ⟨z, hz⟩ := hQ
  obtain ⟨y, hy, -, -⟩ := h z hz
  exact ⟨y, hy⟩

/-- **Aux F5 (the hardest field, general).**  The trivial witness
`Q = Finset.univ` carries provenance **iff** the record's own shadow is the
whole family-index square.  So the restated conclusion is not weaker than
"`familyShadow = univ`": it is equivalent to it whenever the maximal `Q` is the
one produced. -/
theorem hasFamilyProvenance_univ_iff {Cl Ltwo : Type*} [Fintype Ltwo]
    [DecidableEq Ltwo] {zetaOrd zetaFor : Cl → Ltwo} {Pstar : Finset (Cl × Cl)} :
    HasFamilyProvenance zetaOrd zetaFor Pstar (Finset.univ : Finset (Ltwo × Ltwo))
      ↔ familyShadow zetaOrd zetaFor Pstar = Finset.univ := by
  rw [hasFamilyProvenance_iff_subset, Finset.univ_subset_iff]

/-- **What the restated smoke readout forces.**  For *every* record at the
Section-8 parameter point, the family-index shadow of its own `P_*` is the whole
`L_2 x L_2`, and `P_*` therefore carries at least `4` physical pairs.  This is
the content the pre-repair closed form -- `exists Q, Q.card = 4` over a
four-element carrier -- did not carry. -/
theorem probeRealization_forces_full_shadow
    (st : TwoStreamState 2 1 2 12 6 probeN probeM probeC probeS probeRG probeRSig
      probeRD probeOmg probeRho probeYT probeZeta probeXZ probeYZ 1 (1 / 100)
      (1 / 200) (1 / 4) (1 / 2)) :
    familyShadow (probeZeta st.pOrd) (probeZeta st.pFor) st.Pstar = Finset.univ
      ∧ 4 ≤ st.Pstar.card := by
  obtain ⟨Q, hQcard, hprov⟩ := probeRealization_conclusions_fire st
  have hprov' : HasFamilyProvenance (probeZeta st.pOrd) (probeZeta st.pFor) st.Pstar Q :=
    hprov
  obtain ⟨hshadow, hpstar⟩ := hasFamilyProvenance_card_le hprov'
  refine ⟨?_, by omega⟩
  refine Finset.eq_univ_of_card _ ?_
  have hcu : Fintype.card (ProbeLtwo × ProbeLtwo) = 4 := by decide
  have hle := Finset.card_le_univ (familyShadow (probeZeta st.pOrd) (probeZeta st.pFor) st.Pstar)
  omega

/-- **What the restated schedule-legal readout forces.**  For *every* record at
the Section-9 parameter point the shadow is the whole `L_2 x L_2` -- all `9`
family-index pairs -- so `P_*` carries at least `9` physical pairs.

**Consumption bar** as on `schedRealization_conclusions_fire`: a legality
readout of clause (v), never a certificate of `eq:wrapper-template-gates`, and
no route parameter may be read out of `9`, `9/10`, or `1/200`. -/
theorem schedRealization_forces_full_shadow
    (st : TwoStreamState 2 2 2 9 3 schedN schedM schedC schedS schedRG schedRSig
      schedRD schedOmg schedRho schedYT schedZeta schedXZ schedYZ (9 / 10)
      (1 / 100) (1 / 200) (1 / 4) (1 / 2)) :
    familyShadow (schedZeta st.pOrd) (schedZeta st.pFor) st.Pstar = Finset.univ
      ∧ 9 ≤ st.Pstar.card := by
  obtain ⟨Q, hQcard, hprov⟩ := schedRealization_conclusions_fire st
  have hprov' : HasFamilyProvenance (schedZeta st.pOrd) (schedZeta st.pFor) st.Pstar Q :=
    hprov
  obtain ⟨hshadow, hpstar⟩ := hasFamilyProvenance_card_le hprov'
  refine ⟨?_, by omega⟩
  refine Finset.eq_univ_of_card _ ?_
  have hcu : Fintype.card (SchedLtwo × SchedLtwo) = 9 := by decide
  have hle := Finset.card_le_univ (familyShadow (schedZeta st.pOrd) (schedZeta st.pFor) st.Pstar)
  omega

end EthInapproximability.ParameterizedNP.TerminalStateRealization
