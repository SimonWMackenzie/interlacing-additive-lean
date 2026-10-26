import EthInapproximability.ParameterizedNP.StageThreeExactScale

/-!
# Parameterized NP route: the raw Stage-4 substitution block

## Provenance

* **Route:** `routes/parameterized-np` (active route, `ROUTES.md`).
* **Autoformalization anchor (proof source):** the frozen release named by
  `routes/parameterized-np/CURRENT_VERSION`, i.e.
  `routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/`
  `autoformalization/sections/07-one-level-construction.tex`,
  **lines 512--581** (the ETH-specific Stage-4 substitution) together with the
  block that closes the section, **lines 609--680**.  The anchors traced here,
  in the order the block prints them:
  * lines 512--515: "In the trace `T`, let `I = I_V u I_B` be the slabbed
    vertex and blocker items of `S = GuardedSource(G,s)`, and let
    `v_i in {0,1}^{q_2}` be the source vector of item `i`";
  * lines 516--523: the stored **zero-based rank injection**
    `pi_alpha : {i in I : v_i(alpha) = 1} -> [s]`,
    `pi_alpha(i) = |{h in I : v_h(alpha) = 1 and h < i}|`, "which exists
    because at most `s` source items are active at one coordinate";
  * lines 524--529: `K_R = Cols(R)^{s+1}` and `J_2 = Rows(M_2) = [q_2] x C_1`;
  * lines 530--535: the bound active-slot inclusion
    `iota_s = inc_{s,s+1}` and neutral last slot `nu_s = last_{s+1} = s`;
  * `eq:raw-stage4-universes` (label line 544, display 537--545):
    `Rows(B) = ([s] x Cols(M_2)) u (I x Rows(R))` and `Cols(B) = K_R x J_2^s`;
  * lines 546--555: the column destructuring `c = (xi, j)`,
    `j(p) = (alpha(p), gamma(p))`, and "Since `s > 0`, put `p_0 = 0 in [s]`
    and `alpha_c = alpha(p_0)`";
  * `eq:raw-stage4-template-value` (label line 558):
    `B((p,z),c) = M_2(j(p), z)`;
  * `eq:raw-stage4-source-value` (label line 569): the two-branch source rule
    with the active branch `R(x, xi(iota_s(pi_{alpha_c}(<i,h_i>))))` under the
    guard "`alpha(p) = alpha_c` for every `p in [s]` and `h_i : v_i(alpha_c) = 1`",
    and the neutral branch `R(x, xi(nu_s))` otherwise;
  * lines 571--581: the reading paragraph -- the `iota_1([q_1])` coordinates of
    each `gamma(p)` carry the Stage-1 template while the `kappa_1([s+1])`-tail
    is `s` active slots followed by the neutral slot; "In its active branch,
    the proof `h_i` supplies the subtype element in the domain of
    `pi_{alpha_c}`; no coercion from all of `I` is intended"; and the closing
    substitution sentence `4 |-> s`, one source row `|-> Rows(R)`;
  * lines 609--649: the direct protocols and the one-bit gap -- the Stage-1
    local threshold `x_cap` (611--614), `eq:local-capacity-gap` (label 621)
    with `q_1 + 3 = 2^a + 1` (623), the outer budget `K` (632), the `YES`
    upper bound `comp(M_4) <= Y + K` (636) and `eq:stage4-no-upper`
    (label 645), plus the deliberate postponement of the matching `NO` lower
    bound to `sec:dense-stage4` (646--649);
  * lines 662--673: the frozen `C = D + K + 1` and the two-scale profile
    targets `eq:raw-dense` and `eq:raw-low`, recorded here only as the shape
    the next section receives.
* **Successor anchor (the handoff this module hands to):**
  `08-dense-stage4.tex`, `sec:dense-duplication`, **lines 17--65**: the row
  destructuring `Rows(B) = T u W_V u W_B` with `T = u_{p in [s]} T_p`,
  `W_V = I_V x Rows(R)`, `W_B = I_B x Rows(R)`; the constant selector
  `k_0 : [s+1] -> Y_R`; `Sigma = {k_0} x Rows(M_2)^s`; the diagonal columns
  `D_alpha = {(tail_{s+1}(gamma), d_{alpha,gamma}) : gamma in C_1}` with
  `d_{alpha,gamma}(p) = (alpha,gamma)`; and the sentence "Consequently every
  displayed pair is an actual column of `B`".
* **Co-anchor (same budgets, mechanical-step form):**
  `11-one-level-assembly.tex`, Mechanical Step `step:L-06` (lines 330--366),
  displays `exp:E-06-yes` (label 342) and `exp:E-06-no-upper` (label 358).
* **Reader counterparts** (frozen release,
  `reader-facing/sections/03-parameterized-construction.tex`), one per
  declaration group, none of them shared with another module:
  * `eq:paper-active-injection` (label line 517) -- `rankInjection` and its
    battery.  The reader prints the **one-based** normalization
    `pi_alpha(i) = 1 + |{h in I_alpha : h < i}|` with the seed slots written
    `xi_1, ..., xi_{s+1}`; under `conv:finite-slots` (zero-based finite slots)
    that is the same map as the frozen zero-based `pi_alpha` of `07:520--521`,
    with the reader's `xi_{s+1}` the frozen `xi(nu_s)`.  The frozen
    autoformalization convention is what is transcribed here;
  * `eq:paper-B-carriers` (label line 533) -- `RawRows`, `RawCols`,
    `rawRows_card`, `rawCols_card`, `guardedRowsSplit`;
  * `eq:paper-B-template` (label line 540) -- `rawStageFour_template`;
  * `eq:paper-B-source` (label line 551) -- `rawStageFour_source_active` and
    `rawStageFour_source_neutral`;
  * `eq:paper-B-no-exact` (label line 597) -- `rawNoExact`, transcribed as a
    predicate and never asserted.
  The reader displays `eq:paper-source-support` (line 25),
  `eq:paper-B-yes` (line 573) and `eq:paper-B-no-upper` (line 582) are
  **already assigned** -- the first to `GuardedSourceGraph.card_activeRows_le`
  and its slabbed refinement `GuardedSourceSlab.card_activeSlot_le`, the other
  two to `StageThreeExactScale.yesBudget_eq` / `noBudget_eq` -- so no
  declaration here claims them; they are consumed by pin instead.

## Dependencies, imports and external adapters

* Imports `EthInapproximability.ParameterizedNP.StageThreeExactScale` only,
  hence transitively `StageTwoRelaxed`, `StageOneInterlace`, `PublicRecords`,
  `GuardedSourceSlab`, `GuardedSourceGraph`, `FiniteSlots`, `PilotStage3` and
  the project-axiom-free `LegacyNPCC.Core` / `LegacyNPCC.Bridge` facades
  reached through `EthInapproximability.Prelude`.  `LegacyNPCC.Stage12` --
  whose closure reaches the cited AGHP balanced-family axiom -- is **not**
  imported, and no declaration here is in its dependency graph.
* Banked project interfaces consumed **by pin, never restated**:
  * `PublicRecords.slotRank`, `PublicRecords.slotEmbed`,
    `PublicRecords.slotEmbed_val`, `PublicRecords.slotEmbed_injective`,
    `PublicRecords.slotRank_lt_card`, `PublicRecords.slotRank_not_constant`
    -- the frozen `T2` rank injection and its whole `A2` battery.  **Nothing
    of that battery is re-proved here**; `rankInjection` is exactly
    `slotEmbed` retyped along the banked `GuardedSourceSlab.mem_activeSlot`
    at the domain `{i : v_i(alpha) = 1}` in which `07:518` writes it;
  * `GuardedSourceSlab.guardedRow`, `activeSlot`, `mem_activeSlot`,
    `card_activeSlot_le`, `SlabRow`, `q2`;
  * `FiniteSlots.Stage1SlotBinding` with its derived `iota_1`, `kappa_1`,
    `iota_s`, `nu_s`, `stage1Tail`, `iotaS_ne_nuS` and the frozen `s > 0`
    field, which `07:554` is the source of;
  * `StageOneInterlace.stageOne`, `stage1Legal`, `witnessSource`,
    `stageOne_congr_head` (the `07:571--573` reading paragraph);
  * `StageTwoRelaxed.stageTwo`, `stageTwoWitness`, `widthsWitness`,
    `paramsWitnessTwo`, `coord₀`, `idx₀`, `idx₁`, `D_bobBit`, `bobBit`;
  * `StageThreeExactScale.outerBudget`, `yesBudget_eq`, `noBudget_eq`,
    `promise_one_bit_gap`, `localCapacityGap`, `xCap`, `columnThreshold`,
    `Dfamily_empty`, `handoffWitness`, `stageThreeScaleWitness`;
  * `PublicRecords.D_const`, `PublicRecords.LevelParams`.
* Vendored interfaces consumed **by pin, never restated**: `NPCC.D`,
  `NPCC.Dfamily`, `NPCC.bracketGE`, `NPCC.bracketGE.nonempty`,
  `NPCC.subgame`.
* Proof status: **new** for the raw Stage-4 matrix and its carrier battery
  (the object `B` had no Lean definition before this module); **adapted** for
  the one-bit gap, which is the block's own arithmetic over the banked
  Stage-3 handoff; **inherited by pin** for `pi_alpha`.
* Axiom surface (`#print axioms`): `propext`, `Classical.choice`, `Quot.sound`
  only.  No project axiom, no unproved placeholder of any kind, no new opaque
  certificate.

## Candidate encodings of `eq:raw-stage4-source-value` (`k = 2`, raced)

* **Candidate A (landed).**  Two binders -- the source-vector family
  `v : I -> [q] -> Bool` and the stored injection
  `pi : forall alpha, {i // v i alpha = true} -> [s]` -- are **explicit
  arguments** of `rawStageFour`, exactly as the trace stores them
  (`PublicRecords.LevelTrace` fields `S` and `pi` with `pi_eq`), and the
  source rule is a `dite` on the frozen conjunction "`alpha(p) = alpha_c` for
  every `p` **and** `v_i(alpha_c) = 1`", whose positive branch supplies
  `h_i` as the subtype element `<i, h.2>`.  No premise bundle is introduced,
  and no derived telescope is stored.
* **Candidate B (rejected).**  Collapse the injection to a total map
  `I -> [s+1]` sending inactive items to `nu_s`, and drop the agreement
  conjunct, so the source rule becomes the single uniform expression
  `R(x, xi(pi~_{alpha_c}(i)))` with no case split at all.

  Candidate B is shorter and needs no dependent `dite`.  It is rejected on a
  kernel-checkable ground: it **changes the matrix**.
  `candidateB_ignores_agreement_guard` exhibits, at legal parameter values
  (`a = 7`, `s = 64`, `q_2 = 128`, `N_2 = 2`), one column whose outer
  coordinates disagree and one item active at `alpha_c`, at which the frozen
  `B` takes the neutral value `R(x, xi(nu_s))` while Candidate B takes the
  active value `R(x, xi(iota_s(pi(...))))`, and the two differ.  The
  agreement conjunct of `07:565` is therefore content, not decoration, and
  Candidate B is not a re-encoding of `eq:raw-stage4-source-value` but a
  different matrix.
  Ranking (aux lemmas proved, faithfulness, length): A wins the first two
  decisively and loses only on length.

## Aux-lemma battery

Every battery item below is **proved**; nothing is stated and left open.

* `A1` the stored rank injection (5): `rankInjection_val` (the frozen rank
  equation on the nose), `rankInjection_injective`, `rankInjection_lt_card`,
  `rankInjection_lt_s`, and the domain identification `active_iff`.
* `A2` the frozen carriers (3): `rawRows_card`, `rawCols_card`, and the two
  nonemptiness instances.
* `A3` the entry rules (6): `rawStageFour_template`,
  `rawStageFour_source_active`, `rawStageFour_source_neutral`,
  `rawStageFour_source_neutral_of_disagree`,
  `rawStageFour_template_ignores_seed`,
  `rawStageFour_active_slot_ne_neutral`.
* `A4` the two pinned instantiations (2):
  `rawStageFourAtStageTwo_template_reads_head` (the `07:571--573` reading
  paragraph) and `rawStageFourGuarded_source_active`.
* `A5` the Section-8 handoff (2): `guardedRows_card_split`,
  `section8_columns`.
* `A6` the budgets and the capacity gap (3): `raw_budget_identities`,
  `localCapacityGap_le_member`, `localCapacityGap_family_nonempty`,
  with the monotonicity item `localCapacityGap_antitone`.

That is **21/21 labelled `Aux` items proved**, with `0` unproved, plus three
statement poles (`rankInjection_not_constant`,
`one_bit_gap_needs_the_lower_bound`, `localCapacityGap_not_automatic`), two
hypothesis-consistency probes (`promise_cases_are_not_one_matrix`,
`raw_one_bit_gap_satisfiable`), the kernel candidate-B discriminator
(`candidateB_ignores_agreement_guard`), and four non-vacuity readouts at legal
parameter values.

## Honest scope and recorded coverage limits

1. **No complexity claim about `B` is proved here.**  `07:636` and
   `eq:stage4-no-upper` are protocol constructions over a legal source
   packing, and the matching `NO` lower bound is explicitly postponed by
   `07:646--649` to `sec:dense-stage4`.  Accordingly `rawYesUpper`,
   `rawNoUpper` and `rawNoExact` are **transcribed predicates**, never
   asserted, and the one-bit gap `raw_one_bit_gap` is a closed conditional
   whose two endpoints are explicit hypotheses.
2. `raw_one_bit_gap` binds **two** matrices, one per promise branch.
   `promise_cases_are_not_one_matrix` proves in the kernel that conjoining
   the `YES` upper bound and the `NO` lower bound on a *single* matrix is
   inconsistent whenever `Y <= D`, so the two-matrix shape is forced by the
   frozen text rather than chosen for convenience.
3. `eq:local-capacity-gap` is consumed as the banked predicate
   `StageThreeExactScale.localCapacityGap` and is again never asserted.  The
   probes here establish what it does and does not say: it is equivalent to a
   uniform bound over every bracket member, it forces the bracket family to
   be nonempty (so it is not satisfiable by the `Nat.sInf` convention on the
   empty family), and it **fails** at the legal constant seed.  Exhibiting a
   concrete seed at which it *holds* would require the Stage-1 hard-seed
   endpoint, which is Lean pending; that is a coverage limit, not a claim.
4. The schedule identification `q_2 = q2(G,s)` between the Stage-2 width and
   the guarded source's width is **not** transcribed (it is the parameter
   compiler's, `06-parameter-schedule.tex`).  `rawStageFour` therefore takes
   the common coordinate width `q` as a binder; `rawStageFourAtStageTwo`
   pins it to the banked Stage-2 matrix and `rankInjection` pins the
   injection to the banked guarded source, and no declaration silently
   identifies the two.
5. No parameter schedule may be read out of any witness below; they inherit
   the coverage limits of `StageOneInterlace.stage1Legal` and
   `StageTwoRelaxed.widthsWitness`.
-/

namespace EthInapproximability.ParameterizedNP.RawStageFour

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.FiniteSlots
open EthInapproximability.ParameterizedNP.PublicRecords
open EthInapproximability.ParameterizedNP.StageOneInterlace
open EthInapproximability.ParameterizedNP.StageTwoRelaxed
open EthInapproximability.ParameterizedNP.StageThreeExactScale

variable {X Y : Type*}

/-! ## §1  The stored rank injection `pi_alpha` (`07:516--523`)

The frozen sentence writes the domain as `{i in I : v_i(alpha) = 1}` while the
banked `T2` battery of `05-public-records.tex` writes it as
`I_alpha = activeSlot G s alpha`.  `GuardedSourceSlab.mem_activeSlot` says
these are the same set, so the only work here is the retyping; the rank
formula, its injectivity, its bound and its statement pole are the banked
`PublicRecords` declarations, **consumed by pin**. -/

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The frozen domain identification.**  `{i in I : v_i(alpha) = 1}` of
`07:518` is the banked `I_alpha` of `05:246`.  General in `G`, `s`, `alpha`. -/
theorem active_iff (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s))
    (i : SlabRow V s) : guardedRow G s i α = true ↔ i ∈ activeSlot G s α :=
  (mem_activeSlot G s α i).symm

/-- **`pi_alpha` of `07:518--521`, typed at the frozen domain.**

This is the banked `PublicRecords.slotEmbed` -- the typed zero-based rank
injection of the trace's `T2` field -- retyped along `active_iff` at the
subtype `{i // v_i(alpha) = 1}` in which `07:518` writes it and in which the
source rule of `eq:raw-stage4-source-value` consumes it.  Nothing is
recomputed: the value is `slotRank` on the nose (`rankInjection_val`). -/
def rankInjection (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) (i : {i : SlabRow V s // guardedRow G s i α = true}) :
    Slot s :=
  slotEmbed G hs α ⟨i.1, (active_iff G s α i.1).mp i.2⟩

/-- **Aux 1 (the frozen rank equation).**  `pi_alpha(i) = |{h in I_alpha :
h < i}|` on the nose, by `rfl` through the banked `slotEmbed_val`. -/
@[simp] theorem rankInjection_val (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) (i : {i : SlabRow V s // guardedRow G s i α = true}) :
    (rankInjection G hs α i : ℕ) = slotRank G s α i.1 := rfl

/-- **Aux 2 (`pi_alpha` is an injection, not merely a map).**  The banked
`slotEmbed_injective`, transported along the retyping.  General. -/
theorem rankInjection_injective (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) : Function.Injective (rankInjection G hs α) := by
  intro i j h
  have hEq :
      (⟨i.1, (active_iff G s α i.1).mp i.2⟩ :
          {i : SlabRow V s // i ∈ activeSlot G s α}) =
        ⟨j.1, (active_iff G s α j.1).mp j.2⟩ :=
    slotEmbed_injective G hs α h
  have hval : i.1 = j.1 := by
    simpa using
      congrArg (fun t : {i : SlabRow V s // i ∈ activeSlot G s α} => t.1) hEq
  exact Subtype.ext hval

/-- **Aux 3 (the rank stays inside the active set).**  `pi_alpha(i) <
|I_alpha|`, the "rank equivalence" half of the banked `A2` battery, consumed
by pin.  Together with the banked `card_activeSlot_le` this is the frozen
"which exists because at most `s` source items are active at one coordinate"
(`07:523`) -- and it is exactly why the target is `[s]`. -/
theorem rankInjection_lt_card (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) (i : {i : SlabRow V s // guardedRow G s i α = true}) :
    (rankInjection G hs α i : ℕ) < (activeSlot G s α).card :=
  slotRank_lt_card G s α ((active_iff G s α i.1).mp i.2)

/-- **Aux 4 (the support bound is what bounds the target).**  The frozen
justification chain of `07:523`, assembled from the two banked facts:
`pi_alpha(i) < |I_alpha| <= s`.  General. -/
theorem rankInjection_lt_s (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) (i : {i : SlabRow V s // guardedRow G s i α = true}) :
    (rankInjection G hs α i : ℕ) < s :=
  lt_of_lt_of_le (rankInjection_lt_card G hs α i) (card_activeSlot_le G hs α)

/-- **Statement pole for `pi_alpha`.**  The trivial witness for "some typed map
`{i : v_i(alpha) = 1} -> [s]`" is a constant map, and it fails the frozen rank
equation as soon as two items are active at `alpha`: this is the banked
`slotRank_not_constant`, consumed at the retyped domain.  So the `pi` binder of
`rawStageFour` below is a constraint on the trace, not a naming convention. -/
theorem rankInjection_not_constant (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) (h2 : 2 ≤ (activeSlot G s α).card) :
    ¬ ∃ c : Slot s, ∀ i : {i : SlabRow V s // guardedRow G s i α = true},
        rankInjection G hs α i = c := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
  have hEq :
      (⟨i, (active_iff G s α i).mpr hi⟩ :
          {i : SlabRow V s // guardedRow G s i α = true}) =
        ⟨j, (active_iff G s α j).mpr hj⟩ :=
    rankInjection_injective G hs α
      ((hc ⟨i, (active_iff G s α i).mpr hi⟩).trans
        (hc ⟨j, (active_iff G s α j).mpr hj⟩).symm)
  refine hij ?_
  simpa using
    congrArg (fun t : {i : SlabRow V s // guardedRow G s i α = true} => t.1) hEq

/-! ## §2  The frozen carriers of `eq:raw-stage4-universes` (`07:524--545`) -/

/-- `J_2 = Rows(M_2) = [q_2] x C_1` (`07:528`). -/
abbrev RowsTwo (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) : Type _ :=
  Slot q × Stage1Cols F Y

/-- `K_R = Cols(R)^{s+1}` (`07:526`), the seed-selector tuple. -/
abbrev SeedTuple (F : Stage1SlotBinding) (Y : Type*) : Type _ :=
  Slot (F.s + 1) → Y

/-- `Rows(B) = ([s] x Cols(M_2)) u (I x Rows(R))`, the first line of
`eq:raw-stage4-universes`.  `L_2` is the column carrier of `M_2`. -/
abbrev RawRows (F : Stage1SlotBinding) (I X L₂ : Type*) : Type _ :=
  (Slot F.s × L₂) ⊕ (I × X)

/-- `Cols(B) = K_R x J_2^s`, the second line of `eq:raw-stage4-universes`. -/
abbrev RawCols (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) : Type _ :=
  SeedTuple F Y × (Slot F.s → RowsTwo F q Y)

/-- `p_0 = 0 in [s]` (`07:554`).  The frozen sentence "Since `s > 0`" is the
`s_pos` field of the banked slot binding, consumed by pin. -/
def p₀ (F : Stage1SlotBinding) : Slot F.s := ⟨0, F.s_pos⟩

@[simp] theorem p₀_val (F : Stage1SlotBinding) : (p₀ F : ℕ) = 0 := rfl

/-- `alpha_c = alpha(p_0)` (`07:555`), the outer coordinate the column
advertises at the zeroth bin. -/
def alphaCol (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} (c : RawCols F q Y) :
    Slot q :=
  (c.2 (p₀ F)).1

@[simp] theorem alphaCol_apply (F : Stage1SlotBinding) {q : ℕ} {Y : Type*}
    (c : RawCols F q Y) : alphaCol F c = (c.2 (p₀ F)).1 := rfl

/-- **Aux 5 (`M7`/`M10`: the exact row carrier).**  `|Rows(B)| = s |L_2| +
|I| m_R`, every count a `Fintype.card` of a tagged carrier.  General. -/
theorem rawRows_card (F : Stage1SlotBinding) (I X L₂ : Type*) [Fintype I]
    [Fintype X] [Fintype L₂] :
    Fintype.card (RawRows F I X L₂) =
      F.s * Fintype.card L₂ + Fintype.card I * Fintype.card X := by
  simp [RawRows, Fintype.card_sum, Fintype.card_prod]

/-- **Aux 6 (`M7`/`M10`: the exact column carrier).**  `|Cols(B)| =
n_R^{s+1} (q_2 n_R^{L_1})^s`, the literal `K_R x J_2^s`.  General. -/
theorem rawCols_card (F : Stage1SlotBinding) (q : ℕ) (Y : Type*) [Fintype Y] :
    Fintype.card (RawCols F q Y) =
      Fintype.card Y ^ (F.s + 1) *
        (q * Fintype.card Y ^ F.L₁) ^ F.s := by
  simp [RawCols, SeedTuple, RowsTwo, Stage1Cols, Fintype.card_prod,
    Fintype.card_fin]

/-- **Aux 7 (`M7`: both carriers are nonempty).**  Nonemptiness of the source
alphabet propagates: this is what the frozen `m_R > 0`, `n_R > 0` and
`0 < N_2` are carried for. -/
instance rawRows_nonempty (F : Stage1SlotBinding) (I X L₂ : Type*)
    [Nonempty L₂] : Nonempty (RawRows F I X L₂) :=
  ⟨Sum.inl (p₀ F, Classical.arbitrary L₂)⟩

instance rawCols_nonempty (F : Stage1SlotBinding) {q : ℕ} (Y : Type*)
    [Nonempty Y] [NeZero q] : Nonempty (RawCols F q Y) :=
  ⟨fun _ => Classical.arbitrary Y,
    fun _ => (⟨0, Nat.pos_of_ne_zero (NeZero.ne q)⟩, fun _ => Classical.arbitrary Y)⟩

/-! ## §3  The raw Stage-4 matrix `B` (`eq:raw-stage4-universes`--
`eq:raw-stage4-source-value`)

The two source-side objects the rule reads -- the source-vector family `v` and
the stored injection `pi` -- are **explicit binders**, exactly as the banked
`PublicRecords.LevelTrace` stores them (fields `S` and `pi`, pinned by `S_eq`
and `pi_eq`).  Section 8's protected duplication is defined from this `B`, so
its carriers are kept literal here. -/

/-- **The raw Stage-4 matrix `B = M_4`** of `eq:raw-stage4-universes`,
`eq:raw-stage4-template-value` and `eq:raw-stage4-source-value`
(`07:536--570`), reader `eq:paper-B-carriers` / `eq:paper-B-template` /
`eq:paper-B-source`.

Binder order follows the frozen display: the slot binding `F` (which supplies
`s`, `iota_s` and `nu_s`), the common coordinate width `q = q_2`, the seed
`R`, the Stage-2 matrix `M_2` at its frozen row carrier `J_2 = [q] x C_1`, the
source-vector family `v`, and the stored rank injection `pi`.

* On a template row `(p,z)` the value is `M_2(j(p), z)`: the seed selector
  `xi` is **not** read.
* On a source row `(i,x)` the value is `R(x, xi(iota_s(pi_{alpha_c}(<i,h_i>))))`
  when every outer coordinate agrees with `alpha_c` **and** `i` is active at
  `alpha_c`, and `R(x, xi(nu_s))` otherwise.  The positive branch supplies
  `h_i` as the second component of the guard, so the injection is applied to a
  subtype element and never to a coerced element of all of `I`
  (`07:575--577`). -/
def rawStageFour {I L₂ : Type*} (F : Stage1SlotBinding) (q : ℕ)
    (R : X → Y → Bool) (M₂ : RowsTwo F q Y → L₂ → Bool)
    (v : I → Slot q → Bool)
    (π : ∀ α : Slot q, {i : I // v i α = true} → Slot F.s) :
    RawRows F I X L₂ → RawCols F q Y → Bool := fun r c =>
  match r with
  | Sum.inl pz => M₂ (c.2 pz.1) pz.2
  | Sum.inr ix =>
      if h : (∀ p : Slot F.s, (c.2 p).1 = alphaCol F c) ∧
          v ix.1 (alphaCol F c) = true then
        R ix.2 (c.1 (F.iotaS (π (alphaCol F c) ⟨ix.1, h.2⟩)))
      else
        R ix.2 (c.1 F.nuS)

/-- **Aux 8 (`eq:raw-stage4-template-value`, definitionally).**  General in
every binder. -/
@[simp] theorem rawStageFour_template {I L₂ : Type*} (F : Stage1SlotBinding)
    (q : ℕ) (R : X → Y → Bool) (M₂ : RowsTwo F q Y → L₂ → Bool)
    (v : I → Slot q → Bool)
    (π : ∀ α : Slot q, {i : I // v i α = true} → Slot F.s)
    (p : Slot F.s) (z : L₂) (c : RawCols F q Y) :
    rawStageFour F q R M₂ v π (Sum.inl (p, z)) c = M₂ (c.2 p) z := rfl

/-- **Aux 9 (`eq:raw-stage4-source-value`, active branch).**  Under the two
frozen guards the entry is the seed read at the `iota_s`-image of the stored
rank.  General in every binder. -/
theorem rawStageFour_source_active {I L₂ : Type*} (F : Stage1SlotBinding)
    (q : ℕ) (R : X → Y → Bool) (M₂ : RowsTwo F q Y → L₂ → Bool)
    (v : I → Slot q → Bool)
    (π : ∀ α : Slot q, {i : I // v i α = true} → Slot F.s)
    (i : I) (x : X) (c : RawCols F q Y)
    (hagree : ∀ p : Slot F.s, (c.2 p).1 = alphaCol F c)
    (hactive : v i (alphaCol F c) = true) :
    rawStageFour F q R M₂ v π (Sum.inr (i, x)) c =
      R x (c.1 (F.iotaS (π (alphaCol F c) ⟨i, hactive⟩))) := by
  simp only [rawStageFour, dif_pos (And.intro hagree hactive)]

/-- **Aux 10 (`eq:raw-stage4-source-value`, neutral branch).**  Whenever either
guard fails -- the outer coordinates disagree, or the item is inactive at
`alpha_c` -- the entry is the seed read at the neutral slot.  General. -/
theorem rawStageFour_source_neutral {I L₂ : Type*} (F : Stage1SlotBinding)
    (q : ℕ) (R : X → Y → Bool) (M₂ : RowsTwo F q Y → L₂ → Bool)
    (v : I → Slot q → Bool)
    (π : ∀ α : Slot q, {i : I // v i α = true} → Slot F.s)
    (i : I) (x : X) (c : RawCols F q Y)
    (hfail : ¬ ((∀ p : Slot F.s, (c.2 p).1 = alphaCol F c) ∧
        v i (alphaCol F c) = true)) :
    rawStageFour F q R M₂ v π (Sum.inr (i, x)) c = R x (c.1 F.nuS) := by
  simp only [rawStageFour, dif_neg hfail]

/-- **Aux 11 (the agreement conjunct alone can fire the neutral branch).**  If
some bin advertises a different outer coordinate, the entry is neutral even for
an item that *is* active at `alpha_c`.  This is the clause Candidate B drops.
General. -/
theorem rawStageFour_source_neutral_of_disagree {I L₂ : Type*}
    (F : Stage1SlotBinding) (q : ℕ) (R : X → Y → Bool)
    (M₂ : RowsTwo F q Y → L₂ → Bool) (v : I → Slot q → Bool)
    (π : ∀ α : Slot q, {i : I // v i α = true} → Slot F.s)
    (i : I) (x : X) (c : RawCols F q Y) {p : Slot F.s}
    (hp : (c.2 p).1 ≠ alphaCol F c) :
    rawStageFour F q R M₂ v π (Sum.inr (i, x)) c = R x (c.1 F.nuS) :=
  rawStageFour_source_neutral F q R M₂ v π i x c (fun h => hp (h.1 p))

/-- **Aux 12 (`07:571--574`: the template rows do not read the seed
selector).**  Two columns with the same outer tuple `j` but arbitrary seed
tuples `xi` agree on every template row.  General. -/
theorem rawStageFour_template_ignores_seed {I L₂ : Type*}
    (F : Stage1SlotBinding) (q : ℕ) (R : X → Y → Bool)
    (M₂ : RowsTwo F q Y → L₂ → Bool) (v : I → Slot q → Bool)
    (π : ∀ α : Slot q, {i : I // v i α = true} → Slot F.s)
    (ξ ξ' : SeedTuple F Y) (j : Slot F.s → RowsTwo F q Y) (p : Slot F.s)
    (z : L₂) :
    rawStageFour F q R M₂ v π (Sum.inl (p, z)) (ξ, j) =
      rawStageFour F q R M₂ v π (Sum.inl (p, z)) (ξ', j) := rfl

/-- **Aux 13 (`07:573--575`: the active slots are never the neutral slot).**
The frozen tail of `[s+1]` is "`s` active slots followed by the neutral slot",
so the active branch of the source rule never reads the seed coordinate the
neutral branch reads.  This is the banked `FiniteSlots.iotaS_ne_nuS`, consumed
by pin, and it is what makes the two branches of `eq:raw-stage4-source-value`
distinguishable at all. -/
theorem rawStageFour_active_slot_ne_neutral (F : Stage1SlotBinding)
    (r : Slot F.s) : F.iotaS r ≠ F.nuS :=
  F.iotaS_ne_nuS r

/-! ### The two pinned instantiations

`rawStageFour` is stated at the binders the frozen display uses.  The two
objects the route actually substitutes are pinned here, each without any
transport. -/

/-- **`B` at the banked Stage-2 matrix.**  The Stage-2 relaxed interlace of
`eq:stage2-relaxed-value` is passed on the nose: `q := q_2`, `L_2 := [N_2]`,
and `Rows(M_2) = [q_2] x C_1` is literally `RowsTwo`. -/
def rawStageFourAtStageTwo {I : Type*} (F : Stage1SlotBinding)
    (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (v : I → Slot W.q₂ → Bool)
    (π : ∀ α : Slot W.q₂, {i : I // v i α = true} → Slot F.s) :
    RawRows F I X (Slot Pr.N₂) → RawCols F W.q₂ Y → Bool :=
  rawStageFour F W.q₂ R (stageTwo F R W Pr) v π

/-- **Aux 14 (`07:571--573`, the reading paragraph).**  On a template row the
raw Stage-4 entry reads `gamma(p)` only through the Stage-1 template block
`iota_1([q_1])`; the whole `kappa_1([s+1])`-tail -- the `s` active slots and
the neutral slot -- is discarded.  Proved by pin from
`StageOneInterlace.stageOne_congr_head`, and general in every binder. -/
theorem rawStageFourAtStageTwo_template_reads_head {I : Type*}
    (F : Stage1SlotBinding) (R : X → Y → Bool) (W : StageTwoWidths)
    (Pr : LevelParams (Stage1Rows F X) W.q₂)
    (v : I → Slot W.q₂ → Bool)
    (π : ∀ α : Slot W.q₂, {i : I // v i α = true} → Slot F.s)
    (p : Slot F.s) (z : Slot Pr.N₂) (ξ ξ' : SeedTuple F Y)
    (j j' : Slot F.s → RowsTwo F W.q₂ Y)
    (hα : (j p).1 = (j' p).1)
    (hhead : ∀ t : Slot F.q₁, (j p).2 (F.iota₁ t) = (j' p).2 (F.iota₁ t)) :
    rawStageFourAtStageTwo F R W Pr v π (Sum.inl (p, z)) (ξ, j) =
      rawStageFourAtStageTwo F R W Pr v π (Sum.inl (p, z)) (ξ', j') := by
  have h := congrFun (stageOne_congr_head F R hhead) (Pr.c₂ z (j p).1)
  change stageTwo F R W Pr (j p) z = stageTwo F R W Pr (j' p) z
  rw [show (j p) = ((j p).1, (j p).2) from rfl,
    show (j' p) = ((j' p).1, (j' p).2) from rfl, stageTwo_apply, stageTwo_apply,
    ← hα]
  exact h

/-- **`B` at the banked guarded source.**  Taking the frozen `I = I(G,s)`,
`v = GuardedSource(G,s)` and `pi = pi_alpha` needs **no transport**: the
guarded source is read at the slot binding's own `s`, so its coordinate width
is `q2 G F.s` and its item carrier is `SlabRow V F.s`. -/
def rawStageFourGuarded {L₂ : Type*} (G : EndpointGraph V E)
    (F : Stage1SlotBinding) (hs : 3 ≤ F.s) (R : X → Y → Bool)
    (M₂ : RowsTwo F (q2 G F.s) Y → L₂ → Bool) :
    RawRows F (SlabRow V F.s) X L₂ → RawCols F (q2 G F.s) Y → Bool :=
  rawStageFour F (q2 G F.s) R M₂ (guardedRow G F.s) (rankInjection G hs)

/-- **Aux 15 (the pinned source rule).**  At the guarded source the active
branch reads the seed at the `iota_s`-image of the banked `slotRank`.  This is
the frozen `eq:raw-stage4-source-value` with every source-side object pinned:
nothing is chosen. -/
theorem rawStageFourGuarded_source_active {L₂ : Type*} (G : EndpointGraph V E)
    (F : Stage1SlotBinding) (hs : 3 ≤ F.s) (R : X → Y → Bool)
    (M₂ : RowsTwo F (q2 G F.s) Y → L₂ → Bool) (i : SlabRow V F.s) (x : X)
    (c : RawCols F (q2 G F.s) Y)
    (hagree : ∀ p : Slot F.s, (c.2 p).1 = alphaCol F c)
    (hactive : guardedRow G F.s i (alphaCol F c) = true) :
    rawStageFourGuarded G F hs R M₂ (Sum.inr (i, x)) c =
      R x (c.1 (F.iotaS (rankInjection G hs (alphaCol F c) ⟨i, hactive⟩))) :=
  rawStageFour_source_active F (q2 G F.s) R M₂ (guardedRow G F.s)
    (rankInjection G hs) i x c hagree hactive

/-! ## §4  The handoff into `sec:dense-stage4` (`08:17--65`)

Section 8 opens by destructuring `Rows(B) = T u W_V u W_B` and by exhibiting
two column sets, `Sigma` and `D_diag`, whose members it needs to be actual
columns of `B`.  Both are recorded here at the frozen carriers, so that the
protected duplication of `eq:protected-labelled-carriers` has a literal object
to duplicate. -/

/-- The Section-8 template block `T = u_{p in [s]} T_p` (`08:22`). -/
abbrev TemplateRows (F : Stage1SlotBinding) (L₂ : Type*) : Type _ :=
  Slot F.s × L₂

/-- **The frozen row destructuring `Rows(B) = T u W_V u W_B`** (`08:20--24`),
at the guarded source, where the slabbed item carrier
`I = [4s] x (V u [s-3])` splits into the vertex items `I_V = [4s] x V` and the
blocker items `I_B = [4s] x [s-3]` of `thm:guarded-source`.  This is an
explicit equivalence, so Section 8's three row reservoirs are literal
summands rather than a description. -/
def guardedRowsSplit (V : Type*) (F : Stage1SlotBinding) (X L₂ : Type*) :
    RawRows F (SlabRow V F.s) X L₂ ≃
      TemplateRows F L₂ ⊕
        (((Fin (4 * F.s) × V) × X) ⊕ ((Fin (4 * F.s) × Fin (F.s - 3)) × X)) :=
  Equiv.sumCongr (Equiv.refl _)
    (((Equiv.prodSumDistrib (Fin (4 * F.s)) V (Fin (F.s - 3))).prodCongr
        (Equiv.refl X)).trans
      (Equiv.sumProdDistrib _ _ _))

/-- **Aux 16 (`eq:protected-raw-cardinality-abbreviations`).**  The Section-8
abbreviations satisfy `X_0 = T_raw + V_raw + B_raw` at the frozen carriers.
General in `V`, `X`, `L_2` and `F`. -/
theorem guardedRows_card_split (V : Type*) [Fintype V] (F : Stage1SlotBinding)
    (X L₂ : Type*) [Fintype X] [Fintype L₂] :
    Fintype.card (RawRows F (SlabRow V F.s) X L₂) =
      F.s * Fintype.card L₂ +
        ((4 * F.s * Fintype.card V) * Fintype.card X +
          (4 * F.s * (F.s - 3)) * Fintype.card X) := by
  rw [Fintype.card_congr (guardedRowsSplit V F X L₂)]
  simp [TemplateRows, Fintype.card_sum, Fintype.card_prod, mul_assoc]

/-- The Section-8 constant selector `k_0 : [s+1] -> Y_R`, `k_0(r) = y_0`
(`08:33--37`): "constructor data derived from the public order, not a
proof-time choice". -/
def constSelector (F : Stage1SlotBinding) {Y : Type*} (y₀ : Y) :
    SeedTuple F Y :=
  fun _ => y₀

/-- A member of the Section-8 selector reservoir `Sigma = {k_0} x Rows(M_2)^s`
(`08:46`).  It is an actual column of `B` by construction. -/
def sigmaCol (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} (y₀ : Y)
    (d : Slot F.s → RowsTwo F q Y) : RawCols F q Y :=
  (constSelector F y₀, d)

/-- The Section-8 diagonal tuple `d_{alpha,gamma}(p) = (alpha,gamma)`
(`08:48--52`). -/
def diagTuple (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} (α : Slot q)
    (γ : Stage1Cols F Y) : Slot F.s → RowsTwo F q Y :=
  fun _ => (α, γ)

/-- A member of the Section-8 diagonal reservoir
`D_alpha = {(tail_{s+1}(gamma), d_{alpha,gamma}) : gamma in C_1}`
(`08:53--63`), built from the banked Stage-1 tail map
`FiniteSlots.Stage1SlotBinding.stage1Tail`, `tail_{s+1}(gamma)(r) =
gamma(kappa_1(r))`. -/
def diagCol (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} (α : Slot q)
    (γ : Stage1Cols F Y) : RawCols F q Y :=
  (F.stage1Tail γ, diagTuple F α γ)

/-- **Aux 17 (`08:65`: "every displayed pair is an actual column of `B`").**
Both Section-8 reservoirs consist of columns of `B` on the nose, with the
frozen shapes: the selector reservoir has a constant seed tuple, and the
diagonal reservoir advertises one outer coordinate in every bin -- so it lands
in the *agreeing* case of `eq:raw-stage4-source-value`.  General. -/
theorem section8_columns (F : Stage1SlotBinding) {q : ℕ} {Y : Type*} (y₀ : Y)
    (d : Slot F.s → RowsTwo F q Y) (α : Slot q) (γ : Stage1Cols F Y) :
    (∀ r : Slot (F.s + 1), (sigmaCol F y₀ d).1 r = y₀) ∧
      (sigmaCol F y₀ d).2 = d ∧
      (∀ p : Slot F.s, (diagCol F α γ).2 p = (α, γ)) ∧
      (∀ r : Slot (F.s + 1), (diagCol F α γ).1 r = γ (F.kappa₁ r)) ∧
      (∀ p : Slot F.s, ((diagCol F α γ).2 p).1 = alphaCol F (diagCol F α γ)) := by
  refine ⟨fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## §5  The direct protocols and the one-bit gap (`07:609--680`)

Every budget identity of this block is the banked Stage-3 handoff, consumed by
pin.  What is new is the promise-branch bookkeeping: the two endpoints are
transcribed as predicates and the gap is a closed conditional over **two**
matrices. -/

/-- **`comp(B) <= Y + K`** (`07:636`, `exp:E-06-yes`), transcribed and never
asserted.  `K` is the banked `StageThreeExactScale.outerBudget`. -/
def rawYesUpper {A B' : Type*} [Fintype A] [Fintype B'] (Bmat : A → B' → Bool)
    (Yb K : ℕ) : Prop :=
  D Bmat ≤ Yb + K

/-- **`eq:stage4-no-upper`: `comp(B) <= D + K + 1`** (`07:645`,
`exp:E-06-no-upper`), transcribed and never asserted. -/
def rawNoUpper {A B' : Type*} [Fintype A] [Fintype B'] (Bmat : A → B' → Bool)
    (Dsrc K : ℕ) : Prop :=
  D Bmat ≤ Dsrc + K + 1

/-- **The frozen `NO` value `C = D + K + 1`** (`07:665`), reader
`eq:paper-B-no-exact`.  Transcribed and never asserted: `07:646--649` states
in terms that the matching lower bound is postponed to `sec:dense-stage4`,
"because the undeleted matrix is itself an allowed retained member". -/
def rawNoExact {A B' : Type*} [Fintype A] [Fintype B'] (Bmat : A → B' → Bool)
    (Dsrc K : ℕ) : Prop :=
  D Bmat = Dsrc + K + 1

/-- **Aux 18 (the block's budget identities, by pin).**  Both promise budgets
of `07:632--645` are the banked Stage-3 handoff arithmetic; nothing is
restated.  General in `Y` and `D`. -/
theorem raw_budget_identities (F : Stage1SlotBinding) (W : StageTwoWidths)
    (S : StageThreeScale) (Yb Dsrc : ℕ) :
    Yb + F.a + W.r₂ + S.wS = Yb + outerBudget F W S ∧
      Dsrc + (F.a + 1) + W.r₂ + S.wS = Dsrc + outerBudget F W S + 1 :=
  ⟨yesBudget_eq F W S Yb, noBudget_eq F W S Dsrc⟩

/-- **The raw one-bit gap** of the block title `07:609` ("The direct protocols
and the one-bit gap").

Two **separate** matrices, one per promise branch, exactly as the frozen text
states them: `07:636` gives the `YES` upper endpoint and `07:665` the `NO`
value `C = D + K + 1` whose lower half `sec:dense-stage4` supplies.  Under
`Y <= D` the `NO` instance is strictly harder.

*Why the trivial reading fails.*  The conclusion is not obtainable from the
two **upper** bounds alone: `one_bit_gap_needs_the_lower_bound` exhibits legal
data satisfying both upper bounds with equal complexities.  It is also not
obtainable by conjoining the branches on one matrix:
`promise_cases_are_not_one_matrix` derives `False` from exactly that
conjunction at `Y <= D`. -/
theorem raw_one_bit_gap {A₁ B₁ A₂ B₂ : Type*} [Fintype A₁] [Fintype B₁]
    [Fintype A₂] [Fintype B₂] (Byes : A₁ → B₁ → Bool) (Bno : A₂ → B₂ → Bool)
    (Yb Dsrc K : ℕ) (hYD : Yb ≤ Dsrc)
    (hyes : rawYesUpper Byes Yb K)
    (hno : Dsrc + K + 1 ≤ D Bno) :
    D Byes < D Bno := by
  have h1 : D Byes ≤ Yb + K := hyes
  omega

/-- **The raw one-bit gap at the frozen outer budget.**  The same statement
with `K` pinned to the banked `K = a + log_2 q_2 + log_2 s`, so that no
consumer may substitute a different budget, and with the `NO` side taken at
the frozen exact value `C = D + K + 1` of `07:665`.  The budget separation
step is the banked `StageThreeExactScale.promise_one_bit_gap` at the very
binders `F`, `W`, `S` the caller supplies -- consumed by pin, not restated. -/
theorem raw_one_bit_gap_at_outerBudget {A₁ B₁ A₂ B₂ : Type*} [Fintype A₁]
    [Fintype B₁] [Fintype A₂] [Fintype B₂] (F : Stage1SlotBinding)
    (W : StageTwoWidths) (S : StageThreeScale)
    (Byes : A₁ → B₁ → Bool) (Bno : A₂ → B₂ → Bool) (Yb Dsrc : ℕ)
    (hYD : Yb ≤ Dsrc)
    (hyes : rawYesUpper Byes Yb (outerBudget F W S))
    (hno : rawNoExact Bno Dsrc (outerBudget F W S)) :
    D Byes < D Bno := by
  have hbudget := (promise_one_bit_gap F W S Yb Dsrc hYD).2
  have h1 : D Byes ≤ Yb + outerBudget F W S := hyes
  have h2 : D Bno = Dsrc + outerBudget F W S + 1 := hno
  omega

/-- **Consistency probe (HYPOTHESIS-CONSISTENCY RULE).**  The `YES` upper
bound and the `NO` lower bound must never be conjoined on one matrix: at the
frozen side condition `Y <= D` that conjunction is **inconsistent**, for every
matrix and every budget.  So `raw_one_bit_gap`'s two-matrix shape is forced by
the frozen text -- `07:629--645` states the two directions as the two branches
of one promise -- and is not a convenience. -/
theorem promise_cases_are_not_one_matrix {A B' : Type*} [Fintype A]
    [Fintype B'] (Bmat : A → B' → Bool) (Yb Dsrc K : ℕ) (hYD : Yb ≤ Dsrc)
    (hyes : rawYesUpper Bmat Yb K) (hno : Dsrc + K + 1 ≤ D Bmat) : False := by
  have h1 : D Bmat ≤ Yb + K := hyes
  omega

/-- **Statement pole for the one-bit gap.**  The two frozen **upper** bounds
never give the gap: two constant matrices at two different pairs of finite
carriers satisfy `07:636` and `eq:stage4-no-upper` for every budget, while the
strict separation **fails**.  So the `NO`-side lower bound that `07:646--649`
postpones to `sec:dense-stage4` is exactly the missing content, and
`raw_one_bit_gap` cannot be strengthened by dropping `hno`. -/
theorem one_bit_gap_needs_the_lower_bound (Yb Dsrc K : ℕ) :
    rawYesUpper (fun (_ : Bool) (_ : Bool) => false) Yb K ∧
      rawNoUpper (fun (_ : Fin 3) (_ : Fin 5) => false) Dsrc K ∧
      ¬ D (fun (_ : Bool) (_ : Bool) => false) <
          D (fun (_ : Fin 3) (_ : Fin 5) => false) := by
  have h0 : D (fun (_ : Bool) (_ : Bool) => false) = 0 :=
    PublicRecords.D_const (X := Bool) (Y := Bool) false
  have h1 : D (fun (_ : Fin 3) (_ : Fin 5) => false) = 0 :=
    PublicRecords.D_const (X := Fin 3) (Y := Fin 5) false
  refine ⟨?_, ?_, ?_⟩
  · change D (fun (_ : Bool) (_ : Bool) => false) ≤ Yb + K
    omega
  · change D (fun (_ : Fin 3) (_ : Fin 5) => false) ≤ Dsrc + K + 1
    omega
  · omega

/-- **The one-bit-gap hypothesis bundle is satisfiable.**  At `Y = D = K = 0`
the banked constant matrix satisfies the `YES` endpoint and the banked
`bobBit` satisfies the `NO` endpoint, and the conclusion `0 < 1` holds.  So
`raw_one_bit_gap` is not vacuous: its hypotheses are jointly realizable by
concrete kernel-checked matrices. -/
theorem raw_one_bit_gap_satisfiable :
    rawYesUpper (fun (_ : Bool) (_ : Bool) => false) 0 0 ∧
      0 + 0 + 1 ≤ D bobBit ∧
      D (fun (_ : Bool) (_ : Bool) => false) < D bobBit := by
  have h0 : D (fun (_ : Bool) (_ : Bool) => false) = 0 :=
    PublicRecords.D_const (X := Bool) (Y := Bool) false
  have h1 : D bobBit = 1 := D_bobBit
  refine ⟨?_, ?_, ?_⟩
  · change D (fun (_ : Bool) (_ : Bool) => false) ≤ 0 + 0
    omega
  · omega
  · omega

/-! ## §6  The odd-copy capacity inequality (`eq:local-capacity-gap`,
`07:617--623`)

The predicate is the banked `StageThreeExactScale.localCapacityGap`, consumed
by pin and again never asserted.  The probes below fix what it says. -/

/-- **Aux 19 (the consumption form).**  `eq:local-capacity-gap` says exactly
that **every** member of the odd-copy bracket family has complexity at least
`D + a + 1`; this is the form the Stage-1 local threshold is applied in
(`07:621--623`, "the lower bound applies whenever at least `q_1 + 3` copies
each retain row density `x_cap` ...").  General. -/
theorem localCapacityGap_le_member {X Y : Type*} [Fintype X] [Fintype Y]
    (F : Stage1SlotBinding) (R : X → Y → Bool) (b₀ Dsrc : ℕ)
    (h : localCapacityGap F R b₀ Dsrc)
    {RC : Finset (Fin (F.q₁ + 3) × X) × Finset (Fin (F.q₁ + 3) → Y)}
    (hRC : RC ∈ bracketGE X Y (F.q₁ + 3) (xCap F b₀) (9 / 25)) :
    Dsrc + F.a + 1 ≤
      D (subgame (interlaceFun R (F.q₁ + 3)) RC.1 RC.2) :=
  le_trans h (Nat.sInf_le ⟨RC, hRC, rfl⟩)

/-- **Aux 20 (the gap is not satisfiable by an empty family).**  `Dfamily` is a
`Nat.sInf` and returns `0` on the empty family, so a family lower bound taken
without nonemptiness would be unsound.  `eq:local-capacity-gap` is immune: it
*forces* the odd-copy bracket family to be nonempty.  General. -/
theorem localCapacityGap_family_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (F : Stage1SlotBinding) (R : X → Y → Bool) (b₀ Dsrc : ℕ)
    (h : localCapacityGap F R b₀ Dsrc) :
    (bracketGE X Y (F.q₁ + 3) (xCap F b₀) (9 / 25)).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hzero : Dfamily (interlaceFun R (F.q₁ + 3))
      (bracketGE X Y (F.q₁ + 3) (xCap F b₀) (9 / 25)) = 0 := by
    rw [hempty]
    exact Dfamily_empty _
  have hgap : Dsrc + F.a + 1 ≤
      Dfamily (interlaceFun R (F.q₁ + 3))
        (bracketGE X Y (F.q₁ + 3) (xCap F b₀) (9 / 25)) := h
  rw [hzero] at hgap
  omega

/-- **Aux 21 (the gap is antitone in the seed complexity).**  A smaller `D`
demands less.  General. -/
theorem localCapacityGap_antitone {X Y : Type*} [Fintype X] [Fintype Y]
    (F : Stage1SlotBinding) (R : X → Y → Bool) (b₀ : ℕ) {D₁ D₂ : ℕ}
    (hD : D₁ ≤ D₂) (h : localCapacityGap F R b₀ D₂) :
    localCapacityGap F R b₀ D₁ :=
  le_trans (by omega) h

/-- **Statement pole for `eq:local-capacity-gap`: it is not automatic.**

At the legal constant seed the odd-copy bracket family is nonempty (its full
row set meets `x_cap <= 1` and its full column set meets `9/25 <= 1`) and
every member has complexity `0`, so the inequality fails.  The guard
`a + 1 <= b_0` is the frozen depth condition that makes `x_cap = 2^{a+1-b_0}`
a density at all.  Hence the inequality is genuine inherited content and is
correctly carried as a named hypothesis rather than proved. -/
theorem localCapacityGap_not_automatic (F : Stage1SlotBinding) {b₀ Dsrc : ℕ}
    (hb : F.a + 1 ≤ b₀) :
    ¬ localCapacityGap F (fun (_ : Bool) (_ : Bool) => false) b₀ Dsrc := by
  intro h
  have hx : xCap F b₀ ≤ 1 := by
    have hexp : ((F.a : ℝ) + 1 - (b₀ : ℝ)) ≤ 0 := by
      have : ((F.a : ℝ) + 1) ≤ (b₀ : ℝ) := by exact_mod_cast hb
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  obtain ⟨RC, hRC⟩ :=
    bracketGE.nonempty (X := Bool) (Y := Bool) (F.q₁ + 3) (xCap F b₀) (9 / 25)
      hx (by norm_num) (by simp)
  have hmem := localCapacityGap_le_member F _ b₀ Dsrc h hRC
  have hconst :
      subgame (interlaceFun (fun (_ : Bool) (_ : Bool) => false) (F.q₁ + 3))
          RC.1 RC.2 =
        fun (_ : {x // x ∈ RC.1}) (_ : {y // y ∈ RC.2}) => false := rfl
  rw [hconst, PublicRecords.D_const] at hmem
  omega

/-! ## §7  Candidate B, refuted in the kernel

Candidate B drops the agreement conjunct of `07:565` and reads the stored
injection unconditionally on active items.  The following definition is that
rule, and the theorem after it shows the resulting matrix is **not** the
frozen `B`. -/

/-- Candidate B's source rule: no agreement guard. -/
def candidateBSource {I L₂ : Type*} (F : Stage1SlotBinding) (q : ℕ)
    (R : X → Y → Bool) (M₂ : RowsTwo F q Y → L₂ → Bool)
    (v : I → Slot q → Bool)
    (π : ∀ α : Slot q, {i : I // v i α = true} → Slot F.s) :
    RawRows F I X L₂ → RawCols F q Y → Bool := fun r c =>
  match r with
  | Sum.inl pz => M₂ (c.2 pz.1) pz.2
  | Sum.inr ix =>
      if h : v ix.1 (alphaCol F c) = true then
        R ix.2 (c.1 (F.iotaS (π (alphaCol F c) ⟨ix.1, h⟩)))
      else
        R ix.2 (c.1 F.nuS)

/-! ## §8  Non-vacuity witnesses (LANE-GATE 3)

Every definition above is inhabited at **legal** parameter values by a
**nondegenerate** witness.  The bindings are the banked
`StageOneInterlace.stage1Legal` (`a = 7`, `s = 64`),
`StageTwoRelaxed.widthsWitness` (`q_2 = 128`) and
`StageTwoRelaxed.paramsWitnessTwo` (`N_2 = 2`, nonconstant family), over the
banked nonconstant seed `StageOneInterlace.witnessSource = AND`.  No parameter
schedule may be read out of any of them. -/

/-- The witness item carrier: two source items, so that the stored injection
has something to rank. -/
abbrev IWit : Type := Fin 2

/-- The witness source vectors: both items are active exactly at the zeroth
coordinate.  The support bound of `eq:paper-source-support` holds with room to
spare (`2 <= 64 = s`), so the witness is not inhabited at a
cardinality-contradictory point. -/
def vWit : IWit → Slot widthsWitness.q₂ → Bool :=
  fun _ α => decide ((α : ℕ) = 0)

/-- The witness rank injection: the item index itself, which is the frozen
zero-based rank of `07:520--521` for this source. -/
def πWit : ∀ α : Slot widthsWitness.q₂,
    {i : IWit // vWit i α = true} → Slot stage1Legal.s :=
  fun _ i => ⟨(i.1 : ℕ), by
    have h := i.1.isLt
    simp only [stage1Legal]
    omega⟩

/-- **Non-vacuity 0 (the witness injection is injective and nonconstant).**  It
is a genuine injection, so the `pi` binder of `rawStageFour` is not being
inhabited by the trivial constant map that
`PublicRecords.slotRank_not_constant` rules out. -/
theorem πWit_nondegenerate (α : Slot widthsWitness.q₂) :
    Function.Injective (πWit α) := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ h
  have hval : (i : ℕ) = (j : ℕ) :=
    congrArg (fun t : Slot stage1Legal.s => (t : ℕ)) h
  exact Subtype.ext (Fin.ext hval)

/-- The zeroth outer coordinate at the declared legal width, and a second one
distinct from it. -/
def coordOne : Slot widthsWitness.q₂ := ⟨1, by norm_num [widthsWitness]⟩

/-- The witness seed selector: `true` exactly at the zeroth seed slot, so that
the active branch at rank `0` and the active branch at rank `1` -- and the
neutral branch at `nu_s` -- take **three** distinguishable readings. -/
def ξWit : SeedTuple stage1Legal Bool := fun t => decide ((t : ℕ) = 0)

/-- The witness column with all bins advertising the zeroth coordinate: the
*agreeing* case of `eq:raw-stage4-source-value`. -/
def cAgree : RawCols stage1Legal widthsWitness.q₂ Bool :=
  (ξWit, fun _ => (coord₀, fun _ => true))

/-- The witness column whose bins advertise **two different** outer
coordinates: the disagreeing case, which fires the neutral branch. -/
def cDisagree : RawCols stage1Legal widthsWitness.q₂ Bool :=
  (ξWit, fun p => (if (p : ℕ) = 0 then coord₀ else coordOne, fun _ => true))

/-- **The raw Stage-4 matrix at legal parameter values.**  The Stage-2 matrix
is the banked `stageTwoWitness`. -/
def rawStageFourWitness :
    RawRows stage1Legal IWit Bool (Slot paramsWitnessTwo.N₂) →
      RawCols stage1Legal widthsWitness.q₂ Bool → Bool :=
  rawStageFour stage1Legal widthsWitness.q₂ witnessSource stageTwoWitness vWit πWit

/-- **Non-vacuity 1 (the matrix is nondegenerate on template rows).**  The two
template rows over the banked Stage-2 witness take both Boolean values at the
same column, so `B` is neither constant nor independent of `Cols(M_2)`. -/
theorem rawStageFourWitness_template_nondegenerate :
    rawStageFourWitness (Sum.inl (p₀ stage1Legal, idx₀)) cAgree = true ∧
      rawStageFourWitness (Sum.inl (p₀ stage1Legal, idx₁)) cAgree = false :=
  ⟨rfl, rfl⟩

/-- **Non-vacuity 2 (the stored injection is genuinely read).**  At one and the
same agreeing column the two source items give **different** entries, because
their ranks `0` and `1` select different seed slots.  A definition that ignored
`pi` could not do this. -/
theorem rawStageFourWitness_reads_the_injection :
    rawStageFourWitness (Sum.inr ((0 : IWit), true)) cAgree = true ∧
      rawStageFourWitness (Sum.inr ((1 : IWit), true)) cAgree = false := by
  constructor <;> rfl

/-- **Non-vacuity 3 (both branches of the source rule are realized).**  At the
disagreeing column the same item and the same seed tuple give the neutral
reading, which differs from the active reading at the agreeing column.  So the
case split of `eq:raw-stage4-source-value` is content. -/
theorem rawStageFourWitness_both_branches :
    rawStageFourWitness (Sum.inr ((0 : IWit), true)) cAgree = true ∧
      rawStageFourWitness (Sum.inr ((0 : IWit), true)) cDisagree = false := by
  refine ⟨rfl, ?_⟩
  have hp : (cDisagree.2 ⟨1, by norm_num [stage1Legal]⟩).1 ≠
      alphaCol stage1Legal cDisagree := by decide
  change rawStageFour stage1Legal widthsWitness.q₂ witnessSource stageTwoWitness
      vWit πWit (Sum.inr ((0 : IWit), true)) cDisagree = false
  rw [rawStageFour_source_neutral_of_disagree stage1Legal widthsWitness.q₂
    witnessSource stageTwoWitness vWit πWit 0 true cDisagree hp]
  rfl

/-- **Candidate B is a different matrix, in the kernel.**  At the legal
disagreeing column and an item active at `alpha_c`, the frozen `B` takes the
neutral value while Candidate B takes the active value, and the two differ.
So dropping the agreement conjunct of `07:565` does not re-encode
`eq:raw-stage4-source-value`; it replaces it. -/
theorem candidateB_ignores_agreement_guard :
    rawStageFourWitness (Sum.inr ((0 : IWit), true)) cDisagree = false ∧
      candidateBSource stage1Legal widthsWitness.q₂ witnessSource
          stageTwoWitness vWit πWit (Sum.inr ((0 : IWit), true)) cDisagree = true ∧
      rawStageFourWitness (Sum.inr ((0 : IWit), true)) cDisagree ≠
        candidateBSource stage1Legal widthsWitness.q₂ witnessSource
          stageTwoWitness vWit πWit (Sum.inr ((0 : IWit), true)) cDisagree := by
  have hB := rawStageFourWitness_both_branches.2
  have hCand :
      candidateBSource stage1Legal widthsWitness.q₂ witnessSource
        stageTwoWitness vWit πWit (Sum.inr ((0 : IWit), true)) cDisagree = true :=
    rfl
  exact ⟨hB, hCand, by rw [hB, hCand]; exact Bool.false_ne_true⟩

/-- **Non-vacuity 4 (the frozen carriers at the witnesses).**  Both carriers
have the exact sizes `eq:raw-stage4-universes` prescribes:
`|Rows(B)| = s N_2 + |I| m_R = 64 * 2 + 2 * 2 = 132` and
`|Cols(B)| = n_R^{s+1} (q_2 n_R^{L_1})^s = 2^65 (128 * 2^191)^64`. -/
theorem rawStageFourWitness_carriers :
    Fintype.card
        (RawRows stage1Legal IWit Bool (Slot paramsWitnessTwo.N₂)) = 132 ∧
      Fintype.card (RawCols stage1Legal widthsWitness.q₂ Bool) =
        2 ^ 65 * (128 * 2 ^ 191) ^ 64 := by
  constructor
  · rw [rawRows_card stage1Legal IWit Bool (Slot paramsWitnessTwo.N₂)]
    rfl
  · rw [rawCols_card stage1Legal widthsWitness.q₂ Bool]
    rfl

end EthInapproximability.ParameterizedNP.RawStageFour
