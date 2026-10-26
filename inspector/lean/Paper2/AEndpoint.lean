import Paper2.A4T24Cut
import Paper2.A4T24RuntimeComposed
import Paper2.A4DocFix
import Paper2.A4Definitions
import Paper2.PublicScheduleSourceSize

/-!
# Paper A (lock v12) final composition: T01 / T02 / T24 endpoints modulo H_A3 and D-A1 .. D-A7

Lane `owner:a-endpoint-1` (private, 26 September 2026). Composition of ADMITTED production
declarations only (every import is in the Paper2 aggregate; no private object is imported here).
No new machine is built: every machine below is a machine of an admitted shell.

Open inputs, each an explicit parameter or hypothesis (none is chosen here):

* `hA3 : Unit4Shell.Shells.H_A3 B.degreeBound (sourceGap D B)` -- the unit-3 endpoint, in exactly the
  form concluded by `A3H3Run.H_A3_R12` (lane a-h-a3-assembly-owner-3; wave15-a21 under admission).
  `AEndpointR12.lean` substitutes the five named specifications for it.
* D-A1 (randomized model): `TM : TapeModel` and `hDA1 : DA1 D B TM` -- the author's admissibility
  predicate for random-tape laws, asserted of the actual experiment laws.
* D-A2 (the 3-CNF language): `L` with `hDA2 : DA2 L` (`DA2_recommended` shows the map's
  recommendation `EncodedCNF.Language` satisfies it).
* D-A3 (estimator interface): the estimator is an arbitrary finite law `μ` and reading `est` of the
  actual reduction tape (strictly more general than any reading of the printed word).
* D-A4 (classes): the error bound `err` and `Unit4Shell.ClassLemmas.ReductionClosed` hypotheses.
* D-A5 (Cook-Levin contract): `NPHard L` as a hypothesis.
* D-A6 (`def:reth` shape): the sparsity density `cs` is a parameter.
* D-A7 (X03/X04 records): the parameters `D`, `B`.

**No ledger row is closed.** The class-level forms of T02/T24 need, in addition, the OPEN machine
composition U18 (the estimator, median and midpoint machine); see the checkpoint.
-/

/- Heartbeat budget for the whole file: the statements quote large admitted objects; the default
   budget times out in whnf on them (and in the end-of-file symbol-frequency pass). A resource
   option, not an axiom. -/
set_option maxHeartbeats 4000000

namespace Paper2.AEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-! Local notations (expanded at parse time, so every statement below is literally in terms of the
admitted objects `TotalFiniteConstructorScratch.select` / `experiment` and
`EncodedSelectedOutput.outputBits` of the T10 graph of `Φ` at gap `k`). -/

set_option hygiene false in
local notation "SEL" Φ:max k:max => TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

set_option hygiene false in
local notation "OUT" Φ:max k:max t:max => EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k t

/-! ## Author decisions as explicit parameters -/

/-- **D-A1 (author decision, NOT taken).** Which finite tape laws, read through which tape words,
are the random tapes of a randomized algorithm. -/
abbrev TapeModel : Type 1 :=
  (τ : Type) → (inst : Fintype τ) → @FiniteLaw τ inst → (τ → List Bool) → Prop

/-- **D-A1 hypothesis on the actual reduction.** Every experiment law of every T10 graph at every
gap `k ≥ 1` is admissible in the author's model `TM`. -/
def DA1 (TM : TapeModel) : Prop :=
  ∀ (Φ : ValidFormula) (k : ℕ), 1 ≤ k →
    TM (EXP Φ k).output.Tape (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw
      (EXP Φ k).output.tapeBits

/-- The option recommended by the unit-4 map for D-A1: the uniform law on the words of one exact
length (a DEFINITION of the option; whether the author selects it is D-A1). -/
def uniformExact : TapeModel := fun τ inst μ bits =>
  ∃ r : ℕ, (∀ t, (bits t).length = r) ∧ Function.Injective bits ∧
    (∀ w : List Bool, w.length = r → ∃ t, bits t = w) ∧
    ∀ t, @FiniteLaw.weight τ inst μ t = (1 / 2 : ℝ) ^ r

/-- **D-A2 (author decision, NOT taken).** The 3-CNF language `L` agrees with satisfiability on
the encodings of valid formulas. -/
def DA2 (L : EncodedComplexity.BinaryLanguage) : Prop :=
  ∀ Φ : ValidFormula, EncodedCNF.encode Φ.val ∈ L ↔ EncodedCNF.Satisfiable Φ.val

/-- The map's D-A2 recommendation (`EncodedCNF.Language`) satisfies `DA2`. -/
theorem DA2_recommended : DA2 EncodedCNF.Language := by
  intro Φ
  constructor
  · rintro ⟨f, hf, hs⟩
    rw [EncodedCNF.decode_encode Φ.val Φ.property] at hf
    cases hf
    exact hs
  · intro hs
    exact ⟨Φ.val, EncodedCNF.decode_encode Φ.val Φ.property, hs⟩

/-! ## Arithmetic -/

theorem pow_le_pow_of_le' {x a b : ℕ} (h : a ≤ b) : (x + 1) ^ a ≤ (x + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos x) h

/-- The composed polynomial of the fixed-`k` T01 machine, in the encoding length `X`. -/
theorem t01_poly (X bits P Q C1 E1 pb o plen : ℕ)
    (hbits : bits ≤ P * (X + 1) ^ Q)
    (hplen : plen = 2 * X + 1 + bits)
    (ho : o ≤ plen + C1 * (plen + 1) ^ E1 * pb) :
    bits ≤ (P + (2 + P) + C1 * (2 + P) ^ E1 * (1 + pb)) * (X + 1) ^ ((Q + 1) * (E1 + 1)) ∧
    C1 * (plen + 1) ^ E1 ≤ (P + (2 + P) + C1 * (2 + P) ^ E1 * (1 + pb)) * (X + 1) ^ ((Q + 1) * (E1 + 1)) ∧
    o ≤ (P + (2 + P) + C1 * (2 + P) ^ E1 * (1 + pb)) * (X + 1) ^ ((Q + 1) * (E1 + 1)) := by
  subst hplen
  set T := C1 * (2 * X + 1 + bits + 1) ^ E1 with hTdef
  have hT : T ≤ C1 * (2 * X + 1 + bits + 1) ^ E1 := le_refl _
  set Y := (X + 1) ^ ((Q + 1) * (E1 + 1)) with hYdef
  set K := C1 * (2 + P) ^ E1 with hK
  have hQ : (X + 1) ^ Q ≤ Y := pow_le_pow_of_le' (by nlinarith)
  have hQ1 : (X + 1) ^ (Q + 1) ≤ Y := pow_le_pow_of_le' (by nlinarith)
  have hQE : (X + 1) ^ ((Q + 1) * E1) ≤ Y := pow_le_pow_of_le' (by nlinarith)
  have h1 : 1 ≤ (X + 1) ^ Q := Nat.one_le_pow _ _ (Nat.succ_pos X)
  have hX1 : X + 1 ≤ (X + 1) ^ (Q + 1) := by
    calc X + 1 = (X + 1) * 1 := by ring
      _ ≤ (X + 1) * (X + 1) ^ Q := Nat.mul_le_mul_left _ h1
      _ = (X + 1) ^ (Q + 1) := by ring
  -- the input length bound
  have hin : 2 * X + 1 + bits + 1 ≤ (2 + P) * (X + 1) ^ (Q + 1) := by
    have hb2 : bits ≤ P * (X + 1) ^ (Q + 1) :=
      hbits.trans (Nat.mul_le_mul_left _ (pow_le_pow_of_le' (by omega)))
    have : (2 + P) * (X + 1) ^ (Q + 1) = 2 * (X + 1) ^ (Q + 1) + P * (X + 1) ^ (Q + 1) := by ring
    rw [this]; omega
  have hTK : T ≤ K * Y := by
    calc T ≤ C1 * (2 * X + 1 + bits + 1) ^ E1 := hT
      _ ≤ C1 * ((2 + P) * (X + 1) ^ (Q + 1)) ^ E1 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hin _)
      _ = K * (X + 1) ^ ((Q + 1) * E1) := by rw [hK, mul_pow, ← pow_mul]; ring
      _ ≤ K * Y := Nat.mul_le_mul_left _ hQE
  have hbY : bits ≤ P * Y := hbits.trans (Nat.mul_le_mul_left _ hQ)
  have hinY : 2 * X + 1 + bits + 1 ≤ (2 + P) * Y := hin.trans (Nat.mul_le_mul_left _ hQ1)
  have hTpb : T * pb ≤ K * pb * Y := by
    calc T * pb ≤ K * Y * pb := Nat.mul_le_mul_right _ hTK
      _ = K * pb * Y := by ring
  have hexp : (P + (2 + P) + K * (1 + pb)) * Y = P * Y + (2 + P) * Y + K * Y + K * pb * Y := by
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hexp]; omega
  · rw [hexp]; omega
  · rw [hexp]; omega

/-! ## T01 -/

/-- T01 YES clause on one tape (from the admitted `selected_yes_cost_le` and `t10_source`). -/
theorem t01_yes (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L) (Φ : ValidFormula) (k : ℕ)
    (t : (SEL Φ k).Tape) :
    EncodedCNF.encode Φ.val ∈ L →
      Workspace.Types.CommComplexity.D ((SEL Φ k).table t).matrix ≤ (SEL Φ k).budget := by
  intro hmem
  have hsat := (hDA2 Φ).mp hmem
  obtain ⟨hm, _, _, hdeg, hloop, hyes, _⟩ := t10_source D B Φ
  have h := TotalFiniteConstructorScratch.selected_yes_cost_le (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
    (sourceGap D B) k hloop hdeg (source_gap_pos D B) B.degreeBound_pos hm (hyes hsat)
  dsimp only at h
  exact h t

/-- T01 NO clause, lock form `Pr[D ≥ budget + k] ≥ 981/1000` (from the admitted exact form
`DocFix.t01_finite_no_exact`). -/
theorem t01_no (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L) (Φ : ValidFormula) (k : ℕ)
    (hk : 1 ≤ k) :
    EncodedCNF.encode Φ.val ∉ L →
      (981 / 1000 : ℝ) ≤ @FiniteLaw.prob _ (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw
        (fun t => (EXP Φ k).output.budget + k ≤
          Workspace.Types.CommComplexity.D ((EXP Φ k).output.table t).matrix) := by
  intro hnot
  have hunsat : ¬ EncodedCNF.Satisfiable Φ.val := fun h => hnot ((hDA2 Φ).mpr h)
  have h := Unit4Shell.DocFix.t01_finite_no_exact D B Φ k hk hunsat
  unfold TotalFiniteConstructorScratch.successProbability at h
  refine le_trans h ?_
  exact @FiniteLaw.prob_mono _ (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw _ _
    (fun t ht => le_of_eq ht.symm)

/-- **T01 endpoint (lock v12 `sections/01-introduction.tex:80-96`, `intro:theorem`), fixed `k`,
modulo `hA3` and D-A1, D-A2, D-A7.** For every fixed `k ≥ 1` there is ONE machine `M` and a
polynomial `C·(X+1)^E` in the encoding length `X = |encode Φ|` (degree depending on `k`) such that
for every valid 3-CNF `Φ`:
* the random tape law is the actual experiment law of the T10 graph, admissible in the author's
  model `TM` (D-A1), with output the selected object `select`;
* the random-bit count `inputBits` is at most `C·(X+1)^E`, and every tape has exactly that many bits;
* on every tape `t`, `M` prints exactly the encoded instance `out … t` (the explicit total matrix
  `table t` with the public integer `budget`) from `pair (encode Φ) (tapeBits t)` within
  `T ≤ C·(X+1)^E` steps, and the printed word has length at most `C·(X+1)^E`;
* YES (`encode Φ ∈ L`): `D(table t) ≤ budget` on EVERY tape;
* NO (`encode Φ ∉ L`): `Pr[D(table) ≥ budget + k] ≥ 981/1000` under the experiment law.
NOT included: the square power-of-two output option (U17 writer composition); malformed inputs. -/
theorem T01_endpoint (TM : TapeModel) (hDA1 : DA1 D B TM)
    (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hA3 : Unit4Shell.Shells.H_A3 B.degreeBound (sourceGap D B)) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (M : BitMachine.Machine) (C E : ℕ), ∀ Φ : ValidFormula,
      TM (EXP Φ k).output.Tape (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw
        (EXP Φ k).output.tapeBits ∧
      (EXP Φ k).output = SEL Φ k ∧
      (SEL Φ k).inputBits ≤ C * ((EncodedCNF.encode Φ.val).length + 1) ^ E ∧
      (∀ t : (SEL Φ k).Tape,
        ((SEL Φ k).tapeBits t).length = (SEL Φ k).inputBits ∧
        (∃ T : ℕ, T ≤ C * ((EncodedCNF.encode Φ.val).length + 1) ^ E ∧
          M.OutputsWithin
            (EncodedComplexity.pair (EncodedCNF.encode Φ.val) ((SEL Φ k).tapeBits t))
            (OUT Φ k t) T) ∧
        (OUT Φ k t).length ≤ C * ((EncodedCNF.encode Φ.val).length + 1) ^ E ∧
        (EncodedCNF.encode Φ.val ∈ L →
          Workspace.Types.CommComplexity.D ((SEL Φ k).table t).matrix ≤ (SEL Φ k).budget)) ∧
      (EncodedCNF.encode Φ.val ∉ L →
        (981 / 1000 : ℝ) ≤ @FiniteLaw.prob _ (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw
          (fun t => (EXP Φ k).output.budget + k ≤
            Workspace.Types.CommComplexity.D ((EXP Φ k).output.table t).matrix)) := by
  obtain ⟨⟨M, C1, E1, hM⟩, -, -⟩ := Unit4Shell.ShellsTight.T01_tight D B hA3 k hk
  obtain ⟨CS, ES, hbits⟩ := Unit4Shell.RandomBits.random_bits_poly D B
  refine ⟨M, CS ^ (160 * (k + 1)) + (2 + CS ^ (160 * (k + 1))) +
      C1 * (2 + CS ^ (160 * (k + 1))) ^ E1 * (1 + M.pushBound),
    (ES * (160 * (k + 1)) + 1) * (E1 + 1), fun Φ => ?_⟩
  obtain ⟨hb, hlen⟩ := hbits Φ k hk
  refine ⟨hDA1 Φ k hk, TotalFiniteConstructorScratch.experiment_output_eq_select _ _ _ _ _, ?_,
    fun t => ?_, ?_⟩
  · -- the random-bit count
    have hY : ((EncodedCNF.encode Φ.val).length + 1) ^ (ES * (160 * (k + 1))) ≤
        ((EncodedCNF.encode Φ.val).length + 1) ^ ((ES * (160 * (k + 1)) + 1) * (E1 + 1)) :=
      pow_le_pow_of_le' (le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ (Nat.succ_pos E1)))
    calc (SEL Φ k).inputBits
        ≤ CS ^ (160 * (k + 1)) * ((EncodedCNF.encode Φ.val).length + 1) ^ (ES * (160 * (k + 1))) := hb
      _ ≤ CS ^ (160 * (k + 1)) *
          ((EncodedCNF.encode Φ.val).length + 1) ^ ((ES * (160 * (k + 1)) + 1) * (E1 + 1)) :=
          Nat.mul_le_mul_left _ hY
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · -- one tape
    have h1 := EncodedComplexity.pair_length (EncodedCNF.encode Φ.val) ((SEL Φ k).tapeBits t)
    have h2 := hlen t
    have hpl := h1.trans (congrArg (fun x => 2 * (EncodedCNF.encode Φ.val).length + 1 + x) h2)
    obtain ⟨-, hT, ho⟩ := t01_poly (EncodedCNF.encode Φ.val).length ((SEL Φ k).inputBits)
      (CS ^ (160 * (k + 1))) (ES * (160 * (k + 1))) C1 E1 M.pushBound
      _ _ hb hpl (BitMachine.output_length_bound M (hM Φ t))
    exact ⟨h2, ⟨_, hT, hM Φ t⟩, ho, t01_yes D B L hDA2 Φ k t⟩
  · exact t01_no D B L hDA2 Φ k hk

/-! ## T02 -/

/-- The fixed integer gap of the T02 proof ("Choose a fixed integer `k>2a`"). -/
noncomputable def gapOf (a : ℝ) : ℕ := ⌊2 * a⌋₊ + 1

theorem gapOf_spec (a : ℝ) (ha : 0 ≤ a) : 1 ≤ gapOf a ∧ 2 * a < (gapOf a : ℝ) := by
  refine ⟨Nat.le_add_left _ _, ?_⟩
  unfold gapOf
  push_cast
  exact Nat.lt_floor_add_one (2 * a)

/-- **T02 endpoint, law level (lock v12 `sections/01-introduction.tex:111-126`, `intro:corollary`
and its proof), modulo D-A2, D-A7; the estimator (D-A1/D-A3) is an arbitrary finite law.**
For every fixed `a ≥ 0` the fixed integer `k = gapOf a` satisfies `1 ≤ k` and `2a < k`, and for
every valid `Φ`, on the ACTUAL experiment law of the T10 graph at gap `k`:
* (bounded-error estimator) every estimator whose estimate of `D(table b)` is within `a` with
  probability `≥ 2/3` for every reduction tape `b` makes the median-of-147 midpoint test
  (`Shells.accepts`, threshold `budget + k/2`) reject a YES input with probability `≤ 1/100` and
  accept a NO input with probability `≤ 2^-11 + 1/100 < 1/3`;
* (always-correct deterministic estimator) every deterministic estimate `e b` within `a` of
  `D(table b)` on every tape makes the test ACCEPT a YES input on EVERY tape (`e b < budget + k/2`)
  and REJECT a NO input with probability `≥ 1 - 2^-11` (`budget + k/2 < e b`): the one-sided
  (`coRP`) shape.
The reduction machine at this `k` is `T01_endpoint … (gapOf a)`. NOT included: the machine that runs
the estimator, the median and the comparison (U18), and the class statements (`T02_class_*`). -/
theorem T02_endpoint_law (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (a : ℝ) (ha : 0 ≤ a) :
    1 ≤ gapOf a ∧ 2 * a < (gapOf a : ℝ) ∧
    ∀ Φ : ValidFormula,
      (∀ {α : Type} [Fintype α] (μ : FiniteLaw α)
          (est : (EXP Φ (gapOf a)).output.Tape → α → ℝ),
        letI : Fintype (EXP Φ (gapOf a)).output.Tape := (EXP Φ (gapOf a)).tapeFintype
        (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t -
          Workspace.Types.CommComplexity.D ((EXP Φ (gapOf a)).output.table b).matrix| ≤ a)) →
        (EncodedCNF.encode Φ.val ∈ L →
          ((EXP Φ (gapOf a)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
            (fun x => ¬ Unit4Shell.Shells.accepts est (EXP Φ (gapOf a)).output.budget (gapOf a) x)
            ≤ 1 / 100) ∧
        (EncodedCNF.encode Φ.val ∉ L →
          ((EXP Φ (gapOf a)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
            (fun x => Unit4Shell.Shells.accepts est (EXP Φ (gapOf a)).output.budget (gapOf a) x)
            ≤ (1 / 2) ^ 11 + 1 / 100 ∧ (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3)) ∧
      (∀ e : (EXP Φ (gapOf a)).output.Tape → ℝ,
        (∀ b, |e b - Workspace.Types.CommComplexity.D ((EXP Φ (gapOf a)).output.table b).matrix|
          ≤ a) →
        (EncodedCNF.encode Φ.val ∈ L → ∀ b,
          e b < ((EXP Φ (gapOf a)).output.budget : ℝ) + (gapOf a : ℝ) / 2) ∧
        (EncodedCNF.encode Φ.val ∉ L →
          1 - (1 / 2 : ℝ) ^ 11 ≤ @FiniteLaw.prob _ (EXP Φ (gapOf a)).tapeFintype
            (EXP Φ (gapOf a)).tapeLaw
            (fun b => ((EXP Φ (gapOf a)).output.budget : ℝ) + (gapOf a : ℝ) / 2 < e b))) := by
  obtain ⟨hk, hka⟩ := gapOf_spec a ha
  refine ⟨hk, hka, fun Φ => ⟨?_, ?_⟩⟩
  · intro α _ μ est hμ
    have h := Unit4Shell.T24Actual.T02_actual D B (gapOf a) hk a hka Φ μ est hμ
    exact ⟨fun hmem => h.1 ((hDA2 Φ).mp hmem),
      fun hnot => h.2 (fun hs => hnot ((hDA2 Φ).mpr hs))⟩
  · intro e he
    obtain ⟨hm, _, _, hdeg, hloop, hyes, hno⟩ := t10_source D B Φ
    refine ⟨fun hmem b => ?_, fun hnot => ?_⟩
    · have hc := Unit4Shell.T24Actual.actual_yes_cost (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
        (sourceGap D B) (gapOf a) hloop hdeg (source_gap_pos D B) B.degreeBound_pos hm
        (hyes ((hDA2 Φ).mp hmem)) b
      exact Unit4Shell.Amplification.midpoint_yes_real (e b) a _ _ (gapOf a) hc (he b) hka
    · have hunsat : ¬ EncodedCNF.Satisfiable Φ.val := fun hs => hnot ((hDA2 Φ).mpr hs)
      have hmass := Unit4Shell.T24Actual.actual_no_mass (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
        (sourceGap D B) (gapOf a) hk hloop hdeg (source_gap_pos D B) B.degreeBound_pos hm
        (hno hunsat)
      letI := (EXP Φ (gapOf a)).tapeFintype
      rw [Unit4Shell.Amplification.prob_not] at hmass
      have hmono := FiniteLaw.prob_mono (EXP Φ (gapOf a)).tapeLaw
        (E := fun b => Workspace.Types.CommComplexity.D ((EXP Φ (gapOf a)).output.table b).matrix =
          (EXP Φ (gapOf a)).output.budget + gapOf a)
        (F := fun b => ((EXP Φ (gapOf a)).output.budget : ℝ) + (gapOf a : ℝ) / 2 < e b)
        (fun b hb => by
          have h1 := he b
          rw [hb] at h1
          exact Unit4Shell.Amplification.midpoint_no_real (e b) a _ (gapOf a) h1 hka)
      linarith

/-- **T02, class level (first clause), from the law level: `NP ⊆ C`.** For the author's class `C`
(D-A4), closed under the banked reductions (named hypothesis; every D-A4 option must prove it), the
Cook-Levin contract `NPHard L` (D-A5), and the OPEN realization premise `hU18 : C L` (the midpoint
test of `T02_endpoint_law`, run as ONE polynomial machine with the estimator, is a `C`-algorithm for
`L`: U18 machine composition + D-A1/D-A3/D-A4; no lane yet), every `InNP` language is in `C`.
Exact reuse of the admitted `DocFix.np_subset_of_hard_mem`. -/
theorem T02_class_bpp (L : EncodedComplexity.BinaryLanguage)
    (C : EncodedComplexity.BinaryLanguage → Prop) (hC : Unit4Shell.ClassLemmas.ReductionClosed C)
    (hCL : EncodedComplexity.NPHard L) (hU18 : C L) :
    ∀ L', EncodedComplexity.InNP L' → C L' :=
  Unit4Shell.DocFix.np_subset_of_hard_mem C hC hCL hU18

/-- **T02, class level (second clause): `NP = coNP`.** From the one-sided normal form of `L`
(`OneSidedRejectShape L`, the OPEN realization premise of the deterministic-estimator clause of
`T02_endpoint_law`: U18 + D-A1/D-A3), the Cook-Levin contract `NPHard L` (D-A5) and the reduction
closure of `InNP` (named machine-level hypothesis): `NPEqCoNP`. Exact reuse of the admitted
`DocFix.coNP_of_oneSided` and `DocFix.np_eq_coNP_of_hard_mem_coNP`. -/
theorem T02_class_coNP (L : EncodedComplexity.BinaryLanguage)
    (hNP : Unit4Shell.ClassLemmas.ReductionClosed EncodedComplexity.InNP)
    (hCL : EncodedComplexity.NPHard L)
    (hU18 : Unit4Shell.ClassLemmas.OneSidedRejectShape L) :
    Unit4Shell.ClassLemmas.NPEqCoNP :=
  Unit4Shell.DocFix.np_eq_coNP_of_hard_mem_coNP hNP hCL (Unit4Shell.DocFix.coNP_of_oneSided hU18)

/-! ## T24 -/

/-- The printed entry count is the scheduled count beyond the public-check cutoff: for every valid
`Φ` whose T10 graph has at least `sizeThreshold` vertices, `rows·cols = printedT` and the square
padding has `printedTsq` entries (predecessor audit note N-1, for the T10 source). -/
theorem entries_eq_printed (Φ : ValidFormula) (k : ℕ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B) ≤
      (t10Graph D B Φ).vertices) :
    (SEL Φ k).rows * (SEL Φ k).cols =
        printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
          (sourceGap D B) k ∧
    SquarePadding.entries (SEL Φ k).rows (SEL Φ k).cols =
        printedTsq (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
          (sourceGap D B) k := by
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  haveI : Nonempty (Fin (t10Graph D B Φ).vertices) := ⟨⟨0, t10_vertices_pos D B Φ⟩⟩
  have hc := CompletePublicScheduleScratch.all_large_checks_at_graph
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
    (sourceGap D B) (source_gap_pos D B) B.degreeBound_pos hinc hdeg
    (by rw [Fintype.card_fin]; exact hsize)
  rw [Fintype.card_fin] at hc
  rw [TotalFiniteConstructorScratch.select_good _ _ _ _ _ hc]
  exact ⟨rfl, rfl⟩

/-- Beyond `N ≥ Δ·sizeThreshold` the T10 graph of every valid `Φ` passes the size threshold. -/
theorem size_of_large (Φ : ValidFormula)
    (hN : B.degreeBound * CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B)
      ≤ Φ.val.variables) :
    CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B) ≤
      (t10Graph D B Φ).vertices := by
  obtain ⟨hNm, hmn, _⟩ := Unit4Shell.T10Size.t45_relations D B Φ
  have hΔ : 0 < B.degreeBound := B.degreeBound_pos
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have h1 : B.degreeBound * (t10Graph D B Φ).vertices <
      B.degreeBound * CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B) :=
    Nat.mul_lt_mul_of_pos_left hlt hΔ
  omega

/-- **T24 endpoint, reduction and law level (lock v12 `sections/06-reduction.tex:107-153`,
`thm:quantitative`), modulo `hA3`, D-A2, D-A6 (the sparsity density `cs`), D-A7; the estimator
(D-A1/D-A3) is an arbitrary finite law.** For every fixed `0 ≤ c < 1/12` and both output shapes
(`square`), there is ONE machine `M` such that for every `ε > 0` there is a cutoff `N₀`, and for
every valid sparse `Φ` (`clauses ≤ cs·N`, `N = Φ.variables ≥ N₀`), with `k = kOf N = ⌊N/⌈log N⌉²⌋`
computed by `M` itself:
* `1 ≤ k`; the random-bit count is `≤ 2^(εN)`; on every tape `M` prints exactly the reduction's
  word within `T ≤ 2^(εN)` steps;
* the printed table has exactly `printedT` entries (`rows·cols`), and its square padding exactly
  `printedTsq`;
* with `T` that count (rectangular or square) and `a = c·log₂T / log₂log₂T`, every estimator with
  per-run accuracy `a` with probability `≥ 2/3` makes the median midpoint test at gap `k` err with
  probability `≤ 1/100` on YES and `≤ 2^-11 + 1/100 < 1/3` on NO, on the ACTUAL reduction law.
NOT included: the D04 contradiction (needs the U18 machine running estimator + median + midpoint
within `2^(εN)`, and D-A6's formal `RandomizedSparseETH` shape). -/
theorem T24_endpoint (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hA3 : Unit4Shell.Shells.H_A3 B.degreeBound (sourceGap D B))
    (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) (square : Bool) :
    ∃ M : BitMachine.Machine, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables → N₀ ≤ Φ.val.variables →
      1 ≤ kOf Φ.val.variables ∧
      ((SEL Φ (kOf Φ.val.variables)).inputBits : ℝ) ≤ (2 : ℝ) ^ (ε * Φ.val.variables) ∧
      (∀ t : (SEL Φ (kOf Φ.val.variables)).Tape, ∃ T : ℕ,
        M.OutputsWithin
          (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
            ((SEL Φ (kOf Φ.val.variables)).tapeBits t))
          (OUT Φ (kOf Φ.val.variables) t) T ∧
        (T : ℝ) ≤ (2 : ℝ) ^ (ε * Φ.val.variables)) ∧
      (SEL Φ (kOf Φ.val.variables)).rows * (SEL Φ (kOf Φ.val.variables)).cols =
        printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
          (sourceGap D B) (kOf Φ.val.variables) ∧
      SquarePadding.entries (SEL Φ (kOf Φ.val.variables)).rows
          (SEL Φ (kOf Φ.val.variables)).cols =
        printedTsq (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
          (sourceGap D B) (kOf Φ.val.variables) ∧
      let T : ℕ := if square then
          printedTsq (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
            (sourceGap D B) (kOf Φ.val.variables)
        else printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
            (sourceGap D B) (kOf Φ.val.variables)
      let a : ℝ := c * (Real.logb 2 T / Real.logb 2 (Real.logb 2 T))
      ∀ {α : Type} [Fintype α] (μ : FiniteLaw α)
        (est : (EXP Φ (kOf Φ.val.variables)).output.Tape → α → ℝ),
        letI : Fintype (EXP Φ (kOf Φ.val.variables)).output.Tape :=
          (EXP Φ (kOf Φ.val.variables)).tapeFintype
        (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - Workspace.Types.CommComplexity.D
          ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix| ≤ a)) →
        (EncodedCNF.encode Φ.val ∈ L →
          ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
            (fun x => ¬ Unit4Shell.Shells.accepts est (EXP Φ (kOf Φ.val.variables)).output.budget
              (kOf Φ.val.variables) x) ≤ 1 / 100) ∧
        (EncodedCNF.encode Φ.val ∉ L →
          ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
            (fun x => Unit4Shell.Shells.accepts est (EXP Φ (kOf Φ.val.variables)).output.budget
              (kOf Φ.val.variables) x) ≤ (1 / 2) ^ 11 + 1 / 100 ∧
          (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) := by
  obtain ⟨M, hM⟩ := Unit4Shell.T24RuntimeComposed.T24_runtime D B hA3 cs
  obtain ⟨N₁, hN₁⟩ := Unit4Shell.T24ActualCut.T24_actual_cut D B cs c hc0 hc square
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨N₂, hN₂⟩ := hM ε hε
  refine ⟨max (max N₁ N₂) (B.degreeBound *
    CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B)), ?_⟩
  intro Φ hsparse hN
  have hN1 : N₁ ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 := le_trans (le_max_right _ _) hN
  obtain ⟨hk, hbits, hrun⟩ := hN₂ Φ hsparse hN2
  have hent := entries_eq_printed D B Φ (kOf Φ.val.variables) (size_of_large D B Φ hN3)
  refine ⟨hk, hbits, hrun, hent.1, hent.2, ?_⟩
  intro T a α _ μ est
  have hmain := hN₁ Φ hsparse hN1 μ est
  intro hμ
  have h := hmain hμ
  exact ⟨fun hmem => h.1 ((hDA2 Φ).mp hmem), fun hnot => h.2 (fun hs => hnot ((hDA2 Φ).mpr hs))⟩

#print axioms DA2_recommended
#print axioms t01_poly
#print axioms t01_yes
#print axioms t01_no
#print axioms T01_endpoint
#print axioms gapOf_spec
#print axioms T02_endpoint_law
#print axioms T02_class_bpp
#print axioms T02_class_coNP
#print axioms entries_eq_printed
#print axioms size_of_large
#print axioms T24_endpoint

end Paper2.AEndpoint
