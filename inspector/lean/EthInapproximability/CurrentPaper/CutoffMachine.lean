import EthInapproximability.CurrentPaper.ClockedPadding
import EthInapproximability.CurrentPaper.EffectiveIteration
import EthInapproximability.CurrentPaper.BitMachine

/-!
# An encoded search for the paper's polynomial-versus-exponential cutoffs

Source: locked v8 `F-parameter-choices.tex`, the paragraph beginning
"To obtain a persistent cutoff", and `05-iteration.tex`,
`thm:paper-effective-level` and `eq:paper-slow-clock`.

The coefficient program below is finite arithmetic syntax, not a function
oracle returning a cutoff. The search tests successive integers and halts
only when all literal inequalities pass. Its state has an explicit natural
number encoding. The current coefficient recurrence is encoded literally.
A transition currently executes a whole arithmetic test; lowering that test
to bit-level transitions is a separate obligation. Consequently SlowClock's
transition count is not a polynomial bit-time bound for this evaluator.
-/

namespace EthInapproximability.CurrentPaper.CutoffMachine

/-- Finite arithmetic syntax for coefficient formulas. `level` is the
requested prefix length and `index` ranges over its individual levels. -/
inductive Expr where
  | literal : ℕ → Expr
  | level : Expr
  | index : Expr
  | accumulator : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | max : Expr → Expr → Expr
  | clog : Expr → Expr
  | recurse : Expr → Expr → Expr → Expr
  deriving DecidableEq

def Expr.eval (k j acc : ℕ) : Expr → ℕ
  | .literal a => a
  | .level => k
  | .index => j
  | .accumulator => acc
  | .add a b => a.eval k j acc + b.eval k j acc
  | .mul a b => a.eval k j acc * b.eval k j acc
  | .pow a b => a.eval k j acc ^ b.eval k j acc
  | .div a b => a.eval k j acc / b.eval k j acc
  | .max a b => Nat.max (a.eval k j acc) (b.eval k j acc)
  | .clog a => Nat.clog 2 (a.eval k j acc)
  | .recurse seed count body =>
    Nat.rec (seed.eval k j acc) (fun i previous => body.eval k i previous)
      (count.eval k j acc)

/-- Public finite code, without proof or target-conclusion fields. -/
structure Program where
  fixed : List (Expr × Expr)
  perLevel : List (Expr × Expr)
  deriving DecidableEq

def Program.coefficients (P : Program) (k : ℕ) : List (ℕ × ℕ) :=
  P.fixed.map (fun p => (p.1.eval k 0 0, p.2.eval k 0 0)) ++
    (List.range k).flatMap (fun j =>
      P.perLevel.map (fun p => (p.1.eval k j 0, p.2.eval k j 0)))

/-- Literal primitive-recursion code for the paper's degree recurrence. -/
def degreeExpr : Expr := .recurse (.literal 4) .index
  (.add (.mul (.literal 8) .accumulator) (.literal 100))

theorem degreeExpr_eval (k j acc : ℕ) :
    degreeExpr.eval k j acc = EffectiveIteration.degree j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change 8 * degreeExpr.eval k j acc + 100 = EffectiveIteration.degree (j + 1)
    rw [ih, EffectiveIteration.degree_succ]

/-- Literal code for the proved fixed-level scale coefficient recurrence. -/
def coefficientExpr (C : ℕ) : Expr := .recurse (.literal C) .index
  (.add (.mul (.literal 400000000) (.pow .accumulator (.literal 4))) (.literal 7))

theorem coefficientExpr_eval (C k j acc : ℕ) :
    (coefficientExpr C).eval k j acc = EffectiveIteration.coefficient C j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change 400000000 * (coefficientExpr C).eval k j acc ^ 4 + 7 =
      EffectiveIteration.coefficient C (j + 1)
    rw [ih, EffectiveIteration.coefficient_succ]

/-- The finite code checks all levels below the requested level. The extra
`2*k+1` term is the size-budget margin used alongside acceptance. -/
def iterationProgram (C : ℕ) : Program where
  fixed := []
  perLevel := [(
    .add (.add
      (.mul (.literal 500000000) (.pow (.add (coefficientExpr C) (.literal 1)) (.literal 4)))
      (.mul (.literal 2) .level)) (.literal 1),
    .mul (.literal 4) degreeExpr)]

theorem iterationProgram_coefficients (C k : ℕ) :
    (iterationProgram C).coefficients k = (List.range k).map (fun i =>
      (EffectiveIteration.acceptanceCoefficient (EffectiveIteration.coefficient C i) +
        2 * k + 1, 4 * EffectiveIteration.degree i)) := by
  simp [Program.coefficients, iterationProgram, Expr.eval, coefficientExpr_eval,
    degreeExpr_eval, EffectiveIteration.acceptanceCoefficient]
  rw [← List.map_eq_flatMap]

/-- The exact integer check stated in the eventual-validity paragraph. -/
def test (A d v : ℕ) : Bool := decide (2 * d ≤ v ∧ A * (v + 1) ^ d ≤ 2 ^ v)

def passes (P : Program) (k v : ℕ) : Bool :=
  (P.coefficients k).all (fun p => test p.1 p.2 v)

theorem passes_iff (P : Program) (k v : ℕ) :
    passes P k v = true ↔
      ∀ p ∈ P.coefficients k, 2 * p.2 ≤ v ∧ p.1 * (v + 1) ^ p.2 ≤ 2 ^ v := by
  simp [passes, List.all_eq_true, test]

theorem iterationProgram_passes_iff (C k v : ℕ) :
    passes (iterationProgram C) k v = true ↔
      ∀ i < k, EffectiveIteration.CutoffTest
        (EffectiveIteration.acceptanceCoefficient (EffectiveIteration.coefficient C i) +
          2 * k + 1) (4 * EffectiveIteration.degree i) v := by
  rw [passes_iff, iterationProgram_coefficients]
  simp [EffectiveIteration.CutoffTest]

/-- A finite witness used to prove termination; the search itself never
evaluates or jumps to this witness. -/
def successfulBound (P : Program) (k : ℕ) : ℕ :=
  max (2 * k) ((P.coefficients k).map
    (fun p => EffectiveIteration.cutoffWitness p.1 p.2)).sum

theorem successfulBound_spec (P : Program) (k : ℕ) :
    2 * k ≤ successfulBound P k ∧ passes P k (successfulBound P k) = true := by
  refine ⟨le_max_left _ _, (passes_iff _ _ _).mpr ?_⟩
  intro p hp
  apply EffectiveIteration.cutoffTest_persistent
    (EffectiveIteration.cutoffWitness_spec p.1 p.2)
  apply le_trans _ (le_max_right _ _)
  apply List.single_le_sum (fun x hx => Nat.zero_le x)
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem passes_persistent (P : Program) {k v w : ℕ}
    (h : passes P k v = true) (hvw : v ≤ w) : passes P k w = true := by
  apply (passes_iff _ _ _).mpr
  intro p hp
  exact EffectiveIteration.cutoffTest_persistent ((passes_iff _ _ _).mp h p hp) hvw

theorem failure_lt_successfulBound (P : Program) {k v : ℕ}
    (h : ¬ passes P k v = true) : v < successfulBound P k := by
  by_contra hv
  exact h (passes_persistent P (successfulBound_spec P k).2 (by omega))

/-- An executable unbounded search whose totality is justified by the
proved finite arithmetic witness. The witness occurs only in the termination
argument; it is not evaluated by this search. -/
def searchCandidate (P : Program) (k v : ℕ) : ℕ :=
  if h : passes P k v = true then v else searchCandidate P k (v + 1)
termination_by successfulBound P k - v
decreasing_by
  have hv := failure_lt_successfulBound P h
  omega

theorem searchCandidate_spec (P : Program) (k v : ℕ) :
    v ≤ searchCandidate P k v ∧ passes P k (searchCandidate P k v) = true := by
  rw [searchCandidate]
  split
  · exact ⟨le_rfl, ‹_›⟩
  · have h := searchCandidate_spec P k (v + 1)
    exact ⟨by omega, h.2⟩
termination_by successfulBound P k - v
decreasing_by
  have hv := failure_lt_successfulBound P ‹¬ passes P k v = true›
  omega

/-- The explicit total source-cutoff function associated with a finite
coefficient program. Its relation to the current iteration's full list of
size requirements still has to be proved for the concrete program. -/
def computeCutoff (P : Program) (k : ℕ) : ℕ :=
  EffectiveIteration.sourceThreshold (searchCandidate P k (2 * k))

structure State where
  level : ℕ
  candidate : ℕ
  halted : Bool
  deriving DecidableEq

def initial (k : ℕ) : State := ⟨k, 2 * k, false⟩

def step (P : Program) (s : State) : State :=
  if s.halted then s
  else if passes P s.level s.candidate then {s with halted := true}
  else {s with candidate := s.candidate + 1}

def output (s : State) : Option ℕ := if s.halted then some s.candidate else none

def machine (P : Program) : SlowClock.Machine State where
  initial := initial
  step := step P
  output := output
  halted := by
    intro s u hu
    cases h : s.halted <;> simp [output, h] at hu
    simp [step, h]

theorem step_level (P : Program) (s : State) : (step P s).level = s.level := by
  unfold step
  split <;> simp_all
  split <;> rfl

def Valid (P : Program) (s : State) : Prop :=
  2 * s.level ≤ s.candidate ∧
    (s.halted = true → passes P s.level s.candidate = true)

theorem initial_valid (P : Program) (k : ℕ) : Valid P (initial k) := by
  simp [Valid, initial]

theorem step_valid (P : Program) (s : State) (hs : Valid P s) : Valid P (step P s) := by
  unfold step
  split
  · exact hs
  · split
    · simp_all [Valid]
    · simp_all [Valid]
      omega

theorem run_valid (P : Program) (fuel k : ℕ) :
    Valid P (SlowClock.run (machine P) fuel k) := by
  induction fuel with
  | zero => exact initial_valid P k
  | succ fuel ih =>
    change Valid P (((step P)^[fuel + 1]) (initial k))
    rw [Function.iterate_succ_apply']
    exact step_valid P _ ih

theorem run_level (P : Program) (fuel k : ℕ) :
    (SlowClock.run (machine P) fuel k).level = k := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change (((step P)^[fuel + 1]) (initial k)).level = k
    rw [Function.iterate_succ_apply', step_level]
    exact ih

theorem output_correct (P : Program) {fuel k u : ℕ}
    (h : (machine P).output (SlowClock.run (machine P) fuel k) = some u) :
    2 * k ≤ u ∧ passes P k u = true := by
  have hv := run_valid P fuel k
  have hl := run_level P fuel k
  change output _ = some u at h
  unfold output at h
  split at h
  · simp only [Option.some.injEq] at h
    have hp := hv.2 ‹_›
    unfold Valid at hv
    rw [hl, h] at hv hp
    exact ⟨hv.1, hp⟩
  · contradiction

/-- Search termination is proved by descending distance to a successful
candidate; no final output is installed in the machine in advance. -/
theorem search_halts (P : Program) (k start distance : ℕ)
    (hw : passes P k (start + distance) = true) :
    ∃ fuel, fuel ≤ distance + 1 ∧
      output (((step P)^[fuel]) ⟨k, start, false⟩) ≠ none := by
  induction distance generalizing start with
  | zero =>
    refine ⟨1, le_rfl, ?_⟩
    simp only [Nat.add_zero] at hw
    simp [step, output, hw]
  | succ distance ih =>
    by_cases hs : passes P k start = true
    · refine ⟨1, by omega, ?_⟩
      simp [step, output, hs]
    · obtain ⟨fuel, hf, hh⟩ := ih (start + 1) (by simpa [Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hw)
      refine ⟨fuel + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      simpa [step, hs] using hh

theorem searchCandidate_reached (P : Program) (k v : ℕ) :
    ∃ fuel, output (((step P)^[fuel]) ⟨k, v, false⟩) =
      some (searchCandidate P k v) := by
  rw [searchCandidate]
  split
  · refine ⟨1, ?_⟩
    simp [step, output, ‹passes P k v = true›]
  · obtain ⟨fuel, hf⟩ := searchCandidate_reached P k (v + 1)
    refine ⟨fuel + 1, ?_⟩
    rw [Function.iterate_succ_apply]
    simpa [step, ‹¬ passes P k v = true›] using hf
termination_by successfulBound P k - v
decreasing_by
  have hv := failure_lt_successfulBound P ‹¬ passes P k v = true›
  omega

theorem terminates_of_successful_tests (P : Program)
    (hex : ∀ k, 1 ≤ k → ∃ v, 2 * k ≤ v ∧ passes P k v = true) :
    SlowClock.Terminates (machine P) := by
  intro k hk
  obtain ⟨v, hv, hp⟩ := hex k hk
  obtain ⟨fuel, _, hf⟩ := search_halts P k (2 * k) (v - 2 * k)
    (by simpa [Nat.add_sub_of_le hv] using hp)
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hf
  exact ⟨fuel, u, hu⟩

/-- The pair encoding includes every register and the halt flag. -/
def encode (s : State) : ℕ := Nat.pair s.level (Nat.pair s.candidate (if s.halted then 1 else 0))

def decode (n : ℕ) : State :=
  ⟨n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2 != 0⟩

theorem decode_encode (s : State) : decode (encode s) = s := by
  cases s with
  | mk k v halted => cases halted <;> simp [decode, encode]

def encodedStep (P : Program) (n : ℕ) : ℕ :=
  if (decode n).halted then n else encode (step P (decode n))

def encodedOutput (n : ℕ) : Option ℕ := output (decode n)

def encodedMachine (P : Program) : SlowClock.Machine ℕ where
  initial k := encode (initial k)
  step := encodedStep P
  output := encodedOutput
  halted := by
    intro s u hu
    change output (decode s) = some u at hu
    cases h : (decode s).halted <;> simp [output, h] at hu
    simp [encodedStep, h]

theorem encodedStep_encode (P : Program) (s : State) :
    encodedStep P (encode s) = encode (step P s) := by
  simp only [encodedStep, decode_encode]
  by_cases hs : s.halted = true <;> simp [step, hs]

theorem encoded_run (P : Program) (fuel k : ℕ) :
    SlowClock.run (encodedMachine P) fuel k =
      encode (SlowClock.run (machine P) fuel k) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [SlowClock.run, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    exact encodedStep_encode P _

theorem encoded_output_correct (P : Program) {fuel k u : ℕ}
    (h : (encodedMachine P).output (SlowClock.run (encodedMachine P) fuel k) = some u) :
    2 * k ≤ u ∧ passes P k u = true := by
  apply output_correct P (fuel := fuel)
  change output (decode (SlowClock.run (encodedMachine P) fuel k)) = some u at h
  rw [encoded_run, decode_encode] at h
  exact h

theorem encoded_terminates_of_successful_tests (P : Program)
    (hex : ∀ k, 1 ≤ k → ∃ v, 2 * k ≤ v ∧ passes P k v = true) :
    SlowClock.Terminates (encodedMachine P) := by
  intro k hk
  obtain ⟨fuel, u, hu⟩ := terminates_of_successful_tests P hex k hk
  refine ⟨fuel, u, ?_⟩
  change output (decode (SlowClock.run (encodedMachine P) fuel k)) = some u
  rw [encoded_run, decode_encode]
  exact hu

theorem encoded_doubledCutoffs (P : Program) :
    ClockedPadding.DoubledCutoffs (encodedMachine P) := by
  intro fuel k u _ hout
  exact (encoded_output_correct P hout).1

theorem encoded_terminates (P : Program) : SlowClock.Terminates (encodedMachine P) := by
  apply encoded_terminates_of_successful_tests
  intro k _
  exact ⟨successfulBound P k, successfulBound_spec P k⟩

/-- Every returned cutoff validates all later candidates for every
coefficient pair generated by the literal finite program. -/
theorem encoded_output_persistent (P : Program) {fuel k u : ℕ}
    (h : (encodedMachine P).output (SlowClock.run (encodedMachine P) fuel k) = some u)
    (w : ℕ) (huw : u ≤ w) : passes P k w = true :=
  passes_persistent P (encoded_output_correct P h).2 huw

theorem encoded_allowance_unbounded (P : Program) : ∀ K, ∃ T,
    K ≤ FinalPadding.allowance (SlowClock.repetitions (encodedMachine P)) T :=
  ClockedPadding.allowance_unbounded _ (encoded_terminates P)

theorem encoded_exponent_eventually_pos (P : Program) :
    ∀ᶠ n in Filter.atTop,
      0 < FinalPadding.exponent (SlowClock.repetitions (encodedMachine P)) n :=
  ClockedPadding.exponent_eventually_pos _ (encoded_terminates P) (encoded_doubledCutoffs P)

theorem encoded_exponent_ratio_tendsto_zero (P : Program) :
    Filter.Tendsto
      (fun n => (FinalPadding.exponent (SlowClock.repetitions (encodedMachine P)) n : ℝ) / n)
      Filter.atTop (nhds 0) :=
  ClockedPadding.exponent_ratio_tendsto_zero _ (encoded_terminates P)

/-- The explicit scale-to-source conversion. Output computation is still
arithmetic here and has not been compiled to bit transitions. -/
def sourceMachine (P : Program) : SlowClock.Machine ℕ where
  initial := (encodedMachine P).initial
  step := (encodedMachine P).step
  output s := (encodedMachine P).output s |>.map EffectiveIteration.sourceThreshold
  halted := by
    intro s u hu
    cases h : (encodedMachine P).output s with
    | none => simp [h] at hu
    | some v => exact (encodedMachine P).halted s v h

theorem source_run (P : Program) (fuel k : ℕ) :
    SlowClock.run (sourceMachine P) fuel k =
      SlowClock.run (encodedMachine P) fuel k := rfl

theorem source_output_correct (P : Program) {fuel k u : ℕ}
    (h : (sourceMachine P).output (SlowClock.run (sourceMachine P) fuel k) = some u) :
    ∃ v, EffectiveIteration.sourceThreshold v = u ∧
      2 * k ≤ v ∧ passes P k v = true := by
  change ((encodedMachine P).output (SlowClock.run (encodedMachine P) fuel k)).map
    EffectiveIteration.sourceThreshold = some u at h
  cases hv : (encodedMachine P).output (SlowClock.run (encodedMachine P) fuel k) with
  | none => simp [hv] at h
  | some v =>
    simp only [hv, Option.map_some, Option.some.injEq] at h
    exact ⟨v, h, encoded_output_correct P hv⟩

theorem source_terminates (P : Program) : SlowClock.Terminates (sourceMachine P) := by
  intro k hk
  obtain ⟨fuel, u, hu⟩ := encoded_terminates P k hk
  refine ⟨fuel, EffectiveIteration.sourceThreshold u, ?_⟩
  change ((encodedMachine P).output (SlowClock.run (encodedMachine P) fuel k)).map
    EffectiveIteration.sourceThreshold = some (EffectiveIteration.sourceThreshold u)
  rw [hu]
  rfl

theorem sourceMachine_computes (P : Program) (k : ℕ) :
    ∃ fuel, (sourceMachine P).output (SlowClock.run (sourceMachine P) fuel k) =
      some (computeCutoff P k) := by
  obtain ⟨fuel, hf⟩ := searchCandidate_reached P k (2 * k)
  refine ⟨fuel, ?_⟩
  have hraw : (encodedMachine P).output (SlowClock.run (encodedMachine P) fuel k) =
      some (searchCandidate P k (2 * k)) := by
    change output (decode (SlowClock.run (encodedMachine P) fuel k)) = _
    rw [encoded_run, decode_encode]
    exact hf
  change ((encodedMachine P).output (SlowClock.run (encodedMachine P) fuel k)).map
    EffectiveIteration.sourceThreshold = some (computeCutoff P k)
  rw [hraw]
  rfl

theorem source_doubledCutoffs (P : Program) :
    ClockedPadding.DoubledCutoffs (sourceMachine P) := by
  intro fuel k u _ h
  obtain ⟨v, hu, hv, _⟩ := source_output_correct P h
  rw [← hu]
  apply hv.trans
  exact (Nat.le_of_lt (Nat.lt_two_pow_self (n := v))).trans
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := 2 ^ v)))

/-- The returned source cutoff validates the actual lower binary-log scale
at every later source length. -/
theorem source_output_persistent (P : Program) {fuel k u n : ℕ}
    (h : (sourceMachine P).output (SlowClock.run (sourceMachine P) fuel k) = some u)
    (hun : u ≤ n) : passes P k (EffectiveIteration.sourceLog n) = true := by
  obtain ⟨v, hu, _, hp⟩ := source_output_correct P h
  exact passes_persistent P hp (EffectiveIteration.sourceLog_ge_of_threshold
    (by simpa [hu] using hun))

theorem selected_source_tests (P : Program) (n k : ℕ)
    (hk : 1 ≤ k) (hselected : k ≤ SlowClock.repetitions (sourceMachine P) n) :
    passes P k (EffectiveIteration.sourceLog n) = true := by
  obtain ⟨u, hu, hun⟩ := SlowClock.selected_run (sourceMachine P) n k hk hselected
  exact source_output_persistent P hu hun

/-- The selected clock prefix supplies the actual finite tests for every
iteration in that prefix, rather than an assumed cutoff-correctness oracle. -/
theorem selected_iteration_tests (C n k : ℕ) (hk : 1 ≤ k)
    (hselected : k ≤ SlowClock.repetitions (sourceMachine (iterationProgram C)) n) :
    ∀ i < k, EffectiveIteration.CutoffTest
      (EffectiveIteration.acceptanceCoefficient (EffectiveIteration.coefficient C i) +
        2 * k + 1) (4 * EffectiveIteration.degree i) (EffectiveIteration.sourceLog n) :=
  (iterationProgram_passes_iff C k _).mp
    (selected_source_tests (iterationProgram C) n k hk hselected)

/-- Actual selected levels satisfy the current constructor's acceptance and
strict size tests. The source graph's numerical package remains explicit;
there are no supplied per-level acceptance or size conclusions. This is a
mathematical correctness theorem for the macro search, not a bit-time bound. -/
theorem selected_indexing_levels
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (c A d n k : ℕ)
    (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hselected : k ≤ SlowClock.repetitions
      (sourceMachine (iterationProgram (EffectiveIteration.initialCoefficient c A d))) n) :
    ∀ i < k,
      Parameters.Accepted (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) i) ∧
      2 * k * EffectiveIteration.oneLevelBound
        (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) i) < n := by
  apply EffectiveIteration.run_indexing_of_tests G c A d n k hn hv hlower hupper
  simpa only [EffectiveIteration.sizeTestCoefficient] using
    selected_iteration_tests (EffectiveIteration.initialCoefficient c A d) n k hk hselected

theorem source_allowance_unbounded (P : Program) : ∀ K, ∃ T,
    K ≤ FinalPadding.allowance (SlowClock.repetitions (sourceMachine P)) T :=
  ClockedPadding.allowance_unbounded _ (source_terminates P)

theorem source_exponent_eventually_pos (P : Program) :
    ∀ᶠ n in Filter.atTop,
      0 < FinalPadding.exponent (SlowClock.repetitions (sourceMachine P)) n :=
  ClockedPadding.exponent_eventually_pos _ (source_terminates P) (source_doubledCutoffs P)

/-! ## A clock whose transitions are actual finite Boolean-stack transitions

This adapter is independent of the macro evaluator above. Using it for the
paper requires an actual finite-stack program implementing the coefficient
generation and search, together with its correctness and termination proof.
-/

/-- Total decoding of little-endian binary; leading zero bits are allowed. -/
def decodeBits : List Bool → ℕ
  | [] => 0
  | b :: rest => Nat.bit b (decodeBits rest)

theorem decodeBits_bits (n : ℕ) : decodeBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [decodeBits]
  | bit b n hn ih => simp [Nat.bits_append_bit _ _ hn, decodeBits, ih]

/-- This machine uses exactly one actual `TM2.step` per clock transition. -/
def bitClock (M : BitMachine.Machine) : SlowClock.Machine M.Config where
  initial k := M.init k.bits
  step := M.step
  output c := if c.l = none then some (decodeBits (c.stk M.output)) else none
  halted := by
    intro c u hu
    split at hu
    · exact BitMachine.step_halted M c ‹_›
    · contradiction

theorem bitClock_run (M : BitMachine.Machine) (fuel k : ℕ) :
    SlowClock.run (bitClock M) fuel k = M.run fuel (M.init k.bits) := rfl

theorem bitClock_output_of_outputsWithin (M : BitMachine.Machine)
    {k u time : ℕ} (h : M.OutputsWithin k.bits u.bits time) :
    (bitClock M).output (SlowClock.run (bitClock M) time k) = some u := by
  obtain ⟨hh, ho⟩ := BitMachine.outputsWithin_at_bound M h
  change (if (M.run time (M.init k.bits)).l = none then
    some (decodeBits ((M.run time (M.init k.bits)).stk M.output)) else none) = some u
  simp [hh, ho, decodeBits_bits]

theorem bitClock_terminates (M : BitMachine.Machine)
    (h : ∀ k, 1 ≤ k → ∃ (u time : ℕ), M.OutputsWithin k.bits u.bits time) :
    SlowClock.Terminates (bitClock M) := by
  intro k hk
  obtain ⟨u, time, hout⟩ := h k hk
  exact ⟨time, u, bitClock_output_of_outputsWithin M hout⟩

theorem bitClock_terminates_of_halts (M : BitMachine.Machine)
    (h : ∀ k, 1 ≤ k → ∃ time, (M.run time (M.init k.bits)).l = none) :
    SlowClock.Terminates (bitClock M) := by
  intro k hk
  obtain ⟨time, hh⟩ := h k hk
  refine ⟨time, decodeBits ((M.run time (M.init k.bits)).stk M.output), ?_⟩
  change (if (M.run time (M.init k.bits)).l = none then _ else _) = _
  rw [if_pos hh]
  rfl

/-- A selected level has actually halted within the clock's finite number
of Boolean-stack transitions and its decoded output meets the source budget. -/
theorem bitClock_selected_run (M : BitMachine.Machine) (n k : ℕ)
    (hk : 1 ≤ k) (hselected : k ≤ SlowClock.repetitions (bitClock M) n) :
    (M.run n (M.init k.bits)).l = none ∧
      decodeBits ((M.run n (M.init k.bits)).stk M.output) ≤ n := by
  obtain ⟨u, hu, hun⟩ := SlowClock.selected_run (bitClock M) n k hk hselected
  change (if (M.run n (M.init k.bits)).l = none then
    some (decodeBits ((M.run n (M.init k.bits)).stk M.output)) else none) = some u at hu
  split at hu
  · simp only [Option.some.injEq] at hu
    exact ⟨‹_›, hu ▸ hun⟩
  · contradiction

/-- Every output inspected by the clock has only linearly many bits in its
actual transition budget. This bound includes unfinished computations. -/
theorem bitClock_output_length (M : BitMachine.Machine) (n k : ℕ) :
    ((M.run n (M.init k.bits)).stk M.output).length ≤
      k.bits.length + n * M.pushBound := by
  apply (BitMachine.run_length M (M.init k.bits) M.output n).trans
  apply Nat.add_le_add_right
  simp only [BitMachine.Machine.init]
  split <;> simp

end EthInapproximability.CurrentPaper.CutoffMachine
