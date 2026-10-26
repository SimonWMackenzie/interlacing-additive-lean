import EthInapproximability.CurrentPaper.BitMachinePairAlphabet
import EthInapproximability.CurrentPaper.CutoffMachine
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Compilation of the concrete arithmetic cutoff

Source: frozen v8 `05-iteration.tex`, `thm:paper-effective-level` and
`eq:paper-slow-clock`; `F-parameter-choices.tex`, persistent cutoffs;
`06-eth.tex`, deterministic bit-machine convention.

The arithmetic cutoff here is an explicit finite maximum of proved witnesses.
Its primitive-recursive derivation is used to compile an actual stack program;
no cutoff-correctness or arithmetic-evaluation oracle is program data.
-/

namespace EthInapproximability.CurrentPaper.CutoffBitMachine

open EffectiveIteration

theorem nat_pow_primrec : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem degree_primrec : Primrec degree := by
  have hstep : Primrec₂ (fun (_i acc : ℕ) => 8 * acc + 100) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.snd)
      (Primrec.const 100)
  have h := Primrec.nat_rec₁ 4 hstep
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [degree, ih]

theorem coefficient_primrec (C : ℕ) : Primrec (coefficient C) := by
  have hstep : Primrec₂ (fun (_i acc : ℕ) => 400000000 * acc ^ 4 + 7) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 400000000)
        (nat_pow_primrec.comp Primrec.snd (Primrec.const 4))) (Primrec.const 7)
  have h := Primrec.nat_rec₁ C hstep
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [coefficient, ih]

def witness (C k i : ℕ) : ℕ :=
  cutoffWitness (sizeTestCoefficient (coefficient C i) k) (4 * degree i)

theorem witness_primrec (C : ℕ) : Primrec₂ (witness C) := by
  unfold witness cutoffWitness sizeTestCoefficient acceptanceCoefficient
  exact nat_pow_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.const 500000000)
              (nat_pow_primrec.comp
                (Primrec.nat_add.comp ((coefficient_primrec C).comp Primrec.snd)
                  (Primrec.const 1)) (Primrec.const 4)))
            (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)) (Primrec.const 1))
        (Primrec.nat_mul.comp (Primrec.const 4) (degree_primrec.comp Primrec.snd)))
      (Primrec.const 8))

def maxWitness (C k : ℕ) : ℕ :=
  Nat.rec 0 (fun i acc => max acc (witness C k i)) k

theorem maxWitness_primrec (C : ℕ) : Primrec (maxWitness C) := by
  unfold maxWitness
  have hstep : Primrec₂ (fun (k : ℕ) (t : ℕ × ℕ) => max t.2 (witness C k t.1)) :=
    Primrec.nat_max.comp (Primrec.snd.comp Primrec.snd)
    ((witness_primrec C).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
  exact Primrec.nat_rec' Primrec.id (Primrec.const 0) hstep

theorem maxWitness_eq_sup (C k : ℕ) :
    maxWitness C k = (Finset.range k).sup (witness C k) := by
  unfold maxWitness
  generalize k = count
  have h : ∀ j, Nat.rec 0 (fun i acc => max acc (witness C count i)) j =
      (Finset.range j).sup (witness C count) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => simp [Finset.range_add_one, Finset.sup_insert, ih, max_comm]
  exact h count

/-- The doubling guard is explicit, including the empty prefix. -/
def cutoff (c A d k : ℕ) : ℕ :=
  max (2 * k) (max 2 (2 ^ (2 ^ maxWitness (initialCoefficient c A d) k)))

theorem cutoff_primrec (c A d : ℕ) : Primrec (cutoff c A d) := by
  unfold cutoff
  exact Primrec.nat_max.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
    (Primrec.nat_max.comp (Primrec.const 2)
      (nat_pow_primrec.comp (Primrec.const 2)
        (nat_pow_primrec.comp (Primrec.const 2) (maxWitness_primrec _))))

theorem cutoff_ge_sourceCutoff (c A d k : ℕ) : sourceCutoff c A d k ≤ cutoff c A d k := by
  simp only [sourceCutoff, cutoff, maxWitness_eq_sup, witness, cutoffScale, sourceThreshold]
  exact max_le_max (by omega) le_rfl

theorem cutoff_doubled (c A d k : ℕ) : 2 * k ≤ cutoff c A d k := le_max_left _ _

theorem exists_cutoff_code (c A d : ℕ) :
    ∃ p : Turing.ToPartrec.Code, ∀ k,
      p.eval [k] = Part.some [cutoff c A d k] := by
  obtain ⟨p, hp⟩ := Turing.ToPartrec.Code.exists_code
    (Nat.Partrec'.of_prim ((cutoff_primrec c A d).comp
      (Primrec.vector_head (n := 0))))
  refine ⟨p, ?_⟩
  intro k
  simpa using hp (List.Vector.cons k List.Vector.nil)

namespace Compile

open Turing

def symbolEquiv : Bool × Bool ≃ Turing.PartrecToTM2.Γ' where
  toFun
    | (false, false) => .bit0
    | (true, false) => .bit1
    | (false, true) => .cons
    | (true, true) => .consₗ
  invFun
    | .bit0 => (false, false)
    | .bit1 => (true, false)
    | .cons => (false, true)
    | .consₗ => (true, true)
  left_inv x := by rcases x with ⟨a, b⟩; cases a <;> cases b <;> rfl
  right_inv x := by cases x <;> rfl

def stackEquiv : Fin 4 ≃ Turing.PartrecToTM2.K' where
  toFun i := if i.val = 0 then .main else if i.val = 1 then .rev
    else if i.val = 2 then .aux else .stack
  invFun
    | .main => 0
    | .rev => 1
    | .aux => 2
    | .stack => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv k := by cases k <;> rfl

def controlEquiv : Fin 5 ≃ Option Turing.PartrecToTM2.Γ' where
  toFun i := if i.val = 0 then none else if i.val = 1 then some .bit0
    else if i.val = 2 then some .bit1 else if i.val = 3 then some .cons else some .consₗ
  invFun
    | none => 0
    | some .bit0 => 1
    | some .bit1 => 2
    | some .cons => 3
    | some .consₗ => 4
  left_inv i := by fin_cases i <;> rfl
  right_inv o := by cases o with | none => rfl | some a => cases a <;> rfl

def labels (p : ToPartrec.Code) : Finset Turing.PartrecToTM2.Λ' := Turing.PartrecToTM2.codeSupp p .halt

noncomputable def labelEquiv (p : ToPartrec.Code) :
    Fin (labels p).card ≃ ↥(labels p) :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm

def firstLabel (p : ToPartrec.Code) : ↥(labels p) :=
  ⟨Turing.PartrecToTM2.trNormal p .halt, (Turing.PartrecToTM2.tr_supports p .halt).1⟩

def restricted (p : ToPartrec.Code) : ↥(labels p) →
    TM2.Stmt (fun _ : Turing.PartrecToTM2.K' => Turing.PartrecToTM2.Γ') ↥(labels p) (Option Turing.PartrecToTM2.Γ') :=
  BitMachinePairAlphabet.restrictProgram (labels p) Turing.PartrecToTM2.tr (Turing.PartrecToTM2.tr_supports p .halt).2

def restrictedInit (p : ToPartrec.Code) (v : List ℕ) :
    TM2.Cfg (fun _ : Turing.PartrecToTM2.K' => Turing.PartrecToTM2.Γ') ↥(labels p) (Option Turing.PartrecToTM2.Γ') :=
  ⟨some (firstLabel p), none, Turing.PartrecToTM2.K'.elim (Turing.PartrecToTM2.trList v) [] [] []⟩

noncomputable def machine (p : ToPartrec.Code) : BitMachinePairAlphabet.Machine where
  stackCount := 4
  labelCount := (labels p).card
  controlCount := 5
  input := stackEquiv.symm .main
  output := stackEquiv.symm .main
  start := (labelEquiv p).symm (firstLabel p)
  initial := controlEquiv.symm none
  program l := BitMachinePairAlphabet.relocateStmt stackEquiv (labelEquiv p) controlEquiv symbolEquiv
    (restricted p (labelEquiv p l))

def encodeSymbols (v : List ℕ) : List (Bool × Bool) :=
  (Turing.PartrecToTM2.trList v).map symbolEquiv.symm

noncomputable def encodeRestricted (p : ToPartrec.Code)
    (q : TM2.Cfg (fun _ : Turing.PartrecToTM2.K' => Turing.PartrecToTM2.Γ') ↥(labels p) (Option Turing.PartrecToTM2.Γ')) :
    (machine p).Config :=
  BitMachinePairAlphabet.relocateConfig stackEquiv (labelEquiv p) controlEquiv symbolEquiv q

theorem initial_eq (p : ToPartrec.Code) (v : List ℕ) :
    (machine p).init (encodeSymbols v) = encodeRestricted p (restrictedInit p v) := by
  simp only [BitMachinePairAlphabet.Machine.init, machine, encodeRestricted, BitMachinePairAlphabet.relocateConfig, restrictedInit]
  congr 1
  funext k
  fin_cases k <;> simp [stackEquiv, BitMachinePairAlphabet.relocateStacks, encodeSymbols, Turing.PartrecToTM2.K'.elim]

theorem lift_restrictedInit (p : ToPartrec.Code) (v : List ℕ) :
    BitMachinePairAlphabet.liftLabelConfig (labels p) (restrictedInit p v) = Turing.PartrecToTM2.init p v := rfl

theorem restricted_run (p : ToPartrec.Code) (v : List ℕ) (fuel : ℕ) :
    (machine p).run fuel ((machine p).init (encodeSymbols v)) =
      encodeRestricted p (((fun q => (TM2.step (restricted p) q).getD q)^[fuel])
        (restrictedInit p v)) := by
  rw [initial_eq]
  exact BitMachinePairAlphabet.relocate_run stackEquiv (labelEquiv p) controlEquiv symbolEquiv
    (restricted p) (restrictedInit p v) fuel

theorem lift_run (p : ToPartrec.Code) (v : List ℕ) (fuel : ℕ) :
    BitMachinePairAlphabet.liftLabelConfig (labels p)
      (((fun q => (TM2.step (restricted p) q).getD q)^[fuel]) (restrictedInit p v)) =
    ((fun q => (TM2.step Turing.PartrecToTM2.tr q).getD q)^[fuel]) (Turing.PartrecToTM2.init p v) :=
  BitMachinePairAlphabet.restrict_run (labels p) Turing.PartrecToTM2.tr (Turing.PartrecToTM2.tr_supports p .halt).2 (restrictedInit p v) fuel

theorem reaches_has_fuel {α : Type*} {step : α → Option α} {a b : α}
    (h : StateTransition.Reaches step a b) :
    ∃ fuel, ((fun q => (step q).getD q)^[fuel]) a = b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail b c h hbc ih =>
    obtain ⟨fuel, hf⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    rw [Function.iterate_succ_apply', hf, Option.mem_def.mp hbc]
    rfl

theorem source_halting (p : ToPartrec.Code) (v w : List ℕ)
    (h : p.eval v = Part.some w) :
    ∃ fuel, ((fun q => (TM2.step Turing.PartrecToTM2.tr q).getD q)^[fuel])
      (Turing.PartrecToTM2.init p v) = Turing.PartrecToTM2.halt w := by
  apply reaches_has_fuel
  apply (StateTransition.mem_eval.mp ?_).1
  rw [Turing.PartrecToTM2.tr_eval, h]
  exact Part.mem_map _ (Part.mem_some w)

/-- Actual Boolean-stack execution of any compiled terminating source code.
Finite-label restriction and two-bit lowering are proved simulations above;
no transition executes an arithmetic expression or source-code evaluator. -/
theorem machine_outputs (p : ToPartrec.Code) (v w : List ℕ)
    (h : p.eval v = Part.some w) :
    ∃ fuel, (machine p).compile.OutputsWithin
      (BitMachinePairAlphabet.encodeStack (encodeSymbols v))
      (BitMachinePairAlphabet.encodeStack (encodeSymbols w)) fuel := by
  obtain ⟨fuel, hf⟩ := source_halting p v w h
  let q := ((fun q => (TM2.step (restricted p) q).getD q)^[fuel]) (restrictedInit p v)
  have hq : BitMachinePairAlphabet.liftLabelConfig (labels p) q =
      Turing.PartrecToTM2.halt w := (lift_run p v fuel).trans hf
  have hl : q.l = none := by
    have he := congrArg (fun c => c.l) hq
    change q.l.map Subtype.val = none at he
    exact Option.map_eq_none_iff.mp he
  have ho : q.stk .main = Turing.PartrecToTM2.trList w :=
    congrArg (fun c => c.stk .main) hq
  refine ⟨fuel, BitMachinePairAlphabet.compile_outputs (machine p)
    (encodeSymbols v) (encodeSymbols w) fuel ?_ ?_⟩
  · rw [restricted_run]
    change q.l.map (labelEquiv p).symm = none
    rw [hl]
    rfl
  · rw [restricted_run]
    change (q.stk (stackEquiv (stackEquiv.symm .main))).map symbolEquiv.symm = encodeSymbols w
    rw [stackEquiv.apply_symm_apply, ho]
    rfl

end Compile

def encodedNat (k : ℕ) : List Bool :=
  BitMachinePairAlphabet.encodeStack (Compile.encodeSymbols [k])

/-- Read the first delimited binary number. A malformed suffix is treated
as a delimiter, making this parser a total function on every physical stack. -/
def decodedNat : List Bool → ℕ
  | a :: false :: rest => Nat.bit a (decodedNat rest)
  | _ => 0

theorem decoded_posNum (p : PosNum) :
    decodedNat (BitMachinePairAlphabet.encodeStack
      ((Turing.PartrecToTM2.trPosNum p ++ [Turing.PartrecToTM2.Γ'.cons]).map
        Compile.symbolEquiv.symm)) = (p : ℕ) := by
  induction p with
  | one => rfl
  | bit0 p ih =>
    change Nat.bit false (decodedNat (BitMachinePairAlphabet.encodeStack
      ((Turing.PartrecToTM2.trPosNum p ++ [Turing.PartrecToTM2.Γ'.cons]).map
        Compile.symbolEquiv.symm))) = (p.bit0 : ℕ)
    rw [ih]
    simp [Nat.bit, PosNum.cast_bit0, two_mul]
  | bit1 p ih =>
    change Nat.bit true (decodedNat (BitMachinePairAlphabet.encodeStack
      ((Turing.PartrecToTM2.trPosNum p ++ [Turing.PartrecToTM2.Γ'.cons]).map
        Compile.symbolEquiv.symm))) = (p.bit1 : ℕ)
    rw [ih]
    simp [Nat.bit, PosNum.cast_bit1, two_mul]

theorem decoded_num (p : Num) :
    decodedNat (BitMachinePairAlphabet.encodeStack
      ((Turing.PartrecToTM2.trNum p ++ [Turing.PartrecToTM2.Γ'.cons]).map
        Compile.symbolEquiv.symm)) = (p : ℕ) := by
  cases p with
  | zero => rfl
  | pos p => exact decoded_posNum p

theorem decoded_encodedNat (k : ℕ) : decodedNat (encodedNat k) = k := by
  simpa [encodedNat, Compile.encodeSymbols, Turing.PartrecToTM2.trNat] using
    decoded_num (k : Num)

theorem trPosNum_length_le (p : PosNum) :
    (Turing.PartrecToTM2.trPosNum p).length ≤ (p : ℕ) := by
  induction p with
  | one => decide
  | bit0 p ih =>
    have hp := PosNum.to_nat_pos p
    simp only [Turing.PartrecToTM2.trPosNum, List.length_cons, PosNum.cast_bit0]
    omega
  | bit1 p ih =>
    simp only [Turing.PartrecToTM2.trPosNum, List.length_cons, PosNum.cast_bit1]
    omega

theorem trNat_length_le (k : ℕ) : (Turing.PartrecToTM2.trNat k).length ≤ k := by
  have h : ∀ p : Num, (Turing.PartrecToTM2.trNum p).length ≤ (p : ℕ) := by
    intro p
    cases p with
    | zero => decide
    | pos p => exact trPosNum_length_le p
  simpa [Turing.PartrecToTM2.trNat] using h (k : Num)

theorem encodedNat_length (k : ℕ) : (encodedNat k).length ≤ 2 * (k + 1) := by
  unfold encodedNat Compile.encodeSymbols
  rw [BitMachinePairAlphabet.encodeStack_length, List.length_map]
  simp only [Turing.PartrecToTM2.trList, List.length_append, List.length_cons,
    List.length_nil, add_zero]
  exact Nat.mul_le_mul_left 2 (Nat.add_le_add_right (trNat_length_le k) 1)

/-- The cutoff arithmetic is now implemented by an actual fixed finite
Boolean-stack program. Its runtime is finite, with no asserted complexity
bound on the cutoff computation itself. -/
theorem exists_cutoff_machine (c A d : ℕ) :
    ∃ M : BitMachine.Machine, ∀ k, ∃ time,
      M.OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) time := by
  obtain ⟨p, hp⟩ := exists_cutoff_code c A d
  refine ⟨(Compile.machine p).compile, ?_⟩
  intro k
  exact Compile.machine_outputs p [k] [cutoff c A d k] (hp k)

/-- Its state is a real finite Boolean-stack configuration. Input coding is
the delimited two-bit encoding used by the compiled arithmetic program. -/
def clock (M : BitMachine.Machine) : SlowClock.Machine M.Config where
  initial k := M.init (encodedNat k)
  step := M.step
  output q := if q.l = none then some (decodedNat (q.stk M.output)) else none
  halted := by
    intro q u hu
    split at hu
    · exact BitMachine.step_halted M q ‹_›
    · contradiction

theorem clock_run (M : BitMachine.Machine) (n k : ℕ) :
    SlowClock.run (clock M) n k = M.run n (M.init (encodedNat k)) := rfl

/-- Finite clock runs never acquire an unbounded-size hidden output: every
physical stack is bounded by the encoded input and actual pushes. This does
not assert that the whole outer loop has already been compiled. -/
theorem clock_run_stack_length (M : BitMachine.Machine) (n k : ℕ) (j : Fin M.stackCount) :
    ((SlowClock.run (clock M) n k).stk j).length ≤ 2 * (k + 1) + n * M.pushBound := by
  apply (BitMachine.run_length M (M.init (encodedNat k)) j n).trans
  apply Nat.add_le_add_right
  simp only [BitMachine.Machine.init]
  split
  · exact encodedNat_length k
  · simp

theorem clock_output_of_outputsWithin (M : BitMachine.Machine) {k u time : ℕ}
    (h : M.OutputsWithin (encodedNat k) (encodedNat u) time) :
    (clock M).output (SlowClock.run (clock M) time k) = some u := by
  obtain ⟨hh, ho⟩ := BitMachine.outputsWithin_at_bound M h
  change (if (M.run time (M.init (encodedNat k))).l = none then
    some (decodedNat ((M.run time (M.init (encodedNat k))).stk M.output)) else none) = some u
  simp only [hh, if_true, ho, decoded_encodedNat]

theorem clock_terminates (M : BitMachine.Machine) (c A d : ℕ)
    (h : ∀ k, ∃ time, M.OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) time) :
    SlowClock.Terminates (clock M) := by
  intro k _
  obtain ⟨time, ht⟩ := h k
  exact ⟨time, cutoff c A d k, clock_output_of_outputsWithin M ht⟩

theorem clock_output_correct (M : BitMachine.Machine) (c A d : ℕ)
    (h : ∀ k, ∃ time, M.OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) time)
    {fuel k u : ℕ}
    (hu : (clock M).output (SlowClock.run (clock M) fuel k) = some u) :
    u = cutoff c A d k := by
  change (if (M.run fuel (M.init (encodedNat k))).l = none then
    some (decodedNat ((M.run fuel (M.init (encodedNat k))).stk M.output)) else none) = some u at hu
  split at hu
  · obtain ⟨time, ht⟩ := h k
    have hout := BitMachine.outputsWithin_unique M
      (show M.OutputsWithin (encodedNat k)
        ((M.run fuel (M.init (encodedNat k))).stk M.output) fuel from
        ⟨fuel, le_rfl, ‹_›, rfl⟩) ht
    rw [hout, decoded_encodedNat] at hu
    exact (Option.some.inj hu).symm
  · contradiction

theorem clock_doubled (M : BitMachine.Machine) (c A d : ℕ)
    (h : ∀ k, ∃ time, M.OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) time) :
    ClockedPadding.DoubledCutoffs (clock M) := by
  intro fuel k u _ hu
  rw [clock_output_correct M c A d h hu]
  exact cutoff_doubled c A d k

theorem selected_cutoff (M : BitMachine.Machine) (c A d : ℕ)
    (h : ∀ k, ∃ time, M.OutputsWithin (encodedNat k) (encodedNat (cutoff c A d k)) time)
    (n k : ℕ) (hk : 1 ≤ k) (hselected : k ≤ SlowClock.repetitions (clock M) n) :
    sourceCutoff c A d k ≤ n := by
  obtain ⟨u, hu, hun⟩ := SlowClock.selected_run (clock M) n k hk hselected
  rw [clock_output_correct M c A d h hu] at hun
  exact (cutoff_ge_sourceCutoff c A d k).trans hun

end EthInapproximability.CurrentPaper.CutoffBitMachine
