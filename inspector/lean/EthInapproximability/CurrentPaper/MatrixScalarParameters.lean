import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.MatrixScalarAddressStage

/-!
# Literal initialization of the matrix's scalar parameters

Source: frozen v8 `thm:paper-materialization`, scalar formulas and the
actual matrix carrier sizes. The five input unary integers are preserved.
All arithmetic below is implemented by finite Boolean-stack instructions;
no unbounded natural number is stored in the finite control.
-/

namespace EthInapproximability.CurrentPaper.MatrixScalarParameters

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

inductive Stage where
  | q | width | base | duplicate | square | cube | fourth | cut | rows | cols
  deriving DecidableEq, Fintype

inductive Tail where
  | setup | trim | clear (i : Fin 8)
  deriving DecidableEq, Fintype

abbrev Label := MatrixUnaryPower.Label ⊕ ((Stage × MatrixAddressMachine.Label) ⊕ Tail)
abbrev Control := Bool × MatrixUnaryPower.Control
abbrev Config := TM2.Cfg (fun _ : Fin 22 => Bool) Label Control

/-- Registers 0--4 preserve `a,d,N1,N2,n`; 6,7,8,13,14,15 are the six
public outputs `q,C1width,base,rowCut,rows,columns`. Register 5 and
9--12,17--21 are temporary. Register 16 stays empty. -/
def wiring : Stage → Fin 6 → Fin 22
  | .q => ![17, 5, 16, 20, 21, 6]
  | .width => ![17, 5, 16, 20, 21, 7]
  | .base => ![1, 2, 16, 20, 21, 8]
  | .duplicate => ![17, 8, 16, 20, 21, 9]
  | .square => ![8, 9, 16, 20, 21, 10]
  | .cube => ![8, 10, 16, 20, 21, 11]
  | .fourth => ![8, 11, 16, 20, 21, 12]
  | .cut => ![18, 3, 16, 20, 21, 13]
  | .rows => ![18, 3, 4, 20, 21, 14]
  | .cols => ![19, 12, 16, 20, 21, 15]

def registers (stage : Stage) : Fin 6 ↪ Fin 22 :=
  ⟨wiring stage, by cases stage <;> decide⟩

def entry (stage : Stage) : Label := .inr (.inl (stage, .outer))

def continuation : Stage → Label
  | .q => entry .width
  | .width => entry .base
  | .base => entry .duplicate
  | .duplicate => entry .square
  | .square => entry .cube
  | .cube => entry .fourth
  | .fourth => entry .cut
  | .cut => entry .rows
  | .rows => entry .cols
  | .cols => .inr (.inr .trim)

def temporary (i : Fin 8) : Fin 22 := ![5, 9, 10, 11, 12, 17, 18, 19] i

def powerBank : (MatrixUnaryPower.Stack ⊕ Fin 18) ≃ Fin 22 where
  toFun
    | .inl (.inl i) => ![5, 20, 21] i
    | .inl (.inr ()) => 0
    | .inr i => ![1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] i
  invFun i := ![.inl (.inr ()), .inr 0, .inr 1, .inr 2, .inr 3,
    .inl (.inl 0), .inr 4, .inr 5, .inr 6, .inr 7, .inr 8,
    .inr 9, .inr 10, .inr 11, .inr 12, .inr 13, .inr 14,
    .inr 15, .inr 16, .inr 17, .inl (.inl 1), .inl (.inl 2)] i
  left_inv i := by
    rcases i with (i | u) | i
    · fin_cases i <;> rfl
    · cases u; rfl
    · fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def powerControl : MatrixUnaryPower.Control × Bool ≃ Control := Equiv.prodComm _ _

def unary (n : ℕ) : List Bool := List.replicate n true

def inputBank (a d N1 N2 n : ℕ) : Fin 22 → List Bool :=
  ![unary a, unary d, unary N1, unary N2, unary n,
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def outputBank (a d N1 N2 n : ℕ) : Fin 22 → List Bool :=
  ![unary a, unary d, unary N1, unary N2, unary n,
    [], unary (2^a-2), unary (2^a+1), unary (d*N1), [], [], [], [],
    unary (4*N2), unary (4*N2+n), unary (8*(d*N1)^4), [], [], [], [], [], []]

def powerReadyBank (a d N1 N2 n : ℕ) : Fin 22 → List Bool :=
  ![unary a, unary d, unary N1, unary N2, unary n,
    unary (2^a), [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def idle : Control := (false, ((false, false), none))

def powerForeign (d N1 N2 n : ℕ) : Fin 18 → List Bool :=
  ![unary d, unary N1, unary N2, unary n, [], [], [], [], [], [], [], [], [], [], [], [], [], []]

theorem power_cfg (l : Option MatrixUnaryPower.Label) (a d N1 N2 n : ℕ)
    (word work scratch : List Bool) :
    renameCfg powerBank (Equiv.refl _) powerControl
      (liftCfg (some (Sum.inr Tail.setup)) false (powerForeign d N1 N2 n)
        (MatrixUnaryPower.cfg l ((false, false), none) word work scratch (unary a))) =
      (⟨l.elim (some (.inr (.inr .setup))) (fun l => some (.inl l)), idle,
        ![unary a, unary d, unary N1, unary N2, unary n,
          word, [], [], [], [], [], [], [], [], [], [], [], [], [], [], work, scratch]⟩ : Config) := by
  cases l <;> apply congrArg (fun S => (⟨_, idle, S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

theorem power_stage
    (Q : Label → TM2.Stmt (fun _ : Fin 22 => Bool) Label Control)
    (hQ : ∀ l, Q (.inl l) = renameStmt powerBank (Equiv.refl _) powerControl
      (liftStmt (some (Sum.inr Tail.setup)) (MatrixUnaryPower.program l)))
    (a d N1 N2 n : ℕ) :
    ∃ t ≤ 4 * 2^a + 5*a + 7,
      ((advance Q)^[t]) (⟨some (.inl (.inr false)), idle, inputBank a d N1 N2 n⟩ : Config) =
        ⟨some (.inr (.inr .setup)), idle, powerReadyBank a d N1 N2 n⟩ := by
  obtain ⟨t, ht, he⟩ := MatrixUnaryPower.unary_power_run a
  change MatrixUnaryPower.run t
    (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none) [] [] [] (unary a)) =
    MatrixUnaryPower.cfg none ((false,false),none) (unary (2^a)) [] [] (unary a) at he
  have hh : (((advance MatrixUnaryPower.program)^[t])
      (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none)
        [] [] [] (unary a))).l = none := by
    change (MatrixUnaryPower.run t _).l = none
    rw [he]
    rfl
  obtain ⟨u, hu, huout⟩ := lift_outputs_renamed powerBank (Equiv.refl _) powerControl
    MatrixUnaryPower.program Q (some (Sum.inr Tail.setup)) hQ false
    (powerForeign d N1 N2 n)
    (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none) [] [] [] (unary a)) t hh
  change _ = renameCfg _ _ _ (liftCfg _ _ _ (MatrixUnaryPower.run t _)) at huout
  rw [he, power_cfg, power_cfg] at huout
  exact ⟨u, hu.trans ht, huout⟩

def pushOn (r : Fin 22) : ℕ → TM2.Stmt (fun _ : Fin 22 => Bool) Label Control →
    TM2.Stmt (fun _ : Fin 22 => Bool) Label Control
  | 0, next => next
  | k + 1, next => push r (fun _ => true) (pushOn r k next)

def clearNext (i : Fin 8) : Option Label :=
  if h : i.val + 1 < 8 then some (.inr (.inr (.clear ⟨i.val+1, h⟩))) else none

def clearExit (i : Fin 8) : TM2.Stmt (fun _ : Fin 22 => Bool) Label Control :=
  match clearNext i with
  | none => halt
  | some l => goto (fun _ => l)

def program : Label → TM2.Stmt (fun _ : Fin 22 => Bool) Label Control
  | .inl l => renameStmt powerBank (Equiv.refl _) powerControl
      (liftStmt (some (Sum.inr Tail.setup)) (MatrixUnaryPower.program l))
  | .inr (.inl (stage, l)) => MatrixScalarAddressStage.mapStmt (registers stage)
      (fun l => .inr (.inl (stage, l))) (continuation stage) (MatrixAddressMachine.program l)
  | .inr (.inr .setup) => pushOn 17 1 (pushOn 18 4 (pushOn 19 8 (pushOn 7 1
      (goto (fun _ => entry .q)))))
  | .inr (.inr .trim) => pop 6 (fun s _ => s) (pop 6 (fun s _ => s)
      (goto (fun _ => .inr (.inr (.clear 0)))))
  | .inr (.inr (.clear i)) => pop (temporary i) (fun s b => (b.isSome, s.2))
      (branch Prod.fst (goto (fun _ => .inr (.inr (.clear i)))) (clearExit i))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_one (c : Config) : run 1 c = advance program c := rfl

theorem run_add (t u : ℕ) (c : Config) : run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

def stageAt (i : Fin 10) : Stage :=
  ![.q, .width, .base, .duplicate, .square, .cube, .fourth, .cut, .rows, .cols] i

def stageLabel (i : ℕ) : Label :=
  if h : i < 10 then entry (stageAt ⟨i, h⟩) else .inr (.inr .trim)

def rowOperand (a d N1 N2 n i : ℕ) : ℕ :=
  [1, 1, d, 1, d*N1, d*N1, d*N1, 4, 4, 8].getD i 0

def widthOperand (a d N1 N2 n i : ℕ) : ℕ :=
  [2^a, 2^a, N1, d*N1, d*N1, (d*N1)^2, (d*N1)^3, N2, N2, (d*N1)^4].getD i 0

def columnOperand (a d N1 N2 n i : ℕ) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, n, 0].getD i 0

def arithmeticBank (a d N1 N2 n i : ℕ) : Fin 22 → List Bool :=
  ![unary a, unary d, unary N1, unary N2, unary n, unary (2^a),
    if 1 ≤ i then unary (2^a) else [],
    if 2 ≤ i then unary (2^a+1) else unary 1,
    if 3 ≤ i then unary (d*N1) else [],
    if 4 ≤ i then unary (d*N1) else [],
    if 5 ≤ i then unary ((d*N1)^2) else [],
    if 6 ≤ i then unary ((d*N1)^3) else [],
    if 7 ≤ i then unary ((d*N1)^4) else [],
    if 8 ≤ i then unary (4*N2) else [],
    if 9 ≤ i then unary (4*N2+n) else [],
    if 10 ≤ i then unary (8*(d*N1)^4) else [],
    [], unary 1, unary 4, unary 8, [], []]

theorem setup_step (a d N1 N2 n : ℕ) :
    advance program (⟨some (.inr (.inr .setup)), idle, powerReadyBank a d N1 N2 n⟩ : Config) =
      ⟨some (stageLabel 0), idle, arithmeticBank a d N1 N2 n 0⟩ := by
  apply congrArg (fun S => (⟨some (stageLabel 0), idle, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

set_option maxHeartbeats 0 in
theorem arithmetic_output_bank (a d N1 N2 n : ℕ) (i : Fin 10) :
    Function.update (arithmeticBank a d N1 N2 n i.val)
      (registers (stageAt i) 5)
      (List.replicate (rowOperand a d N1 N2 n i.val * widthOperand a d N1 N2 n i.val +
        columnOperand a d N1 N2 n i.val) true ++
          arithmeticBank a d N1 N2 n i.val (registers (stageAt i) 5)) =
      arithmeticBank a d N1 N2 n (i.val+1) := by
  funext k
  fin_cases i <;> fin_cases k <;>
    first | rfl | (simp [registers, stageAt, wiring, arithmeticBank, rowOperand, widthOperand,
      columnOperand, unary, pow_succ, List.replicate_append_replicate, Nat.mul_assoc] <;>
      congr 1 <;> ring)
  simpa only [Nat.add_comm] using (List.replicate_succ' (n := 2^a) (a := true)).symm

set_option maxHeartbeats 0 in
theorem arithmetic_step (a d N1 N2 n : ℕ) (i : Fin 10) :
    ∃ t ≤ MatrixAddressMachine.exactTime (rowOperand a d N1 N2 n i.val)
        (widthOperand a d N1 N2 n i.val) (columnOperand a d N1 N2 n i.val),
      run t (⟨some (stageLabel i.val), idle, arithmeticBank a d N1 N2 n i.val⟩ : Config) =
        ⟨some (stageLabel (i.val+1)), idle, arithmeticBank a d N1 N2 n (i.val+1)⟩ := by
  obtain ⟨t, ht, he⟩ := MatrixScalarAddressStage.address_stage
    (registers (stageAt i)) (fun l => .inr (.inl (stageAt i, l))) (continuation (stageAt i))
    program (fun _ => rfl) ((false,false),none) (arithmeticBank a d N1 N2 n i.val)
    (rowOperand a d N1 N2 n i.val) (widthOperand a d N1 N2 n i.val)
    (columnOperand a d N1 N2 n i.val) false
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl) (by fin_cases i <;> rfl)
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl)
  refine ⟨t, ht, ?_⟩
  have hlabel : stageLabel i.val = entry (stageAt i) := by simp [stageLabel, i.isLt]
  have hnext : continuation (stageAt i) = stageLabel (i.val+1) := by fin_cases i <;> rfl
  have hbank := arithmetic_output_bank a d N1 N2 n i
  simpa only [run, hlabel, entry, hnext, hbank] using he

def arithmeticTime (a d N1 N2 n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, MatrixAddressMachine.exactTime (rowOperand a d N1 N2 n i)
    (widthOperand a d N1 N2 n i) (columnOperand a d N1 N2 n i)

theorem arithmetic_run (a d N1 N2 n k : ℕ) (hk : k ≤ 10) :
    ∃ t ≤ arithmeticTime a d N1 N2 n k,
      run t (⟨some (stageLabel 0), idle, arithmeticBank a d N1 N2 n 0⟩ : Config) =
        ⟨some (stageLabel k), idle, arithmeticBank a d N1 N2 n k⟩ := by
  induction k with
  | zero => exact ⟨0, by simp [arithmeticTime], rfl⟩
  | succ k ih =>
      obtain ⟨t, ht, he⟩ := ih (by omega)
      obtain ⟨u, hu, hue⟩ := arithmetic_step a d N1 N2 n ⟨k, by omega⟩
      refine ⟨t+u, ?_, ?_⟩
      · simp only [arithmeticTime, Finset.sum_range_succ] at ht ⊢
        exact Nat.add_le_add ht hu
      · rw [run_add, he]
        exact hue

def cleanBank (a d N1 N2 n i : ℕ) : Fin 22 → List Bool :=
  ![unary a, unary d, unary N1, unary N2, unary n,
    if 1 ≤ i then [] else unary (2^a),
    unary (2^a-2), unary (2^a+1), unary (d*N1),
    if 2 ≤ i then [] else unary (d*N1),
    if 3 ≤ i then [] else unary ((d*N1)^2),
    if 4 ≤ i then [] else unary ((d*N1)^3),
    if 5 ≤ i then [] else unary ((d*N1)^4),
    unary (4*N2), unary (4*N2+n), unary (8*(d*N1)^4), [],
    if 6 ≤ i then [] else unary 1,
    if 7 ≤ i then [] else unary 4,
    if 8 ≤ i then [] else unary 8, [], []]

def clearLabel (i : ℕ) : Option Label :=
  if h : i < 8 then some (.inr (.inr (.clear ⟨i,h⟩))) else none

theorem trim_step (a d N1 N2 n : ℕ) :
    advance program (⟨some (stageLabel 10), idle, arithmeticBank a d N1 N2 n 10⟩ : Config) =
      ⟨clearLabel 0, idle, cleanBank a d N1 N2 n 0⟩ := by
  simp only [advance, TM2.step, stageLabel, show ¬10 < 10 by decide, ↓reduceDIte,
    program, TM2.stepAux, Option.getD_some]
  apply congrArg (fun S => (⟨clearLabel 0, idle, S⟩ : Config))
  funext k
  fin_cases k <;> simp [arithmeticBank, cleanBank, unary, Nat.sub_sub]

theorem clear_register (i : Fin 8) (bank : Fin 22 → List Bool) (q : List Bool)
    (s : Bool) (w : MatrixUnaryPower.Control) :
    run (q.length+1) (⟨some (.inr (.inr (.clear i))), (s,w),
      Function.update bank (temporary i) q⟩ : Config) =
      ⟨clearNext i, (false,w), Function.update bank (temporary i) []⟩ := by
  induction q generalizing s with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, run, Function.iterate_one, advance,
        TM2.step, program, TM2.stepAux, Function.update_self, List.head?_nil,
        List.tail_nil, Option.isSome_none, cond_false]
      simp only [clearExit]
      cases h : clearNext i <;> simp [TM2.stepAux, h]
  | cons b q ih =>
      rw [List.length_cons, run, Function.iterate_succ_apply]
      change run (q.length+1) (advance program _) = _
      have hstep : advance program (⟨some (.inr (.inr (.clear i))), (s,w),
          Function.update bank (temporary i) (b::q)⟩ : Config) =
          ⟨some (.inr (.inr (.clear i))), (true,w), Function.update bank (temporary i) q⟩ := by
        simp [advance, TM2.step, program, TM2.stepAux, Function.update_self,
          Function.update_idem]
      rw [hstep]
      exact ih true

def garbage (a d N1 i : ℕ) : ℕ :=
  [2^a, d*N1, (d*N1)^2, (d*N1)^3, (d*N1)^4, 1, 4, 8].getD i 0

set_option maxHeartbeats 0 in
theorem clean_step (a d N1 N2 n : ℕ) (i : Fin 8) :
    run (garbage a d N1 i.val+1)
      (⟨clearLabel i.val, idle, cleanBank a d N1 N2 n i.val⟩ : Config) =
      ⟨clearLabel (i.val+1), idle, cleanBank a d N1 N2 n (i.val+1)⟩ := by
  have hinput : Function.update (cleanBank a d N1 N2 n i.val) (temporary i)
      (unary (garbage a d N1 i.val)) = cleanBank a d N1 N2 n i.val := by
    apply Function.update_eq_self_iff.mpr
    fin_cases i <;> rfl
  have houtput : Function.update (cleanBank a d N1 N2 n i.val) (temporary i) [] =
      cleanBank a d N1 N2 n (i.val+1) := by
    funext k
    fin_cases i <;> fin_cases k <;> rfl
  have h := clear_register i (cleanBank a d N1 N2 n i.val)
    (unary (garbage a d N1 i.val)) false ((false,false),none)
  rw [hinput, houtput] at h
  have hlabel : clearLabel i.val = some (.inr (.inr (.clear i))) := by
    simp [clearLabel, i.isLt]
  have hnext : clearNext i = clearLabel (i.val+1) := by rfl
  simpa only [unary, List.length_replicate, hlabel, hnext] using h

def cleanTime (a d N1 k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (garbage a d N1 i+1)

theorem clean_run (a d N1 N2 n k : ℕ) (hk : k ≤ 8) :
    run (cleanTime a d N1 k) (⟨clearLabel 0, idle, cleanBank a d N1 N2 n 0⟩ : Config) =
      ⟨clearLabel k, idle, cleanBank a d N1 N2 n k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hi := ih (by omega)
      simp only [cleanTime, Finset.sum_range_succ] at hi ⊢
      rw [run_add, hi]
      exact clean_step a d N1 N2 n ⟨k, by omega⟩

def exactBound (a d N1 N2 n : ℕ) : ℕ :=
  (4*2^a+5*a+7)+1+arithmeticTime a d N1 N2 n 10+1+cleanTime a d N1 8

/-- The same fixed finite controller handles every tuple of scalar inputs.
The five inputs are unchanged and every non-output workspace is empty. -/
theorem scalar_run (a d N1 N2 n : ℕ) :
    ∃ t ≤ exactBound a d N1 N2 n,
      run t (⟨some (.inl (.inr false)), idle, inputBank a d N1 N2 n⟩ : Config) =
        ⟨none, idle, outputBank a d N1 N2 n⟩ := by
  obtain ⟨u, hu, hue⟩ := power_stage program (fun _ => rfl) a d N1 N2 n
  change run u (⟨some (.inl (.inr false)), idle, inputBank a d N1 N2 n⟩ : Config) =
    ⟨some (.inr (.inr .setup)), idle, powerReadyBank a d N1 N2 n⟩ at hue
  obtain ⟨v, hv, hve⟩ := arithmetic_run a d N1 N2 n 10 le_rfl
  have hc := clean_run a d N1 N2 n 8 le_rfl
  refine ⟨u+1+v+1+cleanTime a d N1 8, by unfold exactBound; omega, ?_⟩
  rw [run_add (u+1+v+1) (cleanTime a d N1 8), run_add (u+1+v) 1,
    run_add (u+1) v, run_add u 1]
  rw [hue]
  simp only [run_one]
  rw [setup_step, hve, trim_step, hc]
  rfl

theorem exactBound_formula (a d N1 N2 n : ℕ) :
    exactBound a d N1 N2 n = 9*2^a+5*a+17*(d*N1)+3*(d*N1)^2+
      3*(d*N1)^3+19*(d*N1)^4+4*d+16*N2+2*n+146 := by
  norm_num [exactBound, arithmeticTime, cleanTime, Finset.sum_range_succ,
    rowOperand, widthOperand, columnOperand, garbage, MatrixAddressMachine.exactTime]
  ring

/-- Every unary intermediate is already bounded by an input scalar or the
fourth power of the column base. This is output-sensitive linear work. -/
theorem exactBound_le (a d N1 N2 n : ℕ) :
    exactBound a d N1 N2 n ≤ 200*(2^a+a+d+N1+N2+n+(d*N1)^4+1) := by
  rw [exactBound_formula]
  have h₁ : d*N1 ≤ (d*N1)^4 := Nat.le_self_pow (by decide) _
  have h₂ : (d*N1)^2 ≤ (d*N1)^4 := by
    by_cases h : d*N1=0
    · simp [h]
    · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero h) (by decide)
  have h₃ : (d*N1)^3 ≤ (d*N1)^4 := by
    by_cases h : d*N1=0
    · simp [h]
    · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero h) (by decide)
  omega

theorem scalar_run_bound (a d N1 N2 n : ℕ) :
    ∃ t ≤ 200*(2^a+a+d+N1+N2+n+(d*N1)^4+1),
      run t (⟨some (.inl (.inr false)), idle, inputBank a d N1 N2 n⟩ : Config) =
        ⟨none, idle, outputBank a d N1 N2 n⟩ := by
  obtain ⟨t, ht, he⟩ := scalar_run a d N1 N2 n
  exact ⟨t, ht.trans (exactBound_le a d N1 N2 n), he⟩

end EthInapproximability.CurrentPaper.MatrixScalarParameters
