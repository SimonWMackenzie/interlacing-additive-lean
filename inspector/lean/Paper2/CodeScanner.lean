import Paper2.CodeHeaderMachine
import EthInapproximability.CurrentPaper.BitMachineClearBank

namespace Paper2.CodeScanner

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization
open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Stack := Fin 7 ⊕ Fin 1

inductive Admin where
  | check | after | clear (i : Fin 7)
  deriving DecidableEq, Fintype

abbrev Label := CodeHeaderMachine.Label ⊕ Admin
abbrev Control := CodeHeaderMachine.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def pending : Stack := .inr 0

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Admin.after) (CodeHeaderMachine.program l)
  | .inr .check => pop pending (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (load (fun _ => ((none, none), none)) (goto (fun _ => .inl .first))) halt)
  | .inr .after =>
      branch (fun v => decide (v.1.2 = some .append))
        (push pending (fun _ => true) (push pending (fun _ => true)
          (load (fun _ => ((none, none), none)) (goto (fun _ => .inr (.clear 0))))))
        (branch (fun v => decide (v.1.2 = some .branch3))
          (push pending (fun _ => true) (push pending (fun _ => true)
            (push pending (fun _ => true)
              (load (fun _ => ((none, none), none)) (goto (fun _ => .inr (.clear 0)))))))
          (load (fun _ => ((none, none), none)) (goto (fun _ => .inr (.clear 0)))))
  | .inr (.clear i) =>
      if h : i.val < 6 then
        BitMachineClearBank.clearStep (.inl ⟨i.val + 1, by omega⟩)
          (.inr (.clear i)) (.inr (.clear ⟨i.val + 1, by omega⟩))
      else BitMachineClearBank.finishStep (fun _ => (none, none)) (.inr .check)

def children : Code → List Code
  | .append a b => [a, b]
  | .branch3 _ _ _ a b c => [a, b, c]
  | _ => []

def bank (S : Fin 7 → List Bool) (fuel : List Bool) : Stack → List Bool :=
  Sum.elim S (fun _ => fuel)

def blank (input fuel : List Bool) : Stack → List Bool :=
  bank (CodeHeaderMachine.contents input [] [] [] [] [] []) fuel

def ready (input fuel : List Bool) : Config :=
  ⟨some (.inr .check), ((none, none), none), blank input fuel⟩

def headerBank (c : Code) (rest fuel : List Bool) : Stack → List Bool :=
  bank (CodeHeaderMachine.contents (CodeHeaderMachine.headerTail c rest)
    (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) [] (CodeHeaderMachine.headerWord c) []) fuel

theorem bank_update_pending (S : Fin 7 → List Bool) (fuel next : List Bool) :
    Function.update (bank S fuel) pending next = bank S next := by
  funext k
  cases k with
  | inl k => simp [bank, pending, Function.update]
  | inr k => fin_cases k; simp [bank, pending, Function.update]

theorem check_cons (input fuel : List Bool) :
    advance program (ready input (true :: fuel)) =
      (⟨some (.inl .first), ((none, none), none), blank input fuel⟩ : Config) := by
  change (⟨some (.inl .first), ((none, none), none),
    Function.update (blank input (true :: fuel)) pending fuel⟩ : Config) = _
  simp only [blank, bank_update_pending]

theorem check_nil (input : List Bool) :
    advance program (ready input []) =
      (⟨none, ((none, none), none), blank input []⟩ : Config) := by
  simp [advance, TM2.step, TM2.stepAux, program, ready, pending, blank, bank]

theorem header_run (c : Code) (rest fuel : List Bool) :
    ∃ t ≤ CodeHeaderMachine.headerCost c,
      ((advance program)^[t])
        (⟨some (.inl .first), ((none, none), none),
          blank (encodeCode c ++ rest) fuel⟩ : Config) =
        ⟨some (.inr .after), ((none, some (CodeHeaderMachine.headerKind c)), none),
          headerBank c rest fuel⟩ := by
  have hh := CodeHeaderMachine.run_header c rest
  have hhalt : (((advance CodeHeaderMachine.program)^[CodeHeaderMachine.headerCost c])
      (CodeHeaderMachine.initial (encodeCode c ++ rest))).l = none := by
    rw [← CodeHeaderMachine.run, hh]
    rfl
  obtain ⟨t, ht, hr⟩ := BitMachineSubroutine.lift_outputs
    CodeHeaderMachine.program program (some Admin.after) (by intro l; rfl)
    (none : Option Bool) (fun _ : Fin 1 => fuel)
    (CodeHeaderMachine.initial (encodeCode c ++ rest))
    (CodeHeaderMachine.headerCost c) hhalt
  refine ⟨t, ht, ?_⟩
  change ((advance program)^[t]) _ =
    liftCfg (some Admin.after) (none : Option Bool) (fun _ : Fin 1 => fuel)
      (CodeHeaderMachine.run (CodeHeaderMachine.headerCost c)
        (CodeHeaderMachine.initial (encodeCode c ++ rest))) at hr
  rw [hh] at hr
  simpa [liftCfg, CodeHeaderMachine.initial,
    CodeHeaderMachine.cfg, blank, bank, headerBank] using hr

theorem after_step (c : Code) (rest fuel : List Bool) :
    advance program
      (⟨some (.inr .after), ((none, some (CodeHeaderMachine.headerKind c)), none),
        headerBank c rest fuel⟩ : Config) =
      ⟨some (.inr (.clear 0)), ((none, none), none),
        headerBank c rest (List.replicate (children c).length true ++ fuel)⟩ := by
  cases c with
  | emit bits => rfl
  | ticket n => rfl
  | bit => rfl
  | append a b =>
      change (⟨some (.inr (.clear 0)), ((none, none), none),
        Function.update (Function.update (headerBank (.append a b) rest fuel)
          pending (true :: fuel)) pending (true :: true :: fuel)⟩ : Config) = _
      simp only [headerBank, bank_update_pending]
      rfl
  | branch3 n a b f s t =>
      change (⟨some (.inr (.clear 0)), ((none, none), none),
        Function.update (Function.update (Function.update
          (headerBank (.branch3 n a b f s t) rest fuel) pending (true :: fuel))
          pending (true :: true :: fuel)) pending (true :: true :: true :: fuel)⟩ : Config) = _
      simp only [headerBank, bank_update_pending]
      rfl

def clearBank (i : Fin 6) : Stack := .inl ⟨i.val + 1, by omega⟩

def clearCost (c : Code) : Nat :=
  (CodeHeaderMachine.headerN c).length + (CodeHeaderMachine.headerA c).length +
    (CodeHeaderMachine.headerB c).length + (CodeHeaderMachine.headerWord c).length + 7

theorem clearBank_injective : Function.Injective clearBank := by
  intro i j h
  have hv := congrArg (fun k : Stack => match k with | .inl k => k.val | .inr _ => 0) h
  simp only [clearBank] at hv
  apply Fin.ext
  omega

theorem cleared_headerBank (c : Code) (rest fuel : List Bool) :
    BitMachineClearBank.cleared clearBank (headerBank c rest fuel) =
      blank (CodeHeaderMachine.headerTail c rest) fuel := by
  funext k
  cases k with
  | inr k =>
      rw [BitMachineClearBank.cleared_foreign]
      · rfl
      · intro i; simp [clearBank]
  | inl k =>
      refine Fin.cases ?_ (fun i => ?_) k
      · rw [BitMachineClearBank.cleared_foreign]
        · rfl
        · intro i h
          have hv := congrArg (fun k : Stack => match k with | .inl k => k.val | .inr _ => 0) h
          simp only [clearBank] at hv
          omega
      · change BitMachineClearBank.cleared clearBank (headerBank c rest fuel)
          (clearBank i) = _
        rw [BitMachineClearBank.cleared_bank]
        fin_cases i <;> rfl

theorem clear_run (c : Code) (rest fuel : List Bool) :
    ((advance program)^[clearCost c])
      (⟨some (.inr (.clear 0)), ((none, none), none), headerBank c rest fuel⟩ : Config) =
      ready (CodeHeaderMachine.headerTail c rest) fuel := by
  have hsteps : ∀ i : Fin 6, program (.inr (.clear i.castSucc)) =
      BitMachineClearBank.clearStep (clearBank i)
        (.inr (.clear i.castSucc)) (.inr (.clear i.succ)) := by
    intro i
    simp only [program, Fin.val_castSucc, i.isLt, dite_true, clearBank]
    rfl
  have hf : program (.inr (.clear (Fin.last 6))) =
      BitMachineClearBank.finishStep (fun _ => (none, none)) (.inr .check) := rfl
  have hr := BitMachineClearBank.clear_bank_run program
    (fun _ => (none, none)) (.inr .check) 6 clearBank clearBank_injective
    (fun i => .inr (.clear i)) hsteps hf (none, none) (headerBank c rest fuel)
  have hc : (∑ i : Fin 6, ((headerBank c rest fuel) (clearBank i)).length) + 6 + 1 =
      clearCost c := by
    simp [Fin.sum_univ_succ, clearBank, headerBank, bank, CodeHeaderMachine.contents,
      clearCost]
    omega
  rw [hc, cleared_headerBank] at hr
  exact hr

def oneCost (c : Code) : Nat := CodeHeaderMachine.headerCost c + clearCost c + 2

theorem one_header (c : Code) (rest fuel : List Bool) :
    ∃ t ≤ oneCost c, ((advance program)^[t])
      (ready (encodeCode c ++ rest) (true :: fuel)) =
      ready (CodeHeaderMachine.headerTail c rest)
        (List.replicate (children c).length true ++ fuel) := by
  obtain ⟨h, hh, hr⟩ := header_run c rest fuel
  refine ⟨clearCost c + 1 + h + 1, by unfold oneCost; omega, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_one, check_cons,
    Function.iterate_add_apply, hr, Function.iterate_add_apply,
    Function.iterate_one, after_step, clear_run]

def scanCost : Code → Nat
  | .append a b => oneCost (.append a b) + scanCost a + scanCost b
  | .branch3 n a b f s t => oneCost (.branch3 n a b f s t) + scanCost f + scanCost s + scanCost t
  | c => oneCost c

theorem scan_one (c : Code) (rest fuel : List Bool) :
    ∃ t ≤ scanCost c, ((advance program)^[t])
      (ready (encodeCode c ++ rest) (true :: fuel)) = ready rest fuel := by
  induction c generalizing rest fuel with
  | emit bits =>
      simpa only [scanCost, CodeHeaderMachine.headerTail, children,
        List.length_nil, List.replicate_zero, List.nil_append] using
        one_header (.emit bits) rest fuel
  | ticket n =>
      simpa only [scanCost, CodeHeaderMachine.headerTail, children,
        List.length_nil, List.replicate_zero, List.nil_append] using
        one_header (.ticket n) rest fuel
  | bit =>
      simpa only [scanCost, CodeHeaderMachine.headerTail, children,
        List.length_nil, List.replicate_zero, List.nil_append] using
        one_header .bit rest fuel
  | append a b iha ihb =>
      obtain ⟨h, hh, hr⟩ := one_header (.append a b) rest fuel
      obtain ⟨x, hx, xr⟩ := iha (encodeCode b ++ rest) (true :: fuel)
      obtain ⟨y, hy, yr⟩ := ihb rest fuel
      have hr' : ((advance program)^[h])
          (ready (encodeCode (.append a b) ++ rest) (true :: fuel)) =
          ready (encodeCode a ++ (encodeCode b ++ rest)) (true :: true :: fuel) := by
        simpa [CodeHeaderMachine.headerTail, children, List.append_assoc] using hr
      refine ⟨y + x + h, by simp only [scanCost]; omega, ?_⟩
      rw [Function.iterate_add_apply, hr', Function.iterate_add_apply, xr, yr]
  | branch3 n a b f s t ihf ihs iht =>
      obtain ⟨h, hh, hr⟩ := one_header (.branch3 n a b f s t) rest fuel
      obtain ⟨x, hx, xr⟩ := ihf (encodeCode s ++ (encodeCode t ++ rest)) (true :: true :: fuel)
      obtain ⟨y, hy, yr⟩ := ihs (encodeCode t ++ rest) (true :: fuel)
      obtain ⟨z, hz, zr⟩ := iht rest fuel
      have hr' : ((advance program)^[h])
          (ready (encodeCode (.branch3 n a b f s t) ++ rest) (true :: fuel)) =
          ready (encodeCode f ++ (encodeCode s ++ (encodeCode t ++ rest)))
            (true :: true :: true :: fuel) := by
        simpa [CodeHeaderMachine.headerTail, children, List.append_assoc] using hr
      refine ⟨z + y + x + h, by simp only [scanCost]; omega, ?_⟩
      rw [Function.iterate_add_apply, hr', Function.iterate_add_apply, xr,
        Function.iterate_add_apply, yr, zr]

theorem scanCost_linear (c : Code) : scanCost c ≤ 5 * codeSize c := by
  induction c with
  | emit bits =>
      simp [scanCost, oneCost, clearCost, codeSize, CodeHeaderMachine.headerCost,
        CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
        CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]
      omega
  | ticket n =>
      simp [scanCost, oneCost, clearCost, codeSize, CodeHeaderMachine.headerCost,
        CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
        CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]
      omega
  | bit => decide
  | append a b ha hb =>
      simp [scanCost, oneCost, clearCost, codeSize, CodeHeaderMachine.headerCost,
        CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
        CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]
      omega
  | branch3 n a b f s t hf hs ht =>
      simp [scanCost, oneCost, clearCost, codeSize, CodeHeaderMachine.headerCost,
        CodeHeaderMachine.headerN, CodeHeaderMachine.headerA,
        CodeHeaderMachine.headerB, CodeHeaderMachine.headerWord]
      omega

/-- Actual fixed-control run skips exactly one serialized code, retains an
arbitrary suffix, and clears every work stack. The scope is valid code. -/
theorem skip_code (c : Code) (rest : List Bool) :
    ∃ t ≤ 5 * codeSize c + 1, ((advance program)^[t])
      (ready (encodeCode c ++ rest) [true]) =
      (⟨none, ((none, none), none), blank rest []⟩ : Config) := by
  obtain ⟨t, ht, hr⟩ := scan_one c rest []
  refine ⟨1 + t, by have := scanCost_linear c; omega, ?_⟩
  rw [Function.iterate_add_apply, hr, Function.iterate_one, check_nil]

#print axioms one_header
#print axioms scan_one
#print axioms scanCost_linear
#print axioms skip_code

end Paper2.CodeScanner
