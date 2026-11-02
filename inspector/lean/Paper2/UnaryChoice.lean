import EthInapproximability.CurrentPaper.BitMachineClearBank
import Mathlib.Tactic

/-! Physical nested unary choice, with no supplied decision bit. -/

namespace Paper2.UnaryChoice

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding

inductive Choice where
  | first | second | third
  deriving DecidableEq, Fintype, Repr

inductive Label where
  | copyScan | copyRestore | compareA | compareB
  | clear (i : Fin 6) | done
  deriving DecidableEq, Fintype

abbrev Control := Choice × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 5 => Bool) Label Control

def contents (i a b copy scratch : List Bool) : Fin 5 → List Bool :=
  ![i, a, b, copy, scratch]

def cfg (l : Option Label) (v : Control)
    (i a b copy scratch : List Bool) : Config :=
  ⟨l, v, contents i a b copy scratch⟩

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Control
  | .copyScan =>
      pop 0 (fun v bit => (v.1, bit))
        (branch (fun v => v.2.isSome)
          (push 4 (fun v => v.2.getD false) (goto (fun _ => .copyScan)))
          (goto (fun _ => .copyRestore)))
  | .copyRestore =>
      pop 4 (fun v bit => (v.1, bit))
        (branch (fun v => v.2.isSome)
          (push 0 (fun v => v.2.getD false)
            (push 3 (fun v => v.2.getD false) (goto (fun _ => .copyRestore))))
          (load (fun v => (v.1, some true)) (goto (fun _ => .compareA))))
  | .compareA =>
      pop 1 (fun v bit => (v.1, bit))
        (branch (fun v => v.2.isSome)
          (pop 0 (fun v bit => (v.1, bit))
            (branch (fun v => v.2.isSome)
              (goto (fun _ => .compareA))
              (load (fun _ => (.first, none)) (goto (fun _ => .clear 0)))))
          (load (fun v => (v.1, some true)) (goto (fun _ => .compareB))))
  | .compareB =>
      pop 2 (fun v bit => (v.1, bit))
        (branch (fun v => v.2.isSome)
          (pop 3 (fun v bit => (v.1, bit))
            (branch (fun v => v.2.isSome)
              (goto (fun _ => .compareB))
              (load (fun _ => (.second, none)) (goto (fun _ => .clear 0)))))
          (load (fun _ => (.third, none)) (goto (fun _ => .clear 0))))
  | .clear j =>
      if h : j.val < 5 then
        BitMachineClearBank.clearStep ⟨j.val, h⟩ (.clear j)
          (.clear ⟨j.val + 1, by omega⟩)
      else BitMachineClearBank.finishStep id .done
  | .done => .halt

def initial (i a b : Nat) : Config :=
  cfg (some .copyScan) (.first, none)
    (List.replicate i true) (List.replicate a true)
    (List.replicate b true) [] []

def output (choice : Choice) : Config :=
  cfg none (choice, none) [] [] [] [] []

theorem copyScan_cons (v : Control) (x : Bool)
    (i a b copy scratch : List Bool) :
    advance program (cfg (some .copyScan) v (x :: i) a b copy scratch) =
      cfg (some .copyScan) (v.1, some x) i a b copy (x :: scratch) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k; fin_cases k <;> rfl

theorem copyScan_nil (v : Control) (a b copy scratch : List Bool) :
    advance program (cfg (some .copyScan) v [] a b copy scratch) =
      cfg (some .copyRestore) (v.1, none) [] a b copy scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

theorem copyRestore_cons (v : Control) (x : Bool)
    (i a b copy scratch : List Bool) :
    advance program (cfg (some .copyRestore) v i a b copy (x :: scratch)) =
      cfg (some .copyRestore) (v.1, some x) (x :: i) a b (x :: copy) scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k; fin_cases k <;> rfl

theorem copyRestore_nil (v : Control) (i a b copy : List Bool) :
    advance program (cfg (some .copyRestore) v i a b copy []) =
      cfg (some .compareA) (v.1, some true) i a b copy [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

theorem copyScan_run (v : Control) (i a b copy scratch : List Bool) :
    ((advance program)^[i.length + 1])
      (cfg (some .copyScan) v i a b copy scratch) =
      cfg (some .copyRestore) (v.1, none) [] a b copy (i.reverse ++ scratch) := by
  induction i generalizing v scratch with
  | nil => simpa using copyScan_nil v a b copy scratch
  | cons x i ih =>
      rw [List.length_cons, Function.iterate_succ_apply, copyScan_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copyRestore_run (v : Control) (i a b copy scratch : List Bool) :
    ((advance program)^[scratch.length + 1])
      (cfg (some .copyRestore) v i a b copy scratch) =
      cfg (some .compareA) (v.1, some true)
        (scratch.reverse ++ i) a b (scratch.reverse ++ copy) [] := by
  induction scratch generalizing v i copy with
  | nil => simpa using copyRestore_nil v i a b copy
  | cons x scratch ih =>
      rw [List.length_cons, Function.iterate_succ_apply, copyRestore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copy_run (i a b : Nat) :
  ((advance program)^[2 * i + 2]) (initial i a b) =
      cfg (some .compareA) (.first, some true)
        (List.replicate i true) (List.replicate a true)
        (List.replicate b true) (List.replicate i true) [] := by
  have hscan := copyScan_run (.first, none) (List.replicate i true)
    (List.replicate a true) (List.replicate b true) [] []
  have hrestore := copyRestore_run (.first, none) []
    (List.replicate a true) (List.replicate b true) []
    (List.replicate i true).reverse
  simp only [List.length_replicate, List.reverse_replicate, List.append_nil] at hscan hrestore
  change ((advance program)^[2 * i + 2]) _ = _
  rw [show 2 * i + 2 = (i + 1) + (i + 1) by omega,
    Nat.add_comm, Function.iterate_add_apply]
  simp only [initial]
  rw [hscan, hrestore]

theorem compareA_pair_step (choice : Choice)
    (i a b copy scratch : List Bool) :
    advance program
      (cfg (some .compareA) (choice, some true)
        (true :: i) (true :: a) b copy scratch) =
      cfg (some .compareA) (choice, some true) i a b copy scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k; fin_cases k <;> rfl

theorem compareA_pair (n : Nat) (choice : Choice)
    (i a b copy scratch : List Bool) :
    ((advance program)^[n])
      (cfg (some .compareA) (choice, some true)
        (List.replicate n true ++ i) (List.replicate n true ++ a) b copy scratch) =
      cfg (some .compareA) (choice, some true) i a b copy scratch := by
  induction n with
  | zero =>
      simp only [List.replicate_zero, List.nil_append, Function.iterate_zero, id_eq]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, List.cons_append,
        Function.iterate_succ_apply, compareA_pair_step, ih]

theorem compareA_less_step (choice : Choice)
    (b copy scratch aTail : List Bool) :
    advance program
      (cfg (some .compareA) (choice, some true) [] (true :: aTail) b copy scratch) =
      cfg (some (.clear 0)) (.first, none) [] aTail b copy scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k; fin_cases k <;> rfl

theorem compareA_ge_step (choice : Choice)
    (i b copy scratch : List Bool) :
    advance program
      (cfg (some .compareA) (choice, some true) i [] b copy scratch) =
      cfg (some .compareB) (choice, some true) i [] b copy scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

theorem compareB_pair_step (choice : Choice)
    (i a b copy scratch : List Bool) :
    advance program
      (cfg (some .compareB) (choice, some true)
        i a (true :: b) (true :: copy) scratch) =
      cfg (some .compareB) (choice, some true) i a b copy scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k; fin_cases k <;> rfl

theorem compareB_pair (n : Nat) (choice : Choice)
    (i a b copy scratch : List Bool) :
    ((advance program)^[n])
      (cfg (some .compareB) (choice, some true)
        i a (List.replicate n true ++ b) (List.replicate n true ++ copy) scratch) =
      cfg (some .compareB) (choice, some true) i a b copy scratch := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, List.cons_append,
        Function.iterate_succ_apply, compareB_pair_step, ih]

theorem compareB_less_step (choice : Choice)
    (i a scratch bTail : List Bool) :
    advance program
      (cfg (some .compareB) (choice, some true) i a (true :: bTail) [] scratch) =
      cfg (some (.clear 0)) (.second, none) i a bTail [] scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k; fin_cases k <;> rfl

theorem compareB_ge_step (choice : Choice)
    (i a copy scratch : List Bool) :
    advance program
      (cfg (some .compareB) (choice, some true) i a [] copy scratch) =
      cfg (some (.clear 0)) (.third, none) i a [] copy scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]

theorem compareA_lt (i a : Nat) (h : i < a)
    (b copy scratch : List Bool) :
    ((advance program)^[i + 1])
      (cfg (some .compareA) (.first, some true)
        (List.replicate i true) (List.replicate a true) b copy scratch) =
      cfg (some (.clear 0)) (.first, none) []
        (List.replicate (a - (i + 1)) true) b copy scratch := by
  obtain ⟨u, hu⟩ : ∃ u, a = i + 1 + u := ⟨a - (i + 1), by omega⟩
  subst a
  have hp := compareA_pair i Choice.first []
    (true :: List.replicate u true) b copy scratch
  have ha : List.replicate (i + 1 + u) true =
      List.replicate i true ++ true :: List.replicate u true := by
    rw [show i + 1 + u = i + (1 + u) by omega, List.replicate_add]
    rw [List.replicate_add]
    rfl
  rw [ha]
  simp only [List.append_nil] at hp
  rw [Function.iterate_succ_apply', hp, compareA_less_step]
  simp

theorem compareA_ge (i a : Nat) (h : a ≤ i)
    (b copy scratch : List Bool) :
    ((advance program)^[a + 1])
      (cfg (some .compareA) (.first, some true)
        (List.replicate i true) (List.replicate a true) b copy scratch) =
      cfg (some .compareB) (.first, some true)
        (List.replicate (i - a) true) [] b copy scratch := by
  obtain ⟨u, hu⟩ : ∃ u, i = a + u := ⟨i - a, by omega⟩
  subst i
  have hp := compareA_pair a Choice.first (List.replicate u true)
    [] b copy scratch
  simp only [List.append_nil, ← List.replicate_add] at hp
  rw [Function.iterate_succ_apply', hp, compareA_ge_step]
  simp

theorem compareB_lt (i b : Nat) (h : i < b)
    (row a scratch : List Bool) :
    ((advance program)^[i + 1])
      (cfg (some .compareB) (.first, some true)
        row a (List.replicate b true) (List.replicate i true) scratch) =
      cfg (some (.clear 0)) (.second, none) row a
        (List.replicate (b - (i + 1)) true) [] scratch := by
  obtain ⟨u, hu⟩ : ∃ u, b = i + 1 + u := ⟨b - (i + 1), by omega⟩
  subst b
  have hp := compareB_pair i Choice.first row a
    (true :: List.replicate u true) [] scratch
  have hb : List.replicate (i + 1 + u) true =
      List.replicate i true ++ true :: List.replicate u true := by
    rw [show i + 1 + u = i + (1 + u) by omega, List.replicate_add]
    rw [List.replicate_add]
    rfl
  rw [hb]
  simp only [List.append_nil] at hp
  rw [Function.iterate_succ_apply', hp, compareB_less_step]
  simp

theorem compareB_ge (i b : Nat) (h : b ≤ i)
    (row a scratch : List Bool) :
    ((advance program)^[b + 1])
      (cfg (some .compareB) (.first, some true)
        row a (List.replicate b true) (List.replicate i true) scratch) =
      cfg (some (.clear 0)) (.third, none) row a []
        (List.replicate (i - b) true) scratch := by
  obtain ⟨u, hu⟩ : ∃ u, i = b + u := ⟨i - b, by omega⟩
  subst i
  have hp := compareB_pair b Choice.first row a [] (List.replicate u true) scratch
  simp only [List.append_nil, ← List.replicate_add] at hp
  rw [Function.iterate_succ_apply', hp, compareB_ge_step]
  simp

theorem clear_run (choice : Choice) (i a b copy scratch : List Bool) :
    ((advance program)^[i.length + a.length + b.length + copy.length +
      scratch.length + 7])
      (cfg (some (.clear 0)) (choice, none) i a b copy scratch) =
      output choice := by
  have hsteps : ∀ j : Fin 5,
      program (.clear j.castSucc) =
        BitMachineClearBank.clearStep j (.clear j.castSucc) (.clear j.succ) := by
    intro j
    simp only [program, Fin.val_castSucc, j.isLt, dite_true]
    rfl
  have hfinish : program (.clear (Fin.last 5)) =
      BitMachineClearBank.finishStep id .done := rfl
  have hr := BitMachineClearBank.clear_bank_run program id .done 5
    (fun j : Fin 5 => j) (fun _ _ h => h) (fun j : Fin 6 => .clear j)
    hsteps hfinish choice (contents i a b copy scratch)
  have hsum : (∑ j : Fin 5, ((contents i a b copy scratch) j).length) + 5 + 1 + 1 =
      i.length + a.length + b.length + copy.length + scratch.length + 7 := by
    simp [Fin.sum_univ_succ, contents]
    omega
  have hclear : BitMachineClearBank.cleared (fun j : Fin 5 => j)
      (contents i a b copy scratch) = contents [] [] [] [] [] := by
    funext j
    simp only [BitMachineClearBank.cleared, exists_eq, ↓reduceIte]
    fin_cases j <;> rfl
  rw [hclear] at hr
  have hr' : ((advance program)^[(∑ j : Fin 5,
      ((contents i a b copy scratch) j).length) + 6])
      (cfg (some (.clear 0)) (choice, none) i a b copy scratch) =
      cfg (some .done) (choice, none) [] [] [] [] [] := by
    simpa [cfg, Nat.add_assoc] using hr
  rw [← hsum, show (∑ j : Fin 5, ((contents i a b copy scratch) j).length) +
      5 + 1 + 1 = (∑ j : Fin 5, ((contents i a b copy scratch) j).length) + 6 + 1
      by omega, Function.iterate_succ_apply', hr']
  simp [advance, TM2.step, TM2.stepAux, program, cfg, output]

def choiceOf (i a b : Nat) : Choice :=
  if i < a then .first else if i < b then .second else .third

/-- The two physical nested comparisons use a copied unary ticket, clear
all five data stacks, and leave only a three-valued finite control tag. -/
theorem choose (i a b : Nat) :
    ∃ t ≤ 20 * (i + a + b + 1),
      ((advance program)^[t]) (initial i a b) = output (choiceOf i a b) := by
  have hc := copy_run i a b
  by_cases ha : i < a
  · have hcmp := compareA_lt i a ha (List.replicate b true)
      (List.replicate i true) []
    have hclear := clear_run Choice.first []
      (List.replicate (a - (i + 1)) true)
      (List.replicate b true) (List.replicate i true) []
    simp only [List.length_nil, List.length_replicate, zero_add, add_zero] at hclear
    refine ⟨(a - (i + 1) + b + i + 7) + (i + 1) + (2 * i + 2), ?_, ?_⟩
    · omega
    · simp only [choiceOf, ha, ↓reduceIte]
      rw [Function.iterate_add_apply, hc,
        Function.iterate_add_apply, hcmp, hclear]
  · have hge : a ≤ i := by omega
    have hcmpA := compareA_ge i a hge (List.replicate b true)
      (List.replicate i true) []
    by_cases hb : i < b
    · have hcmpB := compareB_lt i b hb
        (List.replicate (i - a) true) [] []
      have hclear := clear_run Choice.second
        (List.replicate (i - a) true) []
        (List.replicate (b - (i + 1)) true) [] []
      simp only [List.length_nil, List.length_replicate, add_zero] at hclear
      refine ⟨(i - a + (b - (i + 1)) + 7) + (i + 1) +
        (a + 1) + (2 * i + 2), ?_, ?_⟩
      · omega
      · simp only [choiceOf, ha, hb, ↓reduceIte]
        rw [Function.iterate_add_apply, hc,
          Function.iterate_add_apply, hcmpA,
          Function.iterate_add_apply, hcmpB, hclear]
    · have hbg : b ≤ i := by omega
      have hcmpB := compareB_ge i b hbg
        (List.replicate (i - a) true) [] []
      have hclear := clear_run Choice.third
        (List.replicate (i - a) true) [] []
        (List.replicate (i - b) true) []
      simp only [List.length_nil, List.length_replicate, add_zero] at hclear
      refine ⟨(i - a + (i - b) + 7) + (b + 1) +
        (a + 1) + (2 * i + 2), ?_, ?_⟩
      · omega
      · simp only [choiceOf, ha, hb, ↓reduceIte]
        rw [Function.iterate_add_apply, hc,
          Function.iterate_add_apply, hcmpA,
          Function.iterate_add_apply, hcmpB, hclear]

#print axioms choose

end Paper2.UnaryChoice
