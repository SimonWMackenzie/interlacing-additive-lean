import EthInapproximability.CurrentPaper.SourceListEncoding
import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Actual OR over a canonical list of singleton Boolean outputs

Source: frozen v8 `06-eth.tex`, the final some-YES/every-NO branch test.
The list mapper writes `SourceListEncoding.encode (xs.map fun b => [b])`.
After scanning the count field, each canonical singleton item has the fixed
four-cell form `true,true,false,b`. This finite Boolean-stack program ORs
their payload bits. It halts on every input in linear time. Its semantic
correctness is stated only for canonical mapper output; malformed packets
may produce an arbitrary Boolean and are not confused with validated lists.
-/

namespace EthInapproximability.CurrentPaper.SourceListOR

open Turing Turing.TM2.Stmt BitMachineEncoding EncodedCommunication

inductive Label where
  | countTag | countPayload | itemTag | itemLength | itemEnd | itemBit
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool

def setPopped (v : Control) (b : Option Bool) : Control := (v.1, b)
def finish : TM2.Stmt (fun _ : Fin 2 => Bool) Label Control :=
  push 1 Prod.fst halt
def fail : TM2.Stmt (fun _ : Fin 2 => Bool) Label Control :=
  push 1 (fun _ => false) halt

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .countTag => pop 0 setPopped
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (goto (fun _ => .countPayload)) (goto (fun _ => .itemTag))) fail)
  | .countPayload => pop 0 setPopped
      (branch (fun v => v.2.isSome) (goto (fun _ => .countTag)) fail)
  | .itemTag => pop 0 setPopped
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (goto (fun _ => .itemLength)) fail) finish)
  | .itemLength => pop 0 setPopped
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (goto (fun _ => .itemEnd)) fail) fail)
  | .itemEnd => pop 0 setPopped
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          fail (goto (fun _ => .itemBit))) fail)
  | .itemBit => pop 0
      (fun v b => (v.1 || b.getD false, b))
      (branch (fun v => v.2.isSome) (goto (fun _ => .itemTag)) fail)

abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label Control

def cfg (l : Option Label) (v : Control) (input output : List Bool) : Config :=
  ⟨l, v, ![input, output]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) : run (t + 1) c = run t (advance program c) := by
  exact Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run, Nat.add_comm t u, Function.iterate_add_apply]

theorem count_pair (acc b : Bool) (rest out : List Bool) (p : Option Bool) :
    run 2 (cfg (some .countTag) (acc, p) (true :: b :: rest) out) =
      cfg (some .countTag) (acc, some b) rest out := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, setPopped]
  funext k; fin_cases k <;> rfl

theorem count_end (acc : Bool) (rest out : List Bool) (p : Option Bool) :
    advance program (cfg (some .countTag) (acc, p) (false :: rest) out) =
      cfg (some .itemTag) (acc, some false) rest out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, setPopped]
  funext k; fin_cases k <;> rfl

theorem item_four (acc b : Bool) (rest out : List Bool) (p : Option Bool) :
    run 4 (cfg (some .itemTag) (acc, p) (true :: true :: false :: b :: rest) out) =
      cfg (some .itemTag) (acc || b, some b) rest out := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, setPopped]
  funext k; fin_cases k <;> rfl

theorem item_end (acc : Bool) (out : List Bool) (p : Option Bool) :
    advance program (cfg (some .itemTag) (acc, p) [] out) =
      cfg none (acc, none) [] (acc :: out) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, setPopped, finish]
  funext k; fin_cases k <;> rfl

theorem count_field_run (bits suffix out : List Bool) (acc : Bool) (p : Option Bool) :
    run (2 * bits.length + 1)
      (cfg (some .countTag) (acc, p) (field bits ++ suffix) out) =
      cfg (some .itemTag) (acc, some false) suffix out := by
  induction bits generalizing p with
  | nil => simpa [field, run] using count_end acc suffix out p
  | cons b bits ih =>
      rw [show 2 * (b :: bits).length + 1 = 2 + (2 * bits.length + 1) by simp; omega,
        run_add]
      simp only [field, List.cons_append]
      rw [count_pair acc b (field bits ++ suffix) out p]
      exact ih (some b)

def singletonFields : List Bool → List Bool
  | [] => []
  | b :: rest => true :: true :: false :: b :: singletonFields rest

theorem singletonFields_eq (xs : List Bool) :
    singletonFields xs = SourceListEncoding.fields (xs.map fun b => [b]) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp [singletonFields, SourceListEncoding.fields, natField, field, ih]

theorem singletonFields_length (xs : List Bool) :
    (singletonFields xs).length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp only [singletonFields, List.length_cons]
      rw [ih]
      omega

theorem items_run (xs out : List Bool) (acc : Bool) (p : Option Bool) :
    run (4 * xs.length + 1)
      (cfg (some .itemTag) (acc, p) (singletonFields xs) out) =
      cfg none (acc || xs.any id, none) [] ((acc || xs.any id) :: out) := by
  induction xs generalizing acc p with
  | nil =>
      simpa [singletonFields, run] using item_end acc out p
  | cons b xs ih =>
      rw [show 4 * (b :: xs).length + 1 = 4 + (4 * xs.length + 1) by simp; omega,
        run_add]
      simp only [singletonFields]
      rw [item_four acc b (singletonFields xs) out p]
      simpa [Bool.or_assoc] using ih (acc || b) (some b)

theorem canonical_run (xs : List Bool) :
    run ((SourceListEncoding.encode (xs.map fun b => [b])).length + 1)
      (cfg (some .countTag) (false, none)
        (SourceListEncoding.encode (xs.map fun b => [b])) []) =
      cfg none (xs.any id, none) [] [xs.any id] := by
  have hcount := count_field_run (xs.length.bits) (singletonFields xs) [] false none
  have hitems := items_run xs [] false (some false)
  simp only [Bool.false_or] at hitems
  have hencode : SourceListEncoding.encode (xs.map fun b => [b]) =
      field xs.length.bits ++ singletonFields xs := by
    simp [SourceListEncoding.encode, natField, singletonFields_eq]
  rw [hencode, List.length_append, field_length, show
    2 * xs.length.bits.length + 1 + (singletonFields xs).length + 1 =
      (2 * xs.length.bits.length + 1) + (4 * xs.length + 1) by
        have hlen := singletonFields_length xs
        omega,
    run_add, hcount]
  exact hitems

theorem nil_halts (l : Label) (v : Control) (out : List Bool) :
    (advance program (cfg (some l) v [] out)).l = none := by
  rcases v with ⟨acc, p⟩
  cases l <;> simp [advance, TM2.step, TM2.stepAux, program, cfg,
    setPopped, finish, fail]

theorem cons_progress (l : Label) (v : Control) (b : Bool)
    (rest out : List Bool) :
    (advance program (cfg (some l) v (b :: rest) out)).l = none ∨
      ∃ l' v', advance program (cfg (some l) v (b :: rest) out) =
        cfg (some l') v' rest out := by
  rcases v with ⟨acc, p⟩
  cases l <;> cases b <;> simp [advance, TM2.step, TM2.stepAux,
    program, cfg, setPopped, finish, fail]
  all_goals funext k; fin_cases k <;> rfl

/-- Every transition either consumes one input cell or halts with a Boolean.
There is no unbounded-register or unit-cost list traversal in this scanner. -/
theorem total (l : Label) (v : Control) (input out : List Bool) :
    ∃ t ≤ input.length + 1,
      (run t (cfg (some l) v input out)).l = none := by
  induction input generalizing l v out with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      rw [show 1 = 0 + 1 from rfl, run_succ]
      exact nil_halts l v out
  | cons b rest ih =>
      rcases cons_progress l v b rest out with hh | ⟨l', v', hs⟩
      · refine ⟨1, by simp, ?_⟩
        rw [show 1 = 0 + 1 from rfl, run_succ]
        exact hh
      · obtain ⟨t, ht, hhalt⟩ := ih l' v' out
        refine ⟨t + 1, by simp at ht ⊢; omega, ?_⟩
        rw [show t + 1 = 1 + t by omega, run_add]
        change (run t (advance program (cfg (some l) v (b :: rest) out))).l = none
        rw [hs]
        exact hhalt

def result (input : List Bool) : List Bool :=
  (run (input.length + 1) (cfg (some .countTag) (false, none) input [])).stk 1

theorem result_canonical (xs : List Bool) :
    result (SourceListEncoding.encode (xs.map fun b => [b])) = [xs.any id] := by
  have h := congrArg (fun c : Config => c.stk 1) (canonical_run xs)
  simpa only [result, cfg] using h

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 .countTag ((false, none) : Control) program

theorem rawInit_eq (input : List Bool) :
    rawInit (0 : Fin 2) .countTag ((false, none) : Control) input =
      cfg (some .countTag) (false, none) input [] := by
  unfold rawInit cfg
  congr 1
  funext k; fin_cases k <;> rfl

theorem total_at_bound (input : List Bool) :
    (run (input.length + 1) (cfg (some .countTag) (false, none) input [])).l = none := by
  obtain ⟨t, ht, hh⟩ := total .countTag (false, none) input []
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht
  rw [hu, run_add]
  have hs := BitMachineSubroutine.run_halted program
    (run t (cfg (some .countTag) (false, none) input [])) hh u
  change run u (run t (cfg (some .countTag) (false, none) input [])) =
    run t (cfg (some .countTag) (false, none) input []) at hs
  rw [hs]
  exact hh

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (input.length + 1) := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 .countTag ((false, none) : Control)
    program input (result input) (input.length + 1) (input.length + 1) le_rfl
  · rw [rawInit_eq]
    exact total_at_bound input
  · rw [rawInit_eq]
    rfl

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 1, 1, ?_⟩
  intro input
  simpa using outputs input

end EthInapproximability.CurrentPaper.SourceListOR
