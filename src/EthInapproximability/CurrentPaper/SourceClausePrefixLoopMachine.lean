import EthInapproximability.CurrentPaper.SourceClausePrefixFullCallback
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
Finite-control physical unary loop around the already checked callback.
The generic parameters are the *types* of the fixed callback's finite label
and control sets, not runtime inputs or a list of callback results.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopMachine

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev CoreStack := PrefixSharedCore.Stack
abbrev Stack := CoreStack ⊕ Fin 2

def core : CoreStack ↪ Stack := Function.Embedding.inl
def source : Stack := .inl (.inl 0)
def vertex : Stack := .inl (.inl 1)
def fuel : Stack := .inr 0
def temp : Stack := .inr 1

inductive Admin where
  | copyScan | copyRestore | check | increment
  deriving DecidableEq, Fintype

abbrev Label (L : Type*) := L ⊕ Admin
abbrev Control (V : Type*) := V × Option Bool
abbrev Config (L V : Type*) :=
  TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)

noncomputable def program {L V : Type*}
    (P : L → TM2.Stmt (fun _ : CoreStack => Bool) L V)
    (start : L) (initial : V) :
    Label L → TM2.Stmt (fun _ : Stack => Bool) (Label L) (Control V)
  | .inl l => BitMachineStackEmbedding.stmt core Sum.inl
      (fun v => (v, none)) Prod.fst (some (.inr .increment)) (P l)
  | .inr .copyScan => BitMachineBroadcast.scanStep
      source temp (.inr .copyScan) (.inr .copyRestore)
  | .inr .copyRestore => BitMachineBroadcast.restoreStep
      temp [source, fuel] (.inr .copyRestore) (.inr .check)
  | .inr .check => pop fuel (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (load (fun _ => (initial, none)) (goto (fun _ => .inl start)))
        halt)
  | .inr .increment => push vertex (fun _ => true)
      (load (fun _ => (initial, none)) (goto (fun _ => .inr .check)))

noncomputable def blank (n ordinal : ℕ)
    (saved output count : List Bool) (fuelWord : List Bool) :
    Stack → List Bool :=
  Sum.elim (PrefixGateReady.blank n ordinal saved output count)
    (fun i => if i = 0 then fuelWord else [])

theorem source_word (n ordinal : ℕ) (saved output count fuelWord : List Bool) :
    blank n ordinal saved output count fuelWord source =
      List.replicate n true := by rfl

theorem temp_empty (n ordinal : ℕ) (saved output count fuelWord : List Bool) :
    blank n ordinal saved output count fuelWord temp = [] := by rfl

theorem fuel_word (n ordinal : ℕ) (saved output count fuelWord : List Bool) :
    blank n ordinal saved output count fuelWord fuel = fuelWord := by rfl

theorem copy_prep {L V : Type*}
    (P : L → TM2.Stmt (fun _ : CoreStack => Bool) L V)
    (start : L) (initial : V)
    (n : ℕ) (saved output count : List Bool) :
    ((advance (program P start initial))^[2 * n + 2])
      (⟨some (.inr .copyScan), (initial, none),
        blank n 0 saved output count []⟩ : Config L V) =
      ⟨some (.inr .check), (initial, none),
        blank n 0 saved output count (List.replicate n true)⟩ := by
  let P' := program P start initial
  let B := blank n 0 saved output count []
  let bits := List.replicate n true
  have hs := BitMachineBroadcast.scan_run P' source temp
    (by simp [source, temp]) (.inr .copyScan) (.inr .copyRestore)
    (by rfl) initial none bits [] B
  have hi : BitMachineBroadcast.contents source temp B bits [] = B := by
    rw [BitMachineBroadcast.contents]
    have hsource : B source = bits := source_word n 0 saved output count []
    have htemp : B temp = [] := temp_empty n 0 saved output count []
    rw [← hsource, Function.update_eq_self, ← htemp, Function.update_eq_self]
  rw [hi] at hs
  simp only [List.append_nil] at hs
  have hr := BitMachineBroadcast.restore_run P' temp [source, fuel]
    (by simp [source, fuel]) (by simp [temp, source, fuel])
    (.inr .copyRestore) (.inr .check) (by rfl) initial none
    bits.reverse (Function.update B source [])
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have he := (BitMachineBroadcast.run_add P' hs (bits.length + 1)).trans hr
  have hblank : blank n 0 saved output count bits = Function.update B fuel bits := by
    funext k
    cases k with
    | inl c => simp [blank, B, fuel, Function.update_of_ne]
    | inr i => fin_cases i <;> simp [blank, B, fuel]
  have hf :
      Function.update
          (BitMachineBroadcast.prepend [source, fuel] bits
            (Function.update B source [])) temp [] =
        blank n 0 saved output count bits := by
    rw [hblank]
    funext k
    by_cases ht : k = temp
    · subst k
      have hbt : B temp = [] := temp_empty n 0 saved output count []
      simp only [Function.update_self, Function.update_of_ne (by decide : temp ≠ fuel)]
      exact hbt.symm
    · by_cases hs : k = source
      · subst k
        have hbs : B source = bits := source_word n 0 saved output count []
        simp only [Function.update_of_ne (by decide : source ≠ temp),
          Function.update_of_ne (by decide : source ≠ fuel)]
        simp only [BitMachineBroadcast.prepend, List.mem_cons,
          eq_self, true_or, ite_true, Function.update_self]
        simpa using hbs.symm
      · by_cases hf : k = fuel
        · subst k
          simpa [BitMachineBroadcast.prepend, source, fuel, temp,
            Function.update_of_ne] using
            (fuel_word n 0 saved output count []).symm
        · simp [BitMachineBroadcast.prepend, Function.update_of_ne,
            ht, hs, hf]
  rw [hf] at he
  simpa only [BitMachineBroadcast.run, List.length_replicate,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    P', B, bits] using he

theorem check_more {L V : Type*}
    (P : L → TM2.Stmt (fun _ : CoreStack => Bool) L V)
    (start : L) (initial : V)
    (n v : ℕ) (saved output count : List Bool) (rest : List Bool) :
    advance (program P start initial)
      ⟨some (.inr .check), (initial, none),
        blank n v saved output count (true :: rest)⟩ =
      ⟨some (.inl start), (initial, none),
        blank n v saved output count rest⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some]
  rw [fuel_word]
  simp only [List.head?_cons, Option.isSome_some, Bool.cond_true,
    List.tail_cons]
  congr 1
  funext k
  by_cases hk : k = fuel
  · subst k
    simp [blank, fuel]
  · simp only [Function.update_of_ne hk]
    cases k with
    | inl _ => rfl
    | inr i => fin_cases i <;> simp [blank, fuel] at hk ⊢

theorem check_done {L V : Type*}
    (P : L → TM2.Stmt (fun _ : CoreStack => Bool) L V)
    (start : L) (initial : V)
    (n v : ℕ) (saved output count : List Bool) :
    advance (program P start initial)
      ⟨some (.inr .check), (initial, none),
        blank n v saved output count []⟩ =
      ⟨none, (initial, none), blank n v saved output count []⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, blank, fuel]

theorem increment_step {L V : Type*}
    (P : L → TM2.Stmt (fun _ : CoreStack => Bool) L V)
    (start : L) (initial : V)
    (n v : ℕ) (saved output count fuelWord : List Bool) :
    advance (program P start initial)
      ⟨some (.inr .increment), (initial, none),
        blank n v saved output count fuelWord⟩ =
      ⟨some (.inr .check), (initial, none),
        blank n (v + 1) saved output count fuelWord⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some]
  congr 1
  funext k
  by_cases hk : k = vertex
  · subst k
    simp only [Function.update_self]
    change true :: List.replicate v true = List.replicate (v + 1) true
    simp [List.replicate_succ]
  · simp only [Function.update_of_ne hk]
    cases k with
    | inl c =>
      cases c with
      | inl i => fin_cases i <;> simp [blank, PrefixGateReady.blank,
          PrefixGateReady.coreWords, vertex] at hk ⊢
      | inr i => rfl
    | inr i => rfl

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopMachine
