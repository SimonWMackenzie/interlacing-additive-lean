import CurrentAdditive.RoundedCleanDraw
import EthInapproximability.CurrentPaper.SourceUnaryBinaryCall

/-! Fixed preparation of the rounded-draw banks from unary public a and b.
All input-dependent arithmetic is executed on stacks. -/

namespace EthInapproximability.CurrentPaper.RoundedPrepare

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev counter := SourceUnaryBinaryCall.counter
abbrev CounterStack := BitMachineIteration.Stack counter
abbrev Stack := RoundedCleanDraw.Stack ⊕ (CounterStack ⊕ Fin 3)
abbrev Control := BitMachineIteration.Control counter × Option Bool

def initial : Control := ((counter.initial, none), none)

def publicA : Stack := .inr (.inr 0)
def publicB : Stack := .inr (.inr 1)
def scratch : Stack := .inr (.inr 2)
def fuel : Stack := .inr (.inl (.inr 0))
def binary : Stack := .inr (.inl (.inl counter.input))
def alphabet : Stack := .inl (.inl (.inl (.inr 0)))
def cap : Stack := .inl (.inr 0)
def count : Stack := .inl (.inl (.inr 0))
def tape : Stack := .inl RoundedCleanDraw.tape
def output : Stack := .inl RoundedCleanDraw.output

inductive CopyStage where | fuel | cap | count | binary
  deriving DecidableEq, Fintype

def copySource : CopyStage → Stack
  | .fuel | .cap => publicA
  | .count => publicB
  | .binary => binary

def copyTarget : CopyStage → Stack
  | .fuel => fuel
  | .cap => cap
  | .count => count
  | .binary => alphabet

def copySlot (stage : CopyStage) (i : Fin 3) : Stack :=
  if i = 0 then copySource stage else if i = 1 then copyTarget stage else scratch

theorem copySlot_injective (stage : CopyStage) : Function.Injective (copySlot stage) := by
  intro i j h
  cases stage <;> fin_cases i <;> fin_cases j <;>
    simp [copySlot, copySource, copyTarget, publicA, publicB, scratch,
      fuel, cap, count, alphabet, binary] at h ⊢

def copyEmbed (stage : CopyStage) : Fin 3 ↪ Stack :=
  ⟨copySlot stage, copySlot_injective stage⟩

def counterEmbed : CounterStack ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro i j h; exact Sum.inl_injective (Sum.inr_injective h)⟩

inductive Label where
  | copy (stage : CopyStage) (l : BitMachineCopy.Label)
  | counter (l : BitMachineIteration.Label counter)
  | initialize
  deriving DecidableEq, Fintype

def copyNext : CopyStage → Label
  | .fuel => .copy .cap .scan
  | .cap => .copy .count .scan
  | .count => .counter (.inr .testFuel)
  | .binary => .initialize

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy stage l => stmt (copyEmbed stage) (Label.copy stage)
      (fun v => ((counter.initial, none), v)) Prod.snd
      (some (copyNext stage)) (BitMachineCopy.program l)
  | .counter l => stmt counterEmbed Label.counter
      (fun v => (v, none)) Prod.fst (some (.copy .binary .scan))
      (BitMachineIteration.program counter l)
  | .initialize => push output (fun _ => false)
      (load (fun _ => initial) halt)

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def initialBank (a b : ℕ) (bits : List Bool) : Stack → List Bool :=
  fun k => if k = publicA then List.replicate a true else
    if k = publicB then List.replicate b true else if k = tape then bits else []

def start (a b : ℕ) (bits : List Bool) : Config :=
  ⟨some (.copy .fuel .scan), initial, initialBank a b bits⟩

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem copy_run (stage : CopyStage) (S : Stack → List Bool)
    (htarget : S (copyTarget stage) = []) (hscratch : S scratch = []) :
    ∃ t ≤ 2 * (S (copySource stage)).length + 2,
      run t ⟨some (.copy stage .scan), initial, S⟩ =
        ⟨some (copyNext stage), initial,
          Function.update S (copyTarget stage) (S (copySource stage))⟩ := by
  let source := S (copySource stage)
  let c := BitMachineCopy.cfg (some .scan) none source [] []
  have hbank : bank (copyEmbed stage) S c.stk = S := by
    apply bank_eq_self
    intro i
    fin_cases i <;>
      simp [c, source, BitMachineCopy.cfg, BitMachineCopy.stackContents,
        copyEmbed, copySlot, htarget, hscratch]
  have hrun := BitMachineCopy.run_correct none source []
  simp only [List.append_nil] at hrun
  have hh : (((advance BitMachineCopy.program)^[2 * source.length + 2]) c).l = none := by
    change (BitMachineCopy.run _ c).l = none
    rw [hrun]
    rfl
  obtain ⟨t, ht, hr⟩ := outputs (copyEmbed stage) S (Label.copy stage)
    (fun v => ((counter.initial, none), v)) Prod.snd
    (by intro v; rfl) (some (copyNext stage)) BitMachineCopy.program program
    (by intro l; rfl) c (2 * source.length + 2) hh
  have he : (BitMachineCopy.cfg none none source source []).stk =
      Function.update c.stk 1 source := by
    funext i
    fin_cases i <;> simp [BitMachineCopy.cfg, BitMachineCopy.stackContents, c]
  change run t (cfg (copyEmbed stage) S (Label.copy stage)
      (fun v => ((counter.initial, none), v)) (some (copyNext stage)) c) =
    cfg (copyEmbed stage) S (Label.copy stage)
      (fun v => ((counter.initial, none), v)) (some (copyNext stage))
        (BitMachineCopy.run _ c) at hr
  rw [hrun] at hr
  refine ⟨t, ht, ?_⟩
  change run t ⟨some (.copy stage .scan), initial, bank (copyEmbed stage) S c.stk⟩ =
    ⟨some (copyNext stage), initial,
      bank (copyEmbed stage) S (BitMachineCopy.cfg none none source source []).stk⟩ at hr
  rw [he, bank_update, hbank] at hr
  simpa only [show copyEmbed stage 1 = copyTarget stage by rfl, source] using hr

def fueledBank (a b : ℕ) (bits : List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update (initialBank a b bits)
    fuel (List.replicate a true)) cap (List.replicate a true))
      count (List.replicate b true)

theorem copies_run (a b : ℕ) (bits : List Bool) :
    ∃ t ≤ 4 * a + 2 * b + 6,
      run t (start a b bits) =
        ⟨some (.counter (.inr .testFuel)), initial, fueledBank a b bits⟩ := by
  let S := initialBank a b bits
  let S₁ := Function.update S fuel (List.replicate a true)
  let S₂ := Function.update S₁ cap (List.replicate a true)
  obtain ⟨t₁, ht₁, hr₁⟩ := copy_run .fuel S (by rfl) (by rfl)
  obtain ⟨t₂, ht₂, hr₂⟩ := copy_run .cap S₁ (by rfl) (by rfl)
  obtain ⟨t₃, ht₃, hr₃⟩ := copy_run .count S₂ (by rfl) (by rfl)
  have h₁ : run t₁ (start a b bits) =
      ⟨some (.copy .cap .scan), initial, S₁⟩ := hr₁
  have h₂ : run t₂ ⟨some (.copy .cap .scan), initial, S₁⟩ =
      ⟨some (.copy .count .scan), initial, S₂⟩ := hr₂
  have h₃ : run t₃ ⟨some (.copy .count .scan), initial, S₂⟩ =
      ⟨some (.counter (.inr .testFuel)), initial, fueledBank a b bits⟩ := hr₃
  refine ⟨t₁ + t₂ + t₃, ?_, (run_add ((run_add h₁ t₂).trans h₂) t₃).trans h₃⟩
  simp [copySource, S, S₁, S₂, initialBank, publicA, publicB, tape,
    cap, fuel, List.length_replicate] at ht₁ ht₂ ht₃
  omega

def convertedBank (a b : ℕ) (bits : List Bool) : Stack → List Bool :=
  bank counterEmbed (fueledBank a b bits)
    (BitMachineIteration.finished counter a.bits).stk

theorem counter_run (a b : ℕ) (bits : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (a + 1) ^ 2,
      run t ⟨some (.counter (.inr .testFuel)), initial, fueledBank a b bits⟩ =
        ⟨some (.copy .binary .scan), initial, convertedBank a b bits⟩ := by
  let c := BitMachineIteration.ready counter [] (List.replicate a true)
  have hbank : bank counterEmbed (fueledBank a b bits) c.stk = fueledBank a b bits := by
    apply bank_eq_self
    intro k
    rw [show c.stk = _ from SourceUnaryBinaryCall.initial_bank (List.replicate a true)]
    rcases k with k | k
    · simp [counterEmbed, fueledBank, initialBank, fuel, cap, count,
        publicA, publicB, tape, Function.update]
    · fin_cases k <;> simp [counterEmbed, fueledBank, initialBank, fuel,
        cap, count, publicA, publicB, tape, Function.update]
  obtain ⟨t, ht, hr⟩ := SourceUnaryBinaryCall.raw_run (List.replicate a true)
  simp only [List.length_replicate] at ht hr
  have hh : (((advance (BitMachineIteration.program counter))^[t]) c).l = none := by
    change (BitMachineIteration.run counter t c).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, hur⟩ := outputs counterEmbed (fueledBank a b bits) Label.counter
    (fun v => (v, none)) Prod.fst (by intro v; rfl) (some (.copy .binary .scan))
    (BitMachineIteration.program counter) program (by intro l; rfl) c t hh
  change run u (cfg counterEmbed (fueledBank a b bits) Label.counter
      (fun v => (v, none)) (some (.copy .binary .scan)) c) =
    cfg counterEmbed (fueledBank a b bits) Label.counter
      (fun v => (v, none)) (some (.copy .binary .scan))
        (BitMachineIteration.run counter t c) at hur
  rw [hr] at hur
  change run u ⟨some (.counter (.inr .testFuel)), initial,
      bank counterEmbed (fueledBank a b bits) c.stk⟩ =
    ⟨some (.copy .binary .scan), initial, convertedBank a b bits⟩ at hur
  rw [hbank] at hur
  exact ⟨u, hu.trans ht, hur⟩

theorem converted_left (a b : ℕ) (bits : List Bool) (k : RoundedCleanDraw.Stack) :
    convertedBank a b bits (.inl k) = fueledBank a b bits (.inl k) := by
  apply bank_outside
  rintro ⟨j, h⟩
  cases h

theorem converted_public (a b : ℕ) (bits : List Bool) (k : Fin 3) :
    convertedBank a b bits (.inr (.inr k)) = fueledBank a b bits (.inr (.inr k)) := by
  apply bank_outside
  rintro ⟨j, h⟩
  cases h

theorem converted_counter (a b : ℕ) (bits : List Bool) (k : CounterStack) :
    convertedBank a b bits (.inr (.inl k)) =
      if k = .inl counter.input then a.bits else [] := by
  change bank counterEmbed _ _ (counterEmbed k) = _
  rw [bank_at, SourceUnaryBinaryCall.final_bank]

def finalBank (a b : ℕ) (bits : List Bool) : Stack → List Bool :=
  Function.update (Function.update (convertedBank a b bits) alphabet a.bits)
    output [false]

theorem last_copy_run (a b : ℕ) (bits : List Bool) :
    ∃ t ≤ 2 * a.bits.length + 3,
      run t ⟨some (.copy .binary .scan), initial, convertedBank a b bits⟩ =
        ⟨none, initial, finalBank a b bits⟩ := by
  have hs : convertedBank a b bits binary = a.bits := by
    simpa [binary] using converted_counter a b bits (.inl counter.input)
  have ht : convertedBank a b bits alphabet = [] := by
    rw [alphabet, converted_left]
    rfl
  have hw : convertedBank a b bits scratch = [] := by
    rw [scratch, converted_public]
    rfl
  obtain ⟨t, htime, hr⟩ := copy_run .binary (convertedBank a b bits) ht hw
  simp only [copySource, hs, copyNext, copyTarget] at htime hr
  have ho : (Function.update (convertedBank a b bits) alphabet a.bits) output = [] := by
    simp only [Function.update_of_ne (show output ≠ alphabet by decide)]
    rw [output, converted_left]
    rfl
  refine ⟨t + 1, by omega, ?_⟩
  have h := run_add hr 1
  have hstep : run 1 ⟨some .initialize, initial,
      Function.update (convertedBank a b bits) alphabet a.bits⟩ =
      ⟨none, initial, finalBank a b bits⟩ := by
    simp [run, advance, TM2.step, program, TM2.stepAux, ho, finalBank]
  exact h.trans hstep

def clock (a b : ℕ) : ℕ :=
  4 * a + 2 * b + 6 + UnaryBinaryEncoding.coefficient * (a + 1) ^ 2 +
    (2 * a.bits.length + 3)

theorem physical_prepare (a b : ℕ) (bits : List Bool) :
    ∃ t ≤ clock a b, run t (start a b bits) = ⟨none, initial, finalBank a b bits⟩ := by
  obtain ⟨u, hu, hr₁⟩ := copies_run a b bits
  obtain ⟨v, hv, hr₂⟩ := counter_run a b bits
  obtain ⟨w, hw, hr₃⟩ := last_copy_run a b bits
  refine ⟨u + v + w, by unfold clock; omega, ?_⟩
  exact (run_add ((run_add hr₁ v).trans hr₂) w).trans hr₃

theorem rounded_start_bank (a b : ℕ) (word suffix : List Bool) (hlen : word.length = b) :
    (fun k : RoundedCleanDraw.Stack => finalBank a b (word ++ suffix) (.inl k)) =
      (RoundedTicketUnary.start a.bits word suffix a).stk := by
  funext k
  rcases k with (((i | i) | i) | i)
  all_goals fin_cases i
  all_goals simp [finalBank, converted_left, fueledBank, initialBank,
    alphabet, cap, fuel, count, output, publicA, publicB, tape,
    RoundedCleanDraw.tape, RoundedCleanDraw.output, hlen,
    RoundedTicketUnary.start, RoundedTicketUnary.cfg, RoundedTicketUnary.bank,
    RoundedTicketUnary.rightBank, RoundedMachine.cfg, RoundedMachine.bank,
    RoundedMachine.rightBank, RoundedMachine.mulStart,
    BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]

#print axioms physical_prepare

end
end EthInapproximability.CurrentPaper.RoundedPrepare
