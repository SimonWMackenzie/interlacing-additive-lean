import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Fixed physical coefficient for the bin exponent

From one unary word `true^n`, this fixed program writes the literal
constant 10000 on a separate bank and runs the preserving unary address
multiplier. Thus its output bank contains `true^(10000*n)`. The literal
constant is fixed finite instruction syntax, not an input-dependent register.
-/

namespace EthInapproximability.CurrentPaper.ETHBinsCoefficientScratch

open Turing Turing.TM2.Stmt BitMachineEncoding

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

inductive Label where
  | constant
  | multiply (label : MatrixAddressMachine.Label)
  deriving DecidableEq, Fintype

abbrev Stack := Fin 6
abbrev Control := Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def slots : Fin 6 ↪ Stack := ⟨id, by intro a b h; exact h⟩

def pushOn (r : Stack) : ℕ → TM2.Stmt (fun _ : Stack => Bool) Label Control →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | 0, q => q
  | k+1, q => push r (fun _ => true) (pushOn r k q)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .constant => pushOn 1 10000 (goto (fun _ => .multiply .outer))
  | .multiply l => BitMachineStackEmbedding.stmt slots
      Label.multiply id id none (MatrixAddressMachine.program l)

def unary (n : ℕ) : List Bool := List.replicate n true
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config := ⟨l,v,S⟩
def inputBank (n : ℕ) : Stack → List Bool := ![unary n,[],[],[],[],[]]
def constantBank (n : ℕ) : Stack → List Bool := ![unary n,unary 10000,[],[],[],[]]
def outputBank (n : ℕ) : Stack → List Bool :=
  ![unary n,unary 10000,[],[],[],unary (10000*n)]
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem pushOn_step (r : Stack) (k : ℕ)
    (q : TM2.Stmt (fun _ : Stack => Bool) Label Control)
    (v : Control) (S : Stack → List Bool) :
    TM2.stepAux (pushOn r k q) v S =
      TM2.stepAux q v (Function.update S r (unary k ++ S r)) := by
  induction k generalizing S with
  | zero => simp [pushOn, unary]
  | succ k ih =>
      simp only [pushOn, TM2.stepAux]
      rw [ih]
      simp only [Function.update_self]
      have he : Function.update (Function.update S r (true :: S r)) r
          (unary k ++ true :: S r) =
          Function.update S r (unary (k+1) ++ S r) := by
        funext j
        by_cases hj : j = r
        · subst j
          simp [unary, List.replicate_succ', List.append_assoc]
        · simp [hj]
      rw [he]

theorem constant_step (n : ℕ) :
    advance program (cfg (some .constant) false (inputBank n)) =
      cfg (some (.multiply .outer)) false (constantBank n) := by
  simp only [advance, TM2.step, program, cfg, Option.getD_some,
    pushOn_step, TM2.stepAux]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem multiply_run (n : ℕ) :
    ∃ t ≤ MatrixAddressMachine.exactTime n 10000 0,
      run t (cfg (some (.multiply .outer)) false (constantBank n)) =
        cfg none false (outputBank n) := by
  let input := MatrixAddressMachine.cfg (some .outer) false
    (unary n) (unary 10000) [] [] [] []
  let output := MatrixAddressMachine.cfg none false
    (unary n) (unary 10000) [] [] [] (unary (n*10000))
  have hr : ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime n 10000 0])
      input = output := by
    simpa only [Nat.add_zero, unary, List.append_nil] using
      MatrixAddressMachine.address_run n 10000 0 false []
  have hh : (((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime n 10000 0])
      input).l = none := by
    rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs slots
    (constantBank n) Label.multiply id id (fun _ => rfl) none
    MatrixAddressMachine.program program (fun _ => rfl)
    input (MatrixAddressMachine.exactTime n 10000 0) hh
  rw [hr] at he
  have hi : BitMachineStackEmbedding.cfg slots (constantBank n)
      Label.multiply id none input =
        cfg (some (.multiply .outer)) false (constantBank n) := by
    change (⟨_,_,BitMachineStackEmbedding.bank slots (constantBank n) input.stk⟩ : Config) = _
    congr 1
    funext k
    change BitMachineStackEmbedding.bank slots (constantBank n) input.stk (slots k) = _
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases k <;> rfl
  have ho : BitMachineStackEmbedding.cfg slots (constantBank n)
      Label.multiply id none output = cfg none false (outputBank n) := by
    change (⟨_,_,BitMachineStackEmbedding.bank slots (constantBank n) output.stk⟩ : Config) = _
    congr 1
    funext k
    change BitMachineStackEmbedding.bank slots (constantBank n) output.stk (slots k) = _
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases k <;> simp [outputBank, output, MatrixAddressMachine.cfg,
      unary, Nat.mul_comm]
  exact ⟨t, ht, by simpa only [run, hi, ho] using he⟩

def time (n : ℕ) : ℕ := 1 + MatrixAddressMachine.exactTime n 10000 0

theorem coefficient_run (n : ℕ) :
    ∃ t ≤ time n,
      run t (cfg (some .constant) false (inputBank n)) =
        cfg none false (outputBank n) := by
  obtain ⟨t, ht, hr⟩ := multiply_run n
  refine ⟨t+1, by dsimp [time]; omega, ?_⟩
  change ((advance program)^[t+1]) _ = _
  rw [Function.iterate_succ_apply]
  rw [constant_step]
  exact hr

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (5 : Stack) .constant false program

theorem outputs (n : ℕ) :
    machine.OutputsWithin (unary n) (unary (10000*n)) (time n) := by
  obtain ⟨t, ht, hr⟩ := coefficient_run n
  have hi : rawInit (0 : Stack) Label.constant false (unary n) =
      cfg (some .constant) false (inputBank n) := by
    simp [rawInit, cfg, inputBank]
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Stack) (5 : Stack) .constant false
    program (unary n) (unary (10000*n)) t (time n) ht
  · rw [hi, ← run, hr]; rfl
  · rw [hi, ← run, hr]; rfl

end EthInapproximability.CurrentPaper.ETHBinsCoefficientScratch
