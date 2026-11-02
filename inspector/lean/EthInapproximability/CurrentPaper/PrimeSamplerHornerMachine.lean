import EthInapproximability.CurrentPaper.PrimeSamplerModularStep
import EthInapproximability.CurrentPaper.PrimeSamplerEntryAlgorithm
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Streaming physical Horner evaluation

Source: frozen v8 `B-effectivity-details.tex`, balanced-family entry queries.
Digits are unary words separated by one false bit, most-significant first.
The finite controller scans each digit, calls the literal modular multiply-
add, clears the obsolete operands and quotient, and moves the remainder to
the accumulator. No numerical arithmetic occurs in finite control.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerHornerMachine

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine
open scoped BigOperators

inductive Admin where
  | scan | clear (i : Fin 4) | move
  deriving DecidableEq, Fintype

abbrev Stack := Fin 10
abbrev Label := PrimeSamplerModularStep.Label ⊕ Admin
abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

structure Data where
  coordinate : List Bool := []
  accumulator : List Bool := []
  digit : List Bool := []
  count : List Bool := []
  remainder : List Bool := []
  product : List Bool := []
  modulus : List Bool := []
  quotient : List Bool := []
  saved : List Bool := []
  stream : List Bool := []

def Data.stacks (d : Data) : Stack → List Bool :=
  ![d.coordinate,d.accumulator,d.digit,d.count,d.remainder,d.product,d.modulus,d.quotient,d.saved,d.stream]

def clearStack (i : Fin 3) : Stack := ![1,2,7] i

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt (finSumFinEquiv : Fin 9 ⊕ Fin 1 ≃ Stack) (Equiv.refl _)
      (Equiv.refl _) (liftStmt (some (Admin.clear 0)) (PrimeSamplerModularStep.program l))
  | .inr .scan => pop 9 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (push 2 (fun _ => true) (goto (fun _ => .inr .scan)))
          (load (fun _ => (false,none)) (goto (fun _ => .inl (.inl .outer)))))
        (load (fun _ => (false,none)) halt))
  | .inr (.clear i) => if h : i.val<3 then
      BitMachineClearBank.clearStep (clearStack ⟨i.val,h⟩) (.inr (.clear i))
        (.inr (.clear ⟨i.val+1,by omega⟩))
      else BitMachineClearBank.finishStep (fun _ => false) (.inr .move)
  | .inr .move => pop 4 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 1 (fun _ => true) (goto (fun _ => .inr .move)))
        (load (fun _ => (false,none)) (goto (fun _ => .inr .scan))))

def cfg (l : Option Label) (v : Control) (d : Data) : Config := ⟨l,v,d.stacks⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c=run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_step {c d : Config} (h : advance program c=d) (t : ℕ) :
    run (t+1) c=run t d := by
  simp only [run, Function.iterate_succ_apply, h]

def encodeDigit (a : ℕ) : List Bool := List.replicate a true++[false]
def encode (as : List ℕ) : List Bool := as.flatMap encodeDigit

theorem scan_field (a b : ℕ) (d : Data) (v : Control) :
    run (a+1) (cfg (some (.inr .scan)) v
      {d with digit:=List.replicate b true,stream:=List.replicate a true++false::d.stream}) =
      cfg (some (.inl (.inl .outer))) (false,none)
        {d with digit:=List.replicate (b+a) true} := by
  induction a generalizing b v with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero, List.nil_append, run, Function.iterate_one]
      simp [advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
      funext k
      fin_cases k <;> rfl
  | succ a ih =>
      have hs : advance program (cfg (some (.inr .scan)) v
          {d with digit:=List.replicate b true,stream:=List.replicate (a+1) true++false::d.stream}) =
          cfg (some (.inr .scan)) (v.1,some true)
            {d with digit:=List.replicate (b+1) true,stream:=List.replicate a true++false::d.stream} := by
        simp [List.replicate_succ, advance, cfg, program, TM2.step, TM2.stepAux, Data.stacks]
        funext k
        fin_cases k <;> rfl
      rw [run_step hs]
      simpa only [show b+1+a=b+(a+1) by omega] using ih (b+1) (v.1,some true)

theorem clear_run (d : Data) :
    run (d.accumulator.length+d.digit.length+d.quotient.length+4)
      (cfg (some (.inr (.clear 0))) (false,none) d) =
      cfg (some (.inr .move)) (false,none) {d with accumulator:=[],digit:=[],quotient:=[]} := by
  have hc := BitMachineClearBank.clear_bank_run program (fun _ => false) (.inr .move)
    3 clearStack (by decide) (fun i => (.inr (.clear i) : Label))
    (fun i => by fin_cases i <;> rfl) (by rfl) false d.stacks
  have hs : (∑ i : Fin 3, (d.stacks (clearStack i)).length)+3+1 =
      d.accumulator.length+d.digit.length+d.quotient.length+4 := by
    simp [Fin.sum_univ_succ, Data.stacks, clearStack]
    omega
  have he : BitMachineClearBank.cleared clearStack d.stacks =
      ({d with accumulator:=[],digit:=[],quotient:=[]} : Data).stacks := by
    funext k
    fin_cases k <;> simp [BitMachineClearBank.cleared, clearStack, Data.stacks, Fin.exists_fin_succ]
  simpa only [run, cfg, hs, he] using hc

theorem move_run (a b : ℕ) (d : Data) (v : Control) :
    run (a+1) (cfg (some (.inr .move)) v
      {d with remainder:=List.replicate a true,accumulator:=List.replicate b true}) =
      cfg (some (.inr .scan)) (false,none)
        {d with remainder:=[],accumulator:=List.replicate (b+a) true} := by
  induction a generalizing b v with
  | zero =>
      simp only [Nat.zero_add,Nat.add_zero,List.replicate_zero,run,Function.iterate_one]
      simp [advance,cfg,program,TM2.step,TM2.stepAux,Data.stacks]
  | succ a ih =>
      have hs : advance program (cfg (some (.inr .move)) v
          {d with remainder:=List.replicate (a+1) true,accumulator:=List.replicate b true}) =
          cfg (some (.inr .move)) (v.1,some true)
            {d with remainder:=List.replicate a true,accumulator:=List.replicate (b+1) true} := by
        simp [List.replicate_succ,advance,cfg,program,TM2.step,TM2.stepAux,Data.stacks]
        funext k
        fin_cases k <;> rfl
      rw [run_step hs]
      simpa only [show b+1+a=b+(a+1) by omega] using ih (b+1) (v.1,some true)

def frame (stream : List Bool) (c : PrimeSamplerModularStep.Config) : Config :=
  renameCfg (finSumFinEquiv : Fin 9 ⊕ Fin 1 ≃ Stack) (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (Admin.clear 0)) none (fun _ => stream) c)

theorem mod_run (j a digit p : ℕ) (stream : List Bool) :
    ∃ t ≤ 15*(j+a+digit+p+1)^2,
      run t (cfg (some (.inl (.inl .outer))) (false,none)
        {coordinate:=List.replicate j true,accumulator:=List.replicate a true,
          digit:=List.replicate digit true,modulus:=List.replicate p true,stream:=stream}) =
      cfg (some (.inr (.clear 0))) (false,none)
        {coordinate:=List.replicate j true,accumulator:=List.replicate a true,
          digit:=List.replicate digit true,remainder:=List.replicate ((j*a+digit)%p) true,
          modulus:=List.replicate p true,quotient:=List.replicate ((j*a+digit)/p) true,stream:=stream} := by
  obtain ⟨t,ht,he⟩ := PrimeSamplerModularStep.modular_step j a digit p
  obtain ⟨u,hu,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : Fin 9 ⊕ Fin 1 ≃ Stack) (Equiv.refl _) (Equiv.refl _)
    PrimeSamplerModularStep.program program (some (Admin.clear 0)) (fun _ => rfl)
    none (fun _ => stream)
    (PrimeSamplerModularStep.cfg (some (.inl .outer)) false (List.replicate j true)
      (List.replicate a true) (List.replicate digit true) [] [] [] (List.replicate p true) [] [])
    t (by rw [show ((advance PrimeSamplerModularStep.program)^[t]) _ = _ from he]; rfl)
  change run u (frame _ _) = frame _ (PrimeSamplerModularStep.run t _) at hr
  rw [he] at hr
  have hi : frame stream (PrimeSamplerModularStep.cfg (some (.inl .outer)) false
      (List.replicate j true) (List.replicate a true) (List.replicate digit true) [] [] []
      (List.replicate p true) [] []) =
      cfg (some (.inl (.inl .outer))) (false,none)
        {coordinate:=List.replicate j true,accumulator:=List.replicate a true,
          digit:=List.replicate digit true,modulus:=List.replicate p true,stream:=stream} := by
    unfold frame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : frame stream (PrimeSamplerModularStep.cfg none false
      (List.replicate j true) (List.replicate a true) (List.replicate digit true) []
      (List.replicate ((j*a+digit)%p) true) [] (List.replicate p true)
      (List.replicate ((j*a+digit)/p) true) []) =
      cfg (some (.inr (.clear 0))) (false,none)
        {coordinate:=List.replicate j true,accumulator:=List.replicate a true,
          digit:=List.replicate digit true,remainder:=List.replicate ((j*a+digit)%p) true,
          modulus:=List.replicate p true,quotient:=List.replicate ((j*a+digit)/p) true,stream:=stream} := by
    unfold frame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨u,hu.trans ht,by simpa only [hi,hf] using hr⟩

def ready (p j a : ℕ) (stream : List Bool) : Config :=
  cfg (some (.inr .scan)) (false,none)
    {coordinate:=List.replicate j true,accumulator:=List.replicate a true,
      modulus:=List.replicate p true,stream:=stream}

theorem round_run (p j a digit : ℕ) (stream : List Bool) :
    ∃ t ≤ 25*(j+a+digit+p+1)^2,
      run t (ready p j a (encodeDigit digit++stream)) =
      ready p j ((j*a+digit)%p) stream := by
  have hs := scan_field digit 0
    {coordinate:=List.replicate j true,accumulator:=List.replicate a true,
      modulus:=List.replicate p true,stream:=stream} (false,none)
  simp only [Nat.zero_add,List.replicate_zero] at hs
  obtain ⟨u,hu,hm⟩ := mod_run j a digit p stream
  have hc := clear_run
    {coordinate:=List.replicate j true,accumulator:=List.replicate a true,
      digit:=List.replicate digit true,remainder:=List.replicate ((j*a+digit)%p) true,
      modulus:=List.replicate p true,quotient:=List.replicate ((j*a+digit)/p) true,stream:=stream}
  simp only [List.length_replicate] at hc
  have hv := move_run ((j*a+digit)%p) 0
    {coordinate:=List.replicate j true,modulus:=List.replicate p true,stream:=stream} (false,none)
  simp only [Nat.zero_add,List.replicate_zero] at hv
  refine ⟨((digit+1)+u)+(a+digit+(j*a+digit)/p+4)+((j*a+digit)%p+1),?_,?_⟩
  · have hq := Nat.div_le_self (j*a+digit) p
    have hr := Nat.mod_le (j*a+digit) p
    have hprod : j*a ≤ (j+a+digit+p+1)^2 := by
      have h := Nat.mul_le_mul (show j≤j+a+digit+p+1 by omega)
        (show a≤j+a+digit+p+1 by omega)
      nlinarith
    have hlin : a+4*digit+6 ≤ 6*(j+a+digit+p+1) := by omega
    have hsq : j+a+digit+p+1 ≤ (j+a+digit+p+1)^2 := by nlinarith
    nlinarith
  · have he := (run_add ((run_add ((run_add hs u).trans hm) _).trans hc) _).trans hv
    simpa only [ready,encodeDigit,List.append_assoc,List.singleton_append] using he

theorem evaluation_run (p j a : ℕ) (digits : List ℕ) (hp : 0<p) (hj : j<p) (ha : a<p)
    (hd : ∀ d ∈ digits,d<p) :
    ∃ t ≤ digits.length*(400*(p+1)^2)+1,
      let c := run t (ready p j a (encode digits))
      c.l=none ∧ c.stk 1=List.replicate (PrimeSamplerEntryAlgorithm.evaluate p j digits a) true := by
  induction digits generalizing a with
  | nil =>
      refine ⟨1,by simp,?_⟩
      dsimp only
      simp [run,ready,advance,cfg,program,TM2.step,TM2.stepAux,Data.stacks,encode,
        PrimeSamplerEntryAlgorithm.evaluate]
  | cons digit digits ih =>
      obtain ⟨u,hu,hr⟩ := round_run p j a digit (encode digits)
      have hdig := hd digit (by simp)
      have htime : u ≤ 400*(p+1)^2 := by nlinarith
      obtain ⟨v,hv,hh,ho⟩ := ih ((j*a+digit)%p) (Nat.mod_lt _ hp)
        (fun d hm => hd d (by simp [hm]))
      refine ⟨u+v,?_,?_⟩
      · simp only [List.length_cons]
        nlinarith
      · dsimp only at hh ho ⊢
        simp only [encode,List.flatMap_cons]
        simp only [encode] at hr hh ho
        rw [run_add hr]
        exact ⟨hh,ho⟩

/-- The full final state retains the modulus and coordinate and empties all
scratch banks, allowing the final reduction modulo the alphabet size. -/
theorem evaluation_exact (p j a : ℕ) (digits : List ℕ) (hp : 0<p) (hj : j<p) (ha : a<p)
    (hd : ∀ d ∈ digits,d<p) :
    ∃ t ≤ digits.length*(400*(p+1)^2)+1,
      run t (ready p j a (encode digits)) =
      cfg none (false,none)
        {coordinate:=List.replicate j true,
          accumulator:=List.replicate (PrimeSamplerEntryAlgorithm.evaluate p j digits a) true,
          modulus:=List.replicate p true} := by
  induction digits generalizing a with
  | nil =>
      refine ⟨1,by simp,?_⟩
      simp [run,ready,advance,cfg,program,TM2.step,TM2.stepAux,Data.stacks,encode,
        PrimeSamplerEntryAlgorithm.evaluate]
  | cons digit digits ih =>
      obtain ⟨u,hu,hr⟩ := round_run p j a digit (encode digits)
      have hdig := hd digit (by simp)
      have htime : u ≤ 400*(p+1)^2 := by nlinarith
      obtain ⟨v,hv,hend⟩ := ih ((j*a+digit)%p) (Nat.mod_lt _ hp)
        (fun d hm => hd d (by simp [hm]))
      refine ⟨u+v,?_,?_⟩
      · simp only [List.length_cons]
        nlinarith
      · change run (u+v) (ready p j a (encodeDigit digit++encode digits)) = _
        rw [run_add hr,hend]
        rfl

end EthInapproximability.CurrentPaper.PrimeSamplerHornerMachine
