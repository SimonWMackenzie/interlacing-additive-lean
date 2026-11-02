import EthInapproximability.CurrentPaper.BitMachineBinaryMultiply
import EthInapproximability.CurrentPaper.BitMachineBinaryDivision
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigit

/-!
# Binary modular Horner step

One step computes `(j*h + digit) % p` from binary bitwords. The fixed finite
program places the proved multiplier, unequal-width adder, and divider on
fixed banks, with one transfer reversing the sum into the divider's
MSB-first input. Literal run, arithmetic, and quadratic raw-bank cost are
proved below. Iterated coefficient decoding/Horner remains a separate task.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryModularStep

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition

abbrev Stack := Fin 14
abbrev Label := BitMachineBinaryMultiply.Label ⊕
  (BitMachineBinaryAddAny.Label ⊕ (BitMachineBinaryDivision.Label ⊕ Unit))
abbrev Control := BitMachineBinaryMultiply.Control ×
  (BitMachineBinaryAddAny.Control × (BitMachineBinaryDivision.Control × Option Bool))
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control :=
  (BitMachineBinaryMultiply.initial, BitMachineBinaryAddAny.initial,
    BitMachineBinaryDivision.initial, none)

def mulStacks : (BitMachineBinaryMultiply.Stack ⊕ Fin 8) ≃ Stack :=
  (Equiv.sumCongr BitMachineBinaryMultiply.finStack (Equiv.refl (Fin 8))).trans
    finSumFinEquiv

def addPermutation : Stack ≃ Stack where
  toFun i := ![0,6,4,1,2,3,5,7,8,9,10,11,12,13] i
  invFun i := ![0,3,4,5,2,6,1,7,8,9,10,11,12,13] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def addStacks : (Fin 3 ⊕ Fin 11) ≃ Stack :=
  finSumFinEquiv.trans addPermutation

def divisionPermutation : Stack ≃ Stack where
  toFun i := ![7,8,9,10,11,12,13,0,1,2,3,4,5,6] i
  invFun i := ![7,8,9,10,11,12,13,0,1,2,3,4,5,6] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def divisionStacks : (Fin 7 ⊕ Fin 7) ≃ Stack :=
  finSumFinEquiv.trans divisionPermutation

def addLabels :
    (BitMachineBinaryAddAny.Label ⊕
      (BitMachineBinaryMultiply.Label ⊕ (BitMachineBinaryDivision.Label ⊕ Unit))) ≃
      Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def divisionLabels :
    (BitMachineBinaryDivision.Label ⊕
      (BitMachineBinaryMultiply.Label ⊕ (BitMachineBinaryAddAny.Label ⊕ Unit))) ≃
      Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def addControl :
    (BitMachineBinaryAddAny.Control ×
      (BitMachineBinaryMultiply.Control ×
        (BitMachineBinaryDivision.Control × Option Bool))) ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2.1, s.2.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv s := by rcases s with ⟨a,b,c,d⟩; rfl
  right_inv s := by rcases s with ⟨a,b,c,d⟩; rfl

def divisionControl :
    (BitMachineBinaryDivision.Control ×
      (BitMachineBinaryMultiply.Control ×
        (BitMachineBinaryAddAny.Control × Option Bool))) ≃ Control where
  toFun s := (s.2.1, s.2.2.1, s.1, s.2.2.2)
  invFun s := (s.2.2.1, s.1, s.2.1, s.2.2.2)
  left_inv s := by rcases s with ⟨a,b,c,d⟩; rfl
  right_inv s := by rcases s with ⟨a,b,c,d⟩; rfl

def admin : Label := .inr (.inr (.inr ()))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt mulStacks (Equiv.refl Label) (Equiv.refl Control)
      (liftStmt (some (.inl .scan)) (BitMachineBinaryMultiply.program l))
  | .inr (.inl l) => renameStmt addStacks addLabels addControl
      (liftStmt (some (.inr (.inr ()))) (BitMachineBinaryAddAny.program l))
  | .inr (.inr (.inl l)) => renameStmt divisionStacks divisionLabels divisionControl
      (liftStmt none (BitMachineBinaryDivision.program l))
  | .inr (.inr (.inr ())) => pop 0 (fun s b => (s.1,s.2.1,s.2.2.1,b))
      (branch (fun s => s.2.2.2.isSome)
        (push 7 (fun s => s.2.2.2.getD false) (goto (fun _ => .inr (.inr (.inr ())))))
        (load (fun _ => initial) (goto (fun _ => .inr (.inr (.inl .outer))))))

def bank (product multOperand multScratch coordinate multiplier copyScratch
    digit divInput prime remainder quotient old saved diff : List Bool) : Stack → List Bool :=
  ![product,multOperand,multScratch,coordinate,multiplier,copyScratch,digit,
    divInput,prime,remainder,quotient,old,saved,diff]

def cfg (l : Option Label) (s : Control)
    (product multOperand multScratch coordinate multiplier copyScratch
      digit divInput prime remainder quotient old saved diff : List Bool) : Config :=
  ⟨l,s,bank product multOperand multScratch coordinate multiplier copyScratch
    digit divInput prime remainder quotient old saved diff⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def mulFrame (digit prime : List Bool) (c : BitMachineBinaryMultiply.Config) : Config :=
  renameCfg mulStacks (Equiv.refl Label) (Equiv.refl Control)
    (liftCfg (some (.inl .scan))
      (BitMachineBinaryAddAny.initial, BitMachineBinaryDivision.initial, none)
      (fun i : Fin 8 => ![digit,[],prime,[],[],[],[],[]] i) c)

theorem mulFrame_start (h coordinate digit prime : List Bool) :
    mulFrame digit prime
      (BitMachineBinaryMultiply.cfg (some (.inr (.inr ())))
        BitMachineBinaryMultiply.initial [] [] [] coordinate h []) =
      cfg (some (.inl (.inr (.inr ())))) initial
        [] [] [] coordinate h [] digit [] prime [] [] [] [] [] := by
  unfold mulFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [mulStacks, BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank,
      BitMachineBinaryMultiply.finStack, BitMachineBinaryAddAny.bank,
      BitMachineBinaryAdd.bank, finSumFinEquiv, Fin.addCases]

theorem mulFrame_end (coordinate digit prime h : List Bool) :
    mulFrame digit prime
      (BitMachineBinaryMultiply.cfg none BitMachineBinaryMultiply.initial
        (BitMachineBinaryMultiply.multiplyFrom [] coordinate h)
        [] [] coordinate [] []) =
      cfg (some (.inr (.inl .scan))) initial
        (BitMachineBinaryMultiply.multiplyFrom [] coordinate h)
        [] [] coordinate [] [] digit [] prime [] [] [] [] [] := by
  unfold mulFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [mulStacks, BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank,
      BitMachineBinaryMultiply.finStack, BitMachineBinaryAddAny.bank,
      BitMachineBinaryAdd.bank, finSumFinEquiv, Fin.addCases]

theorem mul_call (h coordinate digit prime : List Bool) :
    ∃ n ≤ (h.length + 1) *
        (4 * (coordinate.length + 2 * h.length) + 7),
      run n (cfg (some (.inl (.inr (.inr ())))) initial
        [] [] [] coordinate h [] digit [] prime [] [] [] [] []) =
      cfg (some (.inr (.inl .scan))) initial
        (BitMachineBinaryMultiply.multiplyFrom [] coordinate h)
        [] [] coordinate [] [] digit [] prime [] [] [] [] [] := by
  have hQ : ∀ l, program (.inl l) =
      renameStmt mulStacks (Equiv.refl Label) (Equiv.refl Control)
        (liftStmt (some (.inl .scan)) (BitMachineBinaryMultiply.program l)) := by
    intro l
    rfl
  obtain ⟨n, hn, hr⟩ := BitMachineBinaryMultiply.standard_run coordinate h
  have hhalt :
      (((advance BitMachineBinaryMultiply.program)^[n])
        (BitMachineBinaryMultiply.cfg (some (.inr (.inr ())))
          BitMachineBinaryMultiply.initial [] [] [] coordinate h [])).l = none := by
    rw [show ((advance BitMachineBinaryMultiply.program)^[n])
      (BitMachineBinaryMultiply.cfg (some (.inr (.inr ())))
        BitMachineBinaryMultiply.initial [] [] [] coordinate h []) =
      BitMachineBinaryMultiply.run n
        (BitMachineBinaryMultiply.cfg (some (.inr (.inr ())))
          BitMachineBinaryMultiply.initial [] [] [] coordinate h []) from rfl,
      hr]
    rfl
  obtain ⟨u, hu, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    mulStacks (Equiv.refl Label) (Equiv.refl Control)
    BitMachineBinaryMultiply.program program (some (.inl .scan)) hQ
    (BitMachineBinaryAddAny.initial, BitMachineBinaryDivision.initial, none)
    (fun i : Fin 8 => ![digit,[],prime,[],[],[],[],[]] i)
    (BitMachineBinaryMultiply.cfg (some (.inr (.inr ())))
      BitMachineBinaryMultiply.initial [] [] [] coordinate h []) n hhalt
  refine ⟨u, hu.trans hn, ?_⟩
  change run u (mulFrame digit prime _) = mulFrame digit prime _ at hglobal
  rw [show ((advance BitMachineBinaryMultiply.program)^[n]) _ =
      BitMachineBinaryMultiply.run n _ from rfl, hr] at hglobal
  simpa only [mulFrame_start, mulFrame_end] using hglobal

def addFrame (coordinate prime : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool)
      BitMachineBinaryAddAny.Label BitMachineBinaryAddAny.Control) : Config :=
  renameCfg addStacks addLabels addControl
    (liftCfg (some (.inr (.inr ())))
      (BitMachineBinaryMultiply.initial, BitMachineBinaryDivision.initial, none)
      (fun i : Fin 11 => ![[],[],coordinate,[],[],prime,[],[],[],[],[]] i) c)

theorem addFrame_start (product coordinate digit prime : List Bool) :
    addFrame coordinate prime
      (BitMachineBinaryAddAny.cfg (some .scan)
        BitMachineBinaryAddAny.initial product digit []) =
      cfg (some (.inr (.inl .scan))) initial
        product [] [] coordinate [] [] digit [] prime [] [] [] [] [] := by
  unfold addFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [addStacks, addPermutation, BitMachineBinaryAddAny.cfg,
      BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank,
      finSumFinEquiv, Fin.addCases]

theorem addFrame_end (product coordinate digit prime : List Bool) :
    addFrame coordinate prime
      (BitMachineBinaryAddAny.cfg none BitMachineBinaryAddAny.initial
        (BitMachineBinaryAddAny.addAny product digit false) [] []) =
      cfg (some admin) initial
        (BitMachineBinaryAddAny.addAny product digit false)
        [] [] coordinate [] [] [] [] prime [] [] [] [] [] := by
  unfold addFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [addStacks, addPermutation, BitMachineBinaryAddAny.cfg,
      BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank,
      finSumFinEquiv, Fin.addCases]

theorem add_call (product coordinate digit prime : List Bool) :
    ∃ n ≤ 2 * max product.length digit.length + 2,
      run n (cfg (some (.inr (.inl .scan))) initial
        product [] [] coordinate [] [] digit [] prime [] [] [] [] []) =
      cfg (some admin) initial
        (BitMachineBinaryAddAny.addAny product digit false)
        [] [] coordinate [] [] [] [] prime [] [] [] [] [] := by
  have hQ : ∀ l, program (addLabels (.inl l)) =
      renameStmt addStacks addLabels addControl
        (liftStmt (some (.inr (.inr ()))) (BitMachineBinaryAddAny.program l)) := by
    intro l
    rfl
  have hr := BitMachineBinaryAddAny.run_correct product digit
  have hhalt : (((advance BitMachineBinaryAddAny.program)^[
      2 * max product.length digit.length + 2])
      (BitMachineBinaryAddAny.cfg (some .scan)
        BitMachineBinaryAddAny.initial product digit [])).l = none := by
    change (BitMachineBinaryAddAny.run
      (2 * max product.length digit.length + 2)
      (BitMachineBinaryAddAny.cfg (some .scan)
        BitMachineBinaryAddAny.initial product digit [])).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    addStacks addLabels addControl
    BitMachineBinaryAddAny.program program (some (.inr (.inr ()))) hQ
    (BitMachineBinaryMultiply.initial, BitMachineBinaryDivision.initial, none)
    (fun i : Fin 11 => ![[],[],coordinate,[],[],prime,[],[],[],[],[]] i)
    (BitMachineBinaryAddAny.cfg (some .scan)
      BitMachineBinaryAddAny.initial product digit [])
    (2 * max product.length digit.length + 2) hhalt
  refine ⟨n, hn, ?_⟩
  change run n (addFrame coordinate prime _) = addFrame coordinate prime _ at hglobal
  rw [show ((advance BitMachineBinaryAddAny.program)^[
      2 * max product.length digit.length + 2]) _ =
      BitMachineBinaryAddAny.run (2 * max product.length digit.length + 2) _ from rfl,
      hr] at hglobal
  simpa only [addFrame_start, addFrame_end] using hglobal

private theorem run_step {c d : Config} (h : TM2.step program c = some d)
    (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d)
    (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_move_cons (s : Control) (x : Bool)
    (sum coordinate prime saved : List Bool) :
    TM2.step program (cfg (some admin) s
      (x :: sum) [] [] coordinate [] [] [] saved prime [] [] [] [] []) =
    some (cfg (some admin) (s.1,s.2.1,s.2.2.1,some x)
      sum [] [] coordinate [] [] [] (x :: saved) prime [] [] [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, admin, cfg, bank]
  funext k
  fin_cases k <;> simp

private theorem step_move_nil (s : Control)
    (coordinate prime saved : List Bool) :
    TM2.step program (cfg (some admin) s
      [] [] [] coordinate [] [] [] saved prime [] [] [] [] []) =
    some (cfg (some (.inr (.inr (.inl .outer)))) initial
      [] [] [] coordinate [] [] [] saved prime [] [] [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, admin, cfg, bank]

theorem move_run (sum coordinate prime saved : List Bool) (s : Control) :
    run (sum.length + 1)
      (cfg (some admin) s sum [] [] coordinate [] [] [] saved prime [] [] [] [] []) =
    cfg (some (.inr (.inr (.inl .outer)))) initial
      [] [] [] coordinate [] [] [] (sum.reverse ++ saved) prime [] [] [] [] [] := by
  induction sum generalizing s saved with
  | nil => simpa using run_step (step_move_nil s coordinate prime saved) 0
  | cons x sum ih =>
      rw [List.length_cons, run_step (step_move_cons s x sum coordinate prime saved)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (x :: saved) (s.1,s.2.1,s.2.2.1,some x)

def divisionFrame (coordinate : List Bool)
    (c : BitMachineBinaryDivision.Config) : Config :=
  renameCfg divisionStacks divisionLabels divisionControl
    (liftCfg none
      (BitMachineBinaryMultiply.initial, BitMachineBinaryAddAny.initial, none)
      (fun i : Fin 7 => ![[],[],[],coordinate,[],[],[]] i) c)

theorem divisionFrame_start (input coordinate prime : List Bool) :
    divisionFrame coordinate
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial input prime [] [] [] [] []) =
      cfg (some (.inr (.inr (.inl .outer)))) initial
        [] [] [] coordinate [] [] [] input prime [] [] [] [] [] := by
  unfold divisionFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [divisionStacks, divisionPermutation, BitMachineBinaryDivision.cfg,
      BitMachineBinaryDivision.bank, finSumFinEquiv, Fin.addCases]

theorem divisionFrame_end (input coordinate prime : List Bool) :
    divisionFrame coordinate
      (BitMachineBinaryDivision.cfg none BitMachineBinaryDivision.initial [] prime
        (BitMachineBinaryDivision.divideFrom input prime [] []).1
        (BitMachineBinaryDivision.divideFrom input prime [] []).2 [] [] []) =
      cfg none initial [] [] [] coordinate [] [] [] [] prime
        (BitMachineBinaryDivision.divideFrom input prime [] []).1
        (BitMachineBinaryDivision.divideFrom input prime [] []).2 [] [] [] := by
  unfold divisionFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [divisionStacks, divisionPermutation, BitMachineBinaryDivision.cfg,
      BitMachineBinaryDivision.bank, finSumFinEquiv, Fin.addCases]

theorem division_call (input coordinate prime : List Bool) :
    ∃ n ≤ (input.length + 1) *
        (4 * (input.length + prime.length + 1) + 5),
      run n (cfg (some (.inr (.inr (.inl .outer)))) initial
        [] [] [] coordinate [] [] [] input prime [] [] [] [] []) =
      cfg none initial [] [] [] coordinate [] [] [] [] prime
        (BitMachineBinaryDivision.divideFrom input prime [] []).1
        (BitMachineBinaryDivision.divideFrom input prime [] []).2 [] [] [] := by
  have hQ : ∀ l, program (divisionLabels (.inl l)) =
      renameStmt divisionStacks divisionLabels divisionControl
        (liftStmt none (BitMachineBinaryDivision.program l)) := by
    intro l
    rfl
  have hr := BitMachineBinaryDivision.total_run input prime [] []
  have ht := BitMachineBinaryDivision.standard_time_bound input prime
  have hhalt : (((advance BitMachineBinaryDivision.program)^[
      BitMachineBinaryDivision.totalTime input prime []])
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial input prime [] [] [] [] [])).l = none := by
    change (BitMachineBinaryDivision.run
      (BitMachineBinaryDivision.totalTime input prime [])
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial input prime [] [] [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    divisionStacks divisionLabels divisionControl
    BitMachineBinaryDivision.program program none hQ
    (BitMachineBinaryMultiply.initial, BitMachineBinaryAddAny.initial, none)
    (fun i : Fin 7 => ![[],[],[],coordinate,[],[],[]] i)
    (BitMachineBinaryDivision.cfg (some .outer)
      BitMachineBinaryDivision.initial input prime [] [] [] [] [])
    (BitMachineBinaryDivision.totalTime input prime []) hhalt
  refine ⟨n, hn.trans ht, ?_⟩
  change run n (divisionFrame coordinate _) = divisionFrame coordinate _ at hglobal
  rw [show ((advance BitMachineBinaryDivision.program)^[
      BitMachineBinaryDivision.totalTime input prime []]) _ =
      BitMachineBinaryDivision.run
        (BitMachineBinaryDivision.totalTime input prime []) _ from rfl,
      hr] at hglobal
  simpa only [divisionFrame_start, divisionFrame_end] using hglobal

def productWord (h coordinate : List Bool) : List Bool :=
  BitMachineBinaryMultiply.multiplyFrom [] coordinate h

def sumWord (h coordinate digit : List Bool) : List Bool :=
  BitMachineBinaryAddAny.addAny (productWord h coordinate) digit false

def stepCost (h coordinate digit prime : List Bool) : ℕ :=
  (h.length + 1) * (4 * (coordinate.length + 2 * h.length) + 7) +
  (2 * max (productWord h coordinate).length digit.length + 2) +
  ((sumWord h coordinate digit).length + 1) +
  ((sumWord h coordinate digit).length + 1) *
    (4 * ((sumWord h coordinate digit).length + prime.length + 1) + 5)

theorem step_run (h coordinate digit prime : List Bool) :
    ∃ n ≤ stepCost h coordinate digit prime,
      run n (cfg (some (.inl (.inr (.inr ())))) initial
        [] [] [] coordinate h [] digit [] prime [] [] [] [] []) =
      cfg none initial [] [] [] coordinate [] [] [] [] prime
        (BitMachineBinaryDivision.divideFrom
          (sumWord h coordinate digit).reverse prime [] []).1
        (BitMachineBinaryDivision.divideFrom
          (sumWord h coordinate digit).reverse prime [] []).2
        [] [] [] := by
  obtain ⟨n₁, hn₁, h₁⟩ := mul_call h coordinate digit prime
  obtain ⟨n₂, hn₂, h₂⟩ := add_call (productWord h coordinate)
    coordinate digit prime
  have h₃ := move_run (sumWord h coordinate digit) coordinate prime [] initial
  simp only [List.append_nil] at h₃
  obtain ⟨n₄, hn₄, h₄⟩ := division_call
    (sumWord h coordinate digit).reverse coordinate prime
  have h₁₂ := (run_add h₁ n₂).trans h₂
  have h₁₂₃ := (run_add h₁₂ ((sumWord h coordinate digit).length + 1)).trans h₃
  have h₁₂₃₄ := (run_add h₁₂₃ n₄).trans h₄
  refine ⟨n₁ + n₂ + ((sumWord h coordinate digit).length + 1) + n₄,
    ?_, h₁₂₃₄⟩
  simp only [stepCost, List.length_reverse] at hn₄ ⊢
  omega

theorem step_value (h coordinate digit prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime) :
    EncodedCommunication.bitsValue
      (BitMachineBinaryDivision.divideFrom
        (sumWord h coordinate digit).reverse prime [] []).1 =
      (EncodedCommunication.bitsValue coordinate *
          BitMachineBinaryMultiply.msbValue h +
        EncodedCommunication.bitsValue digit) %
        EncodedCommunication.bitsValue prime := by
  have hdiv := (BitMachineBinaryDivision.standard_division_spec
    (sumWord h coordinate digit).reverse prime hp).2
  rw [PrimeSamplerBinaryDigit.msbValue_reverse] at hdiv
  have hadd := BitMachineBinaryAddAny.result_value
    (productWord h coordinate) digit
  have hmul := BitMachineBinaryMultiply.standard_value coordinate h
  simp only [sumWord, productWord] at hdiv hadd hmul ⊢
  rw [hadd, hmul] at hdiv
  exact hdiv

theorem stepCost_poly (h coordinate digit prime : List Bool) :
    let N := h.length + coordinate.length + digit.length + prime.length
    stepCost h coordinate digit prime ≤ 100 * (N + 1) ^ 2 := by
  let N := h.length + coordinate.length + digit.length + prime.length
  have hp := BitMachineBinaryMultiply.multiplyFrom_length_bound [] coordinate h
  have hp' : max (productWord h coordinate).length coordinate.length ≤
      coordinate.length + 2 * h.length := by
    simpa [productWord] using hp
  have hprod : (productWord h coordinate).length ≤ 2 * N := by
    omega
  have ha := BitMachineBinaryAddAny.addAny_length
    (productWord h coordinate) digit false
  have hsum : (sumWord h coordinate digit).length ≤ 2 * N + 1 := by
    change (sumWord h coordinate digit).length =
      max (productWord h coordinate).length digit.length + 1 at ha
    omega
  have hmul : (h.length + 1) *
      (4 * (coordinate.length + 2 * h.length) + 7) ≤
      (N + 1) * (8 * N + 7) := by
    apply Nat.mul_le_mul <;> omega
  have hdiv : ((sumWord h coordinate digit).length + 1) *
      (4 * ((sumWord h coordinate digit).length + prime.length + 1) + 5) ≤
      (2 * N + 2) * (12 * N + 13) := by
    apply Nat.mul_le_mul <;> omega
  have hadd : 2 * max (productWord h coordinate).length digit.length + 2 ≤
      4 * N + 2 := by omega
  change stepCost h coordinate digit prime ≤ 100 * (N + 1) ^ 2
  unfold stepCost
  nlinarith [Nat.zero_le N]

theorem step_run_poly (h coordinate digit prime : List Bool) :
    let N := h.length + coordinate.length + digit.length + prime.length
    ∃ n ≤ 100 * (N + 1) ^ 2,
      run n (cfg (some (.inl (.inr (.inr ())))) initial
        [] [] [] coordinate h [] digit [] prime [] [] [] [] []) =
      cfg none initial [] [] [] coordinate [] [] [] [] prime
        (BitMachineBinaryDivision.divideFrom
          (sumWord h coordinate digit).reverse prime [] []).1
        (BitMachineBinaryDivision.divideFrom
          (sumWord h coordinate digit).reverse prime [] []).2
        [] [] [] := by
  obtain ⟨n, hn, hr⟩ := step_run h coordinate digit prime
  exact ⟨n, hn.trans (stepCost_poly h coordinate digit prime), hr⟩

def initialBank (h coordinate digit prime : List Bool) : Stack → List Bool :=
  bank [] [] [] coordinate h [] digit [] prime [] [] [] [] []

def finalBank (h coordinate digit prime : List Bool) : Stack → List Bool :=
  bank [] [] [] coordinate [] [] [] [] prime
    (BitMachineBinaryDivision.divideFrom
      (sumWord h coordinate digit).reverse prime [] []).1
    (BitMachineBinaryDivision.divideFrom
      (sumWord h coordinate digit).reverse prime [] []).2
    [] [] []

def packedInput (h coordinate digit prime : List Bool) : List Bool :=
  BitMachineBankCodec.encode (initialBank h coordinate digit prime)

theorem initialBank_code_length (h coordinate digit prime : List Bool) :
    let N := h.length + coordinate.length + digit.length + prime.length
    (packedInput h coordinate digit prime).length = 2 * N + 14 := by
  rw [packedInput, BitMachineBankCodec.encode_length]
  simp [initialBank, bank, Fin.sum_univ_succ]
  omega

theorem sumWord_length_le (h coordinate digit prime : List Bool) :
    let N := h.length + coordinate.length + digit.length + prime.length
    (sumWord h coordinate digit).length ≤ 2 * N + 1 := by
  let N := h.length + coordinate.length + digit.length + prime.length
  have hp := BitMachineBinaryMultiply.multiplyFrom_length_bound [] coordinate h
  have hp' : max (productWord h coordinate).length coordinate.length ≤
      coordinate.length + 2 * h.length := by
    simpa [productWord] using hp
  have ha := BitMachineBinaryAddAny.addAny_length
    (productWord h coordinate) digit false
  change (sumWord h coordinate digit).length =
    max (productWord h coordinate).length digit.length + 1 at ha
  change (sumWord h coordinate digit).length ≤ 2 * N + 1
  omega

theorem finalBank_code_length_le (h coordinate digit prime : List Bool) :
    let N := h.length + coordinate.length + digit.length + prime.length
    (BitMachineBankCodec.encode (finalBank h coordinate digit prime)).length ≤
      20 * (N + 1) := by
  let N := h.length + coordinate.length + digit.length + prime.length
  have hs := sumWord_length_le h coordinate digit prime
  change (sumWord h coordinate digit).length ≤ 2 * N + 1 at hs
  have hq := BitMachineBinaryDivision.divideFrom_quotient_length
    (sumWord h coordinate digit).reverse prime [] []
  simp only [List.length_reverse, List.length_nil, Nat.add_zero] at hq
  have hr := BitMachineBinaryDivision.divideFrom_remainder_length
    (sumWord h coordinate digit).reverse prime [] []
    (sumWord h coordinate digit).length (by simp) (by simp)
  rw [BitMachineBankCodec.encode_length]
  simp [finalBank, bank, Fin.sum_univ_succ] at hq hr ⊢
  omega

theorem packed_run (h coordinate digit prime : List Bool) :
    ∃ (u : ℕ) (S' : Stack → List Bool),
      u ≤ 1000 * ((packedInput h coordinate digit prime).length + 1) ^ 2 ∧
      BitMachineBankWrapper.run program (.inl (.inr (.inr ()))) initial u
        (BitMachineBankWrapper.cfg
          (some (.inr (.parse (.scan 0)))) (initial, none)
          (fun _ : Stack => []) (packedInput h coordinate digit prime) [] []) =
        BitMachineBankWrapper.cfg none (initial, none) S' [] []
          (BitMachineBankCodec.encode (finalBank h coordinate digit prime)) := by
  have hd : BitMachineBankCodec.decode 14 (packedInput h coordinate digit prime) =
      some (initialBank h coordinate digit prime) := by simp [packedInput]
  obtain ⟨n, hn, hr⟩ := step_run_poly h coordinate digit prime
  let c : Config := ⟨none, initial, finalBank h coordinate digit prime⟩
  have hc : ((advance program)^[n])
      (⟨some (.inl (.inr (.inr ()))), initial,
        initialBank h coordinate digit prime⟩ : Config) = c := by
    simpa [run, cfg, initialBank, finalBank, c] using hr
  have hhalt : c.l = none := rfl
  obtain ⟨u, S', hu, hrun⟩ := BitMachineBankWrapper.packed_run
    program (.inl (.inr (.inr ()))) initial
    (packedInput h coordinate digit prime)
    (initialBank h coordinate digit prime) hd n c hc hhalt
  have he : BitMachineBankSerialize.encode
      (List.ofFn (finalBank h coordinate digit prime)) =
      BitMachineBankCodec.encode (finalBank h coordinate digit prime) := by
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [he] at hu hrun
  refine ⟨u, S', ?_, hrun⟩
  have hi := initialBank_code_length h coordinate digit prime
  have ho := finalBank_code_length_le h coordinate digit prime
  let N := h.length + coordinate.length + digit.length + prime.length
  change (packedInput h coordinate digit prime).length = 2 * N + 14 at hi
  change (BitMachineBankCodec.encode (finalBank h coordinate digit prime)).length ≤
    20 * (N + 1) at ho
  change n ≤ 100 * (N + 1) ^ 2 at hn
  rw [hi] at hu ⊢
  nlinarith [Nat.zero_le N]

noncomputable def packedMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program (.inl (.inr (.inr ()))) initial

theorem packed_outputs (h coordinate digit prime : List Bool) :
    packedMachine.OutputsWithin (packedInput h coordinate digit prime)
      (BitMachineBankCodec.encode (finalBank h coordinate digit prime))
      (1000 * ((packedInput h coordinate digit prime).length + 1) ^ 2) := by
  obtain ⟨u, S', hu, hr⟩ := packed_run h coordinate digit prime
  change (BitMachineBankWrapper.machine program (.inl (.inr (.inr ()))) initial).OutputsWithin
    (packedInput h coordinate digit prime)
    (BitMachineBankCodec.encode (finalBank h coordinate digit prime))
    (1000 * ((packedInput h coordinate digit prime).length + 1) ^ 2)
  apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
    (.inr (.parse (.scan 0))) (initial, none)
    (BitMachineBankWrapper.program program (.inl (.inr (.inr ()))) initial)
    (packedInput h coordinate digit prime)
    (BitMachineBankCodec.encode (finalBank h coordinate digit prime)) u _ hu
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program (.inl (.inr (.inr ()))) initial u _).l = none
    rw [hr]
    rfl
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program (.inl (.inr (.inr ()))) initial u _).stk (.inr 2) = _
    rw [hr]
    rfl

end EthInapproximability.CurrentPaper.PrimeSamplerBinaryModularStep
