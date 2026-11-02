import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# A physical modular multiply-add step

Source: frozen v8 `B-effectivity-details.tex`, Horner evaluation of the
prime-polynomial family. The controller executes the existing literal
multiply-add machine and then the literal quotient/remainder machine.
Inputs are unary; both phases share the physical product stack. There is
no arithmetic operation in a machine transition. This is one operational
Horner primitive, not yet the complete digit-extraction loop.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerModularStep

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine

abbrev Stack := Fin 9
abbrev Label := MatrixAddressMachine.Label ⊕ MatrixUnaryDivision.Label
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Bool

def unitControl : Bool × Unit ≃ Bool where
  toFun := Prod.fst
  invFun b := (b,())
  left_inv v := by rcases v with ⟨b,u⟩; cases u; rfl
  right_inv _ := rfl

def divisorPermutation : Fin 9 ≃ Fin 9 where
  toFun i := ![5,6,3,4,7,8,0,1,2] i
  invFun i := ![6,7,8,2,3,0,1,4,5] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def divisorStacks : Fin 6 ⊕ Fin 3 ≃ Stack := finSumFinEquiv.trans divisorPermutation

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Bool
  | .inl l => renameStmt (finSumFinEquiv : Fin 6 ⊕ Fin 3 ≃ Stack) (Equiv.refl _)
      unitControl (liftStmt (some MatrixUnaryDivision.Label.start) (MatrixAddressMachine.program l))
  | .inr l => renameStmt divisorStacks (Equiv.sumComm _ _) unitControl
      (liftStmt (none : Option MatrixAddressMachine.Label) (MatrixUnaryDivision.program l))

def cfg (l : Option Label) (v : Bool)
    (row width column count remainder product modulus quotient saved : List Bool) : Config :=
  ⟨l,v,![row,width,column,count,remainder,product,modulus,quotient,saved]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c=run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def addressFrame (modulus : List Bool) (c : MatrixAddressMachine.Config) : Config :=
  renameCfg (finSumFinEquiv : Fin 6 ⊕ Fin 3 ≃ Stack) (Equiv.refl _) unitControl
    (liftCfg (some MatrixUnaryDivision.Label.start) () (fun i => ![modulus,[],[]] i) c)

theorem multiply_add_run (row width column p : ℕ) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width column,
      run t (cfg (some (.inl .outer)) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] [] []
        (List.replicate p true) [] []) =
      cfg (some (.inr .start)) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] []
        (List.replicate (row*width+column) true) (List.replicate p true) [] [] := by
  have he := MatrixAddressMachine.address_run row width column false []
  simp only [List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : Fin 6 ⊕ Fin 3 ≃ Stack) (Equiv.refl _) unitControl
    MatrixAddressMachine.program program (some MatrixUnaryDivision.Label.start)
    (fun _ => rfl) () (fun i => ![List.replicate p true,[],[]] i)
    (MatrixAddressMachine.cfg (some .outer) false (List.replicate row true)
      (List.replicate width true) (List.replicate column true) [] [] [])
    (MatrixAddressMachine.exactTime row width column)
    (by rw [show ((advance MatrixAddressMachine.program)^[_]) _ = _ from he]; rfl)
  change run t (addressFrame _ _) = addressFrame _ (MatrixAddressMachine.run _ _) at hr
  rw [he] at hr
  have hi : addressFrame (List.replicate p true)
      (MatrixAddressMachine.cfg (some .outer) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] [] []) =
      cfg (some (.inl .outer)) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] [] []
        (List.replicate p true) [] [] := by
    unfold addressFrame renameCfg liftCfg cfg
    congr 1
    funext i
    fin_cases i <;> rfl
  have hf : addressFrame (List.replicate p true)
      (MatrixAddressMachine.cfg none false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] []
        (List.replicate (row*width+column) true)) =
      cfg (some (.inr .start)) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] []
        (List.replicate (row*width+column) true) (List.replicate p true) [] [] := by
    unfold addressFrame renameCfg liftCfg cfg
    congr 1
    funext i
    fin_cases i <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def divisionFrame (row width column : List Bool) (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg divisorStacks (Equiv.sumComm _ _) unitControl
    (liftCfg (none : Option MatrixAddressMachine.Label) () (fun i => ![row,width,column] i) c)

theorem reduce_run (row width column n p : ℕ) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n p,
      run t (cfg (some (.inr .start)) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] []
        (List.replicate n true) (List.replicate p true) [] []) =
      cfg none false (List.replicate row true) (List.replicate width true)
        (List.replicate column true) [] (List.replicate (n%p) true) []
        (List.replicate p true) (List.replicate (n/p) true) [] := by
  have he := MatrixUnaryDivision.division_total_run n p
  obtain ⟨t,ht,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    divisorStacks (Equiv.sumComm _ _) unitControl MatrixUnaryDivision.program program
    (none : Option MatrixAddressMachine.Label) (fun _ => rfl) ()
    (fun i => ![List.replicate row true,List.replicate width true,List.replicate column true] i)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate p true) [] [] [] []) (MatrixUnaryDivision.totalTime n p)
    (by rw [show ((advance MatrixUnaryDivision.program)^[_]) _ = _ from he]; rfl)
  change run t (divisionFrame _ _ _ _) = divisionFrame _ _ _ (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : divisionFrame (List.replicate row true) (List.replicate width true)
      (List.replicate column true) (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate n true) (List.replicate p true) [] [] [] []) =
      cfg (some (.inr .start)) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] []
        (List.replicate n true) (List.replicate p true) [] [] := by
    unfold divisionFrame renameCfg liftCfg cfg
    congr 1
    funext i
    fin_cases i <;> rfl
  have hf : divisionFrame (List.replicate row true) (List.replicate width true)
      (List.replicate column true) (MatrixUnaryDivision.cfg none false [] (List.replicate p true)
        [] (List.replicate (n%p) true) (List.replicate (n/p) true) []) =
      cfg none false (List.replicate row true) (List.replicate width true)
        (List.replicate column true) [] (List.replicate (n%p) true) []
        (List.replicate p true) (List.replicate (n/p) true) [] := by
    unfold divisionFrame renameCfg liftCfg cfg
    congr 1
    funext i
    fin_cases i <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

/-- Exact modular multiply-add with a uniform quadratic numeric bound. -/
theorem modular_step (row width column p : ℕ) :
    ∃ t ≤ 15*(row+width+column+p+1)^2,
      run t (cfg (some (.inl .outer)) false (List.replicate row true)
        (List.replicate width true) (List.replicate column true) [] [] []
        (List.replicate p true) [] []) =
      cfg none false (List.replicate row true) (List.replicate width true)
        (List.replicate column true) [] (List.replicate ((row*width+column)%p) true) []
        (List.replicate p true) (List.replicate ((row*width+column)/p) true) [] := by
  obtain ⟨a,ha,hr⟩ := multiply_add_run row width column p
  obtain ⟨b,hb,hs⟩ := reduce_run row width column (row*width+column) p
  refine ⟨a+b,?_,(run_add hr b).trans hs⟩
  have hd := MatrixUnaryDivision.totalTime_bound (row*width+column) p
  dsimp [MatrixAddressMachine.exactTime] at ha
  nlinarith

end EthInapproximability.CurrentPaper.PrimeSamplerModularStep
