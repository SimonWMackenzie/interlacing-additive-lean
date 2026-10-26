import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Preserving unary quotient for duplicate-label decoding

Source: frozen v8 `B-effectivity-details.tex`, proof of
`thm:paper-materialization`.  This fixed machine copies a unary label,
divides the copy by a unary multiplicity, and clears the remainder.  Its
original label and divisor survive exactly; no quotient is computed in
finite control or treated as a unit-cost operation.
-/

namespace EthInapproximability.CurrentPaper.MatrixIndexQuotient

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev Stack := Fin 8
abbrev Label := BitMachineCopy.Label ⊕ (MatrixUnaryDivision.Label ⊕ Unit)
abbrev Control := Option Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (none, false)
def start : Label := .inl .scan
def divide : Label := .inr (.inl .start)
def clear : Label := .inr (.inr ())

def copyPermutation : Stack ≃ Stack where
  toFun := ![0,2,3,1,4,5,6,7]
  invFun := ![0,3,1,2,4,5,6,7]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyStacks : Fin 3 ⊕ Fin 5 ≃ Stack := finSumFinEquiv.trans copyPermutation

def divisionPermutation : Stack ≃ Stack where
  toFun := ![2,1,4,5,6,7,0,3]
  invFun := ![6,1,0,7,2,3,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def divisionStacks : Fin 6 ⊕ Fin 2 ≃ Stack :=
  finSumFinEquiv.trans divisionPermutation

def divisionLabels : MatrixUnaryDivision.Label ⊕ (BitMachineCopy.Label ⊕ Unit) ≃ Label where
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

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt copyStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start))
        (BitMachineCopy.program l))
  | .inr (.inl l) => renameStmt divisionStacks divisionLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixUnaryDivision.program l))
  | .inr (.inr ()) => pop 5 (fun v b => (v.1, b.isSome))
      (branch Prod.snd (goto (fun _ => clear)) (load (fun _ => initial) halt))

def cfg (l : Option Label) (v : Control)
    (input divisor work copySaved count remainder quotient divSaved : List Bool) : Config :=
  ⟨l, v, ![input,divisor,work,copySaved,count,remainder,quotient,divSaved]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def copyFrame (divisor count remainder quotient divSaved : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) BitMachineCopy.Label (Option Bool)) : Config :=
  renameCfg copyStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixUnaryDivision.Label.start)) false
      (fun i => ![divisor,count,remainder,quotient,divSaved] i) c)

theorem copy_run (n m : ℕ) :
    ∃ t ≤ 2 * n + 2,
      run t (cfg (some start) initial (List.replicate n true)
        (List.replicate m true) [] [] [] [] [] []) =
      cfg (some divide) initial (List.replicate n true)
        (List.replicate m true) (List.replicate n true) [] [] [] [] [] := by
  have he := BitMachineCopy.run_correct none (List.replicate n true) []
  simp only [List.length_replicate, List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed copyStacks
    (Equiv.refl _) (Equiv.refl _) BitMachineCopy.program program
    (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl)
    false (fun i => ![List.replicate m true,[],[],[],[]] i)
    (BitMachineCopy.cfg (some .scan) none (List.replicate n true) [] [])
    (2*n+2) (by rw [show ((advance BitMachineCopy.program)^[2*n+2]) _ = _ from he]; rfl)
  change run t (copyFrame (List.replicate m true) [] [] [] [] _) =
    copyFrame (List.replicate m true) [] [] [] [] (BitMachineCopy.run _ _) at hr
  rw [he] at hr
  have hi : copyFrame (List.replicate m true) [] [] [] []
      (BitMachineCopy.cfg (some .scan) none (List.replicate n true) [] []) =
      cfg (some start) initial (List.replicate n true)
        (List.replicate m true) [] [] [] [] [] [] := by
    unfold copyFrame renameCfg liftCfg cfg BitMachineCopy.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : copyFrame (List.replicate m true) [] [] [] []
      (BitMachineCopy.cfg none none (List.replicate n true)
        (List.replicate n true) []) =
      cfg (some divide) initial (List.replicate n true)
        (List.replicate m true) (List.replicate n true) [] [] [] [] [] := by
    unfold copyFrame renameCfg liftCfg cfg BitMachineCopy.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def divisionFrame (input copySaved : List Bool) (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg divisionStacks divisionLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) none (fun i => ![input,copySaved] i) c)

theorem division_run (n m : ℕ) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n m,
      run t (cfg (some divide) initial (List.replicate n true)
        (List.replicate m true) (List.replicate n true) [] [] [] [] []) =
      cfg (some clear) initial (List.replicate n true)
        (List.replicate m true) [] [] [] (List.replicate (n % m) true)
        (List.replicate (n / m) true) [] := by
  have he := MatrixUnaryDivision.division_total_run n m
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed divisionStacks divisionLabels
    (Equiv.prodComm _ _) MatrixUnaryDivision.program program
    (some (.inr ())) (fun _ => rfl) none
    (fun i => ![List.replicate n true,[]] i)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n m)
    (by rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m]) _ = _ from he]; rfl)
  change run t (divisionFrame (List.replicate n true) [] _) =
    divisionFrame (List.replicate n true) [] (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
        (List.replicate m true) [] [] [] []) =
      cfg (some divide) initial (List.replicate n true)
        (List.replicate m true) (List.replicate n true) [] [] [] [] [] := by
    unfold divisionFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n % m) true) (List.replicate (n / m) true) []) =
      cfg (some clear) initial (List.replicate n true)
        (List.replicate m true) [] [] [] (List.replicate (n % m) true)
        (List.replicate (n / m) true) [] := by
    unfold divisionFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

theorem clear_run (input divisor quotient remainder : List Bool) (v : Control) :
    run (remainder.length+1)
      (cfg (some clear) v input divisor [] [] [] remainder quotient []) =
      cfg none initial input divisor [] [] [] [] quotient [] := by
  induction remainder generalizing v with
  | nil => simp [run,advance,cfg,clear,program,TM2.step,TM2.stepAux]
  | cons b remainder ih =>
      have hs : advance program
          (cfg (some clear) v input divisor [] [] [] (b::remainder) quotient []) =
          cfg (some clear) (v.1,true) input divisor [] [] [] remainder quotient [] := by
        simp [advance,cfg,clear,program,TM2.step,TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons,run,Function.iterate_succ_apply,hs]
      exact ih (v.1,true)

/-- The quotient is computed from a copied label; all original input bits
and the divisor survive.  The remainder is physically cleared. -/
theorem quotient_run (n m : ℕ) :
    ∃ t ≤ 11*n + 3*m + 7,
      run t (cfg (some start) initial (List.replicate n true)
        (List.replicate m true) [] [] [] [] [] []) =
      cfg none initial (List.replicate n true) (List.replicate m true)
        [] [] [] [] (List.replicate (n/m) true) [] := by
  obtain ⟨a,ha,he⟩ := copy_run n m
  obtain ⟨b,hb,hr⟩ := division_run n m
  have hc := clear_run (List.replicate n true) (List.replicate m true)
    (List.replicate (n/m) true) (List.replicate (n%m) true) initial
  simp only [List.length_replicate] at hc
  refine ⟨a+(b+(n%m+1)),?_,?_⟩
  · have htime := MatrixUnaryDivision.totalTime_bound n m
    have hmod : n%m ≤ n := Nat.mod_le _ _
    omega
  · rw [run_add he,run_add hr,hc]

end EthInapproximability.CurrentPaper.MatrixIndexQuotient
