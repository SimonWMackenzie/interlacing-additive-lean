import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical selection of a mixed-radix coordinate

Source: frozen v8 `02-foundations.tex`, `def:paper-interlace`, and Appendix B
`thm:paper-materialization`.  Starting from unary `i`, `y`, and `cols`, this
fixed Boolean-stack program copies `y`, divides the copy by `cols` exactly
`i+1` times, and retains the last remainder.  Thus its result is
`(y / cols ^ i) % cols`.  It preserves the original `y` and `cols`; every
copy, division, discarded remainder and quotient transfer is physical.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceDigit

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

inductive Admin where
  | test | clearRemainder | moveQuotient | clearQuotient
  deriving DecidableEq, Fintype

abbrev Label := BitMachineCopy.Label ⊕ (MatrixUnaryDivision.Label ⊕ Admin)
abbrev Control := Option Bool × (Bool × Bool)
abbrev Config := TM2.Cfg (fun _ : Fin 9 => Bool) Label Control

def initial : Control := (none, false, false)
def start : Label := .inl .scan
def divide : Label := .inr (.inl .start)
def test : Label := .inr (.inr .test)

private def copyPerm : Fin 9 ≃ Fin 9 where
  toFun := ![1,3,4,0,2,5,6,7,8]
  invFun := ![3,0,4,1,2,5,6,7,8]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def copyStacks : Fin 3 ⊕ Fin 6 ≃ Fin 9 := finSumFinEquiv.trans copyPerm

private def divisionPerm : Fin 9 ≃ Fin 9 where
  toFun := ![3,2,5,6,7,8,0,1,4]
  invFun := ![6,7,1,0,8,2,3,4,5]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def divisionStacks : Fin 6 ⊕ Fin 3 ≃ Fin 9 := finSumFinEquiv.trans divisionPerm

def divisionLabels : MatrixUnaryDivision.Label ⊕ (BitMachineCopy.Label ⊕ Admin) ≃ Label where
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

def divisionControl : Bool × (Option Bool × Bool) ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def program : Label → TM2.Stmt (fun _ : Fin 9 => Bool) Label Control
  | .inl l => renameStmt copyStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start)) (BitMachineCopy.program l))
  | .inr (.inl l) => renameStmt divisionStacks divisionLabels divisionControl
      (liftStmt (some (.inr Admin.test)) (MatrixUnaryDivision.program l))
  | .inr (.inr .test) => pop 0 (fun v b => (v.1, v.2.1, b.isSome))
      (branch (fun v => v.2.2)
        (goto (fun _ => .inr (.inr .clearRemainder)))
        (goto (fun _ => .inr (.inr .clearQuotient))))
  | .inr (.inr .clearRemainder) => pop 6 (fun v b => (v.1, v.2.1, b.isSome))
      (branch (fun v => v.2.2) (goto (fun _ => .inr (.inr .clearRemainder)))
        (goto (fun _ => .inr (.inr .moveQuotient))))
  | .inr (.inr .moveQuotient) => pop 7 (fun v b => (v.1, v.2.1, b.isSome))
      (branch (fun v => v.2.2)
        (push 3 (fun _ => true) (goto (fun _ => .inr (.inr .moveQuotient))))
        (goto (fun _ => divide)))
  | .inr (.inr .clearQuotient) => pop 7 (fun v b => (v.1, v.2.1, b.isSome))
      (branch (fun v => v.2.2) (goto (fun _ => .inr (.inr .clearQuotient)))
        (load (fun _ => initial) halt))

/-- Stack order: counter, preserved ordinal, base, dividend, copy scratch,
division scratch, remainder, quotient, division scratch. -/
def cfg (l : Option Label) (s : Control)
    (counter y base dividend copyScratch count rem quo saved : List Bool) : Config :=
  ⟨l,s,![counter,y,base,dividend,copyScratch,count,rem,quo,saved]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) := Function.iterate_succ_apply _ _ _

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def copyFrame (counter base count rem quo saved : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) BitMachineCopy.Label (Option Bool)) : Config :=
  renameCfg copyStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixUnaryDivision.Label.start)) (false,false)
      (fun i => ![counter,base,count,rem,quo,saved] i) c)

theorem copy_run (i y cols : ℕ) :
    ∃ t ≤ 2*y+2,
      run t (cfg (some start) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true) [] [] [] [] [] []) =
      cfg (some divide) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate y true) [] [] [] [] [] := by
  have he := BitMachineCopy.run_correct none (List.replicate y true) []
  simp only [List.length_replicate, List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed copyStacks
    (Equiv.refl _) (Equiv.refl _) BitMachineCopy.program program
    (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl)
    (false,false)
    (fun k => ![List.replicate i true,List.replicate cols true,[],[],[],[]] k)
    (BitMachineCopy.cfg (some .scan) none (List.replicate y true) [] [])
    (2*y+2)
    (by rw [show ((advance BitMachineCopy.program)^[2*y+2]) _ = _ from he]; rfl)
  change run t (copyFrame (List.replicate i true)
    (List.replicate cols true) [] [] [] [] _) =
    copyFrame (List.replicate i true)
      (List.replicate cols true) [] [] [] [] (BitMachineCopy.run _ _) at hr
  rw [he] at hr
  have hi : copyFrame (List.replicate i true)
      (List.replicate cols true) [] [] [] []
      (BitMachineCopy.cfg (some .scan) none (List.replicate y true) [] []) =
      cfg (some start) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true) [] [] [] [] [] [] := by
    unfold copyFrame renameCfg liftCfg cfg BitMachineCopy.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : copyFrame (List.replicate i true)
      (List.replicate cols true) [] [] [] []
      (BitMachineCopy.cfg none none (List.replicate y true)
        (List.replicate y true) []) =
      cfg (some divide) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate y true) [] [] [] [] [] := by
    unfold copyFrame renameCfg liftCfg cfg BitMachineCopy.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

private theorem step_test_zero (s : Control) (y base rem quo : List Bool) :
    advance program (cfg (some test) s [] y base [] [] [] rem quo []) =
      cfg (some (.inr (.inr .clearQuotient))) (s.1,s.2.1,false)
        [] y base [] [] [] rem quo [] := by
  simp [advance, TM2.step, TM2.stepAux, program, test, cfg]

private theorem step_test_succ (s : Control) (i : ℕ) (y base rem quo : List Bool) :
    advance program (cfg (some test) s (List.replicate (i+1) true)
      y base [] [] [] rem quo []) =
      cfg (some (.inr (.inr .clearRemainder))) (s.1,s.2.1,true)
        (List.replicate i true) y base [] [] [] rem quo [] := by
  simp [advance, TM2.step, TM2.stepAux, program, test, cfg, List.replicate_succ]
  all_goals funext k; fin_cases k <;> rfl

private theorem step_clear_rem_cons (s : Control) (counter y base quo : List Bool)
    (r : ℕ) :
    advance program (cfg (some (.inr (.inr .clearRemainder))) s
      counter y base [] [] [] (List.replicate (r+1) true) quo []) =
      cfg (some (.inr (.inr .clearRemainder))) (s.1,s.2.1,true)
        counter y base [] [] [] (List.replicate r true) quo [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, List.replicate_succ]
  all_goals funext k; fin_cases k <;> rfl

private theorem step_clear_rem_zero (s : Control) (counter y base quo : List Bool) :
    advance program (cfg (some (.inr (.inr .clearRemainder))) s
      counter y base [] [] [] [] quo []) =
      cfg (some (.inr (.inr .moveQuotient))) (s.1,s.2.1,false)
        counter y base [] [] [] [] quo [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

private theorem step_move_quo_cons (s : Control) (counter y base : List Bool)
    (q w : ℕ) :
    advance program (cfg (some (.inr (.inr .moveQuotient))) s
      counter y base (List.replicate w true) [] [] []
      (List.replicate (q+1) true) []) =
      cfg (some (.inr (.inr .moveQuotient))) (s.1,s.2.1,true)
        counter y base (List.replicate (w+1) true) [] [] []
        (List.replicate q true) [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, List.replicate_succ]
  all_goals funext k; fin_cases k <;> rfl

private theorem step_move_quo_zero (s : Control) (counter y base work : List Bool) :
    advance program (cfg (some (.inr (.inr .moveQuotient))) s
      counter y base work [] [] [] [] []) =
      cfg (some divide) (s.1,s.2.1,false)
        counter y base work [] [] [] [] [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, divide]

private theorem step_clear_quo_cons (s : Control) (counter y base rem : List Bool)
    (q : ℕ) :
    advance program (cfg (some (.inr (.inr .clearQuotient))) s
      counter y base [] [] [] rem (List.replicate (q+1) true) []) =
      cfg (some (.inr (.inr .clearQuotient))) (s.1,s.2.1,true)
        counter y base [] [] [] rem (List.replicate q true) [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, List.replicate_succ]
  all_goals funext k; fin_cases k <;> rfl

private theorem step_clear_quo_zero (s : Control) (counter y base rem : List Bool) :
    advance program (cfg (some (.inr (.inr .clearQuotient))) s
      counter y base [] [] [] rem [] []) =
      cfg none initial counter y base [] [] [] rem [] [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, initial]

theorem clear_remainder_run (r : ℕ) (s : Control)
    (counter y base quo : List Bool) :
    run (r+1) (cfg (some (.inr (.inr .clearRemainder))) s
      counter y base [] [] [] (List.replicate r true) quo []) =
      cfg (some (.inr (.inr .moveQuotient))) (s.1,s.2.1,false)
        counter y base [] [] [] [] quo [] := by
  induction r generalizing s with
  | zero => simpa using run_succ 0 _ |>.trans (by simpa using step_clear_rem_zero s counter y base quo)
  | succ r ih =>
      rw [run_succ, step_clear_rem_cons]
      simpa only [Nat.succ_eq_add_one] using ih (s.1,s.2.1,true)

theorem move_quotient_run (q w : ℕ) (s : Control)
    (counter y base : List Bool) :
    run (q+1) (cfg (some (.inr (.inr .moveQuotient))) s
      counter y base (List.replicate w true) [] [] []
      (List.replicate q true) []) =
      cfg (some divide) (s.1,s.2.1,false)
        counter y base (List.replicate (w+q) true) [] [] [] [] [] := by
  induction q generalizing w s with
  | zero =>
      simpa using step_move_quo_zero s counter y base (List.replicate w true)
  | succ q ih =>
      rw [run_succ, step_move_quo_cons]
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 q]
        using ih (w+1) (s.1,s.2.1,true)

theorem clear_quotient_run (q : ℕ) (s : Control)
    (counter y base rem : List Bool) :
    run (q+1) (cfg (some (.inr (.inr .clearQuotient))) s
      counter y base [] [] [] rem (List.replicate q true) []) =
      cfg none initial counter y base [] [] [] rem [] [] := by
  induction q generalizing s with
  | zero => simpa using step_clear_quo_zero s counter y base rem
  | succ q ih =>
      rw [run_succ, step_clear_quo_cons]
      simpa only [Nat.succ_eq_add_one] using ih (s.1,s.2.1,true)

theorem after_division_zero (y cols work : ℕ) :
    run (work/cols+2)
      (cfg (some test) initial [] (List.replicate y true)
        (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true)
        (List.replicate (work/cols) true) []) =
      cfg none initial [] (List.replicate y true)
        (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true) [] [] := by
  have h₁ : run 1
      (cfg (some test) initial [] (List.replicate y true)
        (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true)
        (List.replicate (work/cols) true) []) =
      cfg (some (.inr (.inr .clearQuotient))) (none,false,false)
        [] (List.replicate y true) (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true)
        (List.replicate (work/cols) true) [] := by
    simpa [run_succ] using step_test_zero initial
      (List.replicate y true) (List.replicate cols true)
      (List.replicate (work%cols) true) (List.replicate (work/cols) true)
  have h₂ := clear_quotient_run (work/cols) (none,false,false)
    ([] : List Bool) (List.replicate y true) (List.replicate cols true)
    (List.replicate (work%cols) true)
  have h := (run_add h₁ (work/cols+1)).trans h₂
  simpa only [show 1+(work/cols+1)=work/cols+2 by omega] using h

theorem after_division_succ (i y cols work : ℕ) :
    run ((work%cols)+(work/cols)+3)
      (cfg (some test) initial (List.replicate (i+1) true)
        (List.replicate y true) (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true)
        (List.replicate (work/cols) true) []) =
      cfg (some divide) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate (work/cols) true) [] [] [] [] [] := by
  have h₁ : run 1
      (cfg (some test) initial (List.replicate (i+1) true)
        (List.replicate y true) (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true)
        (List.replicate (work/cols) true) []) =
      cfg (some (.inr (.inr .clearRemainder))) (none,false,true)
        (List.replicate i true) (List.replicate y true)
        (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true)
        (List.replicate (work/cols) true) [] := by
    simpa [run_succ] using step_test_succ initial i
      (List.replicate y true) (List.replicate cols true)
      (List.replicate (work%cols) true) (List.replicate (work/cols) true)
  have h₂ := clear_remainder_run (work%cols) (none,false,true)
    (List.replicate i true) (List.replicate y true)
    (List.replicate cols true) (List.replicate (work/cols) true)
  have h₃ := move_quotient_run (work/cols) 0 (none,false,false)
    (List.replicate i true) (List.replicate y true)
    (List.replicate cols true)
  have h := (run_add ((run_add h₁ (work%cols+1)).trans h₂)
    (work/cols+1)).trans h₃
  simpa only [Nat.zero_add,
    show 1+(work%cols+1)+(work/cols+1) = (work%cols)+(work/cols)+3 by omega]
    using h

def divisionFrame (counter y copyScratch : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg divisionStacks divisionLabels divisionControl
    (liftCfg (some (.inr Admin.test)) (none,false)
      (fun i => ![counter,y,copyScratch] i) c)

theorem division_run (i y work cols : ℕ) :
    ∃ t ≤ MatrixUnaryDivision.totalTime work cols,
      run t (cfg (some divide) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate work true) [] [] [] [] []) =
      cfg (some test) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true)
        [] [] [] (List.replicate (work%cols) true)
        (List.replicate (work/cols) true) [] := by
  have he := MatrixUnaryDivision.division_total_run work cols
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed divisionStacks divisionLabels
    divisionControl MatrixUnaryDivision.program program
    (some (.inr Admin.test)) (fun _ => rfl) (none,false)
    (fun k => ![List.replicate i true,List.replicate y true,[]] k)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate work true)
      (List.replicate cols true) [] [] [] [])
    (MatrixUnaryDivision.totalTime work cols)
    (by rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime work cols]) _ = _ from he]; rfl)
  change run t (divisionFrame (List.replicate i true)
    (List.replicate y true) [] _) =
    divisionFrame (List.replicate i true)
      (List.replicate y true) [] (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : divisionFrame (List.replicate i true)
      (List.replicate y true) []
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate work true)
        (List.replicate cols true) [] [] [] []) =
      cfg (some divide) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate work true) [] [] [] [] [] := by
    unfold divisionFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : divisionFrame (List.replicate i true)
      (List.replicate y true) []
      (MatrixUnaryDivision.cfg none false [] (List.replicate cols true) []
        (List.replicate (work%cols) true) (List.replicate (work/cols) true) []) =
      cfg (some test) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true) [] [] []
        (List.replicate (work%cols) true) (List.replicate (work/cols) true) [] := by
    unfold divisionFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

/-- A full variable-length mixed-radix selection, including every unary
division and inter-division transfer.  `work` is the physically copied column
ordinal; `y` is its untouched original. -/
theorem digit_from_divide (i y work cols : ℕ) :
    ∃ t ≤ 12*(i+1)*(work+cols+1),
      run t (cfg (some divide) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate work true) [] [] [] [] []) =
      cfg none initial [] (List.replicate y true) (List.replicate cols true)
        [] [] [] (List.replicate (work / cols^i % cols) true) [] [] := by
  induction i generalizing work with
  | zero =>
      obtain ⟨a,ha,he⟩ := division_run 0 y work cols
      have hb := after_division_zero y cols work
      refine ⟨a+(work/cols+2), ?_, ?_⟩
      · have hd := MatrixUnaryDivision.totalTime_bound work cols
        have hq := Nat.div_le_self work cols
        omega
      · simpa using (run_add he (work/cols+2)).trans hb
  | succ i ih =>
      obtain ⟨a,ha,he⟩ := division_run (i+1) y work cols
      have hb := after_division_succ i y cols work
      obtain ⟨c,hc,hr⟩ := ih (work/cols)
      refine ⟨a+((work%cols)+(work/cols)+3)+c, ?_, ?_⟩
      · have hd := MatrixUnaryDivision.totalTime_bound work cols
        have hq := Nat.div_le_self work cols
        have hm := Nat.mod_le work cols
        have hprod : 12*(i+1)*((work/cols)+cols+1) ≤
            12*(i+1)*(work+cols+1) := by
          exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right hq cols) 1)
        nlinarith
      · have h := (run_add ((run_add he ((work%cols)+(work/cols)+3)).trans hb) c).trans hr
        have hdiv : (work/cols)/cols^i = work/cols^(i+1) := by
          rw [Nat.div_div_eq_div_mul, pow_succ]
          simp [Nat.mul_comm]
        simpa only [Nat.add_assoc, hdiv] using h

def callbackBound (i y cols : ℕ) : ℕ :=
  2*y+2+12*(i+1)*(y+cols+1)

/-- The original column ordinal and base survive.  The selector counter and
all scratch banks are cleared; the chosen digit is the only new word. -/
theorem digit_run (i y cols : ℕ) :
    ∃ t ≤ callbackBound i y cols,
      run t (cfg (some start) initial (List.replicate i true)
        (List.replicate y true) (List.replicate cols true) [] [] [] [] [] []) =
      cfg none initial [] (List.replicate y true) (List.replicate cols true)
        [] [] [] (List.replicate (y / cols^i % cols) true) [] [] := by
  obtain ⟨a,ha,he⟩ := copy_run i y cols
  obtain ⟨b,hb,hr⟩ := digit_from_divide i y y cols
  refine ⟨a+b, ?_, ?_⟩
  · exact Nat.add_le_add ha hb
  · exact (run_add he b).trans hr

end EthInapproximability.CurrentPaper.MatrixTableInterlaceDigit
