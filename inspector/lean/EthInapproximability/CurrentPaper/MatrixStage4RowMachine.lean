import EthInapproximability.CurrentPaper.MatrixStage4Decode
import EthInapproximability.CurrentPaper.MatrixUnaryCut
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Variable-bin Stage--4 raw-row header, physically decoded

Source: frozen v8 `03-parameterized-construction.tex`, `eq:paper-B-carriers`,
and `B-effectivity-details.tex`, `thm:paper-materialization`.

One fixed ten-stack Boolean machine tests the `s*L` template threshold.
Template rows divide by `L`, leaving bin and family index; graph rows divide
their offset by `|X|`, leaving item and source-row index.  The three scalar
parameters are supplied as unary stacks; preparing them is a separate
charged operation.  No number is kept in the finite control.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4RowMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev Stack := Fin 10
abbrev Label := MatrixUnaryCut.Label ⊕
  (MatrixUnaryDivision.Label ⊕ (MatrixUnaryDivision.Label ⊕ Bool))
abbrev Control := MatrixUnaryCut.Control × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := ((false,true),false)
def cutStart : Label := .inl .scan
def dispatch : Label := .inr (.inr (.inr false))
def templateStart : Label := .inr (.inl .start)
def itemStart : Label := .inr (.inr (.inl .start))
def done : Label := .inr (.inr (.inr true))

def cutStacks : Fin 4 ⊕ Fin 6 ≃ Stack := finSumFinEquiv

def templatePermutation : Stack ≃ Stack where
  toFun := ![0,4,6,7,8,9,1,2,3,5]
  invFun := ![0,6,7,8,1,9,2,3,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def templateStacks : Fin 6 ⊕ Fin 4 ≃ Stack :=
  finSumFinEquiv.trans templatePermutation

def itemPermutation : Stack ≃ Stack where
  toFun := ![0,5,6,7,8,9,1,2,3,4]
  invFun := ![0,6,7,8,9,1,2,3,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def itemStacks : Fin 6 ⊕ Fin 4 ≃ Stack :=
  finSumFinEquiv.trans itemPermutation

def templateLabels : MatrixUnaryDivision.Label ⊕
    (MatrixUnaryCut.Label ⊕ (MatrixUnaryDivision.Label ⊕ Bool)) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inr (.inl l))
    | .inr (.inr (.inr b)) => .inr (.inr (.inr b))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inr (.inl l))
    | .inr (.inr (.inr b)) => .inr (.inr (.inr b))
  left_inv l := by rcases l with l | (l | (l | b)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | b)) <;> rfl

def itemLabels : MatrixUnaryDivision.Label ⊕
    (MatrixUnaryCut.Label ⊕ (MatrixUnaryDivision.Label ⊕ Bool)) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr b)) => .inr (.inr (.inr b))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr b)) => .inr (.inr (.inr b))
  left_inv l := by rcases l with l | (l | (l | b)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | b)) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt cutStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inr (.inr false))) (MatrixUnaryCut.program l))
  | .inr (.inl l) => renameStmt templateStacks templateLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr (.inr true))) (MatrixUnaryDivision.program l))
  | .inr (.inr (.inl l)) => renameStmt itemStacks itemLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr (.inr true))) (MatrixUnaryDivision.program l))
  | .inr (.inr (.inr false)) =>
      branch (fun v => v.1.1) (goto (fun _ => itemStart))
        (goto (fun _ => templateStart))
  | .inr (.inr (.inr true)) => load (fun _ => initial) halt

def cfg (l : Option Label) (v : Control)
    (row threshold familyWidth rowWidth count remainder quotient saved : List Bool) : Config :=
  ⟨l,v,![row,threshold,[],[],familyWidth,rowWidth,count,remainder,quotient,saved]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def cutFrame (familyWidth rowWidth count remainder quotient saved : List Bool)
    (c : MatrixUnaryCut.Config) : Config :=
  renameCfg cutStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inr (.inr false))) false
      (fun i => ![familyWidth,rowWidth,count,remainder,quotient,saved] i) c)

theorem cut_run (row threshold : ℕ) (familyWidth rowWidth : List Bool) :
    ∃ t ≤ 3 * min row threshold + 4,
      run t (cfg (some cutStart) initial
        (List.replicate row true) (List.replicate threshold true)
        familyWidth rowWidth [] [] [] []) =
      cfg (some dispatch) ((decide (threshold ≤ row),false),false)
        (List.replicate (if row < threshold then row else row-threshold) true)
        (List.replicate threshold true) familyWidth rowWidth [] [] [] [] := by
  obtain ⟨a,ha,he⟩ := MatrixUnaryCut.cut_run row threshold
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed cutStacks
    (Equiv.refl _) (Equiv.refl _) MatrixUnaryCut.program program
    (some (.inr (.inr false))) (fun _ => rfl) false
    (fun i => ![familyWidth,rowWidth,[],[],[],[]] i)
    (MatrixUnaryCut.cfg (some .scan) (false,true)
      (List.replicate row true) (List.replicate threshold true) [] []) a
    (by rw [show ((advance MatrixUnaryCut.program)^[a]) _ = _ from he]; rfl)
  change run t (cutFrame familyWidth rowWidth [] [] [] [] _) =
    cutFrame familyWidth rowWidth [] [] [] [] (MatrixUnaryCut.run _ _) at hr
  rw [he] at hr
  have hi : cutFrame familyWidth rowWidth [] [] [] []
      (MatrixUnaryCut.cfg (some .scan) (false,true)
        (List.replicate row true) (List.replicate threshold true) [] []) =
      cfg (some cutStart) initial (List.replicate row true)
        (List.replicate threshold true) familyWidth rowWidth [] [] [] [] := by
    unfold cutFrame renameCfg liftCfg cfg MatrixUnaryCut.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : cutFrame familyWidth rowWidth [] [] [] []
      (MatrixUnaryCut.cfg none (decide (threshold ≤ row),false)
        (List.replicate (if row < threshold then row else row-threshold) true)
        (List.replicate threshold true) [] []) =
      cfg (some dispatch) ((decide (threshold ≤ row),false),false)
        (List.replicate (if row < threshold then row else row-threshold) true)
        (List.replicate threshold true) familyWidth rowWidth [] [] [] [] := by
    unfold cutFrame renameCfg liftCfg cfg MatrixUnaryCut.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht.trans ha,by simpa only [hi,hf] using hr⟩

theorem dispatch_template (row threshold familyWidth rowWidth : List Bool) :
    run 1 (cfg (some dispatch) ((false,false),false)
      row threshold familyWidth rowWidth [] [] [] []) =
    cfg (some templateStart) ((false,false),false)
      row threshold familyWidth rowWidth [] [] [] [] := by
  simp [run,advance,cfg,dispatch,templateStart,program,TM2.step,TM2.stepAux]

theorem dispatch_item (row threshold familyWidth rowWidth : List Bool) :
    run 1 (cfg (some dispatch) ((true,false),false)
      row threshold familyWidth rowWidth [] [] [] []) =
    cfg (some itemStart) ((true,false),false)
      row threshold familyWidth rowWidth [] [] [] [] := by
  simp [run,advance,cfg,dispatch,itemStart,program,TM2.step,TM2.stepAux]

def templateFrame (threshold rowWidth : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg templateStacks templateLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr (.inr true))) (false,false)
      (fun i => ![threshold,[],[],rowWidth] i) c)

theorem template_division_run (n L : ℕ) (threshold rowWidth : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n L,
      run t (cfg (some templateStart) ((false,false),false)
        (List.replicate n true) threshold
        (List.replicate L true) rowWidth [] [] [] []) =
      cfg (some done) ((false,false),false) [] threshold
        (List.replicate L true) rowWidth []
        (List.replicate (n%L) true) (List.replicate (n/L) true) [] := by
  have he := MatrixUnaryDivision.division_total_run n L
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed templateStacks templateLabels
    (Equiv.prodComm _ _) MatrixUnaryDivision.program program
    (some (.inr (.inr true))) (fun _ => rfl) (false,false)
    (fun i => ![threshold,[],[],rowWidth] i)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate L true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n L)
    (by
      rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n L])
        _ = _ from he]
      rfl)
  change run t (templateFrame threshold rowWidth _) =
    templateFrame threshold rowWidth (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : templateFrame threshold rowWidth
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
        (List.replicate L true) [] [] [] []) =
      cfg (some templateStart) ((false,false),false)
        (List.replicate n true) threshold
        (List.replicate L true) rowWidth [] [] [] [] := by
    unfold templateFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : templateFrame threshold rowWidth
      (MatrixUnaryDivision.cfg none false [] (List.replicate L true) []
        (List.replicate (n%L) true) (List.replicate (n/L) true) []) =
      cfg (some done) ((false,false),false) [] threshold
        (List.replicate L true) rowWidth []
        (List.replicate (n%L) true) (List.replicate (n/L) true) [] := by
    unfold templateFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def itemFrame (threshold familyWidth : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg itemStacks itemLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr (.inr true))) (true,false)
      (fun i => ![threshold,[],[],familyWidth] i) c)

theorem item_division_run (n rx : ℕ) (threshold familyWidth : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n rx,
      run t (cfg (some itemStart) ((true,false),false)
        (List.replicate n true) threshold familyWidth
        (List.replicate rx true) [] [] [] []) =
      cfg (some done) ((true,false),false) [] threshold familyWidth
        (List.replicate rx true) []
        (List.replicate (n%rx) true) (List.replicate (n/rx) true) [] := by
  have he := MatrixUnaryDivision.division_total_run n rx
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed itemStacks itemLabels
    (Equiv.prodComm _ _) MatrixUnaryDivision.program program
    (some (.inr (.inr true))) (fun _ => rfl) (true,false)
    (fun i => ![threshold,[],[],familyWidth] i)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate rx true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n rx)
    (by
      rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n rx])
        _ = _ from he]
      rfl)
  change run t (itemFrame threshold familyWidth _) =
    itemFrame threshold familyWidth (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : itemFrame threshold familyWidth
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
        (List.replicate rx true) [] [] [] []) =
      cfg (some itemStart) ((true,false),false)
        (List.replicate n true) threshold familyWidth
        (List.replicate rx true) [] [] [] [] := by
    unfold itemFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : itemFrame threshold familyWidth
      (MatrixUnaryDivision.cfg none false [] (List.replicate rx true) []
        (List.replicate (n%rx) true) (List.replicate (n/rx) true) []) =
      cfg (some done) ((true,false),false) [] threshold familyWidth
        (List.replicate rx true) []
        (List.replicate (n%rx) true) (List.replicate (n/rx) true) [] := by
    unfold itemFrame renameCfg liftCfg cfg MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

theorem done_run (v : Control) (threshold familyWidth rowWidth
    count remainder quotient saved : List Bool) :
    run 1 (cfg (some done) v [] threshold familyWidth rowWidth
      count remainder quotient saved) =
    cfg none initial [] threshold familyWidth rowWidth
      count remainder quotient saved := by
  simp [run,advance,cfg,done,program,TM2.step,TM2.stepAux]

theorem template_run (n threshold L rx : ℕ) (h : n < threshold) :
    ∃ t ≤ 11*n+3*L+10,
      run t (cfg (some cutStart) initial
        (List.replicate n true) (List.replicate threshold true)
        (List.replicate L true) (List.replicate rx true) [] [] [] []) =
      cfg none initial [] (List.replicate threshold true)
        (List.replicate L true) (List.replicate rx true) []
        (List.replicate (n%L) true) (List.replicate (n/L) true) [] := by
  obtain ⟨a,ha,he⟩ := cut_run n threshold
    (List.replicate L true) (List.replicate rx true)
  simp only [if_pos h, decide_eq_false_iff_not.mpr (Nat.not_le.mpr h)] at he
  obtain ⟨b,hb,hbe⟩ := template_division_run n L
    (List.replicate threshold true) (List.replicate rx true)
  have h₁ : run (a+1) (cfg (some cutStart) initial
      (List.replicate n true) (List.replicate threshold true)
      (List.replicate L true) (List.replicate rx true) [] [] [] []) =
      cfg (some templateStart) ((false,false),false)
        (List.replicate n true) (List.replicate threshold true)
        (List.replicate L true) (List.replicate rx true) [] [] [] [] := by
    rw [run_add he 1]
    exact dispatch_template _ _ _ _
  have h₂ : run ((a+1)+b) (cfg (some cutStart) initial
      (List.replicate n true) (List.replicate threshold true)
      (List.replicate L true) (List.replicate rx true) [] [] [] []) =
      cfg (some done) ((false,false),false) []
        (List.replicate threshold true) (List.replicate L true)
        (List.replicate rx true) []
        (List.replicate (n%L) true) (List.replicate (n/L) true) [] := by
    rw [run_add h₁ b]
    exact hbe
  refine ⟨(a+1+b)+1, ?_, ?_⟩
  · have ht := MatrixUnaryDivision.totalTime_bound n L
    have hm : min n threshold = n := Nat.min_eq_left (Nat.le_of_lt h)
    omega
  · rw [run_add h₂ 1]
    exact done_run _ _ _ _ _ _ _ _

theorem item_run (offset threshold L rx : ℕ) (h : threshold ≤ offset) :
    ∃ t ≤ 3*threshold+8*(offset-threshold)+3*rx+10,
      run t (cfg (some cutStart) initial
        (List.replicate offset true) (List.replicate threshold true)
        (List.replicate L true) (List.replicate rx true) [] [] [] []) =
      cfg none initial [] (List.replicate threshold true)
        (List.replicate L true) (List.replicate rx true) []
        (List.replicate ((offset-threshold)%rx) true)
        (List.replicate ((offset-threshold)/rx) true) [] := by
  obtain ⟨a,ha,he⟩ := cut_run offset threshold
    (List.replicate L true) (List.replicate rx true)
  simp only [if_neg (Nat.not_lt.mpr h), decide_eq_true_iff.mpr h] at he
  obtain ⟨b,hb,hbe⟩ := item_division_run (offset-threshold) rx
    (List.replicate threshold true) (List.replicate L true)
  have h₁ : run (a+1) (cfg (some cutStart) initial
      (List.replicate offset true) (List.replicate threshold true)
      (List.replicate L true) (List.replicate rx true) [] [] [] []) =
      cfg (some itemStart) ((true,false),false)
        (List.replicate (offset-threshold) true) (List.replicate threshold true)
        (List.replicate L true) (List.replicate rx true) [] [] [] [] := by
    rw [run_add he 1]
    exact dispatch_item _ _ _ _
  have h₂ : run ((a+1)+b) (cfg (some cutStart) initial
      (List.replicate offset true) (List.replicate threshold true)
      (List.replicate L true) (List.replicate rx true) [] [] [] []) =
      cfg (some done) ((true,false),false) []
        (List.replicate threshold true) (List.replicate L true)
        (List.replicate rx true) []
        (List.replicate ((offset-threshold)%rx) true)
        (List.replicate ((offset-threshold)/rx) true) [] := by
    rw [run_add h₁ b]
    exact hbe
  refine ⟨(a+1+b)+1, ?_, ?_⟩
  · have ht := MatrixUnaryDivision.totalTime_bound (offset-threshold) rx
    have hm : min offset threshold = threshold := Nat.min_eq_right h
    omega
  · rw [run_add h₂ 1]
    exact done_run _ _ _ _ _ _ _ _

open Construction MatrixStage4Codes MatrixStage4Digits

theorem template_row_run {s L nv nb rx : ℕ} (order : ItemOrder nv nb)
    (p : Fin s) (ℓ : Fin L) :
    ∃ t ≤ 11*(rowCode s L nv nb rx order (.inl (p,ℓ))).val+3*L+10,
      run t (cfg (some cutStart) initial
        (List.replicate (rowCode s L nv nb rx order (.inl (p,ℓ))).val true)
        (List.replicate (s*L) true) (List.replicate L true)
        (List.replicate rx true) [] [] [] []) =
      cfg none initial [] (List.replicate (s*L) true)
        (List.replicate L true) (List.replicate rx true) []
        (List.replicate ℓ.val true) (List.replicate p.val true) [] := by
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le ℓ.val) ℓ.isLt
  have hp : L*p.val+L ≤ s*L := by
    calc
      L*p.val+L = L*(p.val+1) := by ring
      _ ≤ L*s := Nat.mul_le_mul_left L (by omega)
      _ = s*L := Nat.mul_comm _ _
  have hrow : (rowCode s L nv nb rx order (.inl (p,ℓ))).val < s*L := by
    rw [template_row_value]
    omega
  have hdiv : (rowCode s L nv nb rx order (.inl (p,ℓ))).val / L = p.val := by
    rw [template_row_value]
    rw [Nat.add_mul_div_left _ _ hL]
    simp [Nat.div_eq_of_lt ℓ.isLt]
  have hmod : (rowCode s L nv nb rx order (.inl (p,ℓ))).val % L = ℓ.val := by
    rw [template_row_value]
    simp [Nat.mod_eq_of_lt ℓ.isLt]
  simpa only [hdiv,hmod] using template_run
    (rowCode s L nv nb rx order (.inl (p,ℓ))).val (s*L) L rx hrow

theorem item_row_run {s L nv nb rx : ℕ} (order : ItemOrder nv nb)
    (i : Fin (nv + nb)) (x : Fin rx) :
    ∃ t ≤ 3*(s*L)+8*(x.val+rx*i.val)+3*rx+10,
      run t (cfg (some cutStart) initial
        (List.replicate
          (rowCode s L nv nb rx order
            ((rawRowEquiv s L nv nb order).symm (.inr (i,x)))).val true)
        (List.replicate (s*L) true) (List.replicate L true)
        (List.replicate rx true) [] [] [] []) =
      cfg none initial [] (List.replicate (s*L) true)
        (List.replicate L true) (List.replicate rx true) []
        (List.replicate x.val true) (List.replicate i.val true) [] := by
  let n := (rowCode s L nv nb rx order
    ((rawRowEquiv s L nv nb order).symm (.inr (i,x)))).val
  have hn : n = s*L+x.val+rx*i.val := item_row_value order i x
  have hcut : s*L ≤ n := by omega
  have hsub : n-s*L = x.val+rx*i.val := by omega
  have hrx : 0 < rx := lt_of_le_of_lt (Nat.zero_le x.val) x.isLt
  have hdiv : (x.val+rx*i.val)/rx = i.val := by
    rw [Nat.add_mul_div_left _ _ hrx]
    simp [Nat.div_eq_of_lt x.isLt]
  have hmod : (x.val+rx*i.val)%rx = x.val := by
    simp [Nat.mod_eq_of_lt x.isLt]
  simpa only [hsub,hmod,hdiv] using item_run n (s*L) L rx hcut

end EthInapproximability.CurrentPaper.MatrixStage4RowMachine
