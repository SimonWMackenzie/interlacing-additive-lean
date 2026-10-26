import EthInapproximability.CurrentPaper.MatrixTableInterlaceDigit
import EthInapproximability.CurrentPaper.MatrixTableLookup
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Fixed-stack classical interlace entry program

Source: frozen v8 `def:paper-interlace` and Appendix B
`thm:paper-materialization`.  The first two phases copy and divide the
row ordinal by the old row count, leaving the within-block row and block
index on physical stacks.  The digit program then computes the selected
coordinate from the original column ordinal and old column count.  The
literal source table is finally addressed and read.  Cleanup restores the
per-cell bank used by the row-major writer.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceEntry

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

inductive Admin where
  | clearDigit | clearRow
  deriving DecidableEq, Fintype

abbrev Label := BitMachineCopy.Label ⊕
  (MatrixUnaryDivision.Label ⊕
    (MatrixTableInterlaceDigit.Label ⊕ (MatrixTableLookup.Label ⊕ Admin)))
abbrev Control := (Option Bool × Bool) ×
  (MatrixTableInterlaceDigit.Control × MatrixTableLookup.Control)
abbrev Stack := Fin 23
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control :=
  ((none,false),(MatrixTableInterlaceDigit.initial,MatrixTableLookup.initial))
def start : Label := .inl .scan
def rowDivide : Label := .inr (.inl .start)
def digitStart : Label := .inr (.inr (.inl MatrixTableInterlaceDigit.start))
def lookupStart : Label := .inr (.inr (.inr (.inl MatrixTableLookup.start)))

private def rowCopyPerm : Stack ≃ Stack where
  toFun := ![0,2,3,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
  invFun := ![0,3,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def rowCopyStacks : Fin 3 ⊕ Fin 20 ≃ Stack := finSumFinEquiv.trans rowCopyPerm

private def rowDivPerm : Stack ≃ Stack where
  toFun := ![2,1,4,5,6,7,0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
  invFun := ![6,1,0,7,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def rowDivStacks : Fin 6 ⊕ Fin 17 ≃ Stack := finSumFinEquiv.trans rowDivPerm

private def digitPerm : Stack ≃ Stack where
  toFun := ![6,8,9,10,11,12,13,14,15,0,1,2,3,4,5,7,16,17,18,19,20,21,22]
  invFun := ![9,10,11,12,13,14,0,15,1,2,3,4,5,6,7,8,16,17,18,19,20,21,22]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def digitStacks : Fin 9 ⊕ Fin 14 ≃ Stack := finSumFinEquiv.trans digitPerm

private def lookupPerm : Stack ≃ Stack where
  toFun := ![5,9,13,16,17,18,19,20,21,22,0,1,2,3,4,6,7,8,10,11,12,14,15]
  invFun := ![10,11,12,13,14,0,15,16,17,1,18,19,20,2,21,22,3,4,5,6,7,8,9]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def lookupStacks : Fin 10 ⊕ Fin 13 ≃ Stack := finSumFinEquiv.trans lookupPerm

def rowCopyControl : Option Bool ×
    (Bool × (MatrixTableInterlaceDigit.Control × MatrixTableLookup.Control)) ≃ Control where
  toFun s := ((s.1,s.2.1),s.2.2)
  invFun s := (s.1.1,s.1.2,s.2)
  left_inv _ := rfl
  right_inv _ := rfl

def rowDivControl : Bool ×
    (Option Bool × (MatrixTableInterlaceDigit.Control × MatrixTableLookup.Control)) ≃ Control where
  toFun s := ((s.2.1,s.1),s.2.2)
  invFun s := (s.1.2,s.1.1,s.2)
  left_inv _ := rfl
  right_inv _ := rfl

def digitControl : MatrixTableInterlaceDigit.Control ×
    ((Option Bool × Bool) × MatrixTableLookup.Control) ≃ Control where
  toFun s := (s.2.1,(s.1,s.2.2))
  invFun s := (s.2.1,(s.1,s.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def lookupControl : MatrixTableLookup.Control ×
    ((Option Bool × Bool) × MatrixTableInterlaceDigit.Control) ≃ Control where
  toFun s := (s.2.1,(s.2.2,s.1))
  invFun s := (s.2.2,(s.1,s.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rowDivLabels : MatrixUnaryDivision.Label ⊕
    (BitMachineCopy.Label ⊕
      (MatrixTableInterlaceDigit.Label ⊕ (MatrixTableLookup.Label ⊕ Admin))) ≃ Label where
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

def digitLabels : MatrixTableInterlaceDigit.Label ⊕
    (BitMachineCopy.Label ⊕ (MatrixUnaryDivision.Label ⊕ (MatrixTableLookup.Label ⊕ Admin))) ≃ Label where
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

def lookupLabels : MatrixTableLookup.Label ⊕
    (BitMachineCopy.Label ⊕
      (MatrixUnaryDivision.Label ⊕ (MatrixTableInterlaceDigit.Label ⊕ Admin))) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inr (.inl l)))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inl l))
    | .inr (.inr (.inr (.inr l))) => .inr (.inr (.inr (.inr l)))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inl l))) => .inl l
    | .inr (.inr (.inr (.inr l))) => .inr (.inr (.inr (.inr l)))
  left_inv l := by rcases l with l | (l | (l | (l | l))) <;> rfl
  right_inv l := by rcases l with l | (l | (l | (l | l))) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt rowCopyStacks (Equiv.refl _) rowCopyControl
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start)) (BitMachineCopy.program l))
  | .inr (.inl l) => renameStmt rowDivStacks rowDivLabels rowDivControl
      (liftStmt (some (.inr (.inl MatrixTableInterlaceDigit.start)))
        (MatrixUnaryDivision.program l))
  | .inr (.inr (.inl l)) => renameStmt digitStacks digitLabels digitControl
      (liftStmt (some (.inr (.inr (.inl MatrixTableLookup.start))))
        (MatrixTableInterlaceDigit.program l))
  | .inr (.inr (.inr (.inl l))) => renameStmt lookupStacks lookupLabels lookupControl
      (liftStmt (some (.inr (.inr (.inr Admin.clearDigit))))
        (MatrixTableLookup.program l))
  | .inr (.inr (.inr (.inr .clearDigit))) =>
      pop 13 (fun s b => ((s.1.1,b.isSome),s.2))
        (branch (fun s => s.1.2)
          (goto (fun _ => .inr (.inr (.inr (.inr .clearDigit)))))
          (goto (fun _ => .inr (.inr (.inr (.inr .clearRow))))))
  | .inr (.inr (.inr (.inr .clearRow))) =>
      pop 5 (fun s b => ((s.1.1,b.isSome),s.2))
        (branch (fun s => s.1.2)
          (goto (fun _ => .inr (.inr (.inr (.inr .clearRow)))))
          (load (fun _ => initial) halt))

/-- Unlisted slots are scratch or framed words. -/
def cfg (l : Option Label) (s : Control)
    (r rows x y cols digit source answer : List Bool)
    (i : List Bool := []) : Config :=
  ⟨l,s,![r,rows,[],[],[],x,i,[],y,cols,[],[],[],digit,[],[],[],[],[],source,answer,[],[]]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) := Function.iterate_succ_apply _ _ _

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def rowCopied (l : Option Label) (r rows y cols : ℕ)
    (source answer : List Bool) : Config :=
  ⟨l,initial,![List.replicate r true,List.replicate rows true,
    List.replicate r true,[],[],[],[],[],List.replicate y true,
    List.replicate cols true,[],[],[],[],[],[],[],[],[],source,answer,[],[]]⟩

def rowCopyFrame (rows y cols : ℕ) (source answer : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) BitMachineCopy.Label (Option Bool)) : Config :=
  renameCfg rowCopyStacks (Equiv.refl _) rowCopyControl
    (liftCfg (some (.inl MatrixUnaryDivision.Label.start))
      (false,(MatrixTableInterlaceDigit.initial,MatrixTableLookup.initial))
      (fun k => ![List.replicate rows true,[],[],[],[],List.replicate y true,
        List.replicate cols true,[],[],[],[],[],[],[],[],[],source,answer,[],[]] k) c)

theorem row_copy_run (r rows y cols : ℕ) (source answer : List Bool) :
    ∃ t ≤ 2*r+2,
      run t (cfg (some start) initial (List.replicate r true)
        (List.replicate rows true) [] (List.replicate y true)
        (List.replicate cols true) [] source answer) =
      rowCopied (some rowDivide) r rows y cols source answer := by
  have he := BitMachineCopy.run_correct none (List.replicate r true) []
  simp only [List.length_replicate, List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed rowCopyStacks
    (Equiv.refl _) rowCopyControl BitMachineCopy.program program
    (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl)
    (false,(MatrixTableInterlaceDigit.initial,MatrixTableLookup.initial))
    (fun k => ![List.replicate rows true,[],[],[],[],List.replicate y true,
      List.replicate cols true,[],[],[],[],[],[],[],[],[],source,answer,[],[]] k)
    (BitMachineCopy.cfg (some .scan) none (List.replicate r true) [] [])
    (2*r+2)
    (by rw [show ((advance BitMachineCopy.program)^[2*r+2]) _ = _ from he]; rfl)
  change run t (rowCopyFrame rows y cols source answer _) =
    rowCopyFrame rows y cols source answer (BitMachineCopy.run _ _) at hr
  rw [he] at hr
  have hi : rowCopyFrame rows y cols source answer
      (BitMachineCopy.cfg (some .scan) none (List.replicate r true) [] []) =
      cfg (some start) initial (List.replicate r true)
        (List.replicate rows true) [] (List.replicate y true)
        (List.replicate cols true) [] source answer := by
    unfold rowCopyFrame renameCfg liftCfg rowCopyControl cfg BitMachineCopy.cfg initial
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : rowCopyFrame rows y cols source answer
      (BitMachineCopy.cfg none none (List.replicate r true)
        (List.replicate r true) []) =
      rowCopied (some rowDivide) r rows y cols source answer := by
    unfold rowCopyFrame renameCfg liftCfg rowCopyControl rowCopied
      BitMachineCopy.cfg initial rowDivide
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def rowDivFrame (r y cols : ℕ) (source answer : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg rowDivStacks rowDivLabels rowDivControl
    (liftCfg (some (.inr (.inl MatrixTableInterlaceDigit.start)))
      (none,(MatrixTableInterlaceDigit.initial,MatrixTableLookup.initial))
      (fun k => ![List.replicate r true,[],List.replicate y true,
        List.replicate cols true,[],[],[],[],[],[],[],[],[],source,answer,[],[]] k) c)

theorem row_division_run (r rows y cols : ℕ) (source answer : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime r rows,
      run t (rowCopied (some rowDivide) r rows y cols source answer) =
      cfg (some digitStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true) [] source answer
        (List.replicate (r/rows) true) := by
  have he := MatrixUnaryDivision.division_total_run r rows
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed rowDivStacks rowDivLabels
    rowDivControl MatrixUnaryDivision.program program
    (some (.inr (.inl MatrixTableInterlaceDigit.start))) (fun _ => rfl)
    (none,(MatrixTableInterlaceDigit.initial,MatrixTableLookup.initial))
    (fun k => ![List.replicate r true,[],List.replicate y true,
      List.replicate cols true,[],[],[],[],[],[],[],[],[],source,answer,[],[]] k)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate r true)
      (List.replicate rows true) [] [] [] [])
    (MatrixUnaryDivision.totalTime r rows)
    (by rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime r rows]) _ = _ from he]; rfl)
  change run t (rowDivFrame r y cols source answer _) =
    rowDivFrame r y cols source answer (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : rowDivFrame r y cols source answer
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate r true)
        (List.replicate rows true) [] [] [] []) =
      rowCopied (some rowDivide) r rows y cols source answer := by
    unfold rowDivFrame renameCfg liftCfg rowDivControl rowCopied
      MatrixUnaryDivision.cfg initial rowDivide
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : rowDivFrame r y cols source answer
      (MatrixUnaryDivision.cfg none false [] (List.replicate rows true) []
        (List.replicate (r%rows) true) (List.replicate (r/rows) true) []) =
      cfg (some digitStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true) [] source answer
        (List.replicate (r/rows) true) := by
    unfold rowDivFrame renameCfg liftCfg rowDivControl cfg
      MatrixUnaryDivision.cfg initial digitStart
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

def digitFrame (r rows x : ℕ) (source answer : List Bool)
    (c : MatrixTableInterlaceDigit.Config) : Config :=
  renameCfg digitStacks digitLabels digitControl
    (liftCfg (some (.inr (.inr (.inl MatrixTableLookup.start))))
      ((none,false),MatrixTableLookup.initial)
      (fun k => ![List.replicate r true,List.replicate rows true,[],[],[],
        List.replicate x true,[],[],[],[],source,answer,[],[]] k) c)

theorem digit_stage_run (r rows y cols : ℕ) (source answer : List Bool) :
    ∃ t ≤ MatrixTableInterlaceDigit.callbackBound (r/rows) y cols,
      run t (cfg (some digitStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true) [] source answer
        (List.replicate (r/rows) true)) =
      cfg (some lookupStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) source answer := by
  have he := MatrixTableInterlaceDigit.digit_run (r/rows) y cols
  obtain ⟨a,ha,hh⟩ := he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed digitStacks digitLabels digitControl
    MatrixTableInterlaceDigit.program program
    (some (.inr (.inr (.inl MatrixTableLookup.start)))) (fun _ => rfl)
    ((none,false),MatrixTableLookup.initial)
    (fun k => ![List.replicate r true,List.replicate rows true,[],[],[],
      List.replicate (r%rows) true,[],[],[],[],source,answer,[],[]] k)
    (MatrixTableInterlaceDigit.cfg (some MatrixTableInterlaceDigit.start)
      MatrixTableInterlaceDigit.initial (List.replicate (r/rows) true)
      (List.replicate y true) (List.replicate cols true) [] [] [] [] [] [])
    a (by rw [show ((advance MatrixTableInterlaceDigit.program)^[a]) _ = _ from hh]; rfl)
  change run t (digitFrame r rows (r%rows) source answer _) =
    digitFrame r rows (r%rows) source answer (MatrixTableInterlaceDigit.run _ _) at hr
  rw [hh] at hr
  have hi : digitFrame r rows (r%rows) source answer
      (MatrixTableInterlaceDigit.cfg (some MatrixTableInterlaceDigit.start)
        MatrixTableInterlaceDigit.initial (List.replicate (r/rows) true)
        (List.replicate y true) (List.replicate cols true) [] [] [] [] [] []) =
      cfg (some digitStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true) [] source answer
        (List.replicate (r/rows) true) := by
    unfold digitFrame renameCfg liftCfg digitControl cfg
      MatrixTableInterlaceDigit.cfg initial digitStart
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : digitFrame r rows (r%rows) source answer
      (MatrixTableInterlaceDigit.cfg none MatrixTableInterlaceDigit.initial []
        (List.replicate y true) (List.replicate cols true) [] [] []
        (List.replicate (y/cols^(r/rows)%cols) true) [] []) =
      cfg (some lookupStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) source answer := by
    unfold digitFrame renameCfg liftCfg digitControl cfg
      MatrixTableInterlaceDigit.cfg initial lookupStart
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht.trans ha,by simpa only [hi,hf] using hr⟩

def lookupFrame (r rows y : ℕ) (_source : List Bool)
    (c : MatrixTableLookup.Config) : Config :=
  renameCfg lookupStacks lookupLabels lookupControl
    (liftCfg (some (.inr (.inr (.inr Admin.clearDigit))))
      ((none,false),MatrixTableInterlaceDigit.initial)
      (fun k => ![List.replicate r true,List.replicate rows true,[],[],[],
        [],[],List.replicate y true,[],[],[],[],[]] k) c)

theorem lookup_stage_run (r rows y cols : ℕ) (source answer : List Bool) :
    ∃ t ≤ 32*((r%rows)+cols+(y/cols^(r/rows)%cols)+source.length+1)^2,
      run t (cfg (some lookupStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) source answer) =
      cfg (some (.inr (.inr (.inr (.inr .clearDigit))))) initial
        (List.replicate r true) (List.replicate rows true)
        (List.replicate (r%rows) true) (List.replicate y true)
        (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) source
        (source[(r%rows)*cols+(y/cols^(r/rows)%cols)]?.getD false::answer) := by
  have he := MatrixTableLookup.lookup_run (r%rows) cols
    (y/cols^(r/rows)%cols) source answer
  obtain ⟨a,ha,hh⟩ := he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed lookupStacks lookupLabels lookupControl
    MatrixTableLookup.program program
    (some (.inr (.inr (.inr Admin.clearDigit)))) (fun _ => rfl)
    ((none,false),MatrixTableInterlaceDigit.initial)
    (fun k => ![List.replicate r true,List.replicate rows true,[],[],[],
      [],[],List.replicate y true,[],[],[],[],[]] k)
    (MatrixTableLookup.cfg (some MatrixTableLookup.start)
      MatrixTableLookup.initial (List.replicate (r%rows) true)
      (List.replicate cols true)
      (List.replicate (y/cols^(r/rows)%cols) true) [] source answer)
    a (by rw [show ((advance MatrixTableLookup.program)^[a]) _ = _ from hh]; rfl)
  change run t (lookupFrame r rows y source _) =
    lookupFrame r rows y source (MatrixTableLookup.run _ _) at hr
  rw [hh] at hr
  have hi : lookupFrame r rows y source
      (MatrixTableLookup.cfg (some MatrixTableLookup.start)
        MatrixTableLookup.initial (List.replicate (r%rows) true)
        (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) [] source answer) =
      cfg (some lookupStart) initial (List.replicate r true)
        (List.replicate rows true) (List.replicate (r%rows) true)
        (List.replicate y true) (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) source answer := by
    unfold lookupFrame renameCfg liftCfg lookupControl cfg
      MatrixTableLookup.cfg initial lookupStart
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : lookupFrame r rows y source
      (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate (r%rows) true) (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) [] source
        (source[(r%rows)*cols+(y/cols^(r/rows)%cols)]?.getD false::answer)) =
      cfg (some (.inr (.inr (.inr (.inr .clearDigit))))) initial
        (List.replicate r true) (List.replicate rows true)
        (List.replicate (r%rows) true) (List.replicate y true)
        (List.replicate cols true)
        (List.replicate (y/cols^(r/rows)%cols) true) source
        (source[(r%rows)*cols+(y/cols^(r/rows)%cols)]?.getD false::answer) := by
    unfold lookupFrame renameCfg liftCfg lookupControl cfg
      MatrixTableLookup.cfg initial
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht.trans ha,by simpa only [hi,hf] using hr⟩

private theorem clear_digit_cons (s : Control) (r rows x y cols : List Bool)
    (d : ℕ) (source answer : List Bool) :
    advance program
      (cfg (some (.inr (.inr (.inr (.inr .clearDigit))))) s
        r rows x y cols (List.replicate (d+1) true) source answer) =
      cfg (some (.inr (.inr (.inr (.inr .clearDigit)))))
        ((s.1.1,true),s.2) r rows x y cols
        (List.replicate d true) source answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, List.replicate_succ]
  all_goals funext k; fin_cases k <;> rfl

private theorem clear_digit_zero (s : Control) (r rows x y cols : List Bool)
    (source answer : List Bool) :
    advance program
      (cfg (some (.inr (.inr (.inr (.inr .clearDigit))))) s
        r rows x y cols [] source answer) =
      cfg (some (.inr (.inr (.inr (.inr .clearRow)))))
        ((s.1.1,false),s.2) r rows x y cols [] source answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

private theorem clear_row_cons (s : Control) (r rows y cols digit : List Bool)
    (x : ℕ) (source answer : List Bool) :
    advance program
      (cfg (some (.inr (.inr (.inr (.inr .clearRow))))) s
        r rows (List.replicate (x+1) true) y cols digit source answer) =
      cfg (some (.inr (.inr (.inr (.inr .clearRow)))))
        ((s.1.1,true),s.2) r rows (List.replicate x true)
        y cols digit source answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, List.replicate_succ]
  all_goals funext k; fin_cases k <;> rfl

private theorem clear_row_zero (s : Control) (r rows y cols digit : List Bool)
    (source answer : List Bool) :
    advance program
      (cfg (some (.inr (.inr (.inr (.inr .clearRow))))) s
        r rows [] y cols digit source answer) =
      cfg none initial r rows [] y cols digit source answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, initial]

theorem clear_digit_run (d : ℕ) (s : Control)
    (r rows x y cols : List Bool) (source answer : List Bool) :
    run (d+1)
      (cfg (some (.inr (.inr (.inr (.inr .clearDigit))))) s
        r rows x y cols (List.replicate d true) source answer) =
      cfg (some (.inr (.inr (.inr (.inr .clearRow)))))
        ((s.1.1,false),s.2) r rows x y cols [] source answer := by
  induction d generalizing s with
  | zero => simpa using clear_digit_zero s r rows x y cols source answer
  | succ d ih =>
      rw [run_succ, clear_digit_cons]
      simpa only [Nat.succ_eq_add_one] using ih ((s.1.1,true),s.2)

theorem clear_row_run (x : ℕ) (s : Control)
    (r rows y cols digit : List Bool) (source answer : List Bool) :
    run (x+1)
      (cfg (some (.inr (.inr (.inr (.inr .clearRow))))) s
        r rows (List.replicate x true) y cols digit source answer) =
      cfg none initial r rows [] y cols digit source answer := by
  induction x generalizing s with
  | zero => simpa using clear_row_zero s r rows y cols digit source answer
  | succ x ih =>
      rw [run_succ, clear_row_cons]
      simpa only [Nat.succ_eq_add_one] using ih ((s.1.1,true),s.2)

def callbackBound (r rows y cols sourceLength : ℕ) : ℕ :=
  128*(r+rows+y+cols+sourceLength+1)^2

/-- The fixed entry controller computes its row-block quotient and selected
column digit on stacks, reads the literal old table, and restores all framed
inputs and scratch banks.  The bound counts all transitions. -/
theorem entry_run (r rows y cols : ℕ) (source answer : List Bool) :
    ∃ t ≤ callbackBound r rows y cols source.length,
      run t (cfg (some start) initial (List.replicate r true)
        (List.replicate rows true) [] (List.replicate y true)
        (List.replicate cols true) [] source answer) =
      cfg none initial (List.replicate r true) (List.replicate rows true)
        [] (List.replicate y true) (List.replicate cols true) [] source
        (source[(r%rows)*cols+(y/cols^(r/rows)%cols)]?.getD false::answer) := by
  obtain ⟨a,ha,h₁⟩ := row_copy_run r rows y cols source answer
  obtain ⟨b,hb,h₂⟩ := row_division_run r rows y cols source answer
  obtain ⟨c,hc,h₃⟩ := digit_stage_run r rows y cols source answer
  obtain ⟨d,hd,h₄⟩ := lookup_stage_run r rows y cols source answer
  let x := r%rows
  let z := y/cols^(r/rows)%cols
  let bit := source[x*cols+z]?.getD false
  have h₅ := clear_digit_run z initial
    (List.replicate r true) (List.replicate rows true)
    (List.replicate x true) (List.replicate y true)
    (List.replicate cols true) source (bit::answer)
  have h₆ := clear_row_run x ((none,false),
    (MatrixTableInterlaceDigit.initial,MatrixTableLookup.initial))
    (List.replicate r true) (List.replicate rows true)
    (List.replicate y true) (List.replicate cols true) [] source (bit::answer)
  have h₅₆ := (run_add h₅ (x+1)).trans h₆
  refine ⟨a+b+c+d+(z+1)+(x+1), ?_, ?_⟩
  · let S := r+rows+y+cols+source.length+1
    have hS : 1 ≤ S := by dsimp [S]; omega
    have hr : r ≤ S := by dsimp [S]; omega
    have hrows : rows ≤ S := by dsimp [S]; omega
    have hy : y ≤ S := by dsimp [S]; omega
    have hc0 : cols ≤ S := by dsimp [S]; omega
    have hsource : source.length ≤ S := by dsimp [S]; omega
    have hq : r/rows ≤ r := Nat.div_le_self _ _
    have hx : x ≤ r := Nat.mod_le _ _
    have hz : z ≤ y := (Nat.mod_le _ _).trans (Nat.div_le_self _ _)
    have hsum : x+cols+z+source.length+1 ≤ S := by dsimp [x,z,S]; omega
    have hsum2 : (r/rows+1) ≤ S := by omega
    have hsum3 : y+cols+1 ≤ S := by dsimp [S]; omega
    have hprod : (r/rows+1)*(y+cols+1) ≤ S^2 := by
      nlinarith [Nat.mul_le_mul hsum2 hsum3]
    have hsquare := Nat.pow_le_pow_left hsum 2
    have hd0 := MatrixUnaryDivision.totalTime_bound r rows
    have htime : b ≤ 8*r+3*rows+4 := hb.trans hd0
    have hS2 : S ≤ S^2 := by nlinarith [Nat.mul_le_mul (le_refl S) hS]
    dsimp [MatrixTableInterlaceDigit.callbackBound] at hc
    have ha' : a ≤ 2*S+2 := by omega
    have hb' : b ≤ 11*S+4 := by omega
    have hc' : c ≤ 2*S+2+12*S^2 := by nlinarith [hprod]
    have hd' : d ≤ 32*S^2 := hd.trans (Nat.mul_le_mul_left 32 hsquare)
    have hcleanup : z+1+(x+1) ≤ 2*S+2 := by omega
    change a+b+c+d+(z+1)+(x+1) ≤ 128*S^2
    omega
  · have h₁₂ := (run_add h₁ b).trans h₂
    have h₁₂₃ := (run_add h₁₂ c).trans h₃
    have h₁₂₃₄ := (run_add h₁₂₃ d).trans h₄
    have h := (run_add h₁₂₃₄ ((z+1)+(x+1))).trans h₅₆
    simpa only [Nat.add_assoc] using h

end EthInapproximability.CurrentPaper.MatrixTableInterlaceEntry
