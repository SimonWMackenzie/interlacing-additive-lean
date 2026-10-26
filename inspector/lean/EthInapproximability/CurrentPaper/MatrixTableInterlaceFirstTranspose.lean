import EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstFinish
import EthInapproximability.CurrentPaper.MatrixTableTranspose

/-!
# Physical transpose wrapper for the first restoration

This fixed controller extends the charged interlace/row-order machine with
explicit data transfers into a literal transposition writer.  A one-pass
move restores the table word's orientation; a two-pass copy duplicates the
unary column header before it is consumed as the output-row count.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstTranspose

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev FStack := MatrixTableInterlaceFirstRestoration.Stack
abbrev TStack := MatrixTableWriter.Stack 7
abbrev Stack := FStack ⊕ TStack
instance : DecidableEq Stack := fun a b =>
  instDecidableEqSum a b
abbrev TLabel := MatrixTableWriter.Label MatrixTableLookup.Label
abbrev TControl := MatrixTableWriter.Control MatrixTableLookup.Control

inductive Bridge where
  | word | copyScan | copyRestore | cols | rows
  deriving DecidableEq, Fintype

abbrev Label := MatrixTableInterlaceFirstRestoration.Label ⊕ (Bridge ⊕ TLabel)
abbrev Control := MatrixTableInterlaceFirstRestoration.Control ×
  (TControl × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def fWord : Stack := .inl (.inr (.inr 6))
def fCols : Stack := .inl (.inr (.inl 1))
def fRows : Stack := .inl (.inl (.inr (.inr .rows)))
def fScratch : Stack := .inl (.inr (.inr 1))
def tSource : Stack := .inr (.inl (.inl 4))
def tWidth : Stack := .inr (.inl (.inl 0))
def tRows : Stack := .inr (.inr .rows)
def tCols : Stack := .inr (.inr .cols)

def start : Label := .inl MatrixTableInterlaceFirstRestoration.start
def bridgeStart : Label := .inr (.inl .word)
def transposeStart : Label := .inr (.inr (.inr (.copy .rows)))

def transposeLabels : TLabel ⊕
    (MatrixTableInterlaceFirstRestoration.Label ⊕ Bridge) ≃ Label where
  toFun
    | .inl l => .inr (.inr l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inl l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr l)
    | .inr (.inr l) => .inl l
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def transposeControl : TControl ×
    (MatrixTableInterlaceFirstRestoration.Control × Option Bool) ≃ Control where
  toFun := fun v => (v.2.1,(v.1,v.2.2))
  invFun := fun v => (v.2.1,(v.1,v.2.2))
  left_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl
  right_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl

def move (source target : Stack) (again next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop source (fun v b => (v.1,(v.2.1,b)))
    (branch (fun v => v.2.2.isSome)
      (push target (fun v => v.2.2.getD false) (goto (fun _ => again)))
      (load (fun v => (v.1,(v.2.1,none))) (goto (fun _ => next))))

def copyScan : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  move fCols fScratch (.inr (.inl .copyScan))
    (.inr (.inl .copyRestore))

def copyRestore : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop fScratch (fun v b => (v.1,(v.2.1,b)))
    (branch (fun v => v.2.2.isSome)
      (push fCols (fun _ => true)
        (push tWidth (fun _ => true)
          (goto (fun _ => .inr (.inl .copyRestore)))))
      (load (fun v => (v.1,(v.2.1,none)))
        (goto (fun _ => .inr (.inl .cols)))))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl .word))
      (MatrixTableInterlaceFirstRestoration.program l)
  | .inr (.inl .word) => move fWord tSource (.inr (.inl .word))
      (.inr (.inl .copyScan))
  | .inr (.inl .copyScan) => copyScan
  | .inr (.inl .copyRestore) => copyRestore
  | .inr (.inl .cols) => move fCols tRows (.inr (.inl .cols))
      (.inr (.inl .rows))
  | .inr (.inl .rows) => move fRows tCols (.inr (.inl .rows))
      transposeStart
  | .inr (.inr l) => renameStmt (Equiv.sumComm TStack FStack)
      transposeLabels transposeControl
      (liftStmt none (MatrixTableWriter.program
        MatrixTableTranspose.entryProgram MatrixTableLookup.start
        MatrixTableLookup.initial l))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def firstFrame (v : TControl) (foreign : TStack → List Bool)
    (c : MatrixTableInterlaceFirstRestoration.Config) : Config :=
  liftCfg (some (.inl .word)) (v,none) foreign c

def transposeFrame (v : MatrixTableInterlaceFirstRestoration.Control)
    (foreign : FStack → List Bool)
    (c : MatrixTableWriter.Config 7 MatrixTableLookup.Label
      MatrixTableLookup.Control) : Config :=
  renameCfg (Equiv.sumComm TStack FStack)
    transposeLabels transposeControl (liftCfg none (v,none) foreign c)

def emptyTransposeBank : TStack → List Bool := fun _ => []

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem move_cons (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v : MatrixTableInterlaceFirstRestoration.Control)
    (w : TControl) (s : Option Bool) (S : Stack → List Bool)
    (b : Bool) (bits : List Bool) (hs : S source = b::bits) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some again,(v,(w,some b)),
        Function.update (Function.update S source bits)
          target (b::S target)⟩ := by
  classical
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs]
  simp [Function.update_apply, hne, Ne.symm hne]

private theorem move_nil (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (v : MatrixTableInterlaceFirstRestoration.Control)
    (w : TControl) (s : Option Bool)
    (S : Stack → List Bool) (hs : S source = []) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),S⟩ := by
  classical
  have hu : Function.update S source [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs, hu]

theorem move_run (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v : MatrixTableInterlaceFirstRestoration.Control)
    (w : TControl) (s : Option Bool)
    (bits : List Bool) (S : Stack → List Bool) (hs : S source = bits) :
    run (bits.length+1) ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),
        Function.update (Function.update S source []) target
          (bits.reverse ++ S target)⟩ := by
  classical
  induction bits generalizing S s with
  | nil =>
      have hnil := move_nil source target again next hprog v w s S hs
      have hu1 : Function.update S source [] = S :=
        Function.update_eq_self_iff.mpr hs.symm
      have hu2 : Function.update S target (S target) = S :=
        Function.update_eq_self_iff.mpr rfl
      simpa only [List.reverse_nil, List.nil_append, hu1, hu2] using hnil
  | cons b bits ih =>
      let S' := Function.update (Function.update S source bits)
        target (b::S target)
      have hs' : S' source = bits := by simp [S', hne]
      have h := run_add (move_cons source target again next hprog hne
        v w s S b bits hs) (bits.length+1)
      have h2 := h.trans (ih (some b) S' hs')
      have hupdate :
          Function.update (Function.update S' source []) target
            (bits.reverse ++ S' target) =
          Function.update (Function.update S source []) target
            (bits.reverse ++ b :: S target) := by
        funext k
        by_cases ht : k = target
        · subst k
          simp [S', Function.update_apply, hne, Ne.symm hne]
        · by_cases hsource : k = source
          · subst k
            simp [S', Function.update_apply, ht, hne, Ne.symm hne]
          · simp [S', Function.update_apply, ht, hsource]
      rw [hupdate] at h2
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2

private theorem restore_cons
    (v : MatrixTableInterlaceFirstRestoration.Control)
    (w : TControl) (s : Option Bool) (S : Stack → List Bool)
    (rest : List Bool) (hs : S fScratch = true :: rest) :
    run 1 ⟨some (.inr (.inl .copyRestore)),(v,(w,s)),S⟩ =
      ⟨some (.inr (.inl .copyRestore)),(v,(w,some true)),
        Function.update
          (Function.update (Function.update S fScratch rest)
            fCols (true :: S fCols))
          tWidth (true :: S tWidth)⟩ := by
  classical
  simp [run, advance, TM2.step, TM2.stepAux, program, copyRestore, hs]
  funext k
  by_cases hc : k = fCols
  · subst k
    simp [fCols, fScratch, tWidth]
  · by_cases ht : k = tWidth
    · subst k
      simp [fCols, fScratch, tWidth]
    · simp [Function.update_apply, hc, ht, fCols, fScratch, tWidth]

private theorem restore_nil
    (v : MatrixTableInterlaceFirstRestoration.Control)
    (w : TControl) (s : Option Bool) (S : Stack → List Bool)
    (hs : S fScratch = []) :
    run 1 ⟨some (.inr (.inl .copyRestore)),(v,(w,s)),S⟩ =
      ⟨some (.inr (.inl .cols)),(v,(w,none)),S⟩ := by
  classical
  have hu : Function.update S fScratch [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run, advance, TM2.step, TM2.stepAux, program, copyRestore, hs, hu]

theorem restore_run
    (v : MatrixTableInterlaceFirstRestoration.Control)
    (w : TControl) (s : Option Bool) (n : ℕ)
    (S : Stack → List Bool)
    (hs : S fScratch = List.replicate n true) :
    run (n+1) ⟨some (.inr (.inl .copyRestore)),(v,(w,s)),S⟩ =
      ⟨some (.inr (.inl .cols)),(v,(w,none)),
        Function.update
          (Function.update (Function.update S fScratch [])
            fCols (List.replicate n true ++ S fCols))
          tWidth (List.replicate n true ++ S tWidth)⟩ := by
  classical
  induction n generalizing S s with
  | zero =>
      have hnil := restore_nil v w s S (by simpa using hs)
      have hu1 : Function.update S fScratch [] = S :=
        Function.update_eq_self_iff.mpr (by simpa using hs.symm)
      have hu2 : Function.update S fCols (S fCols) = S :=
        Function.update_eq_self_iff.mpr rfl
      have hu3 : Function.update S tWidth (S tWidth) = S :=
        Function.update_eq_self_iff.mpr rfl
      simpa only [List.replicate_zero, List.nil_append, hu1, hu2, hu3]
        using hnil
  | succ n ih =>
      let S' := Function.update
        (Function.update (Function.update S fScratch
          (List.replicate n true))
          fCols (true :: S fCols))
        tWidth (true :: S tWidth)
      have hs' : S' fScratch = List.replicate n true := by
        simp [S',fScratch,fCols,tWidth]
      have h1 := restore_cons v w s S (List.replicate n true) hs
      have h2 := (run_add h1 (n+1)).trans (ih (some true) S' hs')
      have hupdate :
          Function.update
            (Function.update (Function.update S' fScratch [])
              fCols (List.replicate n true ++ S' fCols))
            tWidth (List.replicate n true ++ S' tWidth) =
          Function.update
            (Function.update (Function.update S fScratch [])
              fCols (List.replicate (n+1) true ++ S fCols))
            tWidth (List.replicate (n+1) true ++ S tWidth) := by
        funext k
        by_cases hwidth : k = tWidth
        · subst k
          simp [S',fScratch,fCols,tWidth,List.replicate_add,
            List.append_assoc]
        · by_cases hcols : k = fCols
          · subst k
            simp [S',fScratch,fCols,tWidth,hwidth,
              List.replicate_add,List.append_assoc]
          · by_cases hscratch : k = fScratch
            · subst k
              simp [S',fScratch,fCols,tWidth,hwidth,hcols]
            · simp [S',Function.update_apply,hwidth,hcols,hscratch]
      rw [hupdate] at h2
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h2

def sourceBank (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) : Stack → List Bool :=
  (firstFrame (MatrixTableLookup.initial,none) emptyTransposeBank
    (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v)).stk

theorem sourceBank_word (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v fWord =
      (MatrixTableInterlaceFirstFinish.word blocks rows cols f).reverse := by
  exact MatrixTableInterlaceFirstFinish.finalOut_reversed_word blocks rows cols f v

theorem sourceBank_rows (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v fRows =
      List.replicate (blocks*rows) true := by
  exact MatrixTableInterlaceFirstFinish.finalOut_rowCount blocks rows cols f v

theorem sourceBank_cols (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v fCols =
      List.replicate (cols^blocks) true := by
  exact MatrixTableInterlaceFirstFinish.finalOut_colCount blocks rows cols f v

theorem sourceBank_scratch (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v fScratch = [] := by
  rfl

theorem sourceBank_foreign (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) (k : TStack) :
    sourceBank blocks rows cols f v (.inr k) = [] := by
  rfl

def moved (S : Stack → List Bool) (source target : Stack) :
    Stack → List Bool :=
  Function.update (Function.update S source []) target
    ((S source).reverse ++ S target)

def restored (S : Stack → List Bool) (n : ℕ) : Stack → List Bool :=
  Function.update
    (Function.update (Function.update S fScratch [])
      fCols (List.replicate n true ++ S fCols))
    tWidth (List.replicate n true ++ S tWidth)

def bridgeBank (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) : Stack → List Bool :=
  let S := sourceBank blocks rows cols f v
  let S1 := moved S fWord tSource
  let S2 := moved S1 fCols fScratch
  let S3 := restored S2 (cols^blocks)
  let S4 := moved S3 fCols tRows
  moved S4 fRows tCols

def bridgeTime (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  ((MatrixTableInterlaceFirstFinish.word blocks rows cols f).length+1) +
    ((cols^blocks)+1) + ((cols^blocks)+1) +
    ((cols^blocks)+1) + ((blocks*rows)+1)

theorem bridge_run (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    run (bridgeTime blocks rows cols f)
      ⟨some bridgeStart,
        ((MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var,
          ((MatrixTableLookup.initial,none),none)),
        sourceBank blocks rows cols f v⟩ =
      ⟨some transposeStart,
        ((MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var,
          ((MatrixTableLookup.initial,none),none)),
        bridgeBank blocks rows cols f v⟩ := by
  let S := sourceBank blocks rows cols f v
  let S1 := moved S fWord tSource
  let S2 := moved S1 fCols fScratch
  let S3 := restored S2 (cols^blocks)
  let S4 := moved S3 fCols tRows
  let vc := (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var
  have hword : S fWord =
      (MatrixTableInterlaceFirstFinish.word blocks rows cols f).reverse :=
    sourceBank_word blocks rows cols f v
  have hcols : S fCols = List.replicate (cols^blocks) true :=
    sourceBank_cols blocks rows cols f v
  have hrows : S fRows = List.replicate (blocks*rows) true :=
    sourceBank_rows blocks rows cols f v
  have hscratch : S fScratch = [] :=
    sourceBank_scratch blocks rows cols f v
  have hcols1 : S1 fCols = List.replicate (cols^blocks) true := by
    calc S1 fCols = S fCols := by simp [S1,moved,fWord,tSource,fCols]
      _ = _ := hcols
  have hscratch1 : S1 fScratch = [] := by
    calc S1 fScratch = S fScratch := by simp [S1,moved,fWord,tSource,fScratch]
      _ = [] := hscratch
  have hscratch2 : S2 fScratch = List.replicate (cols^blocks) true := by
    calc
      S2 fScratch = (S1 fCols).reverse ++ S1 fScratch := by
        simp [S2,moved,fCols,fScratch]
      _ = _ := by simp [hcols1,hscratch1]
  have hcols3 : S3 fCols = List.replicate (cols^blocks) true := by
    simp [S3,restored,S2,moved,fCols,fScratch,tWidth,hcols1]
  have hrows4 : S4 fRows = List.replicate (blocks*rows) true := by
    calc
      S4 fRows = S fRows := by
        simp [S4,S3,S2,S1,restored,moved,
          fWord,tSource,fCols,fScratch,tWidth,tRows,fRows]
      _ = _ := hrows
  have h1raw := move_run fWord tSource (.inr (.inl .word))
    (.inr (.inl .copyScan)) rfl (by decide) vc
    (MatrixTableLookup.initial,none) none
    (MatrixTableInterlaceFirstFinish.word blocks rows cols f).reverse
    S hword
  have h1 : run ((MatrixTableInterlaceFirstFinish.word blocks rows cols f).length+1)
      ⟨some bridgeStart,(vc,((MatrixTableLookup.initial,none),none)),S⟩ =
      ⟨some (.inr (.inl .copyScan)),
        (vc,((MatrixTableLookup.initial,none),none)),S1⟩ := by
    simpa [bridgeStart,S1,moved,hword] using h1raw
  have h2raw := move_run fCols fScratch (.inr (.inl .copyScan))
    (.inr (.inl .copyRestore)) rfl (by decide) vc
    (MatrixTableLookup.initial,none) none
    (List.replicate (cols^blocks) true) S1 hcols1
  have h2 : run ((cols^blocks)+1)
      ⟨some (.inr (.inl .copyScan)),
        (vc,((MatrixTableLookup.initial,none),none)),S1⟩ =
      ⟨some (.inr (.inl .copyRestore)),
        (vc,((MatrixTableLookup.initial,none),none)),S2⟩ := by
    simpa [S2,moved,hcols1] using h2raw
  have h3raw := restore_run vc (MatrixTableLookup.initial,none) none
    (cols^blocks) S2 hscratch2
  have h3 : run ((cols^blocks)+1)
      ⟨some (.inr (.inl .copyRestore)),
        (vc,((MatrixTableLookup.initial,none),none)),S2⟩ =
      ⟨some (.inr (.inl .cols)),
        (vc,((MatrixTableLookup.initial,none),none)),S3⟩ := by
    simpa [S3,restored] using h3raw
  have h4raw := move_run fCols tRows (.inr (.inl .cols))
    (.inr (.inl .rows)) rfl (by decide) vc
    (MatrixTableLookup.initial,none) none
    (List.replicate (cols^blocks) true) S3 hcols3
  have h4 : run ((cols^blocks)+1)
      ⟨some (.inr (.inl .cols)),
        (vc,((MatrixTableLookup.initial,none),none)),S3⟩ =
      ⟨some (.inr (.inl .rows)),
        (vc,((MatrixTableLookup.initial,none),none)),S4⟩ := by
    simpa [S4,moved,hcols3] using h4raw
  have h5raw := move_run fRows tCols (.inr (.inl .rows))
    transposeStart rfl (by decide) vc
    (MatrixTableLookup.initial,none) none
    (List.replicate (blocks*rows) true) S4 hrows4
  have h5 : run ((blocks*rows)+1)
      ⟨some (.inr (.inl .rows)),
        (vc,((MatrixTableLookup.initial,none),none)),S4⟩ =
      ⟨some transposeStart,
        (vc,((MatrixTableLookup.initial,none),none)),
        moved S4 fRows tCols⟩ := by
    simpa [moved,hrows4] using h5raw
  have h12 := run_add h1 ((cols^blocks)+1)
  rw [h2] at h12
  have h123 := run_add h12 ((cols^blocks)+1)
  rw [h3] at h123
  have h1234 := run_add h123 ((cols^blocks)+1)
  rw [h4] at h1234
  have h12345 := run_add h1234 ((blocks*rows)+1)
  rw [h5] at h12345
  simpa only [bridgeTime,bridgeBank,S,S1,S2,S3,S4,
    Nat.add_assoc] using h12345

def transposeData (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableWriter.Data 7 :=
  MatrixTableWriter.ready
    (MatrixTableTranspose.persistentBank (cols^blocks)
      (MatrixTableInterlaceFirstFinish.word blocks rows cols f))
    (cols^blocks) (blocks*rows) 0 0 0 0 [] []

theorem bridgeBank_transpose (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (fun k : TStack => bridgeBank blocks rows cols f v (.inr k)) =
      (transposeData blocks rows cols f).contents := by
  funext k
  have hw := sourceBank_word blocks rows cols f v
  have hc := sourceBank_cols blocks rows cols f v
  have hr := sourceBank_rows blocks rows cols f v
  have hs := sourceBank_scratch blocks rows cols f v
  have ht (j : TStack) := sourceBank_foreign blocks rows cols f v j
  cases k with
  | inl j =>
      cases j with
      | inl i =>
          fin_cases i <;>
            simp [bridgeBank,transposeData,MatrixTableWriter.ready,
              MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,
              MatrixTableTranspose.persistentBank,restored,moved,
              fWord,fCols,fRows,fScratch,tSource,tWidth,tRows,tCols,
              hw,hc,hr,hs,ht] <;>
            (rw [show sourceBank blocks rows cols f v
                (.inl (.inr (.inr 6))) =
                  (MatrixTableInterlaceFirstFinish.word blocks rows cols f).reverse
              from hw]; simp)
      | inr i =>
          fin_cases i <;>
            simp [bridgeBank,transposeData,MatrixTableWriter.ready,
              MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,
              MatrixTableTranspose.persistentBank,restored,moved,
              fWord,fCols,fRows,fScratch,tSource,tWidth,tRows,tCols,
              hw,hc,hr,hs,ht]
  | inr j =>
      cases j <;>
        simp [bridgeBank,transposeData,MatrixTableWriter.ready,
          MatrixTableWriter.Data.contents,MatrixTableWriter.Data.foreign,
          restored,moved,fWord,fCols,fRows,fScratch,tSource,tWidth,
          tRows,tCols,hw,hc,hr,hs,ht]
      all_goals
        rw [show sourceBank blocks rows cols f v
          (.inl (.inl (.inr (.inr MatrixTableWriter.Extra.rows)))) =
            List.replicate (blocks*rows) true from hr]
        simp

theorem bridgeEnd_transposeFrame (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (⟨some transposeStart,
      ((MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var,
        ((MatrixTableLookup.initial,none),none)),
      bridgeBank blocks rows cols f v⟩ : Config) =
    transposeFrame
      (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var
      (fun k => bridgeBank blocks rows cols f v (.inl k))
      (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
        (MatrixTableLookup.initial,none)
        (transposeData blocks rows cols f)) := by
  have h := bridgeBank_transpose blocks rows cols f v
  congr 1
  funext k
  cases k with
  | inl k => simp [transposeFrame, renameCfg, liftCfg]
  | inr k => simpa [transposeFrame, renameCfg, liftCfg] using congrFun h k

theorem first_phase (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks)) :
    ∃ t ≤ MatrixTableInterlaceFirstFinish.numberedBound blocks rows cols f +
      (MatrixTableInterlaceFirstFinish.word blocks rows cols f).length+2,
      ∃ v : MatrixTableInterlaceCombined.WControl,
        run t (firstFrame (MatrixTableLookup.initial,none)
          emptyTransposeBank
          (MatrixTableInterlaceFirstRestoration.combinedFrame
            (false,(none,SamplerMachineBlockReverse.initial))
            MatrixTableInterlaceFirstRestoration.emptyRowBank
            (MatrixTableInterlaceCombined.bridgeCfg
              MatrixTableInterlaceCombined.start blocks rows cols
              (MatrixMaterialization.rowMajor f) [] [] [] [] []))) =
        firstFrame (MatrixTableLookup.initial,none) emptyTransposeBank
          (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v) := by
  obtain ⟨t,ht,v,he⟩ :=
    MatrixTableInterlaceFirstFinish.first_interlace_halted_run
      blocks rows cols f hwidth
  have hh : (MatrixTableInterlaceFirstRestoration.run t
      (MatrixTableInterlaceFirstRestoration.combinedFrame
        (false,(none,SamplerMachineBlockReverse.initial))
        MatrixTableInterlaceFirstRestoration.emptyRowBank
        (MatrixTableInterlaceCombined.bridgeCfg
          MatrixTableInterlaceCombined.start blocks rows cols
          (MatrixMaterialization.rowMajor f) [] [] [] [] []))).l = none := by
    rw [he]
    exact MatrixTableInterlaceFirstFinish.finalOut_halts blocks rows cols f v
  obtain ⟨u,hu,hr⟩ := lift_outputs
    MatrixTableInterlaceFirstRestoration.program program
    (some (.inl .word)) (fun _ => rfl)
    ((MatrixTableLookup.initial,none),none) emptyTransposeBank
    (MatrixTableInterlaceFirstRestoration.combinedFrame
      (false,(none,SamplerMachineBlockReverse.initial))
      MatrixTableInterlaceFirstRestoration.emptyRowBank
      (MatrixTableInterlaceCombined.bridgeCfg
        MatrixTableInterlaceCombined.start blocks rows cols
        (MatrixMaterialization.rowMajor f) [] [] [] [] [])) t hh
  change run u (firstFrame _ _ _) =
    firstFrame _ _ (MatrixTableInterlaceFirstRestoration.run t _) at hr
  rw [he] at hr
  exact ⟨u,hu.trans ht,v,hr⟩

def transposeEnd (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : TControl) :
    MatrixTableWriter.Config 7 MatrixTableLookup.Label
      MatrixTableLookup.Control :=
  MatrixTableWriter.cfg none v
    (MatrixTableWriter.ready
      (MatrixTableTranspose.persistentBank (cols^blocks)
        (MatrixTableInterlaceFirstFinish.word blocks rows cols f))
      (cols^blocks) (blocks*rows) 0 0 0 0 []
      (MatrixMaterialization.rowMajor
        (fun c r => MatrixTableInterlaceRowReverse.numberedInterlace
          blocks rows cols f r c)))

theorem transpose_phase (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    ∃ t ≤ MatrixTableWriter.writerBound (cols^blocks) (blocks*rows)
      (MatrixTableTranspose.callbackBound (blocks*rows) (cols^blocks)
        (MatrixTableInterlaceFirstFinish.word blocks rows cols f).length),
      ∃ w : TControl,
        run t (transposeFrame
          (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var
          (fun k => bridgeBank blocks rows cols f v (.inl k))
          (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
            (MatrixTableLookup.initial,none)
            (transposeData blocks rows cols f))) =
        transposeFrame
          (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var
          (fun k => bridgeBank blocks rows cols f v (.inl k))
          (transposeEnd blocks rows cols f w) := by
  obtain ⟨t,ht,w,he⟩ := MatrixTableTranspose.transpose_rowMajor
    (blocks*rows) (cols^blocks)
    (MatrixTableInterlaceRowReverse.numberedInterlace blocks rows cols f) []
  have hhe : MatrixTableWriter.run MatrixTableTranspose.entryProgram
      MatrixTableLookup.start MatrixTableLookup.initial t
      (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
        (MatrixTableLookup.initial,none)
        (transposeData blocks rows cols f)) =
      transposeEnd blocks rows cols f w := by
    simpa only [transposeData,transposeEnd,
      MatrixTableInterlaceFirstFinish.word,List.append_nil] using he
  have hh : (MatrixTableWriter.run MatrixTableTranspose.entryProgram
      MatrixTableLookup.start MatrixTableLookup.initial t
      (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
        (MatrixTableLookup.initial,none)
        (transposeData blocks rows cols f))).l = none := by
    rw [hhe]
    rfl
  obtain ⟨u,hu,hr⟩ := lift_outputs_renamed
    (Equiv.sumComm TStack FStack) transposeLabels transposeControl
    (MatrixTableWriter.program MatrixTableTranspose.entryProgram
      MatrixTableLookup.start MatrixTableLookup.initial)
    program none (fun _ => rfl)
    ((MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var,none)
    (fun k => bridgeBank blocks rows cols f v (.inl k))
    (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
      (MatrixTableLookup.initial,none)
      (transposeData blocks rows cols f)) t hh
  change run u (transposeFrame _ _ _) =
    transposeFrame _ _
      (MatrixTableWriter.run MatrixTableTranspose.entryProgram
        MatrixTableLookup.start MatrixTableLookup.initial t _) at hr
  rw [hhe] at hr
  refine ⟨u,hu.trans ht,w,?_⟩
  exact hr

def totalBound (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  (MatrixTableInterlaceFirstFinish.numberedBound blocks rows cols f +
    (MatrixTableInterlaceFirstFinish.word blocks rows cols f).length+2) +
    bridgeTime blocks rows cols f +
    MatrixTableWriter.writerBound (cols^blocks) (blocks*rows)
      (MatrixTableTranspose.callbackBound (blocks*rows) (cols^blocks)
        (MatrixTableInterlaceFirstFinish.word blocks rows cols f).length)

theorem first_transpose_run (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks)) :
    ∃ t ≤ totalBound blocks rows cols f,
      ∃ v : MatrixTableInterlaceCombined.WControl,
      ∃ w : TControl,
        run t (firstFrame (MatrixTableLookup.initial,none)
          emptyTransposeBank
          (MatrixTableInterlaceFirstRestoration.combinedFrame
            (false,(none,SamplerMachineBlockReverse.initial))
            MatrixTableInterlaceFirstRestoration.emptyRowBank
            (MatrixTableInterlaceCombined.bridgeCfg
              MatrixTableInterlaceCombined.start blocks rows cols
              (MatrixMaterialization.rowMajor f) [] [] [] [] []))) =
        transposeFrame
          (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var
          (fun k => bridgeBank blocks rows cols f v (.inl k))
          (transposeEnd blocks rows cols f w) := by
  obtain ⟨t₁,ht₁,v,h₁⟩ := first_phase blocks rows cols f hwidth
  rw [show firstFrame (MatrixTableLookup.initial,none)
      emptyTransposeBank
      (MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v) =
    (⟨some bridgeStart,
      ((MatrixTableInterlaceFirstFinish.finalOut blocks rows cols f v).var,
        ((MatrixTableLookup.initial,none),none)),
      sourceBank blocks rows cols f v⟩ : Config) from rfl] at h₁
  have h₂ := bridge_run blocks rows cols f v
  rw [bridgeEnd_transposeFrame] at h₂
  obtain ⟨t₃,ht₃,w,h₃⟩ := transpose_phase blocks rows cols f v
  have h₁₂ := run_add h₁ (bridgeTime blocks rows cols f)
  rw [h₂] at h₁₂
  have h₁₂₃ := run_add h₁₂ t₃
  rw [h₃] at h₁₂₃
  refine ⟨t₁+bridgeTime blocks rows cols f+t₃, ?_,v,w,?_⟩
  · dsimp [totalBound]
    omega
  · exact h₁₂₃

theorem transposeEnd_numberedRestoration (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) (w : TControl) :
    (transposeEnd (2^r) rows cols f w).stk (.inr .output) =
      MatrixMaterialization.rowMajor
        (MatrixTableInterlaceRowReverse.numberedRestoration r rows cols f) := by
  rw [MatrixTableInterlaceRowReverse.numberedRestoration_eq]
  rfl

set_option maxHeartbeats 1000000 in
theorem totalBound_polynomial (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    totalBound blocks rows cols f ≤
      2048 * (blocks+rows+cols+
        (MatrixMaterialization.rowMajor f).length+
        blocks*rows+cols^blocks+
        (MatrixTableInterlaceFirstFinish.word blocks rows cols f).length+1)^4 := by
  let R := blocks*rows
  let C := cols^blocks
  let L := (MatrixTableInterlaceFirstFinish.word blocks rows cols f).length
  let N := blocks+rows+cols+
    (MatrixMaterialization.rowMajor f).length+R+C+L+1
  have hlen : L = R*C := by
    dsimp [L,R,C,MatrixTableInterlaceFirstFinish.word]
    simp
  have hlen' : (MatrixMaterialization.rowMajor
      (MatrixTableInterlace.interlaced (blocks := blocks) f)).length = L := by
    rw [MatrixMaterialization.rowMajor_length, hlen]
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hN2 : N ≤ N^2 := by
    nlinarith [Nat.mul_le_mul (le_refl N) hN]
  have hN4 : N^2 ≤ N^4 := by
    have h : 1 ≤ N^2 := by nlinarith
    nlinarith [Nat.mul_le_mul (le_refl (N^2)) h]
  have hNto4 : N ≤ N^4 := by omega
  have hcombinedSmall :
      blocks+rows+cols+(MatrixMaterialization.rowMajor f).length+R+C+1 ≤ N := by
    dsimp [N]; omega
  have hrowSmall : blocks+rows+C+L+1 ≤ N := by
    dsimp [N]; omega
  have htransposeSmall : R+C+L+1 ≤ N := by
    dsimp [N]; omega
  have hc := MatrixTableInterlaceCombined.totalBound_polynomial
    blocks rows cols (MatrixMaterialization.rowMajor f).length
  have hc' : MatrixTableInterlaceCombined.totalBound blocks rows cols
      (MatrixMaterialization.rowMajor f).length ≤ 1024*N^4 := by
    exact hc.trans (Nat.mul_le_mul_left 1024
      (Nat.pow_le_pow_left hcombinedSmall 4))
  have hr := MatrixTableInterlaceRowWidth.width_bridge_bound_polynomial
    blocks rows C
  have hr' : MatrixAddressMachine.exactTime rows C 0 +
      (2*L+2 + blocks*SamplerMachineBlockReverse.blockStep (rows*C)) ≤
      11*N^2 := by
    rw [hlen]
    have hrowSmall' : blocks+rows+C+R*C+1 ≤ N := by
      simpa only [hlen] using hrowSmall
    exact hr.trans (Nat.mul_le_mul_left 11
      (Nat.pow_le_pow_left hrowSmall' 2))
  have ht := MatrixTableTranspose.transpose_bound_polynomial R C L
  have ht' : MatrixTableWriter.writerBound C R
      (MatrixTableTranspose.callbackBound R C L) ≤ 256*N^4 := by
    exact ht.trans (Nat.mul_le_mul_left 256
      (Nat.pow_le_pow_left htransposeSmall 4))
  change totalBound blocks rows cols f ≤ 2048*N^4
  dsimp [totalBound,MatrixTableInterlaceFirstFinish.numberedBound,
    bridgeTime]
  rw [hlen']
  change MatrixTableInterlaceCombined.totalBound blocks rows cols
      (MatrixMaterialization.rowMajor f).length +
    ((rows+1)+(C+1)+(L+1)+(L+1)) +
    (MatrixAddressMachine.exactTime rows C 0 +
      (2*L+2+blocks*SamplerMachineBlockReverse.blockStep (rows*C))) +
    L+2 + ((L+1)+(C+1)+(C+1)+(C+1)+(R+1)) +
    MatrixTableWriter.writerBound C R
      (MatrixTableTranspose.callbackBound R C L) ≤ 2048*N^4
  have hsmall : rows+R+C+L+1 ≤ N := by dsimp [N]; omega
  omega

/-- One fixed controller physically writes the exact numeric first
restoration table.  The initial bank still requires the explicit duplicate
unary headers specified by `MatrixTableInterlaceCombined.bridgeCfg`; this
theorem charges every transfer after that prepared input. -/
theorem first_restoration_run (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^(2^r))) :
    ∃ t ≤ 2048 * ((2^r)+rows+cols+
      (MatrixMaterialization.rowMajor f).length+
      (2^r)*rows+cols^(2^r)+
      (MatrixTableInterlaceFirstFinish.word (2^r) rows cols f).length+1)^4,
      ∃ c : Config,
        run t (firstFrame (MatrixTableLookup.initial,none)
          emptyTransposeBank
          (MatrixTableInterlaceFirstRestoration.combinedFrame
            (false,(none,SamplerMachineBlockReverse.initial))
            MatrixTableInterlaceFirstRestoration.emptyRowBank
            (MatrixTableInterlaceCombined.bridgeCfg
              MatrixTableInterlaceCombined.start (2^r) rows cols
              (MatrixMaterialization.rowMajor f) [] [] [] [] []))) = c ∧
        c.l = none ∧
        c.stk (.inr (.inr .output)) =
          MatrixMaterialization.rowMajor
            (MatrixTableInterlaceRowReverse.numberedRestoration
              r rows cols f) := by
  obtain ⟨t,ht,v,w,he⟩ := first_transpose_run (2^r) rows cols f hwidth
  let c := transposeFrame
    (MatrixTableInterlaceFirstFinish.finalOut (2^r) rows cols f v).var
    (fun k => bridgeBank (2^r) rows cols f v (.inl k))
    (transposeEnd (2^r) rows cols f w)
  refine ⟨t,ht.trans (totalBound_polynomial (2^r) rows cols f),c,he,?_,?_⟩
  · rfl
  · change (transposeEnd (2^r) rows cols f w).stk (.inr .output) = _
    exact transposeEnd_numberedRestoration r rows cols f w

end EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstTranspose
