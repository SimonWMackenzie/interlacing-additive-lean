import EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstTranspose
import EthInapproximability.CurrentPaper.MatrixTableInterlaceLevelCodes

/-!
# Physical double-restoration join

One fixed Boolean-stack controller runs the first literal restoration,
physically constructs the second controller's duplicated row/column headers
and row-major source word, then runs the second literal restoration.  A
separate unary stack supplies the second interlace block count; its
computation belongs to the parameter producer, not this join.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceDouble

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev OneStack := MatrixTableInterlaceFirstTranspose.Stack
abbrev Stack := OneStack ⊕ (OneStack ⊕ Fin 1)
abbrev OneLabel := MatrixTableInterlaceFirstTranspose.Label
abbrev OneControl := MatrixTableInterlaceFirstTranspose.Control

inductive Bridge where
  | wordTemp | wordTarget | rows | cols | blocks
  deriving DecidableEq, Fintype

abbrev Label := OneLabel ⊕ (Bridge ⊕ OneLabel)
abbrev Control := OneControl × (OneControl × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

instance : DecidableEq Stack := fun a b => instDecidableEqSum a b

def firstWord : Stack := .inl (.inr (.inr .output))
def firstRows : Stack := .inl (.inr (.inr .rows))
def firstCols : Stack := .inl (.inr (.inr .cols))
def wordTemp : Stack := .inl (.inr (.inr .buffer))
def blockInput : Stack := .inr (.inr 0)

def secondBlock : Stack := .inr (.inl (.inl (.inl (.inl 0))))
def secondSizeRows : Stack := .inr (.inl (.inl (.inl (.inl 1))))
def secondSizeCols : Stack := .inr (.inl (.inl (.inl (.inl 2))))
def secondWriterRows : Stack :=
  .inr (.inl (.inl (.inl (.inr (.inl (.inl 0))))))
def secondWriterCols : Stack :=
  .inr (.inl (.inl (.inl (.inr (.inl (.inl 7))))))
def secondWriterSource : Stack :=
  .inr (.inl (.inl (.inl (.inr (.inl (.inl 17))))))

def start : Label := .inl MatrixTableInterlaceFirstTranspose.start
def bridgeStart : Label := .inr (.inl .wordTemp)
def secondStart : Label := .inr (.inr MatrixTableInterlaceFirstTranspose.start)

def secondLabels : OneLabel ⊕ (OneLabel ⊕ Bridge) ≃ Label where
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

def secondSlots : OneStack ⊕ (OneStack ⊕ Fin 1) ≃ Stack where
  toFun
    | .inl k => .inr (.inl k)
    | .inr (.inl k) => .inl k
    | .inr (.inr k) => .inr (.inr k)
  invFun
    | .inl k => .inr (.inl k)
    | .inr (.inl k) => .inl k
    | .inr (.inr k) => .inr (.inr k)
  left_inv k := by rcases k with k | (k | k) <;> rfl
  right_inv k := by rcases k with k | (k | k) <;> rfl

def secondControl : OneControl × (OneControl × Option Bool) ≃ Control where
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

def duplicate (source target1 target2 : Stack) (again next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop source (fun v b => (v.1,(v.2.1,b)))
    (branch (fun v => v.2.2.isSome)
      (push target1 (fun _ => true)
        (push target2 (fun _ => true) (goto (fun _ => again))))
      (load (fun v => (v.1,(v.2.1,none))) (goto (fun _ => next))))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl .wordTemp))
      (MatrixTableInterlaceFirstTranspose.program l)
  | .inr (.inl .wordTemp) => move firstWord wordTemp
      (.inr (.inl .wordTemp)) (.inr (.inl .wordTarget))
  | .inr (.inl .wordTarget) => move wordTemp secondWriterSource
      (.inr (.inl .wordTarget)) (.inr (.inl .rows))
  | .inr (.inl .rows) => duplicate firstRows secondSizeRows secondWriterRows
      (.inr (.inl .rows)) (.inr (.inl .cols))
  | .inr (.inl .cols) => duplicate firstCols secondSizeCols secondWriterCols
      (.inr (.inl .cols)) (.inr (.inl .blocks))
  | .inr (.inl .blocks) => move blockInput secondBlock
      (.inr (.inl .blocks)) secondStart
  | .inr (.inr l) => renameStmt secondSlots secondLabels secondControl
      (liftStmt none (MatrixTableInterlaceFirstTranspose.program l))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def firstFrame (v : OneControl) (foreign : OneStack ⊕ Fin 1 → List Bool)
    (c : MatrixTableInterlaceFirstTranspose.Config) : Config :=
  liftCfg (some (.inl .wordTemp)) (v,none) foreign c

def secondFrame (v : OneControl)
    (foreign : OneStack ⊕ Fin 1 → List Bool)
    (c : MatrixTableInterlaceFirstTranspose.Config) : Config :=
  renameCfg secondSlots secondLabels secondControl
    (liftCfg none (v,none) foreign c)

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem move_cons (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v w : OneControl) (s : Option Bool) (S : Stack → List Bool)
    (b : Bool) (bits : List Bool) (hs : S source = b::bits) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some again,(v,(w,some b)),
        Function.update (Function.update S source bits)
          target (b::S target)⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs]
  simp [Function.update_apply, hne, Ne.symm hne]

private theorem move_nil (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (v w : OneControl) (s : Option Bool)
    (S : Stack → List Bool) (hs : S source = []) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),S⟩ := by
  have hu : Function.update S source [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs, hu]

theorem move_run (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v w : OneControl) (s : Option Bool)
    (bits : List Bool) (S : Stack → List Bool) (hs : S source = bits) :
    run (bits.length+1) ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),
        Function.update (Function.update S source []) target
          (bits.reverse ++ S target)⟩ := by
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

def moved (S : Stack → List Bool) (source target : Stack) :
    Stack → List Bool :=
  Function.update (Function.update S source []) target
    ((S source).reverse ++ S target)

def duplicated (S : Stack → List Bool)
    (source target1 target2 : Stack) (n : ℕ) :
    Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update S source [])
      target1 (List.replicate n true ++ S target1))
    target2 (List.replicate n true ++ S target2)

private theorem duplicate_cons (source target1 target2 : Stack)
    (again next : Label)
    (hprog : program again = duplicate source target1 target2 again next)
    (h₁ : source ≠ target1) (h₂ : source ≠ target2)
    (h₃ : target1 ≠ target2)
    (v w : OneControl) (s : Option Bool)
    (S : Stack → List Bool) (n : ℕ)
    (hs : S source = true :: List.replicate n true) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some again,(v,(w,some true)),
        Function.update
          (Function.update
            (Function.update S source (List.replicate n true))
            target1 (true :: S target1))
          target2 (true :: S target2)⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux,
    hprog, duplicate, hs]
  funext k
  by_cases ht₂ : k = target2
  · subst k
    simp [Function.update_apply,h₁,h₂,h₃,
      Ne.symm h₁,Ne.symm h₂,Ne.symm h₃]
  · by_cases ht₁ : k = target1
    · subst k
      simp [Function.update_apply,h₁,h₂,h₃,
        Ne.symm h₁,Ne.symm h₂,Ne.symm h₃,ht₂]
    · simp [Function.update_apply,h₁,h₂,h₃,
        Ne.symm h₁,Ne.symm h₂,Ne.symm h₃,ht₁,ht₂]

private theorem duplicate_nil (source target1 target2 : Stack)
    (again next : Label)
    (hprog : program again = duplicate source target1 target2 again next)
    (v w : OneControl) (s : Option Bool)
    (S : Stack → List Bool) (hs : S source = []) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),S⟩ := by
  have hu : Function.update S source [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run, advance, TM2.step, TM2.stepAux,
    hprog, duplicate, hs, hu]

theorem duplicate_run (source target1 target2 : Stack)
    (again next : Label)
    (hprog : program again = duplicate source target1 target2 again next)
    (h₁ : source ≠ target1) (h₂ : source ≠ target2)
    (h₃ : target1 ≠ target2)
    (v w : OneControl) (s : Option Bool) (n : ℕ)
    (S : Stack → List Bool)
    (hs : S source = List.replicate n true) :
    run (n+1) ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),duplicated S source target1 target2 n⟩ := by
  induction n generalizing S s with
  | zero =>
      have hnil := duplicate_nil source target1 target2 again next
        hprog v w s S (by simpa using hs)
      have hu1 : Function.update S source [] = S :=
        Function.update_eq_self_iff.mpr (by simpa using hs.symm)
      have hu2 : Function.update S target1 (S target1) = S :=
        Function.update_eq_self_iff.mpr rfl
      have hu3 : Function.update S target2 (S target2) = S :=
        Function.update_eq_self_iff.mpr rfl
      simpa only [duplicated,List.replicate_zero,List.nil_append,
        hu1,hu2,hu3] using hnil
  | succ n ih =>
      let S' := Function.update
        (Function.update
          (Function.update S source (List.replicate n true))
          target1 (true :: S target1))
        target2 (true :: S target2)
      have hs' : S' source = List.replicate n true := by
        simp [S',h₁,h₂]
      have h1 := duplicate_cons source target1 target2 again next
        hprog h₁ h₂ h₃ v w s S n hs
      have h2 := (run_add h1 (n+1)).trans (ih (some true) S' hs')
      have hupdate : duplicated S' source target1 target2 n =
          duplicated S source target1 target2 (n+1) := by
        funext k
        by_cases ht₂ : k = target2
        · subst k
          simp [duplicated,S',h₁,h₂,h₃,List.replicate_add,
            List.append_assoc]
        · by_cases ht₁ : k = target1
          · subst k
            simp [duplicated,S',h₁,h₂,h₃,ht₂,
              List.replicate_add,List.append_assoc]
          · by_cases hsrc : k = source
            · subst k
              simp [duplicated,S',h₁,h₂,h₃,ht₂,ht₁]
            · simp [duplicated,S',Function.update_apply,
                ht₂,ht₁,hsrc]
      rw [hupdate] at h2
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using h2

def firstRowsCount (r rows : ℕ) : ℕ := (2^r)*rows
def firstColsCount (r cols : ℕ) : ℕ := cols^(2^r)

def firstResult (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    Fin (firstColsCount r cols) → Fin (firstRowsCount r rows) → Bool :=
  MatrixTableInterlaceRowReverse.numberedRestoration r rows cols f

def firstEnd (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    MatrixTableInterlaceFirstTranspose.Config :=
  MatrixTableInterlaceFirstTranspose.transposeFrame
    (MatrixTableInterlaceFirstFinish.finalOut (2^r) rows cols f v).var
    (fun k => MatrixTableInterlaceFirstTranspose.bridgeBank
      (2^r) rows cols f v (.inl k))
    (MatrixTableInterlaceFirstTranspose.transposeEnd (2^r) rows cols f w)

def secondPrepared (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    MatrixTableInterlaceFirstTranspose.Config :=
  MatrixTableInterlaceFirstTranspose.firstFrame
    (MatrixTableLookup.initial,none)
    MatrixTableInterlaceFirstTranspose.emptyTransposeBank
    (MatrixTableInterlaceFirstRestoration.combinedFrame
      (false,(none,SamplerMachineBlockReverse.initial))
      MatrixTableInterlaceFirstRestoration.emptyRowBank
      (MatrixTableInterlaceCombined.bridgeCfg
        MatrixTableInterlaceCombined.start B
        (firstColsCount r cols) (firstRowsCount r rows)
        (MatrixMaterialization.rowMajor (firstResult r rows cols f))
        [] [] [] [] []))

def firstEndBank (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    Stack → List Bool :=
  (firstFrame (secondPrepared B r rows cols f).var
    (Sum.elim (fun _ : OneStack => [])
      (![List.replicate B true] : Fin 1 → List Bool))
    (firstEnd r rows cols f v w)).stk

theorem firstEndBank_word (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    firstEndBank B r rows cols f v w firstWord =
      MatrixMaterialization.rowMajor (firstResult r rows cols f) := by
  exact MatrixTableInterlaceFirstTranspose.transposeEnd_numberedRestoration
    r rows cols f w

theorem firstEndBank_rows (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    firstEndBank B r rows cols f v w firstRows =
      List.replicate (firstColsCount r cols) true := by
  rfl

theorem firstEndBank_cols (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    firstEndBank B r rows cols f v w firstCols =
      List.replicate (firstRowsCount r rows) true := by
  rfl

theorem firstEndBank_temp (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    firstEndBank B r rows cols f v w wordTemp = [] := by
  rfl

theorem firstEndBank_block (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    firstEndBank B r rows cols f v w blockInput =
      List.replicate B true := by
  rfl

theorem firstEndBank_second (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl)
    (k : OneStack) :
    firstEndBank B r rows cols f v w (.inr (.inl k)) = [] := by
  rfl

def bridgeBank (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    Stack → List Bool :=
  let S := firstEndBank B r rows cols f v w
  let S1 := moved S firstWord wordTemp
  let S2 := moved S1 wordTemp secondWriterSource
  let S3 := duplicated S2 firstRows secondSizeRows secondWriterRows
    (firstColsCount r cols)
  let S4 := duplicated S3 firstCols secondSizeCols secondWriterCols
    (firstRowsCount r rows)
  moved S4 blockInput secondBlock

def bridgeTime (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  2*((MatrixMaterialization.rowMajor (firstResult r rows cols f)).length+1) +
    (firstColsCount r cols+1) + (firstRowsCount r rows+1) + (B+1)

theorem bridge_run (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    run (bridgeTime B r rows cols f)
      ⟨some bridgeStart,
        ((firstEnd r rows cols f v w).var,
          ((secondPrepared B r rows cols f).var,none)),
        firstEndBank B r rows cols f v w⟩ =
      ⟨some secondStart,
        ((firstEnd r rows cols f v w).var,
          ((secondPrepared B r rows cols f).var,none)),
        bridgeBank B r rows cols f v w⟩ := by
  let S := firstEndBank B r rows cols f v w
  let S1 := moved S firstWord wordTemp
  let S2 := moved S1 wordTemp secondWriterSource
  let S3 := duplicated S2 firstRows secondSizeRows secondWriterRows
    (firstColsCount r cols)
  let S4 := duplicated S3 firstCols secondSizeCols secondWriterCols
    (firstRowsCount r rows)
  let u := (firstEnd r rows cols f v w).var
  let z := (secondPrepared B r rows cols f).var
  let W := MatrixMaterialization.rowMajor (firstResult r rows cols f)
  let R := firstColsCount r cols
  let C := firstRowsCount r rows
  have hw : S firstWord = W := firstEndBank_word B r rows cols f v w
  have hr : S firstRows = List.replicate R true :=
    firstEndBank_rows B r rows cols f v w
  have hc : S firstCols = List.replicate C true :=
    firstEndBank_cols B r rows cols f v w
  have htemp : S wordTemp = [] := firstEndBank_temp B r rows cols f v w
  have hb : S blockInput = List.replicate B true :=
    firstEndBank_block B r rows cols f v w
  have htemp1 : S1 wordTemp = W.reverse := by
    simp [S1,moved,hw,htemp]
  have hrows2 : S2 firstRows = List.replicate R true := by
    calc
      S2 firstRows = S firstRows := by
        simp [S2,S1,moved,firstWord,wordTemp,
          secondWriterSource,firstRows]
      _ = _ := hr
  have hcols3 : S3 firstCols = List.replicate C true := by
    calc
      S3 firstCols = S firstCols := by
        simp [S3,S2,S1,duplicated,moved,firstWord,wordTemp,
          secondWriterSource,firstRows,secondSizeRows,
          secondWriterRows,firstCols]
      _ = _ := hc
  have hblock4 : S4 blockInput = List.replicate B true := by
    calc
      S4 blockInput = S blockInput := by
        simp [S4,S3,S2,S1,duplicated,moved,
          firstWord,wordTemp,secondWriterSource,
          firstRows,secondSizeRows,secondWriterRows,
          firstCols,secondSizeCols,secondWriterCols,blockInput]
      _ = _ := hb
  have h1raw := move_run firstWord wordTemp (.inr (.inl .wordTemp))
    (.inr (.inl .wordTarget)) rfl (by decide) u z none W S hw
  have h1 : run (W.length+1)
      ⟨some bridgeStart,(u,(z,none)),S⟩ =
      ⟨some (.inr (.inl .wordTarget)),(u,(z,none)),S1⟩ := by
    simpa [bridgeStart,S1,moved,hw] using h1raw
  have h2raw := move_run wordTemp secondWriterSource
    (.inr (.inl .wordTarget)) (.inr (.inl .rows))
    rfl (by decide) u z none W.reverse S1 htemp1
  have h2 : run (W.length+1)
      ⟨some (.inr (.inl .wordTarget)),(u,(z,none)),S1⟩ =
      ⟨some (.inr (.inl .rows)),(u,(z,none)),S2⟩ := by
    simpa [S2,moved,htemp1] using h2raw
  have h3raw := duplicate_run firstRows secondSizeRows secondWriterRows
    (.inr (.inl .rows)) (.inr (.inl .cols))
    rfl (by decide) (by decide) (by decide)
    u z none R S2 hrows2
  have h3 : run (R+1)
      ⟨some (.inr (.inl .rows)),(u,(z,none)),S2⟩ =
      ⟨some (.inr (.inl .cols)),(u,(z,none)),S3⟩ := by
    simpa [S3,duplicated] using h3raw
  have h4raw := duplicate_run firstCols secondSizeCols secondWriterCols
    (.inr (.inl .cols)) (.inr (.inl .blocks))
    rfl (by decide) (by decide) (by decide)
    u z none C S3 hcols3
  have h4 : run (C+1)
      ⟨some (.inr (.inl .cols)),(u,(z,none)),S3⟩ =
      ⟨some (.inr (.inl .blocks)),(u,(z,none)),S4⟩ := by
    simpa [S4,duplicated] using h4raw
  have h5raw := move_run blockInput secondBlock
    (.inr (.inl .blocks)) secondStart
    rfl (by decide) u z none (List.replicate B true) S4 hblock4
  have h5 : run (B+1)
      ⟨some (.inr (.inl .blocks)),(u,(z,none)),S4⟩ =
      ⟨some secondStart,(u,(z,none)),
        moved S4 blockInput secondBlock⟩ := by
    simpa [moved,hblock4] using h5raw
  have h12 := run_add h1 (W.length+1)
  rw [h2] at h12
  have h123 := run_add h12 (R+1)
  rw [h3] at h123
  have h1234 := run_add h123 (C+1)
  rw [h4] at h1234
  have h12345 := run_add h1234 (B+1)
  rw [h5] at h12345
  simpa only [bridgeTime,bridgeBank,W,R,C,u,z,S,S1,S2,S3,S4,
    Nat.two_mul,Nat.add_assoc] using h12345

macro "finish_bank" : tactic =>
  `(tactic| simp [firstEndBank,firstEnd,secondPrepared,firstFrame,
    liftCfg,MatrixTableInterlaceFirstTranspose.firstFrame,
    MatrixTableInterlaceFirstRestoration.combinedFrame,
    MatrixTableInterlaceCombined.bridgeCfg,
    MatrixTableInterlaceCombined.cfg,
    MatrixTableInterlaceCombined.sizeBank,
    MatrixTableInterlaceCombined.writerData,
    MatrixTableInterlaceSize.cfg,
    MatrixTableWriter.Data.contents,
    MatrixTableWriter.Data.cell,
    MatrixTableWriter.Data.foreign,
    MatrixTableInterlace.persistentBank,
    MatrixTableInterlaceFirstRestoration.emptyRowBank,
    MatrixTableInterlaceFirstTranspose.emptyTransposeBank])

theorem bridgeBank_secondPrepared (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    (fun k : OneStack => bridgeBank B r rows cols f v w (.inr (.inl k))) =
      (secondPrepared B r rows cols f).stk := by
  funext k
  have hw := firstEndBank_word B r rows cols f v w
  have hr := firstEndBank_rows B r rows cols f v w
  have hc := firstEndBank_cols B r rows cols f v w
  have hb := firstEndBank_block B r rows cols f v w
  have ht := firstEndBank_temp B r rows cols f v w
  have hz (j : OneStack) := firstEndBank_second B r rows cols f v w j
  cases k with
  | inl j =>
      cases j with
      | inl h =>
          cases h with
          | inl i =>
              fin_cases i <;>
                simp [bridgeBank,secondPrepared,moved,duplicated,
                  firstWord,wordTemp,firstRows,firstCols,blockInput,
                  secondWriterSource,secondSizeRows,secondWriterRows,
                  secondSizeCols,secondWriterCols,secondBlock,
                  hw,hr,hc,hb,ht,hz] <;>
                simp [firstEndBank,firstEnd,secondPrepared,firstFrame,
                  liftCfg,
                  MatrixTableInterlaceFirstTranspose.firstFrame,
                  MatrixTableInterlaceFirstRestoration.combinedFrame,
                  MatrixTableInterlaceCombined.bridgeCfg,
                  MatrixTableInterlaceCombined.cfg,
                  MatrixTableInterlaceCombined.sizeBank,
                  MatrixTableInterlaceCombined.writerData,
                  MatrixTableInterlaceSize.cfg,
                  MatrixTableWriter.Data.contents,
                  MatrixTableWriter.Data.cell,
                  MatrixTableWriter.Data.foreign,
                  MatrixTableInterlace.persistentBank]
          | inr h =>
              cases h with
              | inl j =>
                  cases j with
                  | inl i =>
                      fin_cases i <;>
                        simp [bridgeBank,secondPrepared,moved,duplicated,
                          firstWord,wordTemp,firstRows,firstCols,blockInput,
                          secondWriterSource,secondSizeRows,secondWriterRows,
                          secondSizeCols,secondWriterCols,secondBlock,
                          hw,hr,hc,hb,ht,hz] <;> finish_bank <;>
                        (change (firstEndBank B r rows cols f v w wordTemp).reverse ++
                            firstEndBank B r rows cols f v w firstWord =
                              MatrixMaterialization.rowMajor
                                (firstResult r rows cols f)
                         rw [ht,hw]
                         simp)
                  | inr i =>
                      fin_cases i <;>
                        simp [bridgeBank,secondPrepared,moved,duplicated,
                          firstWord,wordTemp,firstRows,firstCols,blockInput,
                          secondWriterSource,secondSizeRows,secondWriterRows,
                          secondSizeCols,secondWriterCols,secondBlock,
                          hw,hr,hc,hb,ht,hz] <;> finish_bank
              | inr i =>
                  cases i <;>
                    simp [bridgeBank,secondPrepared,moved,duplicated,
                      firstWord,wordTemp,firstRows,firstCols,blockInput,
                      secondWriterSource,secondSizeRows,secondWriterRows,
                      secondSizeCols,secondWriterCols,secondBlock,
                      hw,hr,hc,hb,ht,hz] <;> finish_bank
      | inr h =>
          cases h with
          | inl i =>
              fin_cases i <;>
                simp [bridgeBank,secondPrepared,moved,duplicated,
                  firstWord,wordTemp,firstRows,firstCols,blockInput,
                  secondWriterSource,secondSizeRows,secondWriterRows,
                  secondSizeCols,secondWriterCols,secondBlock,
                  hw,hr,hc,hb,ht,hz] <;> finish_bank
          | inr i =>
              fin_cases i <;>
                simp [bridgeBank,secondPrepared,moved,duplicated,
                  firstWord,wordTemp,firstRows,firstCols,blockInput,
                  secondWriterSource,secondSizeRows,secondWriterRows,
                  secondSizeCols,secondWriterCols,secondBlock,
                  hw,hr,hc,hb,ht,hz] <;> finish_bank
  | inr h =>
      cases h with
      | inl j =>
          cases j with
          | inl i =>
              fin_cases i <;>
                simp [bridgeBank,secondPrepared,moved,duplicated,
                  firstWord,wordTemp,firstRows,firstCols,blockInput,
                  secondWriterSource,secondSizeRows,secondWriterRows,
                  secondSizeCols,secondWriterCols,secondBlock,
                  hw,hr,hc,hb,ht,hz] <;> finish_bank
          | inr i =>
              fin_cases i <;>
                simp [bridgeBank,secondPrepared,moved,duplicated,
                  firstWord,wordTemp,firstRows,firstCols,blockInput,
                  secondWriterSource,secondSizeRows,secondWriterRows,
                  secondSizeCols,secondWriterCols,secondBlock,
                  hw,hr,hc,hb,ht,hz] <;> finish_bank
      | inr i =>
          cases i <;>
            simp [bridgeBank,secondPrepared,moved,duplicated,
              firstWord,wordTemp,firstRows,firstCols,blockInput,
              secondWriterSource,secondSizeRows,secondWriterRows,
              secondSizeCols,secondWriterCols,secondBlock,
              hw,hr,hc,hb,ht,hz] <;> finish_bank
  all_goals
    simp [MatrixTableInterlaceFirstTranspose.firstFrame,
      MatrixTableInterlaceFirstRestoration.combinedFrame,
      MatrixTableInterlaceCombined.bridgeCfg,
      MatrixTableInterlaceCombined.sizeBank,
      MatrixTableInterlaceCombined.writerData,
      MatrixTableInterlace.persistentBank,
      MatrixTableInterlaceFirstTranspose.emptyTransposeBank,
      MatrixTableWriter.Data.contents,MatrixTableWriter.Data.cell,
      MatrixTableWriter.Data.foreign,hw,hr,hc,hb,ht,hz]

def foreignAfter (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    OneStack ⊕ Fin 1 → List Bool
  | .inl k => bridgeBank B r rows cols f v w (.inl k)
  | .inr k => bridgeBank B r rows cols f v w (.inr (.inr k))

theorem bridgeEnd_secondFrame (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    (⟨some secondStart,
      ((firstEnd r rows cols f v w).var,
        ((secondPrepared B r rows cols f).var,none)),
      bridgeBank B r rows cols f v w⟩ : Config) =
    secondFrame (firstEnd r rows cols f v w).var
      (foreignAfter B r rows cols f v w)
      (secondPrepared B r rows cols f) := by
  have h := bridgeBank_secondPrepared B r rows cols f v w
  congr 1
  funext k
  cases k with
  | inl k =>
      simp [secondFrame,foreignAfter,renameCfg,liftCfg,secondSlots]
  | inr k =>
      cases k with
      | inl k =>
          simpa [secondFrame,foreignAfter,renameCfg,liftCfg,secondSlots]
            using congrFun h k
      | inr k =>
          simp [secondFrame,foreignAfter,renameCfg,liftCfg,secondSlots]

def initialForeign (B : ℕ) : OneStack ⊕ Fin 1 → List Bool :=
  Sum.elim (fun _ : OneStack => [])
    (![List.replicate B true] : Fin 1 → List Bool)

def firstPrepared (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    MatrixTableInterlaceFirstTranspose.Config :=
  MatrixTableInterlaceFirstTranspose.firstFrame
    (MatrixTableLookup.initial,none)
    MatrixTableInterlaceFirstTranspose.emptyTransposeBank
    (MatrixTableInterlaceFirstRestoration.combinedFrame
      (false,(none,SamplerMachineBlockReverse.initial))
      MatrixTableInterlaceFirstRestoration.emptyRowBank
      (MatrixTableInterlaceCombined.bridgeCfg
        MatrixTableInterlaceCombined.start (2^r) rows cols
        (MatrixMaterialization.rowMajor f) [] [] [] [] []))

theorem first_phase (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^(2^r))) :
    ∃ t ≤ MatrixTableInterlaceFirstTranspose.totalBound (2^r) rows cols f,
      ∃ v : MatrixTableInterlaceCombined.WControl,
      ∃ w : MatrixTableInterlaceFirstTranspose.TControl,
        run t (firstFrame (secondPrepared B r rows cols f).var
          (initialForeign B) (firstPrepared r rows cols f)) =
        firstFrame (secondPrepared B r rows cols f).var
          (initialForeign B) (firstEnd r rows cols f v w) := by
  obtain ⟨t,ht,v,w,he⟩ :=
    MatrixTableInterlaceFirstTranspose.first_transpose_run
      (2^r) rows cols f hwidth
  have hhe : MatrixTableInterlaceFirstTranspose.run t
      (firstPrepared r rows cols f) = firstEnd r rows cols f v w := by
    simpa only [firstPrepared,firstEnd] using he
  have hh : (MatrixTableInterlaceFirstTranspose.run t
      (firstPrepared r rows cols f)).l = none := by
    rw [hhe]
    rfl
  obtain ⟨u,hu,hr⟩ := lift_outputs
    MatrixTableInterlaceFirstTranspose.program program
    (some (.inl .wordTemp)) (fun _ => rfl)
    ((secondPrepared B r rows cols f).var,none)
    (initialForeign B) (firstPrepared r rows cols f) t hh
  change run u (firstFrame _ _ _) =
    firstFrame _ _ (MatrixTableInterlaceFirstTranspose.run t _) at hr
  rw [hhe] at hr
  exact ⟨u,hu.trans ht,v,w,hr⟩

def secondEnd (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl)
    (w : MatrixTableInterlaceFirstTranspose.TControl) :
    MatrixTableInterlaceFirstTranspose.Config :=
  MatrixTableInterlaceFirstTranspose.transposeFrame
    (MatrixTableInterlaceFirstFinish.finalOut B
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f) v).var
    (fun k => MatrixTableInterlaceFirstTranspose.bridgeBank B
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f) v (.inl k))
    (MatrixTableInterlaceFirstTranspose.transposeEnd B
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f) w)

theorem second_phase (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (u : OneControl)
    (foreign : OneStack ⊕ Fin 1 → List Bool)
    (hwidth : 0 < firstColsCount r cols *
      ((firstRowsCount r rows)^B)) :
    ∃ t ≤ MatrixTableInterlaceFirstTranspose.totalBound B
        (firstColsCount r cols) (firstRowsCount r rows)
        (firstResult r rows cols f),
      ∃ v : MatrixTableInterlaceCombined.WControl,
      ∃ w : MatrixTableInterlaceFirstTranspose.TControl,
        run t (secondFrame u foreign (secondPrepared B r rows cols f)) =
        secondFrame u foreign (secondEnd B r rows cols f v w) := by
  obtain ⟨t,ht,v,w,he⟩ :=
    MatrixTableInterlaceFirstTranspose.first_transpose_run B
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f) hwidth
  have hhe : MatrixTableInterlaceFirstTranspose.run t
      (secondPrepared B r rows cols f) = secondEnd B r rows cols f v w := by
    simpa only [secondPrepared,secondEnd] using he
  have hh : (MatrixTableInterlaceFirstTranspose.run t
      (secondPrepared B r rows cols f)).l = none := by
    rw [hhe]
    rfl
  obtain ⟨t',ht',hr⟩ := lift_outputs_renamed
    secondSlots secondLabels secondControl
    MatrixTableInterlaceFirstTranspose.program program none (fun _ => rfl)
    (u,none) foreign (secondPrepared B r rows cols f) t hh
  change run t' (secondFrame _ _ _) =
    secondFrame _ _ (MatrixTableInterlaceFirstTranspose.run t _) at hr
  rw [hhe] at hr
  exact ⟨t',ht'.trans ht,v,w,hr⟩

def totalBound (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  MatrixTableInterlaceFirstTranspose.totalBound (2^r) rows cols f +
    bridgeTime B r rows cols f +
    MatrixTableInterlaceFirstTranspose.totalBound B
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f)

/-- Two complete, charged interlace/reversal/transpose controllers, with the
second unary block count supplied on `blockInput`. Only the initial bank of the
first controller is prepared; the second bank is physically produced. -/
theorem double_run (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hfirst : 0 < rows*(cols^(2^r)))
    (hsecond : 0 < firstColsCount r cols *
      ((firstRowsCount r rows)^B)) :
    ∃ t ≤ totalBound B r rows cols f,
      ∃ v₁ : MatrixTableInterlaceCombined.WControl,
      ∃ w₁ : MatrixTableInterlaceFirstTranspose.TControl,
      ∃ v₂ : MatrixTableInterlaceCombined.WControl,
      ∃ w₂ : MatrixTableInterlaceFirstTranspose.TControl,
        run t (firstFrame (secondPrepared B r rows cols f).var
          (initialForeign B) (firstPrepared r rows cols f)) =
        secondFrame (firstEnd r rows cols f v₁ w₁).var
          (foreignAfter B r rows cols f v₁ w₁)
          (secondEnd B r rows cols f v₂ w₂) := by
  obtain ⟨t₁,ht₁,v₁,w₁,h₁⟩ :=
    first_phase B r rows cols f hfirst
  have hbridge := bridge_run B r rows cols f v₁ w₁
  have h₁' : run t₁
      (firstFrame (secondPrepared B r rows cols f).var
        (initialForeign B) (firstPrepared r rows cols f)) =
      ⟨some bridgeStart,
        ((firstEnd r rows cols f v₁ w₁).var,
          ((secondPrepared B r rows cols f).var,none)),
        firstEndBank B r rows cols f v₁ w₁⟩ := by
    simpa only [firstEndBank,firstFrame,initialForeign] using h₁
  have h₁₂ := run_add h₁' (bridgeTime B r rows cols f)
  rw [hbridge,bridgeEnd_secondFrame] at h₁₂
  obtain ⟨t₂,ht₂,v₂,w₂,h₂⟩ := second_phase B r rows cols f
    (firstEnd r rows cols f v₁ w₁).var
    (foreignAfter B r rows cols f v₁ w₁) hsecond
  have h₁₂₃ := run_add h₁₂ t₂
  rw [h₂] at h₁₂₃
  refine ⟨t₁+bridgeTime B r rows cols f+t₂, ?_,v₁,w₁,v₂,w₂,h₁₂₃⟩
  dsimp [totalBound]
  omega

def secondOutput : Stack := .inr (.inl (.inr (.inr .output)))

def secondResult (R r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    Fin ((firstRowsCount r rows)^(2^R)) →
      Fin ((2^R)*(firstColsCount r cols)) → Bool :=
  MatrixTableInterlaceRowReverse.numberedRestoration R
    (firstColsCount r cols) (firstRowsCount r rows)
    (firstResult r rows cols f)

/-- The literal row-major two-restoration word at the actual halted output
stack, with no table permutation or isomorphism left implicit. -/
theorem double_restoration_run (R r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hfirst : 0 < rows*(cols^(2^r)))
    (hsecond : 0 < firstColsCount r cols *
      ((firstRowsCount r rows)^(2^R))) :
    ∃ t ≤ totalBound (2^R) r rows cols f,
      ∃ c : Config,
        run t (firstFrame (secondPrepared (2^R) r rows cols f).var
          (initialForeign (2^R)) (firstPrepared r rows cols f)) = c ∧
        c.l = none ∧
        c.stk secondOutput =
          MatrixMaterialization.rowMajor (secondResult R r rows cols f) := by
  obtain ⟨t,ht,v₁,w₁,v₂,w₂,he⟩ :=
    double_run (2^R) r rows cols f hfirst hsecond
  let c := secondFrame (firstEnd r rows cols f v₁ w₁).var
    (foreignAfter (2^R) r rows cols f v₁ w₁)
    (secondEnd (2^R) r rows cols f v₂ w₂)
  refine ⟨t,ht,c,he,?_,?_⟩
  · rfl
  · change (MatrixTableInterlaceFirstTranspose.transposeEnd (2^R)
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f) w₂).stk (.inr .output) = _
    exact MatrixTableInterlaceFirstTranspose.transposeEnd_numberedRestoration
      R (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f) w₂

def firstScale (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  (2^r)+rows+cols+(MatrixMaterialization.rowMajor f).length+
    firstRowsCount r rows+firstColsCount r cols+
    (MatrixTableInterlaceFirstFinish.word (2^r) rows cols f).length+1

def secondScale (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  B+firstColsCount r cols+firstRowsCount r rows+
    (MatrixMaterialization.rowMajor (firstResult r rows cols f)).length+
    B*(firstColsCount r cols)+(firstRowsCount r rows)^B+
    (MatrixTableInterlaceFirstFinish.word B
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f)).length+1

theorem totalBound_polynomial (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    totalBound B r rows cols f ≤
      8192 * (firstScale r rows cols f +
        secondScale B r rows cols f)^4 := by
  let N := firstScale r rows cols f + secondScale B r rows cols f
  have hfirstPos : 1 ≤ firstScale r rows cols f := by
    have hp : 0 < 2^r := by positivity
    dsimp [firstScale]
    omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hN2 : N ≤ N^2 := by
    nlinarith [Nat.mul_le_mul (le_refl N) hN]
  have hN4 : N^2 ≤ N^4 := by
    have h : 1 ≤ N^2 := by nlinarith
    nlinarith [Nat.mul_le_mul (le_refl (N^2)) h]
  have hNto4 : N ≤ N^4 := by omega
  have hfirstScale : firstScale r rows cols f ≤ N := by
    dsimp [N]; omega
  have hsecondScale : secondScale B r rows cols f ≤ N := by
    dsimp [N]; omega
  have hfirst := MatrixTableInterlaceFirstTranspose.totalBound_polynomial
    (2^r) rows cols f
  have hfirst' : MatrixTableInterlaceFirstTranspose.totalBound
      (2^r) rows cols f ≤ 2048*N^4 := by
    calc
      _ ≤ 2048*(firstScale r rows cols f)^4 := by
        simpa only [firstScale,firstRowsCount,firstColsCount] using hfirst
      _ ≤ _ := Nat.mul_le_mul_left 2048
        (Nat.pow_le_pow_left hfirstScale 4)
  have hsecond := MatrixTableInterlaceFirstTranspose.totalBound_polynomial
    B (firstColsCount r cols) (firstRowsCount r rows)
    (firstResult r rows cols f)
  have hsecond' : MatrixTableInterlaceFirstTranspose.totalBound B
      (firstColsCount r cols) (firstRowsCount r rows)
      (firstResult r rows cols f) ≤ 2048*N^4 := by
    calc
      _ ≤ 2048*(secondScale B r rows cols f)^4 := by
        simpa only [secondScale] using hsecond
      _ ≤ _ := Nat.mul_le_mul_left 2048
        (Nat.pow_le_pow_left hsecondScale 4)
  have hsecondPrefix :
      (MatrixMaterialization.rowMajor (firstResult r rows cols f)).length +
        firstColsCount r cols + firstRowsCount r rows + B + 1 ≤
          secondScale B r rows cols f := by
    dsimp [secondScale]
    omega
  have hbridge : bridgeTime B r rows cols f ≤ 5*N := by
    dsimp only [bridgeTime]
    omega
  change MatrixTableInterlaceFirstTranspose.totalBound (2^r) rows cols f +
      bridgeTime B r rows cols f +
      MatrixTableInterlaceFirstTranspose.totalBound B
        (firstColsCount r cols) (firstRowsCount r rows)
        (firstResult r rows cols f) ≤ 8192*N^4
  omega

/-- Under the paper's explicit protected-row and protected-column numberings,
the controller's numeric table is exactly the next-level matrix, entry by
entry. This is a coding identity; the protected source bank remains an input
to the controller theorem above. -/
theorem secondResult_step_entry {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (sourceConstant b y i : ℕ) (M : Iteration.Matrix)
    (x : Fin (Iteration.step G sourceConstant b y i M).rows)
    (z : Fin (Iteration.step G sourceConstant b y i M).columns) :
    (Iteration.step G sourceConstant b y i M).entry x z =
      secondResult
        (Iteration.rQ G sourceConstant b y i M)
        (Iteration.rq G sourceConstant b y i M)
        (Iteration.nRowNumbering G sourceConstant b y i M).size
        (Iteration.nColNumbering G sourceConstant b y i M).size
        (MatrixTableInterlaceLevelCodes.numericSource
          (Iteration.protectedMatrix G sourceConstant b y i M)
          (Iteration.nRowNumbering G sourceConstant b y i M)
          (Iteration.nColNumbering G sourceConstant b y i M)) x z := by
  simpa only [secondResult,firstResult,firstRowsCount,firstColsCount] using
    MatrixTableInterlaceLevelCodes.step_entry_numeric G sourceConstant b y i M x z

theorem double_step_run {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (sourceConstant b y i : ℕ) (M : Iteration.Matrix) :
    let R := Iteration.rQ G sourceConstant b y i M
    let r := Iteration.rq G sourceConstant b y i M
    let rows := (Iteration.nRowNumbering G sourceConstant b y i M).size
    let cols := (Iteration.nColNumbering G sourceConstant b y i M).size
    let f := MatrixTableInterlaceLevelCodes.numericSource
      (Iteration.protectedMatrix G sourceConstant b y i M)
      (Iteration.nRowNumbering G sourceConstant b y i M)
      (Iteration.nColNumbering G sourceConstant b y i M)
    ∃ t ≤ 8192 * (firstScale r rows cols f +
      secondScale (2^R) r rows cols f)^4,
      ∃ c : Config,
        run t (firstFrame (secondPrepared (2^R) r rows cols f).var
          (initialForeign (2^R)) (firstPrepared r rows cols f)) = c ∧
        c.l = none ∧
        c.stk secondOutput =
          MatrixMaterialization.rowMajor
            (Iteration.step G sourceConstant b y i M).entry := by
  dsimp only
  let R := Iteration.rQ G sourceConstant b y i M
  let r := Iteration.rq G sourceConstant b y i M
  let rows := (Iteration.nRowNumbering G sourceConstant b y i M).size
  let cols := (Iteration.nColNumbering G sourceConstant b y i M).size
  let f := MatrixTableInterlaceLevelCodes.numericSource
    (Iteration.protectedMatrix G sourceConstant b y i M)
    (Iteration.nRowNumbering G sourceConstant b y i M)
    (Iteration.nColNumbering G sourceConstant b y i M)
  have hr : 0 < rows :=
    (Iteration.nRowNumbering G sourceConstant b y i M).size_pos
  have hc : 0 < cols :=
    (Iteration.nColNumbering G sourceConstant b y i M).size_pos
  have hfirst : 0 < rows*(cols^(2^r)) := by positivity
  have hsecond : 0 < firstColsCount r cols *
      ((firstRowsCount r rows)^(2^R)) := by
    dsimp [firstColsCount,firstRowsCount]
    positivity
  have hfun : secondResult R r rows cols f =
      (Iteration.step G sourceConstant b y i M).entry := by
    funext x z
    exact (secondResult_step_entry G sourceConstant b y i M x z).symm
  obtain ⟨t,ht,c,he,hh,hw⟩ :=
    double_restoration_run R r rows cols f hfirst hsecond
  refine ⟨t,ht.trans (totalBound_polynomial (2^R) r rows cols f),
    c,he,hh,?_⟩
  simpa only [hfun] using hw

end EthInapproximability.CurrentPaper.MatrixTableInterlaceDouble
