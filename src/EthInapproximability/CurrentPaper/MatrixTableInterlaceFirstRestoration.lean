import EthInapproximability.CurrentPaper.MatrixTableInterlaceCombined
import EthInapproximability.CurrentPaper.MatrixTableInterlaceRowWidth

/-!
# Physical first-restoration join

The combined interlace writer and width/row-order controller are staged in
one finite Boolean-stack instruction table.  Explicit bridge labels consume
the three words used by the second controller: unary old rows, unary new
columns, and the literal interlace table.  The latter uses two moves to
preserve bit order.  No free intermediate table or count header is assumed.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstRestoration

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev CStack := MatrixTableInterlaceCombined.Stack
abbrev RStack := MatrixTableInterlaceRowWidth.Stack
abbrev Stack := CStack ⊕ RStack

inductive Bridge where
  | rows | cols | wordTemp | wordTarget
  deriving DecidableEq, Fintype

abbrev Label := MatrixTableInterlaceCombined.Label ⊕
  (Bridge ⊕ MatrixTableInterlaceRowWidth.Label)
abbrev Control := MatrixTableInterlaceCombined.Control ×
  (MatrixTableInterlaceRowWidth.Control × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def cRow : Stack := .inl (.inr (.inl (.inl 0)))
def cColCount : Stack := .inl (.inr (.inr .cols))
def cWord : Stack := .inl (.inr (.inr .output))
def cTemp : Stack := .inl (.inr (.inr .temp))
def rRow : Stack := .inr (.inl 0)
def rColCount : Stack := .inr (.inl 1)
def rWord : Stack := .inr (.inr 0)

def start : Label := .inl MatrixTableInterlaceCombined.start
def rowStart : Label := .inr (.inr (.inl .outer))

def initial : Control := (MatrixTableInterlaceCombined.initial,
  ((false,(none,SamplerMachineBlockReverse.initial)),none))

def rowLabels : MatrixTableInterlaceRowWidth.Label ⊕
    (MatrixTableInterlaceCombined.Label ⊕ Bridge) ≃ Label where
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

def rowControl : MatrixTableInterlaceRowWidth.Control ×
    (MatrixTableInterlaceCombined.Control × Option Bool) ≃ Control where
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

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl Bridge.rows))
      (MatrixTableInterlaceCombined.program l)
  | .inr (.inl .rows) => move cRow rRow (.inr (.inl .rows))
      (.inr (.inl .cols))
  | .inr (.inl .cols) => move cColCount rColCount (.inr (.inl .cols))
      (.inr (.inl .wordTemp))
  | .inr (.inl .wordTemp) => move cWord cTemp (.inr (.inl .wordTemp))
      (.inr (.inl .wordTarget))
  | .inr (.inl .wordTarget) => move cTemp rWord (.inr (.inl .wordTarget))
      rowStart
  | .inr (.inr l) => renameStmt (Equiv.sumComm RStack CStack)
      rowLabels rowControl
      (liftStmt none (MatrixTableInterlaceRowWidth.program l))

def cfg (l : Option Label) (v : Control)
    (combined : CStack → List Bool) (row : RStack → List Bool) : Config :=
  ⟨l,v,Sum.elim combined row⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem move_cons (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v : MatrixTableInterlaceCombined.Control)
    (w : MatrixTableInterlaceRowWidth.Control)
    (s : Option Bool) (S : Stack → List Bool) (b : Bool) (bits : List Bool)
    (hs : S source = b::bits) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some again,(v,(w,some b)),
        Function.update (Function.update S source bits)
          target (b::S target)⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs]
  simp [Function.update_apply, hne, Ne.symm hne]

private theorem move_nil (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (v : MatrixTableInterlaceCombined.Control)
    (w : MatrixTableInterlaceRowWidth.Control)
    (s : Option Bool)
    (S : Stack → List Bool) (hs : S source = []) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),S⟩ := by
  have hu : Function.update S source [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs, hu]

theorem move_run (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v : MatrixTableInterlaceCombined.Control)
    (w : MatrixTableInterlaceRowWidth.Control)
    (s : Option Bool) (bits : List Bool) (S : Stack → List Bool)
    (hs : S source = bits) :
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

def bridgeAfter (S : Stack → List Bool) : Stack → List Bool :=
  moved (moved (moved (moved S cRow rRow) cColCount rColCount)
    cWord cTemp) cTemp rWord

theorem bridge_run (rows colCount : ℕ) (word : List Bool)
    (v : MatrixTableInterlaceCombined.Control)
    (w : MatrixTableInterlaceRowWidth.Control)
    (S : Stack → List Bool)
    (hr : S cRow = List.replicate rows true)
    (hc : S cColCount = List.replicate colCount true)
    (hw : S cWord = word)
    (htemp : S cTemp = []) :
    run ((rows+1)+(colCount+1)+(word.length+1)+(word.length+1))
      ⟨some (.inr (.inl .rows)),(v,(w,none)),S⟩ =
    ⟨some rowStart,(v,(w,none)),bridgeAfter S⟩ := by
  let S1 := moved S cRow rRow
  let S2 := moved S1 cColCount rColCount
  let S3 := moved S2 cWord cTemp
  have hcol : S1 cColCount = List.replicate colCount true := by
    calc
      S1 cColCount = S cColCount := by simp [S1,moved,cRow,rRow,cColCount]
      _ = List.replicate colCount true := hc
  have hword : S2 cWord = word := by
    calc
      S2 cWord = S cWord := by
        simp [S2,S1,moved,cRow,rRow,cColCount,rColCount,cWord]
      _ = word := hw
  have htemp3 : S3 cTemp = word.reverse := by
    have htemp2 : S2 cTemp = [] := by
      calc
        S2 cTemp = S cTemp := by
          simp [S2,S1,moved,cRow,rRow,cColCount,rColCount,cTemp]
        _ = [] := htemp
    calc
      S3 cTemp = (S2 cWord).reverse ++ S2 cTemp := by
        simp [S3,moved,cWord,cTemp]
      _ = word.reverse := by simp [hword,htemp2]
  have h1raw := move_run cRow rRow (.inr (.inl .rows))
    (.inr (.inl .cols)) rfl (by decide) v w none
    (List.replicate rows true) S hr
  have h1 : run (rows+1)
      ⟨some (.inr (.inl .rows)),(v,(w,none)),S⟩ =
      ⟨some (.inr (.inl .cols)),(v,(w,none)),S1⟩ := by
    simpa [S1,moved,hr] using h1raw
  have h2raw := move_run cColCount rColCount (.inr (.inl .cols))
    (.inr (.inl .wordTemp)) rfl (by decide) v w none
    (List.replicate colCount true) S1 hcol
  have h2 : run (colCount+1)
      ⟨some (.inr (.inl .cols)),(v,(w,none)),S1⟩ =
      ⟨some (.inr (.inl .wordTemp)),(v,(w,none)),S2⟩ := by
    simpa [S2,moved,hcol] using h2raw
  have h3raw := move_run cWord cTemp (.inr (.inl .wordTemp))
    (.inr (.inl .wordTarget)) rfl (by decide) v w none word S2 hword
  have h3 : run (word.length+1)
      ⟨some (.inr (.inl .wordTemp)),(v,(w,none)),S2⟩ =
      ⟨some (.inr (.inl .wordTarget)),(v,(w,none)),S3⟩ := by
    simpa [S3,moved,hword] using h3raw
  have h4raw := move_run cTemp rWord (.inr (.inl .wordTarget))
    rowStart rfl (by decide) v w none word.reverse S3 htemp3
  have h4 : run (word.length+1)
      ⟨some (.inr (.inl .wordTarget)),(v,(w,none)),S3⟩ =
      ⟨some rowStart,(v,(w,none)),bridgeAfter S⟩ := by
    change run (word.length+1) _ =
      ⟨some rowStart,(v,(w,none)),moved S3 cTemp rWord⟩
    simpa only [moved, htemp3, List.length_reverse] using h4raw
  have h := run_add h1 (colCount+1)
  rw [h2] at h
  have h' := run_add h (word.length+1)
  rw [h3] at h'
  have h'' := run_add h' (word.length+1)
  rw [h4] at h''
  simpa only [bridgeAfter, S1, S2, S3, List.length_reverse,
    Nat.add_assoc] using h''

def combinedFrame (v : MatrixTableInterlaceRowWidth.Control)
    (foreign : RStack → List Bool)
    (c : MatrixTableInterlaceCombined.Config) : Config :=
  liftCfg (some (.inl Bridge.rows)) (v,none) foreign c

def rowFrame (v : MatrixTableInterlaceCombined.Control)
    (foreign : CStack → List Bool)
    (c : MatrixTableInterlaceRowWidth.Config) : Config :=
  renameCfg (Equiv.sumComm RStack CStack) rowLabels rowControl
    (liftCfg none (v,none) foreign c)

def emptyRowBank : RStack → List Bool := fun _ => []

def combinedEnd (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    MatrixTableInterlaceCombined.Config :=
  MatrixTableInterlaceCombined.writerFrame MatrixTableInterlaceSize.initial
    (MatrixTableInterlaceCombined.sizeBank blocks rows cols [] [])
    (MatrixTableWriter.cfg none v
      (MatrixTableWriter.ready
        (MatrixTableInterlace.persistentBank rows cols
          (MatrixMaterialization.rowMajor f))
        (blocks*rows) (cols^blocks) 0 0 0 0 []
        (MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f))))

theorem combined_phase (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    ∃ t ≤ MatrixTableInterlaceCombined.totalBound blocks rows cols
        (MatrixMaterialization.rowMajor f).length,
      ∃ v,
        run t (combinedFrame (false,(none,SamplerMachineBlockReverse.initial))
          emptyRowBank
          (MatrixTableInterlaceCombined.bridgeCfg
            MatrixTableInterlaceCombined.start blocks rows cols
            (MatrixMaterialization.rowMajor f) [] [] [] [] [])) =
        combinedFrame (false,(none,SamplerMachineBlockReverse.initial)) emptyRowBank
          (combinedEnd blocks rows cols f v) := by
  obtain ⟨t,ht,v,he⟩ :=
    MatrixTableInterlaceCombined.combined_rowMajor blocks rows cols f []
  have hhalt :
      (MatrixTableInterlaceCombined.run t
        (MatrixTableInterlaceCombined.bridgeCfg
          MatrixTableInterlaceCombined.start blocks rows cols
          (MatrixMaterialization.rowMajor f) [] [] [] [] [])).l = none := by
    rw [he]
    rfl
  obtain ⟨u,hu,hr⟩ := lift_outputs
    MatrixTableInterlaceCombined.program program
    (some (.inl Bridge.rows)) (fun _ => rfl)
    ((false,(none,SamplerMachineBlockReverse.initial)),none) emptyRowBank
    (MatrixTableInterlaceCombined.bridgeCfg
      MatrixTableInterlaceCombined.start blocks rows cols
      (MatrixMaterialization.rowMajor f) [] [] [] [] []) t hhalt
  change run u (combinedFrame _ _ _) =
    combinedFrame _ _ (MatrixTableInterlaceCombined.run t _) at hr
  rw [he] at hr
  refine ⟨u,hu.trans ht,v,?_⟩
  simpa only [combinedEnd, List.append_nil] using hr

def sourceBank (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) : Stack → List Bool :=
  (combinedFrame (false,(none,SamplerMachineBlockReverse.initial))
    emptyRowBank (combinedEnd blocks rows cols f v)).stk

theorem sourceBank_rows (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v cRow = List.replicate rows true := by
  rfl

theorem sourceBank_cols (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v cColCount =
      List.replicate (cols^blocks) true := by
  rfl

theorem sourceBank_word (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v cWord =
      MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f) := by
  rfl

theorem sourceBank_temp (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    sourceBank blocks rows cols f v cTemp = [] := by
  rfl

theorem sourceBank_foreign (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) (k : RStack) :
    sourceBank blocks rows cols f v (.inr k) = [] := by
  rfl

private theorem no_halt_before {K L V : Type} [DecidableEq K]
    {P : L → TM2.Stmt (fun _ : K => Bool) L V}
    {c : TM2.Cfg (fun _ : K => Bool) L V} {t : ℕ}
    (h : (((advance P)^[t]) c).l ≠ none) :
    ∀ k < t, (((advance P)^[k]) c).l ≠ none := by
  intro k hk hk0
  let d := ((advance P)^[k]) c
  have hd : d.l = none := hk0
  have hstep : advance P d = d := by
    rcases d with ⟨l,v,S⟩
    cases l with
    | none => rfl
    | some l => simp at hd
  have hfixed : ∀ n : ℕ, ((advance P)^[n]) d = d := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hstep]
  have ht : t = (t-k)+k := by omega
  rw [ht, Function.iterate_add_apply, hfixed] at h
  exact h hd

theorem row_phase (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks))
    (v : MatrixTableInterlaceCombined.Control)
    (foreign : CStack → List Bool) :
    ∃ t ≤ MatrixAddressMachine.exactTime rows (cols^blocks) 0 +
      (2*(MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*(cols^blocks))),
      run t (rowFrame v foreign
        (MatrixTableInterlaceRowWidth.cfg (some (.inl .outer))
          (false,(none,SamplerMachineBlockReverse.initial))
          (List.replicate rows true) (List.replicate (cols^blocks) true)
          [] [] [] []
          (MatrixMaterialization.rowMajor
            (MatrixTableInterlace.interlaced (blocks := blocks) f))
          [] [] [] [] [] [])) =
      rowFrame v foreign
        (MatrixTableInterlaceRowWidth.cfg (some (.inr (.inr .check)))
          (false,(none,SamplerMachineBlockReverse.initial))
          (List.replicate rows true) (List.replicate (cols^blocks) true)
          [] [] [] (List.replicate (rows*(cols^blocks)) true)
          [] [] [] [] []
          (MatrixMaterialization.rowMajor
            (MatrixTableInterlaceRowReverse.numberedInterlace blocks rows cols f))
          []) := by
  obtain ⟨t,ht,he⟩ := MatrixTableInterlaceRowWidth.numberedInterlace_width_run
    blocks rows cols f hwidth
  let c := MatrixTableInterlaceRowWidth.cfg (some (.inl .outer))
    (false,(none,SamplerMachineBlockReverse.initial))
    (List.replicate rows true) (List.replicate (cols^blocks) true)
    [] [] [] []
    (MatrixMaterialization.rowMajor
      (MatrixTableInterlace.interlaced (blocks := blocks) f))
    [] [] [] [] [] []
  have hn : ∀ k < t,
      (((advance MatrixTableInterlaceRowWidth.program)^[k]) c).l ≠ none := by
    apply no_halt_before
    change (MatrixTableInterlaceRowWidth.run t c).l ≠ none
    rw [he]
    simp [MatrixTableInterlaceRowWidth.cfg]
  have h := lift_run_until_renamed (Equiv.sumComm RStack CStack)
    rowLabels rowControl MatrixTableInterlaceRowWidth.program program none
    (fun _ => rfl) (v,none) foreign c t hn
  change run t (rowFrame v foreign c) =
    rowFrame v foreign (MatrixTableInterlaceRowWidth.run t c) at h
  rw [he] at h
  exact ⟨t,ht,h⟩

def afterBank (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) : Stack → List Bool :=
  bridgeAfter (sourceBank blocks rows cols f v)

theorem afterBank_row (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    afterBank blocks rows cols f v rRow = List.replicate rows true := by
  simp [afterBank,bridgeAfter,moved,cRow,rRow,cColCount,rColCount,
    cWord,cTemp,rWord]
  change (sourceBank blocks rows cols f v cRow).reverse ++
    sourceBank blocks rows cols f v rRow = List.replicate rows true
  rw [sourceBank_rows]
  rw [show sourceBank blocks rows cols f v rRow = [] from
    sourceBank_foreign blocks rows cols f v (.inl 0)]
  simp

theorem afterBank_cols (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    afterBank blocks rows cols f v rColCount =
      List.replicate (cols^blocks) true := by
  simp [afterBank,bridgeAfter,moved,cRow,rRow,cColCount,rColCount,
    cWord,cTemp,rWord]
  change (sourceBank blocks rows cols f v cColCount).reverse ++
    sourceBank blocks rows cols f v rColCount =
      List.replicate (cols^blocks) true
  rw [sourceBank_cols]
  rw [show sourceBank blocks rows cols f v rColCount = [] from
    sourceBank_foreign blocks rows cols f v (.inl 1)]
  simp

theorem afterBank_word (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    afterBank blocks rows cols f v rWord =
      MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f) := by
  simp [afterBank,bridgeAfter,moved,cRow,rRow,cColCount,rColCount,
    cWord,cTemp,rWord]
  change (sourceBank blocks rows cols f v cTemp).reverse ++
    (sourceBank blocks rows cols f v cWord ++
      sourceBank blocks rows cols f v rWord) = _
  rw [sourceBank_temp,sourceBank_word]
  rw [show sourceBank blocks rows cols f v rWord = [] from
    sourceBank_foreign blocks rows cols f v (.inr 0)]
  simp

theorem afterBank_rowFrame (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (fun k : RStack => afterBank blocks rows cols f v (.inr k)) =
      (MatrixTableInterlaceRowWidth.cfg (some (.inl .outer))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate (cols^blocks) true)
        [] [] [] []
        (MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f))
        [] [] [] [] [] []).stk := by
  funext k
  have hrows : sourceBank blocks rows cols f v
      (.inl (.inr (.inl (.inl 0)))) = List.replicate rows true :=
    sourceBank_rows blocks rows cols f v
  have hcols : sourceBank blocks rows cols f v
      (.inl (.inr (.inr .cols))) = List.replicate (cols^blocks) true :=
    sourceBank_cols blocks rows cols f v
  have hword : sourceBank blocks rows cols f v
      (.inl (.inr (.inr .output))) =
        MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f) :=
    sourceBank_word blocks rows cols f v
  have htemp : sourceBank blocks rows cols f v
      (.inl (.inr (.inr .temp))) = [] :=
    sourceBank_temp blocks rows cols f v
  cases k with
  | inl i =>
      fin_cases i <;>
        simp [MatrixTableInterlaceRowWidth.cfg, afterBank,
          bridgeAfter, moved, cRow, rRow, cColCount, rColCount,
          cWord, cTemp, rWord, sourceBank_foreign,
          hrows, hcols]
  | inr i =>
      fin_cases i <;>
        simp [MatrixTableInterlaceRowWidth.cfg, afterBank,
          bridgeAfter, moved, cRow, rRow, cColCount, rColCount,
          cWord, cTemp, rWord, sourceBank_foreign,
          hword, htemp]

theorem combinedEnd_bridgeStart (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    combinedFrame (false,(none,SamplerMachineBlockReverse.initial))
      emptyRowBank (combinedEnd blocks rows cols f v) =
      ⟨some (.inr (.inl .rows)),
        ((MatrixTableInterlaceSize.initial,v),
          ((false,(none,SamplerMachineBlockReverse.initial)),none)),
        sourceBank blocks rows cols f v⟩ := by
  rfl

theorem bridgeEnd_rowFrame (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (⟨some rowStart,
      ((MatrixTableInterlaceSize.initial,v),
        ((false,(none,SamplerMachineBlockReverse.initial)),none)),
      afterBank blocks rows cols f v⟩ : Config) =
    rowFrame (MatrixTableInterlaceSize.initial,v)
      (fun k => afterBank blocks rows cols f v (.inl k))
      (MatrixTableInterlaceRowWidth.cfg (some (.inl .outer))
        (false,(none,SamplerMachineBlockReverse.initial))
        (List.replicate rows true) (List.replicate (cols^blocks) true)
        [] [] [] []
        (MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f))
        [] [] [] [] [] []) := by
  have h := afterBank_rowFrame blocks rows cols f v
  congr 1
  funext k
  cases k with
  | inl k => simp [rowFrame, renameCfg, liftCfg]
  | inr k => simpa [rowFrame, renameCfg, liftCfg] using congrFun h k

def rowEnd (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableInterlaceRowWidth.Config :=
  MatrixTableInterlaceRowWidth.cfg (some (.inr (.inr .check)))
    (false,(none,SamplerMachineBlockReverse.initial))
    (List.replicate rows true) (List.replicate (cols^blocks) true)
    [] [] [] (List.replicate (rows*(cols^blocks)) true)
    [] [] [] [] []
    (MatrixMaterialization.rowMajor
      (MatrixTableInterlaceRowReverse.numberedInterlace blocks rows cols f))
    []

theorem first_interlace_numbered_run (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks)) :
    ∃ t ≤
      MatrixTableInterlaceCombined.totalBound blocks rows cols
        (MatrixMaterialization.rowMajor f).length +
      ((rows+1)+((cols^blocks)+1)+
        ((MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+1)+
        ((MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+1)) +
      (MatrixAddressMachine.exactTime rows (cols^blocks) 0 +
        (2*(MatrixMaterialization.rowMajor
          (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+2 +
          blocks*SamplerMachineBlockReverse.blockStep (rows*(cols^blocks)))),
      ∃ v : MatrixTableInterlaceCombined.WControl,
        run t (combinedFrame
          (false,(none,SamplerMachineBlockReverse.initial)) emptyRowBank
          (MatrixTableInterlaceCombined.bridgeCfg
            MatrixTableInterlaceCombined.start blocks rows cols
            (MatrixMaterialization.rowMajor f) [] [] [] [] [])) =
        rowFrame (MatrixTableInterlaceSize.initial,v)
          (fun k => afterBank blocks rows cols f v (.inl k))
          (rowEnd blocks rows cols f) := by
  obtain ⟨t₁,ht₁,v,h₁⟩ := combined_phase blocks rows cols f
  rw [combinedEnd_bridgeStart] at h₁
  have h₂ := bridge_run rows (cols^blocks)
    (MatrixMaterialization.rowMajor
      (MatrixTableInterlace.interlaced (blocks := blocks) f))
    (MatrixTableInterlaceSize.initial,v)
    (false,(none,SamplerMachineBlockReverse.initial))
    (sourceBank blocks rows cols f v)
    (sourceBank_rows blocks rows cols f v)
    (sourceBank_cols blocks rows cols f v)
    (sourceBank_word blocks rows cols f v)
    (sourceBank_temp blocks rows cols f v)
  rw [show bridgeAfter (sourceBank blocks rows cols f v) =
      afterBank blocks rows cols f v from rfl] at h₂
  rw [bridgeEnd_rowFrame] at h₂
  obtain ⟨t₃,ht₃,h₃⟩ := row_phase blocks rows cols f hwidth
    (MatrixTableInterlaceSize.initial,v)
    (fun k => afterBank blocks rows cols f v (.inl k))
  change run t₃ (rowFrame _ _ _) = rowFrame _ _ (rowEnd blocks rows cols f) at h₃
  let t₂ := ((rows+1)+((cols^blocks)+1)+
    ((MatrixMaterialization.rowMajor
      (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+1)+
    ((MatrixMaterialization.rowMajor
      (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+1))
  have h₁₂ := run_add h₁ t₂
  rw [h₂] at h₁₂
  have h₁₂₃ := run_add h₁₂ t₃
  rw [h₃] at h₁₂₃
  refine ⟨t₁+t₂+t₃, ?_, v, ?_⟩
  · omega
  · simpa only [Nat.add_assoc] using h₁₂₃

end EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstRestoration
