import EthInapproximability.CurrentPaper.MatrixWeightedOrderWriter
import EthInapproximability.CurrentPaper.MatrixTableInterlaceOuterJoin

/-!
# Charged protected-table handoff

The weighted protected-table writer, a finite transfer controller, and the
outer-width/double-interlace controller share one Boolean-stack program.
The transfer controller copies each unary dimension header to both first
restoration consumers and reverses the protected table twice, retaining its
row-major order.  Its output is stated for the literal typed-decoder table;
agreement with the separate `Iteration` numbering is proved elsewhere.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceProtectedBridge

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev WStack := MatrixWeightedOrderWriter.Stack
abbrev OStack := MatrixTableInterlaceOuterJoin.Stack
abbrev Stack := WStack ⊕ OStack
abbrev WLabel := MatrixWeightedOrderWriter.Label
abbrev OLabel := MatrixTableInterlaceOuterJoin.Label
abbrev WControl := MatrixWeightedOrderWriter.Control
abbrev OControl := MatrixTableInterlaceOuterJoin.Control

inductive Bridge where
  | rows | cols | wordTemp | wordTarget
  deriving DecidableEq, Fintype

abbrev Label := WLabel ⊕ (Bridge ⊕ OLabel)
abbrev Control := WControl × (OControl × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable local instance : DecidableEq Stack := Classical.decEq Stack

def wRows : Stack := .inl (.inr .rows)
def wCols : Stack := .inl (.inr .cols)
def wWord : Stack := .inl (.inr .output)
def wTemp : Stack := .inl (.inr .buffer)

def firstCombined (k : MatrixTableInterlaceCombined.Stack) : Stack :=
  .inr (.inr (.inr (.inl (.inl (.inl k)))))

def sizeRows : Stack := firstCombined (.inl 1)
def sizeCols : Stack := firstCombined (.inl 2)
def writerRows : Stack := firstCombined (.inr (.inl (.inl 0)))
def writerCols : Stack := firstCombined (.inr (.inl (.inl 7)))
def writerSource : Stack := firstCombined (.inr (.inl (.inl 17)))

def start : Label := .inl (BitMachineRawSequence.leftLabel
  MatrixWeightedOrderPreparation.start)
noncomputable def outerStart : Label :=
  .inr (.inr (.inl MatrixOuterWidthMachine.machine.start))

def outerLabels : OLabel ⊕ (WLabel ⊕ Bridge) ≃ Label where
  toFun
    | .inl l => .inr (.inr l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inl l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr l)
    | .inr (.inr l) => .inl l
  left_inv k := by rcases k with k | (k | k) <;> rfl
  right_inv k := by rcases k with k | (k | k) <;> rfl

def outerControl : OControl × (WControl × Option Bool) ≃ Control where
  toFun := fun v => (v.2.1,(v.1,v.2.2))
  invFun := fun v => (v.2.1,(v.1,v.2.2))
  left_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl
  right_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl

def duplicate (source target₁ target₂ : Stack) (again next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop source (fun v b => (v.1,(v.2.1,b)))
    (branch (fun v => v.2.2.isSome)
      (push target₁ (fun v => v.2.2.getD false)
        (push target₂ (fun v => v.2.2.getD false)
          (goto (fun _ => again))))
      (load (fun v => (v.1,(v.2.1,none)))
        (goto (fun _ => next))))

def move (source target : Stack) (again next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop source (fun v b => (v.1,(v.2.1,b)))
    (branch (fun v => v.2.2.isSome)
      (push target (fun v => v.2.2.getD false)
        (goto (fun _ => again)))
      (load (fun v => (v.1,(v.2.1,none)))
        (goto (fun _ => next))))

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl Bridge.rows))
      (MatrixWeightedOrderWriter.program l)
  | .inr (.inl .rows) => duplicate wRows sizeRows writerRows
      (.inr (.inl .rows)) (.inr (.inl .cols))
  | .inr (.inl .cols) => duplicate wCols sizeCols writerCols
      (.inr (.inl .cols)) (.inr (.inl .wordTemp))
  | .inr (.inl .wordTemp) => move wWord wTemp
      (.inr (.inl .wordTemp)) (.inr (.inl .wordTarget))
  | .inr (.inl .wordTarget) => move wTemp writerSource
      (.inr (.inl .wordTarget)) outerStart
  | .inr (.inr l) => renameStmt (Equiv.sumComm OStack WStack)
      outerLabels outerControl
      (liftStmt none (MatrixTableInterlaceOuterJoin.program l))

noncomputable def run (t : ℕ) (c : Config) : Config := by
  classical
  exact ((@advance Stack Label Control
    (@instDecidableEqSum WStack OStack inferInstance inferInstance)
    program)^[t]) c

noncomputable def writerFrame (d : MatrixTableInterlaceOuterJoin.Config)
    (c : MatrixWeightedOrderWriter.Config) : Config := by
  classical
  exact liftCfg (some (.inl Bridge.rows)) (d.var,none) d.stk c

noncomputable def outerFrame (c : MatrixWeightedOrderWriter.Config)
    (d : MatrixTableInterlaceOuterJoin.Config) : Config := by
  classical
  exact renameCfg (Equiv.sumComm OStack WStack) outerLabels outerControl
    (liftCfg none (c.var,none) c.stk d)

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem move_cons (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v : WControl) (w : OControl)
    (s : Option Bool) (S : Stack → List Bool) (b : Bool) (bits : List Bool)
    (hs : S source = b::bits) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some again,(v,(w,some b)),
        Function.update (Function.update S source bits)
          target (b::S target)⟩ := by
  classical
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs]
  funext k
  by_cases ht : k = target
  · subst k
    simp [Function.update_apply,hne,Ne.symm hne]
  · by_cases hsrc : k = source
    · subst k
      simp [Function.update_apply,ht,hne,Ne.symm hne]
    · simp [Function.update_apply,ht,hsrc]

private theorem move_nil (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (v : WControl) (w : OControl)
    (s : Option Bool) (S : Stack → List Bool) (hs : S source = []) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),S⟩ := by
  classical
  have hu : Function.update S source [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run, advance, TM2.step, TM2.stepAux, hprog, move, hs, hu]

theorem move_run (source target : Stack) (again next : Label)
    (hprog : program again = move source target again next)
    (hne : source ≠ target)
    (v : WControl) (w : OControl)
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

private theorem duplicate_cons (source target₁ target₂ : Stack)
    (again next : Label)
    (hprog : program again = duplicate source target₁ target₂ again next)
    (hne₁ : source ≠ target₁) (hne₂ : source ≠ target₂)
    (h12 : target₁ ≠ target₂)
    (v : WControl) (w : OControl) (s : Option Bool)
    (S : Stack → List Bool) (n : ℕ)
    (hs : S source = true :: List.replicate n true) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some again,(v,(w,some true)),
        Function.update
          (Function.update
            (Function.update S source (List.replicate n true))
            target₁ (true :: S target₁))
          target₂ (true :: S target₂)⟩ := by
  classical
  simp [run,advance,TM2.step,TM2.stepAux,hprog,duplicate,hs]
  funext k
  by_cases hf : k = target₂
  · subst k
    simp [Function.update_apply,hne₁,hne₂,h12,
      Ne.symm hne₁,Ne.symm hne₂,Ne.symm h12]
  · by_cases hr : k = target₁
    · subst k
      simp [Function.update_apply,hne₁,hne₂,h12,
        Ne.symm hne₁,Ne.symm hne₂,Ne.symm h12,hf]
    · simp [Function.update_apply,hne₁,hne₂,h12,hr,hf]

private theorem duplicate_nil (source target₁ target₂ : Stack)
    (again next : Label)
    (hprog : program again = duplicate source target₁ target₂ again next)
    (v : WControl) (w : OControl) (s : Option Bool)
    (S : Stack → List Bool) (hs : S source = []) :
    run 1 ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),S⟩ := by
  classical
  have hu : Function.update S source [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run,advance,TM2.step,TM2.stepAux,hprog,duplicate,hs,hu]

noncomputable def duplicated (S : Stack → List Bool)
    (source target₁ target₂ : Stack) (n : ℕ) : Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update S source [])
      target₁ (List.replicate n true ++ S target₁))
    target₂ (List.replicate n true ++ S target₂)

theorem duplicate_run (source target₁ target₂ : Stack)
    (again next : Label)
    (hprog : program again = duplicate source target₁ target₂ again next)
    (hne₁ : source ≠ target₁) (hne₂ : source ≠ target₂)
    (h12 : target₁ ≠ target₂)
    (v : WControl) (w : OControl) (s : Option Bool)
    (n : ℕ) (S : Stack → List Bool)
    (hs : S source = List.replicate n true) :
    run (n+1) ⟨some again,(v,(w,s)),S⟩ =
      ⟨some next,(v,(w,none)),duplicated S source target₁ target₂ n⟩ := by
  induction n generalizing S s with
  | zero =>
      have hn := duplicate_nil source target₁ target₂ again next hprog
        v w s S (by simpa using hs)
      have hu1 : Function.update S source [] = S :=
        Function.update_eq_self_iff.mpr (by simpa using hs.symm)
      have hu2 : Function.update S target₁ (S target₁) = S :=
        Function.update_eq_self_iff.mpr rfl
      have hu3 : Function.update S target₂ (S target₂) = S :=
        Function.update_eq_self_iff.mpr rfl
      simpa only [duplicated,List.replicate_zero,List.nil_append,
        hu1,hu2,hu3] using hn
  | succ n ih =>
      let S' := Function.update
        (Function.update
          (Function.update S source (List.replicate n true))
          target₁ (true :: S target₁))
        target₂ (true :: S target₂)
      have hs' : S' source = List.replicate n true := by
        simp [S',hne₁,hne₂,h12]
      have h1 := duplicate_cons source target₁ target₂ again next
        hprog hne₁ hne₂ h12 v w s S n hs
      have h2 := (run_add h1 (n+1)).trans (ih (some true) S' hs')
      have hupdate : duplicated S' source target₁ target₂ n =
          duplicated S source target₁ target₂ (n+1) := by
        funext k
        by_cases hf : k = target₂
        · subst k
          simp [duplicated,S',Function.update_apply,hne₁,hne₂,h12,
            List.replicate_add,List.append_assoc]
        · by_cases hr : k = target₁
          · subst k
            simp [duplicated,S',Function.update_apply,hne₁,hne₂,h12,
              hf,List.replicate_add,List.append_assoc]
          · by_cases hsrc : k = source
            · subst k
              simp [duplicated,S',Function.update_apply,hne₁,hne₂,h12,
                hf,hr]
            · simp [duplicated,S',Function.update_apply,hf,hr,hsrc]
      rw [hupdate] at h2
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using h2

noncomputable def moved (S : Stack → List Bool) (source target : Stack) :
    Stack → List Bool :=
  Function.update (Function.update S source []) target
    ((S source).reverse ++ S target)

noncomputable def bridgeAfter (S : Stack → List Bool) (rows cols : ℕ) :
    Stack → List Bool :=
  moved
    (moved
      (duplicated
        (duplicated S wRows sizeRows writerRows rows)
        wCols sizeCols writerCols cols)
      wWord wTemp)
    wTemp writerSource

theorem bridge_run (rows cols : ℕ) (word : List Bool)
    (v : WControl) (w : OControl) (S : Stack → List Bool)
    (hr : S wRows = List.replicate rows true)
    (hc : S wCols = List.replicate cols true)
    (hw : S wWord = word)
    (htemp : S wTemp = []) :
    run ((rows+1)+(cols+1)+(word.length+1)+(word.length+1))
      ⟨some (.inr (.inl .rows)),(v,(w,none)),S⟩ =
    ⟨some outerStart,(v,(w,none)),bridgeAfter S rows cols⟩ := by
  let S1 := duplicated S wRows sizeRows writerRows rows
  let S2 := duplicated S1 wCols sizeCols writerCols cols
  let S3 := moved S2 wWord wTemp
  have hcol : S1 wCols = List.replicate cols true := by
    calc
      S1 wCols = S wCols := by
        simp [S1,duplicated,wRows,sizeRows,writerRows,wCols,
          firstCombined,Function.update_apply]
      _ = List.replicate cols true := hc
  have hword : S2 wWord = word := by
    calc
      S2 wWord = S wWord := by
        simp [S2,S1,duplicated,wRows,sizeRows,writerRows,
          wCols,sizeCols,writerCols,wWord,firstCombined,Function.update_apply]
      _ = word := hw
  have htemp3 : S3 wTemp = word.reverse := by
    have htemp2 : S2 wTemp = [] := by
      calc
        S2 wTemp = S wTemp := by
          simp [S2,S1,duplicated,wRows,sizeRows,writerRows,
            wCols,sizeCols,writerCols,wTemp,firstCombined,Function.update_apply]
        _ = [] := htemp
    calc
      S3 wTemp = (S2 wWord).reverse ++ S2 wTemp := by
        simp [S3,moved,wWord,wTemp]
      _ = word.reverse := by simp [hword,htemp2]
  have h1raw := duplicate_run wRows sizeRows writerRows
    (.inr (.inl .rows)) (.inr (.inl .cols))
    rfl (by simp [wRows,sizeRows,firstCombined])
    (by simp [wRows,writerRows,firstCombined])
    (by simp [sizeRows,writerRows,firstCombined])
    v w none rows S hr
  have h1 : run (rows+1)
      ⟨some (.inr (.inl .rows)),(v,(w,none)),S⟩ =
      ⟨some (.inr (.inl .cols)),(v,(w,none)),S1⟩ := by
    simpa [S1] using h1raw
  have h2raw := duplicate_run wCols sizeCols writerCols
    (.inr (.inl .cols)) (.inr (.inl .wordTemp))
    rfl (by simp [wCols,sizeCols,firstCombined])
    (by simp [wCols,writerCols,firstCombined])
    (by simp [sizeCols,writerCols,firstCombined])
    v w none cols S1 hcol
  have h2 : run (cols+1)
      ⟨some (.inr (.inl .cols)),(v,(w,none)),S1⟩ =
      ⟨some (.inr (.inl .wordTemp)),(v,(w,none)),S2⟩ := by
    simpa [S2] using h2raw
  have h3raw := move_run wWord wTemp
    (.inr (.inl .wordTemp)) (.inr (.inl .wordTarget))
    rfl (by simp [wWord,wTemp]) v w none word S2 hword
  have h3 : run (word.length+1)
      ⟨some (.inr (.inl .wordTemp)),(v,(w,none)),S2⟩ =
      ⟨some (.inr (.inl .wordTarget)),(v,(w,none)),S3⟩ := by
    simpa [S3,moved,hword] using h3raw
  have h4raw := move_run wTemp writerSource
    (.inr (.inl .wordTarget)) outerStart rfl
    (by simp [wTemp,writerSource,firstCombined])
    v w none word.reverse S3 htemp3
  have h4 : run (word.length+1)
      ⟨some (.inr (.inl .wordTarget)),(v,(w,none)),S3⟩ =
      ⟨some outerStart,(v,(w,none)),bridgeAfter S rows cols⟩ := by
    change run (word.length+1) _ =
      ⟨some outerStart,(v,(w,none)),moved S3 wTemp writerSource⟩
    simpa only [moved,htemp3,List.length_reverse] using h4raw
  have h := run_add h1 (cols+1)
  rw [h2] at h
  have h' := run_add h (word.length+1)
  rw [h3] at h'
  have h'' := run_add h' (word.length+1)
  rw [h4] at h''
  simpa only [bridgeAfter,S1,S2,S3,List.length_reverse,
    Nat.add_assoc] using h''

theorem writer_phase (d : MatrixTableInterlaceOuterJoin.Config)
    (c cf : MatrixWeightedOrderWriter.Config) (t : ℕ)
    (hrun : MatrixWeightedOrderWriter.run t c = cf)
    (hh : cf.l = none) :
    ∃ u ≤ t, run u (writerFrame d c) = writerFrame d cf := by
  have hhalt : (MatrixWeightedOrderWriter.run t c).l = none := by
    rw [hrun]
    exact hh
  obtain ⟨u,hu,he⟩ := lift_outputs
    MatrixWeightedOrderWriter.program program
    (some (.inl Bridge.rows)) (fun _ => rfl)
    (d.var,none) d.stk c t hhalt
  have he' : run u (writerFrame d c) = writerFrame d
      (MatrixWeightedOrderWriter.run t c) := by
    simpa only [run,writerFrame,MatrixWeightedOrderWriter.run,
      instDecidableEqStack] using he
  rw [hrun] at he'
  exact ⟨u,hu,he'⟩

theorem writer_rows (rows cols : ℕ) (S : Fin 64 → List Bool)
    (output : List Bool) :
    (MatrixTableWriter.ready S rows cols 0 0 0 0 [] output).contents
      (.inr .rows) = List.replicate rows true := rfl

theorem writer_cols (rows cols : ℕ) (S : Fin 64 → List Bool)
    (output : List Bool) :
    (MatrixTableWriter.ready S rows cols 0 0 0 0 [] output).contents
      (.inr .cols) = List.replicate cols true := rfl

theorem writer_word (rows cols : ℕ) (S : Fin 64 → List Bool)
    (output : List Bool) :
    (MatrixTableWriter.ready S rows cols 0 0 0 0 [] output).contents
      (.inr .output) = output := rfl

theorem writer_temp (rows cols : ℕ) (S : Fin 64 → List Bool)
    (output : List Bool) :
    (MatrixTableWriter.ready S rows cols 0 0 0 0 [] output).contents
      (.inr .buffer) = [] := rfl

theorem bridgeAfter_sizeRows (S : Stack → List Bool)
    (rows cols : ℕ) (word : List Bool)
    (hr : S wRows = List.replicate rows true)
    (h₀ : S sizeRows = []) :
    bridgeAfter S rows cols sizeRows = List.replicate rows true := by
  simp only [sizeRows,firstCombined] at h₀
  simp [bridgeAfter,moved,duplicated,wRows,wCols,wWord,wTemp,
    sizeRows,sizeCols,writerRows,writerCols,writerSource,firstCombined,
    Function.update_apply,hr,h₀]

theorem bridgeAfter_writerRows (S : Stack → List Bool)
    (rows cols : ℕ)
    (h₀ : S writerRows = []) :
    bridgeAfter S rows cols writerRows = List.replicate rows true := by
  simp only [writerRows,firstCombined] at h₀
  simp [bridgeAfter,moved,duplicated,wRows,wCols,wWord,wTemp,
    sizeRows,sizeCols,writerRows,writerCols,writerSource,firstCombined,
    Function.update_apply,h₀]

theorem bridgeAfter_sizeCols (S : Stack → List Bool)
    (rows cols : ℕ)
    (h₀ : S sizeCols = []) :
    bridgeAfter S rows cols sizeCols = List.replicate cols true := by
  simp only [sizeCols,firstCombined] at h₀
  simp [bridgeAfter,moved,duplicated,wRows,wCols,wWord,wTemp,
    sizeRows,sizeCols,writerRows,writerCols,writerSource,firstCombined,
    Function.update_apply,h₀]

theorem bridgeAfter_writerCols (S : Stack → List Bool)
    (rows cols : ℕ)
    (h₀ : S writerCols = []) :
    bridgeAfter S rows cols writerCols = List.replicate cols true := by
  simp only [writerCols,firstCombined] at h₀
  simp [bridgeAfter,moved,duplicated,wRows,wCols,wWord,wTemp,
    sizeRows,sizeCols,writerRows,writerCols,writerSource,firstCombined,
    Function.update_apply,h₀]

theorem bridgeAfter_source (S : Stack → List Bool)
    (rows cols : ℕ) (word : List Bool)
    (hw : S wWord = word) (ht : S wTemp = [])
    (h₀ : S writerSource = []) :
    bridgeAfter S rows cols writerSource = word := by
  simp only [writerSource,firstCombined] at h₀
  change S (.inl (.inr .output)) = word at hw
  change S (.inl (.inr .buffer)) = [] at ht
  simp [bridgeAfter,moved,duplicated,wRows,wCols,wWord,wTemp,
    sizeRows,sizeCols,writerRows,writerCols,writerSource,firstCombined,
    Function.update_apply,hw,ht,h₀]

def firstCombinedO (k : MatrixTableInterlaceCombined.Stack) : OStack :=
  .inr (.inr (.inl (.inl (.inl k))))

def oSizeRows : OStack := firstCombinedO (.inl 1)
def oSizeCols : OStack := firstCombinedO (.inl 2)
def oWriterRows : OStack := firstCombinedO (.inr (.inl (.inl 0)))
def oWriterCols : OStack := firstCombinedO (.inr (.inl (.inl 7)))
def oWriterSource : OStack := firstCombinedO (.inr (.inl (.inl 17)))

noncomputable def outerReady (B r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    MatrixTableInterlaceOuterJoin.Config :=
  MatrixTableInterlaceOuterJoin.outerFrame
    (MatrixTableInterlaceOuterJoin.emptyInner B r rows cols b c s f)
    (MatrixOuterWidthMachine.startCfg lambda)

theorem combined_source_update (r rows cols : ℕ)
    (f g : Fin rows → Fin cols → Bool) :
    (MatrixTableInterlaceCombined.bridgeCfg
      MatrixTableInterlaceCombined.start (2^r) rows cols
      (MatrixMaterialization.rowMajor f) [] [] [] [] []).stk =
    Function.update
      (MatrixTableInterlaceCombined.bridgeCfg
        MatrixTableInterlaceCombined.start (2^r) rows cols
        (MatrixMaterialization.rowMajor g) [] [] [] [] []).stk
      (.inr (.inl (.inl (17 : Fin 20))))
      (MatrixMaterialization.rowMajor f) := by
  funext k
  cases k with
  | inl k =>
      simp [MatrixTableInterlaceCombined.bridgeCfg,
        MatrixTableInterlaceCombined.cfg,Function.update_apply]
  | inr k =>
      cases k with
      | inr e =>
          cases e <;>
            simp [MatrixTableInterlaceCombined.bridgeCfg,
              MatrixTableInterlaceCombined.cfg,
              MatrixTableInterlaceCombined.writerData,
              MatrixTableWriter.Data.contents,
              MatrixTableWriter.Data.cell,
              MatrixTableWriter.Data.foreign,
              MatrixTableInterlace.persistentBank,Function.update_apply]
      | inl k =>
          cases k with
          | inr k =>
              fin_cases k <;>
                simp [MatrixTableInterlaceCombined.bridgeCfg,
                  MatrixTableInterlaceCombined.cfg,
                  MatrixTableInterlaceCombined.writerData,
                  MatrixTableWriter.Data.contents,
                  MatrixTableWriter.Data.cell,
                  MatrixTableWriter.Data.foreign,
                  Function.update_apply]
          | inl k =>
              fin_cases k <;>
                simp [MatrixTableInterlaceCombined.bridgeCfg,
                  MatrixTableInterlaceCombined.cfg,
                  MatrixTableInterlaceCombined.writerData,
                  MatrixTableWriter.Data.contents,
                  MatrixTableWriter.Data.cell,
                  MatrixTableWriter.Data.foreign,
                  MatrixTableInterlace.persistentBank,Function.update_apply]

theorem combined_other (r rows cols : ℕ)
    (f g : Fin rows → Fin cols → Bool)
    (k : MatrixTableInterlaceCombined.Stack)
    (hk : k ≠ (.inr (.inl (.inl (17 : Fin 20))))) :
    (MatrixTableInterlaceCombined.bridgeCfg
      MatrixTableInterlaceCombined.start (2^r) rows cols
      (MatrixMaterialization.rowMajor f) [] [] [] [] []).stk k =
    (MatrixTableInterlaceCombined.bridgeCfg
      MatrixTableInterlaceCombined.start (2^r) rows cols
      (MatrixMaterialization.rowMajor g) [] [] [] [] []).stk k := by
  rw [combined_source_update]
  exact Function.update_of_ne hk _ _

theorem outerReady_outer_bank (B r rows cols b c s lambda : ℕ)
    (f g : Fin rows → Fin cols → Bool)
    (k : MatrixOuterWidthMachine.Stack) :
    (outerReady B r rows cols b c s lambda f).stk (.inl k) =
      (outerReady B r rows cols b c s lambda g).stk (.inl k) := by
  simp [outerReady,MatrixTableInterlaceOuterJoin.outerFrame,
    renameCfg,liftCfg]

set_option maxRecDepth 4096 in
theorem outerReady_first_bank (B r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (k : MatrixTableInterlaceCombined.Stack)
    (hk : k ≠ (.inl (0 : Fin 11))) :
    (outerReady B r rows cols b c s lambda f).stk (firstCombinedO k) =
    (MatrixTableInterlaceCombined.bridgeCfg
      MatrixTableInterlaceCombined.start (2^r) rows cols
      (MatrixMaterialization.rowMajor f) [] [] [] [] []).stk k := by
  simp only [outerReady,firstCombinedO,
    MatrixTableInterlaceOuterJoin.outerFrame,
    MatrixTableInterlaceOuterJoin.emptyInner,
    MatrixTableInterlaceOuterJoin.readyInner,
    MatrixTableInterlaceScalarJoin.restorationFrame,
    MatrixTableInterlaceScalarJoin.emptyDouble,
    MatrixTableInterlaceDouble.firstFrame,
    MatrixTableInterlaceDouble.firstPrepared,
    MatrixTableInterlaceFirstTranspose.firstFrame,
    MatrixTableInterlaceFirstRestoration.combinedFrame,
    renameCfg,liftCfg]
  simp only [Sum.elim_inr,Sum.elim_inl]
  have hne :
      (Sum.inr (Sum.inl (Sum.inl (Sum.inl k)))) ≠
        MatrixTableInterlaceOuterJoin.firstSlot := by
    simpa [MatrixTableInterlaceOuterJoin.firstSlot,
      MatrixTableInterlaceOuterJoin.firstBlock] using hk
  rw [Function.update_of_ne hne]
  simp only [Sum.elim_inr,Sum.elim_inl]

noncomputable def emptyOuter (d : MatrixTableInterlaceOuterJoin.Config) :
    MatrixTableInterlaceOuterJoin.Config :=
  ⟨d.l,d.var,
    Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update d.stk oSizeRows []) oSizeCols [])
          oWriterRows [])
        oWriterCols [])
      oWriterSource []⟩

private theorem emptyOuter_bank (d : MatrixTableInterlaceOuterJoin.Config)
    (k : OStack) (hk : k = oSizeRows ∨ k = oSizeCols ∨
      k = oWriterRows ∨ k = oWriterCols ∨ k = oWriterSource) :
    (emptyOuter d).stk k = [] := by
  rcases hk with h | h | h | h | h <;> subst k <;>
    simp [emptyOuter,oSizeRows,oSizeCols,oWriterRows,oWriterCols,
      oWriterSource,firstCombinedO,Function.update_apply]

theorem emptyOuter_sizeRows (d : MatrixTableInterlaceOuterJoin.Config) :
    (emptyOuter d).stk oSizeRows = [] :=
  emptyOuter_bank d oSizeRows (Or.inl rfl)
theorem emptyOuter_sizeCols (d : MatrixTableInterlaceOuterJoin.Config) :
    (emptyOuter d).stk oSizeCols = [] :=
  emptyOuter_bank d oSizeCols (Or.inr (Or.inl rfl))
theorem emptyOuter_writerRows (d : MatrixTableInterlaceOuterJoin.Config) :
    (emptyOuter d).stk oWriterRows = [] :=
  emptyOuter_bank d oWriterRows (Or.inr (Or.inr (Or.inl rfl)))
theorem emptyOuter_writerCols (d : MatrixTableInterlaceOuterJoin.Config) :
    (emptyOuter d).stk oWriterCols = [] :=
  emptyOuter_bank d oWriterCols (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem emptyOuter_writerSource (d : MatrixTableInterlaceOuterJoin.Config) :
    (emptyOuter d).stk oWriterSource = [] :=
  emptyOuter_bank d oWriterSource
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem writerFrame_empty (d : MatrixTableInterlaceOuterJoin.Config)
    (c : MatrixWeightedOrderWriter.Config) :
    (writerFrame (emptyOuter d) c).stk sizeRows = [] ∧
    (writerFrame (emptyOuter d) c).stk sizeCols = [] ∧
    (writerFrame (emptyOuter d) c).stk writerRows = [] ∧
    (writerFrame (emptyOuter d) c).stk writerCols = [] ∧
    (writerFrame (emptyOuter d) c).stk writerSource = [] := by
  constructor
  · change (emptyOuter d).stk oSizeRows = []
    exact emptyOuter_sizeRows d
  constructor
  · change (emptyOuter d).stk oSizeCols = []
    exact emptyOuter_sizeCols d
  constructor
  · change (emptyOuter d).stk oWriterRows = []
    exact emptyOuter_writerRows d
  constructor
  · change (emptyOuter d).stk oWriterCols = []
    exact emptyOuter_writerCols d
  · change (emptyOuter d).stk oWriterSource = []
    exact emptyOuter_writerSource d

def transferTime (rows cols : ℕ) (word : List Bool) : ℕ :=
  (rows+1)+(cols+1)+(word.length+1)+(word.length+1)

theorem writer_bridge_run (d : MatrixTableInterlaceOuterJoin.Config)
    (c cf : MatrixWeightedOrderWriter.Config)
    (rows cols : ℕ) (word : List Bool) (N : ℕ)
    (hrun : ∃ t ≤ N, MatrixWeightedOrderWriter.run t c = cf)
    (hh : cf.l = none)
    (hr : cf.stk (.inr .rows) = List.replicate rows true)
    (hc : cf.stk (.inr .cols) = List.replicate cols true)
    (hw : cf.stk (.inr .output) = word)
    (htemp : cf.stk (.inr .buffer) = []) :
    ∃ t ≤ N + transferTime rows cols word,
      ∃ S : Stack → List Bool,
        run t (writerFrame (emptyOuter d) c) =
          ⟨some outerStart,(cf.var,((emptyOuter d).var,none)),S⟩ ∧
        S sizeRows = List.replicate rows true ∧
        S sizeCols = List.replicate cols true ∧
        S writerRows = List.replicate rows true ∧
        S writerCols = List.replicate cols true ∧
        S writerSource = word := by
  obtain ⟨tw,htw,hweighted⟩ := hrun
  obtain ⟨u,hu,hphase⟩ := writer_phase (emptyOuter d) c cf tw hweighted hh
  let S := (writerFrame (emptyOuter d) cf).stk
  have hSrows : S wRows = List.replicate rows true := by
    change cf.stk (.inr .rows) = _
    exact hr
  have hScols : S wCols = List.replicate cols true := by
    change cf.stk (.inr .cols) = _
    exact hc
  have hSword : S wWord = word := by
    change cf.stk (.inr .output) = _
    exact hw
  have hStemp : S wTemp = [] := by
    change cf.stk (.inr .buffer) = _
    exact htemp
  have hstart : writerFrame (emptyOuter d) cf =
      (⟨some (.inr (.inl .rows)),
        (cf.var,((emptyOuter d).var,none)),S⟩ : Config) := by
    cases cf with
    | mk l v stk =>
        cases l <;> simp_all [writerFrame,liftCfg,S]
  have hbridge := bridge_run rows cols word cf.var (emptyOuter d).var S
    hSrows hScols hSword hStemp
  have htotal := run_add hphase (transferTime rows cols word)
  rw [hstart] at htotal
  change run (u+transferTime rows cols word) _ =
    run ((rows+1)+(cols+1)+(word.length+1)+(word.length+1))
      ⟨some (.inr (.inl .rows)),
        (cf.var,((emptyOuter d).var,none)),S⟩ at htotal
  rw [hbridge] at htotal
  let T := bridgeAfter S rows cols
  have ⟨h₁,h₂,h₃,h₄,h₅⟩ := writerFrame_empty d cf
  refine ⟨u+transferTime rows cols word,?_,T,htotal,?_,?_,?_,?_,?_⟩
  · omega
  · exact bridgeAfter_sizeRows S rows cols word hSrows h₁
  · exact bridgeAfter_sizeCols S rows cols h₂
  · exact bridgeAfter_writerRows S rows cols h₃
  · exact bridgeAfter_writerCols S rows cols h₄
  · exact bridgeAfter_source S rows cols word hSword hStemp h₅

end EthInapproximability.CurrentPaper.MatrixTableInterlaceProtectedBridge
