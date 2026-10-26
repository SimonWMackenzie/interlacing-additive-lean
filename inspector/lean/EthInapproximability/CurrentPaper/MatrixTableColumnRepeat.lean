import EthInapproximability.CurrentPaper.MatrixIndexQuotient
import EthInapproximability.CurrentPaper.MatrixTableLookup
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-!
# Physical repeated-column table writer

Source: frozen v8 `B-effectivity-details.tex`, uniform copy index in
`thm:paper-materialization`.  A new column label `y` contains a copy index
inside each old column: `y / copies` is its source column.  The callback
computes this quotient on unary stacks, looks up the old row-major cell,
and clears its quotient.  The writer then enumerates every repeated cell.

This is the uniform-copy primitive, not the full 182:2 protected blow-up:
the latter still needs group-weight and support decoding.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableColumnRepeat

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev Stack := Fin 17
abbrev Label := MatrixIndexQuotient.Label ⊕ (MatrixTableLookup.Label ⊕ Unit)
abbrev Control := MatrixIndexQuotient.Control × MatrixTableLookup.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (MatrixIndexQuotient.initial, MatrixTableLookup.initial)
def start : Label := .inl MatrixIndexQuotient.start
def lookupStart : Label := .inr (.inl MatrixTableLookup.start)
def clear : Label := .inr (.inr ())

def quotientStacks : MatrixIndexQuotient.Stack ⊕ Fin 9 ≃ Stack := finSumFinEquiv

def lookupPermutation : Stack ≃ Stack where
  toFun := ![8,9,6,10,11,12,13,14,15,16,0,1,2,3,4,5,7]
  invFun := ![10,11,12,13,14,15,2,16,0,1,3,4,5,6,7,8,9]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def lookupStacks : MatrixTableLookup.Stack ⊕ Fin 7 ≃ Stack :=
  finSumFinEquiv.trans lookupPermutation

def lookupLabels : MatrixTableLookup.Label ⊕ (MatrixIndexQuotient.Label ⊕ Unit) ≃ Label where
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
  | .inl l => renameStmt quotientStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixTableLookup.start))
        (MatrixIndexQuotient.program l))
  | .inr (.inl l) => renameStmt lookupStacks lookupLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixTableLookup.program l))
  | .inr (.inr ()) => pop 6 (fun v b => (v.1, (b.isSome, v.2.2)))
      (branch (fun v => v.2.1)
        (goto (fun _ => clear)) (load (fun _ => initial) halt))

def cfg (l : Option Label) (v : Control) (y copies x width source answer : List Bool)
    (quotient : List Bool := []) : Config :=
  ⟨l,v,![y,copies,[],[],[],[],quotient,[],x,width,[],[],[],source,answer,[],[]]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def quotientFrame (x width source answer : List Bool)
    (c : MatrixIndexQuotient.Config) : Config :=
  renameCfg quotientStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixTableLookup.start)) MatrixTableLookup.initial
      (fun i => ![x,width,[],[],[],source,answer,[],[]] i) c)

theorem quotient_run (y copies : ℕ) (x width source answer : List Bool) :
    ∃ t ≤ 11*y+3*copies+7,
      run t (cfg (some start) initial (List.replicate y true)
        (List.replicate copies true) x width source answer) =
      cfg (some lookupStart) initial (List.replicate y true)
        (List.replicate copies true) x width source answer
        (List.replicate (y/copies) true) := by
  have he := MatrixIndexQuotient.quotient_run y copies
  obtain ⟨a,ha,hh⟩ := he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed quotientStacks
    (Equiv.refl _) (Equiv.refl _) MatrixIndexQuotient.program program
    (some (.inl MatrixTableLookup.start)) (fun _ => rfl)
    MatrixTableLookup.initial (fun i => ![x,width,[],[],[],source,answer,[],[]] i)
    (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
      MatrixIndexQuotient.initial (List.replicate y true)
      (List.replicate copies true) [] [] [] [] [] []) a
    (by rw [show ((advance MatrixIndexQuotient.program)^[a]) _ = _ from hh]; rfl)
  change run t (quotientFrame x width source answer _) =
    quotientFrame x width source answer (MatrixIndexQuotient.run _ _) at hr
  rw [hh] at hr
  have hi : quotientFrame x width source answer
      (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
        MatrixIndexQuotient.initial (List.replicate y true)
        (List.replicate copies true) [] [] [] [] [] []) =
      cfg (some start) initial (List.replicate y true)
        (List.replicate copies true) x width source answer := by
    unfold quotientFrame renameCfg liftCfg cfg MatrixIndexQuotient.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : quotientFrame x width source answer
      (MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial
        (List.replicate y true) (List.replicate copies true)
        [] [] [] [] (List.replicate (y/copies) true) []) =
      cfg (some lookupStart) initial (List.replicate y true)
        (List.replicate copies true) x width source answer
        (List.replicate (y/copies) true) := by
    unfold quotientFrame renameCfg liftCfg cfg MatrixIndexQuotient.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht.trans ha,by simpa only [hi,hf] using hr⟩

def lookupFrame (y copies : List Bool) (c : MatrixTableLookup.Config) : Config :=
  renameCfg lookupStacks lookupLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) MatrixIndexQuotient.initial
      (fun i => ![y,copies,[],[],[],[],[]] i) c)

theorem lookup_run (y copies x width : ℕ) (source answer : List Bool) :
    ∃ t ≤ 32*(x+width+y/copies+source.length+1)^2,
      run t (cfg (some lookupStart) initial (List.replicate y true)
        (List.replicate copies true) (List.replicate x true)
        (List.replicate width true) source answer
        (List.replicate (y/copies) true)) =
      cfg (some clear) initial (List.replicate y true)
        (List.replicate copies true) (List.replicate x true)
        (List.replicate width true) source
        (source[x*width+y/copies]?.getD false::answer)
        (List.replicate (y/copies) true) := by
  have he := MatrixTableLookup.lookup_run x width (y/copies) source answer
  obtain ⟨a,ha,hh⟩ := he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed lookupStacks lookupLabels
    (Equiv.prodComm _ _) MatrixTableLookup.program program
    (some (.inr ())) (fun _ => rfl) MatrixIndexQuotient.initial
    (fun i => ![List.replicate y true,List.replicate copies true,[],[],[],[],[]] i)
    (MatrixTableLookup.cfg (some MatrixTableLookup.start)
      MatrixTableLookup.initial (List.replicate x true)
      (List.replicate width true) (List.replicate (y/copies) true) [] source answer)
    a (by rw [show ((advance MatrixTableLookup.program)^[a]) _ = _ from hh]; rfl)
  change run t (lookupFrame (List.replicate y true)
    (List.replicate copies true) _) =
    lookupFrame (List.replicate y true) (List.replicate copies true)
      (MatrixTableLookup.run _ _) at hr
  rw [hh] at hr
  have hi : lookupFrame (List.replicate y true) (List.replicate copies true)
      (MatrixTableLookup.cfg (some MatrixTableLookup.start)
        MatrixTableLookup.initial (List.replicate x true)
        (List.replicate width true) (List.replicate (y/copies) true) [] source answer) =
      cfg (some lookupStart) initial (List.replicate y true)
        (List.replicate copies true) (List.replicate x true)
        (List.replicate width true) source answer
        (List.replicate (y/copies) true) := by
    unfold lookupFrame renameCfg liftCfg cfg MatrixTableLookup.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : lookupFrame (List.replicate y true) (List.replicate copies true)
      (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate x true) (List.replicate width true)
        (List.replicate (y/copies) true) [] source
        (source[x*width+y/copies]?.getD false::answer)) =
      cfg (some clear) initial (List.replicate y true)
        (List.replicate copies true) (List.replicate x true)
        (List.replicate width true) source
        (source[x*width+y/copies]?.getD false::answer)
        (List.replicate (y/copies) true) := by
    unfold lookupFrame renameCfg liftCfg cfg MatrixTableLookup.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht.trans ha,by simpa only [hi,hf] using hr⟩

theorem clear_run (y copies x width source answer quotient : List Bool) (v : Control) :
    run (quotient.length+1)
      (cfg (some clear) v y copies x width source answer quotient) =
      cfg none initial y copies x width source answer := by
  induction quotient generalizing v with
  | nil => simp [run,advance,cfg,clear,program,TM2.step,TM2.stepAux]
  | cons b quotient ih =>
      have hs : advance program (cfg (some clear) v y copies x width source answer
          (b::quotient)) =
          cfg (some clear) (v.1,(true,v.2.2)) y copies x width source answer quotient := by
        simp [advance,cfg,clear,program,TM2.step,TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons,run,Function.iterate_succ_apply,hs]
      exact ih (v.1,(true,v.2.2))

def callbackBound (rows cols copies sourceLength : ℕ) : ℕ :=
  80 * (rows + cols + copies + sourceLength + 1) ^ 2

/-- One physical repeated-column lookup; the copy index and source table
are preserved.  The bound includes quotient, address, read and cleanup. -/
theorem repeat_lookup_run (x y width copies : ℕ) (source answer : List Bool) :
    ∃ t ≤ callbackBound x y copies (width+source.length),
      run t (cfg (some start) initial (List.replicate y true)
        (List.replicate copies true) (List.replicate x true)
        (List.replicate width true) source answer) =
      cfg none initial (List.replicate y true)
        (List.replicate copies true) (List.replicate x true)
        (List.replicate width true) source
        (source[x*width+y/copies]?.getD false::answer) := by
  obtain ⟨a,ha,he⟩ := quotient_run y copies (List.replicate x true)
    (List.replicate width true) source answer
  obtain ⟨b,hb,hr⟩ := lookup_run y copies x width source answer
  have hc := clear_run (List.replicate y true) (List.replicate copies true)
    (List.replicate x true) (List.replicate width true) source
    (source[x*width+y/copies]?.getD false::answer)
    (List.replicate (y/copies) true) initial
  simp only [List.length_replicate] at hc
  refine ⟨a+(b+(y/copies+1)),?_,?_⟩
  · let n := x+y+copies+(width+source.length)+1
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hx : x ≤ n := by dsimp [n]; omega
    have hy0 : y ≤ n := by dsimp [n]; omega
    have hc0 : copies ≤ n := by dsimp [n]; omega
    have hy : y/copies ≤ y := Nat.div_le_self _ _
    have hq : x+width+y/copies+source.length+1 ≤ n := by dsimp [n]; omega
    have hsq := Nat.pow_le_pow_left hq 2
    have hn2 : n ≤ n ^ 2 := by nlinarith [Nat.mul_le_mul (le_refl n) hn]
    change a+(b+(y/copies+1)) ≤ 80*n^2
    nlinarith
  · rw [run_add he,run_add hr,hc]

abbrev CellStack := MatrixTableWriter.CellStack 14

private def writerPermutation : Stack ≃ Stack where
  toFun := ![1,2,3,4,5,6,7,9,10,11,12,13,15,16,8,0,14]
  invFun := ![15,0,1,2,3,4,5,6,14,7,8,9,10,11,16,12,13]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def writerSlots : CellStack ≃ Stack := finSumFinEquiv.trans writerPermutation

def entryProgram (l : Label) : TM2.Stmt (fun _ : CellStack => Bool) Label Control :=
  renameStmt writerSlots.symm (Equiv.refl _) (Equiv.refl _) (program l)

def persistentBank (copies width : ℕ) (source : List Bool) : Fin 14 → List Bool :=
  ![List.replicate copies true, [], [], [], [], [], [],
    List.replicate width true, [], [], [], source, [], []]

theorem input_frame (copies width x y : ℕ) (source answer : List Bool)
    (l : Option Label) (s : Control) :
    renameCfg writerSlots.symm (Equiv.refl _) (Equiv.refl _)
      (cfg l s (List.replicate y true) (List.replicate copies true)
        (List.replicate x true) (List.replicate width true) source answer) =
      MatrixTableWriter.cellCfg l s (persistentBank copies width source) x y answer := by
  unfold renameCfg cfg MatrixTableWriter.cellCfg
  cases l with
  | none =>
      apply congrArg
        (fun S => (⟨none, s, S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | some l =>
      apply congrArg
        (fun S => (⟨some l, s, S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl

theorem renamed_run {copies width x y t : ℕ} {source answer : List Bool}
    {s : Control}
    (h : run t (cfg (some start) initial (List.replicate y true)
      (List.replicate copies true) (List.replicate x true)
      (List.replicate width true) source []) =
      cfg none s (List.replicate y true) (List.replicate copies true)
        (List.replicate x true) (List.replicate width true) source answer) :
    ((advance entryProgram)^[t])
      (MatrixTableWriter.cellCfg (some start) initial
        (persistentBank copies width source) x y []) =
      MatrixTableWriter.cellCfg none s (persistentBank copies width source)
        x y answer := by
  have hr := rename_run writerSlots.symm (Equiv.refl Label) (Equiv.refl Control)
    program (cfg (some start) initial (List.replicate y true)
      (List.replicate copies true) (List.replicate x true)
      (List.replicate width true) source []) t
  change ((advance entryProgram)^[t]) _ =
    renameCfg writerSlots.symm (Equiv.refl _) (Equiv.refl _) (run t _) at hr
  rw [h, input_frame, input_frame] at hr
  exact hr

def uniformBound (rows width copies sourceLength : ℕ) : ℕ :=
  callbackBound rows (width*copies) copies (width+sourceLength)

theorem entry_runs (rows width copies : ℕ) (source : List Bool) :
    MatrixTableWriter.EntryRuns entryProgram start initial
      (persistentBank copies width source) rows (width*copies)
      (uniformBound rows width copies source.length)
      (fun x y => source[x*width+y/copies]?.getD false) := by
  intro x hx y hy
  obtain ⟨t,ht,he⟩ := repeat_lookup_run x y width copies source []
  refine ⟨t, ?_, initial, renamed_run he⟩
  have hle : x+y+copies+(width+source.length)+1 ≤
      rows+(width*copies)+copies+(width+source.length)+1 := by omega
  have hpow := Nat.pow_le_pow_left hle 2
  change t ≤ 80 * (x+y+copies+(width+source.length)+1)^2 at ht
  change t ≤ 80 * (rows+(width*copies)+copies+(width+source.length)+1)^2
  exact ht.trans (Nat.mul_le_mul_left 80 hpow)

/-- Literal row-major table with each original column repeated `copies`
times.  All source bits, dimensions, and old output suffix survive. -/
theorem repeat_table (rows width copies : ℕ) (source output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound rows (width*copies)
      (uniformBound rows width copies source.length), ∃ v,
      MatrixTableWriter.run entryProgram start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready (persistentBank copies width source)
            rows (width*copies) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank copies width source)
          rows (width*copies) 0 0 0 0 []
          (MatrixTableWriter.tableWord
            (fun x y => source[x*width+y/copies]?.getD false)
            (width*copies) 0 rows ++ output)) := by
  exact MatrixTableWriter.write_table entryProgram start initial
    (persistentBank copies width source) rows (width*copies)
    (uniformBound rows width copies source.length)
    (fun x y => source[x*width+y/copies]?.getD false)
    (entry_runs rows width copies source) output

end EthInapproximability.CurrentPaper.MatrixTableColumnRepeat
