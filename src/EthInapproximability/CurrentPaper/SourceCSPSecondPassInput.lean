import EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveRows
import EthInapproximability.CurrentPaper.SourceClauseRowWriterCleanup

/-!
# Physical input staging for a second CSP row pass

The validated raw suffix lives in the global controller's saved cell. This
bank adds a disjoint clause-writer accumulator. Two actual three-stack copies
stage the suffix in the writer's row-parser source cell and the unary vertex
count from the preserved cap; one final push restores the leading vertex bit.
No semantic row or clause list is inserted into the machine state.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPSecondPassInput

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable abbrev Stack (q : Nat) :=
  SourceCSPGlobalDecisionProgram.Stack q ⊕
    SourceClauseRowWriterOperands.Stack q

def globalEmbedding {q : Nat} :
    SourceCSPGlobalDecisionProgram.Stack q ↪ Stack q where
  toFun := Sum.inl
  inj' := by intro x y h; exact Sum.inl.inj h

def writerEmbedding {q : Nat} :
    SourceClauseRowWriterOperands.Stack q ↪ Stack q where
  toFun := Sum.inr
  inj' := by intro x y h; exact Sum.inr.inj h

def savedSource {q : Nat} : Stack q :=
  .inl SourceCSPGlobalDecisionProgram.savedSource

def capSource {q : Nat} : Stack q :=
  .inl SourceCSPHeaderRowBridge.capSource

def writerSource {q : Nat} : Stack q :=
  .inr (SourceClauseRowWriterCleanup.rowCell (.inr 0))

def writerVertex {q : Nat} : Stack q :=
  .inr SourceClauseRowWriterOperands.vertex

def work {q : Nat} : Stack q :=
  .inr SourceClauseRowWriterOperands.scratch

def sourceCopyEmbedding {q : Nat} : Fin 3 ↪ Stack q where
  toFun k := if k = 0 then savedSource else
    if k = 1 then writerSource else work
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp [savedSource, writerSource, work,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.scratch] at h <;> simp_all

def vertexCopyEmbedding {q : Nat} : Fin 3 ↪ Stack q where
  toFun k := if k = 0 then capSource else
    if k = 1 then writerVertex else work
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp [capSource, writerVertex, work,
        SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterOperands.scratch] at h <;> simp_all

def sourceCopyProgram {q : Nat} (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack q => Bool)
      BitMachineCopy.Label (Option Bool) :=
  stmt sourceCopyEmbedding id id id none (BitMachineCopy.program l)

def vertexCopyProgram {q : Nat} (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack q => Bool)
      BitMachineCopy.Label (Option Bool) :=
  stmt vertexCopyEmbedding id id id none (BitMachineCopy.program l)

def addVertexProgram {q : Nat} (_ : Unit) :
    TM2.Stmt (fun _ : Stack q => Bool) Unit Unit :=
  .push writerVertex (fun _ => true) .halt

abbrev CopyPairLabel := BitMachineRawSequence.Label
  BitMachineCopy.Label BitMachineCopy.Label

def copyPairProgram {q : Nat} :=
  BitMachineRawSequence.program (sourceCopyProgram (q := q))
    (vertexCopyProgram (q := q)) .scan none none

abbrev Label := BitMachineRawSequence.Label CopyPairLabel Unit
abbrev Control := (Option Bool × Option Bool) × Unit

def program {q : Nat} :=
  BitMachineRawSequence.program (copyPairProgram (q := q))
    (addVertexProgram (q := q)) () (none, none) ()

def copyProgram {q : Nat} (ι : Fin 3 ↪ Stack q)
    (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack q => Bool)
      BitMachineCopy.Label (Option Bool) :=
  stmt ι id id id none (BitMachineCopy.program l)

theorem copy_framed {q : Nat} (ι : Fin 3 ↪ Stack q)
    (before : Stack q → List Bool) (word : List Bool)
    (hsource : before (ι 0) = word)
    (htarget : before (ι 1) = [])
    (hwork : before (ι 2) = []) :
    ∃ t S, t ≤ 2 * word.length + 2 ∧
      ((advance (copyProgram ι))^[t])
        (⟨some .scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S (ι 0) = word ∧ S (ι 1) = word ∧ S (ι 2) = [] ∧
      (∀ k, k ≠ ι 0 → k ≠ ι 1 → k ≠ ι 2 → S k = before k) := by
  let localCfg := BitMachineCopy.cfg (some .scan) none word [] []
  have hlocal : ((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg = BitMachineCopy.cfg none none word word [] := by
    simpa only [BitMachineCopy.run, localCfg, List.append_nil] using
      BitMachineCopy.run_correct none word []
  have hhalt : (((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg).l = none := by rw [hlocal]; rfl
  obtain ⟨t, ht, hr⟩ := outputs ι before id id id
    (fun _ => rfl) none BitMachineCopy.program (copyProgram ι)
    (fun _ => rfl) localCfg (2 * word.length + 2) hhalt
  have hstart : BitMachineStackEmbedding.cfg ι before id id none localCfg =
      (⟨some .scan, none, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          BitMachineCopy.Label (Option Bool)) := by
    simp only [BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, localCfg, BitMachineCopy.cfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;>
      simp [BitMachineCopy.stackContents, hsource, htarget, hwork]
  rw [hstart, hlocal] at hr
  let S := bank ι before (BitMachineCopy.stackContents word word [])
  refine ⟨t, S, ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, BitMachineCopy.cfg, id_eq,
      Option.map_none] using hr
  · change bank ι before _ (ι 0) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 1) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 2) = _
    rw [bank_at]
    rfl
  · intro k hk0 hk1 hk2
    apply bank_outside
    rintro ⟨i, hi⟩
    fin_cases i
    · exact hk0 hi.symm
    · exact hk1 hi.symm
    · exact hk2 hi.symm

theorem source_copy (q : Nat) (before : Stack q → List Bool)
    (word : List Bool)
    (hsource : before savedSource = word)
    (htarget : before writerSource = [])
    (hwork : before work = []) :
    ∃ t S, t ≤ 2 * word.length + 2 ∧
      ((advance (sourceCopyProgram (q := q)))^[t])
        (⟨some .scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S savedSource = word ∧ S writerSource = word ∧
      S work = [] ∧
      (∀ k, k ≠ savedSource → k ≠ writerSource →
        k ≠ work → S k = before k) := by
  simpa only [sourceCopyProgram, copyProgram,
    sourceCopyEmbedding, dif_pos, dif_neg] using
    copy_framed (sourceCopyEmbedding (q := q)) before word
      hsource htarget hwork

theorem vertex_copy (q : Nat) (before : Stack q → List Bool)
    (cap : List Bool)
    (hsource : before capSource = cap)
    (htarget : before writerVertex = [])
    (hwork : before work = []) :
    ∃ t S, t ≤ 2 * cap.length + 2 ∧
      ((advance (vertexCopyProgram (q := q)))^[t])
        (⟨some .scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      S capSource = cap ∧ S writerVertex = cap ∧
      S work = [] ∧
      (∀ k, k ≠ capSource → k ≠ writerVertex →
        k ≠ work → S k = before k) := by
  simpa only [vertexCopyProgram, copyProgram,
    vertexCopyEmbedding, dif_pos, dif_neg] using
    copy_framed (vertexCopyEmbedding (q := q)) before cap
      hsource htarget hwork

/-- The second-pass writer receives a physically copied raw suffix and unary
vertex count. The global saved suffix and unary cap remain available. -/
theorem stage_input (q : Nat) (before : Stack q → List Bool)
    (suffix cap : List Bool)
    (hsaved : before savedSource = suffix)
    (hcap : before capSource = cap)
    (hsourceBlank : before writerSource = [])
    (hvertexBlank : before writerVertex = [])
    (hworkBlank : before work = []) :
    ∃ t S,
      t ≤ (2 * suffix.length + 2) + (2 * cap.length + 2) + 3 ∧
      ((advance (program (q := q)))^[t])
        (⟨some (.inl (.inl .scan)), ((none, none), ()), before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) Label Control) =
        ⟨none, ((none, none), ()), S⟩ ∧
      S savedSource = suffix ∧ S capSource = cap ∧
      S writerSource = suffix ∧ S writerVertex = true :: cap ∧
      S work = [] := by
  obtain ⟨ts, S1, hts, hrs, hs1, hsource1, hwork1, hother1⟩ :=
    source_copy q before suffix hsaved hsourceBlank hworkBlank
  have hcap1 : S1 capSource = cap :=
    (hother1 capSource (by simp [capSource, savedSource,
      SourceCSPGlobalDecisionProgram.savedSource,
      SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.scratch])
      (by simp [capSource, writerSource])
      (by simp [capSource, work])).trans hcap
  have hvertex1 : S1 writerVertex = [] :=
    (hother1 writerVertex (by simp [writerVertex, savedSource])
      (by simp [writerVertex, writerSource,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [writerVertex, work,
        SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterOperands.scratch])).trans hvertexBlank
  obtain ⟨tv, S2, htv, hrv, hcap2, hvertex2, hwork2, hother2⟩ :=
    vertex_copy q S1 cap hcap1 hvertex1 hwork1
  have hsaved2 : S2 savedSource = suffix :=
    (hother2 savedSource (by simp [savedSource, capSource,
      SourceCSPGlobalDecisionProgram.savedSource,
      SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.scratch])
      (by simp [savedSource, writerVertex])
      (by simp [savedSource, work])).trans hs1
  have hsource2 : S2 writerSource = suffix :=
    (hother2 writerSource (by simp [writerSource, capSource])
      (by simp [writerSource, writerVertex,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [writerSource, work,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.scratch])).trans hsource1
  let S3 := Function.update S2 writerVertex (true :: cap)
  have hpush : ((advance (addVertexProgram (q := q)))^[1])
      (⟨some (), (), S2⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) Unit Unit) =
      ⟨none, (), S3⟩ := by
    simp [advance, TM2.step, TM2.stepAux, addVertexProgram,
      S3, hvertex2]
  obtain ⟨t12, ht12, hr12⟩ := BitMachineRawSequence.runs
    (sourceCopyProgram (q := q)) (vertexCopyProgram (q := q))
    .scan .scan none none none none before S1 S2 ts tv hrs hrv
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (copyPairProgram (q := q)) (addVertexProgram (q := q))
    (.inl .scan : CopyPairLabel) () (none, none) (none, none)
    () () before S2 S3 t12 1
    (by simpa only [copyPairProgram] using hr12) hpush
  refine ⟨t, S3, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [program] using hr
  · simpa [S3, writerVertex, savedSource] using hsaved2
  · simpa [S3, writerVertex, capSource] using hcap2
  · simpa [S3, writerVertex, writerSource,
      SourceClauseRowWriterCleanup.rowCell,
      SourceClauseRowWriterOperands.vertex] using hsource2
  · simp [S3, writerVertex]
  · simpa [S3, writerVertex, work,
      SourceClauseRowWriterOperands.vertex,
      SourceClauseRowWriterOperands.scratch] using hwork2

end EthInapproximability.CurrentPaper.SourceCSPSecondPassInput
