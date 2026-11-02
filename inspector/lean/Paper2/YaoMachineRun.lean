import Paper2.YaoMachine

/-! Unit 5 segment Y9 (lane a-yao-owner-2): the composed Yao table machine and its
one-run theorem.  See `YaoMachine.lean` for the cell layout. -/

noncomputable section

namespace Paper2.YaoMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryControllerJoin
open Paper2.YaoCtrlBlock
open Paper2.YaoMaterialization
open Paper2.UnaryFieldListParserScratch
open Paper2.RecursiveLabelCodecScratch
open Paper2.YaoSourceCodec
open Paper2.YaoOneEntry
open Paper2.YaoPrelude
open Paper2.YaoHeaderParser

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

@[simp] theorem st_eq_iff {t lambda : ℕ} {a b : Cells t lambda} : st a = st b ↔ a = b :=
  st_injective.eq_iff

@[simp] theorem cellOf_eq_iff {t lambda : ℕ} {a b : Cells t lambda} :
    cellOf a = cellOf b ↔ a = b := (Fintype.equivFin _).injective.eq_iff

@[simp] theorem st_ne_extra {t lambda : ℕ} (a : Cells t lambda) (q : MatrixTableWriter.Extra) :
    (st a : WStack t lambda) ≠ Sum.inr q := by simp [st]

@[simp] theorem extra_ne_st {t lambda : ℕ} (a : Cells t lambda) (q : MatrixTableWriter.Extra) :
    (Sum.inr q : WStack t lambda) ≠ st a := by simp [st]

@[simp] theorem idx_ne_st {t lambda : ℕ} (a : Cells t lambda) (k : Fin 3) :
    (Sum.inl (Sum.inr k) : WStack t lambda) ≠ st a := by simp [st]

/-- The machine's input: the code in `sN 0`, the raw tape in the controller's
`tapeSource` cell, every other cell empty. -/
def initBank {t : ℕ} (lambda : ℕ) (x : Paper2.YaoSourceCodec.YaoSource t) (tape : List Bool) :
    WStack t lambda → List Bool :=
  fun j => if j = sN 0 then encode x else if j = st (.inl (tapeSource t lambda)) then tape else []

/-- The writer program with the Yao callback. -/
def writerProg (t lambda : ℕ) :=
  MatrixTableWriter.program (entryProgram (omegaPlace t lambda))
    (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel) (entryControl t lambda)

def m45 (t lambda : ℕ) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpCols t lambda))
    (writerProg t lambda) (.inr (.copy .rows)) none (entryControl t lambda, none)
def m345 (t lambda : ℕ) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpRows t lambda))
    (m45 t lambda) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (entryControl t lambda, none))
def m2345 (t lambda : ℕ) :=
  BitMachineRawSequence.program (preludeFull t lambda (thetaPlace t lambda)) (m345 t lambda)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (preludeControl t lambda, dimsControl) (none, (none, (entryControl t lambda, none)))
/-- The fixed Yao table machine (one program per `t, lambda`). -/
def yaoMachine (t lambda : ℕ) :=
  BitMachineRawSequence.program (headerProgram (s5 t lambda)) (m2345 t lambda)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    (none, none) ((preludeControl t lambda, dimsControl), (none, (none, (entryControl t lambda, none))))

def yaoControl (t lambda : ℕ) :=
  (((none : Option Bool), (none : Option Bool)),
    ((preludeControl t lambda, dimsControl), ((none : Option Bool),
      ((none : Option Bool), (entryControl t lambda, (none : Option Bool))))))

/-- The static bank after preparation (explicit). -/
def prepBank {t : ℕ} (lambda : ℕ) (x : Paper2.YaoSourceCodec.YaoSource t) (tape : List Bool) :
    WStack t lambda → List Bool :=
  Function.update (Function.update
    (preludeFullOut (thetaPlace t lambda)
      (headerOut (s5 t lambda) (initBank lambda x tape) x.1 x.2.1
        ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ []))
      x.1 x.2.1)
    (.inr .rows) (List.replicate (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) true))
    (.inr .cols) (List.replicate (columnCount t (paddedEdgeBits x.2.1) lambda) true)

def yaoClock {t : ℕ} (lambda : ℕ) (x : Paper2.YaoSourceCodec.YaoSource t) : ℕ :=
  ((2 * (encode x ++ []).length + 2) + (x.1 + x.2.1 + 2) + 1) +
    preludeFullClock t lambda x.1 x.2.1 +
    (2 * rowCount x.1 t (paddedEdgeBits x.2.1) lambda + 2) +
    (2 * columnCount t (paddedEdgeBits x.2.1) lambda + 2) +
    MatrixTableWriter.writerBound (rowCount x.1 t (paddedEdgeBits x.2.1) lambda)
      (columnCount t (paddedEdgeBits x.2.1) lambda) (Paper2.YaoEntryRuns.yaoT t lambda x.2.2) + 4

/-- Y9 machine theorem: one physical run of the fixed program from the code and
the raw tape to the exact final writer bank, whose output cell holds
`(materialize t lambda x.2.2 bits).bits`. -/
theorem physical_yao_table (t lambda : ℕ) (ht : 1 ≤ t) (x : Paper2.YaoSourceCodec.YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    ∃ total ≤ yaoClock lambda x, ∃ c',
      ((advance (yaoMachine t lambda))^[total])
        (⟨some (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel), yaoControl t lambda,
          initBank lambda x bits.val⟩ : TM2.Cfg (fun _ : WStack t lambda => Bool) _ _) =
        ⟨none, c', (MatrixTableWriter.ready (fun n => prepBank lambda x bits.val (.inl (.inl n)))
          (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda)
          0 0 0 0 [] ((materialize t lambda x.2.2 bits).bits ++ [])).contents⟩ := by
  classical
  have hθ := (thetaPlace t lambda).injective
  have hne0 : ∀ i : Fin 40, i ≠ 0 → (sN i : WStack t lambda) ≠ sN 0 := by
    intro i hi h; exact hi (by simpa [sN, st_eq_iff] using h)
  have hneT : ∀ i : Fin 40, (sN i : WStack t lambda) ≠ st (.inl (tapeSource t lambda)) := by
    intro i h; simp [sN, st_eq_iff] at h
  have hW0 : ∀ i : Fin 40, i ≠ 0 → initBank lambda x bits.val (sN i) = [] := by
    intro i hi; simp [initBank, hne0 i hi, hneT i]
  -- stage 1: header
  obtain ⟨t1, ht1, hr1⟩ := physical_header (s5 t lambda) (initBank lambda x bits.val) x []
    (by simp [s5, initBank]) (by simp [s5, initBank, sN, Fin.ext_iff])
    (by simp [s5, initBank, sN, Fin.ext_iff]) (by simp [s5, initBank, sN, Fin.ext_iff])
    (by simp [s5, initBank, sN, Fin.ext_iff])
  set W1 := headerOut (s5 t lambda) (initBank lambda x bits.val) x.1 x.2.1
    ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ []) with hW1
  -- stage 2: prelude
  have hW1s : ∀ i : Fin 40, 5 ≤ i.val → W1 (sN i) = [] := by
    intro i hi
    simp only [hW1, headerOut, s5, Function.Embedding.coeFn_mk]
    rw [Function.update_of_ne (by simp [sN, st_eq_iff, Fin.ext_iff]; omega),
      Function.update_of_ne (by simp [sN, st_eq_iff, Fin.ext_iff]; omega),
      Function.update_of_ne (by simp [sN, st_eq_iff, Fin.ext_iff]; omega)]
    exact hW0 i (by intro h; subst h; simp at hi)
  obtain ⟨t2, ht2, c2, hr2⟩ := physical_prelude_full t lambda ht (thetaPlace t lambda) W1
    x.1 x.2.1
    (by simp [hW1, headerOut, s5, thetaPlace, thetaFun, thetaIdx, sN, st_eq_iff, Function.update_apply])
    (by simp [hW1, headerOut, s5, thetaPlace, thetaFun, thetaIdx, sN, st_eq_iff, Function.update_apply])
    (by
      intro i hi
      have := hW1s (thetaIdx i) (by revert hi; revert i; decide)
      simpa [thetaPlace, thetaFun] using this)
    (by
      intro k
      simp only [thetaPlace, thetaFun, Function.Embedding.coeFn_mk, hW1, headerOut, s5]
      rw [Function.update_of_ne (by simp [sN, st_eq_iff]),
        Function.update_of_ne (by simp [sN, st_eq_iff]),
        Function.update_of_ne (by simp [sN, st_eq_iff])]
      simp [initBank, sN, st_eq_iff])
  set W2 := preludeFullOut (thetaPlace t lambda) W1 x.1 x.2.1 with hW2
  -- stages 3, 4: copy r and c into the writer's rows/cols cells
  obtain ⟨t3, ht3, hr3⟩ := ExactParameterBranchInstall.copy_run (cpRows t lambda) W2
    (List.replicate (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) true)
    (by simp [hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, cpRows, thetaPlace, thetaFun, sN, st_eq_iff])
    (by simp [hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, cpRows, thetaPlace, thetaFun, sN, hW1,
          headerOut, s5, initBank])
    (by simp [hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, cpRows, thetaPlace, thetaFun, sN, st_eq_iff, hW1,
          headerOut, s5, initBank])
  set W3 := Function.update W2 (.inr .rows)
    (List.replicate (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) true) with hW3
  obtain ⟨t4, ht4, hr4⟩ := ExactParameterBranchInstall.copy_run (cpCols t lambda) W3
    (List.replicate (columnCount t (paddedEdgeBits x.2.1) lambda) true)
    (by simp [hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, cpCols, thetaPlace, thetaFun, sN, st_eq_iff])
    (by simp [hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, cpCols, thetaPlace, thetaFun, sN, hW1,
          headerOut, s5, initBank])
    (by simp [hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, cpCols, thetaPlace, thetaFun, sN, st_eq_iff,
          hW1, headerOut, s5, initBank])
  set W4 := Function.update W3 (.inr .cols)
    (List.replicate (columnCount t (paddedEdgeBits x.2.1) lambda) true) with hW4
  have hW4p : W4 = prepBank lambda x bits.val := rfl
  -- stage 5: the writer
  set bank4 : Fin (YK t lambda) → List Bool := fun n => W4 (.inl (.inl n)) with hbank4
  have hb : ∀ i : Fin 40, bank4 (cellOf (.inr (.inr i))) = W4 (sN i) := fun _ => rfl
  have hW4out : ∀ i : Fin 40, 11 < i.val → W4 (sN i) = W1 (sN i) := by
    intro i hi
    have hne : ∀ j : Fin 22, 2 ≤ j.val → j.val ≤ 8 → i ≠ thetaIdx j := by
      intro j hj1 hj2 h; rw [h] at hi; clear h; revert hi hj1 hj2; revert j; decide
    simp only [hW4, hW3, hW2, preludeFullOut, preludeOut, thetaPlace, thetaFun,
      Function.Embedding.coeFn_mk, sN]
    rw [Function.update_of_ne (st_ne_extra _ _), Function.update_of_ne (st_ne_extra _ _),
      Function.update_of_ne (by simpa using hne 8 (by decide) (by decide)),
      Function.update_of_ne (by simpa using hne 7 (by decide) (by decide)),
      Function.update_of_ne (by simpa using hne 6 (by decide) (by decide)),
      Function.update_of_ne (by simpa using hne 5 (by decide) (by decide)),
      Function.update_of_ne (by simpa using hne 4 (by decide) (by decide)),
      Function.update_of_ne (by simpa using hne 3 (by decide) (by decide)),
      Function.update_of_ne (by simpa using hne 2 (by decide) (by decide))]
  have hcell := entry_runs_gen t lambda x.2.2 bits bank4
    (by rw [hb]; simp [hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace, thetaFun, sN])
    (by rw [hb]; simp [hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace, thetaFun, sN, st_eq_iff])
    (by rw [hb]; simp [hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace, thetaFun, sN, st_eq_iff])
    (by rw [hb]; simp [hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace, thetaFun, sN, st_eq_iff])
    (by rw [hb]; simp [hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace, thetaFun, sN, st_eq_iff,
          hW1, headerOut, s5])
    (by
      rw [hb]
      simp [hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace, thetaFun, sN, st_eq_iff, hW1,
        headerOut, s5, bodyCodec, piCodec_encode_eq_tokens])
    (by intro i hi1 hi2; rw [hb, hW4out i (by omega)]; exact hW1s i (by omega))
    (by
      intro k
      show W4 (st (.inl k)) = _
      simp [hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace, thetaFun, sN, st_eq_iff, hW1,
        headerOut, s5, initBank, tapeOnly])
  obtain ⟨t5, ht5, w5, hr5⟩ := MatrixTableWriter.write_rowMajor (entryProgram (omegaPlace t lambda))
    (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel) (entryControl t lambda)
    bank4 (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda)
    (Paper2.YaoEntryRuns.yaoT t lambda x.2.2) (Paper2.YaoEntryRuns.yaoEntry t lambda x.2.2 bits)
    (materialize t lambda x.2.2 bits).matrix
    (by intro X Y; simp [Paper2.YaoEntryRuns.yaoEntry, X.isLt, Y.isLt]) hcell []
  rw [Paper2.YaoEntryRuns.rowMajor_materialize] at hr5
  have hready : (MatrixTableWriter.ready bank4 (rowCount x.1 t (paddedEdgeBits x.2.1) lambda)
      (columnCount t (paddedEdgeBits x.2.1) lambda) 0 0 0 0 [] []).contents = W4 := by
    funext j
    rcases j with (n | i) | q
    · rfl
    · fin_cases i <;> simp [MatrixTableWriter.ready, MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.cell, hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace,
        thetaFun, sN, hW1, headerOut, s5, initBank]
    · cases q <;> simp [MatrixTableWriter.ready, MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.foreign, hW4, hW3, hW2, preludeFullOut, preludeOut, Function.update_apply, thetaIdx, thetaPlace,
        thetaFun, sN, hW1, headerOut, s5, initBank]
  have hr5' : ((advance (writerProg t lambda))^[t5])
      (⟨some (.inr (.copy .rows)), (entryControl t lambda, none), W4⟩ :
        TM2.Cfg (fun _ : WStack t lambda => Bool) _ _) =
      ⟨none, w5, (MatrixTableWriter.ready (fun n => prepBank lambda x bits.val (.inl (.inl n)))
          (rowCount x.1 t (paddedEdgeBits x.2.1) lambda) (columnCount t (paddedEdgeBits x.2.1) lambda)
          0 0 0 0 [] ((materialize t lambda x.2.2 bits).bits ++ [])).contents⟩ := by
    rw [← hready]
    exact hr5
  -- sequencing
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpCols t lambda)) (writerProg t lambda)
    BitMachineCopy.Label.scan (.inr (.copy .rows)) none none (entryControl t lambda, none) w5
    W3 W4 _ t4 t5 hr4 hr5'
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpRows t lambda)) (m45 t lambda)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (entryControl t lambda, none)) (none, w5) W2 W3 _ t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs
    (preludeFull t lambda (thetaPlace t lambda)) (m345 t lambda)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (preludeControl t lambda, dimsControl) c2 (none, (none, (entryControl t lambda, none)))
    (none, (none, w5)) W1 W2 _ t2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs (headerProgram (s5 t lambda))
    (m2345 t lambda) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    (none, none) (none, some false)
    ((preludeControl t lambda, dimsControl), (none, (none, (entryControl t lambda, none))))
    ((preludeControl t lambda, dimsControl), (none, (none, w5)))
    (initBank lambda x bits.val) W1 _ t1 u2 hr1 hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_replicate] at ht3 ht4
  unfold yaoClock
  omega

#print axioms physical_yao_table

end Paper2.YaoMachine

end
