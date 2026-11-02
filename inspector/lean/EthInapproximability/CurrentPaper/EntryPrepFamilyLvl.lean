import EthInapproximability.CurrentPaper.EntryPrepFamilyProg

/-!
# Lane owner:b-stage4-entry-program-8: level-0 re-run data, clock and gap lemmas for `progF`

`family4` discharges owner-7's interface `EntryPrepVec.Family4Spec` for the fixed program
`progF` with the public clock `TF G n c`; `level0_writer22` then gives the production consumer
`OuterLevel0Full.Writer22Spec` with NO remaining premise (through owner-7's frozen
`level0_writer22_of_family4`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepFamily

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Level-0 parameters of the re-run (the SAME objects as `EntryLevelWords.w0`) -/

abbrev iP (G : EndpointGraph V E) (n c : ℕ) := Iteration.stepParameters G c (b0 n) (y0 n) 0 (M0 n)
abbrev gP (G : EndpointGraph V E) := EncodedETHSource.serializeGraph G
abbrev sP (G : EndpointGraph V E) (n c : ℕ) := Parameters.bins (iP G n c)
abbrev qP (G : EndpointGraph V E) (n c : ℕ) := ParameterizedNP.GuardedSourceSlab.q2 G (sP G n c)
abbrev aP (G : EndpointGraph V E) (n c : ℕ) := Parameters.firstExponent (iP G n c)
abbrev tP (G : EndpointGraph V E) (n c : ℕ) := Parameters.balanceOrder (iP G n c)
abbrev LP (G : EndpointGraph V E) (n c : ℕ) :=
  PrimeSampler.size (qP G n c) (tP G n c) (Construction.qOne (aP G n c) * (iP G n c).rows)
abbrev dP (G : EndpointGraph V E) (n c : ℕ) :=
  ProtectedFullBankBridgeScratch.actualD G c (b0 n) (y0 n) 0 (M0 n)

/-- The admitted level-wired family clock at level 0. -/
noncomputable def famBound (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  WeightedLevelFields15.publicBound15 (iP G n c) (gP G) (Fintype.card E) WeightedRawWords.noW
    (aP G n c) (sP G n c) (qP G n c) (LP G n c) (dP G n c).binBase (dP G n c).rawWidth
    (dP G n c).s +
  EntryFamilyLevel.copyBound (aP G n c) (qP G n c) (LP G n c) (iP G n c).rows (tP G n c) +
  EntryFamilyAssembly.assemblyBound (aP G n c) (qP G n c) (tP G n c) (iP G n c).rows + 6

/-- The growth allowance of a level-bank cell (admitted `run_growth`). -/
noncomputable def growB (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  BitMachineStackGrowth.perStep WeightedLevelFields15.program *
    WeightedLevelFields15.publicBound15 (iP G n c) (gP G) (Fintype.card E) WeightedRawWords.noW
      (aP G n c) (sP G n c) (qP G n c) (LP G n c) (dP G n c).binBase (dP G n c).rawWidth
      (dP G n c).s

/-- The exact family-region exit bank of the re-run. -/
noncomputable def exA (G : EndpointGraph V E) (n c : ℕ) : EntryFamilyAssembly.ACell → List Bool :=
  EntryFamilyAssembly.exitBank (aP G n c) (qP G n c) (tP G n c) (iP G n c).rows
    (Iteration.alphabet_pos G c (b0 n) (y0 n) 0 (M0 n))

/-- The admitted start bank of the re-run. -/
noncomputable def SF (G : EndpointGraph V E) (n c : ℕ) : EntryFamilyLevel.Stack → List Bool :=
  Sum.elim (WeightedLevelColumnSave.initialBank (iP G n c) (gP G) WeightedRawWords.noW)
    EntryFamilyLevel.blankA

set_option maxHeartbeats 1000000 in
theorem level0_family (G : EndpointGraph V E) (n c : ℕ) :
    ∃ Z : WeightedLevelColumnSave.Stack → List Bool, ∃ nn ≤ famBound G n c,
      ((advance EntryFamilyLevel.program)^[nn])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))),
            EntryFamilyLevel.initialControl, SF G n c⟩ :
            TM2.Cfg (fun _ : EntryFamilyLevel.Stack => Bool) _ _) =
          ⟨none, EntryFamilyLevel.initialControl, Sum.elim Z (exA G n c)⟩ ∧
      (∀ j, (Z j).length ≤
        (WeightedLevelColumnSave.initialBank (iP G n c) (gP G) WeightedRawWords.noW j).length +
          growB G n c) ∧
      exA G n c (EntryFamilyAssembly.cell .first) = MatrixStage4FamilyData.fieldTable
        (MatrixStage4FamilyData.familyFirst (Iteration.secondFamily G c (b0 n) (y0 n) 0 (M0 n))) ∧
      exA G n c (EntryFamilyAssembly.cell .row) = MatrixStage4FamilyData.fieldTable
        (MatrixStage4FamilyData.familyRow (Iteration.secondFamily G c (b0 n) (y0 n) 0 (M0 n))) := by
  obtain ⟨F, Q, P, h⟩ := level_family_growth G c (b0 n) (y0 n) 0 (M0 n) WeightedRawWords.noW
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨nn, hnn, hr, hg, h1, h2⟩ := h
  exact ⟨_, nn, hnn, hr, hg, h1, h2⟩

theorem w0_first (G : EndpointGraph V E) (n c : ℕ) :
    (EntryLevelWords.w0 G n c).firstTable = MatrixStage4FamilyData.fieldTable
      (MatrixStage4FamilyData.familyFirst (Iteration.secondFamily G c (b0 n) (y0 n) 0 (M0 n))) := by
  unfold EntryLevelWords.w0 EntryLevelWords.levelWords
  rw [TemplateEntry.actualWords.eq_def]

theorem w0_row (G : EndpointGraph V E) (n c : ℕ) :
    (EntryLevelWords.w0 G n c).rowTable = MatrixStage4FamilyData.fieldTable
      (MatrixStage4FamilyData.familyRow (Iteration.secondFamily G c (b0 n) (y0 n) 0 (M0 n))) := by
  unfold EntryLevelWords.w0 EntryLevelWords.levelWords
  rw [TemplateEntry.actualWords.eq_def]

theorem cellsF_ne_tj (i : Fin nF) (k : Fin 19) : cellsF i ≠ tailEmb (tj k) := fmap_ne_tj _ k

/-- The admitted start bank, cell by cell (`WeightedRawWords.consumer_chain`), with the values
the sources hold at `midBank4`. -/
theorem SF_eq (G : EndpointGraph V E) (n c : ℕ) :
    SF G n c =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update
          (Function.update (fun _ => []) pInF (true :: EncodedGraph.encode (gP G)))
          (rawF 1) (List.replicate (b0 n) true)) (rawF 2) (List.replicate (y0 n) true))
          (rawF 4) (EntryLayout.rep (EntryLevelWords.w0 G n c).cy))
          (rawF 3) (EntryLayout.rep (EntryLevelWords.w0 G n c).rx))
          (rawF 5) (List.replicate (Fintype.card E) true)) (rawF 0) (List.replicate c true) := by
  have h := WeightedRawWords.consumer_chain (iP G n c) (gP G)
  show Sum.elim (Sum.elim (WeightedRawRowsSource.initialBank (iP G n c) (gP G)
    WeightedRawWords.noW) (fun _ => [])) EntryFamilyLevel.blankA = _
  rw [h]
  simp only [← Sum.update_elim_inl]
  have e : (Sum.elim (Sum.elim (fun _ : WeightedRawWords.Cons => ([] : List Bool))
      (fun _ : Fin 7 => [])) EntryFamilyLevel.blankA) = fun _ => [] := by
    funext x
    rcases x with (x | x) | x <;> rfl
  rw [e]
  have w0 : WeightedRawWords.W6 (iP G n c) 0 = List.replicate c true := rfl
  have w1 : WeightedRawWords.W6 (iP G n c) 1 = List.replicate (b0 n) true := rfl
  have w2 : WeightedRawWords.W6 (iP G n c) 2 = List.replicate (y0 n) true := rfl
  have w3 : WeightedRawWords.W6 (iP G n c) 3 = EntryLayout.rep (EntryLevelWords.w0 G n c).rx := by
    simp only [WeightedRawWords.W6, ETHParameterScaleMachineInput.words, EntryLayout.rep,
      EntryLevelWords.w0, EntryLevelWords.levelWords, TemplateEntry.actualWords,
      Iteration.stepParameters, Iteration.parameters, Matrix.cons_val]
  have w4 : WeightedRawWords.W6 (iP G n c) 4 = EntryLayout.rep (EntryLevelWords.w0 G n c).cy := by
    simp only [WeightedRawWords.W6, ETHParameterScaleMachineInput.words, EntryLayout.rep,
      EntryLevelWords.w0, EntryLevelWords.levelWords, TemplateEntry.actualWords,
      Iteration.stepParameters, Iteration.parameters, Matrix.cons_val]
  have w5 : WeightedRawWords.W6 (iP G n c) 5 = List.replicate (Fintype.card E) true := rfl
  rw [w0, w1, w2, w3, w4, w5]
  rfl

/-! ## The four gap cells (the read-back probe `rv_tail_gap`, re-proved here) -/

theorem tail_cell_gap (G : EndpointGraph V E) (n c : ℕ) :
    EntryRunsRaw.cellBank (EntryLevelWords.w0 G n c) =
      Function.update (Function.update (Function.update (Function.update
        (EntryRunsRaw.cellBank (wMid4 G n c))
        (EntryRunsRaw.eo (.inl 4)) (EntryLayout.rep (EntryLevelWords.w0 G n c).qOne))
        (EntryRunsRaw.eo (.inl 5)) (EntryLevelWords.w0 G n c).firstTable)
        (EntryRunsRaw.eo (.inl 8)) (EntryLayout.rep (EntryLevelWords.w0 G n c).firstExp))
        (EntryRunsRaw.eo (.inl 11)) (EntryLevelWords.w0 G n c).rowTable := by
  funext k
  obtain ⟨o, rfl⟩ := EntryRunsRaw.eo.surjective k
  rcases o with i | r
  · simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inl, Function.update_apply,
      EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
    fin_cases i <;> simp [EntryLayout.common, wMid4, wordB_eq]
  · simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inr, Function.update_apply,
      EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false]

theorem tail_gap (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    tailStart Mm G n c F Q P =
      Function.update (Function.update (Function.update (Function.update
        (midBank4 Mm G n c F Q P)
        (tailEmb (tj 4)) (EntryLayout.rep (EntryLevelWords.w0 G n c).qOne))
        (tailEmb (tj 5)) (EntryLevelWords.w0 G n c).firstTable)
        (tailEmb (tj 8)) (EntryLayout.rep (EntryLevelWords.w0 G n c).firstExp))
        (tailEmb (tj 11)) (EntryLevelWords.w0 G n c).rowTable := by
  unfold tailStart midBank4
  have h : bnk0 G n c = EntryRunsRaw.cellBank (EntryLevelWords.w0 G n c) := rfl
  rw [h, tail_cell_gap, start_update, start_update, start_update, start_update]
  simp only [← bank_update]
  rfl

theorem mid4_out (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (i : Fin 19) (hi : i = 4 ∨ i = 5 ∨ i = 8 ∨ i = 11) :
    midBank4 Mm G n c F Q P (tailEmb (tj i)) = [] := by
  rw [mid4_tail]
  simp only [tj, RawTableTail.startBank, RawTableTail.glob, MatrixTableWriter.Data.contents,
    MatrixTableWriter.Data.cell, MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl,
    Equiv.symm_apply_apply, common_wMid4 G n c]
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem firstExp_eq (G : EndpointGraph V E) (n c : ℕ) :
    EntryLayout.rep (EntryLevelWords.w0 G n c).s ++ EntryLayout.rep (EntryLevelWords.w0 G n c).qOne =
      EntryLayout.rep (EntryLevelWords.w0 G n c).firstExp := by
  simp only [EntryLayout.rep, List.replicate_append_replicate]
  congr 1
  simp only [EntryLevelWords.w0, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    Construction.firstLength]
  omega

/-! ## The public clock -/

noncomputable def bnd (G : EndpointGraph V E) (n c : ℕ) : EntryFamilyLevel.Stack → ℕ :=
  Sum.elim (fun j => (WeightedLevelColumnSave.initialBank (iP G n c) (gP G)
      WeightedRawWords.noW j).length + growB G n c)
    (fun x => (exA G n c x).length)

open scoped Classical in
/-- Length allowance of workspace code `x` at the clear (0 for codes outside `range enc`). -/
noncomputable def lenF (G : EndpointGraph V E) (n c : ℕ) (x : FamIdx) : ℕ :=
  if h : ∃ y, enc y = x then bnd G n c (Classical.choose h) else 0

noncomputable def clearB (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  ∑ i : Fin nF, lenF G n c ((Fintype.equivFin FamIdx).symm i)

noncomputable def costA (G : EndpointGraph V E) : ℕ :=
  (2 * (EncodedGraph.encode (gP G)).length + 2) + 0

noncomputable def costC (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  (2 * c + 2) + ((2 * Fintype.card E + 2) + ((2 * (EntryLevelWords.w0 G n c).rx + 2) +
    ((2 * (EntryLevelWords.w0 G n c).cy + 2) + ((2 * y0 n + 2) + ((2 * b0 n + 2) + 0)))))

noncomputable def costE (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  (2 * (EntryLevelWords.w0 G n c).firstTable.length + 2) +
    ((2 * (EntryLevelWords.w0 G n c).rowTable.length + 2) +
      ((2 * (EntryLevelWords.w0 G n c).qOne + 2) + ((2 * (EntryLevelWords.w0 G n c).qOne + 2) + 0)))

/-- The clock of `progF`. -/
noncomputable def TF (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  (costA G + 1) + (1 + ((costC G n c + 1) + (famBound G n c + ((costE G n c + 1) +
    ((2 * (EntryLevelWords.w0 G n c).s + 2) + (clearB G n c + nF + 2) + 1) + 1) + 1) + 1) + 1) + 1

#print axioms level0_family
#print axioms w0_first
#print axioms w0_row
#print axioms SF_eq
#print axioms tail_gap
#print axioms firstExp_eq

end EthInapproximability.CurrentPaper.EntryPrepFamily
