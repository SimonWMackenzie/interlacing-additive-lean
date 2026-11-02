import EthInapproximability.CurrentPaper.EntryClockPolyLevel

/-!
# Segment 2 (instance-determined pieces): boundA, the label division, the wordB copy,
# the writer clock and the clear clock, uniformly polynomial in `Inst.U`

Lane owner:b-entry-clock-2 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic about the
admitted clocks; no machine.

For an arbitrary instance `I` the functions `boundAI`, `labI`, `wordI`, `writerI`,
`clearI` are the admitted level-0 clock pieces with the level-0 data replaced by `I`:
at `I = inst0 G n c` they are literally `EntryPrepCopy.boundA G n c`, the non-`T` part of
`EntryPrepVec.labBound G n c T`, the `wordB` copy of `EntryPrepVec.prepBound`,
`EntryTailClear.tailBound G n c` and `EntryTailClear.clearBound G n c` (`*_eq`).
Over instances with a positive column count (`PI`) their sum `restI` is `PolyIn` the
instance size (`restI_poly`): ONE pair of absolute constants.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-- Instances with an address (positive raw column count). -/
abbrev PI := {I : Inst // 0 < cols I.a I.s I.q I.cy}

/-- The 19 common words of an instance (`TemplateEntry.actualWords`). -/
def wI (I : Inst) : EntryLayout.Words :=
  TemplateEntry.actualWords I.a I.s I.q I.L I.cy I.rx I.R I.family (rowMajor I.vectors)

def copyCostI (I : Inst) : ℕ :=
  (2 * binBase I.a I.s I.q I.cy + 2) + ((2 * wordBase I.a I.s I.cy + 2) +
  ((2 * I.cy + 2) + ((2 * I.rx + 2) + ((2 * I.s + 2) + ((2 * (I.s * I.L) + 2) +
  ((2 * cols I.a I.s I.q I.cy + 2) + 0))))))

def boundAI (I : Inst) : ℕ :=
  (copyCostI I + 1) +
    DerivedScalars.bound I.s I.cy (binBase I.a I.s I.q I.cy) (I.s * I.L) I.nv I.nb I.rx + 1

def labI (I : Inst) : ℕ :=
  ((2 * (I.s * I.L) + 2) + 0 + 1) + MatrixUnaryDivision.exactTime (I.s * I.L) I.s + 1

def wordI (I : Inst) : ℕ := ((2 * wordBase I.a I.s I.cy + 2) + 0) + 1

def writerI (I : Inst) : ℕ :=
  MatrixTableWriter.writerBound (rows I.s I.L I.nv I.nb I.rx) (cols I.a I.s I.q I.cy)
      (EntryRunsRaw.tableT I.R I.hs I.family I.order I.vectors I.cap) +
    (2 * (rows I.s I.L I.nv I.nb I.rx * cols I.a I.s I.q I.cy) + 2) + 1

noncomputable def clearI (I : Inst) : ℕ :=
  (∑ i : Fin EntryTailClear.nR, (RawTableTail.exitBank (EntryRunsRaw.cellBank (wI I))
    (rows I.s I.L I.nv I.nb I.rx) (cols I.a I.s I.q I.cy) (fun _ => [])
    (rawTable I.R I.a I.s I.q I.L I.nv I.nb I.hs I.family I.order I.vectors I.cap)
    (EntryTailClear.regTail ((Fintype.equivFin EntryTailEmbed.Region).symm i))).length) +
    EntryTailClear.nR + 2

/-! ## The level-0 pieces are the instance pieces at `inst0` -/

section eqs

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem boundA_eq (G : EndpointGraph V E) (n c : ℕ) :
    EntryPrepCopy.boundA G n c = boundAI (inst0 G n c) := by
  unfold EntryPrepCopy.boundA EntryPrepCopy.copyCost boundAI copyCostI
  dsimp only [inst0, EntryLevelWords.w0, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    EntryLevelDerived.d0, ProtectedFullBankBridgeScratch.actualD,
    MatrixWeightedEntrySemantic.actualInput, EntryTailClear.c0]

theorem labBound_eq (G : EndpointGraph V E) (n c T : ℕ) :
    EntryPrepVec.labBound G n c T = labI (inst0 G n c) + T + 1 := by
  unfold EntryPrepVec.labBound labI
  dsimp only [inst0, EntryLevelWords.w0, EntryLevelWords.levelWords, TemplateEntry.actualWords]

theorem wordB_eq (G : EndpointGraph V E) (n c : ℕ) :
    ((2 * (EntryLevelWords.w0 G n c).wordB + 2) + 0) + 1 = wordI (inst0 G n c) := by
  unfold wordI
  dsimp only [inst0, EntryLevelWords.w0, EntryLevelWords.levelWords, TemplateEntry.actualWords]

theorem clearBound_eq (G : EndpointGraph V E) (n c : ℕ) :
    EntryTailClear.clearBound G n c = clearI (inst0 G n c) := by
  unfold EntryTailClear.clearBound clearI
  dsimp only [inst0, EntryTailClear.bnk0, EntryTailClear.r0, EntryTailClear.c0, wI,
    EntryLevelWords.levelWords, EntryWriter22Split.word22, ProtectedFullBankBridgeScratch.actualD,
    MatrixWeightedEntrySemantic.actualInput]

theorem inst0_pos (G : EndpointGraph V E) (n c : ℕ) :
    0 < cols (inst0 G n c).a (inst0 G n c).s (inst0 G n c).q (inst0 G n c).cy := by
  have hc : 0 < (inst0 G n c).cy := (EntryTailClear.M0 n).columns_pos
  have hq : 0 < (inst0 G n c).q := EthInapproximability.ParameterizedNP.GuardedSourceSlab.q2_pos G _
  unfold cols
  exact Nat.mul_pos (Nat.pow_pos hc) (Nat.pow_pos (Nat.mul_pos hq (Nat.pow_pos hc)))

end eqs

/-! ## The clear clock: every region cell is bounded by the bank, dimensions and word -/

theorem cellBank_len (w : EntryLayout.Words) (k : Fin EntryRunsRaw.K) :
    (EntryRunsRaw.cellBank w k).length ≤ ∑ i : Fin 19, (EntryLayout.common w i).length := by
  unfold EntryRunsRaw.cellBank
  rcases EntryRunsRaw.eo.symm k with i | r
  · exact Finset.single_le_sum (f := fun i => (EntryLayout.common w i).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  · simp

theorem region_len (w : EntryLayout.Words) (r c : ℕ) (word : List Bool)
    (x : EntryTailEmbed.Region) :
    (RawTableTail.exitBank (EntryRunsRaw.cellBank w) r c (fun _ => []) word
      (EntryTailClear.regTail x)).length ≤
      (∑ i : Fin 19, (EntryLayout.common w i).length) + r + c + word.length := by
  rcases x with ((k | j) | e) | i
  · have := cellBank_len w k
    show (EntryRunsRaw.cellBank w k).length ≤ _
    omega
  · fin_cases j <;>
      simp [EntryTailClear.regTail, RawTableTail.exitBank, RawTableTail.glob,
        MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell, MatrixTableWriter.ready]
  · cases e <;>
      simp [EntryTailClear.regTail, RawTableTail.exitBank, RawTableTail.glob,
        MatrixTableWriter.Data.contents, MatrixTableWriter.Data.foreign, MatrixTableWriter.ready] <;>
      omega
  · simp [EntryTailClear.regTail, RawTableTail.exitBank, RawTableTail.glob]

theorem common_sum (w : EntryLayout.Words) :
    ∑ i : Fin 19, (EntryLayout.common w i).length =
      w.binB + w.wordB + w.binPowS + w.q + w.qOne + w.firstTable.length + 1 + w.cy +
        w.firstExp + w.cyPowF + w.rx + w.rowTable.length + w.Rtable.length + w.s + w.sM1 +
        w.cyPow1 + w.vtable.length + w.sL + w.L := by
  simp [Fin.sum_univ_succ, EntryLayout.common, EntryLayout.rep]
  omega

/-- The per-cell majorant of the clear clock. -/
def cellB (I : Inst) : ℕ :=
  (∑ i : Fin 19, (EntryLayout.common (wI I) i).length) + rows I.s I.L I.nv I.nb I.rx +
    cols I.a I.s I.q I.cy + rows I.s I.L I.nv I.nb I.rx * cols I.a I.s I.q I.cy

theorem clearI_le (I : Inst) : clearI I ≤ EntryTailClear.nR * cellB I + EntryTailClear.nR + 2 := by
  unfold clearI
  have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin EntryTailClear.nR))
    (fun i => (RawTableTail.exitBank (EntryRunsRaw.cellBank (wI I))
    (rows I.s I.L I.nv I.nb I.rx) (cols I.a I.s I.q I.cy) (fun _ => [])
    (rawTable I.R I.a I.s I.q I.L I.nv I.nb I.hs I.family I.order I.vectors I.cap)
    (EntryTailClear.regTail ((Fintype.equivFin EntryTailEmbed.Region).symm i))).length) (cellB I)
    (fun i _ => by
      have := region_len (wI I) (rows I.s I.L I.nv I.nb I.rx) (cols I.a I.s I.q I.cy)
        (rawTable I.R I.a I.s I.q I.L I.nv I.nb I.hs I.family I.order I.vectors I.cap)
        ((Fintype.equivFin EntryTailEmbed.Region).symm i)
      rw [rawTable_length] at this
      unfold cellB
      exact this)
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-! ## Uniform polynomial bounds over instances with an address -/

theorem cellB_poly : PolyIn (fun i : PI => i.1.U) (fun i => cellB i.1) := by
  unfold cellB
  simp only [common_sum, wI, TemplateEntry.actualWords, MatrixStage4FamilyData.fieldTable_length,
    rowMajor_length]
  repeat' (poly_step Subtype.val (fun i : PI => i.2))

theorem boundAI_poly : PolyIn (fun i : PI => i.1.U) (fun i => boundAI i.1) := by
  unfold boundAI copyCostI DerivedScalars.bound
  simp only [MatrixAddressMachine.exactTime]
  repeat' (poly_step Subtype.val (fun i : PI => i.2))

theorem labI_poly : PolyIn (fun i : PI => i.1.U) (fun i => labI i.1) := by
  unfold labI
  simp only [MatrixUnaryDivision.exactTime]
  repeat' (poly_step Subtype.val (fun i : PI => i.2))

theorem wordI_poly : PolyIn (fun i : PI => i.1.U) (fun i => wordI i.1) := by
  unfold wordI
  repeat' (poly_step Subtype.val (fun i : PI => i.2))

theorem writerI_poly : PolyIn (fun i : PI => i.1.U) (fun i => writerI i.1) :=
  PolyIn.comap Subtype.val (fun _ => le_rfl) writer_poly

theorem clearI_poly : PolyIn (fun i : PI => i.1.U) (fun i => clearI i.1) :=
  PolyIn.mono (fun i => clearI_le i.1)
    (PolyIn.add (PolyIn.add (PolyIn.mul (PolyIn.const _) cellB_poly) (PolyIn.const _))
      (PolyIn.const _))

/-- The instance-determined part of the level-0 writer-22 clock. -/
noncomputable def restI (I : Inst) : ℕ :=
  boundAI I + labI I + wordI I + writerI I + clearI I

theorem restI_poly : PolyIn (fun i : PI => i.1.U) (fun i => restI i.1) :=
  PolyIn.add (PolyIn.add (PolyIn.add (PolyIn.add boundAI_poly labI_poly) wordI_poly)
    writerI_poly) clearI_poly

#print axioms boundA_eq
#print axioms labBound_eq
#print axioms wordB_eq
#print axioms clearBound_eq
#print axioms region_len
#print axioms clearI_le
#print axioms cellB_poly
#print axioms boundAI_poly
#print axioms labI_poly
#print axioms restI_poly

end EthInapproximability.CurrentPaper.EntryClockPoly
