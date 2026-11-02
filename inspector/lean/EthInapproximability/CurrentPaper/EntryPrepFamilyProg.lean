import EthInapproximability.CurrentPaper.EntryPrepFamilyEmb

/-!
# Lane owner:b-stage4-entry-program-8: the fixed program `progF` (Family4Spec instance)

ONE fixed program on `HStack`, seven phases, six charged handoffs (`BitMachineRawSequence`),
from `midBank4`:

A. `CopyFill` (owner-4 / admitted `CopyFill`, temp writer 37): master `Gw` (the literal graph
   bytes) -> the workspace parser-input cell `ι pInF`;
B. one push of `true` on `ι pInF` (so it holds `true :: encode (serializeGraph G)`, the
   guarded code the admitted level start bank expects);
C. `CopyFill`: masters `C`, `E`, writers 17, 27, masters `Y`, `B` -> the six raw parameter
   cells `ι (rawF 0) ... ι (rawF 5)` (the six words of `Iteration.stepParameters … 0 M`);
   after A-C the bank is `bank ι midBank4 (Sum.elim (initialBank i g noW) blankA)`, the lifted
   start bank of the admitted `EntryFamilyLevel.program` (`WeightedRawWords.consumer_chain`);
D. the admitted `EntryFamilyLevel.program`, lifted along `ι` (`BitMachineStackRun.run`);
E. `CopyFill`: family `.first` -> cw 5, `.row` -> cw 11, `.w` (`qOne a`) -> cw 4 and -> cw 8;
F. the admitted `copyProgram` (source-preserving append): writer 28 (`s`) onto cw 8, giving
   `rep s ++ rep (qOne a) = rep (firstLength a s - 1)`;
G. the admitted pop clear `WeightedRawWords.clearProgram cellsF` of all 321 workspace cells.
Nothing here depends on `G, n, c`.
-/

namespace EthInapproximability.CurrentPaper.EntryPrepFamily

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec

/-! ## Named workspace cells -/

def rawF (j : Fin 6) : EntryFamilyLevel.Stack := .inl (.inl (WeightedRawWords.consRaw j))
def pInF : EntryFamilyLevel.Stack := .inl (.inl WeightedRawWords.pInCons)
def aF (c : FamilyRowBody.Cell) : EntryFamilyLevel.Stack := .inr (EntryFamilyAssembly.cell c)

theorem rawF_inj : Function.Injective rawF := by
  intro i j h
  have h1 : WeightedRawWords.consRaw i = WeightedRawWords.consRaw j := by
    simpa [rawF] using h
  have h2 : WeightedRawWords.rawCell i = WeightedRawWords.rawCell j := by
    rw [← WeightedRawWords.consRaw_eq, ← WeightedRawWords.consRaw_eq, h1]
  exact (WeightedRawWords.rawCell_inj' i j).1 h2

theorem rawF_ne_pIn (j : Fin 6) : rawF j ≠ pInF := by
  intro h
  have h1 : WeightedRawWords.consRaw j = WeightedRawWords.pInCons := by
    simpa [rawF, pInF] using h
  apply WeightedRawWords.rawCell_ne_pIn j
  rw [← WeightedRawWords.consRaw_eq, h1]
  rfl

/-! ## Separation facts for the workspace image -/

theorem ι_ne_tj (x : EntryFamilyLevel.Stack) (i : Fin 19) : ι x ≠ tailEmb (tj i) :=
  fmap_ne_tj _ i
theorem ι_ne_wj (x : EntryFamilyLevel.Stack) (k : Fin 64) : ι x ≠ tailEmb (wj k) :=
  fmap_ne_wj _ k
theorem ι_ne_mC (x : EntryFamilyLevel.Stack) : ι x ≠ mcell .C := fmap_ne_m _ _ (by simp)
theorem ι_ne_mB (x : EntryFamilyLevel.Stack) : ι x ≠ mcell .B := fmap_ne_m _ _ (by simp)
theorem ι_ne_mY (x : EntryFamilyLevel.Stack) : ι x ≠ mcell .Y := fmap_ne_m _ _ (by simp)
theorem ι_ne_mE (x : EntryFamilyLevel.Stack) : ι x ≠ mcell .E := fmap_ne_m _ _ (by simp)
theorem ι_ne_mGw (x : EntryFamilyLevel.Stack) : ι x ≠ mcell .Gw := fmap_ne_m _ _ (by simp)

theorem wj_ne_m (k : Fin 64) (a : WeightedRawWords.Aux) : tailEmb (wj k) ≠ mcell a := by
  intro h; cases h

/-! ## Phase jobs -/

noncomputable def jobsA : List (HStack × List HStack) := [(mcell .Gw, [ι pInF])]

noncomputable def jobsC : List (HStack × List HStack) :=
  [(mcell .C, [ι (rawF 0)]), (mcell .E, [ι (rawF 5)]), (tailEmb (wj 17), [ι (rawF 3)]),
   (tailEmb (wj 27), [ι (rawF 4)]), (mcell .Y, [ι (rawF 2)]), (mcell .B, [ι (rawF 1)])]

noncomputable def jobsE : List (HStack × List HStack) :=
  [(ι (aF .first), [tailEmb (tj 5)]), (ι (aF .row), [tailEmb (tj 11)]),
   (ι (aF .w), [tailEmb (tj 4)]), (ι (aF .w), [tailEmb (tj 8)])]

theorem goodA : CopyFill.Good tempW jobsA where
  src_not_dst := by
    simp only [jobsA, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq]
    exact fun h => ι_ne_mGw _ h.symm
  dst_nodup := by simp [jobsA]
  src_temp := by
    simp only [jobsA, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq, tempW]
    exact fun h => wj_ne_m 37 _ h.symm
  temp_dst := by
    simp only [jobsA, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq, tempW]
    exact fun h => ι_ne_wj _ 37 h.symm

theorem goodC : CopyFill.Good tempW jobsC where
  src_not_dst := by
    simp only [jobsC, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
      | exact fun h => ι_ne_mC _ h.symm
      | exact fun h => ι_ne_mE _ h.symm
      | exact fun h => ι_ne_mY _ h.symm
      | exact fun h => ι_ne_mB _ h.symm
      | exact fun h => ι_ne_wj _ _ h.symm
  dst_nodup := by
    simp only [jobsC, List.flatMap_cons, List.flatMap_nil, List.singleton_append,
      List.append_nil]
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      EmbeddingLike.apply_eq_iff_eq, rawF_inj.eq_iff, List.nodup_nil, or_false]
    decide
  src_temp := by
    simp only [jobsC, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, tempW]
    refine ⟨fun h => wj_ne_m 37 _ h.symm, fun h => wj_ne_m 37 _ h.symm, ?_, ?_,
      fun h => wj_ne_m 37 _ h.symm, fun h => wj_ne_m 37 _ h.symm⟩ <;>
    · simp [wj]
  temp_dst := by
    simp only [jobsC, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, tempW]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact fun h => ι_ne_wj _ 37 h.symm

theorem goodE : CopyFill.Good tempW jobsE where
  src_not_dst := by
    simp only [jobsE, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    exact ι_ne_tj _ _
  dst_nodup := by
    simp [jobsE, tj]
  src_temp := by
    simp only [jobsE, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, tempW]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact ι_ne_wj _ 37
  temp_dst := by
    simp [jobsE, tempW, wj, tj]

/-! ## The append copy (phase F) -/

noncomputable def idx3 : Fin 3 → TSt := ![wj 28, tj 8, wj 37]

theorem idx3_inj : Function.Injective idx3 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [idx3, wj, tj] at h)

noncomputable def ι3 : Fin 3 ↪ HStack := ⟨fun k => tailEmb (idx3 k), tailEmb.injective.comp idx3_inj⟩

/-! ## The program -/

noncomputable def famP := fun l => stackStmt ι (EntryFamilyLevel.program l)

noncomputable def QFG :=
  BitMachineRawSequence.program (MatrixStage4ScalarPreparationOps.copyProgram ι3)
    (WeightedRawWords.clearProgram cellsF) (0 : Fin (nF + 2)) (none : Option Bool)
    ((), (none : Option Bool))
noncomputable def QEFG :=
  BitMachineRawSequence.program (MultiMove.program (jobsE.map CopyFill.toJob) tempW) QFG
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) MultiMove.initial
    ((none : Option Bool), ((), (none : Option Bool)))
noncomputable def QDEFG :=
  BitMachineRawSequence.program famP QEFG
    (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsE.map CopyFill.toJob)))
    EntryFamilyLevel.initialControl
    (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))
noncomputable def QCDEFG :=
  BitMachineRawSequence.program (MultiMove.program (jobsC.map CopyFill.toJob) tempW) QDEFG
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))))
    MultiMove.initial
    (EntryFamilyLevel.initialControl,
      (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))
noncomputable def QBCDEFG :=
  BitMachineRawSequence.program (pushP (ι pInF)) QCDEFG
    (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsC.map CopyFill.toJob))) ()
    (MultiMove.initial, (EntryFamilyLevel.initialControl,
      (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))

/-- The single fixed program of this lane (the `W` of `Family4Spec`). -/
noncomputable def progF :=
  BitMachineRawSequence.program (MultiMove.program (jobsA.map CopyFill.toJob) tempW) QBCDEFG
    (BitMachineRawSequence.leftLabel ()) MultiMove.initial
    ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
      (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))

end EthInapproximability.CurrentPaper.EntryPrepFamily
