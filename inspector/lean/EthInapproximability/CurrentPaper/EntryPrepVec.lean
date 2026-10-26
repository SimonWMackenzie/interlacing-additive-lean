import EthInapproximability.CurrentPaper.EntryPrepVecEmb

/-!
# Segment 5b: `q` and `rowMajor vectors` recomputed into their tail cells

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

ONE fixed program `progV` on `HStack`, five phases, four charged handoffs, from `midBank`:
1. owner-4 `CopyFill`: master `Gw` (the literal graph bytes `encode (serializeGraph G)`) into
   the workspace input cell `ζ (inp 0)`; writer 28 (unary `s`) into `ζ (inp 1)`;
2. one push of `true` on `ζ (inp 0)` (so it holds `VectorsProducer.code G = true :: bytes`);
3. the admitted `VectorsFromGraphQ.program`, lifted along `ζ` (`BitMachineStackRun.run`),
   with the growth-annotated run `vectors_growth`;
4. `CopyFill`: `ζ (inp 2)` (unary `q2 G s`) into tail cw 3, the writer output cell
   (`rowMajor vectors`) into tail cw 16;
5. the admitted pop clear `WeightedRawWords.clearProgram` of all 137 workspace cells.
Exit: `midBank2` = the tail start bank at `wMid2` (= `wMid` with `q` and `vtable` filled).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy
open VectorsProducer (Z b inp ex)

abbrev Z2 := VectorsFromGraphQ.Z2

noncomputable def zIn (j : Fin 3) : HStack := ζ (Sum.inl (inp j) : Z2)
noncomputable def zOut : HStack := ζ (Sum.inl (ex .output) : Z2)

/-! ## Phase programs -/

noncomputable def jobs1 : List (HStack × List HStack) :=
  [(mcell .Gw, [zIn 0]), (tailEmb (wj 28), [zIn 1])]

noncomputable def jobs4 : List (HStack × List HStack) :=
  [(zIn 2, [tailEmb (tj 3)]), (zOut, [tailEmb (tj 16)])]

theorem good1 : CopyFill.Good tempW jobs1 where
  src_not_dst := by
    simp only [jobs1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, zIn]
    exact ⟨⟨fun h => ζ_ne_mGw _ h.symm, fun h => ζ_ne_mGw _ h.symm⟩,
      ⟨fun h => tail_ne_ζ _ _ h, fun h => tail_ne_ζ _ _ h⟩⟩
  dst_nodup := by
    simp [jobs1, zIn, inp]
  src_temp := by
    simp only [jobs1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, tempW]
    refine ⟨fun h => tail_ne_mGw _ h.symm, ?_⟩
    simp [wj]
  temp_dst := by
    simp only [jobs1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, tempW, zIn]
    exact ⟨fun h => tail_ne_ζ _ _ h, fun h => tail_ne_ζ _ _ h⟩

theorem good4 : CopyFill.Good tempW jobs4 where
  src_not_dst := by
    simp only [jobs4, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, zIn, zOut]
    exact ⟨⟨fun h => tail_ne_ζ _ _ h.symm, fun h => tail_ne_ζ _ _ h.symm⟩,
      ⟨fun h => tail_ne_ζ _ _ h.symm, fun h => tail_ne_ζ _ _ h.symm⟩⟩
  dst_nodup := by
    simp [jobs4, tj]
  src_temp := by
    simp only [jobs4, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, tempW, zIn, zOut]
    exact ⟨fun h => tail_ne_ζ _ _ h.symm, fun h => tail_ne_ζ _ _ h.symm⟩
  temp_dst := by
    simp [jobs4, tempW, wj, tj]

noncomputable def nZ : ℕ := Fintype.card Z2
noncomputable def cellsZ (i : Fin nZ) : HStack := ζ ((Fintype.equivFin Z2).symm i)
theorem cellsZ_inj : Function.Injective cellsZ :=
  fun a b h => (Fintype.equivFin Z2).symm.injective (ζ.injective h)

noncomputable def vecZ := fun l => stackStmt ζ (VectorsFromGraphQ.program l)

noncomputable def Q45 :=
  BitMachineRawSequence.program (MultiMove.program (jobs4.map CopyFill.toJob) tempW)
    (WeightedRawWords.clearProgram cellsZ) (0 : Fin (nZ + 2)) MultiMove.initial
    ((), (none : Option Bool))
noncomputable def Q345 :=
  BitMachineRawSequence.program vecZ Q45
    (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs4.map CopyFill.toJob)))
    VectorsFromGraphQ.initial (MultiMove.initial, ((), (none : Option Bool)))
noncomputable def Q2345 :=
  BitMachineRawSequence.program (pushP (zIn 0)) Q345
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    () (VectorsFromGraphQ.initial, (MultiMove.initial, ((), (none : Option Bool))))
noncomputable def progV :=
  BitMachineRawSequence.program (MultiMove.program (jobs1.map CopyFill.toJob) tempW) Q2345
    (BitMachineRawSequence.leftLabel ()) MultiMove.initial
    ((), (VectorsFromGraphQ.initial, (MultiMove.initial, ((), (none : Option Bool)))))

theorem ready_blank (t : VectorsProducer.TS) :
    (MatrixTableWriter.ready (K := 25) (fun _ => []) 0 0 0 0 0 0 [] []).contents t = [] := by
  rcases t with (k | i) | e
  · rfl
  · fin_cases i <;> rfl
  · cases e <;> rfl

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-0 number of bins. -/
abbrev sv (G : EndpointGraph V E) (n c : ℕ) : ℕ := Iteration.s G c (b0 n) (y0 n) 0 (M0 n)

/-- The words after 5b. -/
noncomputable def wMid2 (G : EndpointGraph V E) (n c : ℕ) : EntryLayout.Words :=
  let w := EntryLevelWords.w0 G n c
  ⟨w.binB, w.wordB, w.binPowS, w.q, 0, [], w.cy, 0, 0, w.rx, [], w.Rtable, w.s, w.sM1, w.cyPow1,
    w.vtable, w.sL, 0⟩

noncomputable def midBank2 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P)
    (RawTableTail.startBank (EntryRunsRaw.cellBank (wMid2 G n c)) (r0 G n c) (c0 G n c)
      (Wlvl Mm G n c F Q P))

/-- Public length allowance of a workspace cell at the end of phase 3. -/
noncomputable def lenB (G : EndpointGraph V E) (n c : ℕ) : Z2 → ℕ :=
  Sum.elim (fun z => (VectorsProducer.exitBank G (sv G n c) [] z).length)
    (fun j => (VectorsFromGraphQ.Qa G (sv G n c) j).length + growQ (sv G n c) (Fintype.card E))

noncomputable def boundV (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  ((2 * (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 2) +
      ((2 * sv G n c + 2) + 0) + 1) +
    (1 + (VectorsFromGraphQ.fullBound G (sv G n c) +
      ((((2 * q2 G (sv G n c) + 2) +
          ((2 * (MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c))).length + 2)
            + 0) + 1) +
        ((∑ i : Fin nZ, lenB G n c ((Fintype.equivFin Z2).symm i)) + nZ + 2) + 1) + 1) + 1) + 1) + 1

end EthInapproximability.CurrentPaper.EntryPrepVec
