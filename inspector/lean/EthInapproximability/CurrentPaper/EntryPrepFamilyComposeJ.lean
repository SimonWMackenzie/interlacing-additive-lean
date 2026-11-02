import EthInapproximability.CurrentPaper.EntryPrepFamilyRunJ
import EthInapproximability.CurrentPaper.EntryWriter22J
import EthInapproximability.CurrentPaper.Level0Install

/-!
# Lane owner:b-entry-levelj-2: level-`j` writer 22 for ONE fixed program, and the KShell `hW`

Segment 2 (hand-written). The single fixed program is owner-1's `writerJ` applied to owner-8's
`progF` (both reused by exact name; neither mentions a level datum):
`writerJ progF wF vF = copy55 ; lift4 ((progA ; progV ; progC ; progL ; progF) ; tailClear)`.

* `writer22F_j`: the admitted consumer `RoundP.Writer22SpecJ` at an ARBITRARY level state, from the
  five level-state master facts only (`family4_j` fed to owner-1's `writer22J_of_family4`).
* `masters_phys`: the five master facts hold at every level `j` of the physical run for the admitted
  master region `StepP.mSj (Level0Install.mb1 M G n c) …` (from `Level0Install.base1`, `StepP.mSj`).
* `writer22F_phys`: `RoundP.Writer22SpecJ` at level `j` of the physical run, NO premise.
* `kshell_hW_F`: KShell's `hW` verbatim for `writerJ progF wF vF`, at every `1 ≤ j < k`, from ONE clock
  premise (a single `T22` majorizing the explicit per-level clocks).
* `kshell_hW_F'`: the same through owner-1's `kshell_hW_of_family4` literally (uniform `TF`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepFamilyJ

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open OuterLevel0Prep EntryPrepCopy EntryPrepVec EntryPrepFamily EntryPrepVecJ EntryWriter22J

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Monotonicity of the interface in its clock. -/
theorem family4J_mono {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW)
    (v₀ : VW) (T T' : ℕ) (G : EndpointGraph V E) (c bJ yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) (hle : T ≤ T')
    (hF : Family4SpecJ W w₀ v₀ T G c bJ yb lv Mx mS) :
    Family4SpecJ W w₀ v₀ T' G c bJ yb lv Mx mS := by
  intro F Q P hf
  obtain ⟨t, ht, v, h⟩ := hF F Q P hf
  exact ⟨t, le_trans ht hle, v, h⟩

/-- `RoundP.Writer22SpecJ` at an arbitrary level state, for the ONE program `writerJ progF wF vF`. -/
theorem writer22F_j (G : EndpointGraph V E) (c bJ yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (hmC : mS .C = List.replicate c true) (hmB : mS .B = List.replicate bJ true)
    (hmY : mS .Y = List.replicate (yb + lv) true)
    (hmE : mS .E = List.replicate (Fintype.card E) true)
    (hGw : mS .Gw = EncodedGraph.encode (EncodedETHSource.serializeGraph G)) :
    RoundP.Writer22SpecJ
      (writerJ progF
        (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
        (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
          (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
      (MultiMove.initial, (prepInit ((MultiMove.initial, false),
          (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
            (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
        (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (writerBound_j G c bJ yb lv Mx (TFJ G c bJ yb lv Mx)) G c bJ yb lv Mx mS
      (EntryLevelJBank.matWord Mx) :=
  writer22J_of_family4 G c bJ yb lv Mx mS hGw progF _ _ (TFJ G c bJ yb lv Mx)
    (family4_j G c bJ yb lv Mx mS hmC hmB hmY hmE hGw)

/-- The five master facts at level `j` of the physical run. -/
theorem masters_phys (M : BitMachine.Machine) (G : EndpointGraph V E) (n c j : ℕ) :
    let mS := StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j
    mS .C = List.replicate c true ∧
    mS .B = List.replicate (EffectiveIteration.sourceDepth n) true ∧
    mS .Y = List.replicate (StepP.yP G c (EffectiveIteration.sourceDepth n) j + j) true ∧
    mS .E = List.replicate (Fintype.card E) true ∧
    mS .Gw = EncodedGraph.encode (EncodedETHSource.serializeGraph G) := by
  intro mS
  obtain ⟨_, _, _, hC, hB, hE, hGw⟩ := Level0Install.base1 M G n c
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show StepP.mSj _ G c _ j .C = _
    rw [StepP.mSj_ne _ _ _ _ _ _ (by intro h; cases h)]; exact hC
  · show StepP.mSj _ G c _ j .B = _
    rw [StepP.mSj_ne _ _ _ _ _ _ (by intro h; cases h)]; exact hB
  · show Function.update (Level0Install.mb1 M G n c) WeightedRawWords.Aux.Y _ WeightedRawWords.Aux.Y = _
    rw [Function.update_self]
  · show StepP.mSj _ G c _ j .E = _
    rw [StepP.mSj_ne _ _ _ _ _ _ (by intro h; cases h)]; exact hE
  · show StepP.mSj _ G c _ j .Gw = _
    rw [StepP.mSj_ne _ _ _ _ _ _ (by intro h; cases h)]; exact hGw

/-- `Family4SpecJ progF` at level `j` of the physical run: no premise. -/
theorem family4_phys (M : BitMachine.Machine) (G : EndpointGraph V E) (n c j : ℕ) :
    Family4SpecJ progF
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
      (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
        (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))
      (TFJ G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j))
      G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
      (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j) := by
  obtain ⟨hC, hB, hY, hE, hGw⟩ := masters_phys M G n c j
  exact family4_j G c _ _ j _ _ hC hB hY hE hGw

/-- `RoundP.Writer22SpecJ` at level `j` of the physical run, for the ONE program, NO premise. -/
theorem writer22F_phys (M : BitMachine.Machine) (G : EndpointGraph V E) (n c j : ℕ) :
    RoundP.Writer22SpecJ
      (writerJ progF
        (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
        (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
          (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
      (MultiMove.initial, (prepInit ((MultiMove.initial, false),
          (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
            (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
        (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (writerBound_j G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (TFJ G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j)))
      G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
      (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
      (MatrixMaterialization.rowMajor
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) :=
  writer22J_of_family4 G c _ _ j _ _ (mSj_Gw M G n c j) progF _ _ _ (family4_phys M G n c j)

/-- KShell's `hW` (verbatim) for the ONE program `writerJ progF wF vF`, at every `1 ≤ j < k`,
from ONE clock premise. -/
theorem kshell_hW_F (M : BitMachine.Machine) (G : EndpointGraph V E) (n c k T22 : ℕ)
    (hT : ∀ j, 1 ≤ j → j < k →
      writerBound_j G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (TFJ G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ≤ T22) :
    ∀ j, 1 ≤ j → j < k →
      RoundP.Writer22SpecJ
        (writerJ progF
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
          (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
            (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
        (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
        (MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
        T22 G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) := by
  intro j hj1 hjk F Q P hf
  obtain ⟨t, ht, v, h⟩ := writer22F_phys M G n c j F Q P hf
  exact ⟨t, le_trans ht (hT j hj1 hjk), v, h⟩

/-- The same, literally through owner-1's `kshell_hW_of_family4` (one uniform family clock `TF`). -/
theorem kshell_hW_F' (M : BitMachine.Machine) (G : EndpointGraph V E) (n c k TF T22 : ℕ)
    (hTF : ∀ j, 1 ≤ j → j < k →
      TFJ G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ≤ TF)
    (hT : ∀ j, 1 ≤ j → j < k →
      writerBound_j G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) TF ≤ T22) :
    ∀ j, 1 ≤ j → j < k →
      RoundP.Writer22SpecJ
        (writerJ progF
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
          (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
            (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
        (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
        (MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
        T22 G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) :=
  kshell_hW_of_family4 M G n c k progF _ _ TF T22
    (fun j hj1 hjk => family4J_mono _ _ _ _ _ G c _ _ j _ _ (hTF j hj1 hjk) (family4_phys M G n c j)) hT

#print axioms family4J_mono
#print axioms writer22F_j
#print axioms masters_phys
#print axioms family4_phys
#print axioms writer22F_phys
#print axioms kshell_hW_F
#print axioms kshell_hW_F'

end EthInapproximability.CurrentPaper.EntryPrepFamilyJ
