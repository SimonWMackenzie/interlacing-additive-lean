import EthInapproximability.CurrentPaper.EntryTailEmbed

/-!
# Segment 6: embedded tail, charged clear, and `Writer22From` from ONE preparation interface

Lane owner:b-stage4-entry-program-6 (Paper B, unit 2, map item 3).

After the embedded tail (`EntryTailEmbed.embedded_tail`) the admitted pop clear
`WeightedRawWords.clearProgram regionCells` empties the 248 cells of the tail region
(`clear_region`): the result is the prep exit bank with ONLY writer 22 changed, to the
table word. Hence (`writer22_from_of_prep`) `EntryWriter22Split.Writer22From zO` holds for
the sequenced program `prep ; tail ; clear` as soon as the preparation interface
`PrepSpec` holds: from the prep exit bank with the matrix word in `oCell`, reach the tail's
start bank `tailStart` (the 19 common words and the rows/cols words in the tail region).
With `EntrySeedSpec.level0_writer22_of_from` this gives `OuterLevel0Full.Writer22Spec`
from `PrepSpec` alone (`level0_writer22_of_prep`).
-/

namespace EthInapproximability.CurrentPaper.EntryTailClear

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## The level-0 tail data -/

abbrev b0 (n : ℕ) := EffectiveIteration.sourceDepth n
abbrev y0 (n : ℕ) := (Iteration.seedState (b0 n)).budget
abbrev M0 (n : ℕ) := (Iteration.seedState (b0 n)).matrix

/-- The fixed common-word bank of the level-0 table. -/
noncomputable abbrev bnk0 (G : EndpointGraph V E) (n c : ℕ) :=
  EntryRunsRaw.cellBank (EntryLevelWords.levelWords G c (b0 n) (y0 n) 0 (M0 n))

/-- The level-0 table dimensions. -/
abbrev r0 (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  rows (Iteration.s G c (b0 n) (y0 n) 0 (M0 n)) (Iteration.labels G c (b0 n) (y0 n) 0 (M0 n))
    (GraphVectors.vertexCount V (Iteration.s G c (b0 n) (y0 n) 0 (M0 n)))
    (GraphVectors.auxiliaryCount (Iteration.s G c (b0 n) (y0 n) 0 (M0 n))) (M0 n).rows
abbrev c0 (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  cols (Iteration.a G c (b0 n) (y0 n) 0 (M0 n)) (Iteration.s G c (b0 n) (y0 n) 0 (M0 n))
    (Iteration.q₂ G c (b0 n) (y0 n) 0 (M0 n)) (M0 n).columns

/-- The tail clock (literally the bound of `embedded_tail`). -/
noncomputable def tailBound (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  MatrixTableWriter.writerBound (r0 G n c) (c0 G n c)
      (EntryRunsRaw.tableT (M0 n).entry
        (lt_of_lt_of_le (by decide : 0 < 4) (Iteration.bins_ge_four G c (b0 n) (y0 n) 0 (M0 n)))
        (Iteration.secondFamily G c (b0 n) (y0 n) 0 (M0 n))
        (GraphVectors.itemOrder G (Iteration.s G c (b0 n) (y0 n) 0 (M0 n)))
        (GraphVectors.vectors G (Iteration.s G c (b0 n) (y0 n) 0 (M0 n)))
        (GraphVectors.supportCap G
          (le_trans (by decide : 3 ≤ 4) (Iteration.bins_ge_four G c (b0 n) (y0 n) 0 (M0 n))))) +
    (2 * (r0 G n c * c0 G n c) + 2) + 1

/-- The tail's start bank on the level stack. -/
noncomputable def tailStart (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P)
    (RawTableTail.startBank (bnk0 G n c) (r0 G n c) (c0 G n c) (Wlvl Mm G n c F Q P))

/-! ## The region clear -/

abbrev nR : ℕ := Fintype.card Region

noncomputable def regionCells (i : Fin nR) : HStack :=
  nwMap (regionEmb ((Fintype.equivFin Region).symm i))

theorem regionCells_inj : Function.Injective regionCells := by
  intro i j h
  exact (Fintype.equivFin Region).symm.injective (regionEmb.injective (nwMap_inj h))

def regTail : Region → RawTableTail.Stack K
  | .inl a => .inl a
  | .inr i => .inr (.inr i)

theorem tailEmb_regTail (r : Region) : tailEmb (regTail r) = nwMap (regionEmb r) := by
  rcases r with a | i <;> rfl

theorem w22_eq : OuterLevel0Full.w22 = wcell 22 := rfl

noncomputable def clearProgram := WeightedRawWords.clearProgram regionCells

/-- The clear clock: the lengths of the tail region's exit contents (independent of the
writer bank), plus the admitted overhead. -/
noncomputable def clearBound (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  (∑ i : Fin nR, (RawTableTail.exitBank (bnk0 G n c) (r0 G n c) (c0 G n c) (fun _ => [])
    (EntryWriter22Split.word22 G n c) (regTail ((Fintype.equivFin Region).symm i))).length) + nR + 2

theorem exit_region_indep (bk : Fin K → List Bool) (r cl : ℕ) (W W' : Fin 64 → List Bool)
    (word : List Bool) (x : Region) :
    RawTableTail.exitBank bk r cl W word (regTail x) = RawTableTail.exitBank bk r cl W' word (regTail x) := by
  rcases x with a | i <;> rfl

theorem clear_region (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    let S := EntryWriter22Split.S0 Mm G n c F Q P
    let X := bank tailEmb S (RawTableTail.exitBank (bnk0 G n c) (r0 G n c) (c0 G n c)
      (Wlvl Mm G n c F Q P) (EntryWriter22Split.word22 G n c))
    ((advance clearProgram)^[clearBound G n c])
        (⟨some 0, ((), none), X⟩ : TM2.Cfg (fun _ : HStack => Bool) _ _) =
      ⟨none, ((), none), Function.update S OuterLevel0Full.w22 (EntryWriter22Split.word22 G n c)⟩ := by
  intro S X
  have hterm : ∀ i : Fin nR,
      (RawTableTail.exitBank (bnk0 G n c) (r0 G n c) (c0 G n c) (fun _ => [])
        (EntryWriter22Split.word22 G n c) (regTail ((Fintype.equivFin Region).symm i))).length =
      (X (regionCells i)).length := by
    intro i
    show _ = (bank tailEmb S _ (nwMap (regionEmb ((Fintype.equivFin Region).symm i)))).length
    rw [← tailEmb_regTail, bank_at, exit_region_indep _ _ _ _ (Wlvl Mm G n c F Q P)]
  have hsum : clearBound G n c = (∑ i, (X (regionCells i)).length) + nR + 2 := by
    unfold clearBound
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have key : BitMachineClearBank.cleared regionCells X =
      Function.update S OuterLevel0Full.w22 (EntryWriter22Split.word22 G n c) := by
    funext x
    by_cases hx : ∃ i, regionCells i = x
    · obtain ⟨i, rfl⟩ := hx
      rw [BitMachineClearBank.cleared_bank, w22_eq,
        Function.update_of_ne (show regionCells i ≠ wcell 22 from nwMap_ne_wcell _ _)]
      exact (exit_blank_nw Mm G n c F Q P _).symm
    · rw [BitMachineClearBank.cleared_foreign _ _ _ (fun i hi => hx ⟨i, hi⟩)]
      by_cases hy : ∃ y, tailEmb y = x
      · obtain ⟨y, rfl⟩ := hy
        rcases y with a | k | i
        · exact absurd ⟨Fintype.equivFin Region (.inl a), by
            simp [regionCells]; rfl⟩ hx
        · show bank tailEmb S _ (tailEmb (.inr (.inl k))) = _
          rw [bank_at]
          show Function.update (Wlvl Mm G n c F Q P) 22 (EntryWriter22Split.word22 G n c) k = _
          by_cases hk : k = 22
          · subst hk
            rw [Function.update_self, w22_eq]
            show _ = Function.update S (wcell 22) _ (wcell 22)
            rw [Function.update_self]
          · rw [Function.update_of_ne hk, w22_eq]
            rw [Function.update_of_ne (show tailEmb (.inr (.inl k)) ≠ wcell 22 from fun h =>
              hk (wc_inj (Sum.inl.inj (Sum.inl.inj h))))]
            rfl
        · exact absurd ⟨Fintype.equivFin Region (.inr i), by
            simp [regionCells]; rfl⟩ hx
      · simp only [not_exists] at hy
        show bank tailEmb S (RawTableTail.exitBank _ _ _ _ _) x = _
        rw [bank_outside _ _ _ _ (by rintro ⟨y, hy'⟩; exact hy y hy')]
        rw [Function.update_of_ne (by
          intro h
          rw [w22_eq] at h
          exact hy (.inr (.inl 22)) h.symm)]
  rw [hsum, show clearProgram = WeightedRawWords.clearProgram regionCells from rfl,
    WeightedRawWords.clear_run regionCells regionCells_inj X, key]

/-! ## `Writer22From` from the preparation interface -/

/-- The preparation interface: from the prep exit bank with the matrix word in `oCell`,
the fixed program `W` halts on the tail's start bank. -/
def PrepSpec {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW)
    (T : ℕ) (G : EndpointGraph V E) (n c : ℕ) : Prop :=
  ∀ (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool),
    level0Facts Mm G n c F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t])
          ⟨some w₀, v₀, Function.update (EntryWriter22Split.S0 Mm G n c F Q P) EntrySeedSpec.oCell
            (EntryWriter22Split.seedWord n)⟩ =
        ⟨none, v₁, tailStart Mm G n c F Q P⟩

/-- Tail then clear, as ONE fixed program. -/
noncomputable def tailClear :=
  BitMachineRawSequence.program tailProgram clearProgram (0 : Fin (nR + 2))
    (RawTableTail.startControl EntryRunsRaw.startControl) ((), (none : Option Bool))

theorem writer22_from_of_prep (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hP : PrepSpec Mm W w₀ v₀ T G n c) :
    EntryWriter22Split.Writer22From Mm EntrySeedSpec.zO
      (BitMachineRawSequence.program W tailClear
        (BitMachineRawSequence.leftLabel RawTableTail.startLabel) v₀
        (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
      (BitMachineRawSequence.leftLabel w₀)
      (v₀, (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
      (T + (tailBound G n c + clearBound G n c + 1) + 1) G n c := by
  intro F Q P hf
  obtain ⟨tp, htp, vp, hp⟩ := hP F Q P hf
  obtain ⟨tt, htt, ht⟩ := embedded_tail Mm G n c F Q P hf
  have hc := clear_region Mm G n c F Q P
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs tailProgram clearProgram
    RawTableTail.startLabel (0 : Fin (nR + 2))
    (RawTableTail.startControl EntryRunsRaw.startControl) ((EntryRunsRaw.startControl, none), none)
    ((), none) ((), none)
    (tailStart Mm G n c F Q P) _ _ tt (clearBound G n c) ht hc
  obtain ⟨t, ht2, hr2⟩ := BitMachineRawSequence.runs W tailClear w₀
    (BitMachineRawSequence.leftLabel RawTableTail.startLabel) v₀ vp
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))
    _ _ _ tp u hp hr
  refine ⟨t, ?_, (v₀, (RawTableTail.startControl EntryRunsRaw.startControl, ((), none))), ?_⟩
  · have : tt ≤ tailBound G n c := htt
    omega
  · exact hr2

theorem level0_writer22_of_prep (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hP : PrepSpec Mm W w₀ v₀ T G n c) :
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program W tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel) v₀
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel w₀)
        ((none : Option Bool), (none : Option Bool))
        (v₀, (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (v₀, (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (T + (tailBound G n c + clearBound G n c + 1) + 1) + 1) G n c :=
  EntrySeedSpec.level0_writer22_of_from Mm G n c _ _ _ _
    (writer22_from_of_prep Mm G n c W w₀ v₀ T hP)

#print axioms regionCells_inj
#print axioms clear_region
#print axioms writer22_from_of_prep
#print axioms level0_writer22_of_prep

end EthInapproximability.CurrentPaper.EntryTailClear
