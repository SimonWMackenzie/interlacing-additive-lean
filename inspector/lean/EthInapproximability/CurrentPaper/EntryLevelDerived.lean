import EthInapproximability.CurrentPaper.DerivedScalars
import EthInapproximability.CurrentPaper.EntryLevelWords
import EthInapproximability.CurrentPaper.EntryExitBlank

/-!
# Segment 5 (partial): the derived words produced on the actual level-0 prep exit

Lane owner:b-stage4-entry-program-5 (Paper B, unit 2, map item 3).

`DerivedScalars.program ιL` runs on the level stack `HStack` itself, reading
writers 28, 27, 29, 16, 18, 15, 17 of the prep exit bank and writing into
twelve fresh scale cells (blank at the exit). From the exact prep exit bank
it halts on the exit bank with `s - 1`, `cy^(s+1)`, `binBase^s`, `[true]` and
the raw row count `rows s L nv nb rx` in five fresh cells (literally the
common words `sM1`, `cyPow1`, `binPowS`, `[true]` of `levelWords` at level 0
and the writer row count of the raw-table tail), every other cell unchanged.
-/

namespace EthInapproximability.CurrentPaper.EntryLevelDerived

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open MatrixStage4Codes

/-- The seven writer inputs `s, cy, binBase, s*L, nv, nb, rx`. -/
def inW : Fin 7 → Fin 64 := ![28, 27, 29, 16, 18, 15, 17]

theorem inW_inj : Function.Injective inW := by decide

/-- Twelve fresh scale cells (the `tail` block of the scale controller). -/
def freshCell (j : Fin 12) : HStack :=
  fresh (Sum.inl (Sum.inr (Sum.inl (Fin.castLE (by decide) j))) : SStack)

def idx (k : Fin 19) : HStack :=
  if h : k.val < 7 then wcell (inW ⟨k.val, h⟩) else freshCell ⟨k.val - 7, by omega⟩

theorem idx_inj : Function.Injective idx := by
  intro a b hab
  unfold idx at hab
  by_cases ha : a.val < 7 <;> by_cases hb : b.val < 7
  · rw [dif_pos ha, dif_pos hb] at hab
    have h1 : wc (inW ⟨a.val, ha⟩) = wc (inW ⟨b.val, hb⟩) := Sum.inl.inj (Sum.inl.inj hab)
    have h2 := inW_inj (wc_inj h1)
    exact Fin.ext (by simpa using h2)
  · rw [dif_pos ha, dif_neg hb] at hab
    cases hab
  · rw [dif_neg ha, dif_pos hb] at hab
    cases hab
  · rw [dif_neg ha, dif_neg hb] at hab
    simp only [freshCell, fresh, Sum.inr.injEq, Sum.inl.injEq] at hab
    have h3 := congrArg Fin.val hab
    simp only [Fin.val_castLE] at h3
    exact Fin.ext (by omega)

def ιL : Fin 19 ↪ HStack := ⟨idx, idx_inj⟩

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-0 table input record. -/
abbrev d0 (G : EndpointGraph V E) (n c : ℕ) :=
  ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix

theorem level_derived_scalars (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    let S := exitBank G n c (G4 (level0RowsBank Mm G n c F Q P))
    let d := d0 G n c
    ∃ t ≤ DerivedScalars.bound d.s d.cy d.binBase d.stagePrefixRows d.nv d.nb d.rx,
      ((advance (DerivedScalars.program ιL))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (MultiMove.startLabel ((DerivedScalars.jobs1 ιL).map CopyFill.toJob))),
          DerivedScalars.initial, S⟩ : TM2.Cfg (fun _ : HStack => Bool) _ _) =
        ⟨none, DerivedScalars.initial,
          DerivedScalars.outBank ιL S d.s d.cy d.binBase d.stagePrefixRows d.nv d.nb d.rx⟩ := by
  intro S d
  have hw : ∀ k : Fin 64, (∀ j, MatrixWeightedOrderPreparation.slots j ≠ k) → k ≠ 22 →
      S (wcell k) = MatrixWeightedEntryController.persistentBank d k :=
    fun k hk h22 => EntryLevelWords.exit_writer_cell Mm G n c F Q P hf k hk h22
  have pb : MatrixWeightedEntryController.persistentBank d 28 = List.replicate d.s true ∧
      MatrixWeightedEntryController.persistentBank d 27 = List.replicate d.cy true ∧
      MatrixWeightedEntryController.persistentBank d 29 = List.replicate d.binBase true ∧
      MatrixWeightedEntryController.persistentBank d 16 =
        List.replicate d.stagePrefixRows true ∧
      MatrixWeightedEntryController.persistentBank d 18 = List.replicate d.nv true ∧
      MatrixWeightedEntryController.persistentBank d 15 = List.replicate d.nb true ∧
      MatrixWeightedEntryController.persistentBank d 17 = List.replicate d.rx true := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [MatrixWeightedEntryController.persistentBank]
  obtain ⟨p28, p27, p29, p16, p18, p15, p17⟩ := pb
  refine DerivedScalars.derived_scalars ιL S d.s d.cy d.binBase d.stagePrefixRows d.nv d.nb d.rx
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show S (wcell 28) = _
    rw [hw 28 (by decide) (by decide), p28]; rfl
  · show S (wcell 27) = _
    rw [hw 27 (by decide) (by decide), p27]; rfl
  · show S (wcell 29) = _
    rw [hw 29 (by decide) (by decide), p29]; rfl
  · show S (wcell 16) = _
    rw [hw 16 (by decide) (by decide), p16]; rfl
  · show S (wcell 18) = _
    rw [hw 18 (by decide) (by decide), p18]; rfl
  · show S (wcell 15) = _
    rw [hw 15 (by decide) (by decide), p15]; rfl
  · show S (wcell 17) = _
    rw [hw 17 (by decide) (by decide), p17]; rfl
  · intro k hk
    show S (idx k) = []
    unfold idx
    rw [dif_neg (by omega)]
    exact EntryExitBlank.exit_blank_fresh G n c _ _

/-- The five produced words are literally the level's common words and the
raw row count of the tail. -/
theorem level_derived_values (G : EndpointGraph V E) (n c : ℕ) :
    let d := d0 G n c
    let w := EntryLevelWords.w0 G n c
    DerivedScalars.rep (d.s - 1) = EntryLayout.rep w.sM1 ∧
    DerivedScalars.rep (d.cy ^ (d.s + 1)) = EntryLayout.rep w.cyPow1 ∧
    DerivedScalars.rep (d.binBase ^ d.s) = EntryLayout.rep w.binPowS ∧
    DerivedScalars.rep (d.stagePrefixRows + (d.nv + d.nb) * d.rx) =
      EntryLayout.rep (rows w.s w.L d.nv d.nb w.rx) := by
  intro d w
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms idx_inj
#print axioms level_derived_scalars
#print axioms level_derived_values

end EthInapproximability.CurrentPaper.EntryLevelDerived
