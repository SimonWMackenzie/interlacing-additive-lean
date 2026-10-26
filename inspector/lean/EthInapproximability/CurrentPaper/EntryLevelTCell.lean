import EthInapproximability.CurrentPaper.WeightedLevelFields15

/-!
# The balance-order word `t` is retained on the actual level bank

Lane owner:b-stage4-entry-program-2, segment 1 (wiring support).

The admitted `WeightedLevelFields15.level_fields15_identity` exposes `a, q, L`
(save 0, 1, 2) and `rx` (writer 17) but not `t = Parameters.balanceOrder i`.
This module proves, by evaluating the definitional chain of the SAME exit
banks (no new machine), that the scalar cell `WeightedActualSizeSuffix.scalar 1`
(the threshold arithmetic's own `t` input cell, source-preserved by its charged
copy into the prime search) still holds `unary t` in the level exit bank `Z`,
for every value of the existential scratch `F, Q, P`.
-/

namespace EthInapproximability.CurrentPaper.EntryLevelTCell

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevelColumnSave

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

/-- The retained `t` cell of the level bank. -/
def tcell : WeightedLevelColumnSave.Stack := .inl (WeightedActualSizeSuffix.scalar 1)

theorem threshold_t (S : WeightedThresholdInputJoin.Stack → List Bool)
    (W : Fin 64 → List Bool) (q t m : ℕ) (F : ChosenPrimeRaw.Stack → List Bool) :
    WeightedThresholdToSize.finalBank S W q t m F (WeightedThresholdToSize.scalar 1) =
      List.replicate t true := by
  unfold WeightedThresholdToSize.finalBank
  rw [bank_outside]
  · unfold WeightedThresholdToSize.afterTCopy WeightedThresholdToSize.afterXCopy
    rw [Function.update_of_ne (by intro e; cases e),
      Function.update_of_ne (by intro e; cases e)]
    unfold WeightedThresholdToSize.afterThreshold
    have h1 : WeightedThresholdToSize.scalar 1 = WeightedThresholdToSize.thresholdSlots 1 := rfl
    rw [h1, bank_at]
    exact (Paper2.WeightedThresholdArithmetic.final_slots q t m).2.1
  · rintro ⟨k, hk⟩
    rcases k with k | (k | k) <;> cases hk

theorem size_suffix_t (S : WeightedPrefixAT.Stack → List Bool) (a rx q t : ℕ)
    (P : ChosenPrimeRaw.Stack → List Bool) :
    WeightedActualSizeSuffix.finalBank S a rx q t P (WeightedActualSizeSuffix.scalar 1) =
      List.replicate t true := by
  unfold WeightedActualSizeSuffix.finalBank
  have h1 : WeightedActualSizeSuffix.scalar 1 =
      WeightedActualSizeSuffix.thresholdSlots (.inl (.inr 1)) := rfl
  rw [h1, bank_at]
  exact threshold_t _ _ q t _ P

theorem column_t (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ) :
    WeightedColumnActualStage.exitBank T a s q L rx cy (WeightedActualSizeSuffix.scalar 1) =
      T (WeightedActualSizeSuffix.scalar 1) := by
  unfold WeightedColumnActualStage.exitBank
  rw [bank_outside]
  rintro ⟨k, hk⟩
  cases hk

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]

/-- In the admitted level exit bank `Z` (for every scratch `F, Q, P`), the
cell `tcell` holds `unary (Iteration.t₂ …)`. -/
theorem level_t (G : EndpointGraph VG EG) (c b y lvl : ℕ) (M : Iteration.Matrix)
    (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool)
    (P : ChosenPrimeRaw.Stack → List Bool) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    let i := Iteration.stepParameters G c b y lvl M
    let g := EncodedETHSource.serializeGraph G
    let s := Parameters.bins i
    let q := ParameterizedNP.GuardedSourceSlab.q2 G s
    let a := Parameters.firstExponent i
    let L := PrimeSampler.size q (Parameters.balanceOrder i)
      (Construction.qOne a * i.rows)
    let W'' := Function.update
      (Function.update W 27 (List.replicate i.columns true))
      17 (List.replicate i.rows true)
    let T := WeightedScalarComplete.finalBank i g W'' F Q P i.rows q
    let X := Function.update (exitBank T a s q L i.rows i.columns)
      (wcell 16) (List.replicate (s * L) true)
    let Y := WeightedLevelFields1346.fieldsBank X d.binBase d.rawWidth d.s
    let Z := WeightedLevelFields15.counts15Bank Y d.s
    Z tcell = List.replicate (Iteration.t₂ G c b y lvl M) true := by
  intro d i g s q a L W'' T X Y Z
  have hw (k : Fin 64) : tcell ≠ wcell k := by
    intro e; cases e
  simp only [Z, Y, X, WeightedLevelFields15.counts15Bank,
    WeightedLevelFields1346.fieldsBank]
  rw [Function.update_of_ne (hw 15), Function.update_of_ne (hw 9),
    Function.update_of_ne (hw 8), Function.update_of_ne (hw 6),
    Function.update_of_ne (hw 4), Function.update_of_ne (hw 3),
    Function.update_of_ne (hw 1), Function.update_of_ne (hw 16)]
  show WeightedColumnActualStage.exitBank T a s q L i.rows i.columns
    (WeightedActualSizeSuffix.scalar 1) = _
  rw [column_t]
  show WeightedActualSizeSuffix.finalBank _ _ _ _ _ _ (WeightedActualSizeSuffix.scalar 1) = _
  exact size_suffix_t _ _ _ _ _ _

#print axioms threshold_t
#print axioms size_suffix_t
#print axioms column_t
#print axioms level_t

end

end EthInapproximability.CurrentPaper.EntryLevelTCell
