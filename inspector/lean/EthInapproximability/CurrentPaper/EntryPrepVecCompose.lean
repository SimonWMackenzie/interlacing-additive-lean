import EthInapproximability.CurrentPaper.EntryPrepVecRun

/-!
# Segment 5b (composition): `RestSpec` from the family-only interface `FamilySpec`

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

`FamilySpec W`: from `midBank2` (tail start bank with cw 4, 5, 8, 9, 11, 18 still blank) to
`tailStart`. `rest_of_family`: `RestSpec (progV ; W)`. With `EntryPrepCopy.prep_of_rest`
and `EntryTailClear.level0_writer22_of_prep` this gives `OuterLevel0Full.Writer22Spec` from
`FamilySpec` alone (`level0_writer22_of_family`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- What remains of segment 5 after 5a and 5b: the six family/level words
(cw 4 `qOne a`, cw 5 first table, cw 8 `firstLength a s - 1`, cw 9 `cy^firstLength a s`,
cw 11 row table, cw 18 `L`) into their tail cells, every other cell restored. -/
def FamilySpec {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW)
    (v₀ : VW) (T : ℕ) (G : EndpointGraph V E) (n c : ℕ) : Prop :=
  ∀ F Q P, level0Facts Mm G n c F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t]) ⟨some w₀, v₀, midBank2 Mm G n c F Q P⟩ =
        ⟨none, v₁, tailStart Mm G n c F Q P⟩

noncomputable def initV :=
  (MultiMove.initial, ((), (VectorsFromGraphQ.initial,
    (MultiMove.initial, ((), (none : Option Bool))))))

theorem rest_of_family (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : FamilySpec Mm W w₀ v₀ T G n c) :
    RestSpec Mm (BitMachineRawSequence.program progV W w₀ initV v₀)
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel (jobs1.map CopyFill.toJob))))
      (initV, v₀) (boundV G n c + T + 1) G n c := by
  intro F Q P hf
  obtain ⟨ta, hta, va, ha⟩ := vec_run Mm G n c F Q P hf
  obtain ⟨tb, htb, v₁, hb⟩ := hF F Q P hf
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs progV W _ w₀ initV va v₀ v₁ _ _ _ ta tb ha hb
  exact ⟨t, by omega, _, hr⟩

theorem prep_of_family (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : FamilySpec Mm W w₀ v₀ T G n c) :
    PrepSpec Mm
      (BitMachineRawSequence.program progA (BitMachineRawSequence.program progV W w₀ initV v₀)
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (MultiMove.startLabel (jobs1.map CopyFill.toJob))))
        (MultiMove.initial, DerivedScalars.initial) (initV, v₀))
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel (copyJobs.map CopyFill.toJob))))
      ((MultiMove.initial, DerivedScalars.initial), (initV, v₀))
      (boundA G n c + (boundV G n c + T + 1) + 1) G n c :=
  prep_of_rest Mm G n c _ _ _ _ (rest_of_family Mm G n c W w₀ v₀ T hF)

#print axioms rest_of_family
#print axioms prep_of_family

end EthInapproximability.CurrentPaper.EntryPrepVec
