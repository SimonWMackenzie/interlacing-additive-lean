import CurrentAdditive.V2ItemFrameCore

/-! The fixed Fin64 V2 writer layout for a prepared feature descriptor. -/

namespace CurrentAdditive.V2FeatureFrameLayout64

open EthInapproximability.CurrentPaper
open CurrentAdditive.V2ItemFrameCore
open Turing BitMachineEncoding

private noncomputable abbrev W := SourceListMachineWriter.framingMachine true

noncomputable def embedded (i : Fin W.stackCount) : Fin 64 :=
  ⟨41+i.val, by
    have hi : i.val < 8 := by simpa only [show W.stackCount = 8 by rfl] using i.isLt
    omega⟩

theorem embedded_injective : Function.Injective embedded := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [embedded] at hv
  omega

noncomputable def slots : Slots 32 where
  machine := ⟨embedded, embedded_injective⟩
  source := 36
  target := 5
  scratch := 7
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have hv := congrArg Fin.val h; simp [embedded] at hv; omega
  target_machine := by intro i h; have hv := congrArg Fin.val h; simp [embedded] at hv; omega
  scratch_machine := by intro i h; have hv := congrArg Fin.val h; simp [embedded] at hv; omega

theorem run (S : Fin 64 → List Bool) (raw : List Bool)
    (hs : S 36 = raw) :
    ∃ u ≤ time slots S raw,
      ((advance (program slots))^[u])
        (⟨some (start slots), control slots, S⟩ :
          Turing.TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
        ⟨none, control slots,
          Function.update (cleared slots S) 5
            (EncodedCommunication.natField raw.length ++ raw)⟩ := by
  exact V2ItemFrameCore.run slots S raw hs

#print axioms run

end CurrentAdditive.V2FeatureFrameLayout64
