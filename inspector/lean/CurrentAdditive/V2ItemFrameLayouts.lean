import CurrentAdditive.V2ItemFrameCore

/-! Two concrete layouts used by the packed getter and request serializer. -/

namespace CurrentAdditive.V2ItemFrameLayouts

open Turing Turing.TM2 EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext
open V2ItemFrameCore BitMachineEncoding

private noncomputable abbrev W := SourceListMachineWriter.framingMachine true

noncomputable def embedded64 (i : Fin W.stackCount) : Fin 64 :=
  ⟨if i.val < 5 then i.val else if i.val = 5 then 6 else
     if i.val = 6 then 61 else 62, by
    have hi : i.val < 8 := by simpa only [show W.stackCount = 8 by rfl] using i.isLt
    split_ifs <;> omega⟩

theorem embedded64_injective : Function.Injective embedded64 := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [embedded64, Fin.val_mk] at hv
  have hi : i.val < 8 := by simpa only [show W.stackCount = 8 by rfl] using i.isLt
  have hj : j.val < 8 := by simpa only [show W.stackCount = 8 by rfl] using j.isLt
  split_ifs at hv with hi5 hi6 hi7 hj5 hj6 hj7 <;> omega

noncomputable def slots64 : Slots 32 where
  machine := ⟨embedded64, embedded64_injective⟩
  source := 23
  target := 5
  scratch := 7
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by
    intro i h
    change (23 : Fin 64) = embedded64 i at h
    have hv := congrArg Fin.val h
    simp only [embedded64, Fin.val_mk] at hv
    split_ifs at hv <;> omega
  target_machine := by
    intro i h
    change (5 : Fin 64) = embedded64 i at h
    have hv := congrArg Fin.val h
    simp only [embedded64, Fin.val_mk] at hv
    split_ifs at hv <;> omega
  scratch_machine := by
    intro i h
    change (7 : Fin 64) = embedded64 i at h
    have hv := congrArg Fin.val h
    simp only [embedded64, Fin.val_mk] at hv
    split_ifs at hv <;> omega

theorem run64 (S : Fin 64 → List Bool) (raw : List Bool)
    (hs : S 23 = raw) :
    ∃ u ≤ time slots64 S raw,
      ((advance (program slots64))^[u])
        (⟨some (start slots64), control slots64, S⟩ :
          TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
        ⟨none, control slots64,
          Function.update (cleared slots64 S) 5
            (EncodedCommunication.natField raw.length ++ raw)⟩ := by
  exact run slots64 S raw hs

noncomputable def embedded32 (i : Fin W.stackCount) : Fin 32 :=
  ⟨18+i.val, by
    have hi : i.val < 8 := by simpa only [show W.stackCount = 8 by rfl] using i.isLt
    omega⟩

theorem embedded32_injective : Function.Injective embedded32 := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [embedded32] at hv
  omega

noncomputable def slots32 : Slots 0 where
  machine := ⟨embedded32, embedded32_injective⟩
  source := 30
  target := 5
  scratch := 7
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by
    intro i h
    have hi : i.val < 8 := by simpa only [show W.stackCount = 8 by rfl] using i.isLt
    have hv := congrArg Fin.val h
    simp [embedded32] at hv
    omega
  target_machine := by intro i h; have hv := congrArg Fin.val h; simp [embedded32] at hv; omega
  scratch_machine := by intro i h; have hv := congrArg Fin.val h; simp [embedded32] at hv; omega

theorem run32 (S : Fin 32 → List Bool) (raw : List Bool)
    (hs : S 30 = raw) :
    ∃ u ≤ time slots32 S raw,
      ((advance (program slots32))^[u])
        (⟨some (start slots32), control slots32, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) _ _) =
        ⟨none, control slots32,
          Function.update (cleared slots32 S) 5
            (EncodedCommunication.natField raw.length ++ raw)⟩ := by
  exact run slots32 S raw hs

#print axioms run64
#print axioms run32

end CurrentAdditive.V2ItemFrameLayouts
