import CurrentAdditive.MinimumRatioBestTail
import CurrentAdditive.RawRatPairFull

namespace CurrentAdditive.MinimumRatioPairAndLess

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout
open CurrentAdditive.MinimumRatioContext

theorem pair_run (S : Bank) (x y : List Bool)
    (hx : S (low 16) = x) (hy : S (low 20) = y)
    (h22 : S (low 22) = []) (h23 : S (low 23) = [])
    (h24 : S (low 24) = []) (h25 : S (low 25) = [])
    (h26 : S (low 26) = []) :
    ∃ u ≤ RawRatPairFull.linearBound extraCount x y,
      ((advance (RawRatPairFull.program extraCount))^[u])
        (⟨some RawRatPairFull.start, RawRatPairFull.control, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, RawRatPairFull.control,
          Function.update S (low 26) (RawRatPairAssembler.pairWord x y)⟩ := by
  have e16 : low 16 = (16 : Stack) := by
    apply Fin.ext
    have h : 16 < 32 + extraCount := by omega
    simpa [low, Nat.mod_eq_of_lt h]
  have e20 : low 20 = (20 : Stack) := by
    apply Fin.ext
    have h : 20 < 32 + extraCount := by omega
    simpa [low, Nat.mod_eq_of_lt h]
  have e22 : low 22 = (22 : Stack) := by
    apply Fin.ext
    have h : 22 < 32 + extraCount := by omega
    simpa [low, Nat.mod_eq_of_lt h]
  have e23 : low 23 = (23 : Stack) := by
    apply Fin.ext
    have h : 23 < 32 + extraCount := by omega
    simpa [low, Nat.mod_eq_of_lt h]
  have e24 : low 24 = (24 : Stack) := by
    apply Fin.ext
    have h : 24 < 32 + extraCount := by omega
    simpa [low, Nat.mod_eq_of_lt h]
  have e25 : low 25 = (25 : Stack) := by
    apply Fin.ext
    have h : 25 < 32 + extraCount := by omega
    simpa [low, Nat.mod_eq_of_lt h]
  have e26 : low 26 = (26 : Stack) := by
    apply Fin.ext
    have h : 26 < 32 + extraCount := by omega
    simpa [low, Nat.mod_eq_of_lt h]
  simpa only [Stack, e26] using
    (RawRatPairFull.run_linear S x y
      (by simpa only [e16] using hx)
      (by simpa only [e20] using hy)
      (by simpa only [e22] using h22)
      (by simpa only [e23] using h23)
      (by simpa only [e24] using h24)
      (by simpa only [e25] using h25)
      (by simpa only [e26] using h26))

theorem less_run (S : Bank) (word : List Bool)
    (hsource : S (low 26) = word)
    (htarget : S (low 18) = [])
    (hscratch : S (low 31) = [])
    (hhigh : ∀ k : Stack, 32 ≤ k.val → S k = []) :
    ∃ u ≤ MachineInvokeFull.uniformBound RationalLess.machine word
        (RationalLess.coefficient*(word.length+1)^RationalLess.exponent),
      ((advance (MachineInvokeFull.program lessSlots))^[u])
        (⟨some (MachineInvokeFull.start lessSlots),
          MachineInvokeFull.control lessSlots, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, MachineInvokeFull.control lessSlots,
          Function.update S (low 18) (RationalLess.result word)⟩ := by
  have hblank : ∀ k, S (lessSlots.machine k) = [] := by
    intro k
    apply hhigh
    simp [lessSlots, slots, high]
  simpa [less_slots_source, less_slots_target] using
    (MachineInvokeFull.invoke_run_uniform lessSlots S word
      (RationalLess.result word)
      (RationalLess.coefficient*(word.length+1)^RationalLess.exponent)
      (by simpa [less_slots_source] using hsource)
      (by simpa [less_slots_target] using htarget)
      (by simpa [lessSlots, slots] using hscratch)
      hblank (RationalLess.outputs word))

end CurrentAdditive.MinimumRatioPairAndLess
