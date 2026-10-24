import CurrentAdditive.OuterPacketCallbackCleanup
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-! After the outer request is framed, the record index is discarded and
the next coordinate is moved from retained cell 6 to callback cell 4. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

noncomputable def coordinateRelocated (T : StackN contextTwoSize → List Bool)
    (p : List Bool) : StackN contextTwoSize → List Bool :=
  SourceClausePreservingBroadcast.result
    (6 : StackN contextTwoSize) 22 [4] p T

noncomputable def coordinateReady (T : StackN contextTwoSize → List Bool)
    (p : List Bool) : StackN contextTwoSize → List Bool :=
  BitMachineClearBank.cleared
    (fun _ : Fin 1 => (6 : StackN contextTwoSize))
    (coordinateRelocated T p)

theorem coordinateRelocated_run
    (T : StackN contextTwoSize → List Bool) (p : List Bool)
    (hp : T 6 = p) (h22 : T 22 = []) :
    ((advance (SourceClausePreservingBroadcast.program
      (6 : StackN contextTwoSize) 22 [4]))^[2*p.length+3])
      (⟨some .scan, ((), none), T⟩ :
        TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
      ⟨none, ((), none), coordinateRelocated T p⟩ := by
  exact SourceClausePreservingBroadcast.run_halt 6 22 [4]
    (by decide) (by decide) (by decide) (by decide)
    p T hp h22

theorem coordinateReady_run
    (T : StackN contextTwoSize → List Bool) (p : List Bool)
    (hp : T 6 = p) (h22 : T 22 = []) :
    ∃ t ≤ p.length + 3,
      ((advance (RegionClear.prog 1
        (fun _ : Fin 1 => (6 : StackN contextTwoSize))))^[t])
        (⟨some 0, ((), none), coordinateRelocated T p⟩ :
          TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
      ⟨none, ((), none), coordinateReady T p⟩ := by
  have hsource : coordinateRelocated T p 6 = p := by
    exact SourceClausePreservingBroadcast.source_restored 6 22 [4]
      (by decide) p T
  have hinj : Function.Injective
      (fun _ : Fin 1 => (6 : StackN contextTwoSize)) := by
    intro i j _
    exact Subsingleton.elim i j
  obtain ⟨t, ht, hr⟩ := RegionClear.clear_run 1
    (fun _ : Fin 1 => (6 : StackN contextTwoSize))
    hinj (coordinateRelocated T p) p.length
    (by intro i; fin_cases i; simp [hsource])
  exact ⟨t, by omega, by simpa [coordinateReady] using hr⟩

theorem coordinateReady_cells
    (T : StackN contextTwoSize → List Bool) (p packet : List Bool)
    (h0 : T 0 = packet) (h6 : T 6 = p)
    (hblank : ∀ k : StackN contextTwoSize,
      1 ≤ k.val → k.val < 32 → k.val ≠ 6 → T k = []) :
    coordinateReady T p 0 = packet ∧
    coordinateReady T p 4 = p ∧
    (∀ k : StackN contextTwoSize,
      1 ≤ k.val → k.val < 32 → k.val ≠ 4 →
        coordinateReady T p k = []) := by
  have hrel0 : coordinateRelocated T p 0 = packet := by
    rw [coordinateRelocated,
      SourceClausePreservingBroadcast.other_preserved
        (6 : StackN contextTwoSize) 22 [4] p T 0
        (by decide) (by decide) (by decide)]
    exact h0
  have hT4 : T 4 = [] := hblank 4 (by decide) (by decide) (by decide)
  have hrel4 : coordinateRelocated T p 4 = p := by
    have h := SourceClausePreservingBroadcast.target_written
      (6 : StackN contextTwoSize) 22 [4]
      (by decide) (by decide) (by decide) p T 4 (by simp)
    simpa [coordinateRelocated, hT4] using h
  have hclear (k : StackN contextTwoSize) (hk : k ≠ 6) :
      coordinateReady T p k = coordinateRelocated T p k := by
    simp only [coordinateReady, BitMachineClearBank.cleared]
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      fin_cases i
      exact (hk hi.symm).elim
    · rfl
  constructor
  · rw [hclear 0 (by decide)]
    exact hrel0
  constructor
  · rw [hclear 4 (by decide)]
    exact hrel4
  · intro k hlo hhi h4
    by_cases hk6 : k = 6
    · subst k
      simp [coordinateReady, BitMachineClearBank.cleared]
    · rw [hclear k hk6]
      by_cases hk22 : k = 22
      · subst k
        exact SourceClausePreservingBroadcast.temp_empty 6 22 [4] p T
      · rw [coordinateRelocated,
          SourceClausePreservingBroadcast.other_preserved
            (6 : StackN contextTwoSize) 22 [4] p T k
            hk6 hk22 (by
              intro hm
              simp only [List.mem_singleton] at hm
              apply h4
              simpa using congrArg Fin.val hm)]
        have hk6val : k.val ≠ 6 := by
          intro hm
          apply hk6
          apply Fin.ext
          simpa using hm
        exact hblank k hlo hhi hk6val

theorem coordinateReady_high_preserved
    (T : StackN contextTwoSize → List Bool) (p : List Bool)
    (k : StackN contextTwoSize) (hk : 32 ≤ k.val) :
    coordinateReady T p k = T k := by
  have hval6 : (6 : StackN contextTwoSize).val = 6 := by
    simp [StackN, Nat.mod_eq_of_lt (by omega : 6 < 32 + contextTwoSize)]
  have hval22 : (22 : StackN contextTwoSize).val = 22 := by
    simp [StackN, Nat.mod_eq_of_lt (by omega : 22 < 32 + contextTwoSize)]
  have hval4 : (4 : StackN contextTwoSize).val = 4 := by
    simp [StackN, Nat.mod_eq_of_lt (by omega : 4 < 32 + contextTwoSize)]
  have h6 : k ≠ 6 := by
    intro h
    have hv := congrArg Fin.val h
    rw [hval6] at hv
    omega
  have h22 : k ≠ 22 := by
    intro h
    have hv := congrArg Fin.val h
    rw [hval22] at hv
    omega
  have h4 : k ∉ ([4] : List (StackN contextTwoSize)) := by
    simp only [List.mem_singleton]
    intro h
    have hv := congrArg Fin.val h
    rw [hval4] at hv
    omega
  have hclear : coordinateReady T p k = coordinateRelocated T p k := by
    simp only [coordinateReady, BitMachineClearBank.cleared]
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      fin_cases i
      exact (h6 hi.symm).elim
    · rfl
  rw [hclear, coordinateRelocated,
    SourceClausePreservingBroadcast.other_preserved
      (6 : StackN contextTwoSize) 22 [4] p T k h6 h22 h4]

#print axioms coordinateRelocated_run
#print axioms coordinateReady_run
#print axioms coordinateReady_cells
#print axioms coordinateReady_high_preserved

end CurrentAdditive.IndexedExecutableStepRecovery
