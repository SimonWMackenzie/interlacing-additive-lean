import CurrentAdditive.IndexedCodeDCoordinatePackedMachine
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-! Charged copies from retained word and coordinate banks into the fixed
V2 getter's serializer slots. The source banks remain available to the
successor scheduler. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Turing

abbrev packetStack := Fin 32

def packetWordCopied (S : packetStack → List Bool) (word : List Bool) :=
  SourceClausePreservingBroadcast.result (3 : packetStack) 22 [18] word S

def packetIndexCopied (S : packetStack → List Bool) (index : List Bool) :=
  SourceClausePreservingBroadcast.result (4 : packetStack) 22 [17] index S

theorem coordinate_packet_copy_runs (S : packetStack → List Bool)
    (word index : List Bool)
    (hword : S 3 = word) (hindex : S 4 = index)
    (h18 : S 18 = []) (h17 : S 17 = []) (h22 : S 22 = []) :
    let S1 := packetWordCopied S word
    let S2 := packetIndexCopied S1 index
    ((advance (SourceClausePreservingBroadcast.program
      (3 : packetStack) 22 [18]))^[2*word.length+3])
      (⟨some .scan, ((), none), S⟩ :
        TM2.Cfg (fun _ : packetStack => Bool)
          SourceClausePreservingBroadcast.Label _) =
      ⟨none, ((), none), S1⟩ ∧
    ((advance (SourceClausePreservingBroadcast.program
      (4 : packetStack) 22 [17]))^[2*index.length+3])
      (⟨some .scan, ((), none), S1⟩ :
        TM2.Cfg (fun _ : packetStack => Bool)
          SourceClausePreservingBroadcast.Label _) =
      ⟨none, ((), none), S2⟩ ∧
    S2 3 = word ∧ S2 4 = index ∧ S2 18 = word ∧ S2 17 = index := by
  dsimp only
  let S1 := packetWordCopied S word
  let S2 := packetIndexCopied S1 index
  have hrun1 := SourceClausePreservingBroadcast.run_halt
    (3 : packetStack) 22 [18]
    (by decide) (by decide) (by decide) (by decide)
    word S hword h22
  have hS1index : S1 4 = index := by
    change SourceClausePreservingBroadcast.result
      (3 : packetStack) 22 [18] word S 4 = index
    rw [SourceClausePreservingBroadcast.other_preserved
      (3 : packetStack) 22 [18] word S 4
      (by decide) (by decide) (by decide)]
    exact hindex
  have hS1scratch : S1 22 = [] := by
    simp [S1, packetWordCopied, SourceClausePreservingBroadcast.result]
  have hrun2 := SourceClausePreservingBroadcast.run_halt
    (4 : packetStack) 22 [17]
    (by decide) (by decide) (by decide) (by decide)
    index S1 hS1index hS1scratch
  have hS1word : S1 3 = word := by
    change SourceClausePreservingBroadcast.result
      (3 : packetStack) 22 [18] word S 3 = word
    exact SourceClausePreservingBroadcast.source_restored
      (3 : packetStack) 22 [18] (by decide) word S
  have hS1copy : S1 18 = word := by
    change SourceClausePreservingBroadcast.result
      (3 : packetStack) 22 [18] word S 18 = word
    rw [SourceClausePreservingBroadcast.target_written
      (3 : packetStack) 22 [18]
      (by decide) (by decide) (by decide) word S 18 (by decide), h18,
      List.append_nil]
  have hS2word : S2 3 = word := by
    change SourceClausePreservingBroadcast.result
      (4 : packetStack) 22 [17] index S1 3 = word
    rw [SourceClausePreservingBroadcast.other_preserved
      (4 : packetStack) 22 [17] index S1 3
      (by decide) (by decide) (by decide)]
    exact hS1word
  have hS2index : S2 4 = index := by
    change SourceClausePreservingBroadcast.result
      (4 : packetStack) 22 [17] index S1 4 = index
    exact SourceClausePreservingBroadcast.source_restored
      (4 : packetStack) 22 [17] (by decide) index S1
  have hS2copyWord : S2 18 = word := by
    change SourceClausePreservingBroadcast.result
      (4 : packetStack) 22 [17] index S1 18 = word
    rw [SourceClausePreservingBroadcast.other_preserved
      (4 : packetStack) 22 [17] index S1 18
      (by decide) (by decide) (by decide)]
    exact hS1copy
  have hS2copyIndex : S2 17 = index := by
    change SourceClausePreservingBroadcast.result
      (4 : packetStack) 22 [17] index S1 17 = index
    have hS117 : S1 17 = [] := by
      change SourceClausePreservingBroadcast.result
        (3 : packetStack) 22 [18] word S 17 = []
      rw [SourceClausePreservingBroadcast.other_preserved
        (3 : packetStack) 22 [18] word S 17
        (by decide) (by decide) (by decide)]
      exact h17
    rw [SourceClausePreservingBroadcast.target_written
      (4 : packetStack) 22 [17]
      (by decide) (by decide) (by decide) index S1 17 (by decide),
      hS117, List.append_nil]
  exact ⟨hrun1, hrun2, hS2word, hS2index, hS2copyWord, hS2copyIndex⟩

#print axioms coordinate_packet_copy_runs

end CurrentAdditive.IndexedExecutableStepRecovery
