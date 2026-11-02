import EthInapproximability.CurrentPaper.SourcePrefixRawCopy

namespace EthInapproximability.CurrentPaper.SourcePrefixRawInput

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourcePrefixRawFrame SourcePrefixRawCopy
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

def rawSource {q : Nat} : Stack q := entryEmbedding entryInput
def headerTarget {q : Nat} : Stack q := headerEmbedding headerInput

theorem source_ne_target {q : Nat} :
    (rawSource : Stack q) ≠ headerTarget := by
  simp [rawSource, headerTarget, entryEmbedding, headerEmbedding]

theorem source_ne_scratch {q : Nat} :
    (rawSource : Stack q) ≠ scratch := by
  simp [rawSource, entryEmbedding, scratch]

theorem target_ne_scratch {q : Nat} :
    (headerTarget : Stack q) ≠ scratch := by
  simp [headerTarget, headerEmbedding, scratch]

def program (q : Nat) :=
  SourcePrefixRawCopy.program (rawSource (q := q)) headerTarget
    source_ne_target source_ne_scratch target_ne_scratch

theorem copied_header (q : Nat) (input : List Bool) :
    ∃ t S, t ≤ 2 * input.length + 2 ∧
      ((advance (program q))^[t])
        (⟨some BitMachineCopy.Label.scan, none, initial q input⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (entryEmbedding k) = initial q input (entryEmbedding k)) ∧
      (∀ k : SourceCSPPositiveHeader.Stack,
        S (headerEmbedding k) = SourceCSPPositiveHeader.initial input k) ∧
      (∀ k : PrefixLoopMachine.Stack, S (prefixEmbedding k) = []) ∧
      S scratch = [] := by
  obtain ⟨t, S, ht, hr, hsrc, hdst, hscratch, hframe⟩ :=
    SourcePrefixRawCopy.framed rawSource headerTarget
      source_ne_target source_ne_scratch target_ne_scratch
      (initial q input) input
      (by exact entry_raw_input q input)
      (by exact initial_header q input headerInput)
      (by exact initial_scratch q input)
  refine ⟨t, S, ht, hr, ?_, ?_, ?_, hscratch⟩
  · intro k
    by_cases hk : k = entryInput
    · subst k
      exact hsrc.trans (entry_raw_input q input).symm
    · apply hframe
      · intro h
        exact hk (by simpa [rawSource, entryEmbedding] using h)
      · simp [headerTarget, entryEmbedding, headerEmbedding]
      · simp [entryEmbedding, scratch]
  · intro k
    by_cases hk : k = headerInput
    · subst k
      exact hdst.trans (positive_header_initial_source input).symm
    · rw [positive_header_initial_other input k hk]
      rw [hframe]
      · exact initial_header q input k
      · simp [rawSource, entryEmbedding, headerEmbedding]
      · intro h
        exact hk (by simpa [headerTarget, headerEmbedding] using h)
      · simp [headerEmbedding, scratch]
  · intro k
    rw [hframe]
    · exact initial_prefix q input k
    · simp [rawSource, entryEmbedding, prefixEmbedding]
    · simp [headerTarget, headerEmbedding, prefixEmbedding]
    · simp [prefixEmbedding, scratch]

end EthInapproximability.CurrentPaper.SourcePrefixRawInput
