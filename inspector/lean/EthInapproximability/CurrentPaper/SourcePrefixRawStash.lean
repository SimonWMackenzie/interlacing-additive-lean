import EthInapproximability.CurrentPaper.SourcePrefixRawLoop

namespace EthInapproximability.CurrentPaper.SourcePrefixRawStash

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourcePrefixRawFrame SourcePrefixRawCopy
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

def savedWord (n q : Nat) : List Bool :=
  (PrefixLoopIteration.prefixFields n q n).reverse

def countWord (n : Nat) : List Bool := List.replicate (8 * n) true

theorem saved_source_ne_target {q : Nat} :
    (prefixSaved (q := q)) ≠ entrySaved := by
  simp [prefixSaved, entrySaved, prefixEmbedding, entryEmbedding]

theorem count_source_ne_target {q : Nat} :
    (prefixCount (q := q)) ≠ entryCount := by
  simp [prefixCount, entryCount, prefixEmbedding, entryEmbedding]

theorem saved_source_ne_scratch {q : Nat} :
    (prefixSaved (q := q)) ≠ scratch := by
  simp [prefixSaved, prefixEmbedding, scratch]

theorem count_source_ne_scratch {q : Nat} :
    (prefixCount (q := q)) ≠ scratch := by
  simp [prefixCount, prefixEmbedding, scratch]

theorem saved_target_ne_scratch {q : Nat} :
    (entrySaved (q := q)) ≠ scratch := by
  simp [entrySaved, entryEmbedding, scratch]

theorem count_target_ne_scratch {q : Nat} :
    (entryCount (q := q)) ≠ scratch := by
  simp [entryCount, entryEmbedding, scratch]

theorem saved_ne_count {q : Nat} :
    (entrySaved (q := q)) ≠ entryCount := by
  simp [entrySaved, entryCount, entryEmbedding,
    SourceCSPEntryWrapper.stash]

def savedProgram (q : Nat) :=
  SourcePrefixRawCopy.program (prefixSaved (q := q)) entrySaved
    saved_source_ne_target saved_source_ne_scratch saved_target_ne_scratch

def countProgram (q : Nat) :=
  SourcePrefixRawCopy.program (prefixCount (q := q)) entryCount
    count_source_ne_target count_source_ne_scratch count_target_ne_scratch

def program (q : Nat) :=
  BitMachineRawSequence.program (savedProgram q) (countProgram q)
    BitMachineCopy.Label.scan none none

theorem prefix_saved_word (n q : Nat) :
    PrefixLoopMachine.blank n n (savedWord n q) [] (countWord n) []
      (.inl (.inl 2)) = savedWord n q := by
  rfl

theorem prefix_count_word (n q : Nat) :
    PrefixLoopMachine.blank n n (savedWord n q) [] (countWord n) []
      (.inl (.inl 4)) = countWord n := by
  rfl

theorem copied_stashes (q n : Nat) (before : Stack q → List Bool)
    (hsaved : before (prefixSaved (q := q)) = savedWord n q)
    (hcount : before (prefixCount (q := q)) = countWord n)
    (htargetSaved : before (entrySaved (q := q)) = [])
    (htargetCount : before (entryCount (q := q)) = [])
    (hscratch : before scratch = []) :
    ∃ t ≤ 2 * (savedWord n q).length + 2 +
        (2 * (countWord n).length + 2) + 1,
      ((advance (program q))^[t])
        (⟨some (.inl BitMachineCopy.Label.scan), (none, none), before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none, (none, none),
          Function.update
            (Function.update before entrySaved (savedWord n q))
            entryCount (countWord n)⟩ := by
  let B1 := Function.update before (entrySaved (q := q)) (savedWord n q)
  let B2 := Function.update B1 (entryCount (q := q)) (countWord n)
  obtain ⟨t1, ht1, h1⟩ :=
    SourcePrefixRawCopy.framed_update (prefixSaved (q := q)) entrySaved
      saved_source_ne_target saved_source_ne_scratch
      saved_target_ne_scratch before (savedWord n q)
      hsaved htargetSaved hscratch
  have hs2 : B1 (prefixCount (q := q)) = countWord n := by
    have hne : (prefixCount (q := q)) ≠ entrySaved := by
      simp [prefixCount, entrySaved, prefixEmbedding, entryEmbedding]
    simpa only [B1, Function.update_of_ne hne] using hcount
  have ht2 : B1 (entryCount (q := q)) = [] := by
    simpa only [B1, Function.update_of_ne saved_ne_count.symm]
      using htargetCount
  have hw2 : B1 scratch = [] := by
    simpa only [B1, Function.update_of_ne saved_target_ne_scratch.symm]
      using hscratch
  obtain ⟨t2, ht2', h2⟩ :=
    SourcePrefixRawCopy.framed_update (prefixCount (q := q)) entryCount
      count_source_ne_target count_source_ne_scratch
      count_target_ne_scratch B1 (countWord n) hs2 ht2 hw2
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (savedProgram q) (countProgram q)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none before B1 B2 t1 t2 h1 h2
  refine ⟨t, ?_, ?_⟩
  · omega
  · exact hr

end EthInapproximability.CurrentPaper.SourcePrefixRawStash
