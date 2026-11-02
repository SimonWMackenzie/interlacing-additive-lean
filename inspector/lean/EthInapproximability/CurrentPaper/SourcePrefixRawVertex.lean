import EthInapproximability.CurrentPaper.SourcePrefixRawHeader

namespace EthInapproximability.CurrentPaper.SourcePrefixRawVertex

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourcePrefixRawFrame SourcePrefixRawCopy
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

theorem unary_positive (n : Nat) (hn : 0 < n) :
    true :: List.replicate (n - 1) true = List.replicate n true := by
  cases n with
  | zero => omega
  | succ n => simp [List.replicate_succ]

theorem vertex_ne_prefix {q : Nat} :
    (headerVertex (q := q)) ≠ prefixVertex := by
  simp [headerVertex, prefixVertex, headerEmbedding, prefixEmbedding]

theorem vertex_ne_scratch {q : Nat} :
    (headerVertex (q := q)) ≠ scratch := by
  simp [headerVertex, headerEmbedding, scratch]

theorem prefix_ne_scratch {q : Nat} :
    (prefixVertex (q := q)) ≠ scratch := by
  simp [prefixVertex, prefixEmbedding, scratch]

def program (q : Nat) :=
  SourcePrefixRawCopy.program (headerVertex (q := q)) prefixVertex
    vertex_ne_prefix vertex_ne_scratch prefix_ne_scratch

theorem copied_unary (q n : Nat) (before : Stack q → List Bool)
    (hsource : before (headerVertex (q := q)) = List.replicate n true)
    (hprefix : ∀ k : PrefixLoopMachine.Stack,
      before (prefixEmbedding k) = [])
    (hscratch : before scratch = []) :
    ∃ t S, t ≤ 2 * n + 2 ∧
      ((advance (program q))^[t])
        (⟨some BitMachineCopy.Label.scan, none, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (entryEmbedding k) = before (entryEmbedding k)) ∧
      (∀ k : SourceCSPPositiveHeader.Stack,
        S (headerEmbedding k) = before (headerEmbedding k)) ∧
      (∀ k : PrefixLoopMachine.Stack,
        S (prefixEmbedding k) =
          PrefixLoopMachine.blank n 0 [] [] [] [] k) ∧
      S scratch = [] := by
  obtain ⟨t, S, ht, hr, hsrc, hdst, hscratch', hframe⟩ :=
    SourcePrefixRawCopy.framed (headerVertex (q := q)) prefixVertex
      vertex_ne_prefix vertex_ne_scratch prefix_ne_scratch
      before (List.replicate n true) hsource
      (hprefix PrefixLoopMachine.source) hscratch
  have ht' : t ≤ 2 * n + 2 := by simpa using ht
  refine ⟨t, S, ht', hr, ?_, ?_, ?_, hscratch'⟩
  · intro k
    exact hframe _ (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h)
  · intro k
    by_cases hk : k = (.inr 6 : SourceCSPPositiveHeader.Stack)
    · subst k
      exact hsrc.trans hsource.symm
    · exact hframe _ (by
        intro h
        exact hk (headerEmbedding.injective h))
        (by intro h; cases h) (by intro h; cases h)
  · intro k
    by_cases hk : k = PrefixLoopMachine.source
    · subst k
      exact hdst.trans (prefix_blank_source n).symm
    · rw [prefix_blank_other n k hk]
      exact (hframe _ (by intro h; cases h) (by
        intro h
        exact hk (prefixEmbedding.injective h))
        (by intro h; cases h)).trans (hprefix k)

end EthInapproximability.CurrentPaper.SourcePrefixRawVertex
