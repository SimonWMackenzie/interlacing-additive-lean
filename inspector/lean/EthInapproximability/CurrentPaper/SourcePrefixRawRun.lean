import EthInapproximability.CurrentPaper.SourcePrefixRawProgram

namespace EthInapproximability.CurrentPaper.SourcePrefixRawRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourcePrefixRawFrame SourcePrefixRawStash
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

noncomputable def rawClock {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q) : Nat :=
  let L := (EncodedETHSource.constraintBits P).length
  let n := P.vertices
  (2 * L + 2) +
    SourceCSPPositiveHeader.positiveBound 2 q L
      P.constraints.bits.length n P.constraints +
    (2 * n + 2) + PrefixLoopPolynomial.polynomialClock n q [] [] [] +
    (2 * (savedWord n q).length + 2 +
      (2 * (countWord n).length + 2) + 1) + 4

theorem entry_after_stash (q n : Nat) (input : List Bool)
    (before : Stack q → List Bool)
    (hentry : ∀ k : SourceCSPEntryWrapper.Ambient q,
      before (entryEmbedding k) = initial q input (entryEmbedding k)) :
    ∀ k : SourceCSPEntryWrapper.Ambient q,
      (Function.update
        (Function.update before entrySaved (savedWord n q))
        entryCount (countWord n)) (entryEmbedding k) =
      (SourceCSPEntryWrapper.initial q input (savedWord n q) []
        (countWord n)).stk k := by
  intro k
  have hinitial := SourcePrefixRawEntry.initial_stashes q input
    (savedWord n q) (countWord n)
  rw [hinitial]
  by_cases hk2 : k = SourceCSPEntryWrapper.stash 2
  · subst k
    simp [entryCount, entryEmbedding]
  by_cases hk0 : k = SourceCSPEntryWrapper.stash 0
  · subst k
    have hne : (entrySaved (q := q)) ≠ entryCount :=
      SourcePrefixRawStash.saved_ne_count
    simp [entrySaved, entryCount, entryEmbedding,
      SourceCSPEntryWrapper.stash]
  have hne2 : entryEmbedding k ≠ (entryCount (q := q)) := by
    intro h
    exact hk2 (entryEmbedding.injective h)
  have hne0 : entryEmbedding k ≠ (entrySaved (q := q)) := by
    intro h
    exact hk0 (entryEmbedding.injective h)
  simp only [Function.update_of_ne hne2,
    Function.update_of_ne hne0,
    Function.update_of_ne hk2, Function.update_of_ne hk0]
  exact (hentry k).trans (initial_entry q input k)

theorem raw_atLeast_stash {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t S, t ≤ rawClock P ∧
      ((advance (SourcePrefixRawProgram.program q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)),
          initial q (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none,
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)), S⟩ ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (entryEmbedding k) =
          (SourceCSPEntryWrapper.initial q
            (EncodedETHSource.constraintBits P)
            (savedWord P.vertices q) [] (countWord P.vertices)).stk k) := by
  let input := EncodedETHSource.constraintBits P
  let n := P.vertices
  obtain ⟨t1, S1, ht1, hr1, he1, hh1, hp1, hw1⟩ :=
    SourcePrefixRawInput.copied_header q input
  obtain ⟨t2, V, S2, ht2, hr2, hv2, he2, hp2, hw2⟩ :=
    SourcePrefixRawHeader.framed_positive P hn hsize S1 hh1
  have hnword : S2 (headerVertex (q := q)) = List.replicate n true := by
    exact hv2.trans (SourcePrefixRawVertex.unary_positive n hn)
  have hp2' : ∀ k : PrefixLoopMachine.Stack,
      S2 (prefixEmbedding k) = [] := by
    intro k
    exact (hp2 k).trans (hp1 k)
  have hw2' : S2 scratch = [] := hw2.trans hw1
  obtain ⟨t3, S3, ht3, hr3, he3, hh3, hp3, hw3⟩ :=
    SourcePrefixRawVertex.copied_unary q n S2 hnword hp2' hw2'
  obtain ⟨t4, S4, ht4, hr4, he4, hh4, hp4, hw4⟩ :=
    SourcePrefixRawLoop.framed_loop q n S3 hp3
  have hs4 : S4 (prefixSaved (q := q)) = savedWord n q := by
    exact (hp4 (.inl (.inl 2))).trans (prefix_saved_word n q)
  have hc4 : S4 (prefixCount (q := q)) = countWord n := by
    exact (hp4 (.inl (.inl 4))).trans (prefix_count_word n q)
  have he4' : ∀ k : SourceCSPEntryWrapper.Ambient q,
      S4 (entryEmbedding k) = initial q input (entryEmbedding k) := by
    intro k
    exact (he4 k).trans ((he3 k).trans ((he2 k).trans (he1 k)))
  have hts : S4 (entrySaved (q := q)) = [] := by
    exact (he4' (SourceCSPEntryWrapper.stash 0)).trans
      (initial_stash_blank q input 0)
  have htc : S4 (entryCount (q := q)) = [] := by
    exact (he4' (SourceCSPEntryWrapper.stash 2)).trans
      (initial_stash_blank q input 2)
  have hw4' : S4 scratch = [] := hw4.trans hw3
  obtain ⟨t5, ht5, hr5⟩ := SourcePrefixRawStash.copied_stashes
    q n S4 hs4 hc4 hts htc hw4'
  let S5 := Function.update
    (Function.update S4 entrySaved (savedWord n q))
    entryCount (countWord n)
  have hentry5 := entry_after_stash q n input S4 he4'
  obtain ⟨t12, ht12, hr12⟩ := BitMachineRawSequence.runs
    (SourcePrefixRawInput.program q) (SourcePrefixRawHeader.program q)
    BitMachineCopy.Label.scan (SourcePrefixRawHeader.startLabel q)
    none none (SourcePrefixRawHeader.initialControl q) V
    (initial q input) S1 S2 t1 t2 hr1 hr2
  obtain ⟨t123, ht123, hr123⟩ := BitMachineRawSequence.runs
    (SourcePrefixRawProgram.phase01 q) (SourcePrefixRawVertex.program q)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan
    (none, SourcePrefixRawHeader.initialControl q)
    (none, V)
    none none (initial q input) S2 S3 t12 t3 hr12 hr3
  obtain ⟨t1234, ht1234, hr1234⟩ := BitMachineRawSequence.runs
    (SourcePrefixRawProgram.phase012 q) (SourcePrefixRawLoop.program q)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (.inr .copyScan)
    ((none, SourcePrefixRawHeader.initialControl q), none)
    ((none, SourcePrefixRawHeader.initialControl q), none)
    (PrefixLoopCallback.initial, none)
    (PrefixLoopCallback.initial, none)
    (initial q input) S3 S4 t123 t4 hr123 hr4
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourcePrefixRawProgram.phase0123 q) (SourcePrefixRawStash.program q)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (((none, SourcePrefixRawHeader.initialControl q), none),
      (PrefixLoopCallback.initial, none))
    (((none, SourcePrefixRawHeader.initialControl q), none),
      (PrefixLoopCallback.initial, none))
    (none, none) (none, none)
    (initial q input) S4 S5 t1234 t5 hr1234 hr5
  refine ⟨t, S5, ?_, ?_, ?_⟩
  · dsimp only [rawClock]
    change t ≤ (2 * input.length + 2) +
      SourceCSPPositiveHeader.positiveBound 2 q input.length
        P.constraints.bits.length n P.constraints +
      (2 * n + 2) + PrefixLoopPolynomial.polynomialClock n q [] [] [] +
      (2 * (savedWord n q).length + 2 +
        (2 * (countWord n).length + 2) + 1) + 4
    have ht2' : t2 ≤ SourceCSPPositiveHeader.positiveBound 2 q
        input.length P.constraints.bits.length n P.constraints := ht2
    omega
  · exact hr
  · exact hentry5

#print axioms raw_atLeast_stash

end EthInapproximability.CurrentPaper.SourcePrefixRawRun
