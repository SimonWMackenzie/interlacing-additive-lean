import EthInapproximability.CurrentPaper.GenericPrefixTransfer

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixComposite

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open PrefixCopy PrefixTransferFrame
open scoped Classical

noncomputable def atProgram (a q : Nat) :=
  fun l => stackStmt PrefixCopy.atEmbedding (AtLeastLoopCallback.program a q l)

noncomputable def pairProgram (a q : Nat) :=
  fun l => stackStmt PrefixCopy.pairEmbedding (PairVertexLoopCallback.program a q l)

noncomputable def phase1 (a q : Nat) :=
  BitMachineRawSequence.program (atProgram a q) PrefixTransfer.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((AtLeastLoopCallback.callback a q).initial,none)
    ((none,none),none)

noncomputable def program (a q : Nat) :=
  BitMachineRawSequence.program (phase1 a q) (pairProgram a q)
    (.inr .copyScan)
    (((AtLeastLoopCallback.callback a q).initial,none),((none,none),none))
    ((PairVertexLoopCallback.routine a q).initial,none)

noncomputable def atSaved (n a q : Nat) (saved : List Bool) : List Bool :=
  (clauseFields (SourceGenericPrefix.atLeastChains n a q)).reverse ++ saved

noncomputable def atCount (n a : Nat) (count : List Bool) : List Bool :=
  List.replicate ((3*a+2)*n) true ++ count

noncomputable def atBank (n a q : Nat)
    (saved output count : List Bool) : PrefixLoopMachine.Stack → List Bool :=
  PrefixLoopMachine.blank n n (atSaved n a q saved)
    output (atCount n a count) []

noncomputable def transferred (n a q : Nat)
    (saved output count : List Bool) : PrefixCopy.Stack → List Bool :=
  paired (atBank n a q saved output count)
    n (atSaved n a q saved) (atCount n a count)

noncomputable def finalBank (n a q : Nat)
    (saved output count : List Bool) : PrefixCopy.Stack → List Bool :=
  bank PrefixCopy.pairEmbedding
    (transferred n a q saved output count)
    (PairVertexLoopMachine.blank n n
      ((clauseFields (SourceGenericPrefix.pairChains n a q)).reverse ++
        atSaved n a q saved)
      output (List.replicate ((8*(a*a))*n) true ++ atCount n a count) [])

noncomputable def cost (n a q : Nat)
    (saved output count : List Bool) : Nat :=
  (2*n+2+AtLeastLoop.tailCost n a q saved output count 0 n) +
  (2*(n+(atSaved n a q saved).length+(atCount n a count).length)+8) + 1 +
  (2*n+2+PairVertexLoop.tailCost n a q
    (atSaved n a q saved) output (atCount n a count) 0 n) + 1

theorem run (n a q : Nat) (saved output count : List Bool)
    (houtput : output = []) :
    ∃ T ≤ cost n a q saved output count,
      ((advance (program a q))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.inr .copyScan))),
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          framedAt (PrefixLoopMachine.blank n 0 saved output count [])⟩ :
          TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) =
        ⟨none,
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          finalBank n a q saved output count⟩ := by
  let A0 := PrefixLoopMachine.blank n 0 saved output count []
  let A1 := atBank n a q saved output count
  let S0 := framedAt A0
  let S1 := framedAt A1
  let S2 := transferred n a q saved output count
  let S3 := finalBank n a q saved output count
  let saved1 := atSaved n a q saved
  let count1 := atCount n a count
  obtain ⟨t0,ht0,hr0⟩ := PrefixLoopEndpoint.atLeast_run n a q
    saved output count
  have hsim0 := BitMachineStackRun.run PrefixCopy.atEmbedding S0
    (AtLeastLoopCallback.program a q)
    (⟨some (.inr .copyScan),
      ((AtLeastLoopCallback.callback a q).initial,none),A0⟩ :
      PrefixLoopMachine.Config _ _) t0
  rw [hr0] at hsim0
  have hbank0 : bank PrefixCopy.atEmbedding S0 A0 = S0 := by
    apply bank_eq_self
    intro x
    exact (framed_at A0 x).symm
  have hbank1 : bank PrefixCopy.atEmbedding S0 A1 = S1 := by
    funext x
    by_cases hx : ∃ k, PrefixCopy.atEmbedding k = x
    · obtain ⟨k,rfl⟩ := hx
      rw [bank_at]
      exact (framed_at A1 k).symm
    · rw [bank_outside PrefixCopy.atEmbedding S0 A1 x hx]
      change framedAt A0 x = framedAt A1 x
      rw [framedAt,bank_outside PrefixCopy.atEmbedding emptyForeign A0 x hx,
        framedAt,bank_outside PrefixCopy.atEmbedding emptyForeign A1 x hx]
  have h0 : ((advance (atProgram a q))^[t0])
      (⟨some (.inr .copyScan),
        ((AtLeastLoopCallback.callback a q).initial,none),S0⟩ :
        TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) =
      ⟨none,((AtLeastLoopCallback.callback a q).initial,none),S1⟩ := by
    have hA : PrefixLoopMachine.blank n n
        ((clauseFields (SourceGenericPrefix.atLeastChains n a q)).reverse ++ saved)
        output (List.replicate ((3*a+2)*n) true ++ count) [] = A1 := rfl
    rw [hA] at hsim0
    simp only [stackCfg,hbank0,hbank1] at hsim0
    simpa only [atProgram] using hsim0
  have hn : A1 PrefixLoopMachine.source = List.replicate n true := by
    exact PrefixLoopMachine.source_word n n saved1 output count1 []
  have hs : A1 (.inl (.inl 2)) = saved1 := rfl
  have hc : A1 (.inl (.inl 4)) = count1 := rfl
  obtain ⟨t1,ht1,h1⟩ := PrefixTransfer.run A1 n saved1 count1 hn hs hc
  obtain ⟨t2,ht2,hr2⟩ := PrefixLoopEndpoint.pair_run n a q
    saved1 output count1
  let P0 := PairVertexLoopMachine.blank n 0 saved1 output count1 []
  have hsim2 := BitMachineStackRun.run PrefixCopy.pairEmbedding S2
    (PairVertexLoopCallback.program a q)
    (⟨some (.inr .copyScan),
      ((PairVertexLoopCallback.routine a q).initial,none),P0⟩ :
      PairVertexLoopMachine.Config _ _) t2
  rw [hr2] at hsim2
  have hbank2 : bank PrefixCopy.pairEmbedding S2 P0 = S2 := by
    apply bank_eq_self
    intro x
    simpa only [houtput,P0] using
      (paired_projection A1 n saved1 count1 x).symm
  have h2 : ((advance (pairProgram a q))^[t2])
      (⟨some (.inr .copyScan),
        ((PairVertexLoopCallback.routine a q).initial,none),S2⟩ :
        TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) =
      ⟨none,((PairVertexLoopCallback.routine a q).initial,none),S3⟩ := by
    simpa only [pairProgram,hbank2,stackCfg,S3,finalBank] using hsim2
  obtain ⟨u,hu,hU⟩ := BitMachineRawSequence.runs
    (atProgram a q) PrefixTransfer.program
    (.inr .copyScan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((AtLeastLoopCallback.callback a q).initial,none)
    ((AtLeastLoopCallback.callback a q).initial,none)
    ((none,none),none) ((none,none),none)
    S0 S1 S2 t0 t1 h0 h1
  obtain ⟨T,hT,hRun⟩ := BitMachineRawSequence.runs
    (phase1 a q) (pairProgram a q)
    (BitMachineRawSequence.leftLabel (.inr .copyScan))
    (.inr .copyScan)
    (((AtLeastLoopCallback.callback a q).initial,none),((none,none),none))
    (((AtLeastLoopCallback.callback a q).initial,none),((none,none),none))
    ((PairVertexLoopCallback.routine a q).initial,none)
    ((PairVertexLoopCallback.routine a q).initial,none)
    S0 S2 S3 u t2 hU h2
  have hcost : T ≤ cost n a q saved output count := by
    change T ≤
      (2*n+2+AtLeastLoop.tailCost n a q saved output count 0 n) +
      (2*(n+saved1.length+count1.length)+8)+1+
      (2*n+2+PairVertexLoop.tailCost n a q saved1 output count1 0 n)+1
    omega
  exact ⟨T,hcost,
    by simpa only [program,S0,S3] using hRun⟩

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixComposite
