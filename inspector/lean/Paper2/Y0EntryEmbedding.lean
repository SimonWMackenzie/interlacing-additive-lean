import Paper2.Y0FixedControl

/-! Embed the frozen `EntryCombined.program` into the loader's actual
Boolean stacks. The evaluator starts only after the charged administrative
handoff; the exact input-bank equality is supplied by the checked loader. -/

namespace Paper2.YaoEntryControllerJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryParameterJoin

def entryEmbed (t lambda : ℕ) : Fin 13 ↪ InputStack t lambda where
  toFun i := .inl (.inr (.inl i))
  inj' := by intro i j h; cases h; rfl

noncomputable def embeddedEntryProgram (t lambda : ℕ)
    (l : Paper2.YaoEntryComposition.Label) :
    TM2.Stmt (fun _ : InputStack t lambda => Bool)
      Paper2.YaoEntryComposition.Label
      Paper2.YaoEntryComposition.Control :=
  BitMachineStackEmbedding.stmt (entryEmbed t lambda) id id id none
    (Paper2.YaoEntryComposition.program l)

noncomputable def entryEndBank (t lambda : ℕ)
    (S : InputStack t lambda → List Bool)
    (F : Fin 13 → List Bool) : InputStack t lambda → List Bool :=
  BitMachineStackEmbedding.bank (entryEmbed t lambda) S F

theorem entry_end_at (t lambda : ℕ)
    (S : InputStack t lambda → List Bool)
    (F : Fin 13 → List Bool) (i : Fin 13) :
    entryEndBank t lambda S F (entryEmbed t lambda i) = F i :=
  BitMachineStackEmbedding.bank_at (entryEmbed t lambda) S F i

theorem entry_end_raw_tape (t lambda : ℕ)
    (S : InputStack t lambda → List Bool)
    (F : Fin 13 → List Bool) :
    entryEndBank t lambda S F (tapeSource t lambda) =
      S (tapeSource t lambda) := by
  apply BitMachineStackEmbedding.bank_outside
  intro h
  rcases h with ⟨i,hi⟩
  cases hi

theorem embedded_entry_after_bank {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda))
    (S : InputStack t lambda → List Bool)
    (hbank : ∀ i : Fin 13, S (entryEmbed t lambda i) =
      (Paper2.YaoEntryComposition.entryInput t lambda edges bits vertex z g a l).stk i) :
    ∃ steps ≤
      Paper2.YaoEntryComposition.selectorBudget t (paddedEdgeBits e) lambda bits z g +
      Paper2.YaoEntryComposition.payloadBudget t (paddedEdgeBits e) lambda bits l
        (positionEval (paddedEdgesEval edges) a vertex) +
      (6*paddedEdgeCount e + 3*paddedEdgeBits e + 6),
      ((advance (embeddedEntryProgram t lambda))^[steps])
        (⟨some (.inl (.inr false)),
          Paper2.YaoEntryComposition.initialControl,S⟩ :
          TM2.Cfg (fun _ : InputStack t lambda => Bool)
            Paper2.YaoEntryComposition.Label
            Paper2.YaoEntryComposition.Control) =
        ⟨none,Paper2.YaoEntryComposition.initialControl,
          entryEndBank t lambda S
            (Paper2.YaoEntryComposition.entryFinal t lambda edges bits vertex z g a l).stk⟩ := by
  let c := Paper2.YaoEntryComposition.entryInput t lambda edges bits vertex z g a l
  let d := Paper2.YaoEntryComposition.entryFinal t lambda edges bits vertex z g a l
  obtain ⟨steps,hsteps,hrun⟩ :=
    Paper2.YaoEntryComposition.physical_entry_combined t lambda
      edges bits vertex z g a l
  have hhalt : ((Paper2.YaoEntryComposition.run steps c).l) = none := by
    rw [hrun]
    rfl
  obtain ⟨actual,hactual,he⟩ := BitMachineStackEmbedding.outputs
    (entryEmbed t lambda) S id id id (by intro x; rfl) none
    Paper2.YaoEntryComposition.program (embeddedEntryProgram t lambda)
    (by intro x; rfl) c steps hhalt
  have hrun' : ((advance Paper2.YaoEntryComposition.program)^[steps]) c = d := by
    simpa only [c,d,Paper2.YaoEntryComposition.run] using hrun
  rw [hrun'] at he
  have hstart : BitMachineStackEmbedding.bank (entryEmbed t lambda) S c.stk = S := by
    exact BitMachineStackEmbedding.bank_eq_self (entryEmbed t lambda) S c.stk
      (by intro i; exact (hbank i).symm)
  refine ⟨actual,by omega,?_⟩
  change ((advance (embeddedEntryProgram t lambda))^[actual])
      (⟨some (.inl (.inr false)),Paper2.YaoEntryComposition.initialControl,
        BitMachineStackEmbedding.bank (entryEmbed t lambda) S c.stk⟩ :
        TM2.Cfg (fun _ : InputStack t lambda => Bool)
          Paper2.YaoEntryComposition.Label Paper2.YaoEntryComposition.Control) =
      ⟨none,Paper2.YaoEntryComposition.initialControl,
        BitMachineStackEmbedding.bank (entryEmbed t lambda) S d.stk⟩ at he
  rw [hstart] at he
  simpa only [entryEndBank,d] using he

#print axioms embedded_entry_after_bank

end Paper2.YaoEntryControllerJoin
