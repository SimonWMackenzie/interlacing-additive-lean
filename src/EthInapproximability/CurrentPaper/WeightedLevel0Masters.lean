import EthInapproximability.CurrentPaper.WeightedLevel0Ready

/-! Lane owner:b-weighted-level-4, unit 2, segment 1/2 interface, piece 1d:
the master region of the level-0 exit, literally.

At the exit of `readyProgram` (`WeightedLevel0Ready.G4 …`), the retained master
cells hold exactly the words later phases need, from the SAME run:
`C = unary c`, `B = unary b(n)`, `Y = unary y₀`, `E = unary |E|`,
`Gw = encode (serializeGraph G)`, `K = unary kValue M n` (k fuel),
`w 7 = unary |V|`; `N` and the rows/cols sources `nat 3 0/1` are blank (cleared).
Pure identities; no machine claim. -/

namespace EthInapproximability.CurrentPaper.WeightedLevel0Masters

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A master cell outside the row program's image is untouched by phases 2–4. -/
theorem l0_master (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (a : WeightedRawWords.Aux) (h7 : a ≠ .w 7) (hn : ∀ m, a ≠ .nat 3 m) :
    level0RowsBank M G n c F Q P (mc a) = masterC M G n c a := by
  unfold level0RowsBank
  rw [bank_outside _ _ _ _ (by
    rintro ⟨j, hj⟩
    change rowCell (rowEquiv j) = mc a at hj
    rcases hr : rowEquiv j with z | (i | m)
    · rw [hr] at hj
      exact h7 (Sum.inr.inj (Sum.inr.inj hj)).symm
    · rw [hr] at hj
      exact wc_ne_mc _ _ hj
    · rw [hr] at hj
      exact hn m.val (Sum.inr.inj (Sum.inr.inj hj)).symm)]
  have hn9 : ¬ ∃ j, cells9 j = mc a := by
    rintro ⟨j, hj⟩
    exact wc_ne_mc _ _ hj
  show (if ∃ j, cells9 j = mc a then [] else C2def M G n c F Q P (mc a)) = _
  rw [if_neg hn9]
  show bank levelEmb (C1def M G n c) (Zdef G n c F Q P) (Sum.inr (Sum.inr a)) = _
  rw [bank_outside _ _ _ _ (by
    rintro ⟨k, hk⟩
    rcases k with k | k <;> cases hk)]
  show bank rawEmb _ _ (rawEmb (Sum.inr a)) = _
  rw [bank_at]
  rfl

/-- The master cells after `readyProgram` for every master other than `N`,
`w 7`, `nat 3 _`. -/
theorem ready_master (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (a : WeightedRawWords.Aux) (hN : a ≠ .N) (h7 : a ≠ .w 7) (hn : ∀ m, a ≠ .nat 3 m) :
    G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc a)) = masterC M G n c a := by
  show BitMachineClearBank.cleared cells2 (G3 (level0RowsBank M G n c F Q P)) (Sum.inl (mc a)) = _
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro i hi
    fin_cases i
    · exact hn 0 (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj hi))).symm
    · exact hn 1 (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj hi))).symm)]
  show Function.update (G2 (level0RowsBank M G n c F Q P)) dstC _ (Sum.inl (mc a)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 (level0RowsBank M G n c F Q P)) dstR _ (Sum.inl (mc a)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show BitMachineClearBank.cleared clearCells (level0RowsBank M G n c F Q P) (mc a) = _
  rw [clean_master _ a hN, l0_master M G n c F Q P a h7 hn]

/-- The level-0 master values. -/
theorem masterC_values (G : EndpointGraph V E) (n c : ℕ) :
    masterC M G n c .C = List.replicate c true ∧
    masterC M G n c .B = List.replicate (EffectiveIteration.sourceDepth n) true ∧
    masterC M G n c .Y =
      List.replicate (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget true ∧
    masterC M G n c .E = List.replicate (Fintype.card E) true ∧
    masterC M G n c .Gw = EncodedGraph.encode (EncodedETHSource.serializeGraph G) ∧
    masterC M G n c .K = List.replicate (WeightedRawWords.kValue M n) true ∧
    masterC M G n c (.w 7) = List.replicate (Fintype.card V) true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [masterC, WeightedVertexWord.masterBankKV, WeightedRawWords.masterBank]
    repeat first
      | rw [Function.update_self]
      | rw [Function.update_of_ne (by intro h; cases h)]

#print axioms l0_master
#print axioms ready_master
#print axioms masterC_values

end
end EthInapproximability.CurrentPaper.WeightedLevel0Masters
