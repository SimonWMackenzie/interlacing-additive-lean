import EthInapproximability.CurrentPaper.WeightedRawWordsCost

/-! # S2: the level-0 numeric words from master N only

One fixed program `level0Program = depthProgram ; costProgram` (one charged
handoff). From the S1 exit bank it writes consumer words 1..4 and masters
`B`, `Y`, and leaves every scratch cell empty. The identities with
`ETHParameterScaleMachineInput.words (EffectiveIteration.initialInput c e b)`
for `b = EffectiveIteration.sourceDepth n` are proved below. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

def level0Program := BitMachineRawSequence.program depthProgram costProgram
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  (edgeCtrl, (none, (none, ((), none)))) costCtrl

abbrev Level0Ctrl := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control ETHScaleEdgePreparation.FullControl
    (BitMachineRawSequence.Control (Option Bool)
      (BitMachineRawSequence.Control (Option Bool) (Unit × Option Bool)))) CostCtrlT

def level0Ctrl : Level0Ctrl := ((edgeCtrl, (none, (none, ((), none)))), costCtrl)

/-- The S2 exit bank. -/
def level0Bank (n : ℕ) (w : List Bool) (c : ℕ) : Global → List Bool :=
  costFinal (afterDepth (afterUnpack n w c) n) (EffectiveIteration.sourceDepth n)

def level0Bound (n : ℕ) : ℕ :=
  depthBound n + costBound (EffectiveIteration.sourceDepth n) + 1

theorem level0_run (n : ℕ) (w : List Bool) (c : ℕ) :
    ∃ t ≤ level0Bound n,
      ((advance level0Program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel edgeStartLabel)), level0Ctrl,
          afterUnpack n w c⟩ : TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, level0Ctrl, level0Bank n w c⟩ := by
  obtain ⟨t1, ht1, h1⟩ := depth_run n (afterUnpack n w c)
    (by simp [afterUnpack, afterParse])
    (by intro k; simp [afterUnpack, afterParse])
    (by simp [afterUnpack, afterParse])
    (by simp [afterUnpack, afterParse])
    (by simp [afterUnpack, afterParse])
  obtain ⟨t2, ht2, h2⟩ := cost_run (EffectiveIteration.sourceDepth n)
    (afterDepth (afterUnpack n w c) n)
    (by simp [afterDepth])
    (by intro i; simp [afterDepth, afterUnpack, afterParse])
    (by intro i; simp [afterDepth, afterUnpack, afterParse])
    (by intro i; simp [afterDepth, afterUnpack, afterParse])
    (by intro k; simp [afterDepth, afterUnpack, afterParse])
    (by simp [afterDepth, afterUnpack, afterParse])
    (by simp [afterDepth, afterUnpack, afterParse])
    (by simp [afterDepth, afterUnpack, afterParse])
    (by simp [afterDepth, afterUnpack, afterParse])
    (by simp [afterDepth, afterUnpack, afterParse])
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs depthProgram costProgram
    (BitMachineRawSequence.leftLabel edgeStartLabel)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (edgeCtrl, (none, (none, ((), none)))) (edgeCtrl, (none, (none, ((), none))))
    costCtrl costCtrl (afterUnpack n w c) (afterDepth (afterUnpack n w c) n)
    (level0Bank n w c) t1 t2 h1 h2
  exact ⟨t, by unfold level0Bound; omega, h⟩

/-! ## Identity with the literal level-0 input -/

theorem costExp_eq (b : ℕ) : costExp b = IndexSeed.exponent b := by
  unfold costExp IndexSeed.exponent
  rw [Nat.add_comm 1 b]

theorem level0_word1 (n : ℕ) (w : List Bool) (c e : ℕ) :
    level0Bank n w c (rawCell 1) = ETHParameterScaleMachineInput.words
      (EffectiveIteration.initialInput c e (EffectiveIteration.sourceDepth n)) 1 := by
  simp [level0Bank, costFinal, afterDepth, ETHParameterScaleMachineInput.words,
    EffectiveIteration.initialInput]

theorem level0_word2 (n : ℕ) (w : List Bool) (c e : ℕ) :
    level0Bank n w c (rawCell 2) = ETHParameterScaleMachineInput.words
      (EffectiveIteration.initialInput c e (EffectiveIteration.sourceDepth n)) 2 := by
  simp [level0Bank, costFinal, ETHParameterScaleMachineInput.words,
    EffectiveIteration.initialInput, costExp_eq, Nat.add_comm]

theorem level0_word3 (n : ℕ) (w : List Bool) (c e : ℕ) :
    level0Bank n w c (rawCell 3) = ETHParameterScaleMachineInput.words
      (EffectiveIteration.initialInput c e (EffectiveIteration.sourceDepth n)) 3 := by
  simp [level0Bank, costFinal, ETHParameterScaleMachineInput.words,
    EffectiveIteration.initialInput, costExp_eq, IndexSeed.width]

theorem level0_word4 (n : ℕ) (w : List Bool) (c e : ℕ) :
    level0Bank n w c (rawCell 4) = ETHParameterScaleMachineInput.words
      (EffectiveIteration.initialInput c e (EffectiveIteration.sourceDepth n)) 4 := by
  simp [level0Bank, costFinal, ETHParameterScaleMachineInput.words,
    EffectiveIteration.initialInput, costExp_eq, IndexSeed.width]

theorem level0_B (n : ℕ) (w : List Bool) (c : ℕ) :
    level0Bank n w c (aux .B) = List.replicate (EffectiveIteration.sourceDepth n) true := by
  simp [level0Bank, costFinal, afterDepth]

theorem level0_Y (n : ℕ) (w : List Bool) (c : ℕ) :
    level0Bank n w c (aux .Y) = List.replicate
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget true := by
  simp [level0Bank, costFinal, Iteration.seedState, costExp_eq, Nat.add_comm]

/-- The whole S2 exit bank, cell by cell: only N, Gw, C, B, Y and consumer
words 1..4 are nonempty. -/
theorem level0Bank_eq (n : ℕ) (w : List Bool) (c : ℕ) :
    level0Bank n w c =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
          (Function.update (fun _ => [])
          (aux .N) (List.replicate n true))
          (aux .Gw) w)
          (aux .C) (List.replicate c true))
          (rawCell 1) (List.replicate (EffectiveIteration.sourceDepth n) true))
          (aux .B) (List.replicate (EffectiveIteration.sourceDepth n) true))
          (aux .Y) (List.replicate (1 + costExp (EffectiveIteration.sourceDepth n)) true))
          (rawCell 2) (List.replicate (1 + costExp (EffectiveIteration.sourceDepth n)) true))
          (rawCell 4) (List.replicate (2 ^ costExp (EffectiveIteration.sourceDepth n)) true))
          (rawCell 3)
            (List.replicate (2 ^ 2 ^ costExp (EffectiveIteration.sourceDepth n)) true) := rfl

#print axioms level0_run
#print axioms level0_word1
#print axioms level0_word2
#print axioms level0_word3
#print axioms level0_word4
#print axioms level0_B
#print axioms level0_Y

end
end EthInapproximability.CurrentPaper.WeightedRawWords
