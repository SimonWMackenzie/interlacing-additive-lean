import CurrentAdditive.FeatureCoordinateTransition96

/-! Literal packed-state size accounting, with all retained words charged. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace CurrentAdditive.FeatureStateSize96
open EthInapproximability.CurrentPaper
open CurrentAdditive.FeatureOldDescriptorFrame96

def measure (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  (SourceListEncoding.encode (words cs)).length+
    (SourceListEncoding.fields (words cs)).length+cs.length+j.bits.length+
    qfuel.length+jUnary.length+carry.length+
    (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length+
    ys.length+1

theorem extra_length_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (k : Fin 96) :
    (extra j ys qfuel jUnary carry k).length ≤ measure j ys cs qfuel jUnary carry := by
  unfold extra
  split_ifs <;> simp [measure] <;> omega

theorem initial_cell_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (k : Fin 96) :
    (FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry k).length ≤
      measure j ys cs qfuel jUnary carry := by
  have hlow (i : Fin 15) :
      (FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry
        (FeatureCoordinateBank96.low i)).length ≤ measure j ys cs qfuel jUnary carry := by
    rw [FeatureCoordinateStage96.initialBank,FeatureCoordinateBank96.frame_low]
    fin_cases i <;> simp [measure] <;> omega
  by_cases hk : k.val<15
  · exact hlow ⟨k.val,hk⟩
  · rw [FeatureCoordinateStage96.initialBank,FeatureCoordinateBank96.frame_high
      _ _ _ _ _ _ k (by omega)]
    exact extra_length_le j ys cs qfuel jUnary carry k

theorem stateWord_length_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (FeatureCoordinateTransition96.stateWord j ys cs qfuel jUnary carry).length ≤
      300*measure j ys cs qfuel jUnary carry := by
  have hs : (∑ k : Fin 96,
      (FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry k).length) ≤
      96*measure j ys cs qfuel jUnary carry := by
    calc
      _ ≤ ∑ _ : Fin 96, measure j ys cs qfuel jUnary carry := by
        apply Finset.sum_le_sum
        intro k _
        exact initial_cell_le j ys cs qfuel jUnary carry k
      _ = _ := by simp
  have hpos : 1 ≤ measure j ys cs qfuel jUnary carry := by unfold measure; omega
  rw [FeatureCoordinateTransition96.stateWord,BitMachineBankCodec.encode_length]
  nlinarith

#print axioms initial_cell_le
#print axioms stateWord_length_le
end CurrentAdditive.FeatureStateSize96
