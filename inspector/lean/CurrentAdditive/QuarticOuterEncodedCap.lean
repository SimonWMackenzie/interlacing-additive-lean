import CurrentAdditive.QuarticOuterOutput

namespace Paper2.CurrentAdditive.QuarticOuterEncodedCap

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticOuterOutput

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536

def growthFactor : ℕ := 2 * ((Lift.a FS + 3) + 3)

def frontSizeCap {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : J => Bool) L V) (I F : ℕ) : ℕ :=
  I + growthFactor * (BitMachineStackGrowth.perStep P * F)

def copyTimeCap (X : ℕ) : ℕ := 3 * (2 * X + 3) + 1

def copySizeCap (X : ℕ) : ℕ :=
  X + growthFactor *
    (BitMachineStackGrowth.perStep (CopyAll.prog copies) * copyTimeCap X)

theorem outer_encoded_le {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : J => Bool) L V)
    (c : TM2.Cfg (fun _ : J => Bool) L V)
    (S : K → List Bool) (t F I : ℕ)
    (hrun : ((((advance P)^[t]) c).stk) = outerBank S)
    (ht : t ≤ F)
    (hI : (BitMachineBankCodec.encode c.stk).length ≤ I) :
    (BitMachineBankCodec.encode (outerBank S)).length ≤
      frontSizeCap P I F := by
  have hg := Lift.size_run P c t
  rw [hrun] at hg
  have hm := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep P) ht
  have hm' := Nat.mul_le_mul_left growthFactor hm
  dsimp [frontSizeCap, growthFactor] at *
  omega

theorem copied_encoded_le (S : K → List Bool)
    (X t : ℕ)
    (hX : (BitMachineBankCodec.encode (outerBank S)).length ≤ X)
    (ht : t ≤ copyTimeCap (BitMachineBankCodec.encode (outerBank S)).length)
    (hrun : ((((advance (CopyAll.prog copies))^[t])
      (⟨some (.inl ⟨0, by omega⟩), none, outerBank S⟩ :
        TM2.Cfg (fun _ : J => Bool) _ _)).stk) =
          CopyAll.done copies 3 (outerBank S)) :
    (BitMachineBankCodec.encode
      (CopyAll.done copies 3 (outerBank S))).length ≤
        copySizeCap X := by
  have hg := Lift.size_run (CopyAll.prog copies)
    (⟨some (.inl ⟨0, by omega⟩), none, outerBank S⟩ :
      TM2.Cfg (fun _ : J => Bool) _ _) t
  rw [hrun] at hg
  have ht' : t ≤ copyTimeCap X := by
    dsimp [copyTimeCap] at *
    omega
  have hm := Nat.mul_le_mul_left
    (BitMachineStackGrowth.perStep (CopyAll.prog copies)) ht'
  have hm' := Nat.mul_le_mul_left growthFactor hm
  dsimp [copySizeCap, growthFactor] at *
  omega

theorem outer_and_copied_encoded_le {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : J => Bool) L V)
    (c : TM2.Cfg (fun _ : J => Bool) L V)
    (S : K → List Bool) (tF F I tC : ℕ)
    (hfront : ((((advance P)^[tF]) c).stk) = outerBank S)
    (htF : tF ≤ F)
    (hI : (BitMachineBankCodec.encode c.stk).length ≤ I)
    (htC : tC ≤ copyTimeCap
      (BitMachineBankCodec.encode (outerBank S)).length)
    (hcopy : ((((advance (CopyAll.prog copies))^[tC])
      (⟨some (.inl ⟨0, by omega⟩), none, outerBank S⟩ :
        TM2.Cfg (fun _ : J => Bool) _ _)).stk) =
          CopyAll.done copies 3 (outerBank S)) :
    (BitMachineBankCodec.encode (outerBank S)).length ≤
      frontSizeCap P I F ∧
    (BitMachineBankCodec.encode
      (CopyAll.done copies 3 (outerBank S))).length ≤
        copySizeCap (frontSizeCap P I F) := by
  have hA := outer_encoded_le P c S tF F I hfront htF hI
  exact ⟨hA, copied_encoded_le S (frontSizeCap P I F) tC hA htC hcopy⟩

#print axioms outer_encoded_le
#print axioms copied_encoded_le
#print axioms outer_and_copied_encoded_le

end
end Paper2.CurrentAdditive.QuarticOuterEncodedCap
