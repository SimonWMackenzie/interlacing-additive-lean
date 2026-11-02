import CurrentAdditive.FeatureCoordinateBank96
import CurrentAdditive.CylinderRawInputProjection
import CurrentAdditive.FeatureSeedMachine

namespace CurrentAdditive.FeatureSeedLayout
noncomputable section

open EthInapproximability.CurrentPaper
open FeatureCoordinateStage96 FeatureOldDescriptorFrame96

def seedBody : List Bool := SourceListEncoding.fields (words [[]])
def seedPacket : List Bool := SourceListEncoding.encode (words [[]])

theorem seedBody_bytes : seedBody=[true,true,false,false] := by decide
theorem seedPacket_bytes : seedPacket=FeatureSeedMachine.seedBytes := by decide

def bank (raw : List Bool) (ys : List Nat) : Fin 96 → List Bool := fun k =>
  if k=8 then seedPacket else if k=9 then seedBody else if k=12 then [true]
  else if k=13 then [true] else if k=29 then raw
  else if k=30 then SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)
  else if k=31 then List.replicate ys.length true else []

theorem bank_exact (raw : List Bool) (ys : List Nat) :
    bank raw ys=FeatureCoordinateStage96.initialBank 0 ys [[]] [] [] raw := by
  funext k
  by_cases hk : k.val<15
  · have h:=FeatureCoordinateBank96.frame_low seedPacket seedBody [true] 0 1
      (extra 0 ys [] [] raw) (⟨k.val,hk⟩:Fin 15)
    change bank raw ys k=frame seedPacket seedBody [true] 0 1 (extra 0 ys [] [] raw) k
    have hb (i : Fin 15) : bank raw ys (FeatureCoordinateBank96.low i)=
        (![[],[],[],[],[],[],[],[],seedPacket,seedBody,[],[],[true],[true],[]] : Fin 15 → List Bool) i := by
      fin_cases i <;> simp [bank,FeatureCoordinateBank96.low]
    exact (hb ⟨k.val,hk⟩).trans h.symm
  · have hk' : 15 ≤ k.val := by omega
    change bank raw ys k=frame seedPacket seedBody [true] 0 1 (extra 0 ys [] [] raw) k
    rw [FeatureCoordinateBank96.frame_high _ _ _ _ _ _ k hk']
    have h8 : k≠8 := by intro h; subst k; omega
    have h9 : k≠9 := by intro h; subst k; omega
    have h12 : k≠12 := by intro h; subst k; omega
    have h13 : k≠13 := by intro h; subst k; omega
    by_cases h15 : k=15
    · subst k; simp [bank,extra]
    by_cases h17 : k=17
    · subst k; simp [bank,extra]
    by_cases h18 : k=18
    · subst k; simp [bank,extra]
    simp [bank,extra,h8,h9,h12,h13,h15,h17,h18]

def output (raw : List Bool) (q : Nat) (ys : List Nat) : List Bool :=
  BitMachineBankCodec.encode ![BitMachineBankCodec.encode (bank raw ys),List.replicate q true]

theorem output_exact (raw : List Bool) (q : Nat) (ys : List Nat) :
    output raw q ys=BitMachineBankCodec.encode
      ![BitMachineBankCodec.encode (FeatureCoordinateStage96.initialBank 0 ys [[]] [] [] raw),
        List.replicate q true] := by rw [output,bank_exact]

#print axioms bank_exact

end
end CurrentAdditive.FeatureSeedLayout
