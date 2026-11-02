import EthInapproximability.CurrentPaper.VectorsPrefix

namespace EthInapproximability.CurrentPaper.VectorsMiddle

open Turing BitMachineEncoding
open EthInapproximability.CurrentPaper.EntryVectorsCell
open EthInapproximability.CurrentPaper.VectorsPrefix

noncomputable section

theorem B4_fresh (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ)
    (k : CS) (h11 : k ≠ c 11) (h16 : k ≠ c 16) (h15 : k ≠ c 15)
    (h12 : k ≠ c 12) (h18 : k ≠ c 18) (h17 : k ≠ c 17) :
    B4 edges D nV m M4 x y k = B0 edges D nV m M4 x y k := by
  rw [B4, Function.update_of_ne h17, Function.update_of_ne h18,
    Function.update_of_ne h12, B3_fresh _ _ _ _ _ _ _ k h12,
    B2_fresh _ _ _ _ _ _ _ k h11 h16 h15]

def B5 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (B4 edges D nV m M4 x y) (c 19) (List.replicate y true)

def B6 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (B5 edges D nV m M4 x y) (c 20) (List.replicate M4 true)

def B7 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (Function.update (Function.update (B6 edges D nV m M4 x y)
    (c 19) []) (c 20) []) (c 21)
      (EntryUnaryCompare.verdict true false false y M4 ::
        B6 edges D nV m M4 x y (c 21))

def B8 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (Function.update (Function.update (B7 edges D nV m M4 x y)
    (c 15) []) (c 17) []) (c 22)
      (EntryUnaryCompare.verdict false true false (y / m) (x / D) ::
        B7 edges D nV m M4 x y (c 22))

theorem B5_fresh (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ)
    (k : CS) (h19 : k ≠ c 19) :
    B5 edges D nV m M4 x y k = B4 edges D nV m M4 x y k := by
  simp only [B5, Function.update_of_ne h19]

theorem B6_fresh (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ)
    (k : CS) (h20 : k ≠ c 20) :
    B6 edges D nV m M4 x y k = B5 edges D nV m M4 x y k := by
  simp only [B6, Function.update_of_ne h20]

theorem copy_y_again (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P5)^[2 * y + 2])
      (⟨some BitMachineCopy.Label.scan, none, B4 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, none, B5 edges D nV m M4 x y⟩ := by
  have h := FamilyRowGeneric.copy_blank sCopyY2 (B4 edges D nV m M4 x y)
    (by change B4 edges D nV m M4 x y (c 21) = []
        rw [B4_fresh _ _ _ _ _ _ _ (c 21)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        rfl)
    (by change B4 edges D nV m M4 x y (c 19) = []
        rw [B4_fresh _ _ _ _ _ _ _ (c 19)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        rfl)
  have hsrc : B4 edges D nV m M4 x y (sCopyY2 0) =
      List.replicate y true := by
    rw [show sCopyY2 0 = YI from rfl,
      B4_fresh _ _ _ _ _ _ _ YI
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem copy_M4 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P6)^[2 * M4 + 2])
      (⟨some BitMachineCopy.Label.scan, none, B5 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, none, B6 edges D nV m M4 x y⟩ := by
  have h := FamilyRowGeneric.copy_blank sCopyM4 (B5 edges D nV m M4 x y)
    (by change B5 edges D nV m M4 x y (c 21) = []
        rw [B5_fresh _ _ _ _ _ _ _ (c 21) (by decide),
          B4_fresh _ _ _ _ _ _ _ (c 21)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        rfl)
    (by change B5 edges D nV m M4 x y (c 20) = []
        rw [B5_fresh _ _ _ _ _ _ _ (c 20) (by decide),
          B4_fresh _ _ _ _ _ _ _ (c 20)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        rfl)
  have hsrc : B5 edges D nV m M4 x y (sCopyM4 0) =
      List.replicate M4 true := by
    rw [show sCopyM4 0 = c 10 from rfl,
      B5_fresh _ _ _ _ _ _ _ (c 10) (by decide),
      B4_fresh _ _ _ _ _ _ _ (c 10)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem compare_padded (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ∃ t ≤ max y M4 + 2, ∃ v,
      ((advance P7)^[t])
        (⟨some EntryUnaryCompare.CL.loop, (none, none),
          B6 edges D nV m M4 x y⟩ : TM2.Cfg (fun _ : CS => Bool) _ _) =
        ⟨none, v, B7 edges D nV m M4 x y⟩ := by
  have h := EntryUnaryCompare.compare_run (c 19) (c 20) (c 21)
    (by decide) (by decide) (by decide) true false false
    (B6 edges D nV m M4 x y) (none, none) y M4
    (by rfl) (by rfl)
  exact h

theorem compare_copies (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ∃ t ≤ max (y / m) (x / D) + 2, ∃ v,
      ((advance P8)^[t])
        (⟨some EntryUnaryCompare.CL.loop, (none, none),
          B7 edges D nV m M4 x y⟩ : TM2.Cfg (fun _ : CS => Bool) _ _) =
        ⟨none, v, B8 edges D nV m M4 x y⟩ := by
  have h := EntryUnaryCompare.compare_run (c 15) (c 17) (c 22)
    (by decide) (by decide) (by decide) false true false
    (B7 edges D nV m M4 x y) (none, none) (y / m) (x / D)
    (by rfl) (by rfl)
  exact h

#print axioms B4_fresh
#print axioms copy_y_again
#print axioms copy_M4
#print axioms compare_padded
#print axioms compare_copies

end
end EthInapproximability.CurrentPaper.VectorsMiddle
