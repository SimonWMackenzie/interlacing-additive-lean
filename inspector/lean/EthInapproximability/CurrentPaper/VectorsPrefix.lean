import EthInapproximability.CurrentPaper.EntryVectorsCell

namespace EthInapproximability.CurrentPaper.VectorsPrefix

open Turing BitMachineEncoding
open EthInapproximability.CurrentPaper.EntryVectorsCell

noncomputable section

def B0 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  st x y (cellBank edges D nV m M4) []

def B1 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (B0 edges D nV m M4 x y) (c 11) (List.replicate y true)

def B2 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (Function.update
    (Function.update (B1 edges D nV m M4 x y) (c 11) [])
    (c 16) (List.replicate (y % m) true))
    (c 15) (List.replicate (y / m) true)

def B3 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (B2 edges D nV m M4 x y) (c 12) (List.replicate x true)

def B4 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (Function.update
    (Function.update (B3 edges D nV m M4 x y) (c 12) [])
    (c 18) (List.replicate (x % D) true))
    (c 17) (List.replicate (x / D) true)

theorem B2_fresh (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ)
    (k : CS) (h11 : k ≠ c 11) (h16 : k ≠ c 16) (h15 : k ≠ c 15) :
    B2 edges D nV m M4 x y k = B0 edges D nV m M4 x y k := by
  simp only [B2, B1, Function.update_of_ne h15, Function.update_of_ne h16,
    Function.update_of_ne h11]

theorem B3_fresh (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ)
    (k : CS) (h12 : k ≠ c 12) :
    B3 edges D nV m M4 x y k = B2 edges D nV m M4 x y k := by
  simp only [B3, Function.update_of_ne h12]

theorem copy_y (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P1)^[2 * y + 2])
      (⟨some BitMachineCopy.Label.scan, none, B0 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, none, B1 edges D nV m M4 x y⟩ := by
  have h := FamilyRowGeneric.copy_blank sCopyY1 (B0 edges D nV m M4 x y)
    (by simp [B0, st, cellBank, sCopyY1, c, YI])
    (by simp [B0, st, cellBank, sCopyY1, c, YI])
  have hsrc : B0 edges D nV m M4 x y (sCopyY1 0) =
      List.replicate y true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem divide_y (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P2)^[MatrixUnaryDivision.totalTime y m])
      (⟨some MatrixUnaryDivision.Label.start, false, B1 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, false, B2 edges D nV m M4 x y⟩ := by
  have h := FamilyRowGeneric.div_run sDivY (B1 edges D nV m M4 x y) y m
    (by simp [B1, B0, st, sDivY, c])
    (by simp [B1, B0, st, cellBank, sDivY, c])
    (by simp [B1, B0, st, cellBank, sDivY, c])
    (by simp [B1, B0, st, cellBank, sDivY, c])
    (by simp [B1, B0, st, cellBank, sDivY, c])
    (by simp [B1, B0, st, cellBank, sDivY, c])
  simpa [P2, B2, sDivY, c] using h

theorem copy_x (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P3)^[2 * x + 2])
      (⟨some BitMachineCopy.Label.scan, none, B2 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, none, B3 edges D nV m M4 x y⟩ := by
  have h := FamilyRowGeneric.copy_blank sCopyX (B2 edges D nV m M4 x y)
    (by change B2 edges D nV m M4 x y (c 19) = []
        rw [B2_fresh _ _ _ _ _ _ _ (c 19) (by decide) (by decide) (by decide)]
        rfl)
    (by change B2 edges D nV m M4 x y (c 12) = []
        rw [B2_fresh _ _ _ _ _ _ _ (c 12) (by decide) (by decide) (by decide)]
        rfl)
  have hsrc : B2 edges D nV m M4 x y (sCopyX 0) =
      List.replicate x true := by
    rw [show sCopyX 0 = XI from rfl,
      B2_fresh _ _ _ _ _ _ _ XI (by decide) (by decide) (by decide)]
    rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem divide_x (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ((advance P4)^[MatrixUnaryDivision.totalTime x D])
      (⟨some MatrixUnaryDivision.Label.start, false, B3 edges D nV m M4 x y⟩ :
        TM2.Cfg (fun _ : CS => Bool) _ _) =
      ⟨none, false, B4 edges D nV m M4 x y⟩ := by
  have h := FamilyRowGeneric.div_run sDivX (B3 edges D nV m M4 x y) x D
    (by rfl)
    (by change B3 edges D nV m M4 x y (c 7) = _
        rw [B3_fresh _ _ _ _ _ _ _ (c 7) (by decide),
      B2_fresh _ _ _ _ _ _ _ (c 7) (by decide) (by decide) (by decide)]; rfl)
    (by change B3 edges D nV m M4 x y (c 13) = _
        rw [B3_fresh _ _ _ _ _ _ _ (c 13) (by decide),
      B2_fresh _ _ _ _ _ _ _ (c 13) (by decide) (by decide) (by decide)]; rfl)
    (by change B3 edges D nV m M4 x y (c 18) = _
        rw [B3_fresh _ _ _ _ _ _ _ (c 18) (by decide),
      B2_fresh _ _ _ _ _ _ _ (c 18) (by decide) (by decide) (by decide)]; rfl)
    (by change B3 edges D nV m M4 x y (c 17) = _
        rw [B3_fresh _ _ _ _ _ _ _ (c 17) (by decide),
      B2_fresh _ _ _ _ _ _ _ (c 17) (by decide) (by decide) (by decide)]; rfl)
    (by change B3 edges D nV m M4 x y (c 14) = _
        rw [B3_fresh _ _ _ _ _ _ _ (c 14) (by decide),
      B2_fresh _ _ _ _ _ _ _ (c 14) (by decide) (by decide) (by decide)]; rfl)
  simpa [P4, B4, sDivX, c] using h

#print axioms copy_y
#print axioms divide_y
#print axioms copy_x
#print axioms divide_x

end
end EthInapproximability.CurrentPaper.VectorsPrefix
