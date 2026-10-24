import EthInapproximability.CurrentPaper.MatrixStage4OneHot
import EthInapproximability.CurrentPaper.MatrixWordGather

/-!
# Literal one-hot serialization of general Stage--4 family fields

Each family pair `(ℓ,α)` has one row in the stored first-coordinate table
and one in the stored source-row table. The representation is intentionally
simple and polynomial in the literal table dimensions. Its production cost
from the sampler is not claimed here.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4FamilyData

open MatrixMaterialization Construction

def oneHot (m : ℕ) (j : Fin m) : List Bool :=
  List.replicate j.val false ++ true :: List.replicate (m-1-j.val) false

@[simp] theorem oneHot_length (m : ℕ) (j : Fin m) :
    (oneHot m j).length = m := by
  simp [oneHot]
  omega

def fieldTable {rows m : ℕ} (f : Fin rows → Fin m) : List Bool :=
  rowMajor (fun r j =>
    (oneHot m (f r)).get ⟨j.val,by rw [oneHot_length]; exact j.isLt⟩)

@[simp] theorem fieldTable_length {rows m : ℕ} (f : Fin rows → Fin m) :
    (fieldTable f).length = rows*m := by
  unfold fieldTable
  exact rowMajor_length _

theorem field_word {rows m : ℕ} (f : Fin rows → Fin m)
    (r : Fin rows) :
    MatrixWordGather.word (r.val*m) m (fieldTable f) =
      oneHot m (f r) := by
  rw [MatrixWordGather.word_eq_ofFn]
  have he :
      (List.ofFn fun j : Fin m =>
        (fieldTable f)[r.val*m+j.val]?.getD false) =
      List.ofFn (fun j : Fin m =>
        (oneHot m (f r)).get ⟨j.val,by rw [oneHot_length]; exact j.isLt⟩) := by
    apply congrArg List.ofFn
    funext j
    unfold fieldTable
    rw [rowMajor_entry]
    rfl
  rw [he]
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_ofFn]
    rfl

theorem field_gather_run {rows m : ℕ} (f : Fin rows → Fin m)
    (r : Fin rows) :
    ∃ t ≤ m * (3*(r.val*m+m)+3*(rows*m)+11)+2,
      MatrixWordGather.Forward.run t
        (MatrixWordGather.Forward.cfg (some (.inr .test)) none
          (List.replicate (r.val*m) true) (fieldTable f) []
          (List.replicate m true) []) =
      MatrixWordGather.Forward.cfg none none
        (List.replicate (r.val*m+m) true) (fieldTable f) [] []
        (oneHot m (f r)) := by
  obtain ⟨t,ht,he⟩ := MatrixWordGather.Forward.gather_run m
    (r.val*m) (fieldTable f) []
  refine ⟨t, ?_, ?_⟩
  · simpa only [fieldTable_length] using ht
  · simpa only [field_word, List.append_nil] using he

theorem field_decode_run {rows m : ℕ} (f : Fin rows → Fin m)
    (r : Fin rows) :
    MatrixStage4OneHot.run ((f r).val+1)
      (MatrixStage4OneHot.cfg (some ()) none
        (oneHot m (f r)) []) =
      MatrixStage4OneHot.cfg none none
        (List.replicate (m-1-(f r).val) false)
        (List.replicate (f r).val true) := by
  simpa only [oneHot, List.replicate_zero, Nat.add_zero] using
    MatrixStage4OneHot.one_hot_run (f r).val 0
      (List.replicate (m-1-(f r).val) false) none

def familyFirst {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx)) :
    Fin (L*q) → Fin (qOne a) :=
  fun r => (family (finProdFinEquiv.symm r).1
    (finProdFinEquiv.symm r).2).1

def familyRow {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx)) :
    Fin (L*q) → Fin rx :=
  fun r => (family (finProdFinEquiv.symm r).1
    (finProdFinEquiv.symm r).2).2

theorem familyFirst_at {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (ℓ : Fin L) (α : Fin q) :
    familyFirst family (finProdFinEquiv (ℓ,α)) = (family ℓ α).1 := by
  simp [familyFirst]

theorem familyRow_at {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (ℓ : Fin L) (α : Fin q) :
    familyRow family (finProdFinEquiv (ℓ,α)) = (family ℓ α).2 := by
  simp [familyRow]

theorem family_first_gather_run {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (ℓ : Fin L) (α : Fin q) :
    let row := finProdFinEquiv (ℓ,α)
    let m := qOne a
    ∃ t ≤ m * (3*(row.val*m+m)+3*(L*q*m)+11)+2,
      MatrixWordGather.Forward.run t
        (MatrixWordGather.Forward.cfg (some (.inr .test)) none
          (List.replicate (row.val*m) true)
          (fieldTable (familyFirst family)) []
          (List.replicate m true) []) =
      MatrixWordGather.Forward.cfg none none
        (List.replicate (row.val*m+m) true)
        (fieldTable (familyFirst family)) [] []
        (oneHot m (family ℓ α).1) := by
  dsimp
  simpa only [familyFirst_at] using
    field_gather_run (familyFirst family) (finProdFinEquiv (ℓ,α))

theorem family_row_gather_run {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (ℓ : Fin L) (α : Fin q) :
    let row := finProdFinEquiv (ℓ,α)
    ∃ t ≤ rx * (3*(row.val*rx+rx)+3*(L*q*rx)+11)+2,
      MatrixWordGather.Forward.run t
        (MatrixWordGather.Forward.cfg (some (.inr .test)) none
          (List.replicate (row.val*rx) true)
          (fieldTable (familyRow family)) []
          (List.replicate rx true) []) =
      MatrixWordGather.Forward.cfg none none
        (List.replicate (row.val*rx+rx) true)
        (fieldTable (familyRow family)) [] []
        (oneHot rx (family ℓ α).2) := by
  dsimp
  simpa only [familyRow_at] using
    field_gather_run (familyRow family) (finProdFinEquiv (ℓ,α))

theorem family_first_decode_run {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (ℓ : Fin L) (α : Fin q) :
    MatrixStage4OneHot.run ((family ℓ α).1.val+1)
      (MatrixStage4OneHot.cfg (some ()) none
        (oneHot (qOne a) (family ℓ α).1) []) =
      MatrixStage4OneHot.cfg none none
        (List.replicate (qOne a-1-(family ℓ α).1.val) false)
        (List.replicate (family ℓ α).1.val true) := by
  simpa only [familyFirst_at] using
    field_decode_run (familyFirst family) (finProdFinEquiv (ℓ,α))

theorem family_row_decode_run {a q L rx : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (ℓ : Fin L) (α : Fin q) :
    MatrixStage4OneHot.run ((family ℓ α).2.val+1)
      (MatrixStage4OneHot.cfg (some ()) none
        (oneHot rx (family ℓ α).2) []) =
      MatrixStage4OneHot.cfg none none
        (List.replicate (rx-1-(family ℓ α).2.val) false)
        (List.replicate (family ℓ α).2.val true) := by
  simpa only [familyRow_at] using
    field_decode_run (familyRow family) (finProdFinEquiv (ℓ,α))

end EthInapproximability.CurrentPaper.MatrixStage4FamilyData
