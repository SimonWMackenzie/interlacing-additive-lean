import CurrentAdditive.GaussWorkItemRoundComplete
import EthInapproximability.CurrentPaper.SourceListEncoding

/-! The descending unary scan prepends each item field.  These equalities
show that its accumulator is the ordered V2 field list for the suffix of
columns not yet processed. -/

namespace CurrentAdditive.GaussWorkListSuffix

open EthInapproximability.CurrentPaper

def packets {m k : Nat} (B : Fin m → Fin k → ℚ) (f : Fin k)
    (j : Nat) : List (List Bool) :=
  ((List.finRange k).drop j).map (GaussWorkItemContextSerialize.workPacket B f)

def fieldsAt {m k : Nat} (B : Fin m → Fin k → ℚ) (f : Fin k)
    (j : Nat) : List Bool := SourceListEncoding.fields (packets B f j)

theorem suffix_cons {k : Nat} (j : Nat) (hj : j < k) :
    (List.finRange k).drop j =
      (⟨j, hj⟩ : Fin k) :: (List.finRange k).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (l := List.finRange k) (i := j)
    (by simpa only [List.length_finRange] using hj)]
  congr 1
  apply Fin.ext
  simp

theorem fields_step {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) (j : Nat) (hj : j < k) :
    fieldsAt B f j =
      SourceListMachineWriter.result true
          (GaussWorkItemContextSerialize.workPacket B f ⟨j, hj⟩) ++
        fieldsAt B f (j + 1) := by
  simp [fieldsAt, packets, suffix_cons j hj, SourceListEncoding.fields,
    SourceListMachineWriter.result, EncodedCommunication.natField]

theorem fields_at_width {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) : fieldsAt B f k = [] := by
  have hl : (List.finRange k).drop k = [] := by simp
  simp [fieldsAt, packets, hl, SourceListEncoding.fields]

theorem fields_at_zero {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) :
    fieldsAt B f 0 =
      SourceListEncoding.fields
        ((List.finRange k).map (GaussWorkItemContextSerialize.workPacket B f)) := by
  simp [fieldsAt, packets]

#print axioms fields_step
#print axioms fields_at_width
#print axioms fields_at_zero

end CurrentAdditive.GaussWorkListSuffix
