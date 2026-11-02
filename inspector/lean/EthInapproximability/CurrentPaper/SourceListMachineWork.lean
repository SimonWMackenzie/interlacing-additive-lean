import EthInapproximability.CurrentPaper.SourceListMachineOuter
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-!
# Per-item accounting for the physical source-list loop

This is arithmetic for the actual controller's intended run theorem. The
unread suffix and already-emitted accumulator are absent from `itemCost`.
Consequently a branch-count bound multiplies one uniform branch cost once,
not a polynomial power of the number of branches.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineWork

open BitMachine

variable (M : Machine)

def itemCost (input output : List Bool) (bound : Nat) : Nat :=
  20*(input.length+1)*(input.length.bits.length+1) + bound +
    4*input.length + output.length +
    M.stackCount*(input.length+bound*M.pushBound+1)+9

def work (inputs : List (List Bool)) (output : List Bool → List Bool)
    (bound : List Bool → Nat) : Nat :=
  (inputs.map fun x => itemCost M x (output x) (bound x)).sum

theorem work_nil (output : List Bool → List Bool) (bound : List Bool → Nat) :
    work M [] output bound = 0 := rfl

theorem work_cons (x : List Bool) (xs : List (List Bool))
    (output : List Bool → List Bool) (bound : List Bool → Nat) :
    work M (x::xs) output bound =
      itemCost M x (output x) (bound x) + work M xs output bound := rfl

/-- One uniform per-branch bound is multiplied by the branch count just once. -/
theorem work_le_count (xs : List (List Bool)) (output : List Bool → List Bool)
    (bound : List Bool → Nat) (B : Nat)
    (h : ∀ x ∈ xs, itemCost M x (output x) (bound x) ≤ B) :
    work M xs output bound ≤ xs.length * B := by
  induction xs with
  | nil => simp [work]
  | cons x xs ih =>
      rw [work_cons]
      have hx := h x (by simp)
      have htail : ∀ y ∈ xs, itemCost M y (output y) (bound y) ≤ B := by
        intro y hy
        exact h y (by simp [hy])
      have ht := ih htail
      simp only [List.length_cons,Nat.succ_mul]
      omega

/-- A uniform per-item envelope is polynomial in the item size and the
actual callback bound, with no dependence on the number of list entries. -/
theorem itemCost_le_envelope (input output : List Bool) (bound L R T : Nat)
    (hin : input.length ≤ L) (hout : output.length ≤ R) (htime : bound ≤ T) :
    itemCost M input output bound ≤
      20*(L+1)*(L+1)+T+4*L+R+
        M.stackCount*(L+T*M.pushBound+1)+9 := by
  have hbits := UnaryBinaryEncoding.bits_length_le input.length
  have hq : (input.length+1)*(input.length.bits.length+1) ≤ (L+1)*(L+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hq20 := Nat.mul_le_mul_left 20 hq
  have hpush := Nat.mul_le_mul_right M.pushBound htime
  have hstack : M.stackCount*(input.length+bound*M.pushBound+1) ≤
      M.stackCount*(L+T*M.pushBound+1) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold itemCost
  nlinarith

end EthInapproximability.CurrentPaper.SourceListMachineWork
