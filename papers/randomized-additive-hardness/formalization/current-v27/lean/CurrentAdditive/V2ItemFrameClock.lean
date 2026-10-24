import CurrentAdditive.V2ItemFrameCore

/-! A uniform quadratic clock in the source length and all cells discarded
from the ten disposable banks. -/

namespace CurrentAdditive.V2ItemFrameClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.V2ItemFrameCore
open CurrentAdditive.MinimumRatioContext

private noncomputable abbrev W := SourceListMachineWriter.framingMachine true

private theorem arithmetic (n s p c : ℕ) :
    (2*n+2) + c*(n+1)^2 +
      (2*(n+c*(n+1)^2*p)+2) +
      (s*(n+c*(n+1)^2*p)+s+2)+3 ≤
    ((s+4)+((s+2)*p+1)*c+s+9)*(n+1)^2 := by
  let q := (n+1)^2
  have hn : n ≤ q := by dsimp [q]; nlinarith [sq_nonneg (n:ℤ)]
  have h1 : 1 ≤ q := by dsimp [q]; nlinarith
  have ha := Nat.mul_le_mul_left (s+4) hn
  have hb := Nat.mul_le_mul_left (s+9) h1
  calc
    (2*n+2) + c*(n+1)^2 +
        (2*(n+c*(n+1)^2*p)+2) +
        (s*(n+c*(n+1)^2*p)+s+2)+3 =
      (s+4)*n + (((s+2)*p+1)*c)*q + (s+9) := by dsimp [q]; ring
    _ ≤ (s+4)*q + (((s+2)*p+1)*c)*q + (s+9)*q := by omega
    _ = ((s+4)+((s+2)*p+1)*c+s+9)*q := by ring

noncomputable def coefficient : ℕ :=
  (W.stackCount+4) + ((W.stackCount+2)*W.pushBound+1)*
    (UnaryBinaryEncoding.coefficient+7) + W.stackCount+9 + 13

noncomputable def inputSize {N : ℕ} (C : Slots N)
    (S : MachineInvokeCore.StackN N → List Bool) (raw : List Bool) : ℕ :=
  raw.length + ∑ i : Fin 10, (S (clearBank C i)).length

theorem uniform_le (raw : List Bool) :
    MachineInvokeFull.uniformBound W raw (writerTime raw) ≤
      (coefficient - 13)*(raw.length+1)^2 := by
  simpa only [MachineInvokeFull.uniformBound, writerTime, coefficient,
    Nat.add_sub_cancel_right] using
    arithmetic raw.length W.stackCount W.pushBound
      (UnaryBinaryEncoding.coefficient+7)

theorem time_le {N : ℕ} (C : Slots N)
    (S : MachineInvokeCore.StackN N → List Bool) (raw : List Bool) :
    time C S raw ≤ coefficient*(inputSize C S raw+1)^2 := by
  let m := inputSize C S raw
  let n := raw.length
  let z := ∑ i : Fin 10, (S (clearBank C i)).length
  have hm : m = n+z := rfl
  have hnm : n ≤ m := by omega
  have hpow : (n+1)^2 ≤ (m+1)^2 := by nlinarith
  have hq : m+1 ≤ (m+1)^2 := by nlinarith
  have hu := uniform_le raw
  have huc : (coefficient-13)*(n+1)^2 ≤
      (coefficient-13)*(m+1)^2 := Nat.mul_le_mul_left _ hpow
  have hc : 13 ≤ coefficient := by
    unfold coefficient
    omega
  have he : (coefficient-13)+13 = coefficient := by omega
  unfold time clearTime
  change z + 12 + MachineInvokeFull.uniformBound W raw (writerTime raw) + 1 ≤
    coefficient*(m+1)^2
  calc
    z+12+MachineInvokeFull.uniformBound W raw (writerTime raw)+1 ≤
      13*(m+1)^2 + (coefficient-13)*(m+1)^2 := by
        have hz : z ≤ m := by omega
        have h13 := Nat.mul_le_mul_left 13 hq
        have hz13 : z + 13 ≤ 13*(m+1)^2 := by omega
        have hum : MachineInvokeFull.uniformBound W raw (writerTime raw) ≤
            (coefficient-13)*(m+1)^2 := hu.trans huc
        omega
    _ = coefficient*(m+1)^2 := by
      rw [← add_mul, Nat.add_comm 13 (coefficient-13), he]

#print axioms time_le

end CurrentAdditive.V2ItemFrameClock
