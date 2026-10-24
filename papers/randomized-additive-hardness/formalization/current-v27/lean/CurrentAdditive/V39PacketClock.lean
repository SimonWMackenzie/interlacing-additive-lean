import CurrentAdditive.V39TypedPacket

/-! Packing overhead is linear in the input length and the actual local run
bound, with a constant depending only on the fixed finite program. -/
namespace CurrentAdditive.V39WholeBankPacket
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
variable {N : Nat} {L V : Type} [Fintype L] [Fintype V]

theorem clock_mono (P : L → TM2.Stmt (fun _ : Fin N => Bool) L V)
    {a b t u : Nat} (hab : a≤b) (htu : t≤u) : clock P a t≤clock P b u := by
  unfold clock size
  gcongr

theorem clock_linear (P : L → TM2.Stmt (fun _ : Fin N => Bool) L V)
    (inputLength time : Nat) :
    clock P inputLength time ≤ clock P 1 1*(inputLength+time+1) := by
  let X := inputLength+time+1
  let A := (2*N+1)+1+(2*N+8)*(2*N*(1+BitMachineStackGrowth.perStep P))
  let B := (2*N+1)+6+(2*N+4)+(2*N+8)*N
  have hB : B≤B*X := by
    have hX : 1≤X := by dsimp [X]; omega
    simpa using Nat.mul_le_mul_left B hX
  calc
    clock P inputLength time ≤ clock P X X := clock_mono P (by dsimp [X]; omega) (by dsimp [X]; omega)
    _ = A*X+B := by unfold clock size; dsimp [A,B]; ring
    _ ≤ A*X+B*X := Nat.add_le_add_left hB _
    _ = clock P 1 1*X := by unfold clock size; dsimp [A,B]; ring

#print axioms clock_linear
end
end CurrentAdditive.V39WholeBankPacket

namespace CurrentAdditive.V39TypedPacket
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
open Turing EthInapproximability.CurrentPaper
variable {S L V : Type} [Fintype S] [DecidableEq S] [Fintype L] [Fintype V]
variable (g k tape : S) (hgk : g≠k) (hgt : g≠tape) (hkt : k≠tape)

def clockCoefficient (P : L → TM2.Stmt (fun _ : S => Bool) L V) :=
  let a := V39ThreePortFrame.workCount g k tape
  3*(a+1)+V39WholeBankPacket.clock (finiteProgram g k tape hgk hgt hkt P) 1 1*(a+1)

theorem clock_linear (P : L → TM2.Stmt (fun _ : S => Bool) L V)
    (inputLength time : Nat) :
    clock g k tape hgk hgt hkt P inputLength time ≤
      clockCoefficient g k tape hgk hgt hkt P*(inputLength+time+1) := by
  let a := V39ThreePortFrame.workCount g k tape
  let X := inputLength+time+1
  let C := V39WholeBankPacket.clock (finiteProgram g k tape hgk hgt hkt P) 1 1
  have hX : 1≤X := by dsimp [X]; omega
  have hsize : inputLength+a+time+1≤(a+1)*X := by dsimp [X]; nlinarith
  have hinner := V39WholeBankPacket.clock_linear
    (finiteProgram g k tape hgk hgt hkt P) (inputLength+a) time
  have hinner' := hinner.trans (Nat.mul_le_mul_left C hsize)
  have hfront : a+1+2*(inputLength+a)+2≤3*(a+1)*X := by dsimp [X] at *; nlinarith
  unfold clock clockCoefficient
  change a+1+2*(inputLength+a)+2+_≤(3*(a+1)+C*(a+1))*X
  calc
    _ ≤ 3*(a+1)*X+C*((a+1)*X) := Nat.add_le_add hfront hinner'
    _ = _ := by ring

#print axioms clock_linear
end
end CurrentAdditive.V39TypedPacket
