import CurrentAdditive.V40ActivityPrepare
import CurrentAdditive.GaussCellPolynomialClock

/-! One polynomial in the actual ordinary eight-field input length covers
the complete graph parser, scanner, sentinel dispatch and binary writer. -/
namespace CurrentAdditive.V40ActivityClock
noncomputable section
open Paper2 EthInapproximability.CurrentPaper V40ActivityScan
open GaussCellPolynomialClock
open MinimumRatioContext
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
attribute [local irreducible] V40ActivityPrepare.producer gateMachine rankMachine sentinelMachine
  UnaryBinaryEncoding.coefficient

theorem pack_length {J : Type} [Fintype J] [DecidableEq J] (S : J → List Bool) :
    (V40PackedProgram.pack S).length=2*(∑j,(S j).length)+Fintype.card J := by
  simp only [V40PackedProgram.pack,BitMachineBankCodec.encode_length]
  rw [(V40PackedProgram.numbering (K:=J)).symm.sum_comp (fun j=>(S j).length)]

theorem input_length (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :
    (V40ActivityScan.input g s a r ig xv kb).length=
      2*(LiteralEdgeScanFuel.bankBits g a r ig xv kb+s)+Fintype.card K := by
  rw [V40ActivityScan.input,pack_length]
  simp [V40ActivityScan.initial,Fintype.sum_sum_type,LiteralEdgeScanFuel.bankBits]

theorem raw_length (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :
    (V40ActivityPrepare.raw g s a r ig xv kb).length=
      2*((EncodedGraph.encode g).length+a+r+g.edges.length+ig+xv+1+s)+8 := by
  simp [V40ActivityPrepare.raw,BitMachineBankCodec.encode_length,Fin.sum_univ_succ]
  omega

def packedCap (n : Nat):=2*(n+2)+Fintype.card K
def scanCap (n : Nat):=(2*Fintype.card K+1)*(packedCap n+1)+1000*(n+3)^3+1
def branchCap (n : Nat):=
  OrdinaryBitBranch.invocationBound gateMachine (packedCap n) (scanCap n)+
  OrdinaryBitBranch.invocationBound sentinelMachine (packedCap n) ((2*Fintype.card K+4)*(packedCap n+1))+
  OrdinaryBitBranch.invocationBound rankMachine (packedCap n) (scanCap n)+1
def activityCap (n : Nat):=branchCap n+2*(n+2)+2+UnaryBinaryEncoding.coefficient*(n+3)^2
def cap (n : Nat):=V40ActivityPrepare.producer.coefficient*(n+1)^V40ActivityPrepare.producer.degree+
  2*packedCap n+2+activityCap n

theorem invocation_mono (M : BitMachine.Machine) (n N t T : Nat) (hn : n ≤ N) (ht : t ≤ T) :
    OrdinaryBitBranch.invocationBound M n t ≤ OrdinaryBitBranch.invocationBound M N T := by
  unfold OrdinaryBitBranch.invocationBound MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  gcongr

theorem clock_bound (g : EncodedGraph.Graph) (s a r ig xv : Nat) (kb : Bool) :
    V40ActivityPrepare.clock g s a r ig xv kb ≤ cap (V40ActivityPrepare.raw g s a r ig xv kb).length := by
  let n:=(V40ActivityPrepare.raw g s a r ig xv kb).length
  have hraw:=raw_length g s a r ig xv kb
  have hbits:=LiteralEdgeScanFuel.bankBits_eq g a r ig xv kb
  have hsi : s+xv ≤ n := by dsimp [n]; omega
  have hb : LiteralEdgeScanFuel.bankBits g a r ig xv kb ≤ n+2 := by dsimp [n]; omega
  have hi : (V40ActivityScan.input g s a r ig xv kb).length ≤ packedCap n := by
    rw [input_length]
    dsimp [packedCap,n]
    omega
  have ht : V40ActivityScan.scanClock g s a r ig xv kb ≤ scanCap n := by
    unfold V40ActivityScan.scanClock scanCap
    gcongr
  have hG:=invocation_mono gateMachine _ _ _ _ hi ht
  have hR:=invocation_mono rankMachine _ _ _ _ hi ht
  have hP:=invocation_mono sentinelMachine _ _ _ _ hi
    (Nat.mul_le_mul_left (2*Fintype.card K+4) (Nat.add_le_add_right hi 1))
  have hbranch : V40ActivityScan.branchClock g s a r ig xv kb ≤ branchCap n := by
    unfold V40ActivityScan.branchClock branchCap
    omega
  have hsq:=Nat.pow_le_pow_left (show s+xv+3 ≤ n+3 by omega) 2
  have hmul:=Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq
  have hactivity : V40ActivityScan.clock g s a r ig xv kb ≤ activityCap n := by
    unfold V40ActivityScan.clock activityCap
    omega
  unfold V40ActivityPrepare.clock cap
  change _ ≤ V40ActivityPrepare.producer.coefficient*(n+1)^V40ActivityPrepare.producer.degree+
    2*packedCap n+2+activityCap n
  dsimp only [n] at *
  omega

theorem packed_polynomial : PolynomialBound (fun _ n=>packedCap n) :=
  add (mul (constant 2) (add second (constant 2))) (constant _)
theorem scan_polynomial : PolynomialBound (fun _ n=>scanCap n) :=
  add (add (mul (constant _) (add packed_polynomial (constant 1)))
    (mul (constant 1000) (power (add second (constant 3)) 3))) (constant 1)
theorem branch_polynomial : PolynomialBound (fun _ n=>branchCap n) := by
  have hg:=uniform_invocation gateMachine packed_polynomial scan_polynomial
  have hp:=uniform_invocation sentinelMachine packed_polynomial
    (mul (constant (2*Fintype.card K+4)) (add packed_polynomial (constant 1)))
  have hr:=uniform_invocation rankMachine packed_polynomial scan_polynomial
  exact add (add (add hg hp) hr) (constant 1)
theorem activity_polynomial : PolynomialBound (fun _ n=>activityCap n) :=
  add (add (add branch_polynomial (mul (constant 2) (add second (constant 2)))) (constant 2))
    (mul (constant _) (power (add second (constant 3)) 2))
theorem cap_polynomial : PolynomialBound (fun _ n=>cap n) :=
  add (add (add (mul (constant _) (power (add second (constant 1)) _))
    (mul (constant 2) packed_polynomial)) (constant 2)) activity_polynomial

theorem exists_bound : ∃C d : Nat,∀n,cap n ≤ C*(n+1)^d := by
  obtain ⟨C,d,h⟩:=cap_polynomial
  exact ⟨C,d,fun n=>by simpa using h 0 n⟩
def coefficient:=Classical.choose exists_bound
def degree:=Classical.choose (Classical.choose_spec exists_bound)
theorem cap_bound (n : Nat) : cap n ≤ coefficient*(n+1)^degree :=
  Classical.choose_spec (Classical.choose_spec exists_bound) n
theorem outputs {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :
    let value:=match LiteralEdgeEncoder.activity hs (LiteralEdgeEncoder.edge g hg) (ig,z) a with
      | some p=>p.val | none=>s
    V40ActivityPrepare.machine.OutputsWithin
      (V40ActivityPrepare.raw g s a.val r ig.val (CanonicalEndpointRankBridge.itemValue z) z.isRight)
      value.bits (coefficient*((V40ActivityPrepare.raw g s a.val r ig.val
        (CanonicalEndpointRankBridge.itemValue z) z.isRight).length+1)^degree) := by
  apply BitMachine.outputsWithin_mono _ (V40ActivityPrepare.outputs g hg hs ig z a)
  exact (clock_bound _ _ _ _ _ _ _).trans (cap_bound _)

#print axioms outputs
end
end CurrentAdditive.V40ActivityClock
