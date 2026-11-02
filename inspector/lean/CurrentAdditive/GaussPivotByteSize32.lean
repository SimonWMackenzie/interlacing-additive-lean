import CurrentAdditive.GaussPivotFinalPolynomial32

namespace CurrentAdditive.GaussPivotByteSize32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussStepFields32

noncomputable section

set_option maxHeartbeats 0

private def C : Nat := UnaryBinaryEncoding.coefficient+7

def copyBytes (S : Stack → List Bool) : Nat :=
  ∑ q : Fin 4, (S (GaussBranchFields32.source .pivot q)).length

theorem copyClock_eq (S : Stack → List Bool) :
    GaussBranchFields32.copyClock .pivot S = 2*copyBytes S+12 := by
  simp [GaussBranchFields32.copyClock,copyBytes,Fin.sum_univ_succ]
  omega

def assemblyBytes (w : Fin 4 → List Bool) : Nat :=
  ∑ q : Fin 4, (w q).length

theorem assemblyClock_eq (w : Fin 4 → List Bool) :
    GaussStateAssemble16.clock w = 2*assemblyBytes w+12 := by
  simp [GaussStateAssemble16.clock,assemblyBytes,Fin.sum_univ_succ]
  omega

def byteCharge {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hr : s.r < m) (hc : s.c < k) : Nat :=
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  let T := GaussStepTagRun32.afterActive
    (GaussStepParseRun32.parsed s foreign).stk true
  let ps' := s.pivots ++ [p]
  let pair := GaussControlTrace.pivotPacket p
  GaussPivotRawClock32.inputBankCharge s foreign +
  (GaussControlTrace.statePacket s).length +
  copyBytes T +
  (GaussControlTrace.pivotsPacket s.pivots).length +
  s.pivots.length.bits.length +
  pair.length +
  (SourceListMachineWriter.result true pair).length +
  (SourceListEncoding.fields
    (s.pivots.map GaussControlTrace.pivotPacket)).length +
  (natField pair.length ++ pair).length +
  ps'.length +
  (SourceListMachineWriter.result false
    (List.replicate ps'.length true)).length +
  (natField ps'.length).length +
  (SourceListEncoding.fields
    (ps'.map GaussControlTrace.pivotPacket)).length +
  assemblyBytes (GaussControlTrace.stateBank
    (⟨(GaussControlTrace.step s).B,ps'.length,s.c+1,ps'⟩ :
      GaussControlTrace.State m k)) +
  (GaussControlTrace.statePacket
    (⟨(GaussControlTrace.step s).B,ps'.length,s.c+1,ps'⟩ :
      GaussControlTrace.State m k)).length

def quadraticCoefficient : Nat := 1000*(C+1)

theorem staticCharge_quadratic {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hr : s.r < m) (hc : s.c < k) :
    GaussPivotPolynomial32.staticCharge s foreign hr hc ≤
      quadraticCoefficient * (byteCharge s foreign hr hc+1)^2 := by
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  let T := GaussStepTagRun32.afterActive
    (GaussStepParseRun32.parsed s foreign).stk true
  let ps' := s.pivots ++ [p]
  let pair := GaussControlTrace.pivotPacket p
  let successor : GaussControlTrace.State m k :=
    ⟨(GaussControlTrace.step s).B,ps'.length,s.c+1,ps'⟩
  let N := byteCharge s foreign hr hc
  have hparts : N =
      GaussPivotRawClock32.inputBankCharge s foreign +
      (GaussControlTrace.statePacket s).length +
      copyBytes T +
      (GaussControlTrace.pivotsPacket s.pivots).length +
      s.pivots.length.bits.length +
      pair.length +
      (SourceListMachineWriter.result true pair).length +
      (SourceListEncoding.fields
        (s.pivots.map GaussControlTrace.pivotPacket)).length +
      (natField pair.length ++ pair).length +
      ps'.length +
      (SourceListMachineWriter.result false
        (List.replicate ps'.length true)).length +
      (natField ps'.length).length +
      (SourceListEncoding.fields
        (ps'.map GaussControlTrace.pivotPacket)).length +
      assemblyBytes (GaussControlTrace.stateBank successor) +
      (GaussControlTrace.statePacket successor).length := rfl
  have hinit : GaussPivotRawClock32.inputBankCharge s foreign ≤ N := by
    omega
  have hstate : (GaussControlTrace.statePacket s).length ≤ N := by
    omega
  have hcopy : copyBytes T ≤ N := by omega
  have hpivots : (GaussControlTrace.pivotsPacket s.pivots).length ≤ N := by
    omega
  have hbits : s.pivots.length.bits.length ≤ N := by omega
  have hpair : pair.length ≤ N := by omega
  have hpairFrame : (SourceListMachineWriter.result true pair).length ≤ N := by
    omega
  have hbody : (SourceListEncoding.fields
      (s.pivots.map GaussControlTrace.pivotPacket)).length ≤ N := by
    omega
  have hpayload : (natField pair.length ++ pair).length ≤ N := by
    omega
  have hcount : ps'.length ≤ N := by omega
  have hcountFrame : (SourceListMachineWriter.result false
      (List.replicate ps'.length true)).length ≤ N := by omega
  have hfield : (natField ps'.length).length ≤ N := by omega
  have hbody' : (SourceListEncoding.fields
      (ps'.map GaussControlTrace.pivotPacket)).length ≤ N := by omega
  have hassembly : assemblyBytes (GaussControlTrace.stateBank successor) ≤ N := by
    omega
  have hpacket : (GaussControlTrace.statePacket successor).length ≤ N := by
    omega
  have hraw : GaussPivotRawClock32.rawPhaseBound s foreign ≤
      11*N+40 := by
    unfold GaussPivotRawClock32.rawPhaseBound
    rw [copyClock_eq]
    change 9*((GaussControlTrace.statePacket s).length+1)+1+9+
      (2*copyBytes T+12+4) ≤ 11*N+40
    omega
  have hsplit : GaussPivotSplitClock32.splitPhaseBound s.pivots ≤
      5*N+6 := by
    unfold GaussPivotSplitClock32.splitPhaseBound
    omega
  have hpairPhase : GaussPivotPairClock32.pairPhaseBound pair ≤
      2*N+3 := by
    unfold GaussPivotPairClock32.pairPhaseBound
    omega
  have hpairSq : (pair.length+1)^2 ≤ (N+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hpairMul := Nat.mul_le_mul_left C hpairSq
  have hframe : GaussPivotPairClock32.payloadPhaseBound pair ≤
      C*(N+1)^2+4*N+8 := by
    unfold GaussPivotPairClock32.payloadPhaseBound
    dsimp [C] at hpairMul ⊢
    omega
  have happend : GaussPivotAppendClock32.appendPhaseBound
      (SourceListEncoding.fields
        (s.pivots.map GaussControlTrace.pivotPacket))
      (natField pair.length ++ pair) ≤ 8*N+11 := by
    unfold GaussPivotAppendClock32.appendPhaseBound
    omega
  have hcountSq : (ps'.length+1)^2 ≤ (N+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hcountMul := Nat.mul_le_mul_left C hcountSq
  have hheader : GaussPivotHeaderJoinClock32.headerPhaseBound ps'.length ≤
      C*(N+1)^2+4*N+8 := by
    unfold GaussPivotHeaderJoinClock32.headerPhaseBound
    dsimp [C] at hcountMul ⊢
    omega
  have hjoin : GaussPivotPolynomial32.joinData ps' ≤ 8*N+12 := by
    unfold GaussPivotPolynomial32.joinData
    omega
  have hfinish : GaussPivotPolynomial32.finishData successor ≤
      4*N+15 := by
    unfold GaussPivotPolynomial32.finishData
    rw [assemblyClock_eq]
    omega
  let Q := C*(N+1)^2
  have hstatic : GaussPivotPolynomial32.staticCharge s foreign hr hc ≤
      2*Q+200*(N+1) := by
    change GaussPivotRawClock32.inputBankCharge s foreign +
      GaussPivotRawClock32.rawPhaseBound s foreign +
      GaussPivotSplitClock32.splitPhaseBound s.pivots +
      GaussPivotPairClock32.pairPhaseBound pair +
      GaussPivotPairClock32.payloadPhaseBound pair +
      GaussPivotAppendClock32.appendPhaseBound
        (SourceListEncoding.fields
          (s.pivots.map GaussControlTrace.pivotPacket))
        (natField pair.length ++ pair) +
      GaussPivotHeaderJoinClock32.headerPhaseBound ps'.length +
      GaussPivotPolynomial32.joinData ps' +
      GaussPivotPolynomial32.finishData successor ≤
      2*Q+200*(N+1)
    omega
  have hlin : N+1 ≤ (N+1)^2 := by nlinarith
  have hpoly1 : 2*Q+200*(N+1) ≤
      (2*C+200)*(N+1)^2 := by
    have hm := Nat.mul_le_mul_left 200 hlin
    dsimp [Q]
    nlinarith
  have hcoeff : 2*C+200 ≤ quadraticCoefficient := by
    dsimp [quadraticCoefficient]
    omega
  have hpoly2 := Nat.mul_le_mul_right ((N+1)^2) hcoeff
  have hfinal := hstatic.trans (hpoly1.trans hpoly2)
  exact hfinal

#print axioms copyClock_eq
#print axioms assemblyClock_eq
#print axioms staticCharge_quadratic

end
end CurrentAdditive.GaussPivotByteSize32
