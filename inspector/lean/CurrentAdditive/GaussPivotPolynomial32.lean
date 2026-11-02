import CurrentAdditive.GaussPivotRawCharged32

/-! A uniform envelope for the fixed pivot writer.  All coefficients below
depend only on the fixed Fin32 program and the canonical framing machine. -/

namespace CurrentAdditive.GaussPivotPolynomial32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussStepFields32

noncomputable section

set_option maxRecDepth 2048

private def P : Nat := GaussPivotClockGrowth32.pushConstant

def joinData {m k : Nat} (ps : List (Fin m × Fin k)) : Nat :=
  1 + (2*(natField ps.length).length+3) +
    (4*(natField ps.length).length+2*
      (SourceListEncoding.fields
        (ps.map GaussControlTrace.pivotPacket)).length+7)+1

def finishData {m k : Nat} (s : GaussControlTrace.State m k) : Nat :=
  GaussStateAssemble16.clock (GaussControlTrace.stateBank s)+1+
    2*(GaussControlTrace.statePacket s).length+2

def joinUpper (charge n : Nat) : Nat :=
  let J := charge+n
  J + 1 + 12*(charge+P*J)+14+1+n

def headerUpper (charge n : Nat) : Nat :=
  n+1+joinUpper (charge+P*(n+1)) n

def appendPrefixUpper (charge n : Nat) : Nat :=
  n+1+8*(charge+P*n)+10+1

def appendUpper (charge n : Nat) : Nat :=
  let A := appendPrefixUpper charge n
  A+headerUpper (charge+P*A) n

def pairUpper (charge n : Nat) : Nat :=
  2*n+2+appendUpper (charge+P*(2*n+2)) n

def splitUpper (charge n : Nat) : Nat :=
  n+1+pairUpper (charge+P*(n+1)) n

def rawUpper (charge n : Nat) : Nat :=
  n+1+splitUpper (charge+P*(n+1)) n

theorem joinUpper_mono_charge {c d n : Nat} (h : c ≤ d) :
    joinUpper c n ≤ joinUpper d n := by
  dsimp [joinUpper]
  have hj : c+n ≤ d+n := Nat.add_le_add_right h n
  have hp := Nat.mul_le_mul_left P hj
  omega

theorem headerUpper_mono_charge {c d n : Nat} (h : c ≤ d) :
    headerUpper c n ≤ headerUpper d n := by
  unfold headerUpper
  apply Nat.add_le_add_left
  exact joinUpper_mono_charge (Nat.add_le_add_right h _)

theorem appendUpper_mono_charge {c d n : Nat} (h : c ≤ d) :
    appendUpper c n ≤ appendUpper d n := by
  have hp : P * appendPrefixUpper c n ≤
      P * appendPrefixUpper d n := Nat.mul_le_mul_left P (by
    unfold appendPrefixUpper
    omega)
  have ha : appendPrefixUpper c n ≤ appendPrefixUpper d n := by
    unfold appendPrefixUpper
    omega
  have hh := headerUpper_mono_charge (n := n)
    (show c+P*appendPrefixUpper c n ≤
      d+P*appendPrefixUpper d n by omega)
  dsimp [appendUpper]
  omega

theorem pairUpper_mono_charge {c d n : Nat} (h : c ≤ d) :
    pairUpper c n ≤ pairUpper d n := by
  unfold pairUpper
  apply Nat.add_le_add_left
  exact appendUpper_mono_charge (Nat.add_le_add_right h _)

theorem splitUpper_mono_charge {c d n : Nat} (h : c ≤ d) :
    splitUpper c n ≤ splitUpper d n := by
  unfold splitUpper
  apply Nat.add_le_add_left
  exact pairUpper_mono_charge (Nat.add_le_add_right h _)

theorem join_clock_le {m k : Nat} (B' : Fin m → Fin k → ℚ)
    (r c : Nat) (ps : List (Fin m × Fin k))
    (charge n : Nat)
    (hj : joinData ps ≤ n)
    (hf : finishData (⟨B',r,c,ps⟩ : GaussControlTrace.State m k) ≤ n) :
    GaussPivotJoinClock32.uniformClock B' r c ps charge ≤
      joinUpper charge n := by
  let J := charge+joinData ps
  let U := charge+n
  have hJ : J ≤ U := Nat.add_le_add_left hj charge
  have hp := Nat.mul_le_mul_left P hJ
  have hclock : GaussPivotJoinClock32.uniformClock B' r c ps charge =
      J + 1 + 12*(charge+P*J)+14+1+
        finishData (⟨B',r,c,ps⟩ : GaussControlTrace.State m k) := by
    simp only [GaussPivotJoinClock32.uniformClock,
      joinData,finishData,P,J]
    ring
  have hupper : joinUpper charge n =
      U + 1 + 12*(charge+P*U)+14+1+n := rfl
  rw [hclock,hupper]
  omega

theorem header_clock_le {m k : Nat} (B' : Fin m → Fin k → ℚ)
    (c : Nat) (ps : List (Fin m × Fin k))
    (charge n : Nat)
    (hh : GaussPivotHeaderJoinClock32.headerPhaseBound ps.length ≤ n)
    (hj : joinData ps ≤ n)
    (hf : finishData
      (⟨B',ps.length,c,ps⟩ : GaussControlTrace.State m k) ≤ n) :
    GaussPivotHeaderJoinClock32.uniformClock B' c ps charge ≤
      headerUpper charge n := by
  let H := GaussPivotHeaderJoinClock32.headerPhaseBound ps.length
  let C := charge+P*(H+1)
  have hc : C ≤ charge+P*(n+1) := by
    have hm := Nat.mul_le_mul_left P (show H+1 ≤ n+1 by omega)
    omega
  have hjoin := join_clock_le B' ps.length c ps C n hj hf
  have hmono := joinUpper_mono_charge (n := n) hc
  change H+1+GaussPivotJoinClock32.uniformClock B' ps.length c ps C ≤
    n+1+joinUpper (charge+P*(n+1)) n
  omega

theorem append_clock_le {m k : Nat} (B' : Fin m → Fin k → ℚ)
    (c : Nat) (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (charge n : Nat)
    (ha : GaussPivotAppendClock32.appendPhaseBound
      (SourceListEncoding.fields
        (ps.map GaussControlTrace.pivotPacket))
      (natField (GaussControlTrace.pivotPacket p).length ++
        GaussControlTrace.pivotPacket p) ≤ n)
    (hh : GaussPivotHeaderJoinClock32.headerPhaseBound
      (ps ++ [p]).length ≤ n)
    (hj : joinData (ps ++ [p]) ≤ n)
    (hf : finishData
      (⟨B',(ps ++ [p]).length,c,ps ++ [p]⟩ :
        GaussControlTrace.State m k) ≤ n) :
    GaussPivotAppendClock32.clock B' c ps p charge ≤
      appendUpper charge n := by
  let body := SourceListEncoding.fields
    (ps.map GaussControlTrace.pivotPacket)
  let payload := natField (GaussControlTrace.pivotPacket p).length ++
    GaussControlTrace.pivotPacket p
  let A := GaussPivotAppendClock32.prefixBound body payload charge
  let U := appendPrefixUpper charge n
  have ha' : GaussPivotAppendClock32.appendPhaseBound body payload ≤ n := by
    simpa [body,payload] using ha
  have hA : A ≤ U := by
    have hm := Nat.mul_le_mul_left
      GaussPivotClockGrowth32.pushConstant ha'
    dsimp [A,U,GaussPivotAppendClock32.prefixBound,
      appendPrefixUpper,P]
    omega
  have hc : charge+P*A ≤ charge+P*U := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left P hA) charge
  have hhead := header_clock_le B' c (ps ++ [p])
    (charge+P*A) n hh hj hf
  have hmono := headerUpper_mono_charge (n := n) hc
  change A+GaussPivotHeaderJoinClock32.uniformClock B' c (ps ++ [p])
      (charge+P*A) ≤ U+headerUpper (charge+P*U) n
  omega

theorem pair_clock_le {m k : Nat} (B' : Fin m → Fin k → ℚ)
    (c : Nat) (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (charge n : Nat)
    (hpair : GaussPivotPairClock32.pairPhaseBound
      (GaussControlTrace.pivotPacket p) ≤ n)
    (hpayload : GaussPivotPairClock32.payloadPhaseBound
      (GaussControlTrace.pivotPacket p) ≤ n)
    (ha : GaussPivotAppendClock32.appendPhaseBound
      (SourceListEncoding.fields
        (ps.map GaussControlTrace.pivotPacket))
      (natField (GaussControlTrace.pivotPacket p).length ++
        GaussControlTrace.pivotPacket p) ≤ n)
    (hh : GaussPivotHeaderJoinClock32.headerPhaseBound
      (ps ++ [p]).length ≤ n)
    (hj : joinData (ps ++ [p]) ≤ n)
    (hf : finishData
      (⟨B',(ps ++ [p]).length,c,ps ++ [p]⟩ :
        GaussControlTrace.State m k) ≤ n) :
    GaussPivotPairClock32.clock B' c ps p charge ≤
      pairUpper charge n := by
  let pair := GaussControlTrace.pivotPacket p
  let A := GaussPivotPairClock32.prefixBound pair
  have hpair' : GaussPivotPairClock32.pairPhaseBound pair ≤ n := by
    simpa [pair] using hpair
  have hpayload' : GaussPivotPairClock32.payloadPhaseBound pair ≤ n := by
    simpa [pair] using hpayload
  have hA : A ≤ 2*n+2 := by
    dsimp [A,GaussPivotPairClock32.prefixBound]
    omega
  have hc : charge+P*A ≤ charge+P*(2*n+2) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left P hA) charge
  have happ := append_clock_le B' c ps p (charge+P*A) n ha hh hj hf
  have hmono := appendUpper_mono_charge (n := n) hc
  change A+GaussPivotAppendClock32.clock B' c ps p (charge+P*A) ≤
    2*n+2+appendUpper (charge+P*(2*n+2)) n
  omega

theorem split_clock_le {m k : Nat} (B' : Fin m → Fin k → ℚ)
    (c : Nat) (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (charge n : Nat)
    (hsplit : GaussPivotSplitClock32.splitPhaseBound ps ≤ n)
    (hpair : GaussPivotPairClock32.pairPhaseBound
      (GaussControlTrace.pivotPacket p) ≤ n)
    (hpayload : GaussPivotPairClock32.payloadPhaseBound
      (GaussControlTrace.pivotPacket p) ≤ n)
    (ha : GaussPivotAppendClock32.appendPhaseBound
      (SourceListEncoding.fields
        (ps.map GaussControlTrace.pivotPacket))
      (natField (GaussControlTrace.pivotPacket p).length ++
        GaussControlTrace.pivotPacket p) ≤ n)
    (hh : GaussPivotHeaderJoinClock32.headerPhaseBound
      (ps ++ [p]).length ≤ n)
    (hj : joinData (ps ++ [p]) ≤ n)
    (hf : finishData
      (⟨B',(ps ++ [p]).length,c,ps ++ [p]⟩ :
        GaussControlTrace.State m k) ≤ n) :
    GaussPivotSplitClock32.clock B' c ps p charge ≤
      splitUpper charge n := by
  let A := GaussPivotSplitClock32.splitPhaseBound ps
  have hc : charge+P*(A+1) ≤ charge+P*(n+1) := by
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left P (by omega : A+1 ≤ n+1)) charge
  have hpair' := pair_clock_le B' c ps p (charge+P*(A+1)) n
    hpair hpayload ha hh hj hf
  have hmono := pairUpper_mono_charge (n := n) hc
  change A+1+GaussPivotPairClock32.clock B' c ps p
      (charge+P*(A+1)) ≤
    n+1+pairUpper (charge+P*(n+1)) n
  omega

theorem raw_clock_le {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hr : s.r < m) (hc : s.c < k)
    (charge n : Nat)
    (hcharge : charge ≤ n)
    (hraw : GaussPivotRawClock32.rawPhaseBound s foreign ≤ n)
    (hsplit : GaussPivotSplitClock32.splitPhaseBound s.pivots ≤ n)
    (hpair : GaussPivotPairClock32.pairPhaseBound
      (GaussControlTrace.pivotPacket
        (⟨s.r,hr⟩,⟨s.c,hc⟩)) ≤ n)
    (hpayload : GaussPivotPairClock32.payloadPhaseBound
      (GaussControlTrace.pivotPacket
        (⟨s.r,hr⟩,⟨s.c,hc⟩)) ≤ n)
    (ha : GaussPivotAppendClock32.appendPhaseBound
      (SourceListEncoding.fields
        (s.pivots.map GaussControlTrace.pivotPacket))
      (natField (GaussControlTrace.pivotPacket
        (⟨s.r,hr⟩,⟨s.c,hc⟩)).length ++
        GaussControlTrace.pivotPacket (⟨s.r,hr⟩,⟨s.c,hc⟩)) ≤ n)
    (hh : GaussPivotHeaderJoinClock32.headerPhaseBound
      (s.pivots ++ [((⟨s.r,hr⟩,⟨s.c,hc⟩) : Fin m × Fin k)]).length ≤ n)
    (hj : joinData (s.pivots ++ [((⟨s.r,hr⟩,⟨s.c,hc⟩) : Fin m × Fin k)]) ≤ n)
    (hf : finishData
      (⟨(GaussControlTrace.step s).B,
        (s.pivots ++ [((⟨s.r,hr⟩,⟨s.c,hc⟩) : Fin m × Fin k)]).length,
        s.c+1,s.pivots ++ [((⟨s.r,hr⟩,⟨s.c,hc⟩) : Fin m × Fin k)]⟩ :
          GaussControlTrace.State m k) ≤ n) :
    GaussPivotRawClock32.clock s foreign hr hc charge ≤
      rawUpper n n := by
  let A := GaussPivotRawClock32.rawPhaseBound s foreign
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  let B' := (GaussControlTrace.step s).B
  have hc' : charge+P*(A+1) ≤ n+P*(n+1) := by
    have hm := Nat.mul_le_mul_left P (show A+1 ≤ n+1 by omega)
    omega
  have hs := split_clock_le B' (s.c+1) s.pivots p
    (charge+P*(A+1)) n hsplit hpair hpayload ha hh hj hf
  have hmono := splitUpper_mono_charge (n := n) hc'
  change A+1+GaussPivotSplitClock32.clock B' (s.c+1) s.pivots p
      (charge+P*(A+1)) ≤ n+1+splitUpper (n+P*(n+1)) n
  omega

def staticCharge {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hr : s.r < m) (hc : s.c < k) : Nat :=
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  GaussPivotRawClock32.inputBankCharge s foreign +
  GaussPivotRawClock32.rawPhaseBound s foreign +
  GaussPivotSplitClock32.splitPhaseBound s.pivots +
  GaussPivotPairClock32.pairPhaseBound (GaussControlTrace.pivotPacket p) +
  GaussPivotPairClock32.payloadPhaseBound (GaussControlTrace.pivotPacket p) +
  GaussPivotAppendClock32.appendPhaseBound
    (SourceListEncoding.fields
      (s.pivots.map GaussControlTrace.pivotPacket))
    (natField (GaussControlTrace.pivotPacket p).length ++
      GaussControlTrace.pivotPacket p) +
  GaussPivotHeaderJoinClock32.headerPhaseBound
    (s.pivots ++ [p]).length +
  joinData (s.pivots ++ [p]) +
  finishData
    (⟨(GaussControlTrace.step s).B,(s.pivots ++ [p]).length,
      s.c+1,s.pivots ++ [p]⟩ : GaussControlTrace.State m k)

theorem clock_le_static {m k : Nat}
    (s : GaussControlTrace.State m k)
    (foreign : Stack → List Bool)
    (hr : s.r < m) (hc : s.c < k) :
    GaussPivotRawClock32.clock s foreign hr hc
      (GaussPivotRawClock32.inputBankCharge s foreign) ≤
      rawUpper (staticCharge s foreign hr hc)
        (staticCharge s foreign hr hc) := by
  let N := staticCharge s foreign hr hc
  have h0 : GaussPivotRawClock32.inputBankCharge s foreign ≤ N := by
    dsimp [N,staticCharge]
    omega
  have h1 : GaussPivotRawClock32.rawPhaseBound s foreign ≤ N := by
    dsimp [N,staticCharge]
    omega
  have h2 : GaussPivotSplitClock32.splitPhaseBound s.pivots ≤ N := by
    dsimp [N,staticCharge]
    omega
  let p : Fin m × Fin k := (⟨s.r,hr⟩,⟨s.c,hc⟩)
  have h3 : GaussPivotPairClock32.pairPhaseBound
      (GaussControlTrace.pivotPacket p) ≤ N := by
    dsimp [N,staticCharge,p]
    omega
  have h4 : GaussPivotPairClock32.payloadPhaseBound
      (GaussControlTrace.pivotPacket p) ≤ N := by
    dsimp [N,staticCharge,p]
    omega
  have h5 : GaussPivotAppendClock32.appendPhaseBound
      (SourceListEncoding.fields
        (s.pivots.map GaussControlTrace.pivotPacket))
      (natField (GaussControlTrace.pivotPacket p).length ++
        GaussControlTrace.pivotPacket p) ≤ N := by
    dsimp [N,staticCharge,p]
    omega
  have h6 : GaussPivotHeaderJoinClock32.headerPhaseBound
      (s.pivots ++ [p]).length ≤ N := by
    dsimp [N,staticCharge,p]
    omega
  have h7 : joinData (s.pivots ++ [p]) ≤ N := by
    dsimp [N,staticCharge,p]
    omega
  have h8 : finishData
      (⟨(GaussControlTrace.step s).B,(s.pivots ++ [p]).length,
        s.c+1,s.pivots ++ [p]⟩ : GaussControlTrace.State m k) ≤ N := by
    dsimp [N,staticCharge,p]
    omega
  exact raw_clock_le s foreign hr hc
    (GaussPivotRawClock32.inputBankCharge s foreign) N
    h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem upper_linear_identity (n : Nat) :
    rawUpper n n + rawUpper 0 0 * n =
      rawUpper 1 1 * n + rawUpper 0 0 := by
  dsimp [rawUpper,splitUpper,pairUpper,appendUpper,
    appendPrefixUpper,headerUpper,joinUpper]
  ring

def polynomialCoefficient : Nat := rawUpper 1 1 + rawUpper 0 0

theorem upper_polynomial (n : Nat) :
    rawUpper n n ≤ polynomialCoefficient * (n+1) := by
  have hi := upper_linear_identity n
  have hmul : rawUpper 1 1 * n ≤
      polynomialCoefficient * n :=
    Nat.mul_le_mul_right n (Nat.le_add_right _ _)
  have hconst : rawUpper 0 0 ≤ polynomialCoefficient :=
    Nat.le_add_left _ _
  unfold polynomialCoefficient at hmul hconst ⊢
  rw [Nat.mul_succ]
  omega

#print axioms clock_le_static
#print axioms upper_polynomial

#print axioms join_clock_le

end
end CurrentAdditive.GaussPivotPolynomial32
