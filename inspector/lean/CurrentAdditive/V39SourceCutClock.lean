import CurrentAdditive.V39SourceCut
import Paper2.E6Clock

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
namespace CurrentAdditive.V39SourceFront
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition

/-- Scalar majorant only; `pb` is the exact fixed inner machine push bound. -/
def cutPolynomial (pb C3 j C E p Y : ℕ) : ℕ :=
  let mid := 4*Y+1+2^j*(2*Y+1)
  AEth2.Cut.cutTimeG (2^j) 1 pb Y
    (C3*(Y+1)^3+2*Y+2+AEth3.innerOf 0 Y Y Y) +
  2*mid+2+SelectedTape.Bind.Retain.timeBound 1 1 SelectedTape.Bind.idC
    SelectedTape.Bind.idD SelectedTape.Bind.idMachine.pushBound mid +
  30*mid+30+C*(mid+1)^E*(1+2*p)

theorem cutPolynomial_poly (pb C3 j C E p : ℕ) :
    Unit4Shell.Poly.PolyIn id (cutPolynomial pb C3 j C E p) := by
  unfold cutPolynomial AEth2.Cut.cutTimeG AEth3.innerOf SelectedTape.Bind.Retain.timeBound
  repeat (first
    | exact Unit4Shell.Poly.self
    | exact Unit4Shell.Poly.const _
    | apply Unit4Shell.Poly.add
    | apply Unit4Shell.Poly.mul
    | apply Unit4Shell.Poly.pow)

theorem cut_clock_dom (K cutoff j C E p : ℕ) (Φ : EncodedCNF.Formula)
    (hr : AEth4.routed4 K cutoff (EncodedCNF.encode Φ) = Φ) (Y : ℕ)
    (hY : (EncodedCNF.encode Φ).length+AEth.expLen Φ.variables+1 ≤ Y)
    (hNX : Φ.variables ≤ (EncodedCNF.encode Φ).length) :
    AEth5.twoCutTime K cutoff j (EncodedCNF.encode Φ)+
      30*cutScale K cutoff j (EncodedCNF.encode Φ)+30+
      C*(cutScale K cutoff j (EncodedCNF.encode Φ)+1)^E*(1+2*p) ≤
    cutPolynomial (AEth4.inner4 K cutoff).pushBound
      (3000+30*AEth4.phiLen cutoff) j C E p Y := by
  have h0 : AEth3.innerOf AEth3.innerMachine.pushBound Y Y Y = AEth3.innerOf 0 Y Y Y := by
    unfold AEth3.innerOf; simp only [Nat.zero_mul]
  have hI := (AEth3.innerOf_mono (pb:=AEth3.innerMachine.pushBound)
    (show (EncodedCNF.encode Φ).length ≤ Y by omega)
    (show Φ.variables ≤ Y by omega) (show AEth.expLen Φ.variables ≤ Y by omega)).trans
      (le_of_eq h0)
  have hT : AEth4.inner4Time K cutoff (EncodedCNF.encode Φ) ≤
      (3000+30*AEth4.phiLen cutoff)*(Y+1)^3+2*Y+2+AEth3.innerOf 0 Y Y Y := by
    unfold AEth4.inner4Time
    rw [AEth4.route3Out_eq,hr,AEth3.innerTime_eq]
    unfold AEth4.route3Time
    have := Nat.mul_le_mul_left (3000+30*AEth4.phiLen cutoff)
      (Nat.pow_le_pow_left (show (EncodedCNF.encode Φ).length+1 ≤ Y+1 by omega) 3)
    omega
  have hcut := AEth4.cutTimeG_mono (2^j) 1 (AEth4.inner4 K cutoff).pushBound
    (show (EncodedCNF.encode Φ).length ≤ Y by omega) hT
  have hf : (AEth3.fOut Φ).length ≤ 2*Y := by rw [AEth3.fOut_length]; omega
  have hm : AEth5.midLen K cutoff j (EncodedCNF.encode Φ) ≤ 4*Y+1+2^j*(2*Y+1) := by
    unfold AEth5.midLen AEth5.L1 AEth3.cutLen
    rw [hr]
    have := Nat.mul_le_mul_left (2^j) (show (AEth3.fOut Φ).length+1 ≤ 2*Y+1 by omega)
    omega
  have he : cutScale K cutoff j (EncodedCNF.encode Φ) =
      AEth5.midLen K cutoff j (EncodedCNF.encode Φ) := rfl
  have hret := AEth5.retain_timeBound_mono SelectedTape.Bind.idC SelectedTape.Bind.idD
    SelectedTape.Bind.idMachine.pushBound hm
  have hp := Nat.mul_le_mul_right (1+2*p) (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) E))
  unfold AEth5.twoCutTime cutPolynomial
  dsimp only
  rw [he]
  omega

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

include D B in
/-- Every fixed physical front clock is subexponential in the ORIGINAL
number of sparse-CNF variables, with the encoded formula polynomial retained. -/
theorem cut_clock_sparse (K cutoff j C E p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ K*Φ.val.variables → N₀ ≤ Φ.val.variables →
      AEth5.twoCutTime K cutoff j (EncodedCNF.encode Φ.val)+
        30*cutScale K cutoff j (EncodedCNF.encode Φ.val)+30+
        C*(cutScale K cutoff j (EncodedCNF.encode Φ.val)+1)^E*(1+2*p) ≤
      A*⌈(2:ℝ)^(ε*Φ.val.variables)⌉₊*((EncodedCNF.encode Φ.val).length+1)^d := by
  apply AEth4.budget_of_dom D B K 0 _
    (cutPolynomial (AEth4.inner4 K cutoff).pushBound (3000+30*AEth4.phiLen cutoff) j C E p)
    (cutPolynomial_poly _ _ _ _ _ _) cutoff _ ε hε
  intro Φ hsp hN
  simp only [Nat.zero_mul,pow_zero,mul_one]
  apply cut_clock_dom
  · exact AEth4.routed4_encode K cutoff Φ.val Φ.property hsp hN
  · nlinarith
  · exact SourceOriginalVariableCapture.original_n_le_input Φ.val

variable {S : Type} [Fintype S] [DecidableEq S]
  (gPort kPort tPort : S) (hgk : gPort ≠ kPort) (hgt : gPort ≠ tPort) (hkt : kPort ≠ tPort)

theorem cutWord_large (K cutoff j : ℕ) (hcutoff : 1 ≤ cutoff) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length ≤ K*Φ.val.variables) (hlarge : cutoff ≤ Φ.val.variables)
    (tape : List Bool) :
    cutWord D B gPort kPort tPort hgk hgt hkt K cutoff j hcutoff
      (EncodedCNF.encode Φ.val) tape =
    EncodedComplexity.pair
      (BitMachineBankCodec.encode (framedBank D B gPort kPort tPort hgk hgt hkt hcutoff
        (EncodedCNF.encode Φ.val) (tape.take (AEth3.cutLen Φ.val))))
      ((tape.take (2^j*AEth3.cutLen Φ.val)).drop (AEth3.cutLen Φ.val)) := by
  unfold cutWord AEth5.L1
  rw [AEth4.routed4_encode K cutoff Φ.val Φ.property hsp hlarge]

end
end CurrentAdditive.V39SourceFront
#print axioms CurrentAdditive.V39SourceFront.cut_clock_sparse
