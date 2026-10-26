import EthInapproximability.CurrentPaper.SourceGenericBooleanListCost
import EthInapproximability.CurrentPaper.SourceOriginalDinurPrefixMachine
import EthInapproximability.CurrentPaper.SourceOriginalBOTCanonicalListMapperCost

/-!
# Monotone polynomial envelopes of the per-branch source clocks

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE.

`PolyEnv F` says `F : ℕ → ℕ` is monotone and bounded by `C * (n+1)^E` for fixed
`C, E`. The class is closed under constants, the identity, `Nat.size`, sums,
products, fixed powers and composition. Every per-branch envelope of the three
source stages (the admitted Dinur and BOT mappers and packetizer, and this lane's
Boolean mapper) is shown to be `PolyEnv` in the ORIGINAL variable count `n`,
with the digit cap `W c n = c*n+1` substituted for the branch-count digits.
The constants are fixed by the cited records `S, D, B` only.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.PolyEnvelope

def PolyEnv (F : ℕ → ℕ) : Prop := Monotone F ∧ ∃ C E : ℕ, ∀ n, F n ≤ C * (n + 1) ^ E

namespace PolyEnv

theorem const (c : ℕ) : PolyEnv (fun _ => c) :=
  ⟨fun _ _ _ => le_rfl, c, 0, fun _ => by simp⟩

theorem ident : PolyEnv (fun n => n) :=
  ⟨fun _ _ h => h, 1, 1, fun n => by simp⟩

theorem size : PolyEnv (fun n => n.size) :=
  ⟨fun _ _ h => Nat.size_le_size h, 1, 1, fun n => by
    have := EncodedETHSourceComposition.nat_size_le_self n
    simp only [pow_one, one_mul]
    omega⟩

theorem add {F G : ℕ → ℕ} (hF : PolyEnv F) (hG : PolyEnv G) :
    PolyEnv (fun n => F n + G n) := by
  obtain ⟨mF, CF, EF, bF⟩ := hF
  obtain ⟨mG, CG, EG, bG⟩ := hG
  refine ⟨fun a b h => Nat.add_le_add (mF h) (mG h), CF + CG, EF + EG, fun n => ?_⟩
  have h1 : (n+1)^EF ≤ (n+1)^(EF+EG) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n+1)^EG ≤ (n+1)^(EF+EG) := Nat.pow_le_pow_right (by omega) (by omega)
  calc F n + G n ≤ CF*(n+1)^EF + CG*(n+1)^EG := Nat.add_le_add (bF n) (bG n)
    _ ≤ CF*(n+1)^(EF+EG) + CG*(n+1)^(EF+EG) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (CF+CG)*(n+1)^(EF+EG) := by ring

theorem mul {F G : ℕ → ℕ} (hF : PolyEnv F) (hG : PolyEnv G) :
    PolyEnv (fun n => F n * G n) := by
  obtain ⟨mF, CF, EF, bF⟩ := hF
  obtain ⟨mG, CG, EG, bG⟩ := hG
  refine ⟨fun a b h => Nat.mul_le_mul (mF h) (mG h), CF * CG, EF + EG, fun n => ?_⟩
  calc F n * G n ≤ (CF*(n+1)^EF) * (CG*(n+1)^EG) := Nat.mul_le_mul (bF n) (bG n)
    _ = (CF*CG)*(n+1)^(EF+EG) := by ring

theorem pow {F : ℕ → ℕ} (hF : PolyEnv F) (k : ℕ) : PolyEnv (fun n => F n ^ k) := by
  obtain ⟨mF, CF, EF, bF⟩ := hF
  refine ⟨fun a b h => Nat.pow_le_pow_left (mF h) k, CF ^ k, EF * k, fun n => ?_⟩
  calc F n ^ k ≤ (CF*(n+1)^EF) ^ k := Nat.pow_le_pow_left (bF n) k
    _ = CF^k*(n+1)^(EF*k) := by rw [mul_pow, ← pow_mul]

theorem comp {F G : ℕ → ℕ} (hF : PolyEnv F) (hG : PolyEnv G) :
    PolyEnv (fun n => F (G n)) := by
  obtain ⟨mF, CF, EF, bF⟩ := hF
  obtain ⟨mG, CG, EG, bG⟩ := hG
  refine ⟨fun a b h => mF (mG h), CF * (CG + 1) ^ EF, EG * EF, fun n => ?_⟩
  have hp : 1 ≤ (n+1)^EG := Nat.one_le_pow _ _ (by omega)
  have hg : G n + 1 ≤ (CG + 1) * (n+1)^EG := by
    have := bG n
    nlinarith
  calc F (G n) ≤ CF * (G n + 1)^EF := bF (G n)
    _ ≤ CF * ((CG + 1) * (n+1)^EG)^EF := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg EF)
    _ = CF * (CG + 1) ^ EF * (n+1)^(EG*EF) := by rw [mul_pow, ← pow_mul]; ring

/-- A monotone envelope evaluated below `x` is bounded in `x`. -/
theorem at_le {F : ℕ → ℕ} (hF : PolyEnv F) :
    ∃ C E : ℕ, ∀ n x, n ≤ x → F n ≤ C * (x + 1) ^ E := by
  obtain ⟨mF, C, E, bF⟩ := hF
  exact ⟨C, E, fun n x h => (mF h).trans (bF x)⟩

end PolyEnv

/-- Structural closure tactic for explicit envelope expressions. -/
macro "poly_env" : tactic =>
  `(tactic| repeat (first
    | with_reducible assumption
    | with_reducible exact PolyEnv.const _
    | with_reducible exact PolyEnv.ident
    | with_reducible exact PolyEnv.size
    | with_reducible apply PolyEnv.add
    | with_reducible apply PolyEnv.mul
    | with_reducible apply PolyEnv.pow))

/-- The digit cap for the branch count: `c*n+1`. -/
def W (c n : ℕ) : ℕ := c * n + 1

theorem W_env (c : ℕ) : PolyEnv (W c) := by
  unfold W; poly_env

open EncodedETHSource

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (EncodedETHSourceComposition.booleanOccurrence D))

/-! ## Admitted Dinur mapper envelopes -/

theorem dinurInput_env : PolyEnv (SourceOriginalDinurListMapper.inputEnvelope S) := by
  have h : SourceOriginalDinurListMapper.inputEnvelope S =
      fun n => 2*(n+(8*S.density+3)*n*(n.size+1))+2 := rfl
  rw [h]; poly_env

theorem dinurCallback_env : PolyEnv (SourceOriginalDinurListMapper.callbackEnvelope S D) := by
  have hi := dinurInput_env S
  have h : SourceOriginalDinurListMapper.callbackEnvelope S D = fun n =>
      SourceOriginalDinurListMapper.coefficient D *
        (SourceOriginalDinurListMapper.inputEnvelope S n + 3) ^
          SourceOriginalDinurListMapper.exponent D := rfl
  rw [h]; poly_env

theorem dinurOutput_env : PolyEnv (SourceOriginalDinurListMapper.outputEnvelope S D) := by
  have hi := dinurInput_env S
  have hc := dinurCallback_env S D
  have h : SourceOriginalDinurListMapper.outputEnvelope S D = fun n =>
      SourceOriginalDinurListMapper.inputEnvelope S n +
        SourceOriginalDinurListMapper.callbackEnvelope S D n *
          (SourceDinurPacketMachine.machine D).pushBound := rfl
  rw [h]; poly_env

theorem dinurFramed_env : PolyEnv (SourceOriginalDinurListMapper.framedEnvelope S D) := by
  have ho := dinurOutput_env S D
  have h : SourceOriginalDinurListMapper.framedEnvelope S D = fun n =>
      3*SourceOriginalDinurListMapper.outputEnvelope S D n+1 := rfl
  rw [h]; poly_env

theorem dinurFramedTime_env :
    PolyEnv (SourceOriginalDinurListMapper.framedTimeEnvelope S D) := by
  have ho := dinurOutput_env S D
  have hc := dinurCallback_env S D
  have h : SourceOriginalDinurListMapper.framedTimeEnvelope S D = fun n =>
      SourceOriginalDinurListMapper.callbackEnvelope S D n +
        2*SourceOriginalDinurListMapper.outputEnvelope S D n+2 +
        (UnaryBinaryEncoding.coefficient+7)*
          (SourceOriginalDinurListMapper.outputEnvelope S D n+1)^2 := rfl
  rw [h]; poly_env

theorem dinurItem_env : PolyEnv (SourceOriginalDinurListMapper.itemEnvelope S D) := by
  have hi := dinurInput_env S
  have hf := dinurFramed_env S D
  have ht := dinurFramedTime_env S D
  have h : SourceOriginalDinurListMapper.itemEnvelope S D = fun n =>
      20*(SourceOriginalDinurListMapper.inputEnvelope S n+1)*
          (SourceOriginalDinurListMapper.inputEnvelope S n+1) +
        SourceOriginalDinurListMapper.framedTimeEnvelope S D n +
        4*SourceOriginalDinurListMapper.inputEnvelope S n +
        SourceOriginalDinurListMapper.framedEnvelope S D n +
        (SourceListMachineOuterFramed.itemMachine (SourceDinurPacketMachine.machine D)).stackCount *
          (SourceOriginalDinurListMapper.inputEnvelope S n +
            SourceOriginalDinurListMapper.framedTimeEnvelope S D n *
              (SourceListMachineOuterFramed.itemMachine
                (SourceDinurPacketMachine.machine D)).pushBound + 1) + 9 := rfl
  rw [h]; poly_env

/-! ## This lane's Boolean mapper envelopes -/

theorem boolIn_env : PolyEnv (BooleanListMapper.inEnv S D) := dinurOutput_env S D

theorem boolBound_env : PolyEnv (BooleanListMapper.boundEnv S D) := by
  have hi := boolIn_env S D
  have h : BooleanListMapper.boundEnv S D = fun n =>
      7 * (BooleanListMapper.inEnv S D n + 2) +
        (1 + 4 * (BooleanListMapper.convMachine D).pushBound) *
          (Converter.convC D.alphabet D.arity * (BooleanListMapper.inEnv S D n + 1) ^ 27) := rfl
  rw [h]; poly_env

theorem boolOut_env : PolyEnv (BooleanListMapper.outEnv S D) := by
  have hi := boolIn_env S D
  have hb := boolBound_env S D
  have h : BooleanListMapper.outEnv S D = fun n =>
      BooleanListMapper.inEnv S D n +
        BooleanListMapper.boundEnv S D n * (BooleanListMapper.itemMachine D).pushBound := rfl
  rw [h]; poly_env

theorem boolFramed_env : PolyEnv (BooleanListMapper.framedEnv S D) := by
  have ho := boolOut_env S D
  have h : BooleanListMapper.framedEnv S D = fun n => 3 * BooleanListMapper.outEnv S D n + 1 := rfl
  rw [h]; poly_env

theorem boolFramedTime_env : PolyEnv (BooleanListMapper.framedTimeEnv S D) := by
  have ho := boolOut_env S D
  have hb := boolBound_env S D
  have h : BooleanListMapper.framedTimeEnv S D = fun n =>
      BooleanListMapper.boundEnv S D n + 2 * BooleanListMapper.outEnv S D n + 2 +
        (UnaryBinaryEncoding.coefficient + 7) * (BooleanListMapper.outEnv S D n + 1) ^ 2 := rfl
  rw [h]; poly_env

theorem boolItem_env : PolyEnv (BooleanListMapper.itemEnv S D) := by
  have hi := boolIn_env S D
  have hf := boolFramed_env S D
  have ht := boolFramedTime_env S D
  have h : BooleanListMapper.itemEnv S D = fun n =>
      20*(BooleanListMapper.inEnv S D n+1)*(BooleanListMapper.inEnv S D n+1) +
        BooleanListMapper.framedTimeEnv S D n + 4*BooleanListMapper.inEnv S D n +
        BooleanListMapper.framedEnv S D n +
        (SourceListMachineOuterFramed.itemMachine (BooleanListMapper.itemMachine D)).stackCount *
          (BooleanListMapper.inEnv S D n + BooleanListMapper.framedTimeEnv S D n *
            (SourceListMachineOuterFramed.itemMachine
              (BooleanListMapper.itemMachine D)).pushBound + 1) + 9 := rfl
  rw [h]; poly_env

/-! ## Admitted BOT canonical mapper envelopes at word cap `outEnv` -/

theorem botInput_env :
    PolyEnv (fun n => SourceOriginalBOTCanonicalListMapper.inputEnvelope n
      (BooleanListMapper.outEnv S D n)) := by
  have ho := boolOut_env S D
  unfold SourceOriginalBOTCanonicalListMapper.inputEnvelope
  poly_env

theorem botCallback_env :
    PolyEnv (fun n => SourceOriginalBOTCanonicalListMapper.callbackEnvelope B n
      (BooleanListMapper.outEnv S D n)) := by
  have hi := botInput_env S D
  unfold SourceOriginalBOTCanonicalListMapper.callbackEnvelope
  poly_env

theorem botOutput_env :
    PolyEnv (fun n => SourceOriginalBOTCanonicalListMapper.outputEnvelope B n
      (BooleanListMapper.outEnv S D n)) := by
  have hi := botInput_env S D
  have hc := botCallback_env S D B
  unfold SourceOriginalBOTCanonicalListMapper.outputEnvelope
  poly_env

theorem botFramed_env :
    PolyEnv (fun n => SourceOriginalBOTCanonicalListMapper.framedEnvelope B n
      (BooleanListMapper.outEnv S D n)) := by
  have ho := botOutput_env S D B
  unfold SourceOriginalBOTCanonicalListMapper.framedEnvelope
  poly_env

theorem botFramedTime_env :
    PolyEnv (fun n => SourceOriginalBOTCanonicalListMapper.framedTimeEnvelope B n
      (BooleanListMapper.outEnv S D n)) := by
  have ho := botOutput_env S D B
  have hc := botCallback_env S D B
  unfold SourceOriginalBOTCanonicalListMapper.framedTimeEnvelope
  poly_env

theorem botItem_env :
    PolyEnv (fun n => SourceOriginalBOTCanonicalListMapper.itemEnvelope B n
      (BooleanListMapper.outEnv S D n)) := by
  have hi := botInput_env S D
  have hf := botFramed_env S D B
  have ht := botFramedTime_env S D B
  unfold SourceOriginalBOTCanonicalListMapper.itemEnvelope
  simp only []
  poly_env

/-! ## Admitted packetizer envelopes at digit cap `W c` -/

theorem branchLimit_env :
    PolyEnv (fun n => (8*S.density+3)*n*(n.size+1)) := by
  poly_env

theorem packetItem_env (c : ℕ) :
    PolyEnv (fun n => SourceOriginalListPacketizer.itemEnvelope n (W c n)
      ((8*S.density+3)*n*(n.size+1))) := by
  have hW := W_env c
  have hb := branchLimit_env S
  unfold SourceOriginalListPacketizer.itemEnvelope SourceOriginalListPacketizer.framingEnvelope
    SourceOriginalListPacketizer.packetLimit
  poly_env

#print axioms PolyEnv.comp
#print axioms dinurItem_env
#print axioms boolItem_env
#print axioms botItem_env
#print axioms packetItem_env

end EthInapproximability.CurrentPaper.SourceGenericComposite.PolyEnvelope
