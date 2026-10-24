import EthInapproximability.CurrentPaper.SourceGenericConverterRun

/-!
# Size facts for the converter clock (unit 1, segment 5, part 1)

Paper B, locked v8 Section 6; CP-SOURCE-EFFECTIVE, arbitrary fixed `a`.
Fixed-`(a,q)` polynomial bounds, in the raw input length, of every quantity
that appears in the explicit converter clock: the word envelope, the generic
variable count, emitted-clause count and payload length, the word bound `H`
fed to the row suffix, and the suffix and phase clocks. All coefficients are
proof-side functions of `(a,q)` only.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Converter

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

theorem le_pow_self (X k : Nat) (hX : 0 < X) (hk : 1 ≤ k) : X ≤ X ^ k := by
  calc X = X ^ 1 := (pow_one X).symm
    _ ≤ X ^ k := Nat.pow_le_pow_right hX hk

theorem pow_mono (X i j : Nat) (hX : 0 < X) (h : i ≤ j) : X ^ i ≤ X ^ j :=
  Nat.pow_le_pow_right hX h

/-! ## Literal translation sizes -/

theorem flatten_ofFn_length_le {α : Type} {N c : Nat} (f : Fin N → List α)
    (h : ∀ i, (f i).length ≤ c) : (List.ofFn f).flatten.length ≤ N * c := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, List.flatten_cons, List.length_append]
      have h0 := h 0
      have ht := ih (fun i => f i.succ) (fun i => h i.succ)
      rw [Nat.succ_mul]
      omega

theorem tupleClause_length_le {a q : Nat} (hq : 0 < q) (k : Fin (a ^ q))
    (query : Fin q → Nat) (accept : Bool) :
    (SourceClauseRowSchedule.tupleClause hq k query accept).length ≤ q + 1 := by
  unfold SourceClauseRowSchedule.tupleClause
  split <;> simp

theorem rowChain_length_le {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hq : 0 < q) (r : Fin m) (k : Fin (a ^ q)) :
    (SourceGenericOrder.rowChain P hq r k).length ≤ 3 * q + 5 := by
  unfold SourceGenericOrder.rowChain
  rw [SourceClauseEncoding.chain_length]
  have := tupleClause_length_le hq k (fun j => (P.query r j).val)
    (P.accept r (SourceClauseRowSchedule.tuple a q k))
  omega

theorem rowChains_length_le {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hq : 0 < q) :
    (SourceGenericOrder.rowChains P hq).length ≤ m * (a ^ q * (3 * q + 5)) := by
  unfold SourceGenericOrder.rowChains
  apply flatten_ofFn_length_le
  intro r
  apply flatten_ofFn_length_le
  intro k
  exact rowChain_length_le P hq r k

theorem emitted_le {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hq : 0 < q) :
    SourceGenericOrder.sourceEmittedCount P hq ≤
      (3 * a + 2 + 8 * a * a) * n + m * (a ^ q * (3 * q + 5)) := by
  unfold SourceGenericOrder.sourceEmittedCount
  have := rowChains_length_le P hq
  omega

theorem payload_length_le {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hq : 0 < q) :
    (SourceGenericOrder.sourceReversePayload P hq).length ≤
      SourceGenericOrder.sourceEmittedCount P hq *
        (6 * SourceGenericOrder.sourceVariables P + 6) := by
  rw [SourceGenericOrder.sourceReversePayload_eq, List.length_reverse,
    SourceGenericOrder.sourceEmittedCount_eq, SourceGenericOrder.sourceVariables_eq P hq]
  exact EncodedCNF.clauseFields_length_upper _ _
    (SourceBooleanEncoding.threeCNF_valid P hq)

/-! ## Coefficients (functions of `a,q` only) -/

noncomputable def ctlC (a q : Nat) : Nat :=
  SourceCSPFirstRowController.cubicCoefficient a q
noncomputable def envC (a q : Nat) : Nat :=
  1 + BitMachineStackGrowth.perStep (SourceCSPGlobalDecisionProgram.program a q) *
      (ctlC a q + 1) +
    BitMachineStackGrowth.perStep (SourceCSPFirstRowController.bodyProgram q a) *
      (ctlC a q + 1)
def varC (a q : Nat) : Nat :=
  SourceGenericVariableUnary.vertexCoefficient a q * q +
    SourceGenericVariableUnary.rowCoefficient a q
def cntC (a q : Nat) : Nat :=
  (3 * a + 2 + 8 * a * a) * q + a ^ q * (3 * q + 5)
def payC (a q : Nat) : Nat := cntC a q * (6 * varC a q + 6)
noncomputable def hC (a q : Nat) : Nat :=
  envC a q + q + 2 + a ^ q + payC a q + cntC a q

/-! ## Bounds -/

theorem controller_parts_le (a q L : Nat) :
    SourceCSPGlobalTotalValidation.totalBound a q L + 1 ≤ (ctlC a q + 1) * (L + 1) ^ 3 ∧
    SourceCSPFirstRowController.uniformStageBound q L +
        SourceCSPFirstRowController.uniformRowBound a q L + 1 ≤
      (ctlC a q + 1) * (L + 1) ^ 3 := by
  have hc := SourceCSPFirstRowController.controllerBound_le_cubic a q L
  unfold SourceCSPFirstRowController.controllerBound at hc
  have h1 : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold ctlC
  constructor <;> nlinarith

theorem envelope_le (a q L : Nat) :
    AcceptedSource.envelope a q L ≤ envC a q * (L + 1) ^ 3 := by
  obtain ⟨h1, h2⟩ := controller_parts_le a q L
  have hL : L ≤ (L + 1) ^ 3 := (Nat.le_succ L).trans (le_pow_self _ 3 (by omega) (by norm_num))
  unfold AcceptedSource.envelope envC
  calc L + BitMachineStackGrowth.perStep (SourceCSPGlobalDecisionProgram.program a q) *
          (SourceCSPGlobalTotalValidation.totalBound a q L + 1) +
        BitMachineStackGrowth.perStep (SourceCSPFirstRowController.bodyProgram q a) *
          (SourceCSPFirstRowController.uniformStageBound q L +
            SourceCSPFirstRowController.uniformRowBound a q L + 1)
      ≤ (L + 1) ^ 3 +
          BitMachineStackGrowth.perStep (SourceCSPGlobalDecisionProgram.program a q) *
            ((ctlC a q + 1) * (L + 1) ^ 3) +
          BitMachineStackGrowth.perStep (SourceCSPFirstRowController.bodyProgram q a) *
            ((ctlC a q + 1) * (L + 1) ^ 3) := by gcongr
    _ = _ := by ring

theorem vars_le {n m a q L : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hsize : n ≤ q * m) (hmL : m ≤ L) :
    SourceGenericOrder.sourceVariables P ≤ varC a q * (L + 1) := by
  rw [SourceGenericVariableUnary.sourceVariables_affine]
  have hn : n ≤ q * (L + 1) := hsize.trans (Nat.mul_le_mul_left q (by omega))
  have hm : m ≤ L + 1 := by omega
  calc SourceGenericVariableUnary.vertexCoefficient a q * n +
        SourceGenericVariableUnary.rowCoefficient a q * m
      ≤ SourceGenericVariableUnary.vertexCoefficient a q * (q * (L + 1)) +
        SourceGenericVariableUnary.rowCoefficient a q * (L + 1) := by gcongr
    _ = varC a q * (L + 1) := by unfold varC; ring

theorem cnt_le {n m a q L : Nat} (P : SourceBooleanEncoding.CSP n m a q) (hq : 0 < q)
    (hsize : n ≤ q * m) (hmL : m ≤ L) :
    SourceGenericOrder.sourceEmittedCount P hq ≤ cntC a q * (L + 1) := by
  have he := emitted_le P hq
  have hn : n ≤ q * (L + 1) := hsize.trans (Nat.mul_le_mul_left q (by omega))
  have hm : m ≤ L + 1 := by omega
  calc SourceGenericOrder.sourceEmittedCount P hq
      ≤ (3 * a + 2 + 8 * a * a) * n + m * (a ^ q * (3 * q + 5)) := he
    _ ≤ (3 * a + 2 + 8 * a * a) * (q * (L + 1)) + (L + 1) * (a ^ q * (3 * q + 5)) := by
        gcongr
    _ = cntC a q * (L + 1) := by unfold cntC; ring

theorem payload_le {n m a q L : Nat} (P : SourceBooleanEncoding.CSP n m a q) (hq : 0 < q)
    (hsize : n ≤ q * m) (hmL : m ≤ L) :
    (SourceGenericOrder.sourceReversePayload P hq).length ≤ payC a q * (L + 1) ^ 2 := by
  have hp := payload_length_le P hq
  have hc := cnt_le P hq hsize hmL
  have hv := vars_le P hsize hmL
  have hX : 1 ≤ L + 1 := by omega
  calc (SourceGenericOrder.sourceReversePayload P hq).length
      ≤ SourceGenericOrder.sourceEmittedCount P hq *
          (6 * SourceGenericOrder.sourceVariables P + 6) := hp
    _ ≤ (cntC a q * (L + 1)) * (6 * (varC a q * (L + 1)) + 6 * (L + 1)) := by
        gcongr
        omega
    _ = payC a q * (L + 1) ^ 2 := by unfold payC; ring

#print axioms rowChains_length_le
#print axioms payload_length_le
#print axioms envelope_le
#print axioms vars_le
#print axioms cnt_le
#print axioms payload_le

end EthInapproximability.CurrentPaper.SourceGenericComposite.Converter
