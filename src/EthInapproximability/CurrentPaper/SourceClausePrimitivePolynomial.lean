import EthInapproximability.CurrentPaper.SourceClauseCallbackPolynomial

/-!
Primitive-clock estimates for the fixed-arity clause callback.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCallbackPrimitivePolynomial

open scoped Classical
open SourceClauseCallback SourceClauseCallbackPolynomial

theorem costPrefix_le {M : ℕ} (sizes : Fin M → ℕ)
    (B : ℕ) (hB : ∀ i, sizes i ≤ B) (m : ℕ) :
    SourceClauseFixedBatch.costPrefix sizes m ≤ m * (B + 1) := by
  induction m with
  | zero => simp [SourceClauseFixedBatch.costPrefix]
  | succ m ih =>
      rw [SourceClauseFixedBatch.costPrefix]
      split_ifs with h
      · have hs := hB ⟨m, h⟩
        nlinarith
      · nlinarith

def fixedSizeBound (q : ℕ) : ℕ :=
  8 + 2 ^ q + SourceClauseCallback.width q + q

theorem unit_sizes_le {q : ℕ} (k : Fin (2 ^ q))
    (ell : ℕ) (hell : ell ≤ q + 1) (i : Fin 6) :
    SourceClauseRowWriterOperands.unitSizes 2 q k.val
      (SourceClauseCallback.width q) ell i ≤ fixedSizeBound q := by
  have hpow : 0 < 2 ^ q := pow_pos (by decide) _
  have hk := k.isLt
  fin_cases i <;>
    simp [SourceClauseRowWriterOperands.unitSizes,
      fixedSizeBound, SourceClauseCallback.width] <;>
    omega

theorem gate_sizes_le {q : ℕ} (k : Fin (2 ^ q))
    (s t : ℕ) (hs : s ≤ 1) (ht : t ≤ q + 1) (i : Fin 8) :
    SourceClauseRowWriterOperands.gateSizes 2 q k.val s t
      (SourceClauseCallback.width q) i ≤ fixedSizeBound q := by
  have hpow : 0 < 2 ^ q := pow_pos (by decide) _
  have hk := k.isLt
  fin_cases i <;>
    simp [SourceClauseRowWriterOperands.gateSizes,
      fixedSizeBound, SourceClauseCallback.width] <;>
    omega

theorem unit_stage_le {q : ℕ} (k : Fin (2 ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    SourceClauseRowWriterUnitReady.stageCost q n r 2 k.val
      (SourceClauseCallback.width q) ell ≤
      4 * H + 6 * (fixedSizeBound q + 1) + 16 := by
  have hc := costPrefix_le
    (SourceClauseRowWriterOperands.unitSizes 2 q k.val
      (SourceClauseCallback.width q) ell)
    (fixedSizeBound q) (unit_sizes_le k ell hell) 6
  dsimp [SourceClauseRowWriterUnitReady.stageCost] at *
  omega

theorem gate_stage_le {q : ℕ} (j : Fin q) (k : Fin (2 ^ q))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H s t : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hrow : (row (.inl (j, 1))).length ≤ H)
    (hs : s ≤ 1) (ht : t ≤ q + 1) :
    SourceClauseRowWriterGateRun.stageCost j row n r 2 k.val s t
      (SourceClauseCallback.width q) ≤
      6 * H + 8 * (fixedSizeBound q + 1) + 20 := by
  have hc := costPrefix_le
    (SourceClauseRowWriterOperands.gateSizes 2 q k.val s t
      (SourceClauseCallback.width q))
    (fixedSizeBound q) (gate_sizes_le k s t hs ht) 8
  dsimp [SourceClauseRowWriterGateRun.stageCost] at *
  omega

def slotCoefficient (q : ℕ) : ℕ := 5 + 2 * (2 ^ q)

theorem slot_le_linear {q : ℕ} (k : Fin (2 ^ q))
    (n r H : ℕ) (hn : n ≤ H) (hr : r ≤ H) :
    SourceClauseRowSlotAddress.slot n r 2 q k.val ≤
      slotCoefficient q * (H + 1) := by
  have hpow : 0 < 2 ^ q := pow_pos (by decide) _
  have h₁ := Nat.mul_le_mul_left 5 hn
  have h₂ := Nat.mul_le_mul_right (2 ^ q) hr
  have hk := k.isLt
  dsimp [SourceClauseRowSlotAddress.slot, slotCoefficient]
  nlinarith

def addressCoefficient (q : ℕ) : ℕ :=
  slotCoefficient q * SourceClauseCallback.width q + q + 3

theorem unit_address_le_linear {q : ℕ} (k : Fin (2 ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    SourceClauseRowUnitAddress.address n r 2 q k.val
      (SourceClauseCallback.width q) ell ≤
      addressCoefficient q * (H + 1) := by
  have hs := slot_le_linear k n r H hn hr
  have hmul := Nat.mul_le_mul_right
    (SourceClauseCallback.width q) hs
  have hn₂ := Nat.mul_le_mul_right 2 hn
  dsimp [SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue,
    SourceClauseRowUnitAddress.offsetValue, addressCoefficient]
  nlinarith

def slotCostCoefficient (q : ℕ) : ℕ := 40 + 4 * (2 ^ q)

theorem slot_cost_le_linear {q : ℕ} (k : Fin (2 ^ q))
    (n r H : ℕ) (hn : n ≤ H) (hr : r ≤ H) :
    SourceClauseRowSlotAddress.cost n r 2 q k.val ≤
      slotCostCoefficient q * (H + 1) := by
  have hpow : 0 < 2 ^ q := pow_pos (by decide) _
  have hmul := Nat.mul_le_mul_right (2 ^ q) hr
  have hk := k.isLt
  dsimp [SourceClauseRowSlotAddress.cost,
    SourceClauseRowSlotAddress.firstSize,
    MatrixAddressMachine.exactTime, slotCostCoefficient]
  nlinarith

theorem emitTime_le_variables (c : EncodedCNF.Clause) :
    SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) ≤
      c.first.variable + c.second.variable + c.third.variable + 6 := by
  have h₀ := UnaryBinaryEncoding.bits_length_le c.first.variable
  have h₁ := UnaryBinaryEncoding.bits_length_le c.second.variable
  have h₂ := UnaryBinaryEncoding.bits_length_le c.third.variable
  simp only [SourceLiteralWriter.emitTime, SourceLiteralWriter.words]
  simp
  omega

noncomputable def unitAddressCostCoefficient (q : ℕ) : ℕ :=
  slotCostCoefficient q +
    8 * slotCoefficient q +
    4 * slotCoefficient q * SourceClauseCallback.width q +
    10 * q + 100 +
    UnaryBinaryEncoding.coefficient * (addressCoefficient q + 1) ^ 2

theorem unit_address_cost_le_quadratic {q : ℕ} (k : Fin (2 ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    SourceClauseRowUnitAddress.cost n r 2 q k.val
      (SourceClauseCallback.width q) ell ≤
      unitAddressCostCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let s := SourceClauseRowUnitAddress.slotValue n r 2 q k.val
  let c := SourceClauseRowUnitAddress.offsetValue n 2 ell
  let p := SourceClauseRowUnitAddress.address n r 2 q k.val
    (SourceClauseCallback.width q) ell
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hMsq : M ≤ M ^ 2 := by nlinarith
  have hs : s ≤ slotCoefficient q * M := by
    simpa only [s, M, SourceClauseRowUnitAddress.slotValue] using
      slot_le_linear k n r H hn hr
  have hc : c ≤ (q + 3) * M := by
    dsimp [c, SourceClauseRowUnitAddress.offsetValue, M]
    nlinarith
  have hp : p ≤ addressCoefficient q * M := by
    simpa only [p, M] using unit_address_le_linear k n r H ell hn hr hell
  have hp₁ : p + 1 ≤ (addressCoefficient q + 1) * M := by
    nlinarith
  have hp₂ : (p + 1) ^ 2 ≤
      (addressCoefficient q + 1) ^ 2 * M ^ 2 := by
    nlinarith [Nat.mul_le_mul hp₁ hp₁]
  have hb := slot_cost_le_linear k n r H hn hr
  have hcoef := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hp₂
  have hsW := Nat.mul_le_mul_right (SourceClauseCallback.width q) hs
  have hlinear := Nat.mul_le_mul_left
    (slotCostCoefficient q + 8 * slotCoefficient q +
      4 * slotCoefficient q * SourceClauseCallback.width q +
      10 * q + 100) hMsq
  dsimp [SourceClauseRowUnitAddress.cost,
    MatrixAddressMachine.exactTime, unitAddressCostCoefficient,
    M, s, c, p] at *
  nlinarith

noncomputable def unitMachineCostCoefficient (q : ℕ) : ℕ :=
  unitAddressCostCoefficient q + 7 * addressCoefficient q + 20

theorem unit_machine_cost_le_quadratic {q : ℕ} (k : Fin (2 ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    SourceClauseRowUnitMachine.cost n r 2 q k.val
      (SourceClauseCallback.width q) ell ≤
      unitMachineCostCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let p := SourceClauseRowUnitMachine.p n r 2 q k.val
    (SourceClauseCallback.width q) ell
  have hM : M ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hp : p ≤ addressCoefficient q * M := by
    simpa only [p, SourceClauseRowUnitMachine.p, M] using
      unit_address_le_linear k n r H ell hn hr hell
  have hbits := UnaryBinaryEncoding.bits_length_le p
  have haddr := unit_address_cost_le_quadratic k n r H ell hn hr hell
  have hlin := Nat.mul_le_mul_left (7 * addressCoefficient q + 20) hM
  dsimp [SourceClauseRowUnitMachine.cost,
    unitMachineCostCoefficient, M, p] at *
  nlinarith

noncomputable def unitPreCoefficient (q : ℕ) : ℕ :=
  unitMachineCostCoefficient q +
    6 * (fixedSizeBound q + 1) + 21

theorem unit_pre_cost_le_quadratic {q : ℕ} (k : Fin (2 ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    unitPreCost n r k ell ≤ unitPreCoefficient q * (H + 1) ^ 2 := by
  have hM : H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hs := unit_stage_le k n r H ell hn hr hell
  have hm := unit_machine_cost_le_quadratic k n r H ell hn hr hell
  have hlin := Nat.mul_le_mul_left
    (6 * (fixedSizeBound q + 1) + 21) hM
  dsimp [unitPreCost, unitPreCoefficient] at *
  nlinarith

theorem three_emitTime_le (p : ℕ) (l : EncodedCNF.Literal) :
    SourceLiteralWriter.emitTime
        (SourceLiteralWriter.words (SourceClauseGatePrepare.firstClause p l)) +
      SourceLiteralWriter.emitTime
        (SourceLiteralWriter.words (SourceClauseGatePrepare.secondClause p)) +
      SourceLiteralWriter.emitTime
        (SourceLiteralWriter.words (SourceClauseGatePrepare.thirdClause p l)) ≤
      7 * p + 2 * l.variable + 23 := by
  have h₀ := emitTime_le_variables (SourceClauseGatePrepare.firstClause p l)
  have h₁ := emitTime_le_variables (SourceClauseGatePrepare.secondClause p)
  have h₂ := emitTime_le_variables (SourceClauseGatePrepare.thirdClause p l)
  simp only [SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    SourceClauseEncoding.positive, SourceClauseEncoding.negative,
    SourceClauseEncoding.negate] at h₀ h₁ h₂ ⊢
  nlinarith

noncomputable def gateSlotCostCoefficient (q : ℕ) : ℕ :=
  30 * addressCoefficient q +
    20 * slotCoefficient q * SourceClauseCallback.width q +
    20 * slotCoefficient q + 20 * q + 200 +
    UnaryBinaryEncoding.coefficient * (addressCoefficient q + 1) ^ 2

theorem gate_slot_cost_le_quadratic (q n H t j : ℕ)
    (l : EncodedCNF.Literal)
    (hn : n ≤ H) (ht : t ≤ q + 1)
    (hj : j ≤ slotCoefficient q * (H + 1))
    (hl : l.variable ≤ 3 * (H + 1))
    (hp : j * SourceClauseCallback.width q + (n * 2 + t) ≤
      addressCoefficient q * (H + 1)) :
    SourceClauseGateSlotAddress.cost n 2 t j
      (SourceClauseCallback.width q) l ≤
      gateSlotCostCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let c := n * 2 + t
  let p := j * SourceClauseCallback.width q + c
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hMsq : M ≤ M ^ 2 := by nlinarith
  have hc : c ≤ (q + 3) * M := by
    dsimp [c, M]
    nlinarith
  have hjW := Nat.mul_le_mul_right (SourceClauseCallback.width q) hj
  have hp₁ : p + 1 ≤ (addressCoefficient q + 1) * M := by
    dsimp [p, c, M] at *
    nlinarith
  have hp₂ : (p + 1) ^ 2 ≤
      (addressCoefficient q + 1) ^ 2 * M ^ 2 := by
    nlinarith [Nat.mul_le_mul hp₁ hp₁]
  have hcoef := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hp₂
  have hb₀ := UnaryBinaryEncoding.bits_length_le p
  have hb₁ := UnaryBinaryEncoding.bits_length_le (p + 1)
  have hbl := UnaryBinaryEncoding.bits_length_le l.variable
  have hemit := three_emitTime_le p l
  have hlinear := Nat.mul_le_mul_left
    (30 * addressCoefficient q +
      20 * slotCoefficient q * SourceClauseCallback.width q +
      20 * slotCoefficient q + 20 * q + 200) hMsq
  dsimp [SourceClauseGateSlotAddress.cost,
    MatrixAddressMachine.exactTime, gateSlotCostCoefficient,
    M, c, p] at *
  nlinarith

noncomputable def rowGateCostCoefficient (q : ℕ) : ℕ :=
  gateSlotCostCoefficient q + 4 * UnaryBinaryEncoding.coefficient + 40

theorem row_gate_cost_le_quadratic {q : ℕ} (k : Fin (2 ^ q))
    (n r H v s t : ℕ) (sign : Bool)
    (hn : n ≤ H) (hr : r ≤ H) (hv : v ≤ H)
    (hs : s ≤ 1) (ht : t ≤ q + 1) :
    SourceClauseRowGate.cost v 2 s n t
      (SourceClauseRowSlotAddress.slot n r 2 q k.val)
      (SourceClauseCallback.width q) sign ≤
      rowGateCostCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let j := SourceClauseRowSlotAddress.slot n r 2 q k.val
  let l : EncodedCNF.Literal := ⟨v * 2 + s, sign⟩
  have hM : M ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hj : j ≤ slotCoefficient q * M := by
    simpa only [j, M] using slot_le_linear k n r H hn hr
  have hl : l.variable ≤ 3 * M := by
    dsimp [l, M]
    omega
  have hp : j * SourceClauseCallback.width q + (n * 2 + t) ≤
      addressCoefficient q * M := by
    simpa only [j, M, SourceClauseRowUnitAddress.address,
      SourceClauseRowUnitAddress.slotValue,
      SourceClauseRowUnitAddress.offsetValue] using
      unit_address_le_linear k n r H t hn hr ht
  have hslot := gate_slot_cost_le_quadratic q n H t j l hn ht hj hl hp
  have hv₂ : v * 2 + s + 1 ≤ 2 * M := by dsimp [M]; omega
  have hvpow : (v * 2 + s + 1) ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith [Nat.mul_le_mul hv₂ hv₂]
  have hcoef := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hvpow
  have hbits := UnaryBinaryEncoding.bits_length_le (v * 2 + s)
  have hlinear := Nat.mul_le_mul_left 40 hM
  dsimp [SourceClauseRowGate.cost, rowGateCostCoefficient,
    MatrixAddressMachine.exactTime, M, j, l] at *
  nlinarith

noncomputable def indexedGateCostCoefficient (q : ℕ) : ℕ :=
  rowGateCostCoefficient q + slotCostCoefficient q +
    2 * slotCoefficient q + 10

theorem indexed_gate_cost_le_quadratic {q : ℕ} (k : Fin (2 ^ q))
    (n r H v s t : ℕ) (sign : Bool)
    (hn : n ≤ H) (hr : r ≤ H) (hv : v ≤ H)
    (hs : s ≤ 1) (ht : t ≤ q + 1) :
    SourceClauseRowIndexedGate.cost q n r 2 k.val v s t
      (SourceClauseCallback.width q) sign ≤
      indexedGateCostCoefficient q * (H + 1) ^ 2 := by
  have hM : H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hslot := slot_le_linear k n r H hn hr
  have hslotCost := slot_cost_le_linear k n r H hn hr
  have hgate := row_gate_cost_le_quadratic k n r H v s t sign
    hn hr hv hs ht
  have hlin := Nat.mul_le_mul_left
    (slotCostCoefficient q + 2 * slotCoefficient q + 10) hM
  dsimp [SourceClauseRowIndexedGate.cost,
    indexedGateCostCoefficient] at *
  nlinarith

noncomputable def gatePreCoefficient (q : ℕ) : ℕ :=
  indexedGateCostCoefficient q +
    8 * (fixedSizeBound q + 1) + 27

theorem gate_pre_cost_le_quadratic {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (2 ^ q)) (s t : ℕ) (sign : Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : (row (.inl (j, 1))).length ≤ H)
    (hs : s ≤ 1) (ht : t ≤ q + 1) :
    gatePreCost j row n r k s t sign ≤
      gatePreCoefficient q * (H + 1) ^ 2 := by
  have hM : H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hstage := gate_stage_le j k row n r H s t
    hn hr hrow hs ht
  have hgate := indexed_gate_cost_le_quadratic k n r H
    (row (.inl (j, 1))).length s t sign hn hr hrow hs ht
  have hlin := Nat.mul_le_mul_left
    (8 * (fixedSizeBound q + 1) + 27) hM
  dsimp [gatePreCost, gatePreCoefficient] at *
  nlinarith

end EthInapproximability.CurrentPaper.SourceClauseCallbackPrimitivePolynomial
