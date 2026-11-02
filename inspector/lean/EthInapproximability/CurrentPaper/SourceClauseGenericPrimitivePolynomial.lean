import EthInapproximability.CurrentPaper.SourceClauseGenericCallbackPolynomial
import EthInapproximability.CurrentPaper.SourceClausePrimitivePolynomial

namespace EthInapproximability.CurrentPaper.SourceClauseGenericPrimitivePolynomial

open scoped Classical
open SourceClauseGenericCallback
open SourceClauseGenericCallbackPolynomial
open SourceClauseCallbackPrimitivePolynomial (costPrefix_le emitTime_le_variables three_emitTime_le)

set_option maxHeartbeats 1000000

def fixedSizeBound (a q : ℕ) : ℕ :=
  8 + a + a * a + a ^ q + SourceClauseGenericCallback.width a q + q

theorem unit_sizes_le {a q : ℕ} (k : Fin (a ^ q))
    (ell : ℕ) (hell : ell ≤ q + 1) (i : Fin 6) :
    SourceClauseRowWriterOperands.unitSizes a q k.val
      (SourceClauseGenericCallback.width a q) ell i ≤ fixedSizeBound a q := by
  have hk := k.isLt
  have hpow : 0 < a ^ q := by omega
  fin_cases i <;>
    simp [SourceClauseRowWriterOperands.unitSizes,
      fixedSizeBound, SourceClauseGenericCallback.width] <;>
    omega

theorem gate_sizes_le {a q : ℕ} (k : Fin (a ^ q))
    (s t : ℕ) (hs : s < a) (ht : t ≤ q + 1) (i : Fin 8) :
    SourceClauseRowWriterOperands.gateSizes a q k.val s t
      (SourceClauseGenericCallback.width a q) i ≤ fixedSizeBound a q := by
  have hk := k.isLt
  have hpow : 0 < a ^ q := by omega
  fin_cases i <;>
    simp [SourceClauseRowWriterOperands.gateSizes,
      fixedSizeBound, SourceClauseGenericCallback.width] <;>
    omega

theorem unit_stage_le {a q : ℕ} (k : Fin (a ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    SourceClauseRowWriterUnitReady.stageCost q n r a k.val
      (SourceClauseGenericCallback.width a q) ell ≤
      4 * H + 6 * (fixedSizeBound a q + 1) + 16 := by
  have hc := costPrefix_le
    (SourceClauseRowWriterOperands.unitSizes a q k.val
      (SourceClauseGenericCallback.width a q) ell)
    (fixedSizeBound a q) (unit_sizes_le k ell hell) 6
  dsimp [SourceClauseRowWriterUnitReady.stageCost] at *
  omega

theorem gate_stage_le {a q : ℕ} (j : Fin q) (k : Fin (a ^ q))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H s t : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hrow : (row (.inl (j, 1))).length ≤ H)
    (hs : s < a) (ht : t ≤ q + 1) :
    SourceClauseRowWriterGateRun.stageCost j row n r a k.val s t
      (SourceClauseGenericCallback.width a q) ≤
      6 * H + 8 * (fixedSizeBound a q + 1) + 20 := by
  have hc := costPrefix_le
    (SourceClauseRowWriterOperands.gateSizes a q k.val s t
      (SourceClauseGenericCallback.width a q))
    (fixedSizeBound a q) (gate_sizes_le k s t hs ht) 8
  dsimp [SourceClauseRowWriterGateRun.stageCost] at *
  omega

def slotCoefficient (a q : ℕ) : ℕ := 5 + a * a + 2 * (a ^ q)

theorem slot_le_linear {a q : ℕ} (k : Fin (a ^ q))
    (n r H : ℕ) (hn : n ≤ H) (hr : r ≤ H) :
    SourceClauseRowSlotAddress.slot n r a q k.val ≤
      slotCoefficient a q * (H + 1) := by
  have hk := k.isLt
  have hpow : 0 < a ^ q := by omega
  have h₁ := Nat.mul_le_mul_left 5 hn
  have h₂ := Nat.mul_le_mul_right (a ^ q) hr
  dsimp [SourceClauseRowSlotAddress.slot, slotCoefficient]
  nlinarith

def addressCoefficient (a q : ℕ) : ℕ :=
  slotCoefficient a q * SourceClauseGenericCallback.width a q + a + q + 3

theorem unit_address_le_linear {a q : ℕ} (k : Fin (a ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    SourceClauseRowUnitAddress.address n r a q k.val
      (SourceClauseGenericCallback.width a q) ell ≤
      addressCoefficient a q * (H + 1) := by
  have hs := slot_le_linear k n r H hn hr
  have hmul := Nat.mul_le_mul_right
    (SourceClauseGenericCallback.width a q) hs
  have hn₂ := Nat.mul_le_mul_right a hn
  dsimp [SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue,
    SourceClauseRowUnitAddress.offsetValue, addressCoefficient]
  nlinarith

def slotCostCoefficient (a q : ℕ) : ℕ := 40 + 10 * a * a + 4 * (a ^ q)

theorem slot_cost_le_linear {a q : ℕ} (k : Fin (a ^ q))
    (n r H : ℕ) (hn : n ≤ H) (hr : r ≤ H) :
    SourceClauseRowSlotAddress.cost n r a q k.val ≤
      slotCostCoefficient a q * (H + 1) := by
  have hk := k.isLt
  have hpow : 0 < a ^ q := by omega
  have hmul := Nat.mul_le_mul_right (a ^ q) hr
  dsimp [SourceClauseRowSlotAddress.cost,
    SourceClauseRowSlotAddress.firstSize,
    MatrixAddressMachine.exactTime, slotCostCoefficient]
  nlinarith

noncomputable def unitAddressCostCoefficient (a q : ℕ) : ℕ :=
  slotCostCoefficient a q +
    8 * slotCoefficient a q +
    4 * slotCoefficient a q * SourceClauseGenericCallback.width a q +
    10 * (a + q + 1) ^ 2 + 100 +
    UnaryBinaryEncoding.coefficient * (addressCoefficient a q + 1) ^ 2

theorem unit_address_cost_le_quadratic {a q : ℕ} (k : Fin (a ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    SourceClauseRowUnitAddress.cost n r a q k.val
      (SourceClauseGenericCallback.width a q) ell ≤
      unitAddressCostCoefficient a q * (H + 1) ^ 2 := by
  let M := H + 1
  let s := SourceClauseRowUnitAddress.slotValue n r a q k.val
  let c := SourceClauseRowUnitAddress.offsetValue n a ell
  let p := SourceClauseRowUnitAddress.address n r a q k.val
    (SourceClauseGenericCallback.width a q) ell
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hMsq : M ≤ M ^ 2 := by nlinarith
  have hs : s ≤ slotCoefficient a q * M := by
    simpa only [s, M, SourceClauseRowUnitAddress.slotValue] using
      slot_le_linear k n r H hn hr
  have hc : c ≤ (a + q + 3) * M := by
    dsimp [c, SourceClauseRowUnitAddress.offsetValue, M]
    nlinarith
  have hp : p ≤ addressCoefficient a q * M := by
    simpa only [p, M] using unit_address_le_linear k n r H ell hn hr hell
  have hp₁ : p + 1 ≤ (addressCoefficient a q + 1) * M := by
    nlinarith
  have hp₂ : (p + 1) ^ 2 ≤
      (addressCoefficient a q + 1) ^ 2 * M ^ 2 := by
    nlinarith [Nat.mul_le_mul hp₁ hp₁]
  have hb := slot_cost_le_linear k n r H hn hr
  have hcoef := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hp₂
  have hsW := Nat.mul_le_mul_right (SourceClauseGenericCallback.width a q) hs
  have hlinear := Nat.mul_le_mul_left
    (slotCostCoefficient a q + 8 * slotCoefficient a q +
      4 * slotCoefficient a q * SourceClauseGenericCallback.width a q +
      10 * (a + q + 1) ^ 2 + 100) hMsq
  have hnA := Nat.mul_le_mul_right a hn
  have hbudget : 6 * a + 6 * q + 50 ≤
      10 * (a + q + 1) ^ 2 + 100 := by nlinarith
  have hbudgetM := Nat.mul_le_mul_right M hbudget
  have hEll : ell ≤ (q + 1) * M := by dsimp [M]; nlinarith
  dsimp [SourceClauseRowUnitAddress.cost,
    MatrixAddressMachine.exactTime, unitAddressCostCoefficient,
    M, s, c, p] at *
  nlinarith

noncomputable def unitMachineCostCoefficient (a q : ℕ) : ℕ :=
  unitAddressCostCoefficient a q + 7 * addressCoefficient a q + 20

theorem unit_machine_cost_le_quadratic {a q : ℕ} (k : Fin (a ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
   SourceClauseRowUnitMachine.cost n r a q k.val
      (SourceClauseGenericCallback.width a q) ell ≤
      unitMachineCostCoefficient a q * (H + 1) ^ 2 := by
  let M := H + 1
  let p := SourceClauseRowUnitMachine.p n r a q k.val
    (SourceClauseGenericCallback.width a q) ell
  have hM : M ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hp : p ≤ addressCoefficient a q * M := by
    simpa only [p, SourceClauseRowUnitMachine.p, M] using
      unit_address_le_linear k n r H ell hn hr hell
  have hbits := UnaryBinaryEncoding.bits_length_le p
  have haddr := unit_address_cost_le_quadratic k n r H ell hn hr hell
  have hlin := Nat.mul_le_mul_left (7 * addressCoefficient a q + 20) hM
  dsimp [SourceClauseRowUnitMachine.cost,
    unitMachineCostCoefficient, M, p] at *
  nlinarith

noncomputable def unitPreCoefficient (a q : ℕ) : ℕ :=
  unitMachineCostCoefficient a q +
    6 * (fixedSizeBound a q + 1) + 21

theorem unit_pre_cost_le_quadratic {a q : ℕ} (k : Fin (a ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    unitPreCost n r k ell ≤ unitPreCoefficient a q * (H + 1) ^ 2 := by
  have hM : H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hs := unit_stage_le k n r H ell hn hr hell
  have hm := unit_machine_cost_le_quadratic k n r H ell hn hr hell
  have hlin := Nat.mul_le_mul_left
    (6 * (fixedSizeBound a q + 1) + 21) hM
  dsimp [unitPreCost, unitPreCoefficient] at *
  nlinarith

noncomputable def gateSlotCostCoefficient (a q : ℕ) : ℕ :=
  30 * addressCoefficient a q +
    20 * slotCoefficient a q * SourceClauseGenericCallback.width a q +
    20 * slotCoefficient a q + 100 * (a + q + 1) ^ 2 + 200 +
    UnaryBinaryEncoding.coefficient * (addressCoefficient a q + 1) ^ 2

theorem gate_slot_cost_le_quadratic (a q n H t j : ℕ)
    (l : EncodedCNF.Literal)
    (hn : n ≤ H) (ht : t ≤ q + 1)
    (hj : j ≤ slotCoefficient a q * (H + 1))
    (hl : l.variable ≤ (a + 1) * (H + 1))
    (hp : j * SourceClauseGenericCallback.width a q + (n * a + t) ≤
      addressCoefficient a q * (H + 1)) :
    SourceClauseGateSlotAddress.cost n a t j
      (SourceClauseGenericCallback.width a q) l ≤
      gateSlotCostCoefficient a q * (H + 1) ^ 2 := by
  let M := H + 1
  let c := n * a + t
  let p := j * SourceClauseGenericCallback.width a q + c
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hMsq : M ≤ M ^ 2 := by nlinarith
  have hc : c ≤ (a + q + 3) * M := by
    dsimp [c, M]
    nlinarith
  have hjW := Nat.mul_le_mul_right (SourceClauseGenericCallback.width a q) hj
  have hp₁ : p + 1 ≤ (addressCoefficient a q + 1) * M := by
    dsimp [p, c, M] at *
    nlinarith
  have hp₂ : (p + 1) ^ 2 ≤
      (addressCoefficient a q + 1) ^ 2 * M ^ 2 := by
    nlinarith [Nat.mul_le_mul hp₁ hp₁]
  have hcoef := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hp₂
  have hb₀ := UnaryBinaryEncoding.bits_length_le p
  have hb₁ := UnaryBinaryEncoding.bits_length_le (p + 1)
  have hbl := UnaryBinaryEncoding.bits_length_le l.variable
  have hemit := three_emitTime_le p l
  have hlinear := Nat.mul_le_mul_left
    (30 * addressCoefficient a q +
      20 * slotCoefficient a q * SourceClauseGenericCallback.width a q +
      20 * slotCoefficient a q + 100 * (a + q + 1) ^ 2 + 200) hMsq
  have hnA := Nat.mul_le_mul_right a hn
  have hbudget : 6 * a + 6 * q + 50 ≤
      100 * (a + q + 1) ^ 2 + 200 := by nlinarith
  have hbudgetM := Nat.mul_le_mul_right M hbudget
  dsimp [SourceClauseGateSlotAddress.cost,
    MatrixAddressMachine.exactTime, gateSlotCostCoefficient,
    M, c, p] at *
  nlinarith

noncomputable def rowGateCostCoefficient (a q : ℕ) : ℕ :=
  gateSlotCostCoefficient a q + (a + 1) ^ 2 * UnaryBinaryEncoding.coefficient +
    40 * (a + 1) ^ 2

theorem row_gate_cost_le_quadratic {a q : ℕ} (k : Fin (a ^ q))
    (n r H v s t : ℕ) (sign : Bool)
    (hn : n ≤ H) (hr : r ≤ H) (hv : v ≤ H)
    (hs : s < a) (ht : t ≤ q + 1) :
    SourceClauseRowGate.cost v a s n t
      (SourceClauseRowSlotAddress.slot n r a q k.val)
      (SourceClauseGenericCallback.width a q) sign ≤
      rowGateCostCoefficient a q * (H + 1) ^ 2 := by
  let M := H + 1
  let j := SourceClauseRowSlotAddress.slot n r a q k.val
  let l : EncodedCNF.Literal := ⟨v * a + s, sign⟩
  have hM : M ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hj : j ≤ slotCoefficient a q * M := by
    simpa only [j, M] using slot_le_linear k n r H hn hr
  have hl : l.variable ≤ (a + 1) * M := by
    dsimp [l, M]
    nlinarith [Nat.mul_le_mul_right a hv]
  have hp : j * SourceClauseGenericCallback.width a q + (n * a + t) ≤
      addressCoefficient a q * M := by
   simpa only [j, M, SourceClauseRowUnitAddress.address,
      SourceClauseRowUnitAddress.slotValue,
      SourceClauseRowUnitAddress.offsetValue] using
      unit_address_le_linear k n r H t hn hr ht
  have hslot := gate_slot_cost_le_quadratic a q n H t j l hn ht hj hl hp
  have hv₂ : v * a + s + 1 ≤ (a + 1) * M := by
    dsimp [M]
    nlinarith [Nat.mul_le_mul_right a hv]
  have hvpow : (v * a + s + 1) ^ 2 ≤ (a + 1) ^ 2 * M ^ 2 := by
    nlinarith [Nat.mul_le_mul hv₂ hv₂]
  have hcoef := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hvpow
  have hbits := UnaryBinaryEncoding.bits_length_le (v * a + s)
  have hlinear := Nat.mul_le_mul_left (40 * (a + 1) ^ 2) hM
  have hvA := Nat.mul_le_mul_right a hv
  dsimp [SourceClauseRowGate.cost, rowGateCostCoefficient,
    MatrixAddressMachine.exactTime, M, j, l] at *
  nlinarith

noncomputable def indexedGateCostCoefficient (a q : ℕ) : ℕ :=
  rowGateCostCoefficient a q + slotCostCoefficient a q +
    2 * slotCoefficient a q + 10

theorem indexed_gate_cost_le_quadratic {a q : ℕ} (k : Fin (a ^ q))
    (n r H v s t : ℕ) (sign : Bool)
    (hn : n ≤ H) (hr : r ≤ H) (hv : v ≤ H)
    (hs : s < a) (ht : t ≤ q + 1) :
    SourceClauseRowIndexedGate.cost q n r a k.val v s t
      (SourceClauseGenericCallback.width a q) sign ≤
      indexedGateCostCoefficient a q * (H + 1) ^ 2 := by
  have hM : H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hslot := slot_le_linear k n r H hn hr
  have hslotCost := slot_cost_le_linear k n r H hn hr
  have hgate := row_gate_cost_le_quadratic k n r H v s t sign
    hn hr hv hs ht
  have hlin := Nat.mul_le_mul_left
    (slotCostCoefficient a q + 2 * slotCoefficient a q + 10) hM
  dsimp [SourceClauseRowIndexedGate.cost,
    indexedGateCostCoefficient] at *
  nlinarith

noncomputable def gatePreCoefficient (a q : ℕ) : ℕ :=
  indexedGateCostCoefficient a q +
    8 * (fixedSizeBound a q + 1) + 27

theorem gate_pre_cost_le_quadratic {a q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q)) (s t : ℕ) (sign : Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : (row (.inl (j, 1))).length ≤ H)
    (hs : s < a) (ht : t ≤ q + 1) :
    gatePreCost j row n r k s t sign ≤
      gatePreCoefficient a q * (H + 1) ^ 2 := by
  have hM : H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hstage := gate_stage_le j k row n r H s t
    hn hr hrow hs ht
  have hgate := indexed_gate_cost_le_quadratic k n r H
    (row (.inl (j, 1))).length s t sign hn hr hrow hs ht
  have hlin := Nat.mul_le_mul_left
    (8 * (fixedSizeBound a q + 1) + 27) hM
  dsimp [gatePreCost, gatePreCoefficient] at *
  nlinarith

end EthInapproximability.CurrentPaper.SourceClauseGenericPrimitivePolynomial
