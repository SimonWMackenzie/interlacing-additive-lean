import EthInapproximability.CurrentPaper.SourceClauseCallPolynomial

/-!
Payload growth for the exact fixed-arity clause block. These bounds are on
the source's actual signed binary three-CNF codec.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCallbackBlockPolynomial

open scoped Classical
open SourceClauseCallback SourceClauseCircuitClock
open SourceClauseCallbackPolynomial SourceClauseCallbackPrimitivePolynomial
open SourceClauseCallbackCallPolynomial
open SourceClauseRowSchedule
open SourceClauseEncoding EncodedCNF

theorem encodeLiteral_length_le (l : Literal) :
    (encodeLiteral l).length ≤ 2 * l.variable + 2 := by
  have h := EncodedGraph.natField_length_upper l.variable
  simp only [encodeLiteral, List.length_cons] at ⊢
  omega

theorem encodeClause_length_le (c : Clause) :
    (encodeClause c).length ≤
      2 * (c.first.variable + c.second.variable + c.third.variable) + 6 := by
  have h₀ := encodeLiteral_length_le c.first
  have h₁ := encodeLiteral_length_le c.second
  have h₂ := encodeLiteral_length_le c.third
  simp only [encodeClause, List.length_append]
  omega

theorem unit_bytes_le (v : ℕ) (sign : Bool) :
    (encodeClause (unit ⟨v, sign⟩)).length ≤ 6 * v + 6 := by
  have h := encodeClause_length_le (unit ⟨v, sign⟩)
  simp only [unit] at h ⊢
  omega

theorem gate_bytes_le (p : ℕ) (l : Literal) :
    (clauseFields (orGate p l)).length ≤
      14 * p + 4 * l.variable + 28 := by
  have h₀ := encodeClause_length_le
    (SourceClauseGatePrepare.firstClause p l)
  have h₁ := encodeClause_length_le
    (SourceClauseGatePrepare.secondClause p)
  have h₂ := encodeClause_length_le
    (SourceClauseGatePrepare.thirdClause p l)
  simp only [SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    SourceClauseEncoding.positive, SourceClauseEncoding.negative,
    SourceClauseEncoding.negate] at h₀ h₁ h₂
  simp only [orGate, clauseFields, List.length_append,
    List.length_nil, Nat.add_zero,
    SourceClauseEncoding.positive, SourceClauseEncoding.negative,
    SourceClauseEncoding.negate] at ⊢
  omega

def gateByteCoefficient (q : ℕ) : ℕ :=
  14 * addressCoefficient q + 40

def unitByteCoefficient (q : ℕ) : ℕ :=
  6 * addressCoefficient q + 6

theorem gate_bytes_le_linear (q H p : ℕ) (l : Literal)
    (hp : p ≤ addressCoefficient q * (H + 1))
    (hl : l.variable ≤ 3 * (H + 1)) :
    (clauseFields (orGate p l)).length ≤
      gateByteCoefficient q * (H + 1) := by
  have h := gate_bytes_le p l
  have hM : 1 ≤ H + 1 := by omega
  dsimp [gateByteCoefficient]
  nlinarith

theorem unit_bytes_le_linear (q H p : ℕ) (sign : Bool)
    (hp : p ≤ addressCoefficient q * (H + 1)) :
    (encodeClause (unit ⟨p, sign⟩)).length ≤
      unitByteCoefficient q * (H + 1) := by
  have h := unit_bytes_le p sign
  have hM : 1 ≤ H + 1 := by omega
  dsimp [unitByteCoefficient]
  nlinarith

theorem foldSaved_length_le {α : Type} (payload : α → List Bool)
    (as : List α) (saved : List Bool) (B : ℕ)
    (hB : ∀ a ∈ as, (payload a).length ≤ B) :
    (foldSaved payload as saved).length ≤ saved.length + as.length * B := by
  induction as generalizing saved with
  | nil => simp [foldSaved]
  | cons a as ih =>
      have ha := hB a (by simp)
      have htail : ∀ b ∈ as, (payload b).length ≤ B := by
        intro b hb
        exact hB b (by simp [hb])
      have h := ih (payload a ++ saved) htail
      simp only [foldSaved, List.foldl_cons,
        List.length_append, List.length_cons] at h ⊢
      rw [Nat.add_mul]
      omega

theorem base_offset_le {q : ℕ} (k : Fin (2 ^ q))
    (n r H ell : ℕ) (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1) :
    base n r k + ell ≤ addressCoefficient q * (H + 1) := by
  have h := unit_address_le_linear k n r H ell hn hr hell
  simpa [SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue,
    SourceClauseRowUnitAddress.offsetValue,
    SourceClauseCallback.base, SourceClauseCallback.width,
    SourceClauseRowSlotAddress.slot,
    SourceClauseRowSchedule.slot, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

theorem false_gate_bytes_le {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (2 ^ q)) (j : Fin q)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (falseGateBytes row n r k j).length ≤
      gateByteCoefficient q * (H + 1) := by
  have hp := base_offset_le k n r H j.val hn hr (by omega)
  have hv := hrow (.inl (j, 1))
  have hs := (tuple 2 q k j).isLt
  have hl :
      (SourceClauseRowInstruction.literal (rowQuery row)
        (SourceClauseRowInstruction.rejected k j)).variable ≤
        3 * (H + 1) := by
    simp only [SourceClauseRowInstruction.literal,
      SourceClauseRowInstruction.rejected, rowQuery]
    omega
  have h := gate_bytes_le_linear q H (base n r k + j.val)
    (SourceClauseRowInstruction.literal (rowQuery row)
      (SourceClauseRowInstruction.rejected k j)) hp hl
  simpa only [falseGateBytes, SourceClauseCallback.gatePayload,
    List.length_reverse] using h

theorem true_gate_bytes_le {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (2 ^ q)) (p : Fin (q + 1))
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (trueGateBytes hq row n r k p).length ≤
      gateByteCoefficient q * (H + 1) := by
  have hp := base_offset_le k n r H p.val hn hr (by omega)
  have hv := hrow (.inl ((SourceTrueClauseCallback.instruction hq k p).1, 1))
  have hs := (SourceTrueClauseCallback.instruction hq k p).2.1.isLt
  have hl :
      (SourceClauseRowInstruction.literal (rowQuery row)
        (SourceTrueClauseCallback.instruction hq k p)).variable ≤
        3 * (H + 1) := by
    simp only [SourceClauseRowInstruction.literal, rowQuery]
    omega
  have h := gate_bytes_le_linear q H (base n r k + p.val)
    (SourceClauseRowInstruction.literal (rowQuery row)
      (SourceTrueClauseCallback.instruction hq k p)) hp hl
  simpa only [trueGateBytes, SourceTrueClauseCallback.gatePayload,
    List.length_reverse] using h

theorem listCost_le_bounded {α : Type}
    (stepCost : α → List Bool → List Bool → List Bool → ℕ)
    (payload : α → List Bool) (as : List α)
    (saved output count : List Bool) (B G C : ℕ)
    (hpayload : ∀ a ∈ as, (payload a).length ≤ B)
    (hsaved : saved.length + as.length * B ≤ G)
    (hcount : count.length + 3 * as.length ≤ G)
    (hstep : ∀ a ∈ as, ∀ s c,
      s.length ≤ G → c.length ≤ G →
      stepCost a s output c ≤ C) :
    listCost stepCost payload as saved output count ≤
      as.length * (C + 1) + 1 := by
  induction as generalizing saved count with
  | nil => simp [listCost]
  | cons a as ih =>
      have ha : (payload a).length ≤ B := hpayload a (by simp)
      have hpTail : ∀ b ∈ as, (payload b).length ≤ B := by
        intro b hb
        exact hpayload b (by simp [hb])
      have hsTail : ∀ b ∈ as, ∀ s c,
          s.length ≤ G → c.length ≤ G →
          stepCost b s output c ≤ C := by
        intro b hb s c hsc hcc
        exact hstep b (by simp [hb]) s c hsc hcc
      have hs₁ : (payload a ++ saved).length + as.length * B ≤ G := by
        simp only [List.length_append, List.length_cons] at hsaved ⊢
        rw [Nat.add_mul] at hsaved
        omega
      have hc₁ : (true :: true :: true :: count).length +
          3 * as.length ≤ G := by
        simp only [List.length_cons] at hcount ⊢
        omega
      have ht := ih (payload a ++ saved)
        (true :: true :: true :: count) hpTail hs₁ hc₁ hsTail
      have hhead := hstep a (by simp) saved count
        (by omega) (by omega)
      simp only [listCost, List.length_cons] at ⊢
      rw [Nat.add_mul]
      omega

def gateListFactor (q : ℕ) : ℕ :=
  1 + (q + 1) * (gateByteCoefficient q + 3)

noncomputable def gateListCoefficient (q : ℕ) : ℕ :=
  (q + 1) *
    (gateCallCoefficient q * (gateListFactor q) ^ 2 + 1) + 1

theorem gate_list_cost_le_quadratic {α : Type} (q H : ℕ)
    (stepCost : α → List Bool → List Bool → List Bool → ℕ)
    (payload : α → List Bool) (as : List α)
    (saved output count : List Bool)
    (hlen : as.length ≤ q + 1)
    (hsaved : saved.length ≤ H) (hcount : count.length ≤ H)
    (hpayload : ∀ a ∈ as,
      (payload a).length ≤ gateByteCoefficient q * (H + 1))
    (hstep : ∀ a ∈ as, ∀ s c,
      s.length ≤ H + (q + 1) *
        (gateByteCoefficient q * (H + 1) + 3) →
      c.length ≤ H + (q + 1) *
        (gateByteCoefficient q * (H + 1) + 3) →
      stepCost a s output c ≤ gateCallCoefficient q *
        (H + (q + 1) * (gateByteCoefficient q * (H + 1) + 3) + 1) ^ 2) :
    listCost stepCost payload as saved output count ≤
      gateListCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let B := gateByteCoefficient q * M
  let G := H + (q + 1) * (B + 3)
  let F := gateListFactor q
  have hM : 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hB : saved.length + as.length * B ≤ G := by
    have hm := Nat.mul_le_mul hlen (Nat.le_add_right B 3)
    dsimp [G, B] at hm ⊢
    omega
  have hC : count.length + 3 * as.length ≤ G := by
    have hm := Nat.mul_le_mul hlen (Nat.le_add_left 3 B)
    rw [Nat.mul_comm as.length 3] at hm
    dsimp [G, B] at hm ⊢
    omega
  have ht := listCost_le_bounded stepCost payload as
    saved output count B G
    (gateCallCoefficient q * (G + 1) ^ 2)
    (by simpa only [B, M] using hpayload)
    hB hC (by simpa only [G, B, M] using hstep)
  have hF : G + 1 ≤ F * M := by
    have hthree : 3 ≤ 3 * M := by dsimp [M]; omega
    have hmul := Nat.mul_le_mul_left (q + 1)
      (Nat.add_le_add_left hthree B)
    dsimp [G, F, B, M, gateListFactor]
    nlinarith
  have hF₂ : (G + 1) ^ 2 ≤ F ^ 2 * M ^ 2 := by
    nlinarith [Nat.mul_le_mul hF hF]
  have hclock := Nat.mul_le_mul_left (gateCallCoefficient q) hF₂
  have hlenmul := Nat.mul_le_mul_right
    (gateCallCoefficient q * F ^ 2 * M ^ 2 + 1) hlen
  dsimp [gateListCoefficient, F, M] at *
  nlinarith

theorem false_list_cost_le_quadratic {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H) (houtput : output.length ≤ H)
    (hcount : count.length ≤ H)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    listCost (falseGateCost row n r k) (falseGateBytes row n r k)
      (List.ofFn (fun j : Fin q => j)) saved output count ≤
      gateListCoefficient q * (H + 1) ^ 2 := by
  let G := H + (q + 1) *
    (gateByteCoefficient q * (H + 1) + 3)
  apply gate_list_cost_le_quadratic q H
    (falseGateCost row n r k) (falseGateBytes row n r k)
    (List.ofFn (fun j : Fin q => j)) saved output count
  · simp
  · exact hsaved
  · exact hcount
  · intro j _
    exact false_gate_bytes_le row n r H k j hn hr hrow
  · intro j _ s c hs hc
    have hHG : H ≤ G := by dsimp [G]; omega
    have hrowG : ∀ x, (row x).length ≤ G := by
      intro x
      exact (hrow x).trans hHG
    have hbank := blank_words_le row n r G s output c
      (hn.trans hHG) (hr.trans hHG) hrowG hs
      (houtput.trans hHG) hc
    have h := gate_call_le_quadratic j row n r G k
      (tuple 2 q k j).val j.val false s output c
      (hn.trans hHG) (hr.trans hHG)
      ((hrow (.inl (j, 1))).trans hHG)
      (by have hh := (tuple 2 q k j).isLt; omega)
      (by omega) (hquery j) hbank
    simpa only [falseGateCost, G] using h

theorem true_list_cost_le_quadratic {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H) (houtput : output.length ≤ H)
    (hcount : count.length ≤ H)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    listCost (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
      (List.ofFn (fun p : Fin (q + 1) => p)) saved output count ≤
      gateListCoefficient q * (H + 1) ^ 2 := by
  let G := H + (q + 1) *
    (gateByteCoefficient q * (H + 1) + 3)
  apply gate_list_cost_le_quadratic q H
    (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
    (List.ofFn (fun p : Fin (q + 1) => p)) saved output count
  · simp
  · exact hsaved
  · exact hcount
  · intro p _
    exact true_gate_bytes_le hq row n r H k p hn hr hrow
  · intro p _ s c hs hc
    have hHG : H ≤ G := by dsimp [G]; omega
    have hrowG : ∀ x, (row x).length ≤ G := by
      intro x
      exact (hrow x).trans hHG
    have hbank := blank_words_le row n r G s output c
      (hn.trans hHG) (hr.trans hHG) hrowG hs
      (houtput.trans hHG) hc
    have h := gate_call_le_quadratic
      (SourceTrueClauseCallback.instruction hq k p).1 row n r G k
      (SourceTrueClauseCallback.instruction hq k p).2.1.val p.val
      (SourceTrueClauseCallback.instruction hq k p).2.2 s output c
      (hn.trans hHG) (hr.trans hHG)
      ((hrow (.inl ((SourceTrueClauseCallback.instruction hq k p).1, 1))).trans hHG)
      (by have hh := (SourceTrueClauseCallback.instruction hq k p).2.1.isLt;
          omega)
      (by omega) (hquery (SourceTrueClauseCallback.instruction hq k p).1)
      hbank
    simpa only [trueGateCost, G] using h

def blockGrowthCoefficient (q : ℕ) : ℕ :=
  unitByteCoefficient q + (q + 1) * (gateByteCoefficient q + 3) + 2

def blockFactor (q : ℕ) : ℕ := 1 + blockGrowthCoefficient q

noncomputable def blockCoefficient (q : ℕ) : ℕ :=
  (2 * unitCallCoefficient q + gateListCoefficient q) *
    (blockFactor q) ^ 2 + 2

theorem block_capacity {q H : ℕ} :
    (H + blockGrowthCoefficient q * (H + 1)) + 1 =
      blockFactor q * (H + 1) := by
  dsimp [blockFactor]
  ring

theorem opening_bytes_le {q : ℕ}
    (n r H : ℕ) (k : Fin (2 ^ q))
    (hn : n ≤ H) (hr : r ≤ H) :
    (encodeClause (unit (negative (base n r k)))).length ≤
      unitByteCoefficient q * (H + 1) := by
  have hp := base_offset_le k n r H 0 hn hr (by omega)
  simpa only [negative] using
    unit_bytes_le_linear q H (base n r k) false hp

theorem false_block_cost_le_quadratic {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H) (houtput : output.length ≤ H)
    (hcount : count.length ≤ H)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    falseBlockCost row n r k saved output count ≤
      blockCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let G := H + blockGrowthCoefficient q * M
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let js := List.ofFn (fun j : Fin q => j)
  let s₁ := foldSaved (falseGateBytes row n r k) js s₀
  let c₁ := List.replicate (3 * q) true ++ c₀
  have hHG : H ≤ G := by dsimp [G]; omega
  have hM₁ : 1 ≤ M := by dsimp [M]; omega
  have hG : G + 1 = blockFactor q * M := by
    simpa only [G, M] using block_capacity (q := q) (H := H)
  have hs₀ : s₀.length ≤ G := by
    have hb := opening_bytes_le n r H k hn hr
    have hcoeff : unitByteCoefficient q ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      omega
    have hmul := Nat.mul_le_mul_right M hcoeff
    have hfirst : s₀.length ≤ H + unitByteCoefficient q * M := by
      dsimp [s₀]
      simp only [List.length_append, List.length_reverse]
      dsimp [M] at ⊢
      omega
    exact hfirst.trans (by
      change H + unitByteCoefficient q * M ≤
        H + blockGrowthCoefficient q * M
      exact Nat.add_le_add_left hmul H)
  have hc₀ : c₀.length ≤ G := by
    have hc : 1 ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      omega
    have hpos := Nat.mul_le_mul hc hM₁
    change count.length + 1 ≤ H + blockGrowthCoefficient q * M
    simp only [one_mul] at hpos
    omega
  have hbytes : ∀ j ∈ js,
      (falseGateBytes row n r k j).length ≤
        gateByteCoefficient q * M := by
    intro j _
    exact false_gate_bytes_le row n r H k j hn hr hrow
  have hs₁ : s₁.length ≤ G := by
    have hf := foldSaved_length_le (falseGateBytes row n r k)
      js s₀ (gateByteCoefficient q * M) hbytes
    have hb := opening_bytes_le n r H k hn hr
    have hfirst : s₀.length ≤ H + unitByteCoefficient q * M := by
      dsimp [s₀]
      simp only [List.length_append, List.length_reverse]
      dsimp [M] at ⊢
      omega
    have hq : js.length ≤ q + 1 := by simp [js]
    have hm := Nat.mul_le_mul_right (gateByteCoefficient q * M) hq
    have hcoeff : unitByteCoefficient q +
        (q + 1) * gateByteCoefficient q ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      nlinarith
    have hg := Nat.mul_le_mul_right M hcoeff
    have hg' : unitByteCoefficient q * M +
        (q + 1) * (gateByteCoefficient q * M) ≤
        blockGrowthCoefficient q * M := by
      nlinarith
    calc
      s₁.length ≤ s₀.length + js.length *
          (gateByteCoefficient q * M) := by simpa only [s₁] using hf
      _ ≤ H + unitByteCoefficient q * M +
          (q + 1) * (gateByteCoefficient q * M) := by omega
      _ ≤ G := by change _ ≤ H + blockGrowthCoefficient q * M; omega
  have hc₁ : c₁.length ≤ G := by
    have hc : 3 * q + 1 ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      nlinarith
    have hmul := Nat.mul_le_mul hc hM₁
    dsimp [c₁, c₀, G]
    simp only [List.length_append, List.length_replicate,
      List.length_cons]
    change 3 * q + (count.length + 1) ≤
      H + blockGrowthCoefficient q * M
    omega
  have hrowG : ∀ x, (row x).length ≤ G := by
    intro x
    exact (hrow x).trans hHG
  have hbank₀ := blank_words_le row n r G saved output count
    (hn.trans hHG) (hr.trans hHG) hrowG
    (hsaved.trans hHG) (houtput.trans hHG) (hcount.trans hHG)
  have hbank₁ := blank_words_le row n r G s₁ output c₁
    (hn.trans hHG) (hr.trans hHG) hrowG hs₁
    (houtput.trans hHG) hc₁
  have hu₀ := unit_call_le_quadratic row n r G k 0 false
    saved output count (hn.trans hHG) (hr.trans hHG) (by omega) hbank₀
  have hl := false_list_cost_le_quadratic row n r G k s₀ output c₀
    (hn.trans hHG) (hr.trans hHG) hrowG hs₀
    (houtput.trans hHG) hc₀ hquery
  have hu₁ := unit_call_le_quadratic row n r G k q true
    s₁ output c₁ (hn.trans hHG) (hr.trans hHG) (by omega) hbank₁
  have hM : 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
  dsimp [falseBlockCost, blockCoefficient,
    s₀, c₀, js, s₁, c₁] at *
  rw [hG] at hu₀ hu₁ hl
  rw [mul_pow] at hu₀ hu₁ hl
  have hsum :
      unitCost row n r k 0 false saved output count +
          (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
              (List.ofFn (fun j : Fin q => j))
              ((encodeClause (unit (negative (base n r k)))).reverse ++ saved)
              output (true :: count) +
            unitCost row n r k q true
              (foldSaved (falseGateBytes row n r k)
                (List.ofFn (fun j : Fin q => j))
                ((encodeClause (unit (negative (base n r k)))).reverse ++ saved))
              output (List.replicate (3 * q) true ++ true :: count) + 1) + 1 ≤
        (2 * unitCallCoefficient q + gateListCoefficient q) *
          (blockFactor q ^ 2 * M ^ 2) + 2 := by
    nlinarith
  have htwo : 2 ≤ 2 * M ^ 2 := by nlinarith
  have heq :
      ((2 * unitCallCoefficient q + gateListCoefficient q) *
          blockFactor q ^ 2 + 2) * M ^ 2 =
        (2 * unitCallCoefficient q + gateListCoefficient q) *
          (blockFactor q ^ 2 * M ^ 2) + 2 * M ^ 2 := by ring
  rw [show (H + 1) ^ 2 = M ^ 2 by rfl, heq]
  omega

theorem true_block_cost_le_quadratic {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H) (houtput : output.length ≤ H)
    (hcount : count.length ≤ H)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    trueBlockCost hq row n r k saved output count ≤
      blockCoefficient q * (H + 1) ^ 2 := by
  let M := H + 1
  let G := H + blockGrowthCoefficient q * M
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let ps := List.ofFn (fun p : Fin (q + 1) => p)
  let s₁ := foldSaved (trueGateBytes hq row n r k) ps s₀
  let c₁ := List.replicate (3 * (q + 1)) true ++ c₀
  have hHG : H ≤ G := by dsimp [G]; omega
  have hM₁ : 1 ≤ M := by dsimp [M]; omega
  have hG : G + 1 = blockFactor q * M := by
    simpa only [G, M] using block_capacity (q := q) (H := H)
  have hs₀ : s₀.length ≤ G := by
    have hb := opening_bytes_le n r H k hn hr
    have hcoeff : unitByteCoefficient q ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      omega
    have hmul := Nat.mul_le_mul_right M hcoeff
    have hfirst : s₀.length ≤ H + unitByteCoefficient q * M := by
      dsimp [s₀]
      simp only [List.length_append, List.length_reverse]
      dsimp [M] at ⊢
      omega
    exact hfirst.trans (by
      change H + unitByteCoefficient q * M ≤
        H + blockGrowthCoefficient q * M
      exact Nat.add_le_add_left hmul H)
  have hc₀ : c₀.length ≤ G := by
    have hc : 1 ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      omega
    have hpos := Nat.mul_le_mul hc hM₁
    change count.length + 1 ≤ H + blockGrowthCoefficient q * M
    simp only [one_mul] at hpos
    omega
  have hbytes : ∀ p ∈ ps,
      (trueGateBytes hq row n r k p).length ≤
        gateByteCoefficient q * M := by
    intro p _
    exact true_gate_bytes_le hq row n r H k p hn hr hrow
  have hs₁ : s₁.length ≤ G := by
    have hf := foldSaved_length_le (trueGateBytes hq row n r k)
      ps s₀ (gateByteCoefficient q * M) hbytes
    have hfirst : s₀.length ≤ H + unitByteCoefficient q * M := by
      have hb := opening_bytes_le n r H k hn hr
      dsimp [s₀]
      simp only [List.length_append, List.length_reverse]
      dsimp [M] at ⊢
      omega
    have hq' : ps.length ≤ q + 1 := by simp [ps]
    have hm := Nat.mul_le_mul_right (gateByteCoefficient q * M) hq'
    have hcoeff : unitByteCoefficient q +
        (q + 1) * gateByteCoefficient q ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      nlinarith
    have hg := Nat.mul_le_mul_right M hcoeff
    have hg' : unitByteCoefficient q * M +
        (q + 1) * (gateByteCoefficient q * M) ≤
        blockGrowthCoefficient q * M := by
      nlinarith
    calc
      s₁.length ≤ s₀.length + ps.length *
          (gateByteCoefficient q * M) := by simpa only [s₁] using hf
      _ ≤ H + unitByteCoefficient q * M +
          (q + 1) * (gateByteCoefficient q * M) := by omega
      _ ≤ G := by change _ ≤ H + blockGrowthCoefficient q * M; omega
  have hc₁ : c₁.length ≤ G := by
    have hc : 3 * (q + 1) + 1 ≤ blockGrowthCoefficient q := by
      dsimp [blockGrowthCoefficient]
      nlinarith
    have hmul := Nat.mul_le_mul hc hM₁
    dsimp [c₁, c₀, G]
    simp only [List.length_append, List.length_replicate,
      List.length_cons]
    change 3 * (q + 1) + (count.length + 1) ≤
      H + blockGrowthCoefficient q * M
    omega
  have hrowG : ∀ x, (row x).length ≤ G := by
    intro x
    exact (hrow x).trans hHG
  have hbank₀ := blank_words_le row n r G saved output count
    (hn.trans hHG) (hr.trans hHG) hrowG
    (hsaved.trans hHG) (houtput.trans hHG) (hcount.trans hHG)
  have hbank₁ := blank_words_le row n r G s₁ output c₁
    (hn.trans hHG) (hr.trans hHG) hrowG hs₁
    (houtput.trans hHG) hc₁
  have hu₀ := unit_call_le_quadratic row n r G k 0 false
    saved output count (hn.trans hHG) (hr.trans hHG) (by omega) hbank₀
  have hl := true_list_cost_le_quadratic hq row n r G k s₀ output c₀
    (hn.trans hHG) (hr.trans hHG) hrowG hs₀
    (houtput.trans hHG) hc₀ hquery
  have hu₁ := unit_call_le_quadratic row n r G k (q + 1) true
    s₁ output c₁ (hn.trans hHG) (hr.trans hHG) (by omega) hbank₁
  have hM : 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
  dsimp [trueBlockCost, blockCoefficient,
    s₀, c₀, ps, s₁, c₁] at *
  rw [hG] at hu₀ hu₁ hl
  rw [mul_pow] at hu₀ hu₁ hl
  have hsum :
      unitCost row n r k 0 false saved output count +
          (listCost (trueGateCost hq row n r k)
              (trueGateBytes hq row n r k)
              (List.ofFn (fun p : Fin (q + 1) => p))
              ((encodeClause (unit (negative (base n r k)))).reverse ++ saved)
              output (true :: count) +
            unitCost row n r k (q + 1) true
              (foldSaved (trueGateBytes hq row n r k)
                (List.ofFn (fun p : Fin (q + 1) => p))
                ((encodeClause (unit (negative (base n r k)))).reverse ++ saved))
              output (List.replicate (3 * (q + 1)) true ++ true :: count) + 1) + 1 ≤
        (2 * unitCallCoefficient q + gateListCoefficient q) *
          (blockFactor q ^ 2 * M ^ 2) + 2 := by
    nlinarith
  have htwo : 2 ≤ 2 * M ^ 2 := by nlinarith
  have heq :
      ((2 * unitCallCoefficient q + gateListCoefficient q) *
          blockFactor q ^ 2 + 2) * M ^ 2 =
        (2 * unitCallCoefficient q + gateListCoefficient q) *
          (blockFactor q ^ 2 * M ^ 2) + 2 * M ^ 2 := by ring
  rw [show (H + 1) ^ 2 = M ^ 2 by rfl, heq]
  omega

end EthInapproximability.CurrentPaper.SourceClauseCallbackBlockPolynomial
