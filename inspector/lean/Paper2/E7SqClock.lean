import Paper2.E7SqDec
import Paper2.E6DecClock
-- root successor copy (30 September 2026, for the R22 batch): the docstring citation of `Paper2.AEth6.budget_of_dom` (which does not exist) replaced by the actual constant `Paper2.AEth4.budget_of_dom` (readback:a-eth-7 defect D3) corrected; no other change.

/-!
# Paper A (lock v12), lane `owner:a-eth-7`, segment 6e: the square decider's clock is inside D-A6

`decTimeSq_eq`: the composite square clock is the a-eth-owner-6 expression `Paper2.AEth6.GD` at the seven
atoms of the square decider (definitional). On sparse valid inputs beyond one cutoff:
* the five front atoms are at most `hdTime4` (`Paper2.AEth6.front_atoms`, `Paper2.AEth6.hd_split`), and
  `hdTime4 ≤ H := P4 Y` (`Paper2.AEth4.hdTime4_dom`), `Y = (|x|+1)(expLen N+1)(n+2)^((K0+164)(k+1))`;
* the square header word length `hwLenSq ≤ W := Y^3` (`hw_length_le_sq`: `≤ (n+2)^(332(k+1))`);
* the square tail clock `tailTimeSq ≤ QT H W` (`tailTimeSq_le`), with the admitted post clock
  `squareCP (ob+1)^squareEP`, `ob ≤ H`, and `GrowHeader.clock_le` for the square header.
Hence `decTimeSq ≤ GDH (H + W + QT H W)`, ONE fixed polynomial of `Y`, and the frozen
`Paper2.AEth4.budget_of_dom` gives the D-A6 budget (`decTimeSq_budget`).

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth7

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth4 Paper2.AEth5 Paper2.AEth6
open Paper2.AEth3 (fOut cutLen cutLen_ge cut0 inputBits_fit)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem decTimeSq_eq (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) :
    decTimeSq D B C K N₁ hN₁ w =
      GD C (inner4 K N₁).pushBound w.length (inner4Time K N₁ w)
        (fOut (routedV K N₁ hN₁ w).val).length (cutLen (routedV K N₁ hN₁ w).val)
        (EncodedCNF.encode (routedV K N₁ hN₁ w).val).length (tailTimeSq D B (routedV K N₁ hN₁ w))
        (hwLenSq D B (routedV K N₁ hN₁ w)) := rfl

/-- The square tail bound as ONE expression in `H` (the header clock bound) and `W` (the square word bound). -/
def QT (H W : ℕ) : ℕ :=
  100 * (H + (W + H + 1) + 1) + Paper2.ASquare.Post.squareCP * (H + 1) ^ Paper2.ASquare.Post.squareEP +
    (H + 2 * (2 * H + 1 + (W + H + 1)) + 2 + 4 * (2 * H + (W + H + 1) + 2) ^ 2)

theorem sobLen_le (Φ : ValidFormula) : sobLen D B Φ ≤ hwLenSq D B Φ + obLen D B Φ + 1 := by
  unfold sobLen hwLenSq obLen sideOf
  simp only [EncodedCommunication.natField, EncodedCommunication.field_length]
  omega

set_option maxHeartbeats 800000 in
/-- **The square tail clock is at most `QT H W`** whenever the header clock atoms are at most `H` and the square
word length is at most `W`. -/
theorem tailTimeSq_le (Φ : ValidFormula) (H W : ℕ) (hT : tailTime D B Φ ≤ H) (hW : hwLenSq D B Φ ≤ W) :
    tailTimeSq D B Φ ≤ QT H W := by
  have hsb := sobLen_le D B Φ
  have htail : (EncodedCNF.encode Φ.val).length ≤ H ∧ cutLen Φ.val ≤ H ∧ obLen D B Φ ≤ H ∧
      mgTime D B Φ ≤ H ∧ khTime D B Φ ≤ H := by
    simp only [tailTime] at hT
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨he, hL, hob, hmg, hkh⟩ := htail
  have hk : kOf Φ.val.variables ≤ H := by unfold khTime at hkh; omega
  have hkh1 : 2 * (EncodedCNF.encode Φ.val).length +
      Paper2.Unit4Shell.KofFront.BK * (Φ.val.variables + 1) ^ 2 + 2 * kOf Φ.val.variables + 6 ≤ H := by
    unfold khTime at hkh; omega
  -- the square header clock
  have hgc := GrowHeader.clock_le (kOf Φ.val.variables)
    ⟨sideOf D B Φ, sideOf D B Φ, (Sel D B Φ).budget, List.replicate (sideOf D B Φ * sideOf D B Φ) false⟩
  have hencl : (EncodedCommunication.encodeInstance
      ⟨sideOf D B Φ, sideOf D B Φ, (Sel D B Φ).budget,
        List.replicate (sideOf D B Φ * sideOf D B Φ) false⟩).length = sobLen D B Φ := by
    rw [EncodedCommunication.encodeInstance_length]
    simp only [List.length_replicate]
    rfl
  rw [EncodedComplexity.pair_length, List.length_replicate, hencl] at hgc
  dsimp only at hgc
  have hsq : Paper2.ASquare.Post.squareCP * (obLen D B Φ + 1) ^ Paper2.ASquare.Post.squareEP ≤
      Paper2.ASquare.Post.squareCP * (H + 1) ^ Paper2.ASquare.Post.squareEP :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hg2 : 4 * (2 * kOf Φ.val.variables + 1 + sobLen D B Φ + 1) ^ 2 ≤
      4 * (2 * H + (W + H + 1) + 2) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  simp only [tailTimeSq, khTimeSq, QT]
  omega

set_option maxHeartbeats 1600000 in
/-- **Domination of the square clock on sparse promise inputs.** -/
theorem decTimeSq_dom (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) :
    ∃ N₂ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ K * Φ.val.variables →
      N₂ ≤ Φ.val.variables →
      decTimeSq D B C K N₁ hN₁ (EncodedCNF.encode Φ.val) ≤
        GDH C (inner4 K N₁).pushBound
          ((P4 D B K N₁ (((EncodedCNF.encode Φ.val).length + 1) *
              (Paper2.AEth.expLen Φ.val.variables + 1) *
              ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) +
            (((EncodedCNF.encode Φ.val).length + 1) *
              (Paper2.AEth.expLen Φ.val.variables + 1) *
              ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) ^ 3) +
            QT (P4 D B K N₁ (((EncodedCNF.encode Φ.val).length + 1) *
              (Paper2.AEth.expLen Φ.val.variables + 1) *
              ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) +
            (((EncodedCNF.encode Φ.val).length + 1) *
              (Paper2.AEth.expLen Φ.val.variables + 1) *
              ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) ^ 3)
            (P4 D B K N₁ (((EncodedCNF.encode Φ.val).length + 1) *
              (Paper2.AEth.expLen Φ.val.variables + 1) *
              ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) +
            (((EncodedCNF.encode Φ.val).length + 1) *
              (Paper2.AEth.expLen Φ.val.variables + 1) *
              ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) ^ 3)) := by
  obtain ⟨N₂, hN₂⟩ := hdTime4_dom D B K N₁ hN₁
  obtain ⟨Nf, hNf⟩ := inputBits_fit D B K
  refine ⟨max N₁ (max N₂ (max Nf (cut0 D B))), fun Φ hsp hN => ?_⟩
  have hN1 : N₁ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNf' : Nf ≤ Φ.val.variables :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hc0 : cut0 D B ≤ Φ.val.variables :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hN
  have hr4 : routed4 K N₁ (EncodedCNF.encode Φ.val) = Φ.val :=
    routed4_encode K N₁ Φ.val Φ.property hsp hN1
  have hV : routedV K N₁ hN₁ (EncodedCNF.encode Φ.val) = Φ := Subtype.ext hr4
  have hdom := hN₂ Φ hsp hN2
  obtain ⟨a1, a2, a3, a4, a5⟩ := front_atoms K N₁ (EncodedCNF.encode Φ.val)
  have hs := hd_split D B K N₁ hN₁ (EncodedCNF.encode Φ.val)
  rw [hV] at hs
  have e3 : (fOut Φ.val).length = (fOut (routed4 K N₁ (EncodedCNF.encode Φ.val))).length := by rw [hr4]
  have e4 : cutLen Φ.val = cutLen (routed4 K N₁ (EncodedCNF.encode Φ.val)) := by rw [hr4]
  have e5 : (EncodedCNF.encode Φ.val).length =
      (EncodedCNF.encode (routed4 K N₁ (EncodedCNF.encode Φ.val))).length := by rw [hr4]
  -- the square word length
  obtain ⟨hk, hI⟩ := hNf Φ hsp hNf'
  have hge := cutLen_ge Φ.val
  have hI' : (Sel D B Φ).inputBits ≤ Paper2.AEth.expLen Φ.val.variables := hI
  obtain ⟨t', -, -⟩ := mg_outputs D B Φ hk hc0 (List.replicate (cutLen Φ.val) false)
    (by simp) (by simp only [List.length_replicate]; omega)
  have hwl := hw_length_le_sq D B Φ hk t'
  rw [hw_length_eq_sq] at hwl
  have hexp : 332 * (kOf Φ.val.variables + 1) ≤ (Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1) * 3 := by
    calc 332 * (kOf Φ.val.variables + 1) ≤ 492 * (kOf Φ.val.variables + 1) :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 164 * (kOf Φ.val.variables + 1) * 3 := by ring
      _ ≤ (Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1) * 3 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hn2 : 1 ≤ (t10Graph D B Φ).vertices + 2 := by omega
  have hA : 1 ≤ ((EncodedCNF.encode Φ.val).length + 1) * (Paper2.AEth.expLen Φ.val.variables + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hW : hwLenSq D B Φ ≤ (((EncodedCNF.encode Φ.val).length + 1) *
      (Paper2.AEth.expLen Φ.val.variables + 1) *
      ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) ^ 3 := by
    have h1 : ((t10Graph D B Φ).vertices + 2) ^ (332 * (kOf Φ.val.variables + 1)) ≤
        ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1) * 3) :=
      Nat.pow_le_pow_right hn2 hexp
    have h1' : ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1) * 3) =
        (((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) ^ 3 :=
      pow_mul _ _ _
    have h2 : ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1)) ≤
        ((EncodedCNF.encode Φ.val).length + 1) * (Paper2.AEth.expLen Φ.val.variables + 1) *
          ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1)) :=
      Nat.le_mul_of_pos_left _ hA
    have h3 := Nat.pow_le_pow_left h2 3
    exact le_trans (Nat.le_succ _) (le_trans hwl (le_trans h1 (le_trans h1'.le h3)))
  have hT : tailTime D B Φ ≤ P4 D B K N₁ (((EncodedCNF.encode Φ.val).length + 1) *
      (Paper2.AEth.expLen Φ.val.variables + 1) *
      ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) := by
    omega
  have hQ := tailTimeSq_le D B Φ (P4 D B K N₁ (((EncodedCNF.encode Φ.val).length + 1) * (Paper2.AEth.expLen Φ.val.variables + 1) * ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) + (((EncodedCNF.encode Φ.val).length + 1) * (Paper2.AEth.expLen Φ.val.variables + 1) * ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) ^ 3)
    (P4 D B K N₁ (((EncodedCNF.encode Φ.val).length + 1) * (Paper2.AEth.expLen Φ.val.variables + 1) * ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) + (((EncodedCNF.encode Φ.val).length + 1) * (Paper2.AEth.expLen Φ.val.variables + 1) * ((t10Graph D B Φ).vertices + 2) ^ ((Paper2.AEth3.K0 D B + 164) * (kOf Φ.val.variables + 1))) ^ 3)
    (le_trans hT (Nat.le_add_right _ _)) (le_trans hW (Nat.le_add_left _ _))
  rw [decTimeSq_eq, hV]
  have a3' : (fOut Φ.val).length ≤ frontTime4 K N₁ (EncodedCNF.encode Φ.val) := by rw [e3]; exact a3
  have a4' : cutLen Φ.val ≤ frontTime4 K N₁ (EncodedCNF.encode Φ.val) := by rw [e4]; exact a4
  have a5' : (EncodedCNF.encode Φ.val).length ≤ frontTime4 K N₁ (EncodedCNF.encode Φ.val) := by
    rw [e5]; exact a5
  apply GD_mono
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

set_option maxRecDepth 20000 in
theorem QTZ_poly : Paper2.Unit4Shell.Poly.PolyIn id (fun Z => Z + QT Z Z) := by
  unfold QT
  generalize Paper2.ASquare.Post.squareCP = cp
  generalize Paper2.ASquare.Post.squareEP = ep
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow
    | exact Paper2.Unit4Shell.Poly.const _)

theorem ZY_poly (K N₁ : ℕ) : Paper2.Unit4Shell.Poly.PolyIn id (fun Y => P4 D B K N₁ Y + Y ^ 3) := by
  apply Paper2.Unit4Shell.Poly.add
  · exact P4_poly D B K N₁
  · apply Paper2.Unit4Shell.Poly.pow
    exact Paper2.Unit4Shell.Poly.self

/-- **The square decider's clock is inside the D-A6 budget** on sparse valid inputs, for every `ε > 0`
eventually. -/
theorem decTimeSq_budget (C : Paper2.SelectedTape.Algorithm) (K : ℕ) :
    ∀ N₁ (hN₁ : 1 ≤ N₁), 2 ≤ K * N₁ → ∀ ε : ℝ, 0 < ε →
      ∃ C' d N₂ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ K * Φ.val.variables →
        N₂ ≤ Φ.val.variables →
        decTimeSq D B C K N₁ hN₁ (EncodedCNF.encode Φ.val) ≤
          C' * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ * ((EncodedCNF.encode Φ.val).length + 1) ^ d := by
  intro N₁ hN₁ _ ε hε
  obtain ⟨N₂, hN₂⟩ := decTimeSq_dom D B C K N₁ hN₁
  have hP := polyIn_comp (GDH_poly C (inner4 K N₁).pushBound) (polyIn_comp QTZ_poly (ZY_poly D B K N₁))
  exact budget_of_dom D B K (Paper2.AEth3.K0 D B + 164) (fun Φ => decTimeSq D B C K N₁ hN₁ (EncodedCNF.encode Φ.val))
    (fun Y => GDH C (inner4 K N₁).pushBound ((P4 D B K N₁ Y + Y ^ 3) + QT (P4 D B K N₁ Y + Y ^ 3) (P4 D B K N₁ Y + Y ^ 3))) hP N₂
    (fun Φ hsp hN => hN₂ Φ hsp hN) ε hε

end Paper2.AEth7

end

#print axioms Paper2.AEth7.decTimeSq_eq
#print axioms Paper2.AEth7.sobLen_le
#print axioms Paper2.AEth7.tailTimeSq_le
#print axioms Paper2.AEth7.decTimeSq_dom
#print axioms Paper2.AEth7.QTZ_poly
#print axioms Paper2.AEth7.ZY_poly
#print axioms Paper2.AEth7.decTimeSq_budget
