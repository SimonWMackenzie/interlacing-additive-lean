import Paper2.E6Dec
import Paper2.E6Clock
-- root successor copy (30 September 2026, for the R22 batch): the docstring citation of a non-existent `atoms_le` replaced by the actual facts `front_atoms`, `hd_split` (readback:a-eth-6 defect D4) corrected; no other change.

/-!
# Paper A (lock v12), lane `owner:a-eth-6`, segment 2 (clock): the composite decider is inside D-A6

The composite clock `decTime` (E6Dec, copy of a-eth-owner-5 `E5Dec`) is ONE fixed polynomial expression
`GD` of seven atoms (the front-cut input length, the inner clock, `|fOut Φ'|`, `cutLen Φ'`, `|encode Φ'|`,
the header tail clock and the header word length), `decTime_eq` (definitional). Every atom is at most the
a-eth-owner-4 header clock `hdTime4` on EVERY word (`front_atoms`, `hd_split`), so `decTime ≤ GD(hdTime4)` (`decTime_le`),
and `hdTime4 ≤ P4(Z)` on sparse inputs (a-eth-owner-4 `hdTime4_dom`); the frozen `budget_of_dom` then gives
the D-A6 budget (`decTime_budget`). This module imports NO `ETape`.

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth6

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth4 Paper2.AEth5
open Paper2.AEth3 (fOut cutLen cutLen_ge)

/-- The composite clock as ONE expression in seven atoms. -/
def GD (C : Paper2.SelectedTape.Algorithm) (pb m T fL L eL tl hL : ℕ) : ℕ :=
  (Paper2.AEth2.Cut.cutTimeG (2 ^ C.cR) 1 pb m T + 2 * (2 * fL + 1 + 2 ^ C.cR * L) + 2 +
      Paper2.SelectedTape.Bind.Retain.timeBound 1 1 Paper2.SelectedTape.Bind.idC
        Paper2.SelectedTape.Bind.idD Paper2.SelectedTape.Bind.idMachine.pushBound
        (2 * fL + 1 + 2 ^ C.cR * L)) +
    2 * (2 * (2 * fL + 1 + L) + 1 + 2 ^ C.cR * L) + 2 +
    ((2 * (2 * fL + 1 + L) +
        ((2 * fL + (2 * eL + 3) + 2 * eL + 6) + 2 * (2 * eL + 1 + L) + 2 + tl) +
        2 * hL + 6) +
      2 * (2 * hL + 1 + 2 ^ C.cR * L) + 2 + clsTime C hL (2 ^ C.cR * L))

/-- `GD` at one common bound. -/
def GDH (C : Paper2.SelectedTape.Algorithm) (pb H : ℕ) : ℕ := GD C pb H H H H H H H

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem decTime_eq (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) :
    decTime D B C K N₁ hN₁ w =
      GD C (inner4 K N₁).pushBound w.length (inner4Time K N₁ w)
        (fOut (routedV K N₁ hN₁ w).val).length (cutLen (routedV K N₁ hN₁ w).val)
        (EncodedCNF.encode (routedV K N₁ hN₁ w).val).length (tailTime D B (routedV K N₁ hN₁ w))
        (hwLen D B (routedV K N₁ hN₁ w)) := rfl

theorem clsTime_mono (C : Paper2.SelectedTape.Algorithm) {X Y X' Y' : ℕ} (hX : X ≤ X') (hY : Y ≤ Y') :
    clsTime C X Y ≤ clsTime C X' Y' := by
  unfold clsTime
  have h1 := trunc_timeBound_mono C.cR C.dR Paper2.SelectedTape.Bind.idC Paper2.SelectedTape.Bind.idD
    Paper2.SelectedTape.Bind.idMachine.pushBound (show 2 * X + 1 + Y ≤ 2 * X' + 1 + Y' by omega)
  gcongr

theorem GD_mono (C : Paper2.SelectedTape.Algorithm) (pb : ℕ) {m T fL L eL tl hL H : ℕ}
    (hm : m ≤ H) (hT : T ≤ H) (hf : fL ≤ H) (hL1 : L ≤ H) (he : eL ≤ H) (ht : tl ≤ H) (hh : hL ≤ H) :
    GD C pb m T fL L eL tl hL ≤ GDH C pb H := by
  unfold GDH GD
  have h1 := cutTimeG_mono (2 ^ C.cR) 1 pb hm hT
  have hY : 2 ^ C.cR * L ≤ 2 ^ C.cR * H := Nat.mul_le_mul_left _ hL1
  have h2 := retain_timeBound_mono Paper2.SelectedTape.Bind.idC Paper2.SelectedTape.Bind.idD
    Paper2.SelectedTape.Bind.idMachine.pushBound
    (show 2 * fL + 1 + 2 ^ C.cR * L ≤ 2 * H + 1 + 2 ^ C.cR * H by omega)
  have h3 := clsTime_mono C hh hY
  gcongr

theorem GDH_mono (C : Paper2.SelectedTape.Algorithm) (pb : ℕ) {H H' : ℕ} (h : H ≤ H') :
    GDH C pb H ≤ GDH C pb H' :=
  GD_mono C pb h h h h h h h

set_option maxRecDepth 20000 in
theorem GDH_poly (C : Paper2.SelectedTape.Algorithm) (pb : ℕ) :
    Paper2.Unit4Shell.Poly.PolyIn id (GDH C pb) := by
  unfold GDH GD Paper2.AEth2.Cut.cutTimeG Paper2.SelectedTape.Bind.Retain.timeBound clsTime
    NPOwner1.Trunc.timeBound
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

/-- Composition of a fixed polynomial after a fixed polynomial. -/
theorem polyIn_comp {F G : ℕ → ℕ} (hF : Paper2.Unit4Shell.Poly.PolyIn id F)
    (hG : Paper2.Unit4Shell.Poly.PolyIn id G) :
    Paper2.Unit4Shell.Poly.PolyIn id (fun Y => F (G Y)) := by
  refine Paper2.Unit4Shell.Poly.transfer (sz := G) hG ?_
  obtain ⟨C, E, h⟩ := hF
  exact ⟨C, E, fun i => h (G i)⟩

/-- The front-cut atoms are below the front clock, on EVERY word. -/
theorem front_atoms (K N₁ : ℕ) (w : List Bool) :
    w.length ≤ frontTime4 K N₁ w ∧ inner4Time K N₁ w ≤ frontTime4 K N₁ w ∧
      (fOut (routed4 K N₁ w)).length ≤ frontTime4 K N₁ w ∧
      cutLen (routed4 K N₁ w) ≤ frontTime4 K N₁ w ∧
      (EncodedCNF.encode (routed4 K N₁ w)).length ≤ frontTime4 K N₁ w := by
  unfold frontTime4 Paper2.AEth2.Cut.cutTimeG
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The front clock and the header tail clock are below the header clock, on EVERY word. -/
theorem hd_split (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) :
    frontTime4 K N₁ w + tailTime D B (routedV K N₁ hN₁ w) ≤ hdTime4 D B K N₁ hN₁ w := by
  simp only [hdTime4, tailTime]
  omega

/-- **Every atom of the composite clock is below the header clock `hdTime4`, on EVERY word**
(for `N₁` beyond the decider cutoff and the header-size cutoff, `2 ≤ K N₁`). -/
theorem decTime_le (C : Paper2.SelectedTape.Algorithm) (K : ℕ) :
    ∃ N₀ : ℕ, ∀ N₁ (hN₁ : 1 ≤ N₁), N₀ ≤ N₁ → 2 ≤ K * N₁ → ∀ w : List Bool,
      decTime D B C K N₁ hN₁ w ≤ GDH C (inner4 K N₁).pushBound (hdTime4 D B K N₁ hN₁ w) := by
  obtain ⟨Nh, hNh⟩ := hw_fit D B K 1
  refine ⟨max (N0 D B C K) Nh, fun N₁ hN₁ hle hK w => ?_⟩
  have hN0 : N0 D B C K ≤ N₁ := le_trans (le_max_left _ _) hle
  have hNh1 : Nh ≤ N₁ := le_trans (le_max_right _ _) hle
  set Φ := routedV K N₁ hN₁ w with hΦ
  have hvars : N₁ ≤ Φ.val.variables := routed4_variables K N₁ w
  have hsp : Φ.val.clauses.length ≤ K * Φ.val.variables := routed4_sparse K N₁ hK w
  -- a typed tape of the selected output (from the decider run on the all-false tape)
  obtain ⟨-, t', -⟩ := (N0_spec D B C K).2 N₁ hN₁ hN0 hK w
    (List.replicate (2 ^ C.cR * L1 K N₁ w) false) (by simp)
  have hfit := (hNh Φ hsp (le_trans hNh1 hvars)).2 t'
  rw [pow_one, hw_length_eq] at hfit
  have hcl := cutLen_ge Φ.val
  obtain ⟨a1, a2, a3, a4, a5⟩ := front_atoms K N₁ w
  have hs := hd_split D B K N₁ hN₁ w
  have e3 : (fOut Φ.val).length = (fOut (routed4 K N₁ w)).length := rfl
  have e4 : cutLen Φ.val = cutLen (routed4 K N₁ w) := rfl
  have e5 : (EncodedCNF.encode Φ.val).length = (EncodedCNF.encode (routed4 K N₁ w)).length := rfl
  rw [decTime_eq]
  apply GD_mono
  · omega
  · omega
  · rw [e3]; omega
  · rw [e4]; omega
  · rw [e5]; omega
  · omega
  · rw [← hΦ]; rw [e4] at hcl; omega

/-- **Segment 2 (clock): the composite decider's clock is inside the D-A6 budget** on sparse valid
inputs, for every `ε > 0` eventually. -/
theorem decTime_budget (C : Paper2.SelectedTape.Algorithm) (K : ℕ) :
    ∃ N₀ : ℕ, ∀ N₁ (hN₁ : 1 ≤ N₁), N₀ ≤ N₁ → 2 ≤ K * N₁ → ∀ ε : ℝ, 0 < ε →
      ∃ C' d N₂ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ K * Φ.val.variables →
        N₂ ≤ Φ.val.variables →
        decTime D B C K N₁ hN₁ (EncodedCNF.encode Φ.val) ≤
          C' * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ * ((EncodedCNF.encode Φ.val).length + 1) ^ d := by
  obtain ⟨N₀, hN₀⟩ := decTime_le D B C K
  refine ⟨N₀, fun N₁ hN₁ hle hK ε hε => ?_⟩
  obtain ⟨N₂, hN₂⟩ := hdTime4_dom D B K N₁ hN₁
  have hP := polyIn_comp (GDH_poly C (inner4 K N₁).pushBound) (P4_poly D B K N₁)
  exact budget_of_dom D B K (Paper2.AEth3.K0 D B + 164) (fun Φ => decTime D B C K N₁ hN₁ (EncodedCNF.encode Φ.val))
    (fun Y => GDH C (inner4 K N₁).pushBound (P4 D B K N₁ Y)) hP N₂
    (fun Φ hsp hN => le_trans (hN₀ N₁ hN₁ hle hK _) (GDH_mono C _ (hN₂ Φ hsp hN))) ε hε

end Paper2.AEth6

end

#print axioms Paper2.AEth6.decTime_eq
#print axioms Paper2.AEth6.clsTime_mono
#print axioms Paper2.AEth6.GD_mono
#print axioms Paper2.AEth6.GDH_poly
#print axioms Paper2.AEth6.polyIn_comp
#print axioms Paper2.AEth6.front_atoms
#print axioms Paper2.AEth6.hd_split
#print axioms Paper2.AEth6.decTime_le
#print axioms Paper2.AEth6.decTime_budget
