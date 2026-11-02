import CurrentAdditive.V40GeneratedTestPairs
namespace CurrentAdditive.V40GeneratedTestEquivalence
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
open V38Schedule V39GeneratedConstruction V40GeneratedFractions V40GeneratedTestPairs

theorem denominator_positive (p : SourceConstants) (n m L : Nat) (hn : 0<n) :
    ∀ i, 0<(fractionPairs p n m L i).1.den ∧ 0<(fractionPairs p n m L i).2.den := by
  have hs : 0<generatedS L := by unfold generatedS; positivity
  have hN : 0<generatedN L := by unfold generatedN; positivity
  have hw : 0<generatedW L := by unfold generatedW; positivity
  have hQ : 0<generatedQ L := by unfold generatedQ; positivity
  have hd := p.deletion.den_pos
  have hg := p.gamma.den_pos
  have hp := p.degree_pos
  have hC := C128.den_pos
  intro i
  fin_cases i <;>
    simp only [fractionPairs,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
    dsimp only [Fr.nat,Fr.mul,Fr.div,Fr.divNat,Fr.pow,Fr.ofRat,
      etaFr,deltaFr,zetaFr,rhoFr,xFr,scaledEtaFr,c128Fr] <;>
    constructor <;> positivity

theorem fractions_iff_literal (p : SourceConstants) (n m L : Nat) (hn : 0<n) :
    fractionTests p n m L ↔ literalTests p n m L := by
  unfold fractionTests literalTests literalPairs
  apply forall_congr'
  intro i
  exact Fr.cross_iff _ _ (denominator_positive p n m L hn i).1
    (denominator_positive p n m L hn i).2

/-- This is the actual source test, expanded without any large-candidate
assumption. The minimum comparison becomes its three literal comparisons. -/
theorem generated_iff_fractions (p : SourceConstants) (n m L : Nat) :
    GeneratedTests p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma) ↔
      fractionTests p n m L := by
  unfold GeneratedTests CommonTests
  dsimp only [generatedInput]
  rw [le_div_iff₀ (by norm_num : (0:ℚ)<2^16),le_min_iff,le_min_iff]
  simp only [fractionTests,fractionPairs,Fin.forall_fin_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fr.nat_value,Fr.mul_value,Fr.div_value,
    Fr.divNat_value,Fr.pow_value,eta_value,delta_value,zeta_value,rho_value,x_value,
    scaledEta_value,c128_value,unitCount_eq,etaCount_eq,restCount_eq,
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_le]
  simp only [generatedQlog,Eexc,e0,theta,deltaU,mul_assoc,div_eq_mul_inv,one_mul]
  have hz (P : Fin 0 → Prop) : (∀ i,P i) ↔ True := ⟨fun _ => trivial,fun _ i => Fin.elim0 i⟩
  simp only [hz,and_true,Nat.cast_one,one_mul,←Nat.cast_mul,←Nat.cast_pow,Nat.cast_le]
  norm_cast
  tauto

/-- Exact all-candidate scalar specification for the physical twenty-test
compiler. The sole input guard is n>0; m=0 and every failed early L remain
covered. No sufficient cutoff replaces any test. -/
theorem generated_iff_literal (p : SourceConstants) (n m L : Nat) (hn : 0<n) :
    GeneratedTests p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma) ↔
      literalTests p n m L :=
  (generated_iff_fractions p n m L).trans (fractions_iff_literal p n m L hn)

instance literalDecidable (p : SourceConstants) (n m L : Nat) : Decidable (literalTests p n m L) := by
  unfold literalTests
  infer_instance

theorem generatedPass_eq_literal (p : SourceConstants) (n m L : Nat) (hn : 0<n) :
    generatedPass p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma)=
      decide (literalTests p n m L) := by
  unfold generatedPass
  congr 1
  exact propext (generated_iff_literal p n m L hn)

#print axioms denominator_positive
#print axioms generated_iff_literal
#print axioms generatedPass_eq_literal
end
end CurrentAdditive.V40GeneratedTestEquivalence
