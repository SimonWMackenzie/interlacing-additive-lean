import CurrentAdditive.V40RandomizedPhysicalClockFits
import CurrentAdditive.V40RandomizedETHClock
import CurrentAdditive.V40SourceClassifierRun

/-! The concrete source-cut/request/classifier clock is bounded in the
original number of source variables. No completed-run or clock premise. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V38Schedule V39PublicSchedule
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

private theorem cap_arithmetic (bw J m U gl k L raw entries : ℕ)
    (hg : gl ≤ U) (hk : k ≤ m) (hL : L=2*m+2*U+3)
    (hr : raw+entries ≤ U) :
    2*(bw+2*(gl+k+L)+3)+1+J*L ≤ (2*bw+30+3*J)*(m+U+1) ∧
    (bw+2*(gl+k+L)+3)+raw+entries+J*L+1 ≤
      (2*bw+30+3*J)*(m+U+1) := by
  have hY : 1 ≤ m+U+1 := by omega
  have hLs : L ≤ 3*(m+U+1) := by omega
  have hJL := Nat.mul_le_mul_left J hLs
  have hbw : bw ≤ bw*(m+U+1) := by nlinarith
  have hb : bw+2*(gl+k+L)+3 ≤ (bw+10)*(m+U+1) := by nlinarith
  constructor <;> nlinarith

def callerTailPoly (C : SelectedTape.Algorithm) (x : ℕ) :=
  2*x+2+V40RawClassifierClock.cap C x

theorem callerTailPoly_poly (C : SelectedTape.Algorithm) :
    Unit4Shell.Poly.PolyIn id (callerTailPoly C) := by
  exact Unit4Shell.Poly.add
    (Unit4Shell.Poly.add (Unit4Shell.Poly.mul (Unit4Shell.Poly.const 2) Unit4Shell.Poly.self)
      (Unit4Shell.Poly.const 2)) (V40RawClassifierClock.cap_poly C)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem actual_size_caps_sparse (C : SelectedTape.Algorithm) (cs cutoff : ℕ)
    (hcut : 1 ≤ cutoff) :
    ∃ A N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      V40SourceClassifier.frontWordCap D B C cs cutoff hcut (EncodedCNF.encode Φ.val) ≤
        A*((EncodedCNF.encode Φ.val).length+AEth.expLen Φ.val.variables+1) ∧
      V40SourceClassifier.sizeCap D B C cs cutoff hcut (EncodedCNF.encode Φ.val) ≤
        A*((EncodedCNF.encode Φ.val).length+AEth.expLen Φ.val.variables+1) := by
  obtain ⟨Nr,hr⟩ := raw_clock_and_entries_fit (D.sizeExponent+2)
  obtain ⟨Ng,hg⟩ := graph_bytes_fit (D.sizeExponent+2)
  refine ⟨2*V40SourceClassifier.bankWidth+30+3*2^(classifierBlockExponent C),
    cutoff+Nr+Ng+V39SourceGeometry.originalCutoff D B cs,?_⟩
  intro Φ hsp hN
  have hsp' : Φ.val.clauses.length ≤ (cs+2)*Φ.val.variables :=
    hsp.trans (Nat.mul_le_mul_right _ (by omega))
  have hroute : V40SourceClassifier.routed cs cutoff hcut (EncodedCNF.encode Φ.val)=Φ :=
    Subtype.ext (AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property hsp' (by omega))
  have hgraph : V40SourceClassifier.graph D B cs cutoff hcut (EncodedCNF.encode Φ.val)=
      t10Graph D B Φ := by unfold V40SourceClassifier.graph; rw [hroute]
  have hgap : V40SourceClassifier.gap cs cutoff hcut (EncodedCNF.encode Φ.val)=
      kOf Φ.val.variables := by unfold V40SourceClassifier.gap; rw [hroute]
  have hblock : V40SourceClassifier.blockLength cs cutoff (EncodedCNF.encode Φ.val)=
      2*(EncodedCNF.encode Φ.val).length+2*AEth.expLen Φ.val.variables+3 := by
    change AEth3.cutLen (AEth4.routed4 (cs+2) cutoff (EncodedCNF.encode Φ.val))=_
    rw [AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property hsp' (by omega),AEth3.cutLen_eq]
  obtain ⟨facts,ht,hsize⟩ := V39SourceGeometry.source_all_large D B cs Φ hsp (by omega)
  have hraw := hr Φ.val.variables (by omega) (t10Graph D B Φ) facts.valid
    facts.vertices_pos hsize _ _ _ ht
  have hbytes := hg Φ.val.variables (by omega) (t10Graph D B Φ) facts.valid
    facts.vertices_pos hsize _ _ _ ht
  have hk : kOf Φ.val.variables ≤ (EncodedCNF.encode Φ.val).length :=
    (Nat.div_le_self _ _).trans (AEth.encode_length_ge Φ.val)
  unfold V40SourceClassifier.frontWordCap V40SourceClassifier.sizeCap
    V40SourceClassifier.bankInputCap
  rw [hgraph,hgap,hblock]
  exact cap_arithmetic _ _ _ _ _ _ _ _ _ hbytes hk rfl hraw

/-- Every transition in the concrete caller, including the source and
bounded tape cut, satisfies the sparse source budget in original N. -/
theorem actual_time_sparse (C : SelectedTape.Algorithm) (cs cutoff : ℕ)
    (hcut : 1 ≤ cutoff) (ε : ℝ) (hε : 0<ε) :
    ∃ K d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      V40SourceClassifier.time D B C cs cutoff hcut (EncodedCNF.encode Φ.val) ≤
        K*⌈(2:ℝ)^(ε*Φ.val.variables)⌉₊*((EncodedCNF.encode Φ.val).length+1)^d := by
  obtain ⟨A,Ns,hs⟩ := actual_size_caps_sparse D B C cs cutoff hcut
  obtain ⟨K₁,d₁,N₁,h₁⟩ := polynomial_of_source_prefix_subexponential
    (callerTailPoly C) (callerTailPoly_poly C) A ε hε
  obtain ⟨K₂,d₂,N₂,h₂⟩ := V40SourceClassifier.sourceClock_sparse D B C cs cutoff hcut ε hε
  refine ⟨K₁+K₂,d₁+d₂,max Ns (max N₁ N₂),?_⟩
  intro Φ hsp hN
  obtain ⟨hfront,hsize⟩ := hs Φ hsp ((le_max_left _ _).trans hN)
  have hcap := V40SourceClassifier.caller_cap_mono C hsize
  have htail := h₁ Φ.val.variables ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    (EncodedCNF.encode Φ.val).length (AEth.encode_length_ge Φ.val)
  have hsource := h₂ Φ hsp ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have htail' : 2*V40SourceClassifier.frontWordCap D B C cs cutoff hcut (EncodedCNF.encode Φ.val)+2+
      V40RawClassifierClock.cap C (V40SourceClassifier.sizeCap D B C cs cutoff hcut (EncodedCNF.encode Φ.val)) ≤
      K₁*⌈(2:ℝ)^(ε*Φ.val.variables)⌉₊*((EncodedCNF.encode Φ.val).length+1)^d₁ := by
    apply (show _ ≤ callerTailPoly C (A*((EncodedCNF.encode Φ.val).length+AEth.expLen Φ.val.variables+1)) by
      unfold callerTailPoly; omega).trans htail
  have hp₁ : ((EncodedCNF.encode Φ.val).length+1)^d₁ ≤
      ((EncodedCNF.encode Φ.val).length+1)^(d₁+d₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp₂ : ((EncodedCNF.encode Φ.val).length+1)^d₂ ≤
      ((EncodedCNF.encode Φ.val).length+1)^(d₁+d₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have htail'' := htail'.trans (Nat.mul_le_mul_left _ hp₁)
  have hsource' := hsource.trans (Nat.mul_le_mul_left _ hp₂)
  unfold V40SourceClassifier.time
  calc
    _ ≤ K₂*⌈(2:ℝ)^(ε*Φ.val.variables)⌉₊*((EncodedCNF.encode Φ.val).length+1)^(d₁+d₂)+
        K₁*⌈(2:ℝ)^(ε*Φ.val.variables)⌉₊*((EncodedCNF.encode Φ.val).length+1)^(d₁+d₂) := by omega
    _ = _ := by ring

#print axioms actual_size_caps_sparse
#print axioms actual_time_sparse
end
end CurrentAdditive.V40RandomizedETHEndpoint
