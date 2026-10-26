import CurrentAdditive.V39ActualItemStreams
import CurrentAdditive.V39GeneratedNearFullCast
import CurrentAdditive.V39GeneratedSourceProfiles
import CurrentAdditive.V39GeneratedNearFullGuards

namespace CurrentAdditive.V39ActualGeneratedSource

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicIndexedMatrix CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge
open Workspace.Types.CommComplexity V38Schedule

def sourceCost (d L : ℕ) : ℕ := d+quarterCeil L+4*L+quarterCeil L+1

variable {L n m nx ny rep : ℕ}
  [NeZero (generatedQ₁ L)] [NeZero (generatedQ₂ L)] [NeZero (generatedS L)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
    (s := generatedS L) μX μY)

def activity (hs : 4 ≤ generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) :=
  fun i α => LiteralEdgeEncoder.indexedActivity (by omega : 3 ≤ generatedS L) edge i (Fin.cast hwidth α)

theorem nearfull_of_tests
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4 ≤ generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ)*m ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (R : Fin nx → Fin ny → Bool) (d : ℕ) (hd : 2 ≤ d) (hD : D R=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) (d : ℤ))
    (W : Set (src.Row (ni := 4*(generatedS L)*(n+(generatedS L-3)))))
    (U : Set src.Column)
    (hW : 1-((generatedEta c L : ℚ) : ℝ) ≤
      (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)).toFiniteLaw.prob (· ∈ W))
    (hU : 1-((generatedEta c L : ℚ) : ℝ) ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U)) :
    sourceCost d L ≤ Compression.restrictionD
      (fun col row => src.B R (activity hs hwidth edge) row col) U W := by
  classical
  letI : NeZero (2^quarterCeil L-2) := ⟨by
    have hh := NeZero.ne (generatedQ₁ L)
    exact hh⟩
  let μI := LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn
  let act := activity hs hwidth edge
  let ξ₀ : Tail (generatedS L) (Fin ny) := fun _ => Classical.choice μY.nonempty
  obtain ⟨_hDA,_hDT,hA,hT,_hRef⟩ := V39GeneratedSourceProfiles.costs_and_profiles_of_tests
    (toSources src) μI R act ξ₀ d c (sourceDeltaV γ Δ n m) (sourceZeta γ) m htests hd hD hp
  obtain ⟨hη,hηsmall,hηtemplate,hallow,hassign,hmargin,hsmall,hprefix,hdominant⟩ :=
    V39GeneratedNearFullGuards.source_guards γ c Δ L n m hc hγ hΔ hn hm htests
  obtain ⟨_ha,hell,hρ,hx,_hx1,_hrest⟩ := V39GeneratedProfileGuards.scalar_parameters
    c (sourceDeltaV γ Δ n m) (sourceZeta γ) L m htests
  have hqpow : generatedQ₂ L=2^(4*L) := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    congr 1
    omega
  have hq2 : 2 ≤ generatedQ₂ L := by
    rw [hqpow]
    exact le_trans (by norm_num : 2 ≤ 2^2) (Nat.pow_le_pow_right (by decide) hell)
  have hA' : V38RestrictionProfiles.TwoThresholdProfile (Sources.A (toSources src) R)
      src.gamma.law.toFiniteLaw (product (uniform (generatedQ₁ L)) μX).toFiniteLaw
      ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L : ℕ) : ℤ) := by
    simpa only [uniform_eq,product_eq] using hA
  have hT' : V38RestrictionProfiles.TwoThresholdProfile (V39GeneratedPrefix.template src R)
      src.inner.law.toFiniteLaw (product (uniform (generatedQ₂ L)) src.gamma.law).toFiniteLaw
      ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L+4*L : ℕ) : ℤ) := by
    simpa only [V39GeneratedPrefix.template_eq,uniform_eq,product_eq] using hT
  exact V39GeneratedNearFullCast.restriction_lower src hwidth (by norm_num) hs hn
    edge loopless Δ hΔ hdegree (γ : ℝ) (by exact_mod_cast hγ) hm gap R d (4*L) hd hqpow hq2
    ((generatedX L : ℚ) : ℝ) ((generatedRho L : ℚ) : ℝ) ((generatedEta c L : ℚ) : ℝ)
    hx hρ hη hηsmall hηtemplate hallow hassign hmargin hsmall hprefix hdominant hp hA' hT' W U hW hU

theorem source_upper (hs : 4 ≤ generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (R : Fin nx → Fin ny → Bool) (d : ℕ) (hD : D R=d) :
    D (fun col row => src.B R (activity hs hwidth edge) row col) ≤ sourceCost d L := by
  rw [transpose_D]
  have hupper := src.B_upper R (activity hs hwidth edge)
  have hlogS : Nat.clog 2 (generatedS L)=quarterCeil L := by simp [generatedS]
  have hlogQ : Nat.clog 2 (generatedQ₂ L)=4*L := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    simp only [Nat.clog_pow,one_lt_two]
    omega
  have hlogTail : Nat.clog 2 (generatedQ₁ L+generatedS L+1) ≤ quarterCeil L+1 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    rw [pow_succ]
    change generatedS L-2+generatedS L+1 ≤ (generatedS L)*2
    omega
  rw [hlogS,hlogQ,hD] at hupper
  dsimp only [sourceCost]
  omega

end CurrentAdditive.V39ActualGeneratedSource

#print axioms CurrentAdditive.V39ActualGeneratedSource.nearfull_of_tests
#print axioms CurrentAdditive.V39ActualGeneratedSource.source_upper
