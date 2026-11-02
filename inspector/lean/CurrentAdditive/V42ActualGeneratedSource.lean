import CurrentAdditive.V42GeneratedSourceProfiles
import CurrentAdditive.V42SourceNearFullGuards
import CurrentAdditive.V39GeneratedNearFullCast
import CurrentAdditive.V39GraphGenerated

/-! Replacement v42 `src:near-full` for the actual three-call source.
The external graph violation gap is explicit.  The source lower bound,
retained collisions, forced prefix, and marked recursion are proved by
the existing generic current-profile argument, with the revised recipe. -/

namespace CurrentAdditive.V42ActualGeneratedSource

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicIndexedMatrix CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge
open Workspace.Types.CommComplexity V42Schedule

def sourceCost (d k : ℕ) : ℕ := d+k+(4*k+2*k)+k+1

theorem sourceCost_eq (d k : ℕ) : sourceCost d k=d+8*k+1 := by
  unfold sourceCost; omega

theorem sourceCost_logs (d k : ℕ) :
    sourceCost d k=d+2*Nat.clog 2 (s k)+Nat.clog 2 (q₂ k (4*k))+1 := by
  simp only [s,q₂,Nat.clog_pow 2 _ (by decide)]
  unfold sourceCost; omega

variable {k n m nx ny rep : ℕ}
  [NeZero (q₁ k)] [NeZero (q₂ k (4*k))] [NeZero (s k)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  (src : SourceData (D := 8192) (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k) μX μY)

theorem nearfull
    (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k)
    (hs : 4 ≤ s k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ)*m ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (R : Fin nx → Fin ny → Bool) (d : ℕ) (hd : 2 ≤ d) (hD : D R=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      (rho (4*k) : ℝ) (d : ℤ))
    (W : Set (src.Row (ni := 4*(s k)*(n+(s k-3))))) (U : Set src.Column)
    (hW : 1-(eta k : ℝ) ≤
      (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn)).toFiniteLaw.prob (· ∈ W))
    (hU : 1-(eta k : ℝ) ≤ src.columnLaw.toFiniteLaw.prob (· ∈ U)) :
    sourceCost d k ≤ Compression.restrictionD
      (fun col row => src.B R (graphActivity (by omega) hwidth edge) row col) U W := by
  classical
  letI : NeZero (2^k-2) := ⟨by exact NeZero.ne (q₁ k)⟩
  let μI := LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn
  let act := graphActivity (by omega : 3 ≤ s k) hwidth edge
  let ξ₀ : Tail (s k) (Fin ny) := fun _ => Classical.choice μY.nonempty
  have hδ : 0 < V38Schedule.sourceDeltaV γ Δ n m := by
    unfold V38Schedule.sourceDeltaV; positivity
  have hζ : 0 < V38Schedule.sourceZeta γ := by
    unfold V38Schedule.sourceZeta; positivity
  have hk200 := (cutoff_small _ _ Δ k hδ hζ hk).1
  obtain ⟨_hDA,_hDT,hA,hT,_hRef⟩ := V42GeneratedSourceProfiles.costs_and_profiles
    (toSources src) μI R act ξ₀ d hk200 hd hD hp
  obtain ⟨hη,hηsmall,hηtemplate,hallow,hassign,hmargin,hsmall,hprefix,hdominant⟩ :=
    V42SourceNearFullGuards.source_guards γ Δ k n m hγ hΔ hn hm hk
  obtain ⟨_ha,_hb,hρ,hx,_hx1,_hrest⟩ :=
    V42GeneratedProfileGuards.scalar_parameters k hk200
  have hqpow : q₂ k (4*k)=2^(4*k+2*k) := rfl
  have hq2 : 2 ≤ q₂ k (4*k) := by
    rw [hqpow]
    exact (by norm_num : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hA' : V38RestrictionProfiles.TwoThresholdProfile (Sources.A (toSources src) R)
      src.gamma.law.toFiniteLaw (product (uniform (q₁ k)) μX).toFiniteLaw
      (x (4*k) : ℝ) ((d+k : ℕ) : ℤ) := by
    simpa only [uniform_eq,product_eq] using hA
  have hT' : V38RestrictionProfiles.TwoThresholdProfile (V39GeneratedPrefix.template src R)
      src.inner.law.toFiniteLaw (product (uniform (q₂ k (4*k))) src.gamma.law).toFiniteLaw
      (x (4*k) : ℝ) ((d+k+(4*k+2*k) : ℕ) : ℤ) := by
    simpa only [V39GeneratedPrefix.template_eq,uniform_eq,product_eq] using hT
  exact V39GeneratedNearFullCast.restriction_lower src hwidth (by norm_num) hs hn
    edge loopless Δ hΔ hdegree (γ : ℝ) (by exact_mod_cast hγ) hm gap R d (4*k+2*k) hd hqpow hq2
    (x (4*k) : ℝ) (rho (4*k) : ℝ) (eta k : ℝ)
    hx hρ hη hηsmall hηtemplate hallow hassign hmargin hsmall hprefix hdominant
    hp hA' hT' W U hW hU

theorem source_upper (hs : 4 ≤ s k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (R : Fin nx → Fin ny → Bool) (d : ℕ) (hD : D R=d) :
    D (fun col row => src.B R (graphActivity (by omega) hwidth edge) row col) ≤ sourceCost d k := by
  rw [transpose_D]
  have hupper := src.B_upper R (graphActivity (by omega : 3 ≤ s k) hwidth edge)
  have hlogS : Nat.clog 2 (s k)=k := by simp [s]
  have hlogQ : Nat.clog 2 (q₂ k (4*k))=4*k+2*k := by simp [q₂]
  have hlogTail : Nat.clog 2 (q₁ k+s k+1) ≤ k+1 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    rw [pow_succ]
    change s k-2+s k+1 ≤ (s k)*2
    omega
  rw [hlogS,hlogQ,hD] at hupper
  dsimp only [sourceCost]
  omega

theorem source_exact
    (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k)
    (hs : 4 ≤ s k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ)*m ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (R : Fin nx → Fin ny → Bool) (d : ℕ) (hd : 2 ≤ d) (hD : D R=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      (rho (4*k) : ℝ) (d : ℤ)) :
    D (fun col row => src.B R (graphActivity (by omega) hwidth edge) row col)=sourceCost d k := by
  apply Nat.le_antisymm (source_upper src hs hwidth edge R d hD)
  have hη : (0 : ℝ) < (eta k : ℝ) := by unfold eta; push_cast; positivity
  have hl := nearfull src γ Δ hγ hΔ hn hm hk hs hwidth edge loopless hdegree gap R d hd hD hp
    Set.univ Set.univ (by simp only [Set.mem_univ,FiniteLaw.prob_true]; linarith)
      (by simp only [Set.mem_univ,FiniteLaw.prob_true]; linarith)
  exact hl.trans (SourceProfilesInner.restrictionD_le _ Set.univ Set.univ)

#print axioms nearfull
#print axioms source_upper
#print axioms source_exact

end CurrentAdditive.V42ActualGeneratedSource
