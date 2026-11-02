import CurrentAdditive.V42GeneratedConstruction
import CurrentAdditive.V42ActualGeneratedSource
import CurrentAdditive.V42ActualInternal
import CurrentAdditive.V42RestorationGuards
import CurrentAdditive.V39StoredSeedProfile

/-! The new explicit schedule's actual seven-call successor and iteration.
The graph promise and base profile prove the next profile; neither is stored
in the constructor. All source, alignment and restoration guards are derived
from the explicit public cutoff. -/
namespace CurrentAdditive.V42GeneratedNo

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42Schedule V39GeneratedConstruction V39GeneratedSourceBridge
open CurrentAdditive.DeterministicIndexedMatrix

private theorem law_ext {A : Type} [Fintype A] (μ ν : PositiveRationalLaw A)
    (h : μ.weight=ν.weight) : μ=ν := by cases μ; cases ν; cases h; rfl

local instance sNZ (k : ℕ) : NeZero (s k) := ⟨(s_pos k).ne'⟩
local instance q₂NZ (k : ℕ) : NeZero (q₂ k (4*k)) := ⟨(q₂_pos k (4*k)).ne'⟩
local instance wNZ (k : ℕ) : NeZero (w k) := ⟨(w_pos k).ne'⟩
local instance QNZ (k : ℕ) : NeZero (Q k) := ⟨(Q_pos k).ne'⟩

variable {k n m nx ny rep : ℕ} [NeZero (q₁ k)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}

theorem successor_no
    (src : SourceData (D := 8192) (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k) μX μY)
    (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k)
    (hs : 4 ≤ s k) (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : Fin nx → Fin ny → Bool) (d : ℕ) (hd : 2 ≤ d) (hD : D R=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      (rho (4*k):ℝ) (d:ℤ))
    (st : src.Streams (w := w k) (μI := LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn))
    (out : ExactList 8192 (Q k) (Fin (w k) × src.Column)
      (product (uniform (w k)) src.columnLaw)) :
    D (src.successor st out R (graphActivity (by omega) hwidth edge))=d+40*k+1 ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (src.successor st out R (graphActivity (by omega) hwidth edge))
      out.law.toFiniteLaw (product (uniform (Q k)) (SourceData.Streams.law src st)).toFiniteLaw
      (rho (4*k):ℝ) ((d+40*k+1:ℕ):ℤ) := by
  classical
  have hδ : 0 < V38Schedule.sourceDeltaV γ Δ n m := by unfold V38Schedule.sourceDeltaV; positivity
  have hζ : 0 < V38Schedule.sourceZeta γ := by unfold V38Schedule.sourceZeta; positivity
  have hk200 := (cutoff_small _ _ Δ k hδ hζ hk).1
  have hs3 : 3 ≤ s k := by omega
  let μItem := LiteralEdgeEncoder.itemLaw (s k) n hs hn
  let act := graphActivity hs3 hwidth edge
  let actItem := fun i α => act (LiteralEdgeEncoder.itemNumber (s k) n i) α
  let ξ₀ : Tail (s k) (Fin ny) := fun _ => Classical.choice μY.nonempty
  obtain ⟨_,_,hA,hT,href⟩ := V42GeneratedSourceProfiles.costs_and_profiles
    (toSources src) μItem R actItem ξ₀ d hk200 hd hD hp
  have hrow : V39IndexedReferenceProfile.rowLaw (toSources src) μItem =
      Sources.rowLaw (toSources src) μItem := by
    apply law_ext
    funext a
    cases a <;> rfl
  rw [hrow] at href
  have g := V42RestorationGuards.generated_guards k hk200
  have a := g.alignment
  have hnear := V42ActualGeneratedSource.nearfull src γ Δ hγ hΔ hn hm hk hs
    hwidth edge loopless hdegree gap R d hd hD hp
  have hu := V42ActualGeneratedSource.source_upper src hs hwidth edge R d hD
  have h := V42ActualInternal.indexed_restoration src hs hn st R act ξ₀
    (d+k) (4*k+2*k) k (8*k) (ownerBudget k)
    (x (4*k):ℝ) (theta k:ℝ) (eta k:ℝ)
    (by omega) a.r_ge a.w_pow a.q_pow a.s_pow a.x_pos a.theta_pos a.eta_pos
    hA hT href (by intro U Z hU hZ; exact hnear Z U hZ hU)
    a.cap a.exc a.receipt a.init a.wx a.two_x a.loss a.width a.foreign a.floor
    a.pair_margin a.small a.pair_small a.flag a.exception a.theta_le_one
    a.profile_exception a.profile_wx hu
    (Q k) (24*k) out g.Q_pow (rho (4*k):ℝ) g.phi_pos g.phi_le_one
    g.restoration_width g.restoration_scale
  have he : d+k+(4*k+2*k)+k+1+8*k+24*k=d+40*k+1 := by omega
  simpa only [he] using h

theorem numberedStep_no
    (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k)
    (hk2 : 2 ≤ k) (hs : 4 ≤ s k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : NumberedMatrix) (d : ℕ) (hd : 2 ≤ d) (hD : D R.entry=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R.entry R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw
      (rho (4*k):ℝ) (d:ℤ)) :
    let out := V42GeneratedConstruction.numberedStep k (4*k) hk2
      (LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn) (graphActivity (by omega) hwidth edge) R
    D out.entry=d+40*k+1 ∧ V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw (rho (4*k):ℝ) ((d+40*k+1:ℕ):ℤ) := by
  let src := sourceData (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k)
    (executableCodeD 8192) R.rowLaw R.colLaw
  let st := SourceData.streams (w := w k) (executableCodeD 8192) src
    (μI := LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn)
  let out := SourceData.final (w := w k) (Q := Q k) (executableCodeD 8192) src
  have h := successor_no src γ Δ hγ hΔ hn hm hk hs hwidth edge loopless hdegree gap R.entry d hd hD hp st out
  exact ⟨(src.numbered_cost st out R.entry _).trans h.1,
    src.numbered_profile st out R.entry _ _ _ h.2⟩

#print axioms successor_no
#print axioms numberedStep_no

end CurrentAdditive.V42GeneratedNo

