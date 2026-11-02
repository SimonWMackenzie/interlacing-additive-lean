import Paper2.TwoStreamConversation
import Paper2.TwoStreamOriginalInputs

/-!
# The two-stream lower bound from the original retained inputs

Frozen v12, Section 5, `res:two-stream`, lines 134--201. This endpoint
starts with the original matrix, its ambient laws and maps, and its
retained input sets. The common raw carrier, its law, the initial protocol
state and every terminal contradiction are constructed by the proof.
-/

namespace Paper2.TwoStreamObstruction

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open TwoStreamRawRows TwoStreamOriginalInputs TwoStreamInitial
open PairedSelectorPopulation

variable {B J Rw Ω F E : Type*} [Fintype B] [Fintype J]
  [Fintype Rw] [Fintype Ω] [Fintype F] [Fintype E]
  [DecidableEq E] {q s : ℕ} [NeZero q]

/-- A short protocol is impossible under the frozen two-stream hypotheses.
The paired-row rules are required only on the original retained `P0`.
Foreign entries outside that family are unrestricted. -/
theorem short_protocol_impossible
    (μ : PositiveRationalLaw B) (ν : PositiveRationalLaw J)
    (base : B → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q = 2 ^ ell) (hs : s = 2 ^ a)
    (x : ℝ) (hx : 0 < x)
    (hbase : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hT : RestrictionProfile
      (fun z : Fin q → J => fun c : Fin q × B => base c.2 (z c.1))
      (ν.iid q).toFiniteLaw (columnLaw μ).toFiniteLaw x ((H + ell : ℕ) : ℤ))
    (κΩ : FiniteLaw Ω) (κF : FiniteLaw F) (κE : FiniteLaw E)
    (bin : Rw → Fin s) (selector : Rw → Fin q → J)
    (Φ : Ω → Fin s → Fin q × B) (ψ : F → Fin q × B)
    (hordinary : ∀ r c, M r (.inl c) =
      base (Φ c (bin r)).2 (selector r (Φ c (bin r)).1))
    (hΦ : κΩ.PushesTo ((columnLaw μ).toFiniteLaw.iid s) Φ)
    (hψ : κF.PushesTo (columnLaw μ).toFiniteLaw ψ)
    (ι : E → Rw) (ζ : E → (Fin q → J) × (Fin q → J))
    (hζ : κE.PushesTo ((ν.iid q).toFiniteLaw.prod (ν.iid q).toFiniteLaw) ζ)
    (star : Fin s) (P0 : Finset E) (R : Set Rw) (O : Set Ω) (G : Set F)
    (hι : ∀ e ∈ P0, ι e ∈ R)
    (hstar : ∀ e ∈ P0, bin (ι e) = star ∧ selector (ι e) = (ζ e).1)
    (hforeign : ∀ e ∈ P0, ∀ f,
      M (ι e) (.inr f) = base (ψ f).2 ((ζ e).2 (ψ f).1))
    (hpair : 2 * s * x ≤ (ν.iid q).toFiniteLaw.prob
      (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)))
    (hrow : ∀ i ≠ star, 2 * s * x ≤ (ν.iid q).toFiniteLaw.prob
      (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z))
    (hretain : ∀ P' : Finset E, P' ⊆ P0 →
      SourceSupportStep.mass κE (P0 \ P') < 2 * s * x →
      (49 / 64 : ℝ) ≤ ((ν.iid q).toFiniteLaw.prod (ν.iid q).toFiniteLaw).prob
        (· ∈ ζ '' (P' : Set E)))
    (ε δ : ℝ) (hO : 1 - ε ≤ κΩ.prob (· ∈ O))
    (hF : δ ≤ κF.prob (· ∈ G)) (hδ : δ ≤ 1)
    (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ)
    (hsmall : 2 * s * x ≤ 1 / 8)
    (P : Protocol R (retainedColumns O G) Bool)
    (hP : P.Computes (fun r c => M r.val c.val))
    (hcost : P.cost ≤ H + ell + a) : False := by
  classical
  let μS := (ν.iid q).toFiniteLaw
  letI : Nonempty E := κE.nonempty
  letI : Nonempty Rw := ⟨ι (Classical.choice inferInstance)⟩
  let default : Fin q → J := Classical.choice μS.nonempty
  let σ := firstSelector ζ selector default
  let input := rawInput ι
  let supports := initialSupport star P0 (binRows R bin)
  have hspos : 0 < s := by rw [hs]; positivity
  have htpos : (0 : ℝ) < 2 * s * x := by positivity
  have hP0 : P0.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : (ν.iid q).toFiniteLaw.prob
        (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)) = 0 := by simp [he]
    rw [hz] at hpair
    linarith
  obtain ⟨e, he⟩ := hP0
  let row0 : R := ⟨ι e, hι e he⟩
  have hdense := (ordinary_density κΩ O q (NeZero.pos q) x ε δ hx.le
    hO hδ hslack).2.2
  obtain ⟨c, hc⟩ := columns_nonempty_of_mass κΩ O G (by linarith)
  let col0 : retainedColumns O G := ⟨c, hc⟩
  let init := initial R O G row0 col0 P star supports
  have hbin' : ∀ i, ∀ w ∈ supports i, bin (input w) = i :=
    supports_bin R bin ι star P0 (fun e he => (hstar e he).1)
  have hreach' : ∀ i, ∀ w ∈ supports i, input w ∈ R :=
    supports_retained R bin ι star P0 hι
  have hsel' : ∀ i, ∀ w ∈ supports i, σ w = selector (input w) :=
    supports_selector R bin ι ζ selector default star P0 (fun e he => (hstar e he).2)
  have hmass' : ∀ i, SourceSupportSchedule.floor s x 0 ≤
      ProjectedSupportStep.mass μS σ (supports i) := by
    simpa only [SourceSupportSchedule.floor_zero] using
      supports_floor μS R bin ζ selector default star P0 (2 * s * x) hpair hrow
  have hretain' := retention_transfer κE μS ζ selector default P0
    (2 * s * x) hretain
  have hforeign' : ∀ w ∈ supports star, ∀ f,
      M (input w) (.inr f) = base (ψ f).2
        ((jointSelector ζ selector default w).2 (ψ f).1) :=
    supports_foreign R bin ι ζ selector default star P0
      (fun r f => M r (.inr f)) (fun z f => base (ψ f).2 (z (ψ f).1)) hforeign
  have hprojected : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ ψ '' G) :=
    hF.trans (FiniteLaw.prob_le_image κF (columnLaw μ).toFiniteLaw ψ hψ G)
  have hpush : (pairedLaw (Rw := Rw) κE).PushesTo
      (PairedSelectorMatrix.selectorLaw ν q).toFiniteLaw
      (jointSelector ζ selector default) := by
    simpa only [PairedSelectorMatrix.selectorLaw, PositiveRationalLaw.toFiniteLaw_prod]
      using pairedLaw_pushes κE μS ζ selector default hζ
  apply TwoStreamConversation.no_short_transposed μ ν base M
    H ell a hH hq hs x hx hbase hT κΩ (pairedLaw κE)
    bin selector Φ ψ hordinary hΦ (jointSelector ζ selector default)
    hpush σ rfl input star init
    rfl rfl (fun i _ => hbin' i) (fun i _ => hsel' i)
    (fun i _ => hreach' i) (fun i _ => hmass' i)
    O G ?_ hforeign' ?_ ε δ hO hprojected hδ hslack ?_ ?_
  · exact ambientProtocol_computesOn M R O G row0 col0 P hP
  · simpa only [init, initial, supports, initialSupport_star,
      SourceSupportSchedule.floor_zero, PairedSelectorMatrix.selectorLaw,
      PositiveRationalLaw.toFiniteLaw_prod] using hretain'
  · simpa only [SourceSupportSchedule.floor_zero] using hsmall
  · simpa only [init, initial, ambientProtocol_cost] using hcost

/-- The final cost bound concerns the original retained matrix. It
assumes neither a frontier, an auxiliary row law nor a terminal lower bound. -/
theorem restriction_lower
    (μ : PositiveRationalLaw B) (ν : PositiveRationalLaw J)
    (base : B → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q = 2 ^ ell) (hs : s = 2 ^ a)
    (x : ℝ) (hx : 0 < x)
    (hbase : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hT : RestrictionProfile
      (fun z : Fin q → J => fun c : Fin q × B => base c.2 (z c.1))
      (ν.iid q).toFiniteLaw (columnLaw μ).toFiniteLaw x ((H + ell : ℕ) : ℤ))
    (κΩ : FiniteLaw Ω) (κF : FiniteLaw F) (κE : FiniteLaw E)
    (bin : Rw → Fin s) (selector : Rw → Fin q → J)
    (Φ : Ω → Fin s → Fin q × B) (ψ : F → Fin q × B)
    (hordinary : ∀ r c, M r (.inl c) =
      base (Φ c (bin r)).2 (selector r (Φ c (bin r)).1))
    (hΦ : κΩ.PushesTo ((columnLaw μ).toFiniteLaw.iid s) Φ)
    (hψ : κF.PushesTo (columnLaw μ).toFiniteLaw ψ)
    (ι : E → Rw) (ζ : E → (Fin q → J) × (Fin q → J))
    (hζ : κE.PushesTo ((ν.iid q).toFiniteLaw.prod (ν.iid q).toFiniteLaw) ζ)
    (star : Fin s) (P0 : Finset E) (R : Set Rw) (O : Set Ω) (G : Set F)
    (hι : ∀ e ∈ P0, ι e ∈ R)
    (hstar : ∀ e ∈ P0, bin (ι e) = star ∧ selector (ι e) = (ζ e).1)
    (hforeign : ∀ e ∈ P0, ∀ f,
      M (ι e) (.inr f) = base (ψ f).2 ((ζ e).2 (ψ f).1))
    (hpair : 2 * s * x ≤ (ν.iid q).toFiniteLaw.prob
      (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)))
    (hrow : ∀ i ≠ star, 2 * s * x ≤ (ν.iid q).toFiniteLaw.prob
      (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z))
    (hretain : ∀ P' : Finset E, P' ⊆ P0 →
      SourceSupportStep.mass κE (P0 \ P') < 2 * s * x →
      (49 / 64 : ℝ) ≤ ((ν.iid q).toFiniteLaw.prod (ν.iid q).toFiniteLaw).prob
        (· ∈ ζ '' (P' : Set E)))
    (ε δ : ℝ) (hO : 1 - ε ≤ κΩ.prob (· ∈ O))
    (hF : δ ≤ κF.prob (· ∈ G)) (hδ : δ ≤ 1)
    (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ)
    (hsmall : 2 * s * x ≤ 1 / 8) :
    H + ell + a + 1 ≤ Compression.restrictionD M R (retainedColumns O G) := by
  classical
  by_contra hn
  obtain ⟨P, hcost, hP⟩ := Nat.sInf_mem
    (Workspace.UpperBound.AchievableCosts_nonempty
      (fun (r : R) (c : retainedColumns O G) => M r.val c.val))
  apply short_protocol_impossible μ ν base M H ell a hH hq hs x hx
    hbase hT κΩ κF κE bin selector Φ ψ hordinary hΦ hψ ι ζ hζ
    star P0 R O G hι hstar hforeign hpair hrow hretain ε δ hO hF hδ hslack
    hsmall P hP
  change P.cost = Compression.restrictionD M R (retainedColumns O G) at hcost
  omega

end Paper2.TwoStreamObstruction

#print axioms Paper2.TwoStreamObstruction.short_protocol_impossible
#print axioms Paper2.TwoStreamObstruction.restriction_lower
