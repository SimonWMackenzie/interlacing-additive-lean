import CurrentAdditive.V42Schedule
import Paper2.SourceProjection
import Paper2.Frontier
import CurrentAdditive.IndependentStreams

/-! Source-facing interfaces for v42 def:amplification-parameters,
obs:representatives and lem:kraft-count. These statements prove the
literal scalar recipe, arbitrary retained projections, and arbitrary
prefix-free integer counts; no amplifier or protocol conclusion is assumed. -/
namespace CurrentAdditive.V42SourceFacing
open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open scoped BigOperators

/-- The source's dyadic parameter choice, including its initial scalar
constraints. The effective choice of k0 and all hardness consequences
belong to the separate common-margin and source theorems. -/
theorem amplification_parameters (n k₀ k b : ℕ)
    (hn : n≤2^b) (hk : k₀≤k) (hb : 4*k≤b) :
    (n:ℚ)≤(V42Schedule.rho b)⁻¹ ∧
    V42Schedule.rho b≤1/(V42Schedule.s k:ℚ)^4 ∧
    V42Schedule.s k₀≤V42Schedule.s k ∧
    V42Schedule.q₁ k=V42Schedule.s k-2 ∧
    (V42Schedule.q₂ k b:ℚ)=(V42Schedule.s k:ℚ)^2/V42Schedule.rho b ∧
    V42Schedule.w k=(V42Schedule.s k)^8 ∧
    V42Schedule.Q k=(V42Schedule.s k)^24 ∧
    V42Schedule.x b=(V42Schedule.rho b)^8 ∧
    V42Schedule.eta k=1/(V42Schedule.s k:ℚ)^2 ∧
    V42Schedule.theta k=1/(512*(V42Schedule.Q k:ℚ)) ∧
    V42Schedule.deltaU k=V42Schedule.eta k/(16*(V42Schedule.w k:ℚ)) := by
  have hr : (n:ℚ)≤(V42Schedule.rho b)⁻¹ := by
    simpa only [V42Schedule.rho,one_div,inv_inv,Nat.cast_pow,Nat.cast_ofNat] using
      (show (n:ℚ)≤((2^b:ℕ):ℚ) by exact_mod_cast hn)
  have hscale : V42Schedule.rho b≤1/(V42Schedule.s k:ℚ)^4 := by
    have h:=V42Schedule.reciprocal_le b (4*k) hb
    simpa only [V42Schedule.rho,V42Schedule.s,Nat.cast_pow,Nat.cast_ofNat,
      ←pow_mul,show k*4=4*k by omega] using h
  exact ⟨hr,hscale,Nat.pow_le_pow_right (by decide) hk,rfl,V42Schedule.recipe_exact k b⟩

section Representatives
variable {X Y L : Type*} [Fintype X] [Fintype Y] [Fintype L]
  {q l : ℕ}

def project (decode : L → Fin q → Y) (e : Fin l → Fin q) : L → Fin l → Y :=
  fun label j => decode label (e j)
def selectedRows (e : Fin l → Fin q) (U : Set (Fin q × X)) : Set (Fin l × X) :=
  fun a => (e a.1,a.2)∈U
def retainedRow (e : Fin l → Fin q) (U : Set (Fin q × X)) : selectedRows e U → U :=
  fun a => ⟨(e a.val.1,a.val.2),a.property⟩

/-- One actual surviving label is used simultaneously for every retained
row. The product weight belongs to the projected tuple set, not to the
chosen representatives or to a purported independent conditional law. -/
theorem representatives
    (R : X → Y → Bool) (decode : L → Fin q → Y)
    (e : Fin l → Fin q) (he : Function.Injective e)
    (U : Set (Fin q × X)) (K : Set L)
    (μX : FiniteLaw X) (μY : FiniteLaw Y) (ν : FiniteLaw L) :
    ∃ pick : (project decode e '' K) → K,
      Function.Injective pick ∧
      Function.Injective (retainedRow e U) ∧
      (∀ c,project decode e (pick c).val=c.val) ∧
      (∀ (a : selectedRows e U) (c : project decode e '' K),
        fullInterlace R l a.val c.val=
          R a.val.2 (decode (pick c).val (e a.val.1))) ∧
      (∀ j,μX.prob (fun x=>(j,x)∈selectedRows e U)=
        μX.prob (fun x=>(e j,x)∈U)) ∧
      Compression.restrictionD (fullInterlace R l) (selectedRows e U) (project decode e '' K)≤
        Compression.restrictionD (fun a label=>R a.2 (decode label a.1)) U K ∧
      (ν.PushesTo (μY.iid l) (project decode e) →
        ν.prob (·∈K)≤(μY.iid l).prob (·∈project decode e '' K)) := by
  classical
  let pick : (project decode e '' K) → K:=SourceProjection.representative (project decode e) K
  have hmap (c : project decode e '' K) : project decode e (pick c).val=c.val :=
    SourceProjection.representative_maps (project decode e) K c
  refine ⟨pick,?_,?_,hmap,?_,?_,?_,?_⟩
  · intro c d h
    apply Subtype.ext
    exact (hmap c).symm.trans ((congrArg (fun a : K=>project decode e a.val) h).trans (hmap d))
  · intro a b h
    apply Subtype.ext
    apply Prod.ext
    · apply he
      exact congrArg (fun c : U=>c.val.1) h
    · exact congrArg (fun c : U=>c.val.2) h
  · intro a c
    have hh:=congrFun (hmap c) a.val.1
    exact congrArg (R a.val.2) hh.symm
  · intro j
    rfl
  · exact SourceProjection.restrictionD_projected_le
      (fun (a : Fin q × X) label=>R a.2 (decode label a.1)) (fullInterlace R l)
      (fun a : Fin l × X=>(e a.1,a.2)) (project decode e) U K (selectedRows e U)
      (fun _ h=>h) (by intros; rfl)
  · intro hmarginal
    exact FiniteLaw.prob_le_image ν (μY.iid l) (project decode e) hmarginal K

/-- Exact D-wise marginals imply the displayed original-law pushforward
for every injectively chosen set of at most D coordinates. -/
theorem dwise_project_pushes (D : ℕ) (ν : FiniteLaw L) (μ : FiniteLaw Y)
    (decode : L → Fin q → Y) (hwise : IsDWise D ν decode μ)
    (hl : l≤D) (e : Fin l → Fin q) (he : Function.Injective e) :
    ν.PushesTo (μ.iid l) (project decode e) := by
  classical
  intro P
  let J : Finset (Fin q):=Finset.univ.image e
  have hJcard : J.card≤D := Finset.card_image_le.trans (by simpa only [Finset.card_univ,Fintype.card_fin] using hl)
  have hmem (j : Fin l) : e j∈J:=Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  let E : (J → Y) → Prop:=fun z=>P (fun j=>z ⟨e j,hmem j⟩)
  have hs:=hwise J hJcard E
  have hr:=FiniteLaw.pi_prob_restrict (fun _ : Fin q=>μ) (fun j : J=>j.val) Subtype.val_injective E
  have hp:=FiniteLaw.pi_prob_restrict (fun _ : Fin q=>μ) e he P
  calc
    ν.prob (fun label=>P (project decode e label))=
        ν.prob (fun label=>E (fun j : J=>decode label j.val)) := rfl
    _=(FiniteLaw.pi (fun _ : J=>μ)).prob E := hs
    _=(μ.iid q).prob (fun c=>P (fun j=>c (e j))) := by
      simpa only [FiniteLaw.iid,E] using hr.symm
    _=(μ.iid l).prob P := by simpa only [FiniteLaw.iid] using hp

theorem projected_weight_of_dwise (D : ℕ) (ν : FiniteLaw L) (μ : FiniteLaw Y)
    (decode : L → Fin q → Y) (hwise : IsDWise D ν decode μ)
    (hl : l≤D) (e : Fin l → Fin q) (he : Function.Injective e) (K : Set L) :
    ν.prob (·∈K)≤(μ.iid l).prob (·∈project decode e '' K) :=
  FiniteLaw.prob_le_image ν (μ.iid l) _ (dwise_project_pushes D ν μ decode hwise hl e he) K

theorem projected_weight_full_product (μ : FiniteLaw Y)
    (e : Fin l → Fin q) (he : Function.Injective e) (K : Set (Fin q → Y)) :
    (μ.iid q).prob (·∈K)≤(μ.iid l).prob (·∈project id e '' K) :=
  SourceProjection.iid_projection_mass μ e he K
end Representatives

/-- The integer form of q*2^-depth for every node no deeper than log2 q. -/
theorem capacity_real (q r depth : ℕ) (hq : q=2^r) (hd : depth≤r) :
    ((2^(r-depth):ℕ):ℝ)=(q:ℝ)/(2:ℝ)^depth := by
  subst q
  push_cast
  simpa only [div_eq_mul_inv] using (pow_sub₀ (2:ℝ) (by norm_num) hd)

/-- The source's Kraft overload count on arbitrary prefix-free binary
paths and arbitrary natural object/marked counts. -/
theorem kraft_count {I : Type*} [Fintype I]
    (q r : ℕ) (hq : q=2^r) (route : I → List Bool)
    (hpf : Frontier.PrefixFree route) (hdepth : ∀ v,(route v).length≤r)
    (h z : I → ℕ) (hmarked : ∀ v : I, z v ≤ h v)
    (hover : q < (∑ v : I, (h v + z v))) :
    ∃ v : I, 2^(r-(route v).length)<h v+z v ∧
      (2≤2^(r-(route v).length) → 2^(r-(route v).length)/2+1≤h v) ∧
      (2^(r-(route v).length)=1 → 2≤h v ∨ h v=1 ∧ z v=1) := by
  classical
  have hsum:=Frontier.sum_integer_capacity_le route hpf r hdepth
  have hex : ∃ v : I, 2^(r-(route v).length)<h v+z v := by
    by_contra! hn
    have hle:=Finset.sum_le_sum (fun v (_ : v∈Finset.univ)=>hn v)
    rw [hq] at hover
    omega
  obtain ⟨v,hv⟩:=hex
  refine ⟨v,hv,?_,?_⟩
  · intro hk
    have hp : 1≤r-(route v).length := by
      by_contra hn
      have he : r-(route v).length=0 := by omega
      rw [he] at hk
      norm_num at hk
    have he : 2^(r-(route v).length)=2*2^(r-(route v).length-1) := by
      rw [←pow_succ']
      congr 1
      omega
    have hz:=hmarked v
    rw [he] at hv ⊢
    omega
  · intro hk
    rw [hk] at hv
    have hz:=hmarked v
    omega

#print axioms amplification_parameters
#print axioms representatives
#print axioms dwise_project_pushes
#print axioms projected_weight_of_dwise
#print axioms projected_weight_full_product
#print axioms capacity_real
#print axioms kraft_count
end CurrentAdditive.V42SourceFacing
