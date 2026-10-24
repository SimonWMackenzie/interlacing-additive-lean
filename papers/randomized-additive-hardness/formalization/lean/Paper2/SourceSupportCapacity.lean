import Paper2.SourceSupportProjection
import Paper2.SourceSupportSchedule
import Paper2.SourceSupportStep

/-!
# Capacity at an actual Alice node

Frozen v12 Section 4, `src:near-full`, the denser-child argument. The child
below is obtained from the actual Alice query. Its retained templates are
a single joint set; every diagonal word support remains unchanged. The
capacity estimates therefore apply to the very source matrix computed by
that child, rather than a matrix carrying an assumed lower bound.
-/

namespace Paper2.SourceSupportCapacity

open SourceMatrix SourceProjection SourceSupportProjection
open Workspace.Types.CommComplexity Workspace.Types.Protocol

section AliceFibre

variable {A B : Type*}

/-- Extend an actual query to unused raw labels only to describe its fibres
as subsets of the original carrier. The value outside the retained set is
irrelevant to every statement below. -/
noncomputable def rawQuery (V : Set A) (query : V → Bool) (v : A) : Bool := by
  classical
  exact if h : v ∈ V then query ⟨v, h⟩ else false

@[simp] theorem rawQuery_of_mem (V : Set A) (query : V → Bool)
    (v : A) (hv : v ∈ V) : rawQuery V query v = query ⟨v, hv⟩ := by
  classical
  simp [rawQuery, hv]

def rowFibre (V : Set A) (query : V → Bool) (b : Bool) : Set A :=
  {v | v ∈ V ∧ rawQuery V query v = b}

/-- The chosen original child, with only the row carrier restricted to
inputs that actually send its bit. Bob's entire carrier is unchanged. -/
noncomputable def childProtocol (V : Set A) (query : V → Bool)
    (left right : Protocol V B Bool) (b : Bool) : Protocol (rowFibre V query b) B Bool :=
  NPCC.Protocol.pullback (fun v => ⟨v.val, v.property.1⟩) id
    (if b then right else left)

theorem childProtocol_computes (F : A → B → Bool) (V : Set A)
    (query : V → Bool) (left right : Protocol V B Bool)
    (hP : (Protocol.aNode query left right).Computes (fun v u => F v.val u))
    (b : Bool) : (childProtocol V query left right b).Computes
      (fun v u => F v.val u) := by
  intro v u
  have hb : query ⟨v.val, v.property.1⟩ = b := by
    rw [← rawQuery_of_mem V query v.val v.property.1]
    exact v.property.2
  have hp := hP ⟨v.val, v.property.1⟩ u
  rw [Protocol.eval, hb] at hp
  rw [childProtocol, NPCC.Protocol.pullback_eval]
  cases b <;> simpa using hp

theorem childProtocol_cost (V : Set A) (query : V → Bool)
    (left right : Protocol V B Bool) (b : Bool) :
    (childProtocol V query left right b).cost + 1 ≤
      (Protocol.aNode query left right).cost := by
  rw [childProtocol, NPCC.Protocol.pullback_cost]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Protocol.cost]
  · have := Nat.le_max_left left.cost right.cost
    omega
  · have := Nat.le_max_right left.cost right.cost
    omega

end AliceFibre

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
variable {q₁ q₂ s n : ℕ} [NeZero q₁] [NeZero s]

/-- One actual template fibre of an Alice query. -/
def templateFibre (p : Fin s) (A : Set (Template q₁ q₂ X))
    (V : Set (RawRow q₁ q₂ s X I)) (query : V → Bool) (b : Bool) :
    Set (Template q₁ q₂ X) :=
  {z | z ∈ A ∧ rawQuery V query (Sum.inl (p, z)) = b}

omit [Fintype X] [Fintype I] [NeZero q₁] [NeZero s] in
theorem templateFibre_retained (p : Fin s) (A : Set (Template q₁ q₂ X))
    (V : Set (RawRow q₁ q₂ s X I)) (query : V → Bool) (b : Bool)
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V) :
    ∀ z ∈ templateFibre p A V query b, Sum.inl (p, z) ∈ rowFibre V query b := by
  intro z hz
  exact ⟨hA z hz.1, hz.2⟩

omit [Fintype I] [NeZero s] in
/-- The actual heavier query fibre keeps more than 0.499 of the original
template law, so in particular satisfies the common-column threshold. -/
theorem exists_dense_template_child
    (μ : PositiveRationalLaw X) (p : Fin s) (A : Set (Template q₁ q₂ X))
    (V : Set (RawRow q₁ q₂ s X I)) (query : V → Bool)
    (hA : (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A)) :
    ∃ b, (499 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
      (· ∈ templateFibre p A V query b) := by
  classical
  let law := (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
  let f := fun z : Template q₁ q₂ X => rawQuery V query (Sum.inl (p, z))
  let b := SourceSupportStep.heavyBit law A.toFinset f
  have hp := SourceSupportStep.mass_partition_heavy law A.toFinset f
  have hg := SourceSupportStep.heavy_ge_other law A.toFinset f
  have he : ∀ c, SourceSupportStep.mass law (SourceSupportStep.fibre A.toFinset f c) =
      law.prob (· ∈ templateFibre p A V query c) := by
    intro c
    simp only [SourceSupportStep.mass, SourceSupportStep.mem_fibre, Set.mem_toFinset]
    rfl
  refine ⟨b, ?_⟩
  change (499 / 1000 : ℝ) < law.prob (· ∈ templateFibre p A V query b)
  rw [he, he] at hp
  rw [he, he] at hg
  have hm : SourceSupportStep.mass law A.toFinset = law.prob (· ∈ A) := by
    simp [SourceSupportStep.mass]
  rw [hm] at hp
  change (998 / 1000 : ℝ) < law.prob (· ∈ A) at hA
  dsimp only [b]
  linarith

omit [NeZero q₁] in
/-- Any actual raw-row protocol bounds the communication complexity of
the same retained source in its displayed tagged-row orientation. -/
theorem sourceD_le_protocol
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (P : Protocol V U Bool)
    (hP : P.Computes (fun v u => N R activity ξ₀ u.val v.val)) :
    Compression.restrictionD (N R activity ξ₀) U V ≤ P.cost := by
  classical
  have hup : D (fun (v : V) (u : U) => N R activity ξ₀ u.val v.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  have he := restrictionD_transpose (N R activity ξ₀) U V
  exact he ▸ hup

/-- The power capacity is paid below the actual Alice bit, giving one
additional bit at the node. All selected coordinates use the same dense
template child, and every word support is independent of its template. -/
theorem alice_power_cost
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H k : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hk : 2 ≤ k)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (e : Fin n → Fin q₂) (he : Function.Injective e)
    (A : Set (Template q₁ q₂ X)) (S : Set (Fin n × Word q₁ s Y))
    (hn : 2 ^ (k - 1) + 1 ≤ n)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U)
    (hrow : ∀ i, (2 : ℝ) ^ k * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S))
    (hAmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (query : V → Bool) (left right : Protocol V U Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun v u => N R activity ξ₀ u.val v.val)) :
    H + k + 1 ≤ (Protocol.aNode query left right).cost := by
  classical
  obtain ⟨b, hb⟩ := exists_dense_template_child μ p A V query hAmass
  have hcount : 2 ^ (k - 1) + 1 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hn
  have hl := selected_capacity_power μ ν R activity ξ₀ H k hH hx hk hscale hprofile
    p e he (templateFibre p A V query b) S Finset.univ hcount U (rowFibre V query b)
    (templateFibre_retained p A V query b hA) hS (fun i _ => hrow i) (by linarith)
  have hc := childProtocol_computes (fun v (u : U) => N R activity ξ₀ u.val v)
    V query left right hP b
  have hu := sourceD_le_protocol R activity ξ₀ U (rowFibre V query b)
    (childProtocol V query left right b) hc
  have hd := childProtocol_cost V query left right b
  omega

/-- The two-copy case also applies at capacity one when there are at
least two supports. Its lower bound concerns the actual denser child. -/
theorem alice_two_cost
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (e : Fin n → Fin q₂) (he : Function.Injective e)
    (A : Set (Template q₁ q₂ X)) (S : Set (Fin n × Word q₁ s Y)) (hn : 2 ≤ n)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U)
    (hrow : ∀ i, 2 * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S))
    (hAmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (query : V → Bool) (left right : Protocol V U Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun v u => N R activity ξ₀ u.val v.val)) :
    H + 2 ≤ (Protocol.aNode query left right).cost := by
  classical
  obtain ⟨b, hb⟩ := exists_dense_template_child μ p A V query hAmass
  have hcount : 2 ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hn
  have hl := selected_capacity_two μ ν R activity ξ₀ H hH hx hscale hprofile
    p e he (templateFibre p A V query b) S Finset.univ hcount U (rowFibre V query b)
    (templateFibre_retained p A V query b hA) hS (fun i _ => hrow i) (by linarith)
  have hc := childProtocol_computes (fun v (u : U) => N R activity ξ₀ u.val v)
    V query left right hP b
  have hu := sourceD_le_protocol R activity ξ₀ U (rowFibre V query b)
    (childProtocol V query left right b) hc
  have hd := childProtocol_cost V query left right b
  omega

/-- The actual excess-node power case: the integer rounding is proved
from its three-quarter count, and its stronger support floor is weakened
only in the direction permitted by the row-capacity theorem. -/
theorem alice_power_contradiction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H k : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hk : 2 ≤ k)
    (hscale : (2 : ℝ) ^ k * x ≤ 1)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (e : Fin n → Fin q₂) (he : Function.Injective e)
    (A : Set (Template q₁ q₂ X)) (S : Set (Fin n × Word q₁ s Y))
    (hn : (3 / 4 : ℝ) * (2 : ℝ) ^ k ≤ (n : ℝ))
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U)
    (hrow : ∀ i, 2 * (2 : ℝ) ^ k * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S))
    (hAmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (query : V → Bool) (left right : Protocol V U Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun v u => N R activity ξ₀ u.val v.val))
    (hcost : (Protocol.aNode query left right).cost ≤ H + k) : False := by
  have hr : ∀ i, (2 : ℝ) ^ k * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S) := by
    intro i
    have hi := hrow i
    have hp : 0 ≤ (2 : ℝ) ^ k * x := by positivity
    nlinarith
  have hl := alice_power_cost μ ν R activity ξ₀ H k hH hx hk hscale hprofile
    p e he A S (SourceSupportSchedule.power_block_count hk hn) U V hA hS hr
    hAmass query left right hP
  omega

/-- Capacity two, including the integer count conversion at that node. -/
theorem alice_capacity_two_contradiction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (e : Fin n → Fin q₂) (he : Function.Injective e)
    (A : Set (Template q₁ q₂ X)) (S : Set (Fin n × Word q₁ s Y))
    (hn : (3 / 4 : ℝ) * 2 ≤ (n : ℝ))
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U)
    (hrow : ∀ i, 4 * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S))
    (hAmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (query : V → Bool) (left right : Protocol V U Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun v u => N R activity ξ₀ u.val v.val))
    (hcost : (Protocol.aNode query left right).cost ≤ H + 1) : False := by
  have hl := alice_two_cost μ ν R activity ξ₀ H hH hx hscale hprofile
    p e he A S (SourceSupportSchedule.two_block_count hn) U V hA hS
    (fun i => by have hi := hrow i; linarith) hAmass query left right hP
  omega

/-- Capacity one with at least two actual supports. An attachment is
unnecessary in this case; the remaining one-support case is a parent
argument and is deliberately not routed through an Alice child. -/
theorem alice_capacity_one_many_contradiction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (e : Fin n → Fin q₂) (he : Function.Injective e)
    (A : Set (Template q₁ q₂ X)) (S : Set (Fin n × Word q₁ s Y)) (hn : 2 ≤ n)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U)
    (hrow : ∀ i, 2 * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S))
    (hAmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (query : V → Bool) (left right : Protocol V U Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun v u => N R activity ξ₀ u.val v.val))
    (hcost : (Protocol.aNode query left right).cost ≤ H) : False := by
  have hl := alice_two_cost μ ν R activity ξ₀ H hH hx hscale hprofile
    p e he A S hn U V hA hS hrow hAmass query left right hP
  omega

end Paper2.SourceSupportCapacity

#print axioms Paper2.SourceSupportCapacity.childProtocol_computes
#print axioms Paper2.SourceSupportCapacity.exists_dense_template_child
#print axioms Paper2.SourceSupportCapacity.sourceD_le_protocol
#print axioms Paper2.SourceSupportCapacity.alice_power_contradiction
#print axioms Paper2.SourceSupportCapacity.alice_capacity_two_contradiction
#print axioms Paper2.SourceSupportCapacity.alice_capacity_one_many_contradiction
