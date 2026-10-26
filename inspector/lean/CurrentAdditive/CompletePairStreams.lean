import CurrentAdditive.IndependentStreams
import Paper2.PairedSelectorMatrixCore

/-! The two complete indexed selector streams used at `det:paired`.
Their product is formed before any retained pair set or protocol rectangle. -/

namespace CurrentAdditive.CompletePairStreams

open Paper2 Paper2.FiniteLaw

variable {Seed J : Type*} [Fintype Seed] [Fintype J]
  {q : ℕ}

def pairToBool : Seed × Seed → Bool → Seed :=
  fun z b => if b then z.2 else z.1

def boolToPair : (Bool → Seed) → Seed × Seed :=
  fun f => (f false, f true)

omit [Fintype Seed] in
theorem boolToPair_pairToBool (z : Seed × Seed) :
    boolToPair (pairToBool z) = z := by
  cases z
  rfl

omit [Fintype Seed] in
theorem pairToBool_boolToPair (f : Bool → Seed) :
    pairToBool (boolToPair f) = f := by
  funext b
  cases b <;> rfl

def pairBoolEquiv : (Seed × Seed) ≃ (Bool → Seed) where
  toFun := pairToBool
  invFun := boolToPair
  left_inv := boolToPair_pairToBool
  right_inv := pairToBool_boolToPair

/-- Independent *whole* selector streams have the product law on their
two tagged indices, including events involving both streams at once. -/
theorem pair_pushes_to_bool_product (σ : FiniteLaw Seed) :
    (σ.prod σ).PushesTo (FiniteLaw.pi (fun _ : Bool => σ)) pairToBool := by
  intro E
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv pairBoolEquiv
  intro z
  congr 1
  simp [FiniteLaw.prod, FiniteLaw.pi, pairBoolEquiv, pairToBool, mul_comm]

/-- The two independent complete streams give exact joint marginals on
both tags.  This concerns the original pair law, before a retained pair
event is selected. -/
theorem pair_streams_dwise (D : ℕ) (σ : FiniteLaw Seed) :
    IsDWise D (σ.prod σ) pairToBool σ := by
  intro s hs E
  calc
    (σ.prod σ).prob (fun z => E (fun i : s => pairToBool z i.val)) =
        (FiniteLaw.pi (fun _ : Bool => σ)).prob
          (fun z => E (fun i : s => z i.val)) :=
      pair_pushes_to_bool_product σ
        (fun z : Bool → Seed => E (fun i : s => z i.val))
    _ = (FiniteLaw.pi (fun _ : s => σ)).prob E := by
      exact FiniteLaw.pi_prob_restrict (fun _ : Bool => σ)
        Subtype.val Subtype.val_injective E

/-- Each indexed selector has only bounded-wise inner coordinates, but
the *two complete draws* are independent.  Hence any at most `D` distinct
tagged coordinates have the true product law, including equal inner
indices with different tags. -/
theorem paired_tagged_flatten_dwise
    (D : ℕ) (σ : FiniteLaw Seed) (μ : FiniteLaw J)
    (decode : Seed → Fin q → J)
    (hinner : IsDWise D σ decode μ) :
    IsDWise D (σ.prod σ)
      (fun z (p : Bool × Fin q) => decode (pairToBool z p.1) p.2) μ := by
  classical
  exact flatten_dwise D σ (σ.prod σ) μ decode pairToBool
    hinner (pair_streams_dwise D σ)

/-- The actual image of an arbitrarily retained indexed selector-pair
set has at least the pair-set's original mass.  No independence survives
or is assumed after retention. -/
theorem paired_tagged_image_mass
    (D : ℕ) (σ : FiniteLaw Seed) (μ : FiniteLaw J)
    (decode : Seed → Fin q → J)
    (hinner : IsDWise D σ decode μ)
    (s : Finset (Bool × Fin q)) (hs : s.card ≤ D)
    (K : Set (Seed × Seed)) :
    (σ.prod σ).prob (· ∈ K) ≤
      (FiniteLaw.pi (fun _ : s => μ)).prob
        (· ∈ (fun z (p : s) =>
          decode (pairToBool z p.val.1) p.val.2) '' K) := by
  exact FiniteLaw.prob_le_image _ _ _
    (paired_tagged_flatten_dwise D σ μ decode hinner s hs) K

end CurrentAdditive.CompletePairStreams

#print axioms CurrentAdditive.CompletePairStreams.pair_pushes_to_bool_product
#print axioms CurrentAdditive.CompletePairStreams.pair_streams_dwise
#print axioms CurrentAdditive.CompletePairStreams.paired_tagged_flatten_dwise
#print axioms CurrentAdditive.CompletePairStreams.paired_tagged_image_mass
