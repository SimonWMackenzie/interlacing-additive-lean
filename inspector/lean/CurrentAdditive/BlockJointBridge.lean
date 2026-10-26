import CurrentAdditive.IndependentStreams

/-! Private bridge: disjoint bounded-coordinate tests of a bounded-wise source. -/

namespace CurrentAdditive

open Paper2 Paper2.FiniteLaw
open scoped BigOperators

variable {ι A Ω : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype Ω] {m R : ℕ}

private theorem prob_comp_eq_of_fibres
    {X Y B : Type*} [Fintype X] [Fintype Y] [Fintype B]
    (ν : FiniteLaw X) (τ : FiniteLaw Y) (f : X → B) (g : Y → B)
    (hf : ∀ b : B, ν.prob (fun x => f x = b) =
      τ.prob (fun y => g y = b)) (E : B → Prop) :
    ν.prob (fun x => E (f x)) = τ.prob (fun y => E (g y)) := by
  classical
  have he (ρ : FiniteLaw X) (h : X → B) :
      ρ.prob (fun x => E (h x)) =
        ∑ b : B, if E b then ρ.prob (fun x => h x = b) else 0 := by
    unfold FiniteLaw.prob
    calc
      (∑ x, if E (h x) then ρ.weight x else 0) =
          ∑ x, ∑ b : B, if h x = b then (if E b then ρ.weight x else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        simp
      _ = ∑ b : B, ∑ x, if h x = b then (if E b then ρ.weight x else 0) else 0 :=
        Finset.sum_comm
      _ = ∑ b : B, if E b then ∑ x, if h x = b then ρ.weight x else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> simp
  have he' (ρ : FiniteLaw Y) (h : Y → B) :
      ρ.prob (fun y => E (h y)) =
        ∑ b : B, if E b then ρ.prob (fun y => h y = b) else 0 := by
    unfold FiniteLaw.prob
    calc
      (∑ y, if E (h y) then ρ.weight y else 0) =
          ∑ y, ∑ b : B, if h y = b then (if E b then ρ.weight y else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        simp
      _ = ∑ b : B, ∑ y, if h y = b then (if E b then ρ.weight y else 0) else 0 :=
        Finset.sum_comm
      _ = ∑ b : B, if E b then ∑ y, if h y = b then ρ.weight y else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> simp
  rw [he ν f, he' τ g]
  apply Finset.sum_congr rfl
  intro b _
  rw [hf b]

/-- An `8R`-wise decoded source agrees on all Boolean events involving at
most `R` tests, when each test reads at most eight coordinates and the
coordinate blocks are pairwise disjoint. The comparator draws one whole
source outcome independently per test. -/
theorem disjoint_blocks_indicator_joint_agreement
    (ν : FiniteLaw Ω) (μ : FiniteLaw A)
    (decode : Ω → ι → A)
    (hwise : IsDWise (8 * R) ν decode μ)
    (blocks : Fin m → Finset ι)
    (hsize : ∀ i, (blocks i).card ≤ 8)
    (hdisj : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (H : ∀ i : Fin m, (blocks i → A) → Bool)
    (s : Finset (Fin m)) (hs : s.card ≤ R)
    (E : (s → Bool) → Prop) :
    ν.prob (fun ω => E (fun i : s =>
      H i (fun j => decode ω j))) =
    (ν.iid m).prob (fun ws => E (fun i : s =>
      H i (fun j => decode (ws i) j))) := by
  classical
  let U : Finset ι := s.biUnion blocks
  have hU : U.card ≤ 8 * R := by
    have hb := Finset.card_biUnion_le_card_mul s blocks 8 (by
      intro i hi
      exact hsize i)
    calc
      U.card ≤ s.card * 8 := hb
      _ ≤ R * 8 := Nat.mul_le_mul_right 8 hs
      _ = 8 * R := Nat.mul_comm _ _
  have hmem (i : s) (j : blocks i.val) : (j.val : ι) ∈ U :=
    Finset.mem_biUnion.mpr ⟨i.val, i.property, j.property⟩
  let testU : (U → A) → (s → Bool) := fun x i =>
    H i (fun j => x ⟨j.val, hmem i j⟩)
  have hsource : ν.prob (fun ω => E (fun i : s =>
      H i (fun j => decode ω j))) =
      (FiniteLaw.pi (fun _ : U => μ)).prob (fun x => E (testU x)) := by
    simpa only [testU] using hwise U hU (fun x => E (testU x))
  have hfull : (FiniteLaw.pi (fun _ : U => μ)).prob (fun x => E (testU x)) =
      (FiniteLaw.pi (fun _ : ι => μ)).prob (fun x => E (fun i : s =>
        H i (fun j => x j))) := by
    symm
    exact FiniteLaw.pi_prob_restrict (fun _ : ι => μ)
      (fun j : U => j.val) Subtype.val_injective (fun x => E (testU x))
  -- It remains to compare the full product with independent whole-source
  -- draws, by factoring each joint atom over the disjoint blocks.
  rw [hsource, hfull]
  apply prob_comp_eq_of_fibres
    (FiniteLaw.pi (fun _ : ι => μ)) (ν.iid m)
    (fun x (i : s) => H i (fun j => x j))
    (fun ws (i : s) => H i (fun j => decode (ws i) j))
  intro b
  have hd : Pairwise (fun i j : s => Disjoint (blocks i) (blocks j)) := by
    intro i j hij
    exact hdisj (fun heq => hij (Subtype.ext heq))
  have hatomFull :
      (FiniteLaw.pi (fun _ : ι => μ)).prob
        (fun x => (fun i : s => H i (fun j => x j)) = b) =
      ∏ i : s, (FiniteLaw.pi (fun j : blocks i => μ)).prob
        (fun z => H i z = b i) := by
    simpa only [funext_iff] using
      (Paper2.ProductProjections.prob_disjoint_blocks
        (fun _ : ι => μ) (fun i : s => blocks i) hd
        (fun i z => H i z = b i))
  have hblock (i : s) :
      (FiniteLaw.pi (fun j : blocks i => μ)).prob
        (fun z => H i z = b i) =
      ν.prob (fun ω => H i (fun j => decode ω j) = b i) := by
    have hspos : 0 < R :=
      lt_of_lt_of_le (Finset.card_pos.mpr ⟨i.val, i.property⟩) hs
    have hb : (blocks i).card ≤ 8 * R := by
      have := hsize i
      omega
    simpa only [] using
      (hwise (blocks i) hb (fun z => H i z = b i)).symm
  have hiid : ν.iid m = FiniteLaw.pi (fun _ : Fin m => ν) := rfl
  have hatomProxy :
      (ν.iid m).prob (fun ws =>
        (fun i : s => H i (fun j => decode (ws i) j)) = b) =
      ∏ i : s, ν.prob (fun ω => H i (fun j => decode ω j) = b i) := by
    rw [hiid]
    calc
      _ = (FiniteLaw.pi (fun _ : s => ν)).prob
          (fun ys => ∀ i : s, H i (fun j => decode (ys i) j) = b i) := by
        simpa only [funext_iff] using
          (FiniteLaw.pi_prob_restrict (fun _ : Fin m => ν)
            (fun i : s => i.val) Subtype.val_injective
            (fun ys => ∀ i : s, H i (fun j => decode (ys i) j) = b i))
      _ = _ := FiniteLaw.pi_prob_coordinatewise (fun _ : s => ν)
        (fun i ω => H i (fun j => decode ω j) = b i)
  rw [hatomFull, hatomProxy]
  apply Finset.prod_congr rfl
  intro i _
  exact hblock i

end CurrentAdditive

#print axioms CurrentAdditive.disjoint_blocks_indicator_joint_agreement
