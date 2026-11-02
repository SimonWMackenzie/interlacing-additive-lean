import Paper2.ReferenceCertificateProtocol

/-!
# Counting unsplit reference owners on the actual stopping tree

Frozen Paper 2 v12, `sections/05-restoration.tex`, `res:destinations`,
lines 273--310. The finite count below consumes the local first-Bob and
final-node bounds, not an owner-count certificate. The actual-run adapter
derives conservation, complete capacity and unsplit-origin uniqueness from
the checked annotated recursion. Source-specific local contradictions and
initialization are separate obligations before this proves the paper lemma.
-/

namespace Paper2.ReferenceOwners

open ReferenceCertificates ReferenceCertificateTree SourceSupportFrontier
open scoped BigOperators
open scoped Classical

variable {V I W : Type*} [Fintype V]

/-- Physical final positions which retain an unsplit original coordinate. -/
noncomputable def ownerNodes (family : V → Family I W) (final : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => final v ∧ (family v).unsplit.Nonempty)

@[simp] theorem mem_ownerNodes (family : V → Family I W) (final : V → Prop) (v : V) :
    v ∈ ownerNodes family final ↔ final v ∧ (family v).unsplit.Nonempty := by
  classical
  simp [ownerNodes]

/-- All nonowner capacity, including empty physical paths, remains counted. -/
noncomputable def exceptionalCapacity (family : V → Family I W) (final : V → Prop)
    (capacity : V → ℕ) : ℕ := by
  classical
  exact ∑ v, if v ∈ ownerNodes family final then 0 else capacity v

theorem capacity_partition (family : V → Family I W) (final : V → Prop)
    (capacity : V → ℕ) (hfinal : ∀ v, final v → capacity v = 1) :
    (ownerNodes family final).card + exceptionalCapacity family final capacity =
      ∑ v, capacity v := by
  classical
  have hone : (∑ v : V, if v ∈ ownerNodes family final then (1 : ℕ) else 0) =
      (ownerNodes family final).card := by simp [ownerNodes]
  rw [← hone, exceptionalCapacity, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ ownerNodes family final
  · simp [hv, hfinal v ((mem_ownerNodes _ _ _).mp hv).1]
  · simp [hv]

theorem local_units_le (family : V → Family I W) (final : V → Prop)
    (capacity : V → ℕ)
    (hvalid : ∀ v, (family v).unsplit ⊆ (family v).active)
    (hfinal : ∀ v, final v → capacity v = 1 ∧ (family v).active.card ≤ 1)
    (hbob : ∀ v, ¬ final v → (units (family v) : ℝ) < 9 * (capacity v : ℝ) / 8)
    (v : V) :
    8 * units (family v) ≤ 9 * capacity v +
      7 * (if v ∈ ownerNodes family final then 1 else 0) := by
  classical
  by_cases hf : final v
  · obtain ⟨hc, ha⟩ := hfinal v hf
    have hu := Finset.card_le_card (hvalid v)
    by_cases ho : v ∈ ownerNodes family final
    · simp only [ho, if_true, hc]
      dsimp only [units]
      omega
    · have hn : ¬ (family v).unsplit.Nonempty := fun hn =>
        ho ((mem_ownerNodes _ _ _).mpr ⟨hf, hn⟩)
      have he : (family v).unsplit = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [ho, if_false, hc, mul_zero, add_zero, units, he, Finset.card_empty]
      omega
  · have ho : v ∉ ownerNodes family final := fun ho =>
      hf ((mem_ownerNodes _ _ _).mp ho).1
    simp only [ho, if_false, mul_zero, add_zero]
    have h := hbob v hf
    have hle : 8 * (units (family v) : ℝ) ≤ 9 * (capacity v : ℝ) := by linarith
    exact_mod_cast hle

theorem total_units_le (family : V → Family I W) (final : V → Prop)
    (capacity : V → ℕ)
    (hvalid : ∀ v, (family v).unsplit ⊆ (family v).active)
    (hfinal : ∀ v, final v → capacity v = 1 ∧ (family v).active.card ≤ 1)
    (hbob : ∀ v, ¬ final v → (units (family v) : ℝ) < 9 * (capacity v : ℝ) / 8) :
    8 * (∑ v, units (family v)) ≤ 9 * (∑ v, capacity v) +
      7 * (ownerNodes family final).card := by
  classical
  calc
    _ = ∑ v, 8 * units (family v) := Finset.mul_sum ..
    _ ≤ ∑ v, (9 * capacity v + 7 * (if v ∈ ownerNodes family final then 1 else 0)) :=
      Finset.sum_le_sum (fun v _ => local_units_le family final capacity hvalid hfinal hbob v)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      congr 1
      simp [ownerNodes]

/-- The exact ceiling from the paper, not a rounded asymptotic budget. -/
noncomputable def exceptionBudget (e0 : ℕ) : ℕ := Nat.ceil (16 * (e0 : ℝ) / 7)

theorem owner_count (family : V → Family I W) (final : V → Prop)
    (capacity : V → ℕ) (w n e0 : ℕ)
    (hvalid : ∀ v, (family v).unsplit ⊆ (family v).active)
    (hfinal : ∀ v, final v → capacity v = 1 ∧ (family v).active.card ≤ 1)
    (hbob : ∀ v, ¬ final v → (units (family v) : ℝ) < 9 * (capacity v : ℝ) / 8)
    (hcapacity : ∑ v, capacity v = w)
    (hweight : 2 * n ≤ ∑ v, units (family v)) (hinitial : w ≤ n + e0) :
    w - exceptionBudget e0 ≤ (ownerNodes family final).card ∧
      exceptionalCapacity family final capacity ≤ exceptionBudget e0 := by
  have htotal := total_units_le family final capacity hvalid hfinal hbob
  have hpart := capacity_partition family final capacity (fun v hv => (hfinal v hv).1)
  rw [hcapacity] at htotal hpart
  have hdefect : 7 * exceptionalCapacity family final capacity ≤ 16 * e0 := by
    nlinarith
  have hceil : 16 * (e0 : ℝ) / 7 ≤ (exceptionBudget e0 : ℝ) := Nat.le_ceil _
  have hreal : 7 * (exceptionalCapacity family final capacity : ℝ) ≤ 16 * (e0 : ℝ) := by
    exact_mod_cast hdefect
  have hbound : exceptionalCapacity family final capacity ≤ exceptionBudget e0 := by
    have : (exceptionalCapacity family final capacity : ℝ) ≤ (exceptionBudget e0 : ℝ) := by
      linarith
    exact_mod_cast this
  exact ⟨by omega, hbound⟩

/-- An owner carries an original coordinate, chosen only for the proof.
The choice is not used by the matrix constructor or protocol. -/
noncomputable def origin (family : V → Family I W) (final : V → Prop)
    (v : {v // v ∈ ownerNodes family final}) : I :=
  Classical.choose ((mem_ownerNodes family final v.val).mp v.property).2

theorem origin_mem (family : V → Family I W) (final : V → Prop)
    (v : {v // v ∈ ownerNodes family final}) :
    origin family final v ∈ (family v.val).unsplit :=
  Classical.choose_spec ((mem_ownerNodes family final v.val).mp v.property).2

theorem origin_injective (family : V → Family I W) (final : V → Prop)
    (hdisjoint : ∀ v z : V, v ≠ z → Disjoint (family v).unsplit (family z).unsplit) :
    Function.Injective (origin family final) := by
  intro v z he
  apply Subtype.ext
  by_contra hne
  have hv := origin_mem family final v
  have hz := origin_mem family final z
  rw [← he] at hz
  exact Finset.disjoint_left.mp (hdisjoint v.val z.val hne) hv hz

theorem origin_eq_of_mem (family : V → Family I W) (final : V → Prop)
    (hvalid : ∀ v, (family v).unsplit ⊆ (family v).active)
    (hfinal : ∀ v, final v → (family v).active.card ≤ 1)
    (v : {v // v ∈ ownerNodes family final}) (i : I)
    (hi : i ∈ (family v.val).unsplit) : i = origin family final v := by
  apply Finset.card_le_one.mp (hfinal v.val ((mem_ownerNodes _ _ _).mp v.property).1)
  · exact hvalid v.val hi
  · exact hvalid v.val (origin_mem family final v)

section ActualRun

variable {A C : Type*} [Fintype W]

/-- The finite owner estimate specialized to the actual complete annotated
run. Only the two local communication bounds remain as inputs. -/
theorem run_owner_count (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (r : ℕ) (s : State A C I W) (n e0 : ℕ)
    (hvalid : s.family.unsplit ⊆ s.family.active)
    (hprefix : ReferencePrefix.NoEarlyLeaf r s.protocol)
    (hinitial : 2 ^ r ≤ n + e0) (hunits : 2 * n ≤ units s.family)
    (hfinal : ∀ v : (run μ input floor 0 r s).Leaves,
      ((run μ input floor 0 r s).route v).length = r →
        ((run μ input floor 0 r s).state v).family.active.card ≤ 1)
    (hbob : ∀ v : (run μ input floor 0 r s).Leaves,
      ((run μ input floor 0 r s).route v).length ≠ r →
        (units ((run μ input floor 0 r s).state v).family : ℝ) <
          9 * ((2 ^ (r - ((run μ input floor 0 r s).route v).length) : ℕ) : ℝ) / 8) :
    let T := run μ input floor 0 r s
    let F := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    2 ^ r - exceptionBudget e0 ≤ (ownerNodes F final).card ∧
      exceptionalCapacity F final (fun v => 2 ^ (r - (T.route v).length)) ≤ exceptionBudget e0 := by
  dsimp only
  apply owner_count _ _ _ (2 ^ r) n e0
  · exact run_valid μ input floor 0 r s hvalid
  · intro v hv
    exact ⟨by simp [hv], hfinal v hv⟩
  · exact hbob
  · exact ReferenceCertificateProtocol.run_capacity_eq μ input floor 0 r s hprefix
  · exact hunits.trans (run_units μ input floor 0 r s hvalid)
  · exact hinitial

theorem run_origin_injective (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (r : ℕ) (s : State A C I W) :
    Function.Injective (origin
      (fun v : (run μ input floor 0 r s).Leaves => ((run μ input floor 0 r s).state v).family)
      (fun v => ((run μ input floor 0 r s).route v).length = r)) :=
  origin_injective _ _ (run_unsplit_disjoint μ input floor 0 r s)

theorem run_origin_mem_initial (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (r : ℕ) (s : State A C I W)
    (v : {v : (run μ input floor 0 r s).Leaves // v ∈ ownerNodes
      (fun z => ((run μ input floor 0 r s).state z).family)
      (fun z => ((run μ input floor 0 r s).route z).length = r)}) :
    origin (fun z => ((run μ input floor 0 r s).state z).family)
      (fun z => ((run μ input floor 0 r s).route z).length = r) v ∈ s.family.unsplit :=
  (run_sets_subset μ input floor 0 r s v.val).2.1 (origin_mem _ _ v)

end ActualRun
end Paper2.ReferenceOwners

#print axioms Paper2.ReferenceOwners.owner_count
#print axioms Paper2.ReferenceOwners.origin_injective
#print axioms Paper2.ReferenceOwners.run_owner_count
#print axioms Paper2.ReferenceOwners.run_origin_injective
