import Paper2.ReferenceOwners

/-! v39 robustness.tex, res:destinations.  Twice the reference weight at a
first-Bob stop is at most its capacity.  The actual support recursion then
gives the exact exceptional budget 2 e0, including empty physical paths. -/

namespace CurrentAdditive.V39ReferenceOwnersSharp

open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceCertificateProtocol Paper2.ReferenceOwners
open scoped BigOperators
open scoped Classical

variable {V I W : Type*} [Fintype V]

theorem local_units_le (family : V → Family I W) (final : V → Prop)
    (capacity : V → ℕ)
    (hvalid : ∀ v, (family v).unsplit ⊆ (family v).active)
    (hfinal : ∀ v, final v → capacity v = 1 ∧ (family v).active.card ≤ 1)
    (hbob : ∀ v, ¬ final v → units (family v) ≤ capacity v) (v : V) :
    units (family v) ≤ capacity v + if v ∈ ownerNodes family final then 1 else 0 := by
  classical
  by_cases hf : final v
  · obtain ⟨hc, ha⟩ := hfinal v hf
    have hu := Finset.card_le_card (hvalid v)
    by_cases ho : v ∈ ownerNodes family final
    · simp only [ho, if_true, hc, units]
      omega
    · have hn : ¬ (family v).unsplit.Nonempty := fun hn =>
        ho ((mem_ownerNodes _ _ _).mpr ⟨hf, hn⟩)
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [ho, if_false, hc, units, he, Finset.card_empty]
      omega
  · have ho : v ∉ ownerNodes family final := fun ho =>
      hf ((mem_ownerNodes _ _ _).mp ho).1
    simpa only [ho, if_false, Nat.add_zero] using hbob v hf

theorem owner_count (family : V → Family I W) (final : V → Prop)
    (capacity : V → ℕ) (w n e0 : ℕ)
    (hvalid : ∀ v, (family v).unsplit ⊆ (family v).active)
    (hfinal : ∀ v, final v → capacity v = 1 ∧ (family v).active.card ≤ 1)
    (hbob : ∀ v, ¬ final v → units (family v) ≤ capacity v)
    (hcapacity : ∑ v, capacity v = w)
    (hweight : 2*n ≤ ∑ v, units (family v)) (hinitial : w ≤ n+e0) :
    w - 2*e0 ≤ (ownerNodes family final).card ∧
      exceptionalCapacity family final capacity ≤ 2*e0 := by
  classical
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
    local_units_le family final capacity hvalid hfinal hbob v)
  have howners : (∑ v : V, if v ∈ ownerNodes family final then (1 : ℕ) else 0) =
      (ownerNodes family final).card := by simp [ownerNodes]
  rw [Finset.sum_add_distrib, howners, hcapacity] at hsum
  have hpart := capacity_partition family final capacity (fun v hv => (hfinal v hv).1)
  rw [hcapacity] at hpart
  constructor <;> omega

variable {A C : Type*} [Fintype W]

/-- The leaves, capacities, supports and origins are all computed by one
actual annotated Alice-prefix run. Only its two local communication
obstructions remain to be supplied by source-specific Fin-2 bounds. -/
theorem run_owner_count (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (r : ℕ) (state : State A C I W) (n e0 : ℕ)
    (hvalid : state.family.unsplit ⊆ state.family.active)
    (hprefix : Paper2.ReferencePrefix.NoEarlyLeaf r state.protocol)
    (hinitial : 2^r ≤ n+e0) (hunits : 2*n ≤ units state.family)
    (hfinal : ∀ v : (run μ input floor 0 r state).Leaves,
      ((run μ input floor 0 r state).route v).length = r →
      ((run μ input floor 0 r state).state v).family.active.card ≤ 1)
    (hbob : ∀ v : (run μ input floor 0 r state).Leaves,
      ((run μ input floor 0 r state).route v).length ≠ r →
      units ((run μ input floor 0 r state).state v).family ≤
        2^(r-((run μ input floor 0 r state).route v).length)) :
    let T := run μ input floor 0 r state
    let F := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    2^r - 2*e0 ≤ (ownerNodes F final).card ∧
      exceptionalCapacity F final (fun v => 2^(r-(T.route v).length)) ≤ 2*e0 := by
  dsimp only
  apply owner_count _ _ _ (2^r) n e0
  · exact run_valid μ input floor 0 r state hvalid
  · intro v hv
    exact ⟨by simp [hv], hfinal v hv⟩
  · exact hbob
  · exact run_capacity_eq μ input floor 0 r state hprefix
  · exact hunits.trans (run_units μ input floor 0 r state hvalid)
  · exact hinitial

/-- A bound of κ/2 on active supports supplies the sharp weight bound,
because every unsplit support is active. -/
theorem units_le_capacity (family : Family I W) (half κ : ℕ)
    (hvalid : family.unsplit ⊆ family.active)
    (hactive : family.active.card ≤ half) (hκ : κ = 2*half) :
    units family ≤ κ := by
  have hu := Finset.card_le_card hvalid
  dsimp only [units]
  omega

end CurrentAdditive.V39ReferenceOwnersSharp

#print axioms CurrentAdditive.V39ReferenceOwnersSharp.local_units_le
#print axioms CurrentAdditive.V39ReferenceOwnersSharp.owner_count
#print axioms CurrentAdditive.V39ReferenceOwnersSharp.run_owner_count
#print axioms CurrentAdditive.V39ReferenceOwnersSharp.units_le_capacity
