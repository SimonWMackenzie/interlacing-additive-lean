import Paper2.YaoLookupRestriction
import Paper2.YaoEventsNormalization
import Paper2.YaoSelectorEvents
import Paper2.YaoLowerBoundStrategies
import Paper2.YaoLowerBoundProjection

/-!
# The deterministic lower-bound implication of the two sampling properties

Locked source: v12 Section 7, proof of `yao:lift`. The sampling properties
are stated explicitly; neither assumes a communication lower bound for the
constructed matrix. Actual early strategies supply a source colouring, and
actual retained labels yield a payload lookup restriction.
-/

namespace Paper2.YaoLowerBound

open Paper2.Yao Paper2.YaoLookup
open Workspace.Types.Protocol
open scoped BigOperators

variable {V E : Type*} {K H q m n : ℕ}

/-- Sample labels landing in a product set of addresses. Repeated sampled
tuples retain separate labels in this empirical count. -/
def selectorBox (C : Fin m → Fin q → Fin H) (J : Fin q → Finset (Fin H)) :
    Finset (Fin m) := Finset.univ.filter (fun z => ∀ g, C z g ∈ J g)

/-- Every member of a retained class lies in the product of that class's
coordinate projections. -/
theorem retained_subset_selectorBox (C : Fin m → Fin q → Fin H) (Z : Finset (Fin m)) :
    Z ⊆ selectorBox C (fun g => Z.image (fun z => C z g)) := by
  intro z hz
  simp only [selectorBox, Finset.mem_filter, Finset.mem_univ, true_and]
  intro g
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- A class occupying at least `1/S` of labels has projection product at
least `3/(4S)` under the selector event. The positive sample count prevents
vacuous division by zero. -/
theorem retained_projection_product (S : ℕ) (hS : 0 < S) (hm : 0 < m)
    (C : Fin m → Fin q → Fin H) (hC : selectorGood q H S m C)
    (Z : Finset (Fin m)) (hZ : m ≤ S * Z.card) :
    3 / (4 * (S : ℝ)) ≤
      ∏ g, ((Z.image (fun z => C z g)).card : ℝ) / H := by
  apply selectorGood_large_class C hC hm hS Z hZ
  intro z hz g
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- The large represented-address set gives an actual forbidden payload
protocol, not an abstract matrix with a related density or rank. -/
theorem payload_failure_of_large_projection
    (r t jmin : ℕ) (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool)
    (α : Fin H) (e : Fin K ↪ V) (he : edges α = some e)
    (g : Fin q) (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) .alice)
    (hP : P.Computes (matrix edges C W)) (hcost : P.cost ≤ 2 * r + 1)
    (σ : ResponseStrategy t)
    (hσ : ∀ i z, z ∈ Z i → earlyStrategy t P.toProtocol (e i, z) = σ)
    (hlarge : jmin ≤ ∑ i, (Restriction.addresses C g Z i).card) :
    payloadShortProtocolFailure r t jmin n W := by
  let Q := Restriction.payloadProtocol e C g α Z P
  refine ⟨Restriction.payloadSet C g Z, ?_, Q.toProtocol, ?_, Q.alternates,
    ⟨σ, ?_⟩, ?_⟩
  · simpa only [Restriction.payloadSet_card] using hlarge
  · exact (Restriction.payloadProtocol_cost e C g α Z P).le.trans hcost
  · exact Restriction.payloadProtocol_earlyStrategy t e C g α Z P σ hσ
  · exact Restriction.payloadProtocol_computes edges C W α e he g Z P hP

/-- On a NO-colouring source and a good selector sample, every short
protocol for the constructed matrix produces a forbidden payload protocol.
The only source premise is the explicit hypergraph colouring promise. -/
theorem short_protocol_payload_failure (t b : ℕ) (ht : 4 ≤ t) (hm : 0 < m)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V) (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) m C)
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool)
    (P : StrictProtocol (V × Fin m) (Fin (2 ^ (t - 1)) × Fin (2 ^ b) × Fin n) .alice)
    (hP : P.Computes (matrix (placeEdges edges index) C W))
    (hcost : P.cost ≤ 2 * (b + 3 * t - 3) + 1) :
    payloadShortProtocolFailure (b + 3 * t - 3) t (payloadMinimum b t) n W := by
  obtain ⟨e, σ, _, hσ, hsize⟩ :=
    LowerBound.exists_monochromatic_dominantClasses t P.toProtocol edges hno
  let Z : Fin (2 ^ t * 2 ^ t) → Finset (Fin m) :=
    fun i => LowerBound.dominantClass t P.toProtocol (edges e i)
  have hp (i : Fin (2 ^ t * 2 ^ t)) :
      (3 : ℝ) / (4 * (2 : ℝ) ^ (2 ^ t - 1)) ≤
        ∏ g, ((Restriction.addresses C g Z i).card : ℝ) / (2 : ℝ) ^ b := by
    simpa only [Restriction.addresses, Nat.cast_pow, Nat.cast_ofNat] using
      retained_projection_product (2 ^ (2 ^ t - 1)) (pow_pos (by decide) _) hm
        C hC (Z i) (hsize i)
  obtain ⟨g, hg⟩ := exists_large_projection t b ht
    (fun i g => (Restriction.addresses C g Z i).card) hp
  exact payload_failure_of_large_projection (b + 3 * t - 3) t (payloadMinimum b t)
    (placeEdges edges index) C W (index e) (edges e) (placeEdges_real edges index e)
    g Z P hP hcost σ hσ hg

/-- Conditional deterministic form of `yao:lift`: when the two concrete
sample properties hold, the actual constructed matrix has the full NO gap.
No communication bound is assumed for that matrix or for a replacement. -/
theorem lower_bound_of_good_events [Fintype V]
    (t b : ℕ) (ht : 4 ≤ t) (hm : 0 < m)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V) (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) m C)
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool)
    (hW : ¬ payloadShortProtocolFailure (b + 3 * t - 3) t (payloadMinimum b t) n W) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤ Dalt .alice (matrix (placeEdges edges index) C W) := by
  obtain ⟨P, hcost, hP⟩ := exists_optimal .alice (matrix (placeEdges edges index) C W)
  by_contra h
  have hp : P.cost ≤ 2 * (b + 3 * t - 3) + 1 := by omega
  exact hW (short_protocol_payload_failure t b ht hm edges index hno C hC W P hP hp)

end Paper2.YaoLowerBound
