import Paper2.YaoLookup
import Paper2.YaoCapacity

/-!
# A lookup matrix on actual retained rows

Frozen source: Paper 2 v12, `sections/07-yao.tex`, `yao:lift`, the final
restriction paragraph (lines 316--327). For a fixed real edge and coordinate,
one actual sample label is retained for each represented address at each
vertex. These rows and payload positions are distinct. The resulting matrix
is literally the payload lookup matrix, and restricting a protocol preserves
its early strategies, complete depth, and normalized last messages.

This module supplies the restriction step, not the sampling events, the
large-projection inequality, or the external hypergraph source theorem.
-/

namespace Paper2.YaoLookup.Restriction

open Paper2.Yao Workspace.Types.Protocol Workspace.UpperBound

variable {V : Type*} {K H q m n : ℕ}

/-- Addresses represented by retained sample labels at a vertex. -/
def addresses (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (i : Fin K) : Finset (Fin H) :=
  (Z i).image (fun z => C z g)

/-- One row index for each edge vertex and represented address. -/
abbrev Rows (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) :=
  (i : Fin K) × {h : Fin H // h ∈ addresses C g Z i}

theorem exists_representative (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) :
    ∃ z ∈ Z p.1, C z g = p.2.val :=
  Finset.mem_image.mp p.2.property

/-- An actual retained sample label, chosen only for the restriction proof.
The original matrix constructor does not make this choice. -/
noncomputable def representative (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) : Fin m :=
  Classical.choose (exists_representative C g Z p)

theorem representative_mem (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) :
    representative C g Z p ∈ Z p.1 :=
  (Classical.choose_spec (exists_representative C g Z p)).1

@[simp] theorem representative_address (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) :
    C (representative C g Z p) g = p.2.val :=
  (Classical.choose_spec (exists_representative C g Z p)).2

/-- The retained row is an input of the original matrix. -/
noncomputable def rowMap (e : Fin K ↪ V) (C : Fin m → Fin q → Fin H)
    (g : Fin q) (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) : V × Fin m :=
  (e p.1, representative C g Z p)

/-- Distinct represented addresses do not accidentally select the same
sample label, and distinct edge vertices remain distinct. -/
theorem rowMap_injective (e : Fin K ↪ V) (C : Fin m → Fin q → Fin H)
    (g : Fin q) (Z : Fin K → Finset (Fin m)) :
    Function.Injective (rowMap e C g Z) := by
  intro p r heq
  have hi : p.1 = r.1 := e.injective (congrArg Prod.fst heq)
  have hz : representative C g Z p = representative C g Z r := congrArg Prod.snd heq
  have hh : p.2.val = r.2.val := by
    simpa only [representative_address] using congrArg (fun z => C z g) hz
  rcases p with ⟨i, h, hm⟩
  rcases r with ⟨j, h', hm'⟩
  dsimp at hi hh
  subst j
  subst h'
  rfl

/-- A genuine lookup location, with the edge slot in `1,...,K`. -/
def payloadMap (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) : Fin H × Fin (K + 1) :=
  (p.2.val, p.1.succ)

theorem payloadMap_injective (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) : Function.Injective (payloadMap C g Z) := by
  intro p r heq
  have hh : p.2.val = r.2.val := congrArg Prod.fst heq
  have hi : p.1 = r.1 := Fin.succ_inj.mp (congrArg Prod.snd heq)
  rcases p with ⟨i, h, hm⟩
  rcases r with ⟨j, h', hm'⟩
  dsimp at hi hh
  subst j
  subst h'
  rfl

def columnMap (g : Fin q) (α : Fin H) (ℓ : Fin n) : Fin q × Fin H × Fin n :=
  (g, α, ℓ)

theorem columnMap_injective (g : Fin q) (α : Fin H) :
    Function.Injective (columnMap (n := n) g α) := by
  intro x y h
  exact congrArg (fun p => p.2.2) h

/-- Equality of the literal matrix entries, not only an equality of costs. -/
theorem matrix_restriction (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool)
    (α : Fin H) (e : Fin K ↪ V) (he : edges α = some e)
    (g : Fin q) (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) (ℓ : Fin n) :
    matrix edges C W (rowMap e C g Z p) (columnMap g α ℓ) =
      W ℓ (payloadMap C g Z p) := by
  simp [rowMap, columnMap, payloadMap, matrix_real_edge edges C W α e he]

theorem row_card (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) :
    Fintype.card (Rows C g Z) = ∑ i, (addresses C g Z i).card := by
  simp [Rows, Fintype.card_sigma]

/-- The actual subset of the original payload positions. -/
def payloadSet (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) : Finset (Fin H × Fin (K + 1)) :=
  Finset.univ.image (payloadMap C g Z)

theorem payloadSet_card (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) :
    (payloadSet C g Z).card = ∑ i, (addresses C g Z i).card := by
  rw [payloadSet, Finset.card_image_of_injective _ (payloadMap_injective C g Z)]
  simpa using row_card C g Z

/-- The represented-address indexing and actual payload subset are exactly
equivalent. Reindexing through this equivalence loses no rows. -/
noncomputable def payloadEquiv (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) : Rows C g Z ≃ {j // j ∈ payloadSet C g Z} :=
  Equiv.ofBijective
    (fun p => ⟨payloadMap C g Z p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => payloadMap_injective C g Z (congrArg Subtype.val h), by
      intro j
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp j.property
      exact ⟨p, Subtype.ext hp⟩⟩

@[simp] theorem payloadEquiv_val (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (p : Rows C g Z) :
    (payloadEquiv C g Z p).val = payloadMap C g Z p := rfl

@[simp] theorem payloadEquiv_symm_map (C : Fin m → Fin q → Fin H) (g : Fin q)
    (Z : Fin K → Finset (Fin m)) (j : {j // j ∈ payloadSet C g Z}) :
    payloadMap C g Z ((payloadEquiv C g Z).symm j) = j.val := by
  exact congrArg Subtype.val ((payloadEquiv C g Z).apply_symm_apply j)

/-- Restriction along the selected actual row and column maps. The tree is
unchanged; only each player's local input map is composed. -/
noncomputable def protocol {s : Turn} (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s) :
    StrictProtocol (Rows C g Z) (Fin n) s :=
  ⟨Protocol.comap (rowMap e C g Z) (columnMap g α) P.toProtocol,
    alternates_comap P.toProtocol _ _ s P.alternates⟩

@[simp] theorem protocol_cost {s : Turn} (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s) :
    (protocol e C g α Z P).cost = P.cost :=
  Protocol.comap_cost _ _ _

theorem protocol_computes {s : Turn} (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool)
    (α : Fin H) (e : Fin K ↪ V) (he : edges α = some e)
    (g : Fin q) (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (hP : P.Computes (matrix edges C W)) :
    (protocol e C g α Z P).Computes (fun p ℓ => W ℓ (payloadMap C g Z p)) := by
  intro p ℓ
  change (Protocol.comap _ _ P.toProtocol).eval p ℓ = _
  rw [Protocol.comap_eval]
  exact (hP _ _).trans (matrix_restriction edges C W α e he g Z p ℓ)

theorem protocol_earlyStrategy {s : Turn} (t : ℕ) (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (σ : ResponseStrategy t)
    (hσ : ∀ i z, z ∈ Z i → earlyStrategy t P.toProtocol (e i, z) = σ) :
    ∀ p, earlyStrategy t (protocol e C g α Z P).toProtocol p = σ := by
  intro p
  rw [protocol, earlyStrategy_comap]
  exact hσ p.1 (representative C g Z p) (representative_mem C g Z p)

theorem protocol_complete {s : Turn} (d : ℕ) (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (hP : IsComplete P.toProtocol d) :
    IsComplete (protocol e C g α Z P).toProtocol d :=
  isComplete_comap _ _ _ _ hP

theorem protocol_canonical {s : Turn} (d : ℕ) (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (hP : CanonicalLastLeaves d P.toProtocol) :
    CanonicalLastLeaves d (protocol e C g α Z P).toProtocol :=
  canonicalLastLeaves_comap _ _ _ _ hP

/-- The same restriction, indexed directly by the actual payload subset
used in sampling property (ii). -/
noncomputable def payloadProtocol {s : Turn} (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s) :
    StrictProtocol {j // j ∈ payloadSet C g Z} (Fin n) s :=
  ⟨Protocol.comap (fun j => rowMap e C g Z ((payloadEquiv C g Z).symm j))
      (columnMap g α) P.toProtocol,
    alternates_comap P.toProtocol _ _ s P.alternates⟩

@[simp] theorem payloadProtocol_cost {s : Turn} (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s) :
    (payloadProtocol e C g α Z P).cost = P.cost :=
  Protocol.comap_cost _ _ _

theorem payloadProtocol_computes {s : Turn} (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool)
    (α : Fin H) (e : Fin K ↪ V) (he : edges α = some e)
    (g : Fin q) (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (hP : P.Computes (matrix edges C W)) :
    (payloadProtocol e C g α Z P).Computes (fun j ℓ => W ℓ j.val) := by
  intro j ℓ
  change (Protocol.comap _ _ P.toProtocol).eval j ℓ = _
  rw [Protocol.comap_eval]
  exact (hP _ _).trans ((matrix_restriction edges C W α e he g Z
    ((payloadEquiv C g Z).symm j) ℓ).trans (by simp))

theorem payloadProtocol_earlyStrategy {s : Turn} (t : ℕ) (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (σ : ResponseStrategy t)
    (hσ : ∀ i z, z ∈ Z i → earlyStrategy t P.toProtocol (e i, z) = σ) :
    ∀ j, earlyStrategy t (payloadProtocol e C g α Z P).toProtocol j = σ := by
  intro j
  rw [payloadProtocol, earlyStrategy_comap]
  let p := (payloadEquiv C g Z).symm j
  exact hσ p.1 (representative C g Z p) (representative_mem C g Z p)

theorem payloadProtocol_complete {s : Turn} (d : ℕ) (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (hP : IsComplete P.toProtocol d) :
    IsComplete (payloadProtocol e C g α Z P).toProtocol d :=
  isComplete_comap _ _ _ _ hP

theorem payloadProtocol_canonical {s : Turn} (d : ℕ) (e : Fin K ↪ V)
    (C : Fin m → Fin q → Fin H) (g : Fin q) (α : Fin H)
    (Z : Fin K → Finset (Fin m))
    (P : StrictProtocol (V × Fin m) (Fin q × Fin H × Fin n) s)
    (hP : CanonicalLastLeaves d P.toProtocol) :
    CanonicalLastLeaves d (payloadProtocol e C g α Z P).toProtocol :=
  canonicalLastLeaves_comap _ _ _ _ hP

end Paper2.YaoLookup.Restriction
