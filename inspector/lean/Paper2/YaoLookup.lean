import Paper2.YaoModel
import Paper2.CappedSamplerBits
import Paper2.YaoLookupExchange
import Paper2.YaoLookupBalance
import Paper2.InterlaceRank

/-!
# The concrete sampled lookup matrix and its short alternating protocols

Frozen source: v12 Section 7, `yao:entry` and `yao:budget` (lines 96--180).
The constructor takes only incidence data and labelled samples, never a
colouring. Unused edge labels have position zero; duplicated samples retain
their labels. Colourings are used only to construct a protocol in the proof.

This file concerns finite matrices and actual strictly alternating trees.
It does not prove the external source reduction, sampling events, or runtime.
-/

namespace Paper2.YaoLookup

open Paper2.Yao
open Workspace.Types.Protocol

variable {V E : Type*} {K H q m n : ℕ}

/-- Position in an ordered distinct-vertex edge, with zero reserved for an
absent vertex. The genuine positions are `1,...,K`. -/
noncomputable def edgePosition (e : Fin K ↪ V) (v : V) : Fin (K + 1) := by
  classical
  exact if h : ∃ i, e i = v then (Classical.choose h).succ else 0

@[simp] theorem edgePosition_apply (e : Fin K ↪ V) (i : Fin K) :
    edgePosition e (e i) = i.succ := by
  classical
  have h : ∃ j, e j = e i := ⟨i, rfl⟩
  simp only [edgePosition, dif_pos h]
  exact congrArg Fin.succ (e.injective (Classical.choose_spec h))

theorem edgePosition_absent (e : Fin K ↪ V) (v : V)
    (h : ∀ i, e i ≠ v) : edgePosition e v = 0 := by
  classical
  simp [edgePosition, not_exists.mpr h]

/-- Public incidence array; `none` is an unused edge address. -/
noncomputable def position (edges : Fin H → Option (Fin K ↪ V))
    (α : Fin H) (v : V) : Fin (K + 1) :=
  match edges α with
  | none => 0
  | some e => edgePosition e v

@[simp] theorem position_unused (edges : Fin H → Option (Fin K ↪ V))
    (α : Fin H) (h : edges α = none) (v : V) : position edges α v = 0 := by
  simp [position, h]

@[simp] theorem position_on_edge (edges : Fin H → Option (Fin K ↪ V))
    (α : Fin H) (e : Fin K ↪ V) (h : edges α = some e) (i : Fin K) :
    position edges α (e i) = i.succ := by
  simp [position, h]

/-- Place the actual edges at distinct public indices. This uses no promise
or colouring. The empty edge set yields an everywhere-unused array. -/
noncomputable def placeEdges (edges : E → Fin K ↪ V) (index : E ↪ Fin H) :
    Fin H → Option (Fin K ↪ V) := by
  classical
  exact fun α => if h : ∃ e, index e = α then some (edges (Classical.choose h)) else none

@[simp] theorem placeEdges_real (edges : E → Fin K ↪ V) (index : E ↪ Fin H) (e : E) :
    placeEdges edges index (index e) = some (edges e) := by
  classical
  have h : ∃ e', index e' = index e := ⟨e, rfl⟩
  simp only [placeEdges, dif_pos h]
  rw [index.injective (Classical.choose_spec h)]

theorem placeEdges_unused (edges : E → Fin K ↪ V) (index : E ↪ Fin H)
    (α : Fin H) (h : ∀ e, index e ≠ α) : placeEdges edges index α = none := by
  classical
  simp [placeEdges, not_exists.mpr h]

theorem placeEdges_empty [IsEmpty E] (edges : E → Fin K ↪ V) (index : E ↪ Fin H)
    (α : Fin H) : placeEdges edges index α = none :=
  placeEdges_unused edges index α (fun e => isEmptyElim e)

theorem placeEdges_eq_some_iff (edges : E → Fin K ↪ V) (index : E ↪ Fin H)
    (α : Fin H) (e : Fin K ↪ V) :
    placeEdges edges index α = some e ↔ ∃ j, index j = α ∧ edges j = e := by
  classical
  constructor
  · intro hs
    by_cases h : ∃ j, index j = α
    · rw [placeEdges, dif_pos h] at hs
      exact ⟨Classical.choose h, Classical.choose_spec h, Option.some.inj hs⟩
    · simp [placeEdges, h] at hs
  · rintro ⟨j, rfl, rfl⟩
    exact placeEdges_real edges index j

/-- The labelled matrix of `yao:entry`. `C` and `W` are arrays rather than
sets, so coincident sample values are not identified. -/
noncomputable def matrix (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H)
    (W : Fin n → Fin H × Fin (K + 1) → Bool) :
    (V × Fin m) → (Fin q × Fin H × Fin n) → Bool :=
  fun x y => W y.2.2 (C x.2 y.1, position edges y.2.1 x.1)

@[simp] theorem matrix_apply (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool)
    (v : V) (z : Fin m) (g : Fin q) (α : Fin H) (ℓ : Fin n) :
    matrix edges C W (v, z) (g, α, ℓ) = W ℓ (C z g, position edges α v) := rfl

/-- The unswitched lookup matrix `R` from the interlacing interpretation
immediately following `yao:entry`. -/
noncomputable def baseMatrix (edges : Fin H → Option (Fin K ↪ V))
    (W : Fin n → Fin H × Fin (K + 1) → Bool) :
    (V × Fin H) → (Fin H × Fin n) → Bool :=
  fun x y => W y.2 (x.2, position edges y.1 x.1)

/-- Every selected address is paired with the same vertex, not a resampled
vertex. This is the actual indexed tuple family for the transposed interlace. -/
def selectorTuple (C : Fin m → Fin q → Fin H) (x : V × Fin m) :
    Fin q → V × Fin H := fun g => (x.1, C x.2 g)

theorem matrix_is_transposed_indexedInterlace
    (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool) :
    matrix edges C W = fun x y =>
      indexedInterlace (fun y' x' => baseMatrix edges W x' y') (selectorTuple C) y x := rfl

@[simp] theorem selectorTuple_vertex (C : Fin m → Fin q → Fin H)
    (x : V × Fin m) (g : Fin q) : (selectorTuple C x g).1 = x.1 := rfl

/-- With a real edge fixed, the literal entries are lookup positions, not
merely a matrix with comparable density or rank. -/
theorem matrix_real_edge (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool)
    (α : Fin H) (e : Fin K ↪ V) (he : edges α = some e)
    (i : Fin K) (z : Fin m) (g : Fin q) (ℓ : Fin n) :
    matrix edges C W (e i, z) (g, α, ℓ) = W ℓ (C z g, i.succ) := by
  simp [matrix, position_on_edge edges α e he]

theorem real_edge_positions_injective (edges : Fin H → Option (Fin K ↪ V))
    (α : Fin H) (e : Fin K ↪ V) (he : edges α = some e) :
    Function.Injective (fun p : Fin K × Fin H => (p.2, position edges α (e p.1))) := by
  intro p r h
  have hh : p.2 = r.2 := congrArg Prod.fst h
  have hi : p.1 = r.1 := by
    have hs := congrArg Prod.snd h
    simpa only [position_on_edge edges α e he, Fin.succ_inj] using hs
  exact Prod.ext hi hh

/-- Positions consistent with a fixed colour, including the neutral zero.
This set is public once the colour and edge address have been transmitted. -/
noncomputable def colourSlots {s : ℕ} (colour : V → Fin s)
    (edges : Fin H → Option (Fin K ↪ V)) (α : Fin H) (c : Fin s) :
    Finset (Fin (K + 1)) := by
  classical
  exact match edges α with
  | none => {0}
  | some e => insert 0 ((Finset.univ.filter (fun i => colour (e i) = c)).image Fin.succ)

theorem position_mem_colourSlots {s : ℕ} (colour : V → Fin s)
    (edges : Fin H → Option (Fin K ↪ V)) (α : Fin H) (v : V) :
    position edges α v ∈ colourSlots colour edges α (colour v) := by
  classical
  cases he : edges α with
  | none => simp [position, colourSlots, he]
  | some e =>
      by_cases hv : ∃ i, e i = v
      · obtain ⟨i, rfl⟩ := hv
        simp [position, colourSlots, he]
      · simp [position, colourSlots, he, edgePosition, hv]

theorem colourSlots_card_real {s : ℕ} (colour : V → Fin s)
    (edges : Fin H → Option (Fin K ↪ V)) (α : Fin H)
    (e : Fin K ↪ V) (he : edges α = some e) (c : Fin s) :
    (colourSlots colour edges α c).card =
      (Finset.univ.filter (fun i => colour (e i) = c)).card + 1 := by
  classical
  simp [colourSlots, he, Finset.card_image_of_injective, Fin.succ_injective]

theorem colourSlots_card_le {s : ℕ} (colour : V → Fin s)
    (edges : Fin H → Option (Fin K ↪ V)) (α : Fin H) (c : Fin s) :
    (colourSlots colour edges α c).card ≤ K + 1 := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

/-- A concrete local encoder/decoder for within-colour positions. The
correctness field is an equality of finite indices, not a cost assumption. -/
structure SlotCode {s : ℕ} (colour : V → Fin s)
    (edges : Fin H → Option (Fin K ↪ V)) (width : ℕ) where
  encode : Fin H → V → Fin (2 ^ width)
  decode : Fin H → Fin s → Fin (2 ^ width) → Fin (K + 1)
  correct : ∀ α v, decode α (colour v) (encode α v) = position edges α v

/-- Finite position-set bounds produce an actual encoder and total decoder;
all unused messages decode to the neutral slot. -/
noncomputable def slotCodeOfCard {s width : ℕ} (colour : V → Fin s)
    (edges : Fin H → Option (Fin K ↪ V))
    (hcard : ∀ α c, (colourSlots colour edges α c).card ≤ 2 ^ width) :
    SlotCode colour edges width := by
  classical
  let emb (α : Fin H) (c : Fin s) :
      {j // j ∈ colourSlots colour edges α c} ↪ Fin (2 ^ width) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hcard α c))
  let enc (α : Fin H) (v : V) :=
    emb α (colour v) ⟨position edges α v, position_mem_colourSlots colour edges α v⟩
  let dec (α : Fin H) (c : Fin s) (w : Fin (2 ^ width)) : Fin (K + 1) :=
    if h : ∃ j, emb α c j = w then (Classical.choose h).val else 0
  refine ⟨enc, dec, ?_⟩
  intro α v
  let j : {j // j ∈ colourSlots colour edges α (colour v)} :=
    ⟨position edges α v, position_mem_colourSlots colour edges α v⟩
  have hex : ∃ j', emb α (colour v) j' = emb α (colour v) j := ⟨j, rfl⟩
  dsimp [dec, enc]
  rw [dif_pos hex]
  exact congrArg Subtype.val ((emb α (colour v)).injective (Classical.choose_spec hex))

section ShortProtocol

variable {a b width : ℕ}

/-- Executable fixed-length binary encoding, including the empty word when
the address set is a singleton. -/
def bits (k : ℕ) : Fin (2 ^ k) → Fin k → Bool :=
  (CappedSampler.bitsTicketEquiv k).symm

def ofBits (k : ℕ) : (Fin k → Bool) → Fin (2 ^ k) :=
  CappedSampler.bitsTicketEquiv k

@[simp] theorem ofBits_bits (k : ℕ) (j : Fin (2 ^ k)) : ofBits k (bits k j) = j :=
  (CappedSampler.bitsTicketEquiv k).apply_symm_apply j

@[simp] theorem bits_ofBits (k : ℕ) (w : Fin k → Bool) : bits k (ofBits k w) = w :=
  (CappedSampler.bitsTicketEquiv k).symm_apply_apply w

/-- Once the two indices are public, Bob sends the selected array bit. -/
def answerProtocol (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (h : Fin (2 ^ b)) (j : Fin (K + 1)) :
    StrictProtocol (V × Fin m) (Fin (2 ^ a) × Fin (2 ^ b) × Fin n) .bob :=
  .bob (fun y => W y.2.2 (h, j)) (.leaf .alice false) (.leaf .alice true)

@[simp] theorem answerProtocol_eval
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (h : Fin (2 ^ b)) (j : Fin (K + 1)) (x : V × Fin m)
    (y : Fin (2 ^ a) × Fin (2 ^ b) × Fin n) :
    (answerProtocol W h j).eval x y = W y.2.2 (h, j) := by
  simp [answerProtocol, StrictProtocol.eval, StrictProtocol.bob,
    StrictProtocol.leaf, Protocol.eval]

@[simp] theorem answerProtocol_cost
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (h : Fin (2 ^ b)) (j : Fin (K + 1)) :
    (answerProtocol (V := V) (m := m) (a := a) W h j).cost = 1 := rfl

/-- Stage 3: Bob sends dummy bits while Alice identifies the within-colour
position. The protocol then has Bob send the answer. -/
def slotProtocol (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (c : Fin (2 ^ (a + 1))) (α h : Fin (2 ^ b)) :
    StrictProtocol (V × Fin m) (Fin (2 ^ a) × Fin (2 ^ b) × Fin n) .bob :=
  .exchange width .bob (fun x => bits width (code.encode α x.1))
    (fun _ _ => false)
    (fun j _ => answerProtocol W h (code.decode α c (ofBits width j)))

theorem slotProtocol_eval (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (α h : Fin (2 ^ b)) (x : V × Fin m)
    (y : Fin (2 ^ a) × Fin (2 ^ b) × Fin n) :
    (slotProtocol colour edges code W (colour x.1) α h).eval x y =
      W y.2.2 (h, position edges α x.1) := by
  simp [slotProtocol, code.correct]

theorem slotProtocol_cost_le (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (c : Fin (2 ^ (a + 1))) (α h : Fin (2 ^ b)) :
    (slotProtocol (m := m) colour edges code W c α h).cost ≤ 2 * width + 1 := by
  exact StrictProtocol.exchange_cost_le _ _ _ _ _ 1 (by intros; simp)

/-- Stage 2: Bob transmits the edge address while Alice transmits her selected
address. Alice needs only the already-public coordinate `g`, not `α`, to
choose those bits. The stage is empty for `b=0`. -/
def addressProtocol (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (c : Fin (2 ^ (a + 1))) (g : Fin (2 ^ a)) :
    StrictProtocol (V × Fin m) (Fin (2 ^ a) × Fin (2 ^ b) × Fin n) .bob :=
  .exchange b .bob (fun x => bits b (C x.2 g)) (fun y => bits b y.2.1)
    (fun h α => slotProtocol colour edges code W c (ofBits b α) (ofBits b h))

theorem addressProtocol_eval (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (g : Fin (2 ^ a)) (x : V × Fin m)
    (y : Fin (2 ^ a) × Fin (2 ^ b) × Fin n) :
    (addressProtocol colour edges code C W (colour x.1) g).eval x y =
      W y.2.2 (C x.2 g, position edges y.2.1 x.1) := by
  simp [addressProtocol, slotProtocol_eval]

theorem addressProtocol_cost_le (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (c : Fin (2 ^ (a + 1))) (g : Fin (2 ^ a)) :
    (addressProtocol colour edges code C W c g).cost ≤ 2 * b + 2 * width + 1 := by
  exact (StrictProtocol.exchange_cost_le _ _ _ _ _ (2 * width + 1)
    (fun _ _ => slotProtocol_cost_le _ _ _ _ _ _ _)).trans (by omega)

/-- After the first `a` pairs, Alice sends the remaining colour bit. All
continuations depend on the communicated words, not on hidden input data. -/
def finalColourProtocol (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (tail : Fin a → Bool) (g : Fin (2 ^ a)) :
    StrictProtocol (V × Fin m) (Fin (2 ^ a) × Fin (2 ^ b) × Fin n) .alice :=
  .alice (fun x => bits (a + 1) (colour x.1) 0)
    (addressProtocol colour edges code C W (ofBits (a + 1) (Fin.cons false tail)) g)
    (addressProtocol colour edges code C W (ofBits (a + 1) (Fin.cons true tail)) g)

theorem finalColourProtocol_eval (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (g : Fin (2 ^ a)) (x : V × Fin m)
    (y : Fin (2 ^ a) × Fin (2 ^ b) × Fin n) :
    (finalColourProtocol colour edges code C W
      (Fin.tail (bits (a + 1) (colour x.1))) g).eval x y =
      W y.2.2 (C x.2 g, position edges y.2.1 x.1) := by
  have hr : Fin.cons (bits (a + 1) (colour x.1) 0)
      (Fin.tail (bits (a + 1) (colour x.1))) = bits (a + 1) (colour x.1) :=
    Fin.cons_self_tail _
  cases hh : bits (a + 1) (colour x.1) 0 <;>
    simp only [hh] at hr <;>
    simpa [finalColourProtocol, StrictProtocol.eval, StrictProtocol.alice,
      Protocol.eval, hh, hr] using addressProtocol_eval colour edges code C W g x y

theorem finalColourProtocol_cost_le (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool)
    (tail : Fin a → Bool) (g : Fin (2 ^ a)) :
    (finalColourProtocol colour edges code C W tail g).cost ≤
      2 * b + 2 * width + 2 := by
  have h0 := addressProtocol_cost_le colour edges code C W
    (ofBits (a + 1) (Fin.cons false tail)) g
  have h1 := addressProtocol_cost_le colour edges code C W
    (ofBits (a + 1) (Fin.cons true tail)) g
  simp only [StrictProtocol.cost] at h0 h1
  change 1 + max _ _ ≤ _
  omega

/-- The manuscript's three-stage schedule as a literal binary protocol tree.
Only its existence proof uses a colour/slot code; `matrix` does not. -/
def shortProtocol (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool) :
    StrictProtocol (V × Fin m) (Fin (2 ^ a) × Fin (2 ^ b) × Fin n) .alice :=
  .exchange a .alice (fun x => Fin.tail (bits (a + 1) (colour x.1)))
    (fun y => bits a y.1)
    (fun tail g => finalColourProtocol colour edges code C W tail (ofBits a g))

theorem shortProtocol_computes (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool) :
    (shortProtocol colour edges code C W).Computes (matrix edges C W) := by
  intro x y
  simp [shortProtocol, finalColourProtocol_eval, matrix]

theorem shortProtocol_cost_le (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool) :
    (shortProtocol colour edges code C W).cost ≤ 2 * a + 2 * b + 2 * width + 2 := by
  exact (StrictProtocol.exchange_cost_le _ _ _ _ _ (2 * b + 2 * width + 2)
    (fun _ _ => finalColourProtocol_cost_le _ _ _ _ _ _ _)).trans (by omega)

/-- Every-tape upper bound: arbitrary arrays, including repeated samples.
The only substantive hypothesis is a finite within-colour slot bound. -/
theorem Dalt_le_of_slot_card [Fintype V]
    (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (hcard : ∀ α c, (colourSlots colour edges α c).card ≤ 2 ^ width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool) :
    Dalt .alice (matrix edges C W) ≤ 2 * a + 2 * b + 2 * width + 2 := by
  let code := slotCodeOfCard colour edges hcard
  exact (Dalt_le_cost (shortProtocol colour edges code C W)
    (shortProtocol_computes _ _ _ _ _)).trans (shortProtocol_cost_le _ _ _ _ _)

end ShortProtocol

section Budgets

variable [Fintype V]

/-- The balanced promise is used only here, after the input matrix has been
fixed. Every real edge has the required minimum count for every colour. -/
theorem balanced_budget_succ (a b : ℕ)
    (edges : Fin (2 ^ b) → Option (Fin (2 ^ (a + 1) * 2 ^ (a + 1)) ↪ V))
    (colour : V → Fin (2 ^ (a + 1)))
    (hbalanced : ∀ α e, edges α = some e → ∀ c,
      2 ^ (a + 1) - 1 ≤ colourFiberCard (fun i => colour (e i)) c)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ (a + 1) * 2 ^ (a + 1) + 1) → Bool) :
    Dalt .alice (matrix edges C W) ≤ 2 * b + 4 * (a + 1) + 2 := by
  have hc : ∀ α c, (colourSlots colour edges α c).card ≤ 2 ^ (a + 2) := by
    intro α c
    cases he : edges α with
    | none => simpa [colourSlots, he] using Nat.one_le_pow (a + 2) 2 (by omega)
    | some e =>
        rw [colourSlots_card_real colour edges α e he c]
        have h := pow_two_card_colourSlot_le (a + 1)
          (fun i => colour (e i)) (hbalanced α e he) c
        rw [card_colourSlot] at h
        simpa only [colourFiberCard, Nat.add_assoc] using h
  exact (Dalt_le_of_slot_card colour edges hc C W).trans (by omega)

/-- Exact manuscript budget `B = 2b+4t+2`, on every tape. This includes `b=0`
and an empty source edge set (all edge labels unused). -/
theorem balanced_budget (t b : ℕ) (ht : 1 ≤ t)
    (edges : Fin (2 ^ b) → Option (Fin (2 ^ t * 2 ^ t) ↪ V))
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ α e, edges α = some e → ∀ c,
      2 ^ t - 1 ≤ colourFiberCard (fun i => colour (e i)) c)
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool) :
    Dalt .alice (matrix edges C W) ≤ 2 * b + 4 * t + 2 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  exact balanced_budget_succ a b edges colour hbalanced C W

/-- The YES upper bound for an ordinary finite source hypergraph, after
placing its distinct ordered edges at the public padded addresses. The
empty edge family is allowed and does not require a selected real edge. -/
theorem placed_balanced_budget (t b : ℕ) (ht : 1 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V) (index : E ↪ Fin (2 ^ b))
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤ colourFiberCard (fun i => colour (edges e i)) c)
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool) :
    Dalt .alice (matrix (placeEdges edges index) C W) ≤ 2 * b + 4 * t + 2 := by
  apply balanced_budget t b ht _ colour _ C W
  intro α e he c
  obtain ⟨j, _, rfl⟩ := (placeEdges_eq_some_iff edges index α e).mp he
  exact hbalanced j c

/-- The neutral slot and every edge position fit into `2t+1` bits even
without a colouring. The chosen constant colour does not affect the matrix. -/
theorem universal_budget_succ (a b : ℕ)
    (edges : Fin (2 ^ b) → Option (Fin (2 ^ (a + 1) * 2 ^ (a + 1)) ↪ V))
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ (a + 1) * 2 ^ (a + 1) + 1) → Bool) :
    Dalt .alice (matrix edges C W) ≤ 2 * b + 6 * (a + 1) + 2 := by
  let colour : V → Fin (2 ^ (a + 1)) := fun _ => 0
  have hpow : 2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ (2 * (a + 1)) := by
    simp only [two_mul, pow_add]
  have hcard : ∀ α c, (colourSlots colour edges α c).card ≤ 2 ^ (2 * (a + 1) + 1) := by
    intro α c
    apply (colourSlots_card_le colour edges α c).trans
    rw [hpow, pow_succ]
    have hp : 1 ≤ 2 ^ (2 * (a + 1)) := Nat.one_le_pow _ _ (by omega)
    omega
  exact (Dalt_le_of_slot_card colour edges hcard C W).trans (by omega)

/-- Unconditional `B+2t` bound from the same constructor and actual schedule. -/
theorem universal_budget (t b : ℕ) (ht : 1 ≤ t)
    (edges : Fin (2 ^ b) → Option (Fin (2 ^ t * 2 ^ t) ↪ V))
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool) :
    Dalt .alice (matrix edges C W) ≤ (2 * b + 4 * t + 2) + 2 * t := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  exact (universal_budget_succ a b edges C W).trans (by omega)

/-- Exact number of indexed entries; this counts labels, not distinct
sample values. Runtime for generating/printing them is a separate obligation. -/
theorem table_entry_count :
    Fintype.card (V × Fin m) * Fintype.card (Fin q × Fin H × Fin n) =
      Fintype.card V * m * q * H * n := by
  simp [Nat.mul_assoc]

end Budgets

end Paper2.YaoLookup
