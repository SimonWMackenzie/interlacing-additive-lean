import Paper2.HypergraphClones
import Paper2.YaoLookupBalance
import Paper2.YaoSrcCodecB

/-! Unit 5 segment Y10, structural layer (lane a-yao-owner-1): the explicit,
choice-free clone source for T34 `yao:clones` (lock v12 YA:92-116).

From an occurrence hypergraph `edges : Fin e → Fin K → Fin v` with
`K = 2^t*2^t`, the output Yao source has vertices `(w, r) ↦ w*(K*S)+r`
(`finProdFinEquiv`), padded to one isolated vertex exactly when there are no
clones (YA:113-116, "if needed"), and one edge for every injective lift, in
an explicit list order: original edges in increasing order, and for each the
lifts `r : Fin K → Fin (K*S)` in lexicographic order (first coordinate
slowest), filtered by injectivity.  The list `liftList` has `toFinset` equal
to the admitted `HypergraphClones.enumerateLifts`.  No `Fintype.equivFin`,
no choice in the construction.

Value theorems reuse the admitted `HypergraphClones.lifted_colours` and
`HypergraphClones.no_proper_colouring_preserved` by exact name.
The physical clone MACHINE is not in this module (NOT DONE).  The occurrence
input codec at the end is a Yao-chosen DRAFT pending author decision AD-1. -/

namespace Paper2.YaoCloneSource

open Paper2.HypergraphClones
open Paper2.YaoSourceCodec
open Paper2.RecursiveLabelCodecScratch

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-! ## Lexicographic enumeration of all functions `Fin n → Fin m` -/

def allFuns (m : ℕ) : (n : ℕ) → List (Fin n → Fin m)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange m).flatMap (fun a => (allFuns m n).map (Fin.cons a))

theorem mem_allFuns (m : ℕ) : (n : ℕ) → (f : Fin n → Fin m) → f ∈ allFuns m n
  | 0, f => by
      have : f = Fin.elim0 := funext (fun i => i.elim0)
      simp [allFuns, this]
  | n + 1, f => by
      simp only [allFuns, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
      exact ⟨f 0, Fin.tail f, mem_allFuns m n _, Fin.cons_self_tail f⟩

theorem length_allFuns (m : ℕ) : (n : ℕ) → (allFuns m n).length = m ^ n
  | 0 => by simp [allFuns]
  | n + 1 => by
      simp only [allFuns, List.length_flatMap, List.length_map, length_allFuns m n]
      simp [pow_succ, Nat.mul_comm]

/-! ## One edge's lifts, as an explicit list -/

variable {K v S : ℕ}

def liftList (edge : Fin K → Fin v) (S : ℕ) : List (Fin K → Fin (K * S)) :=
  (allFuns (K * S) K).filter (fun r => decide (Function.Injective (fun i => (edge i, r i))))

theorem mem_liftList (edge : Fin K → Fin v) (r : Fin K → Fin (K * S)) :
    r ∈ liftList edge S ↔ Function.Injective (fun i => (edge i, r i)) := by
  simp [liftList, mem_allFuns]

/-- The explicit list enumerates exactly the admitted finset of lifts. -/
theorem liftList_toFinset (edge : Fin K → Fin v) :
    (liftList edge S).toFinset = enumerateLifts edge S := by
  ext r
  simp only [List.mem_toFinset, mem_liftList, mem_enumerateLifts]

theorem length_liftList_le (edge : Fin K → Fin v) :
    (liftList edge S).length ≤ (K * S) ^ K := by
  calc (liftList edge S).length ≤ (allFuns (K * S) K).length := List.length_filter_le _ _
    _ = (K * S) ^ K := length_allFuns _ _

/-! ## The clone source -/

variable {e : ℕ}

/-- All (edge, lift) pairs, edges in order, lifts lexicographic. -/
def allLifts (edges : Fin e → Fin K → Fin v) (S : ℕ) :
    List (Fin e × (Fin K → Fin (K * S))) :=
  (List.finRange e).flatMap (fun i => (liftList (edges i) S).map (fun r => (i, r)))

theorem mem_allLifts (edges : Fin e → Fin K → Fin v) (i : Fin e) (r : Fin K → Fin (K * S)) :
    (i, r) ∈ allLifts edges S ↔ Function.Injective (fun j => (edges i j, r j)) := by
  simp [allLifts, mem_liftList]

theorem allLifts_injective (edges : Fin e → Fin K → Fin v) (p : Fin e × (Fin K → Fin (K * S)))
    (hp : p ∈ allLifts edges S) : Function.Injective (fun j => (edges p.1 j, p.2 j)) :=
  (mem_allLifts edges p.1 p.2).1 hp

/-- Output edge count. -/
def cloneEdgeCount (edges : Fin e → Fin K → Fin v) (S : ℕ) : ℕ := (allLifts edges S).length

theorem cloneEdgeCount_le (edges : Fin e → Fin K → Fin v) :
    cloneEdgeCount edges S ≤ e * (K * S) ^ K := by
  unfold cloneEdgeCount allLifts
  rw [List.length_flatMap]
  calc ((List.finRange e).map (fun i => ((liftList (edges i) S).map (fun r => (i, r))).length)).sum
      ≤ ((List.finRange e).map (fun _ => (K * S) ^ K)).sum := by
        apply List.sum_le_sum
        intro i _
        simpa using length_liftList_le (S := S) (edges i)
    _ = e * (K * S) ^ K := by simp

/-- Output vertex count: all clones, plus one isolated vertex only if needed. -/
def cloneVertexCount (v K S : ℕ) : ℕ := max 1 (v * (K * S))

theorem cloneVertexCount_pos (v K S : ℕ) : 0 < cloneVertexCount v K S := by
  unfold cloneVertexCount; omega

/-- Vertex numbering `(w, r) ↦ w*(K*S)+r`. -/
def vertexNumber (v K S : ℕ) (w : Fin v × Fin (K * S)) : Fin (cloneVertexCount v K S) :=
  Fin.castLE (by unfold cloneVertexCount; omega) (finProdFinEquiv w)

theorem vertexNumber_injective (v K S : ℕ) : Function.Injective (vertexNumber v K S) := by
  intro a b h
  exact finProdFinEquiv.injective (Fin.castLE_injective _ h)

theorem vertexNumber_val (v K S : ℕ) (w : Fin v × Fin (K * S)) :
    (vertexNumber v K S w).val = w.1.val * (K * S) + w.2.val := by
  simp [vertexNumber, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- The explicit output edges. -/
def cloneEdges (edges : Fin e → Fin K → Fin v) (S : ℕ) :
    Fin (cloneEdgeCount edges S) → Fin K ↪ Fin (cloneVertexCount v K S) :=
  fun k =>
    ⟨fun j => vertexNumber v K S (edges ((allLifts edges S).get k).1 j,
        ((allLifts edges S).get k).2 j),
      fun _j₁ _j₂ h => allLifts_injective edges _ (List.get_mem _ _)
        (vertexNumber_injective v K S h)⟩

/-- The clone source in the Yao consumer shape (`K = 2^t*2^t`). -/
def cloneSource (t S : ℕ) (x : Σ v : ℕ, Σ e : ℕ, Fin e → Fin (2 ^ t * 2 ^ t) → Fin v) :
    YaoSource t :=
  ⟨cloneVertexCount x.1 (2 ^ t * 2 ^ t) S, cloneEdgeCount x.2.2 S, cloneEdges x.2.2 S⟩

/-! ## Correspondence with the admitted `HypergraphClones` construction -/

/-- The admitted `Edge` element named by output index `k`. -/
def toEdge (edges : Fin e → Fin K → Fin v) (k : Fin (cloneEdgeCount edges S)) :
    Edge edges S :=
  ⟨((allLifts edges S).get k).1,
    ⟨((allLifts edges S).get k).2, allLifts_injective edges _ (List.get_mem _ _)⟩⟩

theorem cloneEdges_eq_incidence (edges : Fin e → Fin K → Fin v)
    (k : Fin (cloneEdgeCount edges S)) (j : Fin K) :
    cloneEdges edges S k j = vertexNumber v K S (incidence edges (toEdge edges k) j) := rfl

/-- Every admitted lift occurs at some output index (surjectivity of the order). -/
theorem toEdge_surjective (edges : Fin e → Fin K → Fin v) :
    Function.Surjective (toEdge (S := S) edges) := by
  rintro ⟨i, r, hr⟩
  have hm : (i, r) ∈ allLifts edges S := (mem_allLifts edges i r).2 hr
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 hm
  refine ⟨k, ?_⟩
  unfold toEdge
  have h1 : ((allLifts edges S).get k).1 = i := by rw [hk]
  have h2 : ((allLifts edges S).get k).2 = r := by rw [hk]
  subst h1
  congr 1
  exact Subtype.ext h2

/-! ## YES transfer: ordered colour vectors are preserved exactly -/

/-- An original colouring read on clones (the padded vertex gets `c₀`). -/
def liftColour {C : Type*} (c₀ : C) (colour : Fin v → C) :
    Fin (cloneVertexCount v K S) → C :=
  fun w => if h : w.val < v * (K * S) then colour (finProdFinEquiv.symm ⟨w.val, h⟩).1 else c₀

theorem liftColour_vertexNumber {C : Type*} (c₀ : C) (colour : Fin v → C)
    (w : Fin v × Fin (K * S)) :
    liftColour c₀ colour (vertexNumber v K S w) = colour w.1 := by
  unfold liftColour
  have hlt : (vertexNumber v K S w).val < v * (K * S) := by
    have h1 := w.1.isLt
    have h2 := w.2.isLt
    rw [vertexNumber_val]
    nlinarith
  rw [dif_pos hlt]
  have : (⟨(vertexNumber v K S w).val, hlt⟩ : Fin (v * (K * S))) = finProdFinEquiv w := by
    ext; simp [vertexNumber]
  rw [this, Equiv.symm_apply_apply]

/-- Each output edge carries exactly the ordered colour vector of its
original edge (admitted `lifted_colours`). -/
theorem clone_colour_vector {C : Type*} (c₀ : C) (colour : Fin v → C)
    (edges : Fin e → Fin K → Fin v) (k : Fin (cloneEdgeCount edges S)) :
    (fun j => liftColour c₀ colour (cloneEdges edges S k j)) =
      fun j => colour (edges (toEdge edges k).1 j) := by
  funext j
  rw [cloneEdges_eq_incidence, liftColour_vertexNumber]
  exact congrFun (lifted_colours colour edges (toEdge edges k)) j

/-- YES clause in the banked consumer form (`hbalanced` of
`materialize_yes_bound`). -/
theorem clone_balanced {s : ℕ} (c₀ : Fin s) (colour : Fin v → Fin s)
    (edges : Fin e → Fin K → Fin v)
    (hbal : ∀ i c, s - 1 ≤ Paper2.YaoLookup.colourFiberCard (fun j => colour (edges i j)) c) :
    ∀ k c, s - 1 ≤ Paper2.YaoLookup.colourFiberCard
      (fun j => liftColour c₀ colour (cloneEdges edges S k j)) c := by
  intro k c
  rw [clone_colour_vector]
  exact hbal _ c

/-! ## NO transfer (admitted `no_proper_colouring_preserved`) -/

theorem clone_no_proper_colouring (hS : 0 < S) (edges : Fin e → Fin K → Fin v)
    (hno : ∀ colour : Fin v → Fin S, ∃ i c, ∀ j, colour (edges i j) = c) :
    ∀ colour : Fin (cloneVertexCount v K S) → Fin S,
      ∃ k c, ∀ j, colour (cloneEdges edges S k j) = c := by
  intro colour
  obtain ⟨⟨i, r⟩, b, hb⟩ := no_proper_colouring_preserved hS edges hno
    (fun w => colour (vertexNumber v K S w))
  obtain ⟨k, hk⟩ := toEdge_surjective (S := S) edges ⟨i, r⟩
  refine ⟨k, b, fun j => ?_⟩
  rw [cloneEdges_eq_incidence, hk]
  exact hb j

/-! ## Sizes -/

theorem cloneSource_sizes (t S : ℕ)
    (x : Σ v : ℕ, Σ e : ℕ, Fin e → Fin (2 ^ t * 2 ^ t) → Fin v) :
    (cloneSource t S x).1 = max 1 (x.1 * (2 ^ t * 2 ^ t * S)) ∧
      0 < (cloneSource t S x).1 ∧
      (cloneSource t S x).2.1 ≤ x.2.1 * (2 ^ t * 2 ^ t * S) ^ (2 ^ t * 2 ^ t) :=
  ⟨rfl, cloneVertexCount_pos _ _ _, cloneEdgeCount_le _⟩

/-! ## DRAFT (pending AD-1): a Yao-chosen occurrence input codec

The occurrence format is fixed by author decision AD-1 (the X05 contract).
Until then this codec is a clearly marked DRAFT: `unary v ++ unary e ++`
the same admitted body codec, with NO injectivity filter. -/

abbrev DraftOccSource (t : ℕ) := Σ v : ℕ, Σ e : ℕ, Fin e → Fin (2 ^ t * 2 ^ t) → Fin v

def draftOccEncode {t : ℕ} (x : DraftOccSource t) : List Bool :=
  unaryNat x.1 ++ unaryNat x.2.1 ++
    (bodyCodec t x.1 x.2.1).encode (fun k => x.2.2 (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2)

def draftOccDecode (t : ℕ) (bits : List Bool) : Option (DraftOccSource t × List Bool) := do
  let (v, r₁) ← decodeUnary bits
  let (e, r₂) ← decodeUnary r₁
  let (f, r₃) ← (bodyCodec t v e).decode r₂
  some (⟨v, e, fun i j => f (finProdFinEquiv (i, j))⟩, r₃)

theorem draftOccDecode_encode {t : ℕ} (x : DraftOccSource t) (rest : List Bool) :
    draftOccDecode t (draftOccEncode x ++ rest) = some (x, rest) := by
  obtain ⟨v, e, edges⟩ := x
  simp only [draftOccDecode, draftOccEncode, List.append_assoc, decodeUnary_unaryNat,
    (bodyCodec t v e).roundtrip, Option.bind_eq_bind, Option.bind_some]
  congr
  funext i j
  simp

#print axioms mem_allFuns
#print axioms liftList_toFinset
#print axioms cloneEdgeCount_le
#print axioms toEdge_surjective
#print axioms clone_colour_vector
#print axioms clone_balanced
#print axioms clone_no_proper_colouring
#print axioms cloneSource_sizes
#print axioms draftOccDecode_encode

end Paper2.YaoCloneSource
