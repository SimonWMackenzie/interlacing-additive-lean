import Paper2.YaoCloneSrc

/-! Unit 5 segment Y10 (lane a-yao-clone-owner-1): the list-level specification
of the physical clone machine and its bridge to the admitted structural layer.

The machine of `YaoCloneMachine` is stated on label-vector lists
`ls : List (Fin K → ℕ)` (one vector per occurrence edge).  This module proves
that for an occurrence source `x` (the Yao-chosen DRAFT occurrence codec of
the admitted `Paper2.YaoCloneSrc`, pending AD-1):

* `draftOccEncode x = occInput x.1 (labelsOf x)`   (the machine input), and
* `encode (cloneSource t S x) = cloneOutput (K*S) x.1 (labelsOf x)`
  (the Option B code of the admitted clone source, the machine output),

with `K = 2^t*2^t`.  The lift filter used by the machine is the finite
equality-pattern test `injB (eqPat l)`, proved equal to the admitted
`liftList` injectivity filter. -/

namespace Paper2.YaoCloneMachine

open Paper2.YaoCloneSource
open Paper2.YaoSourceCodec
open Paper2.RecursiveLabelCodecScratch
open Paper2.UnaryFieldListParserScratch

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Unary marks. -/
abbrev rep (n : ℕ) : List Bool := List.replicate n true

/-- One bounded-unary field, the admitted `finCodec` encoding. -/
def field (x : ℕ) : List Bool := rep x ++ [false]

variable {K : ℕ}

/-- The equality pattern of one edge's labels (finite data). -/
def eqPat (l : Fin K → ℕ) : Fin K → Fin K → Bool := fun a b => decide (l a = l b)

/-- The lift test decided from an equality pattern. -/
def injB {M : ℕ} (P : Fin K → Fin K → Bool) (r : Fin K → Fin M) : Bool :=
  decide (∀ a b : Fin K, a ≠ b → r a = r b → P a b = false)

/-- The input fields of one occurrence edge. -/
def edgeInput (l : Fin K → ℕ) : List Bool := (List.ofFn fun j : Fin K => field (l j)).flatten

/-- The output fields of one lift: labels `l j * M + r j`. -/
def liftBlock (M : ℕ) (l : Fin K → ℕ) (r : Fin K → Fin M) : List Bool :=
  (List.ofFn fun j : Fin K => field (l j * M + (r j).val)).flatten

/-- The injective lifts of one edge, in the explicit lexicographic order. -/
def goodLifts (M : ℕ) (l : Fin K → ℕ) : List (Fin K → Fin M) :=
  (allFuns M K).filter (injB (eqPat l))

def edgeBlock (M : ℕ) (l : Fin K → ℕ) : List Bool := (goodLifts M l).flatMap (liftBlock M l)

/-- Machine input: `unary v ++ unary e ++` the edges' fields. -/
def occInput (v : ℕ) (ls : List (Fin K → ℕ)) : List Bool :=
  unaryNat v ++ unaryNat ls.length ++ ls.flatMap edgeInput

/-- Machine output. -/
def cloneOutput (M v : ℕ) (ls : List (Fin K → ℕ)) : List Bool :=
  unaryNat (max 1 (v * M)) ++ unaryNat (ls.map (fun l => (goodLifts M l).length)).sum ++
    ls.flatMap (edgeBlock M)

/-! ## The equality-pattern test is the admitted injectivity filter -/

theorem injB_iff {v M : ℕ} (edge : Fin K → Fin v) (r : Fin K → Fin M) :
    injB (eqPat (fun j => (edge j).val)) r = decide (Function.Injective (fun j => (edge j, r j))) := by
  unfold injB eqPat
  apply decide_eq_decide.mpr
  constructor
  · intro h a b hab
    by_contra hne
    have h1 := h a b hne (congrArg Prod.snd hab)
    have h2 : (edge a).val = (edge b).val := congrArg Fin.val (congrArg Prod.fst hab)
    simp [h2] at h1
  · intro h a b hne hr
    by_contra hP
    have hv : (edge a).val = (edge b).val := by simpa using hP
    exact hne (h (Prod.ext (Fin.ext hv) hr))

theorem goodLifts_eq_liftList {v S : ℕ} (edge : Fin K → Fin v) :
    goodLifts (K * S) (fun j => (edge j).val) = liftList edge S := by
  unfold goodLifts liftList
  congr 1
  funext r
  exact injB_iff edge r

/-! ## Flattening over `finProdFinEquiv` -/

theorem ofFn_prod {α : Type*} {m n : ℕ} (h : Fin m → Fin n → α) :
    List.ofFn (fun k : Fin (m * n) => h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) =
      (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => h i j).flatten := by
  rw [List.ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i =>
    congrArg List.ofFn (funext fun j => ?_)))
  have hk : finProdFinEquiv.symm (⟨i.val * n + j.val, by
      calc i.val * n + j.val < (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ m * n := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (m * n)) = (i, j) := by
    rw [Equiv.symm_apply_eq]
    ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [hk]

theorem tokens_eq_flatten {a : ℕ} (xs : List (Fin a)) :
    tokens xs = (xs.map fun y => field y.val).flatten := by
  simp [tokens, List.flatMap_def, finCodec, field]

theorem tokens_ofFn_prod {a m n : ℕ} (h : Fin m → Fin n → Fin a) :
    tokens (List.ofFn (fun k : Fin (m * n) => h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) =
      (List.ofFn fun i : Fin m => (List.ofFn fun j : Fin n => field (h i j).val).flatten).flatten := by
  rw [ofFn_prod, tokens_eq_flatten, List.map_flatten, List.flatten_flatten]
  congr 1
  simp [List.map_ofFn, Function.comp_def]

/-! ## The machine's input and output are the DRAFT occurrence code and the
Option B code of the admitted clone source -/

/-- The label vectors of an occurrence source. -/
def labelsOf {t : ℕ} (x : DraftOccSource t) : List (Fin (2 ^ t * 2 ^ t) → ℕ) :=
  List.ofFn fun i j => (x.2.2 i j).val

theorem length_labelsOf {t : ℕ} (x : DraftOccSource t) : (labelsOf x).length = x.2.1 := by
  simp [labelsOf]

theorem draftOccEncode_eq {t : ℕ} (x : DraftOccSource t) :
    draftOccEncode x = occInput x.1 (labelsOf x) := by
  obtain ⟨v, e, edges⟩ := x
  simp only [draftOccEncode, occInput, length_labelsOf, bodyCodec, piCodec_encode_eq_tokens]
  congr 1
  rw [tokens_ofFn_prod (m := e) (n := 2 ^ t * 2 ^ t) edges]
  simp [labelsOf, List.flatMap_def, List.map_ofFn, Function.comp_def, edgeInput]

theorem ofFn_get_map {α β : Type*} (L : List α) (g : α → β) :
    List.ofFn (fun k : Fin L.length => g (L.get k)) = L.map g := by
  apply List.ext_getElem <;> simp

theorem cloneEdgeCount_eq {S v e : ℕ} (edges : Fin e → Fin K → Fin v) :
    cloneEdgeCount edges S =
      ((List.ofFn fun i j => (edges i j).val).map (fun l => (goodLifts (K * S) l).length)).sum := by
  unfold cloneEdgeCount allLifts
  rw [List.length_flatMap]
  simp only [List.length_map, List.map_ofFn, Function.comp_def]
  rw [← List.ofFn_eq_map]
  exact congrArg List.sum (congrArg List.ofFn (funext fun i => by rw [goodLifts_eq_liftList]))

theorem encode_cloneSource_eq {t : ℕ} (S : ℕ) (x : DraftOccSource t) :
    encode (cloneSource t S x) = cloneOutput (2 ^ t * 2 ^ t * S) x.1 (labelsOf x) := by
  obtain ⟨v, e, edges⟩ := x
  simp only [encode, cloneSource, cloneOutput, bodyCodec, piCodec_encode_eq_tokens]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl (by rw [cloneEdgeCount_eq]; rfl)) ?_
  rw [show flatten (cloneEdges edges S) = (fun k : Fin (cloneEdgeCount edges S * (2 ^ t * 2 ^ t)) =>
      cloneEdges edges S (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      from rfl, tokens_ofFn_prod (fun i j => cloneEdges edges S i j)]
  have hb : ∀ k : Fin (cloneEdgeCount edges S),
      (List.ofFn fun j : Fin (2 ^ t * 2 ^ t) => field (cloneEdges edges S k j).val).flatten =
        (fun p : Fin e × (Fin (2 ^ t * 2 ^ t) → Fin (2 ^ t * 2 ^ t * S)) =>
          liftBlock (2 ^ t * 2 ^ t * S) (fun j => (edges p.1 j).val) p.2)
          ((allLifts edges S).get k) := by
    intro k
    simp only [liftBlock]
    refine congrArg List.flatten (congrArg List.ofFn (funext fun j => congrArg field ?_))
    show (vertexNumber v (2 ^ t * 2 ^ t) S _).val = _
    rw [vertexNumber_val]
  simp only [hb]
  have hofn := ofFn_get_map (allLifts edges S) (fun p : Fin e × (Fin (2 ^ t * 2 ^ t) → Fin (2 ^ t * 2 ^ t * S)) =>
          liftBlock (2 ^ t * 2 ^ t * S) (fun j => (edges p.1 j).val) p.2)
  simp only [cloneEdgeCount] at hofn ⊢
  rw [hofn]
  unfold allLifts
  rw [List.flatMap_def, List.map_flatten, List.flatten_flatten]
  simp only [List.map_map, Function.comp_def]
  simp only [labelsOf, List.flatMap_def, List.map_ofFn, Function.comp_def, edgeBlock]
  rw [List.ofFn_eq_map]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [goodLifts_eq_liftList]

#print axioms injB_iff
#print axioms goodLifts_eq_liftList
#print axioms draftOccEncode_eq
#print axioms cloneEdgeCount_eq
#print axioms encode_cloneSource_eq

end Paper2.YaoCloneMachine
