import Paper2.YaoLookup

/-!
# Executable entries for the sampled Yao matrix

Frozen v12 Section 7 `yao:entry`, and Appendix B `yao:materialization`.
The finite communication proof permits arbitrary local computation. This
module nevertheless gives an executable position/table evaluator and proves
that its entries are exactly those of the matrix in that proof. It does not
claim an encoded-machine running-time bound or a SAT source algorithm.
-/

namespace Paper2.YaoLookup

variable {V : Type*} {K H q m n : ℕ}

section EntryEvaluation

variable [DecidableEq V]

/-- Finite search for a vertex in an ordered edge. The minimum is selected
only to make the evaluator executable; distinctness makes it the unique hit. -/
def edgePositionEval (e : Fin K ↪ V) (v : V) : Fin (K + 1) :=
  let hits := Finset.univ.filter (fun i => e i = v)
  if h : hits.Nonempty then (hits.min' h).succ else 0

theorem edgePositionEval_eq (e : Fin K ↪ V) (v : V) :
    edgePositionEval e v = edgePosition e v := by
  unfold edgePositionEval
  dsimp only
  split
  next h =>
    let hits := Finset.univ.filter (fun i => e i = v)
    have hv : e (hits.min' h) = v :=
      (Finset.mem_filter.mp (Finset.min'_mem hits h)).2
    have hp := edgePosition_apply e (hits.min' h)
    rw [hv] at hp
    exact hp.symm
  next h =>
    symm
    apply edgePosition_absent
    intro i hi
    exact h ⟨i, by simp [hi]⟩

/-- Unused addresses are handled without inspecting any edge or vertex. -/
def positionEval (edges : Fin H → Option (Fin K ↪ V))
    (α : Fin H) (v : V) : Fin (K + 1) :=
  match edges α with
  | none => 0
  | some e => edgePositionEval e v

theorem positionEval_eq (edges : Fin H → Option (Fin K ↪ V))
    (α : Fin H) (v : V) : positionEval edges α v = position edges α v := by
  cases he : edges α <;> simp [positionEval, position, he, edgePositionEval_eq]

/-- A total executable table-entry function using the original labelled
samples. The constructor still accepts no colouring or protocol witness. -/
def matrixEval (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H)
    (W : Fin n → Fin H × Fin (K + 1) → Bool) :
    (V × Fin m) → (Fin q × Fin H × Fin n) → Bool :=
  fun x y => W y.2.2 (C x.2 y.1, positionEval edges y.2.1 x.1)

theorem matrixEval_eq (edges : Fin H → Option (Fin K ↪ V))
    (C : Fin m → Fin q → Fin H) (W : Fin n → Fin H × Fin (K + 1) → Bool) :
    matrixEval edges C W = matrix edges C W := by
  funext x y
  simp [matrixEval, matrix, positionEval_eq]

/-- Every short protocol proved for the finite matrix therefore computes
the very same executable table, entry for entry. -/
theorem shortProtocol_computes_matrixEval {a b width : ℕ}
    (colour : V → Fin (2 ^ (a + 1)))
    (edges : Fin (2 ^ b) → Option (Fin K ↪ V))
    (code : SlotCode colour edges width)
    (C : Fin m → Fin (2 ^ a) → Fin (2 ^ b))
    (W : Fin n → Fin (2 ^ b) × Fin (K + 1) → Bool) :
    (shortProtocol colour edges code C W).Computes (matrixEval edges C W) := by
  rw [matrixEval_eq]
  exact shortProtocol_computes _ _ _ _ _

end EntryEvaluation

/-- Public padding parameter from the number of input edges alone. -/
def paddedEdgeBits (edgeCount : ℕ) : ℕ := Nat.clog 2 (max 1 edgeCount)

def paddedEdgeCount (edgeCount : ℕ) : ℕ := 2 ^ paddedEdgeBits edgeCount

theorem le_paddedEdgeCount (edgeCount : ℕ) : edgeCount ≤ paddedEdgeCount edgeCount :=
  (Nat.le_max_right 1 edgeCount).trans (Nat.le_pow_clog (by decide) _)

/-- The selected power of two is the least admissible one, including the
empty edge set whose selected exponent is zero. -/
theorem paddedEdgeBits_minimal (edgeCount k : ℕ) :
    paddedEdgeBits edgeCount ≤ k ↔ max 1 edgeCount ≤ 2 ^ k :=
  Nat.clog_le_iff_le_pow (by decide)

@[simp] theorem paddedEdgeBits_zero : paddedEdgeBits 0 = 0 := by
  simp [paddedEdgeBits]

@[simp] theorem paddedEdgeCount_zero : paddedEdgeCount 0 = 1 := by
  simp [paddedEdgeCount]

/-- Real edges receive their own numerical indices; remaining power-of-two
indices are unused. There is no search for a colouring or valid sample. -/
def paddedEdgesEval {edgeCount : ℕ} (edges : Fin edgeCount → Fin K ↪ V) :
    Fin (paddedEdgeCount edgeCount) → Option (Fin K ↪ V) :=
  fun α => if h : α.val < edgeCount then some (edges ⟨α.val, h⟩) else none

theorem paddedEdgesEval_eq {edgeCount : ℕ} (edges : Fin edgeCount → Fin K ↪ V) :
    paddedEdgesEval edges = placeEdges edges (Fin.castLEEmb (le_paddedEdgeCount edgeCount)) := by
  funext α
  by_cases h : α.val < edgeCount
  · let j : Fin edgeCount := ⟨α.val, h⟩
    have hj : (Fin.castLEEmb (le_paddedEdgeCount edgeCount)) j = α := Fin.ext rfl
    have hp := placeEdges_real edges (Fin.castLEEmb (le_paddedEdgeCount edgeCount)) j
    rw [hj] at hp
    simpa only [paddedEdgesEval, dif_pos h] using hp.symm
  · rw [paddedEdgesEval, dif_neg h]
    symm
    apply placeEdges_unused
    intro j hj
    have hv : j.val = α.val := congrArg Fin.val hj
    exact h (hv ▸ j.isLt)

/-- All padded addresses are unused when the source contains no edges. -/
theorem paddedEdgesEval_empty (edges : Fin 0 → Fin K ↪ V)
    (α : Fin (paddedEdgeCount 0)) : paddedEdgesEval edges α = none := by
  simp [paddedEdgesEval]

/-- End-to-end finite YES guarantee for the executable padded table. The
formula/source algorithm and random tape sampler remain separate objects;
all fixed labelled selector and payload arrays satisfy this bound. -/
theorem paddedMatrixEval_balanced_budget [Fintype V] [DecidableEq V] {edgeCount : ℕ}
    (t : ℕ) (ht : 1 ≤ t)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ V)
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤ colourFiberCard (fun i => colour (edges e i)) c)
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (paddedEdgeCount edgeCount))
    (W : Fin n → Fin (paddedEdgeCount edgeCount) × Fin (2 ^ t * 2 ^ t + 1) → Bool) :
    Yao.Dalt .alice (matrixEval (paddedEdgesEval edges) C W) ≤
      2 * paddedEdgeBits edgeCount + 4 * t + 2 := by
  rw [matrixEval_eq, paddedEdgesEval_eq]
  exact placed_balanced_budget t (paddedEdgeBits edgeCount) ht edges
    (Fin.castLEEmb (le_paddedEdgeCount edgeCount)) colour hbalanced C W

theorem paddedMatrixEval_universal_budget [Fintype V] [DecidableEq V] {edgeCount : ℕ}
    (t : ℕ) (ht : 1 ≤ t)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ V)
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (paddedEdgeCount edgeCount))
    (W : Fin n → Fin (paddedEdgeCount edgeCount) × Fin (2 ^ t * 2 ^ t + 1) → Bool) :
    Yao.Dalt .alice (matrixEval (paddedEdgesEval edges) C W) ≤
      (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t := by
  rw [matrixEval_eq]
  exact universal_budget t (paddedEdgeBits edgeCount) ht _ C W

end Paper2.YaoLookup
