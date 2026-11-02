import Paper2.YaoLowerBoundTapes

/-!
# Serialized finite tapes for the Yao matrix generator

Frozen source: Paper 2 v12, Appendix B, `yao:materialization` and
`yao:random-bits`. The tape is now a literal Boolean list of the fixed public
length. Selector bits come first, in `(sample, coordinate, bit)` order;
payload bits follow, in `(sample, address, slot)` order.

Every index equivalence below is computational: product indices use quotient
and remainder, and the sum index uses a prefix offset. No chosen enumeration
of a finite type is used. Reading and writing are mutually inverse, including
empty bit blocks. This file does not assert a machine-time bound for list
indexing or for the complete matrix materializer.
-/

namespace Paper2.YaoLowerBound.Materialization

open Paper2.Yao

/-- Row-major enumeration of three finite coordinates, constructed from
the computational product equivalences. -/
def tripleIndex (a b c : ℕ) : (Fin a × Fin b × Fin c) ≃ Fin (a * b * c) :=
  (Equiv.prodAssoc (Fin a) (Fin b) (Fin c)).symm.trans
    ((finProdFinEquiv.prodCongr (Equiv.refl (Fin c))).trans finProdFinEquiv)

@[simp] theorem tripleIndex_val (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    (tripleIndex a b c (i, j, k)).val = (i.val * b + j.val) * c + k.val := by
  dsimp [tripleIndex, finProdFinEquiv]
  ring

/-- Canonical numbering of every selector and payload bit, with selectors
occupying the initial interval. -/
def tapeIndex (t b lambda : ℕ) : TapePosition t b lambda ≃ Fin (tapeBitCount t b lambda) :=
  ((tripleIndex (selectorCount t b lambda) (2 ^ (t - 1)) b).sumCongr
    (tripleIndex (payloadCount t b lambda) (2 ^ b) (2 ^ t * 2 ^ t + 1))).trans
      finSumFinEquiv

@[simp] theorem tapeIndex_selector_val (t b lambda : ℕ)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) (k : Fin b) :
    (tapeIndex t b lambda (.inl (z, g, k))).val =
      (z.val * 2 ^ (t - 1) + g.val) * b + k.val := by
  change (tripleIndex _ _ _ (z, g, k)).val = _
  exact tripleIndex_val _ _ _ z g k

@[simp] theorem tapeIndex_payload_val (t b lambda : ℕ)
    (l : Fin (payloadCount t b lambda)) (h : Fin (2 ^ b))
    (j : Fin (2 ^ t * 2 ^ t + 1)) :
    (tapeIndex t b lambda (.inr (l, h, j))).val =
      selectorCount t b lambda * 2 ^ (t - 1) * b +
        (l.val * 2 ^ b + h.val) * (2 ^ t * 2 ^ t + 1) + j.val := by
  change selectorCount t b lambda * 2 ^ (t - 1) * b +
    (tripleIndex _ _ _ (l, h, j)).val = _
  rw [tripleIndex_val]
  omega

theorem selector_offset_lt (t b lambda : ℕ)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) (k : Fin b) :
    (z.val * 2 ^ (t - 1) + g.val) * b + k.val < tapeBitCount t b lambda := by
  simpa only [tapeIndex_selector_val] using
    (tapeIndex t b lambda (.inl (z, g, k))).isLt

theorem payload_offset_lt (t b lambda : ℕ)
    (l : Fin (payloadCount t b lambda)) (h : Fin (2 ^ b))
    (j : Fin (2 ^ t * 2 ^ t + 1)) :
    selectorCount t b lambda * 2 ^ (t - 1) * b +
      (l.val * 2 ^ b + h.val) * (2 ^ t * 2 ^ t + 1) + j.val <
        tapeBitCount t b lambda := by
  simpa only [tapeIndex_payload_val] using
    (tapeIndex t b lambda (.inr (l, h, j))).isLt

/-- A literal list of bits with its fixed public length, not an input oracle. -/
abbrev SerializedTape (t b lambda : ℕ) :=
  {bits : List Bool // bits.length = tapeBitCount t b lambda}

/-- Read the list at the canonically numbered position. `List.Vector.get`
is `List.get` with the length proof transported to the public bound. -/
def readTape (t b lambda : ℕ) (bits : SerializedTape t b lambda) :
    TapePosition t b lambda → Bool :=
  fun p => List.Vector.get bits (tapeIndex t b lambda p)

/-- Serialize in increasing canonical-index order. -/
def writeTape (t b lambda : ℕ) (tape : TapePosition t b lambda → Bool) :
    SerializedTape t b lambda :=
  List.Vector.ofFn (fun i => tape ((tapeIndex t b lambda).symm i))

@[simp] theorem readTape_writeTape (t b lambda : ℕ)
    (tape : TapePosition t b lambda → Bool) :
    readTape t b lambda (writeTape t b lambda tape) = tape := by
  funext p
  simp [readTape, writeTape]

@[simp] theorem writeTape_readTape (t b lambda : ℕ)
    (bits : SerializedTape t b lambda) :
    writeTape t b lambda (readTape t b lambda bits) = bits := by
  apply List.Vector.ext
  intro i
  simp [writeTape, readTape]

/-- A computational bijection between serialized lists and all finite tapes. -/
def serializedTapeEquiv (t b lambda : ℕ) :
    SerializedTape t b lambda ≃ (TapePosition t b lambda → Bool) where
  toFun := readTape t b lambda
  invFun := writeTape t b lambda
  left_inv := writeTape_readTape t b lambda
  right_inv := readTape_writeTape t b lambda

theorem readTape_bijective (t b lambda : ℕ) : Function.Bijective (readTape t b lambda) :=
  (serializedTapeEquiv t b lambda).bijective

@[simp] theorem writeTape_length (t b lambda : ℕ)
    (tape : TapePosition t b lambda → Bool) :
    (writeTape t b lambda tape).val.length = tapeBitCount t b lambda :=
  (writeTape t b lambda tape).property

/-- Selector reads use the explicit row-major offset in the original list. -/
theorem readTape_selector (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) (k : Fin b) :
    readTape t b lambda bits (.inl (z, g, k)) =
      bits.val.get ⟨(z.val * 2 ^ (t - 1) + g.val) * b + k.val,
        by rw [bits.property]; exact selector_offset_lt t b lambda z g k⟩ := by
  change bits.val.get _ = bits.val.get _
  congr 1
  apply Fin.ext
  exact tapeIndex_selector_val t b lambda z g k

/-- Payload reads use the selector-prefix offset followed by row-major
payload coordinates. The neutral slot `j=0` is included. -/
theorem readTape_payload (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda)) (h : Fin (2 ^ b))
    (j : Fin (2 ^ t * 2 ^ t + 1)) :
    readTape t b lambda bits (.inr (l, h, j)) =
      bits.val.get ⟨selectorCount t b lambda * 2 ^ (t - 1) * b +
        (l.val * 2 ^ b + h.val) * (2 ^ t * 2 ^ t + 1) + j.val,
        by rw [bits.property]; exact payload_offset_lt t b lambda l h j⟩ := by
  change bits.val.get _ = bits.val.get _
  congr 1
  apply Fin.ext
  exact tapeIndex_payload_val t b lambda l h j

/-- Written lists really contain the original selector bit at its announced
numeric offset. -/
theorem writeTape_selector (t b lambda : ℕ) (tape : TapePosition t b lambda → Bool)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) (k : Fin b) :
    List.Vector.get (writeTape t b lambda tape)
      ⟨(z.val * 2 ^ (t - 1) + g.val) * b + k.val, selector_offset_lt t b lambda z g k⟩ =
      tape (.inl (z, g, k)) := by
  have he : (⟨(z.val * 2 ^ (t - 1) + g.val) * b + k.val,
      selector_offset_lt t b lambda z g k⟩ : Fin (tapeBitCount t b lambda)) =
        tapeIndex t b lambda (.inl (z, g, k)) := by
    apply Fin.ext
    exact (tapeIndex_selector_val t b lambda z g k).symm
  rw [he]
  exact congrFun (readTape_writeTape t b lambda tape) (.inl (z, g, k))

theorem writeTape_payload (t b lambda : ℕ) (tape : TapePosition t b lambda → Bool)
    (l : Fin (payloadCount t b lambda)) (h : Fin (2 ^ b))
    (j : Fin (2 ^ t * 2 ^ t + 1)) :
    List.Vector.get (writeTape t b lambda tape)
      ⟨selectorCount t b lambda * 2 ^ (t - 1) * b +
        (l.val * 2 ^ b + h.val) * (2 ^ t * 2 ^ t + 1) + j.val,
        payload_offset_lt t b lambda l h j⟩ = tape (.inr (l, h, j)) := by
  have he : (⟨selectorCount t b lambda * 2 ^ (t - 1) * b +
      (l.val * 2 ^ b + h.val) * (2 ^ t * 2 ^ t + 1) + j.val,
      payload_offset_lt t b lambda l h j⟩ : Fin (tapeBitCount t b lambda)) =
        tapeIndex t b lambda (.inr (l, h, j)) := by
    apply Fin.ext
    exact (tapeIndex_payload_val t b lambda l h j).symm
  rw [he]
  exact congrFun (readTape_writeTape t b lambda tape) (.inr (l, h, j))

/-- Enumeration is needed only to analyse the finite law. Neither the tape
reader nor writer calls this instance or enumerates a function space. -/
noncomputable instance serializedTapeFintype (t b lambda : ℕ) :
    Fintype (SerializedTape t b lambda) :=
  Fintype.ofEquiv (TapePosition t b lambda → Bool) (serializedTapeEquiv t b lambda).symm

instance serializedTapeNonempty (t b lambda : ℕ) : Nonempty (SerializedTape t b lambda) :=
  ⟨writeTape t b lambda (fun _ => false)⟩

theorem serializedTape_card (t b lambda : ℕ) :
    Fintype.card (SerializedTape t b lambda) = 2 ^ tapeBitCount t b lambda := by
  rw [Fintype.card_congr (serializedTapeEquiv t b lambda)]
  simp [tapeBitCount, Nat.mul_assoc]

/-- Uniform literal Boolean lists of the exact public length. This is the
fair-bit law on serialized tapes; its analysis is noncomputable, not its
list-based decoder. -/
noncomputable def serializedTapeLaw (t b lambda : ℕ) :
    FiniteLaw (SerializedTape t b lambda) :=
  FiniteLaw.uniform (SerializedTape t b lambda)

theorem serializedTapeLaw_weight (t b lambda : ℕ) (bits : SerializedTape t b lambda) :
    (serializedTapeLaw t b lambda).weight bits =
      (1 / 2 : ℝ) ^ tapeBitCount t b lambda := by
  simp [serializedTapeLaw, FiniteLaw.uniform, serializedTape_card, one_div, inv_pow]

/-- Every event for the finite-tape generator has exactly the same
probability when the generator reads an actual uniformly random bit list. -/
theorem serializedTapeLaw_flat_prob (t b lambda : ℕ)
    (E : (TapePosition t b lambda → Bool) → Prop) :
    (serializedTapeLaw t b lambda).prob (fun bits => E (readTape t b lambda bits)) =
      (flatTapeLaw t b lambda).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [serializedTapeLaw_weight, flatTapeLaw_weight]
  exact (serializedTapeEquiv t b lambda).sum_comp
    (fun tape => if E tape then (1 / 2 : ℝ) ^ tapeBitCount t b lambda else 0)

end Paper2.YaoLowerBound.Materialization
