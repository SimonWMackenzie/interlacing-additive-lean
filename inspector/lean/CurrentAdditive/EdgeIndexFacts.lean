import CurrentAdditive.EdgeEncoder

namespace CurrentAdditive.LiteralEdgeEncoder

@[simp] theorem paddedNumber_edge (s m : ℕ) (g : Fin (4*s)) (e : Fin m) :
    (paddedNumber s m (.inl (g,e))).val = e.val + m*g.val := rfl

@[simp] theorem paddedNumber_padding (s m : ℕ)
    (j : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) -
      Fintype.card (Fin (4*s) × Fin m))) :
    (paddedNumber s m (.inr j)).val = 4*s*m + j.val := rfl

theorem coordinate_decode_edge {s m r : ℕ}
    (g : Fin (4*s)) (e : Fin m) (t : Fin r) :
    let a := coordinateNumber s m r (.inl (g,e),t)
    a.val / r / m = g.val ∧ a.val / r % m = e.val ∧ a.val % r = t.val := by
  dsimp only
  have hb := coordinateNumber_symm_base s m r
    (coordinateNumber s m r (.inl (g,e),t))
  have ht := coordinateNumber_symm_repeat s m r
    (coordinateNumber s m r (.inl (g,e),t))
  simp only [Equiv.symm_apply_apply, paddedNumber_edge] at hb ht
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) e.isLt
  refine ⟨?_, ?_, ht.symm⟩
  · rw [← hb, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
  · rw [← hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]

theorem coordinate_decode_padding {s m r : ℕ}
    (j : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) -
      Fintype.card (Fin (4*s) × Fin m))) (t : Fin r) :
    let a := coordinateNumber s m r (.inr j,t)
    a.val / r = 4*s*m + j.val ∧ a.val % r = t.val := by
  dsimp only
  constructor
  · have h := coordinateNumber_symm_base s m r
      (coordinateNumber s m r (.inr j,t))
    simpa only [Equiv.symm_apply_apply, paddedNumber_padding] using h.symm
  · have h := coordinateNumber_symm_repeat s m r
      (coordinateNumber s m r (.inr j,t))
    simpa only [Equiv.symm_apply_apply] using h.symm

theorem active_padding {s n m r : ℕ} (e : Fin m → Bool → Fin n)
    (j : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) -
      Fintype.card (Fin (4*s) × Fin m))) (t : Fin r) (i : Items s n) :
    active e (coordinateNumber s m r (.inr j,t)) i = false := by
  simp [active]

#print axioms coordinate_decode_edge
#print axioms coordinate_decode_padding
#print axioms active_padding

end CurrentAdditive.LiteralEdgeEncoder
