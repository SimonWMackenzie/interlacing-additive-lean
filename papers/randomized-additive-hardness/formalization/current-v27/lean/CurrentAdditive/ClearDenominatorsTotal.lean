import CurrentAdditive.RationalBitBounds
import CurrentAdditive.SequentialCode

/-! Totality of the frozen executable integer-relation conversion. -/

namespace CurrentAdditive.RationalBitBounds

open CurrentAdditive.SequentialCode

private theorem foldl_den_eq_prod (xs : List ℚ) (b : ℕ) :
    xs.foldl (fun acc r => acc * r.den) b =
      b * (xs.map Rat.den).prod := by
  induction xs generalizing b with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      rw [ih]
      ring

def denominatorProduct (x : Array ℚ) : ℕ :=
  x.foldl (fun acc r => acc * r.den) 1

theorem denominatorProduct_eq (x : Array ℚ) :
    denominatorProduct x = (x.toList.map Rat.den).prod := by
  rw [denominatorProduct, ← Array.foldl_toList]
  simpa using foldl_den_eq_prod x.toList 1

private theorem list_product_bits (xs : List ℕ) :
    xs.prod ≤ 2 ^ (xs.map Nat.size).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      calc
        a * rest.prod ≤ 2 ^ Nat.size a * 2 ^ (rest.map Nat.size).sum :=
          Nat.mul_le_mul (le_of_lt (Nat.lt_size_self a)) ih
        _ = 2 ^ (Nat.size a + (rest.map Nat.size).sum) := by rw [pow_add]

theorem denominatorProduct_bits (x : Array ℚ) :
    Nat.size (denominatorProduct x) ≤
      ((x.toList.map fun r => Nat.size r.den).sum) + 1 :=
  size_le_of_pow_bound (by
    rw [denominatorProduct_eq]
    simpa only [List.map_map, Function.comp_def] using
      (list_product_bits (x.toList.map Rat.den)))

theorem denominatorProduct_pos (x : Array ℚ) :
    0 < denominatorProduct x := by
  rw [denominatorProduct_eq]
  exact List.prod_pos (by
    intro a ha
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    exact r.den_pos)

theorem denominator_dvd_product (x : Array ℚ) (i : Fin x.size) :
    (x[i]).den ∣ denominatorProduct x := by
  rw [denominatorProduct_eq]
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨x[i], Array.getElem_mem_toList i.isLt, rfl⟩

/-- Every scaled entry is an integer.  The factor is the *actual* product
computed by `clearDenominators`; this is not a choice of an abstract lcm. -/
theorem scaled_den_eq_one (x : Array ℚ) (i : Fin x.size) :
    ((denominatorProduct x : ℚ) * x[i]).den = 1 := by
  let b := denominatorProduct x
  have hb : 0 < b := denominatorProduct_pos x
  have hd : (x[i]).den ∣ b := denominator_dvd_product x i
  let enc := commonDenominatorOfDvd (fun _ : Unit => x[i]) b hb (fun _ => hd)
  have hrepr := enc.represents ()
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hscaled : (b : ℚ) * x[i] = (enc.numerator () : ℚ) := by
    calc
      (b : ℚ) * x[i] =
          (b : ℚ) * ((enc.numerator () : ℚ) / (enc.denominator : ℚ)) :=
        congrArg (fun r : ℚ => (b : ℚ) * r) hrepr
      _ = (enc.numerator () : ℚ) := by
        change (b : ℚ) * ((enc.numerator () : ℚ) / (b : ℚ)) = _
        field_simp
  rw [hscaled]
  exact Rat.den_intCast _

/-- The frozen `clearDenominators` check succeeds for every rational array.
The returned integer vector is exactly the input vector multiplied by the
computed positive common denominator. -/
theorem clearDenominators_total (x : Array ℚ) :
    ∃ z : Array ℤ,
      clearDenominators x = some z ∧
      z.size = x.size ∧
      ∀ i : Fin x.size,
        ((z[i.val]?.getD 0 : ℤ) : ℚ) =
          (denominatorProduct x : ℚ) * x[i] := by
  let b := denominatorProduct x
  let scaled := x.map (fun r => (b : ℚ) * r)
  have hall : scaled.all (fun r => decide (r.den = 1)) = true := by
    apply Array.all_eq_true.mpr
    intro i hi
    have hi' : i < x.size := by simpa [scaled] using hi
    have hs := scaled_den_eq_one x ⟨i, hi'⟩
    simpa [scaled] using hs
  refine ⟨scaled.map Rat.num, ?_, by simp [scaled], ?_⟩
  · change (if scaled.all (fun r => decide (r.den = 1)) then
        some (scaled.map Rat.num) else none) = some (scaled.map Rat.num)
    simp [hall]
  · intro i
    have hi : i.val < scaled.size := by simp [scaled, i.isLt]
    have hs := scaled_den_eq_one x i
    have hnum := (Rat.den_eq_one_iff ((b : ℚ) * x[i])).mp hs
    simpa [scaled] using hnum

/-- The cleared coefficient has at most the input numerator bits plus the
sum of all input denominator bits, up to two harmless endpoint bits. -/
theorem clearDenominators_coefficient_bits (x : Array ℚ) (z : Array ℤ)
    (hz : clearDenominators x = some z) (i : Fin x.size) :
    Nat.size (z[i.val]?.getD 0).natAbs ≤
      Nat.size (x[i].num.natAbs) +
        (x.toList.map fun r => Nat.size r.den).sum + 2 := by
  obtain ⟨z', hz', _, hscale⟩ := clearDenominators_total x
  have hzz : z = z' := by simpa [hz] using hz'
  subst z'
  let b := denominatorProduct x
  have hb : 0 < b := denominatorProduct_pos x
  have hd : (x[i]).den ∣ b := denominator_dvd_product x i
  let enc := commonDenominatorOfDvd (fun _ : Unit => x[i]) b hb (fun _ => hd)
  have hrepr := enc.represents ()
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hscaled : (b : ℚ) * x[i] = (enc.numerator () : ℚ) := by
    calc
      (b : ℚ) * x[i] =
          (b : ℚ) * ((enc.numerator () : ℚ) / (enc.denominator : ℚ)) :=
        congrArg (fun r : ℚ => (b : ℚ) * r) hrepr
      _ = (enc.numerator () : ℚ) := by
        change (b : ℚ) * ((enc.numerator () : ℚ) / (b : ℚ)) = _
        field_simp
  have hzi : z[i.val]?.getD 0 = enc.numerator () := by
    have hq := (hscale i).trans hscaled
    exact_mod_cast hq
  have hnat : (z[i.val]?.getD 0).natAbs ≤ (x[i]).num.natAbs * b := by
    rw [hzi]
    change ((x[i]).num * (((b / (x[i]).den : ℕ) : ℤ))).natAbs ≤ _
    rw [Int.natAbs_mul]
    simp only [Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  have hsize : Nat.size (z[i.val]?.getD 0).natAbs ≤
      Nat.size (x[i].num.natAbs) + Nat.size b + 1 := by
    apply size_le_of_pow_bound
    exact hnat.trans (mul_fits_bits (le_of_lt (Nat.lt_size_self _))
      (le_of_lt (Nat.lt_size_self _)))
  have hbsize := denominatorProduct_bits x
  dsimp [b] at hsize
  change Nat.size (z[i.val]?.getD 0).natAbs ≤
    Nat.size (x[i.val].num.natAbs) +
      (x.toList.map fun r => Nat.size r.den).sum + 2
  omega

private theorem list_sum_den_bits_le (xs : List ℚ) (R : ℕ)
    (h : ∀ r ∈ xs, Nat.size r.den ≤ R) :
    (xs.map fun r => Nat.size r.den).sum ≤ xs.length * R := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      have ha := h a (by simp)
      have hrest : ∀ r ∈ rest, Nat.size r.den ≤ R := by
        intro r hr
        exact h r (by simp [hr])
      have hr := ih hrest
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

/-- If every materialized Gauss--Jordan rational entry has at most `R`
numerator and denominator bits, the frozen product-clearing code returns
integer coefficients of at most `(k+1)R+2` bits for `k` entries. -/
theorem clearDenominators_uniform_coefficient_bits
    (x : Array ℚ) (z : Array ℤ) (R : ℕ)
    (hz : clearDenominators x = some z)
    (hnum : ∀ i : Fin x.size, Nat.size (x[i].num.natAbs) ≤ R)
    (hden : ∀ r ∈ x.toList, Nat.size r.den ≤ R)
    (i : Fin x.size) :
    Nat.size (z[i.val]?.getD 0).natAbs ≤ (x.size + 1) * R + 2 := by
  have hbits := clearDenominators_coefficient_bits x z hz i
  have hsum := list_sum_den_bits_le x.toList R hden
  have hlength : x.toList.length = x.size := by simp
  have hnumi := hnum i
  rw [hlength] at hsum
  nlinarith

theorem scaled_integer_isDependence (a : Array (Array ℚ))
    (x : Array ℚ) (z : Array ℤ)
    (hx : IsDependence a x)
    (hsize : z.size = x.size)
    (hscale : ∀ i : Fin x.size,
      ((z[i.val]?.getD 0 : ℤ) : ℚ) =
        (denominatorProduct x : ℚ) * x[i]) :
    IsDependence a (z.map fun k : ℤ => (k : ℚ)) := by
  let b : ℚ := denominatorProduct x
  have hb : b ≠ 0 := by
    change (denominatorProduct x : ℚ) ≠ 0
    exact_mod_cast (Nat.ne_of_gt (denominatorProduct_pos x))
  have h := (dependence_spec a x).mp hx
  have hlen : (z.map fun k : ℤ => (k : ℚ)).size = x.size := by
    simp [hsize]
  have hentry (j : Nat) (hj : j < x.size) :
      ((z.map fun k : ℤ => (k : ℚ))[j]?.getD 0) =
        b * (x[j]?.getD 0) := by
    have hs := hscale ⟨j, hj⟩
    simp [b, hsize, hj] at hs ⊢
    exact hs
  apply (dependence_spec a _).mpr
  refine ⟨hlen.trans h.1, ?_, ?_⟩
  · obtain ⟨j, hj, hxj⟩ := h.2.1
    have hj' : j < x.size := List.mem_range.mp hj
    refine ⟨j, by simpa [hlen] using hj, ?_⟩
    rw [hentry j hj']
    exact mul_ne_zero hb hxj
  · intro i hi
    have hsum := h.2.2 i hi
    rw [hlen]
    calc
      ((List.range x.size).map (fun j =>
          cell a i j * ((z.map fun k : ℤ => (k : ℚ))[j]?.getD 0))).sum =
        ((List.range x.size).map (fun j =>
          b * (cell a i j * (x[j]?.getD 0)))).sum := by
            congr 1
            apply List.map_congr_left
            intro j hj
            rw [hentry j (List.mem_range.mp hj)]
            ring
      _ = b * ((List.range x.size).map (fun j =>
          cell a i j * (x[j]?.getD 0))).sum := by
            simpa using (List.sum_map_mul_left (List.range x.size)
              (fun j => cell a i j * (x[j]?.getD 0)) b)
      _ = 0 := by rw [hsum, mul_zero]

/-- An already certified rational relation cannot fail at the frozen
integer-clearing stage. This does not assume the Gauss--Jordan finder is
complete; that is the separate totality theorem in the support worker's file. -/
theorem checkedIntegerDependence_of_checked
    (a : Array (Array ℚ))
    (cert : {x : Array ℚ // IsDependence a x})
    (hcert : checkedDependence a = some cert) :
    ∃ zcert, checkedIntegerDependence a = some zcert := by
  obtain ⟨z, hz, hsize, hscale⟩ := clearDenominators_total cert.val
  have hdep := scaled_integer_isDependence a cert.val z cert.property hsize hscale
  unfold checkedIntegerDependence
  simp only [hcert, hz]
  refine ⟨⟨z, hdep⟩, ?_⟩
  dsimp [IsDependence] at hdep
  simp [hdep]

end CurrentAdditive.RationalBitBounds
