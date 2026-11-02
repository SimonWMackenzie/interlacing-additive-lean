import Paper2.FetchIndexed
import Paper2.SCCaps

/-! Unit 3, clock bounds, segment (2), first part: the admitted indexed-fetch clocks
`FetchLabel.loopBound`, `FetchIndexed.colBound`, `FetchIndexed.rowBound` are bounded by
`60 * (code size + 1) *` (column fetch; `80 *` for the row fetch) (total word length + list length + index + suffix length + 1)`.
Pure arithmetic about the admitted clock expressions. -/

set_option maxHeartbeats 4000000

namespace Paper2.SuccessClock

open Paper2.GeneratorCode Paper2.GeneratorSerialization

theorem iterSum_eq (c : Code) : ∀ ws : List (List Bool),
    (ws.map (FetchLabel.iterBound c)).sum =
      11 * codeSize c * (ws.flatten.length + ws.length) + 7 * ws.length
  | [] => by simp
  | w :: ws => by
      simp only [List.map_cons, List.sum_cons, iterSum_eq c ws, FetchLabel.iterBound,
        List.flatten_cons, List.length_append, List.length_cons]
      ring

theorem loopBound_le (c : Code) (ws : List (List Bool)) :
    FetchLabel.loopBound c ws ≤ 11 * ((codeSize c + 1) * (ws.flatten.length + ws.length + 1)) := by
  unfold FetchLabel.loopBound
  rw [iterSum_eq]
  nlinarith

theorem flatten_take_le (cs : List (List Bool)) (y : ℕ) :
    (cs.take y).flatten.length ≤ cs.flatten.length := by
  have h := congrArg (fun l : List (List Bool) => l.flatten.length) (List.take_append_drop y cs)
  simp only [List.flatten_append, List.length_append] at h
  omega

theorem flatten_drop_le (cs : List (List Bool)) (y : ℕ) :
    (cs.drop y).flatten.length ≤ cs.flatten.length := by
  have h := congrArg (fun l : List (List Bool) => l.flatten.length) (List.take_append_drop y cs)
  simp only [List.flatten_append, List.length_append] at h
  omega

theorem getD_le : ∀ (cs : List (List Bool)) (y : ℕ), (cs.getD y []).length ≤ cs.flatten.length
  | [], _ => by simp
  | c :: cs, 0 => by simp
  | c :: cs, y + 1 => by
      have := getD_le cs y
      simp only [List.getD_cons_succ, List.flatten_cons, List.length_append]
      omega

theorem colBound_le (col : Code) (cs : List (List Bool)) (y : ℕ) (O : List Bool) :
    FetchIndexed.colBound col cs y O ≤
      60 * ((codeSize col + 1) * (cs.flatten.length + cs.length + y + O.length + 1)) := by
  set S := codeSize col
  set F := cs.flatten.length
  set Z := F + cs.length + y + O.length + 1 with hZ
  set A := (S + 1) * Z with hA
  have hZA : Z ≤ A := Nat.le_mul_of_pos_left Z (by omega)
  have hSA : S + 1 ≤ A := Nat.le_mul_of_pos_right (S + 1) (by omega)
  have hl : FetchLabel.loopBound col (cs.take y) ≤ 11 * A := by
    have h1 : FetchLabel.loopBound col (cs.take y) ≤ 11 * ((S + 1) *
        ((cs.take y).flatten.length + (cs.take y).length + 1)) := loopBound_le col (cs.take y)
    have h2 := flatten_take_le cs y
    have h3 : (cs.take y).length ≤ y := by simp
    have h4 : (cs.take y).flatten.length + (cs.take y).length + 1 ≤ Z := by omega
    have h5 : (S + 1) * ((cs.take y).flatten.length + (cs.take y).length + 1) ≤ A :=
      Nat.mul_le_mul_left (S + 1) h4
    omega
  have hi : FetchLabel.iterBound col (cs.getD y []) ≤ 11 * A + 7 := by
    unfold FetchLabel.iterBound
    have h1 := getD_le cs y
    have h4 : (cs.getD y []).length + 1 ≤ Z := by omega
    have h5 : S * ((cs.getD y []).length + 1) ≤ A := Nat.mul_le_mul (by omega) h4
    change 11 * S * _ + 7 ≤ _
    rw [Nat.mul_assoc]
    omega
  have hd := flatten_drop_le cs (y + 1)
  unfold FetchIndexed.colBound
  simp only [List.length_append]
  change (2 * (F + O.length) + 2) + (2 * y + 2) + (2 * S + 2) + _ + _ + (S + 1) +
    ((cs.drop (y + 1)).flatten.length + O.length) + 1 + 6 ≤ 60 * A
  omega

theorem rowBound_le (col row : Code) (cs rs : List (List Bool)) (x : ℕ) (O : List Bool) :
    FetchIndexed.rowBound col row cs rs x O ≤
      80 * ((codeSize col + codeSize row + 1) *
        (cs.flatten.length + rs.flatten.length + cs.length + rs.length + x + O.length + 1)) := by
  set Sc := codeSize col
  set Sr := codeSize row
  set Fc := cs.flatten.length
  set Fr := rs.flatten.length
  set Z := Fc + Fr + cs.length + rs.length + x + O.length + 1 with hZ
  set A := (Sc + Sr + 1) * Z with hA
  have hZA : Z ≤ A := Nat.le_mul_of_pos_left Z (by omega)
  have hSA : Sc + Sr + 1 ≤ A := Nat.le_mul_of_pos_right _ (by omega)
  have hlc : FetchLabel.loopBound col cs ≤ 11 * A := by
    have h1 : FetchLabel.loopBound col cs ≤ 11 * ((Sc + 1) * (Fc + cs.length + 1)) :=
      loopBound_le col cs
    have h4 : Fc + cs.length + 1 ≤ Z := by omega
    have h5 : (Sc + 1) * (Fc + cs.length + 1) ≤ A :=
      Nat.mul_le_mul (by omega) h4
    omega
  have hlr : FetchLabel.loopBound row (rs.take x) ≤ 11 * A := by
    have h1 : FetchLabel.loopBound row (rs.take x) ≤ 11 * ((Sr + 1) *
        ((rs.take x).flatten.length + (rs.take x).length + 1)) := loopBound_le row (rs.take x)
    have h2 := flatten_take_le rs x
    have h3 : (rs.take x).length ≤ x := by simp
    have h4 : (rs.take x).flatten.length + (rs.take x).length + 1 ≤ Z := by omega
    have h5 : (Sr + 1) * ((rs.take x).flatten.length + (rs.take x).length + 1) ≤ A :=
      Nat.mul_le_mul (by omega) h4
    omega
  have hi : FetchLabel.iterBound row (rs.getD x []) ≤ 11 * A + 7 := by
    unfold FetchLabel.iterBound
    have h1 := getD_le rs x
    have h4 : (rs.getD x []).length + 1 ≤ Z := by omega
    have h5 : Sr * ((rs.getD x []).length + 1) ≤ A := Nat.mul_le_mul (by omega) h4
    change 11 * Sr * _ + 7 ≤ _
    rw [Nat.mul_assoc]
    omega
  have hd := flatten_drop_le rs (x + 1)
  unfold FetchIndexed.rowBound
  simp only [List.length_append]
  change (2 * (Fc + Fr + O.length) + 2) + (2 * cs.length + 2) + (2 * Sc + 2) + _ + (Sc + 1) +
    (2 * x + 2) + (2 * Sr + 2) + _ + _ + (Sr + 1) +
    ((rs.drop (x + 1)).flatten.length + O.length) + 1 + 10 ≤ 80 * A
  omega

end Paper2.SuccessClock

#print axioms Paper2.SuccessClock.loopBound_le
#print axioms Paper2.SuccessClock.colBound_le
#print axioms Paper2.SuccessClock.rowBound_le
