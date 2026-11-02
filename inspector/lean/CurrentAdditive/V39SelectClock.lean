import CurrentAdditive.V39PhysicalSelect

/-! Uniform arithmetic bound for the actual physical selection stage.
This bounds every current label, and therefore every generator tape. It
does not include later activity computation, recursion or table printing. -/

namespace CurrentAdditive.V39SelectClock

open Paper2 Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
open Paper2.RecursiveLabelCodecScratch
open CurrentAdditive.V39RecursiveGenerator CurrentAdditive.V39PhysicalSelect

theorem loopBound_eq (c : Code) (ws : List (List Bool)) :
    FetchLabel.loopBound c ws =
      11 * codeSize c * (ws.flatten.length + ws.length) + 7 * ws.length + 1 := by
  induction ws with
  | nil => simp [FetchLabel.loopBound]
  | cons a ws ih =>
    simp only [FetchLabel.loopBound, List.map_cons, List.sum_cons,
      List.flatten_cons, List.length_append, List.length_cons, FetchLabel.iterBound] at *
    nlinarith

theorem member_length_le_flatten (ws : List (List Bool)) (a : List Bool) (ha : a ∈ ws) :
    a.length ≤ ws.flatten.length := by
  induction ws with
  | nil => simp at ha
  | cons b ws ih =>
    simp only [List.mem_cons] at ha
    simp only [List.flatten_cons, List.length_append]
    rcases ha with rfl | ha
    · omega
    · exact (ih ha).trans (by omega)

theorem getD_length_le_flatten (ws : List (List Bool)) (j : ℕ) :
    (ws.getD j []).length ≤ ws.flatten.length := by
  by_cases hj : j < ws.length
  · have hm : ws.getD j [] ∈ ws := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        using List.getElem_mem hj
    exact member_length_le_flatten ws _ hm
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ j)]

theorem take_flatten_length_le (ws : List (List Bool)) (j : ℕ) :
    (ws.take j).flatten.length ≤ ws.flatten.length := by
  have h := congrArg (fun zs : List (List Bool) => zs.flatten.length) (List.take_append_drop j ws)
  simp only [List.flatten_append, List.length_append] at h
  omega

theorem drop_flatten_length_le (ws : List (List Bool)) (j : ℕ) :
    (ws.drop j).flatten.length ≤ ws.flatten.length := by
  have h := congrArg (fun zs : List (List Bool) => zs.flatten.length) (List.take_append_drop j ws)
  simp only [List.flatten_append, List.length_append] at h
  omega

/-- A bound independent of the selected index and all label values. -/
theorem fetchBound_le (c : Code) (ws : List (List Bool)) (j : ℕ) (hj : j ≤ ws.length) :
    FetchIndexed.colBound c ws j [] ≤
      100 * (codeSize c + 1) * (ws.flatten.length + ws.length + 1) := by
  have ht := take_flatten_length_le ws j
  have hd := drop_flatten_length_le ws (j + 1)
  have hg := getD_length_le_flatten ws j
  have hn : (ws.take j).length ≤ ws.length := List.length_take_le' _ _
  have hb := loopBound_eq c (ws.take j)
  unfold FetchIndexed.colBound
  simp only [List.append_nil, FetchLabel.iterBound]
  rw [hb]
  have hprod :
      11 * codeSize c * ((ws.take j).flatten.length + (ws.take j).length) ≤
        11 * codeSize c * (ws.flatten.length + ws.length) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add ht hn)
  have hgprod := Nat.mul_le_mul_left (11 * codeSize c) (Nat.add_le_add_right hg 1)
  nlinarith

variable (n p₀ q₁ q₂ s w Q : ℕ)

def selectionClock (k : ℕ) : ℕ :=
  let D := defaultCarrierCodecs n p₀ s q₁ q₂ w Q (k + 1)
  let c := seedRecursiveCodes n p₀ s q₁ q₂ w Q k
  let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
  let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
  2 * D.2.maxLen + 2 + (Q + 1) +
    100 * (codeSize E + 1) * (D.1.maxLen + Q + 1) +
    (w + 1) + 100 * (codeSize G + 1) * (D.2.maxLen + w + 1) + 4

variable {n p₀ q₁ q₂ s w Q}

theorem every_label_clock (k : ℕ)
    (x : Row n p₀ q₁ q₂ s w Q (k + 1))
    (y : Column n p₀ q₁ q₂ s w Q (k + 1)) :
    let C := defaultCarrierCodecs n p₀ s q₁ q₂ w Q k
    let c := seedRecursiveCodes n p₀ s q₁ q₂ w Q k
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
    let tx := (embedding n p₀ q₁ q₂ s w Q (k + 1)).1 x
    let ty := (embedding n p₀ q₁ q₂ s w Q (k + 1)).2 y
    let entry := prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)
    let rrow := rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)
    let cs := List.ofFn (fun j => entry.encode (tx j))
    let rs := List.ofFn (fun i => rrow.encode (ty.2 i))
    RequestSelect.clock (columnWord (k + 1) y) y.1.val (x y.1).1.val E G cs rs ≤
      selectionClock n p₀ q₁ q₂ s w Q k := by
  intro C c E G tx ty entry rrow cs rs
  let D := defaultCarrierCodecs n p₀ s q₁ q₂ w Q (k + 1)
  have hX : rowWord (k + 1) x = cs.flatten := by
    change (piCodec entry Q).encode tx = _
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
  have hR : (piCodec rrow w).encode ty.2 = rs.flatten := by
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
  have hY : columnWord (k + 1) y = (finCodec Q).encode y.1 ++ rs.flatten := by
    change (finCodec Q).encode y.1 ++ (piCodec rrow w).encode ty.2 = _
    rw [hR]
  have hx : cs.flatten.length ≤ D.1.maxLen := by
    rw [← hX]
    exact D.1.length_le tx
  have hy : rs.flatten.length ≤ D.2.maxLen := by
    have hb := D.2.length_le ty
    change (columnWord (k + 1) y).length ≤ D.2.maxLen at hb
    rw [hY, List.length_append] at hb
    omega
  have hlY : (columnWord (k + 1) y).length ≤ D.2.maxLen := D.2.length_le ty
  have hcs : cs.length = Q := List.length_ofFn
  have hrs : rs.length = w := List.length_ofFn
  have hbE := fetchBound_le E cs y.1.val (by rw [hcs]; exact Nat.le_of_lt y.1.isLt)
  have hbG := fetchBound_le G rs (x y.1).1.val (by rw [hrs]; exact Nat.le_of_lt (x y.1).1.isLt)
  have he : FetchIndexed.colBound E cs y.1.val [] ≤
      100 * (codeSize E + 1) * (D.1.maxLen + Q + 1) :=
    hbE.trans (Nat.mul_le_mul_left _ (by omega))
  have hg : FetchIndexed.colBound G rs (x y.1).1.val [] ≤
      100 * (codeSize G + 1) * (D.2.maxLen + w + 1) :=
    hbG.trans (Nat.mul_le_mul_left _ (by omega))
  unfold RequestSelect.clock
  change _ ≤ 2 * D.2.maxLen + 2 + (Q + 1) +
    100 * (codeSize E + 1) * (D.1.maxLen + Q + 1) +
    (w + 1) + 100 * (codeSize G + 1) * (D.2.maxLen + w + 1) + 4
  have hj := y.1.isLt
  have hi := (x y.1).1.isLt
  omega

#print axioms fetchBound_le
#print axioms every_label_clock

end CurrentAdditive.V39SelectClock
