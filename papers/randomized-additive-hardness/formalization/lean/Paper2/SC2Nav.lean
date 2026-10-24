import Paper2.NavJoin
import Paper2.SCCaps

/-! Lane a-success-clock-owner-2, segment (1a): the admitted level join clock
`NavJoin.joinBound` is linear in the serialized sizes of the two level-`k+1`
codes.  Pure arithmetic over the literal production clock expressions
(`LevelNav.leftBound`, `LevelNav.midBound`, `LevelNavCol.bound`,
`LevelNavRow.bound`, `LevelNavCodes.cpsBound` / `outerBound` / `tentryBound`,
`ChildNav.takeBound` / `dropBound`) and the admitted size identities
(`GeneratorSerialization.encodeCode_length`, `GeneratorSize.*`). No machine is
defined here. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.SuccessClock2

open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
  Paper2.GeneratorSize

theorem copies_succ_size (m : ℕ) (c : Code) :
    codeSize (copies (m + 1) c) = 3 + codeSize c + codeSize (copies m c) := rfl

theorem copies_size_ge (m : ℕ) (c : Code) : 4 ≤ codeSize (copies m c) := by
  rw [copies_size]; omega

theorem codeSize_ge (c : Code) : 3 ≤ codeSize c := by
  cases c <;> simp [codeSize] <;> omega

theorem dropBound_le (c : Code) (w : List Bool) :
    ChildNav.dropBound c w ≤ 16 * (codeSize c + w.length) + 21 := by
  unfold ChildNav.dropBound
  simp only [List.length_append, encodeCode_length]
  omega

theorem takeBound_le (c : Code) (w : List Bool) :
    ChildNav.takeBound c w ≤ 16 * (codeSize c + w.length) + 21 := by
  unfold ChildNav.takeBound
  simp only [List.length_append, encodeCode_length]
  omega

/-- The words left behind by the column navigation are no longer than the tagged code. -/
theorem R_lengths (q₁ q₂ s : ℕ) (col : Code) :
    (LevelNavCol.R1 q₁ q₂ s col).length + codeSize (rawCode q₁ q₂ s col) + 6 ≤
        codeSize (taggedCode q₁ q₂ s col) ∧
      codeSize col + (LevelNavCol.R3 q₁ q₂ s col).length ≤ codeSize (taggedCode q₁ q₂ s col) ∧
      codeSize (copies (s + 1) col) + (LevelNavCol.R2 q₁ q₂ s col).length ≤
        codeSize (taggedCode q₁ q₂ s col) := by
  have ht := tagged_size q₁ q₂ s col
  have hraw : codeSize (rawCode q₁ q₂ s col) =
      3 + codeSize (copies (s + 1) col) + codeSize (copies s (outerCode q₁ q₂ s col)) := rfl
  have hft : fixedTailCode q₁ q₂ s col = copies s (outerCode q₁ q₂ s col) := rfl
  have hcs := copies_succ_size s col
  simp only [LevelNavCol.R1, LevelNavCol.R2, LevelNavCol.R3, List.length_append,
    encodeCode_length, codeSize, List.length_cons, List.length_nil, hft] at ht ⊢
  omega

theorem colPrefix_le (q₁ q₂ s w : ℕ) (col : Code) :
    LevelNavCodes.colPrefixBound q₁ q₂ s w col ≤
      60 * codeSize (.append (.ticket w) (taggedCode q₁ q₂ s col)) + 1000 := by
  obtain ⟨h1, h2, h3⟩ := R_lengths q₁ q₂ s col
  have d1 := dropBound_le (.ticket w) (encodeCode (taggedCode q₁ q₂ s col))
  have d2 := dropBound_le (.emit [false])
    (encodeCode (rawCode q₁ q₂ s col) ++ LevelNavCol.R1 q₁ q₂ s col)
  unfold LevelNavCodes.colPrefixBound
  simp only [List.length_append, encodeCode_length, codeSize, List.length_cons,
    List.length_nil] at d1 d2 ⊢
  omega

theorem col_le (q₁ q₂ s w : ℕ) (col : Code) :
    LevelNavCol.bound q₁ q₂ s w col ≤
      100 * codeSize (.append (.ticket w) (taggedCode q₁ q₂ s col)) + 2000 := by
  obtain ⟨h1, h2, h3⟩ := R_lengths q₁ q₂ s col
  have d1 := dropBound_le (.ticket w) (encodeCode (taggedCode q₁ q₂ s col))
  have d2 := dropBound_le (.emit [false])
    (encodeCode (rawCode q₁ q₂ s col) ++ LevelNavCol.R1 q₁ q₂ s col)
  have d3 := takeBound_le col (LevelNavCol.R3 q₁ q₂ s col)
  unfold LevelNavCol.bound
  simp only [List.length_append, encodeCode_length, codeSize, List.length_cons,
    List.length_nil] at d1 d2 d3 ⊢
  omega

theorem cps_le (q₁ q₂ s w : ℕ) (col : Code) :
    LevelNavCodes.cpsBound q₁ q₂ s w col ≤
      100 * codeSize (.append (.ticket w) (taggedCode q₁ q₂ s col)) + 2000 := by
  obtain ⟨h1, h2, h3⟩ := R_lengths q₁ q₂ s col
  have d0 := colPrefix_le q₁ q₂ s w col
  have d3 := takeBound_le (copies (s + 1) col) (LevelNavCol.R2 q₁ q₂ s col)
  unfold LevelNavCodes.cpsBound
  simp only [codeSize] at d0 ⊢
  omega

theorem outer_le (q₁ q₂ s w : ℕ) (hs : 1 ≤ s) (col : Code) :
    LevelNavCodes.outerBound q₁ q₂ s w col ≤
      120 * codeSize (.append (.ticket w) (taggedCode q₁ q₂ s col)) + 2000 := by
  obtain ⟨h1, h2, h3⟩ := R_lengths q₁ q₂ s col
  have d0 := colPrefix_le q₁ q₂ s w col
  have d2 := dropBound_le (copies (s + 1) col) (LevelNavCol.R2 q₁ q₂ s col)
  have d3 := takeBound_le (outerCode q₁ q₂ s col)
    (encodeCode (copies (s - 1) (outerCode q₁ q₂ s col)) ++ LevelNavCol.R1 q₁ q₂ s col)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hs' : s' + 1 - 1 = s' := by omega
  rw [hs'] at d3
  have hcO := copies_succ_size s' (outerCode q₁ q₂ (s' + 1) col)
  have hR2 : (LevelNavCol.R2 q₁ q₂ (s' + 1) col).length =
      codeSize (copies (s' + 1) (outerCode q₁ q₂ (s' + 1) col)) +
        (LevelNavCol.R1 q₁ q₂ (s' + 1) col).length := by
    simp only [LevelNavCol.R2, List.length_append, encodeCode_length]
  unfold LevelNavCodes.outerBound
  simp only [hs', List.length_append, encodeCode_length, codeSize] at d0 d2 d3 ⊢
  omega

theorem left_le (E : Code) (Q : ℕ) (hQ : 1 ≤ Q) :
    LevelNav.leftBound E (copies (Q - 1) E) ≤ 20 * codeSize (copies Q E) + 100 := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  have hQ' : Q' + 1 - 1 = Q' := by omega
  rw [hQ']
  have d := takeBound_le E (encodeCode (copies Q' E))
  have hc := copies_succ_size Q' E
  unfold LevelNav.leftBound
  simp only [List.length_append, encodeCode_length, codeSize] at d hc ⊢
  omega

theorem mid_le (G : Code) (Q w : ℕ) (hw : 1 ≤ w) :
    LevelNav.midBound (.ticket Q) G (copies (w - 1) G) ≤
      40 * codeSize (.append (.ticket Q) (copies w G)) + 100 := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hw' : w' + 1 - 1 = w' := by omega
  rw [hw']
  have d1 := dropBound_le (.ticket Q) (encodeCode (.append G (copies w' G)))
  have d2 := takeBound_le G (encodeCode (copies w' G))
  have hc := copies_succ_size w' G
  unfold LevelNav.midBound
  simp only [List.length_append, encodeCode_length, codeSize] at d1 d2 hc ⊢
  omega

theorem rowNav_le (n q₁ q₂ s : ℕ) (row : Code) :
    LevelNavRow.bound n q₁ q₂ s row ≤
      100 * codeSize (graphRowsCode (V := Fin n) q₁ q₂ s row) + 3000 := by
  have hg : codeSize (graphRowsCode (V := Fin n) q₁ q₂ s row) =
      3 + 513 + 511 + 512 +
        (3 + codeSize (.emit [false]) + codeSize (templateRowCode q₁ q₂ s row)) +
        (3 + codeSize (.emit [true]) +
          (3 + codeSize (vertexLabelsCode (V := Fin n) s) + codeSize row)) +
        (3 + codeSize (.emit [true]) + (3 + codeSize (auxiliaryLabelsCode s) + codeSize row)) := rfl
  have d1 := dropBound_le (.append (.emit [false]) (templateRowCode q₁ q₂ s row))
    (LevelNavRow.encB n s row ++ LevelNavRow.encC s row)
  have d2 := dropBound_le (.emit [true])
    (encodeCode (.append (vertexLabelsCode (V := Fin n) s) row) ++ LevelNavRow.encC s row)
  have d3 := dropBound_le (vertexLabelsCode (V := Fin n) s) (encodeCode row ++ LevelNavRow.encC s row)
  have d4 := takeBound_le row (LevelNavRow.encC s row)
  unfold LevelNavRow.bound
  simp only [LevelNavRow.encB, LevelNavRow.encC, List.length_append, encodeCode_length,
    codeSize, List.length_cons, List.length_nil] at hg d1 d2 d3 d4 ⊢
  omega

theorem tentry_le (n q₁ q₂ s : ℕ) (hq₂ : 1 ≤ q₂) (row : Code) :
    LevelNavCodes.tentryBound n q₁ q₂ s row ≤
      100 * codeSize (graphRowsCode (V := Fin n) q₁ q₂ s row) + 3000 := by
  have hg : codeSize (graphRowsCode (V := Fin n) q₁ q₂ s row) =
      3 + 513 + 511 + 512 +
        (3 + codeSize (.emit [false]) + codeSize (templateRowCode q₁ q₂ s row)) +
        (3 + codeSize (.emit [true]) +
          (3 + codeSize (vertexLabelsCode (V := Fin n) s) + codeSize row)) +
        (3 + codeSize (.emit [true]) + (3 + codeSize (auxiliaryLabelsCode s) + codeSize row)) := rfl
  have htr : codeSize (templateRowCode q₁ q₂ s row) =
      3 + codeSize (.ticket s) + codeSize (templateCode q₁ q₂ row) := rfl
  have d1 := dropBound_le (.emit [false])
    (encodeCode (templateRowCode q₁ q₂ s row) ++ LevelNavCodes.rB n s row)
  have d2 := dropBound_le (.ticket s)
    (encodeCode (templateCode q₁ q₂ row) ++ LevelNavCodes.rB n s row)
  have d3 := takeBound_le (.append (.ticket q₁) row)
    (encodeCode (copies (q₂ - 1) (.append (.ticket q₁) row)) ++ LevelNavCodes.rB n s row)
  obtain ⟨q', rfl⟩ : ∃ q', q₂ = q' + 1 := ⟨q₂ - 1, by omega⟩
  have hq' : q' + 1 - 1 = q' := by omega
  rw [hq'] at d3
  have htc : codeSize (templateCode q₁ (q' + 1) row) =
      3 + codeSize (.append (.ticket q₁) row) + codeSize (copies q' (.append (.ticket q₁) row)) := rfl
  unfold LevelNavCodes.tentryBound
  simp only [hq', LevelNavCodes.rB, LevelNavRow.encB, LevelNavRow.encC, List.length_append,
    encodeCode_length, codeSize, List.length_cons, List.length_nil] at hg htr htc d1 d2 d3 ⊢
  omega

/-- Segment (1a), generic codes: the level join clock is linear in the two level-`k+1` code sizes. -/
theorem joinBound_le (n p s q₁ q₂ w Q k : ℕ) (hQ : 1 ≤ Q) (hw : 1 ≤ w) (hs : 1 ≤ s)
    (hq₂ : 1 ≤ q₂) :
    NavJoin.joinBound n p s q₁ q₂ w Q k ≤
      1000 * (codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 +
        codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 + 10) := by
  unfold NavJoin.joinBound
  extract_lets c E G
  have h1 := left_le E Q hQ
  have h2 := mid_le G Q w hw
  have h3 := col_le q₁ q₂ s w c.2
  have h4 := rowNav_le n q₁ q₂ s c.1
  have h5 := cps_le q₁ q₂ s w c.2
  have h6 := outer_le q₁ q₂ s w hs c.2
  have h7 := tentry_le n q₁ q₂ s hq₂ c.1
  have e1 : copies Q E = (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 := rfl
  have e2 : Code.append (.ticket Q) (copies w G) = (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 :=
    rfl
  rw [e1] at h1
  rw [e2] at h2
  have hd := Paper2.SuccessClock.derived_le (n := n) (s := s) (q₁ := q₁) (q₂ := q₂) hw hQ
    (copies p .bit) (.ticket p) k
  obtain ⟨hE, -, -, -, -, hG, -⟩ := hd
  change codeSize (.append (.ticket w) (taggedCode q₁ q₂ s c.2)) ≤
    codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 at hE
  change codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) ≤
    codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 at hG
  have hE' : codeSize E = codeSize (.append (.ticket w) (taggedCode q₁ q₂ s c.2)) := rfl
  have hG' : codeSize G = codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) := rfl
  have g1 := codeSize_ge (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1
  have g2 := codeSize_ge (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2
  omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.dropBound_le
#print axioms Paper2.SuccessClock2.col_le
#print axioms Paper2.SuccessClock2.rowNav_le
#print axioms Paper2.SuccessClock2.tentry_le
#print axioms Paper2.SuccessClock2.joinBound_le
