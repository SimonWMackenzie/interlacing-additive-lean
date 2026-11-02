import Paper2.FiniteFallbackSourceGap

/-!
Frozen v12 Appendix D, finite-source fallback. Explicit ternary enumeration
and counted edge testing; count is not a bit-machine runtime theorem.
-/

namespace Paper2.FiniteFallbackSearchScratch

open FiniteFallbackOutput

/-- A fixed executable ternary enumeration, with each function formed by
prepending one colour to a recursively enumerated tail. -/
def allColourings : (v : ℕ) → List (Fin v → Fin 3)
  | 0 => [fun i => Fin.elim0 i]
  | v + 1 =>
      (List.finRange 3).flatMap fun head =>
        (allColourings v).map fun tail => Fin.cases head tail

/-- Evaluate graph edges in label order, stopping at the first violation.
The counter increments once per edge comparison actually made. -/
def testEdges {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (colour : Fin v → Fin 3) : List (Fin e) → Bool × ℕ
  | [] => (true, 0)
  | z :: zs =>
      if colour (edge z false) = colour (edge z true) then (false, 1)
      else
        let result := testEdges edge colour zs
        (result.1, result.2 + 1)

/-- The actual edge-list test, with no promise decision supplied. -/
def properTest {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (colour : Fin v → Fin 3) : Bool × ℕ :=
  testEdges edge colour (List.finRange e)

/-- Search in the fixed enumeration order. Charge one candidate dispatch plus
each edge comparison performed by `properTest`. -/
def scan {v e : ℕ} (edge : Fin e → Bool → Fin v) :
    List (Fin v → Fin 3) → Bool × ℕ
  | [] => (false, 0)
  | colour :: rest =>
      let trial := properTest edge colour
      if trial.1 then (true, trial.2 + 1)
      else
        let later := scan edge rest
        (later.1, trial.2 + 1 + later.2)

def search {v e : ℕ} (edge : Fin e → Bool → Fin v) : Bool × ℕ :=
  scan edge (allColourings v)

theorem allColourings_mem (v : ℕ) (colour : Fin v → Fin 3) :
    colour ∈ allColourings v := by
  induction v with
  | zero =>
      simp only [allColourings, List.mem_singleton]
      funext i
      exact Fin.elim0 i
  | succ v ih =>
      have htail := ih (fun i => colour i.succ)
      have hhead : colour 0 ∈ List.finRange 3 := by simp
      simp only [allColourings, List.mem_flatMap, List.mem_map]
      refine ⟨colour 0, hhead, (fun i => colour i.succ), htail, ?_⟩
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl

theorem allColourings_length (v : ℕ) :
    (allColourings v).length = 3 ^ v := by
  induction v with
  | zero => simp [allColourings]
  | succ v ih =>
      simp [allColourings, List.finRange, ih, pow_succ]
      omega

theorem testEdges_found_iff {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (colour : Fin v → Fin 3) (zs : List (Fin e)) :
    (testEdges edge colour zs).1 = true ↔
      ∀ z ∈ zs, colour (edge z false) ≠ colour (edge z true) := by
  induction zs with
  | nil => simp [testEdges]
  | cons z zs ih =>
      by_cases h : colour (edge z false) = colour (edge z true)
      · simp [testEdges, h]
      · simp [testEdges, h, ih]

theorem testEdges_cost_le {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (colour : Fin v → Fin 3) (zs : List (Fin e)) :
    (testEdges edge colour zs).2 ≤ zs.length := by
  induction zs with
  | nil => simp [testEdges]
  | cons z zs ih =>
      by_cases h : colour (edge z false) = colour (edge z true)
      · simp [testEdges, h]
      · simp only [testEdges, if_neg h, List.length_cons]
        omega

theorem properTest_found_iff {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (colour : Fin v → Fin 3) :
    (properTest edge colour).1 = true ↔
      ∀ z : Fin e, colour (edge z false) ≠ colour (edge z true) := by
  rw [properTest, testEdges_found_iff]
  simp

theorem properTest_cost_le {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (colour : Fin v → Fin 3) : (properTest edge colour).2 ≤ e := by
  simpa [properTest] using
    testEdges_cost_le edge colour (List.finRange e)

theorem scan_found_iff {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (xs : List (Fin v → Fin 3)) :
    (scan edge xs).1 = true ↔
      ∃ colour ∈ xs, ∀ z : Fin e,
        colour (edge z false) ≠ colour (edge z true) := by
  induction xs with
  | nil => simp [scan]
  | cons colour xs ih =>
      cases h : (properTest edge colour).1 with
      | false =>
          have hp : ¬ ∀ z : Fin e,
              colour (edge z false) ≠ colour (edge z true) := by
            intro hc
            have ht := (properTest_found_iff edge colour).2 hc
            rw [h] at ht
            cases ht
          simp [scan, h, ih, hp]
      | true =>
          have hp : ∀ z : Fin e,
              colour (edge z false) ≠ colour (edge z true) :=
            (properTest_found_iff edge colour).1 h
          simp [scan, h, hp]

theorem scan_cost_le {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (xs : List (Fin v → Fin 3)) :
    (scan edge xs).2 ≤ xs.length * (e + 1) := by
  induction xs with
  | nil => simp [scan]
  | cons colour xs ih =>
      have hp := properTest_cost_le edge colour
      cases h : (properTest edge colour).1 with
      | false =>
          simp [scan, h]
          nlinarith [ih, hp]
      | true =>
          simp [scan, h]
          nlinarith [ih, hp]

theorem search_found_iff {v e : ℕ} (edge : Fin e → Bool → Fin v) :
    (search edge).1 = true ↔ ThreeColourable edge := by
  rw [search, scan_found_iff]
  simp only [ThreeColourable]
  constructor
  · rintro ⟨colour, -, h⟩
    exact ⟨colour, h⟩
  · rintro ⟨colour, h⟩
    exact ⟨colour, allColourings_mem v colour, h⟩

theorem search_cost_le {v e : ℕ} (edge : Fin e → Bool → Fin v) :
    (search edge).2 ≤ 3 ^ v * (e + 1) := by
  simpa only [search, allColourings_length] using
    scan_cost_le edge (allColourings v)

/-- The explicit search controls exactly the existing exceptional branch. -/
def scannedFallbackMatrix {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) : Fin (rows k) → Fin (cols k) → Bool :=
  if (search edge).1 then fun _ _ => false else hardMatrix k

theorem scannedFallbackMatrix_eq {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) : scannedFallbackMatrix edge k = fallbackMatrix edge k := by
  by_cases h : ThreeColourable edge
  · have hs := (search_found_iff edge).2 h
    simp [scannedFallbackMatrix, fallbackMatrix, h, hs]
  · have hs : (search edge).1 = false := by
      cases hh : (search edge).1 with
      | false => rfl
      | true => exact False.elim (h ((search_found_iff edge).1 hh))
    simp [scannedFallbackMatrix, fallbackMatrix, h, hs]

def scannedFallbackTable {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) : YaoMaterialization.SerializedTable (rows k) (cols k) :=
  YaoMaterialization.tabulate (scannedFallbackMatrix edge k)

theorem scannedFallbackTable_eq {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) : scannedFallbackTable edge k = fallbackTable edge k := by
  simp only [scannedFallbackTable, fallbackTable, scannedFallbackMatrix_eq]

/-- Exact output cell count, not folded into the colouring-search counter. -/
theorem scannedFallback_bits_length {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) : (scannedFallbackTable edge k).bits.length = rows k * cols k := by
  rw [scannedFallbackTable_eq]
  exact fallbackTable_bits_length edge k

theorem scannedFallback_bits_length_le {v e : ℕ}
    (edge : Fin e → Bool → Fin v) (k : ℕ) (hk : 1 ≤ k) :
    (scannedFallbackTable edge k).bits.length ≤ 2 ^ (2 * k) := by
  rw [scannedFallbackTable_eq]
  exact fallback_bits_length_le edge k hk



end Paper2.FiniteFallbackSearchScratch

