import CurrentAdditive.CylinderSource

/-!
Executable rational matrix operations toward v27 Appendix H, `det:code`.
Rows and coefficients are arrays, and every pivot choice is made in increasing
index order. `checkedDependence` checks the output against the original matrix;
this file does not yet prove that elimination always finds a dependence when
there are more columns than rows, nor a polynomial bit-cost bound.
-/

namespace CurrentAdditive

namespace SequentialCode

/-- Out-of-range cells are zero. The intended matrices are rectangular; this
convention makes every intermediate operation total. -/
def cell (a : Array (Array ℚ)) (i j : Nat) : ℚ :=
  (a[i]?.getD #[])[j]?.getD 0

def rowCount (a : Array (Array ℚ)) : Nat := a.size

def columnCount (a : Array (Array ℚ)) : Nat :=
  a.foldl (fun n row => max n row.size) 0

def replaceRow (a : Array (Array ℚ)) (i : Nat) (row : Array ℚ) :
    Array (Array ℚ) :=
  a.set! i row

/-- Swap two rows, including when the indices coincide. -/
def swapRows (a : Array (Array ℚ)) (i j : Nat) : Array (Array ℚ) :=
  let ri := a[i]?.getD #[]
  let rj := a[j]?.getD #[]
  replaceRow (replaceRow a i rj) j ri

/-- First nonzero entry in a given column, at or below the active row. -/
def pivotRow (a : Array (Array ℚ)) (r c : Nat) : Option Nat :=
  (List.range a.size).find? (fun i => decide (r ≤ i ∧ cell a i c ≠ 0))

/-- Normalize a pivot row and clear its column in every other row. -/
def clearPivot (a : Array (Array ℚ)) (r c cols : Nat) : Array (Array ℚ) := Id.run do
  let p := cell a r c
  if p = 0 then return a
  let normalized := Array.ofFn (n := cols) (fun j => cell a r j.val / p)
  let mut b := replaceRow a r normalized
  for i in [:a.size] do
    if i != r then
      let factor := cell a i c
      let next := Array.ofFn (n := cols)
        (fun j => cell a i j.val - factor * (normalized[j.val]?.getD 0))
      b := replaceRow b i next
  return b

/-- Deterministic Gauss--Jordan computation with a column fuel. The returned
list records normalized pivot row/column pairs in discovery order. -/
def echelon (a : Array (Array ℚ)) (r c cols fuel : Nat) :
    Array (Array ℚ) × List (Nat × Nat) :=
  match fuel with
  | 0 => (a, [])
  | fuel + 1 =>
    if c < cols ∧ r < a.size then
      match pivotRow a r c with
      | none => echelon a r (c + 1) cols fuel
      | some i =>
        let b := clearPivot (swapRows a r i) r c cols
        let (out, pivots) := echelon b (r + 1) (c + 1) cols fuel
        (out, (r, c) :: pivots)
    else (a, [])

/-- Pick the first column that was not used as a pivot. -/
def freeColumn (cols : Nat) (pivots : List (Nat × Nat)) : Option Nat :=
  (List.range cols).find? (fun c => !pivots.any (fun p => p.2 == c))

/-- A candidate null vector obtained from the reduced matrix. -/
def dependenceCandidate (a : Array (Array ℚ)) : Option (Array ℚ) := do
  let cols := columnCount a
  let (b, pivots) := echelon a 0 0 cols cols
  let free ← freeColumn cols pivots
  some <| Array.ofFn (n := cols) fun j =>
    if j.val == free then (1 : ℚ)
    else match pivots.find? (fun p => p.2 == j.val) with
      | some (r, _) => -cell b r free
      | none => 0

/-- The finite rational check defining a genuine nonzero kernel vector. -/
def dependenceCheck (a : Array (Array ℚ)) (x : Array ℚ) : Bool :=
  decide (x.size = columnCount a) &&
  (List.range x.size).any (fun j => decide (x[j]?.getD 0 ≠ 0)) &&
  (List.range a.size).all (fun i =>
    decide (((List.range x.size).map
      (fun j => cell a i j * (x[j]?.getD 0))).sum = 0))

def IsDependence (a : Array (Array ℚ)) (x : Array ℚ) : Prop :=
  dependenceCheck a x = true

theorem dependence_spec (a : Array (Array ℚ)) (x : Array ℚ) :
    IsDependence a x ↔
      x.size = columnCount a ∧
      (∃ j ∈ List.range x.size, x[j]?.getD 0 ≠ 0) ∧
      ∀ i ∈ List.range a.size,
        ((List.range x.size).map
          (fun j => cell a i j * (x[j]?.getD 0))).sum = 0 := by
  simp [IsDependence, dependenceCheck, Bool.and_eq_true, and_assoc]

/-- Verification makes every returned candidate a certified exact dependence.
Completeness of the pivot computation remains a separate theorem obligation. -/
def checkedDependence (a : Array (Array ℚ)) :
    Option {x : Array ℚ // IsDependence a x} :=
  match dependenceCandidate a with
  | none => none
  | some x =>
    if h : dependenceCheck a x = true then some ⟨x, h⟩ else none

theorem checkedDependence_sound (a : Array (Array ℚ))
    (x : {x : Array ℚ // IsDependence a x})
    (_h : checkedDependence a = some x) : IsDependence a x :=
  x.property

/-- Clear rational denominators with the product of their denominators, then
check integrality before extracting integer numerators. -/
def clearDenominators (x : Array ℚ) : Option (Array ℤ) :=
  let b : Nat := x.foldl (fun acc r => acc * r.den) 1
  let scaled := x.map (fun r => (b : ℚ) * r)
  if scaled.all (fun r => decide (r.den = 1)) then
    some (scaled.map Rat.num)
  else none

/-- A certified integer relation suitable for the manuscript's min-ratio
update. The final rational check protects against any clearing error. -/
def checkedIntegerDependence (a : Array (Array ℚ)) :
    Option {z : Array ℤ //
      IsDependence a (z.map (fun (k : ℤ) => (k : ℚ)))} :=
  match checkedDependence a with
  | none => none
  | some cert =>
    match clearDenominators cert.val with
    | none => none
    | some z =>
      if h : dependenceCheck a (z.map (fun (k : ℤ) => (k : ℚ))) = true then
        some ⟨z, h⟩
      else none

theorem checkedIntegerDependence_sound (a : Array (Array ℚ))
    (z : {z : Array ℤ // IsDependence a (z.map (fun (k : ℤ) => (k : ℚ)))})
    (_h : checkedIntegerDependence a = some z) :
    IsDependence a (z.val.map (fun (k : ℤ) => (k : ℚ))) := z.property

/-- A fully executable one-step weight update, after a dependence is found.
The minimum is over positive coefficients in index order. -/
def minimumRatio (weights coeff : Array ℚ) : Option ℚ :=
  (List.range (min weights.size coeff.size)).foldl (fun best i =>
    let ai := coeff[i]?.getD 0
    if 0 < ai then
      let ratio := (weights[i]?.getD 0) / ai
      match best with
      | none => some ratio
      | some previous => some (min previous ratio)
    else best) none

def eliminateWeights (weights coeff : Array ℚ) : Option (Array ℚ) := do
  let ratio ← minimumRatio weights coeff
  some <| Array.ofFn (n := weights.size)
    (fun i => weights[i] - ratio * (coeff[i.val]?.getD 0))

/-- Retain exactly the strictly positive entries, preserving their indices. -/
def positiveIndices (weights : Array ℚ) : List Nat :=
  (List.range weights.size).filter (fun i => decide (0 < weights[i]?.getD 0))

def selectWeights (weights : Array ℚ) (indices : List Nat) : Array ℚ :=
  indices.toArray.map (fun i => weights[i]?.getD 0)

def selectColumns (a : Array (Array ℚ)) (indices : List Nat) :
    Array (Array ℚ) :=
  a.map (fun row => indices.toArray.map (fun i => row[i]?.getD 0))

def rowMoment (a : Array (Array ℚ)) (weights : Array ℚ) (i : Nat) : ℚ :=
  ((List.range weights.size).map
    (fun j => cell a i j * (weights[j]?.getD 0))).sum

/-- Exact fail-closed check for mass and all supplied feature moments. -/
def sameMoments (a : Array (Array ℚ))
    (before after : Array ℚ) : Bool :=
  decide (before.size = after.size) &&
  decide (before.toList.sum = after.toList.sum) &&
  (List.range a.size).all (fun i =>
    decide (rowMoment a before i = rowMoment a after i))

theorem sameMoments_spec (a : Array (Array ℚ))
    (before after : Array ℚ) :
    sameMoments a before after = true ↔
      before.size = after.size ∧
      before.toList.sum = after.toList.sum ∧
      ∀ i ∈ List.range a.size,
        rowMoment a before i = rowMoment a after i := by
  simp [sameMoments, Bool.and_eq_true, and_assoc]

/-- One checked elimination and deletion of zero weights. Returning `none`
means either no certified relation was produced or support did not shrink. -/
def compressOnce (a : Array (Array ℚ)) (weights : Array ℚ) :
    Option (Array (Array ℚ) × Array ℚ) := do
  if weights.size != columnCount a then none else
  let cert ← checkedDependence a
  let updated ← eliminateWeights weights cert.1
  let indices := positiveIndices updated
  if indices.length < weights.size then
    some (selectColumns a indices, selectWeights updated indices)
  else none

/-- Fuel-bounded exact rational compression. The construction has no classical
choice and can be evaluated, but its success/complexity theorem is pending. -/
def compressFuel (a : Array (Array ℚ)) (weights : Array ℚ)
    (limit fuel : Nat) : Option (Array (Array ℚ) × Array ℚ) :=
  match fuel with
  | 0 => if weights.size ≤ limit then some (a, weights) else none
  | fuel + 1 =>
    if weights.size ≤ limit then some (a, weights) else do
      let (b, next) ← compressOnce a weights
      compressFuel b next limit fuel

/-- Product append keeps each old index and each alphabet index separately. -/
def appendWeighted {α β : Type*} (source : Array (α × ℚ))
    (alphabet : Array (β × ℚ)) : Array ((α × β) × ℚ) :=
  source.foldl (fun out x =>
    out ++ alphabet.map (fun y => ((x.1, y.1), x.2 * y.2))) #[]

/-- Append one coordinate to a finite word. -/
def appendWord {Y : Type*} {q : Nat} (v : Fin q → Y) (y : Y) :
    Fin (q + 1) → Y := fun j =>
  if h : j.val < q then v ⟨j.val, h⟩ else y

/-- The explicitly indexed append used before each compression. -/
def appendSource {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ)) : Array ((Fin (q + 1) → Y) × ℚ) :=
  source.foldl (fun out x =>
    out ++ alphabet.map (fun y => (appendWord x.1 y.1, x.2 * y.2))) #[]

/-- Assemble one row per feature. The array positions retain distinct labels
even if two labels happen to decode to the same mathematical word. -/
def featureRows {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Array (Array ℚ) :=
  Array.ofFn (n := n) (fun j => source.map (fun x => φ x.1 j))

def sourceMass {α : Type*} (source : Array (α × ℚ)) : ℚ :=
  (source.toList.map Prod.snd).sum

def sourceMoment {α : Type*} {n : Nat} (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (j : Fin n) : ℚ :=
  (source.toList.map (fun x => x.2 * φ x.1 j)).sum

/-- Check the actual retained, labelled source after zero deletion. -/
def sourceMomentsCheck {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (before after : Array (α × ℚ)) : Bool :=
  decide (sourceMass before = sourceMass after ∧
    ∀ j : Fin n, sourceMoment φ before j = sourceMoment φ after j)

theorem sourceMomentsCheck_spec {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (before after : Array (α × ℚ)) :
    sourceMomentsCheck n φ before after = true ↔
      sourceMass before = sourceMass after ∧
      ∀ j : Fin n, sourceMoment φ before j = sourceMoment φ after j := by
  simp [sourceMomentsCheck]

/-- Carry labels through one exact checked support reduction. -/
def compressSourceOnce {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Option (Array (α × ℚ)) :=
  let matrix := featureRows n φ source
  let weights := source.map Prod.snd
  match checkedIntegerDependence matrix with
  | none => none
  | some cert =>
    match eliminateWeights weights (cert.val.map (fun (k : ℤ) => (k : ℚ))) with
    | none => none
    | some updated =>
      let indices := positiveIndices updated
      if weights.all (fun w => decide (0 < w)) &&
          updated.all (fun w => decide (0 ≤ w)) &&
          sameMoments matrix weights updated then
        if indices.length < source.size then
          let out := (indices.filterMap (fun i =>
            (source[i]?).map (fun entry => (entry.1, updated[i]?.getD 0)))).toArray
          if sourceMomentsCheck n φ source out then some out else none
        else none
      else none

private theorem filterMap_length_le {α β : Type*} (f : α → Option β)
    (l : List α) : (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.filterMap_cons]
      cases f x <;> simp_all; omega

theorem compressSourceOnce_size_lt {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source out : Array (α × ℚ))
    (h : compressSourceOnce n φ source = some out) :
    out.size < source.size := by
  unfold compressSourceOnce at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            exact lt_of_le_of_lt
              (by simpa using (filterMap_length_le _ _))
              (by assumption)
          · cases h
        · cases h
      · cases h

theorem compressSourceOnce_moments {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source out : Array (α × ℚ))
    (h : compressSourceOnce n φ source = some out) :
    sourceMass source = sourceMass out ∧
      ∀ j : Fin n, sourceMoment φ source j = sourceMoment φ out j := by
  unfold compressSourceOnce at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            exact (sourceMomentsCheck_spec n φ source _).mp (by assumption)
          · cases h
        · cases h
      · cases h

/-- Exactly `fuel` opportunities to remove a support point. -/
def compressSourceFuel {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) : Option (Array (α × ℚ)) :=
  match fuel with
  | 0 => if source.size ≤ n then some source else none
  | fuel + 1 =>
    if source.size ≤ n then some source else do
      let next ← compressSourceOnce n φ source
      compressSourceFuel n φ next fuel

theorem compressSourceFuel_size_le {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) (out : Array (α × ℚ))
    (h : compressSourceFuel n φ source fuel = some out) : out.size ≤ n := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressSourceFuel] at h
      split_ifs at h with hs
      · cases h
        exact hs
  | succ fuel ih =>
      simp only [compressSourceFuel] at h
      split_ifs at h with hs
      · cases h
        exact hs
      · simp only [Option.bind_eq_bind, Option.bind] at h
        split at h
        · cases h
        · exact ih _ h

theorem compressSourceFuel_moments {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressSourceFuel n φ source fuel = some out) :
    sourceMass source = sourceMass out ∧
      ∀ j : Fin n, sourceMoment φ source j = sourceMoment φ out j := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressSourceFuel] at h
      split_ifs at h
      cases h
      exact ⟨rfl, fun _ => rfl⟩
  | succ fuel ih =>
      simp only [compressSourceFuel] at h
      split_ifs at h
      · cases h
        exact ⟨rfl, fun _ => rfl⟩
      · cases hstep : compressSourceOnce n φ source with
        | none => simp [hstep] at h
        | some next =>
            simp [hstep] at h
            have hfirst := compressSourceOnce_moments n φ source next hstep
            have hrest := ih next h
            exact ⟨hfirst.1.trans hrest.1,
              fun j => (hfirst.2 j).trans (hrest.2 j)⟩

/-- At coordinate `j`, retain all old partial assignments and add every
alphabet value to those using fewer than `D` coordinates. -/
def extendFeatures {Y : Type*} (D : Nat) (alphabet : Array Y)
    (j : Nat) (features : Array (List (Nat × Y))) :
    Array (List (Nat × Y)) :=
  features ++ (features.filter (fun c => decide (c.length < D))).foldl
    (fun out c => out ++ alphabet.map (fun y => (j, y) :: c)) #[]

/-- Explicit feature enumeration, beginning with the empty cylinder. -/
def generatedFeatures {Y : Type*} (q D : Nat) (alphabet : Array Y) :
    Array (List (Nat × Y)) :=
  (List.range q).foldl
    (fun current j => extendFeatures D alphabet j current) #[[]]

/-- Evaluate one generated cylinder on a length-`q` word. -/
def generatedFeatureValue {Y : Type*} [DecidableEq Y] {q : Nat}
    (v : Fin q → Y) (feature : List (Nat × Y)) : ℚ :=
  if feature.all (fun p =>
      if h : p.1 < q then decide (v ⟨p.1, h⟩ = p.2) else false)
  then 1 else 0

/-- A deterministic, fuel-bounded sequential candidate for the manuscript's
`Code_D`. All features are generated from finite arrays. It is executable;
success and exact marginal correctness are not yet theorems. A failed check
returns `none` instead of silently assuming a witness. -/
def sequentialCandidate {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    (q : Nat) → Option (Array ((Fin q → Y) × ℚ))
  | 0 => some #[(Fin.elim0, 1)]
  | q + 1 => do
    let prev ← sequentialCandidate D alphabet q
    let extended := appendSource prev alphabet
    let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
    let n := featuresAt.size
    let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
      fun v j => generatedFeatureValue v featuresAt[j]
    compressSourceFuel n features extended extended.size

theorem sequentialCandidate_size_le_features {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat)
    (out : Array ((Fin (q + 1) → Y) × ℚ))
    (h : sequentialCandidate D alphabet (q + 1) = some out) :
    out.size ≤ (generatedFeatures (q + 1) D (alphabet.map Prod.fst)).size := by
  simp only [sequentialCandidate] at h
  cases hprev : sequentialCandidate D alphabet q with
  | none => simp [hprev] at h
  | some prev =>
      simp [hprev] at h
      exact compressSourceFuel_size_le _ _ _ _ _ h

#eval (checkedDependence #[#[1, 0, 1], #[0, 1, 1]]).map (fun x => x.1)
#eval (checkedIntegerDependence #[#[1, 0, 1], #[0, 1, 1]]).map (fun x => x.1)
#eval compressFuel #[#[1, 1, 1]] #[1 / 3, 1 / 3, 1 / 3] 1 3
#eval (generatedFeatures 3 1 #[false, true]).size
#eval (sequentialCandidate 1 (#[(false, 1 / 2), (true, 1 / 2)]) 3).map
  (fun source => source.size)
#print axioms checkedDependence_sound
#print axioms checkedIntegerDependence_sound
#print axioms dependence_spec
#print axioms sameMoments_spec
#print axioms sourceMomentsCheck_spec
#print axioms compressSourceOnce_size_lt
#print axioms compressSourceOnce_moments
#print axioms compressSourceFuel_size_le
#print axioms compressSourceFuel_moments
#print axioms sequentialCandidate
#print axioms sequentialCandidate_size_le_features

end SequentialCode

end CurrentAdditive
