import Paper2.GeneratorFullSample

/-! The only branch layouts used by the actual recursive label generator.
The row-source discriminator follows a shared bounded-unary item ordinal. -/

namespace Paper2.RecursiveRequestCodeShape

open GeneratorCode GeneratorSource GeneratorFullSample

def TaggedShape (a b c : Code) : Prop :=
  ∃ x y z : Code,
    a = .append (.emit [false]) x ∧
    b = .append (.emit [true, false]) y ∧
    c = .append (.emit [true, true]) z

def RowsShape (a b c : Code) : Prop :=
  ∃ d : Nat, ∃ x y z r : Code,
    a = .append (.emit [false]) x ∧
    b = .append (.emit [true])
      (.append (.append (.ticket d) (.append (.emit [false]) y)) r) ∧
    c = .append (.emit [true])
      (.append (.append (.ticket d) (.append (.emit [true]) z)) r)

def PrefixTagged : Code → Prop
  | .emit _ | .ticket _ | .bit => True
  | .append a b => PrefixTagged a ∧ PrefixTagged b
  | .branch3 n firstCut secondCut a b c =>
      ((n = 0) ∨
       (n = 256 ∧ firstCut = 254 ∧ secondCut = 255 ∧ TaggedShape a b c) ∨
       (n = 512 ∧ firstCut = 510 ∧ secondCut = 511 ∧ RowsShape a b c)) ∧
      PrefixTagged a ∧ PrefixTagged b ∧ PrefixTagged c

theorem prefixTagged_append (a b : Code)
    (ha : PrefixTagged a) (hb : PrefixTagged b) :
    PrefixTagged (.append a b) := ⟨ha, hb⟩

theorem prefixTagged_copies (n : Nat) (c : Code)
    (hc : PrefixTagged c) : PrefixTagged (copies n c) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hc, ih⟩

theorem prefixTagged_outer (q₁ q₂ s : Nat) (c : Code)
    (hc : PrefixTagged c) : PrefixTagged (outerCode q₁ q₂ s c) := by
  exact ⟨trivial, prefixTagged_copies _ _ hc⟩

theorem prefixTagged_raw (q₁ q₂ s : Nat) (c : Code)
    (hc : PrefixTagged c) : PrefixTagged (rawCode q₁ q₂ s c) := by
  exact ⟨prefixTagged_copies _ _ hc,
    prefixTagged_copies _ _ (prefixTagged_outer q₁ q₂ s c hc)⟩

theorem prefixTagged_fixedTail (q₁ q₂ s : Nat) (c : Code)
    (hc : PrefixTagged c) : PrefixTagged (fixedTailCode q₁ q₂ s c) := by
  exact prefixTagged_copies _ _ (prefixTagged_outer q₁ q₂ s c hc)

theorem prefixTagged_tagged (q₁ q₂ s : Nat) (c : Code)
    (hc : PrefixTagged c) : PrefixTagged (taggedCode q₁ q₂ s c) := by
  refine ⟨Or.inr (Or.inl ⟨rfl, rfl, rfl, ?_⟩), ?_, ?_, ?_⟩
  · exact ⟨rawCode q₁ q₂ s c, fixedTailCode q₁ q₂ s c,
      outerCode q₁ q₂ s c, rfl, rfl, rfl⟩
  · exact ⟨trivial, prefixTagged_raw q₁ q₂ s c hc⟩
  · exact ⟨trivial, prefixTagged_fixedTail q₁ q₂ s c hc⟩
  · exact ⟨trivial, prefixTagged_outer q₁ q₂ s c hc⟩

theorem prefixTagged_template (q₁ q₂ : Nat) (c : Code)
    (hc : PrefixTagged c) : PrefixTagged (templateCode q₁ q₂ c) := by
  exact prefixTagged_copies _ _ ⟨trivial, hc⟩

theorem prefixTagged_templateRow (q₁ q₂ s : Nat) (c : Code)
    (hc : PrefixTagged c) : PrefixTagged (templateRowCode q₁ q₂ s c) := by
  exact ⟨trivial, prefixTagged_template q₁ q₂ c hc⟩

theorem prefixTagged_graphRows (n q₁ q₂ s : Nat) (c : Code)
    (hc : PrefixTagged c) :
    PrefixTagged (graphRowsCode (V := Fin n) q₁ q₂ s c) := by
  change PrefixTagged (rowsCode q₁ q₂ s (vertexLabelsCode (V := Fin n) s)
    (auxiliaryLabelsCode s) c)
  refine ⟨Or.inr (Or.inr ⟨rfl, rfl, rfl, ?_⟩), ?_, ?_, ?_⟩
  · exact ⟨4 * s, templateRowCode q₁ q₂ s c,
      .ticket (Fintype.card (Fin n)),
      .ticket (s - 3), c, rfl, rfl, rfl⟩
  · exact ⟨trivial, prefixTagged_templateRow q₁ q₂ s c hc⟩
  · exact ⟨trivial, ⟨⟨trivial, ⟨trivial, trivial⟩⟩, hc⟩⟩
  · exact ⟨trivial, ⟨⟨trivial, ⟨trivial, trivial⟩⟩, hc⟩⟩

theorem prefixTagged_recursiveCodes (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code)
    (hr : PrefixTagged row₀) (hc : PrefixTagged col₀) (k : Nat) :
    PrefixTagged (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1 ∧
    PrefixTagged (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 := by
  induction k with
  | zero => exact ⟨hr, hc⟩
  | succ k ih =>
      exact ⟨prefixTagged_copies _ _ ⟨trivial,
          prefixTagged_tagged q₁ q₂ s _ ih.2⟩,
        ⟨trivial, prefixTagged_copies _ _
          (prefixTagged_graphRows n q₁ q₂ s _ ih.1)⟩⟩

theorem prefixTagged_seedSampleCode (n p s q₁ q₂ w Q k mX mY : Nat) :
    PrefixTagged (seedSampleCode n p s q₁ q₂ w Q k mX mY) := by
  have h := prefixTagged_recursiveCodes n s q₁ q₂ w Q
    (copies p .bit) (.ticket p)
    (prefixTagged_copies p .bit trivial) trivial k
  exact ⟨prefixTagged_copies _ _ h.2, prefixTagged_copies _ _ h.1⟩

end Paper2.RecursiveRequestCodeShape

namespace Paper2.RecursiveRequestCodeShape

open RecursiveSamplingProgram RecursiveSamplingProgram.Program
open RecursiveLabelCodecScratch
open GeneratorCode GeneratorSource GeneratorFullSample

/-- A possible terminal value of the existing finite-choice program. This
relation states semantics only; the physical parser must still consume bits. -/
inductive Produces {A : Type*} : Program A → A → Prop where
  | pure (a : A) : Produces (.pure a) a
  | draw {n : Nat} {hn : 0 < n} {next : Fin n → Program A}
      (i : Fin n) {a : A} (h : Produces (next i) a) :
      Produces (.draw n hn next) a

theorem produces_bind {A B : Type*} (p : Program A) (f : A → Program B)
    {b : B} : Produces (Program.bind p f) b ↔
      ∃ a, Produces p a ∧ Produces (f a) b := by
  induction p with
  | pure a =>
      simp only [Program.bind_pure]
      constructor
      · intro h; exact ⟨a, .pure a, h⟩
      · rintro ⟨a', ha, hb⟩
        cases ha
        exact hb
  | draw n hn next ih =>
      simp only [Program.bind_draw]
      constructor
      · intro h
        cases h with
        | draw i hi =>
            obtain ⟨a, ha, hb⟩ := (ih i).mp hi
            exact ⟨a, .draw i ha, hb⟩
      · rintro ⟨a, ha, hb⟩
        cases ha with
        | draw i hi =>
            exact .draw i ((ih i).mpr ⟨a, hi, hb⟩)

theorem produces_map {A B : Type*} (f : A → B) (p : Program A)
    {b : B} : Produces (Program.map f p) b ↔
      ∃ a, Produces p a ∧ f a = b := by
  simp only [Program.map, produces_bind]
  constructor
  · rintro ⟨a, ha, hb⟩
    cases hb
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, .pure (f a)⟩

theorem produces_concat (p q : Program (List Bool)) {bits : List Bool} :
    Produces (GeneratorCode.concat p q) bits ↔
      ∃ x y, Produces p x ∧ Produces q y ∧ bits = x ++ y := by
  simp only [GeneratorCode.concat, produces_bind]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨y, hy', he⟩ := (produces_map (fun ys => x ++ ys) q).mp hy
    exact ⟨x, y, hx, hy', he.symm⟩
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨x, hx, (produces_map (fun ys => x ++ ys) q).mpr ⟨y, hy, rfl⟩⟩

theorem produces_emit (bits x : List Bool) :
    Produces (meaning (.emit bits)) x ↔ x = bits := by
  constructor
  · intro h; cases h; rfl
  · intro h
    subst x
    exact .pure bits

theorem produces_ticket (n : Nat) (bits : List Bool) :
    Produces (meaning (.ticket n)) bits ↔
      (n = 0 ∧ bits = []) ∨
        ∃ i : Fin n, bits = (finCodec n).encode i := by
  cases n with
  | zero =>
      change Produces (.pure []) bits ↔
        ((0 : Nat) = 0 ∧ bits = []) ∨
          ∃ i : Fin 0, bits = (finCodec 0).encode i
      constructor
      · intro h; cases h; exact Or.inl ⟨rfl, rfl⟩
      · rintro (⟨_, rfl⟩ | ⟨i, _⟩)
        · exact .pure []
        · exact i.elim0
  | succ n =>
      simp only [meaning, produces_map, RecursiveSamplingProgram.Program.uniform]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact Or.inr ⟨i, rfl⟩
      · rintro (⟨h, _⟩ | ⟨i, rfl⟩)
        · omega
        · exact ⟨i, .draw i (.pure i), rfl⟩

theorem produces_prefixed (tag bits : List Bool) (c : Code) :
    Produces (meaning (.append (.emit tag) c)) bits ↔
      ∃ rest, Produces (meaning c) rest ∧ bits = tag ++ rest := by
  change Produces (GeneratorCode.concat (meaning (.emit tag)) (meaning c)) bits ↔ _
  rw [produces_concat]
  constructor
  · rintro ⟨x, y, hx, hy, hbits⟩
    have hx' := (produces_emit tag x).mp hx
    subst x
    exact ⟨y, hy, hbits⟩
  · rintro ⟨rest, hr, hbits⟩
    exact ⟨tag, rest, (produces_emit tag tag).mpr rfl, hr, hbits⟩

theorem produces_branch3 {n a b : Nat} (h : 0 < n)
    (first second third : Code) (bits : List Bool) :
    Produces (meaning (.branch3 n a b first second third)) bits ↔
      ∃ i : Fin n,
        Produces (if i.val < a then meaning first
          else if i.val < b then meaning second else meaning third) bits := by
  cases n with
  | zero => omega
  | succ n =>
      change Produces (.draw (n + 1) (by omega) (fun i =>
        if i.val < a then meaning first else if i.val < b then meaning second
          else meaning third)) bits ↔ _
      constructor
      · intro hp
        cases hp with
        | draw i hi => exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩
        exact .draw i hi

theorem tagged_output_cases (q₁ q₂ s : Nat) (c : Code)
    (bits : List Bool)
    (h : Produces (meaning (taggedCode q₁ q₂ s c)) bits) :
    (∃ tail, bits = false :: tail) ∨
    (∃ tail, bits = true :: false :: tail) ∨
    (∃ tail, bits = true :: true :: tail) := by
  obtain ⟨i, hi⟩ := (produces_branch3 (by decide) _ _ _ bits).mp h
  by_cases h₁ : i.val < 254
  · have hp : Produces
      (meaning (.append (.emit [false]) (rawCode q₁ q₂ s c))) bits := by
        simpa only [h₁, ↓reduceIte] using hi
    obtain ⟨tail, _, hb⟩ :=
      (produces_prefixed [false] bits (rawCode q₁ q₂ s c)).mp hp
    exact Or.inl ⟨tail, hb⟩
  · by_cases h₂ : i.val < 255
    · have hp : Produces
        (meaning (.append (.emit [true, false])
          (fixedTailCode q₁ q₂ s c))) bits := by
          simpa only [h₁, h₂, ↓reduceIte] using hi
      obtain ⟨tail, _, hb⟩ :=
        (produces_prefixed [true, false] bits (fixedTailCode q₁ q₂ s c)).mp hp
      exact Or.inr (Or.inl ⟨tail, hb⟩)
    · have hp : Produces
        (meaning (.append (.emit [true, true]) (outerCode q₁ q₂ s c))) bits := by
          simpa only [h₁, h₂, ↓reduceIte] using hi
      obtain ⟨tail, _, hb⟩ :=
        (produces_prefixed [true, true] bits (outerCode q₁ q₂ s c)).mp hp
      exact Or.inr (Or.inr ⟨tail, hb⟩)

theorem rows_output_cases (n q₁ q₂ s : Nat) (c : Code)
    (bits : List Bool)
    (h : Produces (meaning (graphRowsCode (V := Fin n) q₁ q₂ s c)) bits) :
    (∃ tail, bits = false :: tail) ∨
    (∃ item rest, Produces (meaning (.ticket (4 * s))) item ∧
      bits = true :: (item ++ false :: rest)) ∨
    (∃ item rest, Produces (meaning (.ticket (4 * s))) item ∧
      bits = true :: (item ++ true :: rest)) := by
  obtain ⟨i, hi⟩ := (produces_branch3 (by decide) _ _ _ bits).mp h
  by_cases h₁ : i.val < 510
  · have hp : Produces
      (meaning (.append (.emit [false]) (templateRowCode q₁ q₂ s c))) bits := by
        simpa only [graphRowsCode, rowsCode, h₁, ↓reduceIte] using hi
    obtain ⟨tail, _, hb⟩ :=
      (produces_prefixed [false] bits (templateRowCode q₁ q₂ s c)).mp hp
    exact Or.inl ⟨tail, hb⟩
  · by_cases h₂ : i.val < 511
    · have hp : Produces (meaning (.append (.emit [true])
        (.append (vertexLabelsCode (V := Fin n) s) c))) bits := by
          simpa only [graphRowsCode, rowsCode, h₁, h₂, ↓reduceIte] using hi
      obtain ⟨tail, htail, hb⟩ :=
        (produces_prefixed [true] bits
          (.append (vertexLabelsCode (V := Fin n) s) c)).mp hp
      obtain ⟨itemCode, restCode, hitemCode, _, htailEq⟩ :=
        (produces_concat (meaning (vertexLabelsCode (V := Fin n) s))
          (meaning c)).mp htail
      obtain ⟨item, tagTail, hitem, htagTail, hitemEq⟩ :=
        (produces_concat (meaning (.ticket (4 * s)))
          (meaning (.append (.emit [false])
            (.ticket (Fintype.card (Fin n)))))).mp hitemCode
      obtain ⟨rest, _, htagEq⟩ :=
        (produces_prefixed [false] tagTail
          (.ticket (Fintype.card (Fin n)))).mp htagTail
      exact Or.inr (Or.inl ⟨item, rest ++ restCode, hitem, by
        simp only [hb, htailEq, hitemEq, htagEq]
        simp [List.append_assoc]⟩)
    · have hp : Produces (meaning (.append (.emit [true])
        (.append (auxiliaryLabelsCode s) c))) bits := by
          simpa only [graphRowsCode, rowsCode, h₁, h₂, ↓reduceIte] using hi
      obtain ⟨tail, htail, hb⟩ :=
        (produces_prefixed [true] bits (.append (auxiliaryLabelsCode s) c)).mp hp
      obtain ⟨itemCode, restCode, hitemCode, _, htailEq⟩ :=
        (produces_concat (meaning (auxiliaryLabelsCode s)) (meaning c)).mp htail
      obtain ⟨item, tagTail, hitem, htagTail, hitemEq⟩ :=
        (produces_concat (meaning (.ticket (4 * s)))
          (meaning (.append (.emit [true]) (.ticket (s - 3))))).mp hitemCode
      obtain ⟨rest, _, htagEq⟩ :=
        (produces_prefixed [true] tagTail (.ticket (s - 3))).mp htagTail
      exact Or.inr (Or.inr ⟨item, rest ++ restCode, hitem, by
        simp only [hb, htailEq, hitemEq, htagEq]
        simp [List.append_assoc]⟩)

/-- Branch readout for the two concrete, prefix-disjoint layouts. A zero
item alphabet emits no unary token, so that case peeks at the next bit. -/
def taggedRoute : List Bool → Option Nat
  | false :: _ => some 0
  | true :: false :: _ => some 1
  | true :: true :: _ => some 2
  | _ => none

def rowsRoute (itemAlphabet : Nat) : List Bool → Option Nat
  | false :: _ => some 0
  | true :: rest =>
      let afterItem := if itemAlphabet = 0 then some (0, rest)
        else RecursiveLabelCodecScratch.decodeUnary rest
      match afterItem with
      | some (_, false :: _) => some 1
      | some (_, true :: _) => some 2
      | _ => none
  | [] => none

private theorem decodeUnary_replicate (j : Nat) (rest : List Bool) :
    RecursiveLabelCodecScratch.decodeUnary
      (List.replicate j true ++ false :: rest) = some (j, rest) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate, RecursiveLabelCodecScratch.decodeUnary, ih]

theorem taggedRoute_first (tail : List Bool) :
    taggedRoute (false :: tail) = some 0 := rfl
theorem taggedRoute_second (tail : List Bool) :
    taggedRoute (true :: false :: tail) = some 1 := rfl
theorem taggedRoute_third (tail : List Bool) :
    taggedRoute (true :: true :: tail) = some 2 := rfl

theorem rowsRoute_first (d : Nat) (tail : List Bool) :
    rowsRoute d (false :: tail) = some 0 := rfl

theorem rowsRoute_second (d : Nat) (item rest : List Bool)
    (h : Produces (meaning (.ticket d)) item) :
    rowsRoute d (true :: (item ++ false :: rest)) = some 1 := by
  rcases (produces_ticket d item).mp h with (⟨rfl, rfl⟩ | ⟨i, rfl⟩)
  · rfl
  · have hd : d ≠ 0 := by exact Nat.ne_zero_of_lt i.isLt
    simp [rowsRoute, hd, finCodec, decodeUnary_replicate]

theorem rowsRoute_third (d : Nat) (item rest : List Bool)
    (h : Produces (meaning (.ticket d)) item) :
    rowsRoute d (true :: (item ++ true :: rest)) = some 2 := by
  rcases (produces_ticket d item).mp h with (⟨rfl, rfl⟩ | ⟨i, rfl⟩)
  · rfl
  · have hd : d ≠ 0 := by exact Nat.ne_zero_of_lt i.isLt
    simp [rowsRoute, hd, finCodec, decodeUnary_replicate]
end Paper2.RecursiveRequestCodeShape
