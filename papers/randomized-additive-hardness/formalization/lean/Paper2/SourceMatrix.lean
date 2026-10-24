import Paper2.InterlaceRank

/-!
# The actual full-product source matrices

Frozen Paper 2 v12, Section 4, equations `eq:source-interlaces`,
`eq:raw-template`, `eq:raw-source` and the three tagged column families.

These definitions use the complete finite product carriers, not a record
postulating a gap. The activity map is public source data: `none` means an
inactive item and `some p` gives the active item's position. Injectivity of
active positions and the colouring promise are not needed to define an entry.
The graph-to-activity construction and the protected probability laws are
separate obligations. No colouring or communication optimum is an input.
-/

namespace Paper2.SourceMatrix

variable {X Y I : Type*} {s q₁ q₂ : ℕ}

abbrev Tail (s : ℕ) (Y : Type*) := Fin (s + 1) → Y
abbrev Word (q₁ s : ℕ) (Y : Type*) := Fin (q₁ + s + 1) → Y
abbrev InnerRow (q₁ : ℕ) (X : Type*) := Fin q₁ × X
abbrev Template (q₁ q₂ : ℕ) (X : Type*) := Fin q₂ → InnerRow q₁ X
abbrev OuterColumn (q₁ q₂ s : ℕ) (Y : Type*) := Fin q₂ × Word q₁ s Y
abbrev RawColumn (q₁ q₂ s : ℕ) (Y : Type*) :=
  Tail s Y × (Fin s → OuterColumn q₁ q₂ s Y)
abbrev RawRow (q₁ q₂ s : ℕ) (X I : Type*) :=
  (Fin s × Template q₁ q₂ X) ⊕ (I × X)

/-- The first `q₁` positions of a word, reserving its last `s+1` positions. -/
def head (γ : Word q₁ s Y) : Fin q₁ → Y :=
  fun i => γ ⟨i, by omega⟩

/-- The last `s+1` positions used on diagonal columns. -/
def tail (γ : Word q₁ s Y) : Tail s Y :=
  fun i => γ ⟨q₁ + i, by omega⟩

def M₁ (R : X → Y → Bool) : InnerRow q₁ X → Word q₁ s Y → Bool :=
  fun a γ => R a.2 (head γ a.1)

def M₂ (R : X → Y → Bool) :
    OuterColumn q₁ q₂ s Y → Template q₁ q₂ X → Bool :=
  fun j z => M₁ R (z j.1) j.2

def T (R : X → Y → Bool) :
    Template q₁ q₂ X → OuterColumn q₁ q₂ s Y → Bool :=
  fun z j => M₂ R j z

theorem M₁_eq_indexedInterlace (R : X → Y → Bool) :
    (M₁ R : InnerRow q₁ X → Word q₁ s Y → Bool) =
      indexedInterlace R head := rfl

theorem M₂_eq_fullInterlace (R : X → Y → Bool) :
    (M₂ R : OuterColumn q₁ q₂ s Y → Template q₁ q₂ X → Bool) =
      fullInterlace (fun γ a => M₁ R a γ) q₂ := rfl

/-- Off-diagonal columns use the neutral tail position. With a nonempty
bin set, its first bin gives the unique common coordinate when diagonal. -/
def sourcePosition [NeZero s] (activity : I → Fin q₂ → Option (Fin s))
    (i : I) (Z : RawColumn q₁ q₂ s Y) : Fin (s + 1) :=
  if (∀ p, (Z.2 p).1 = (Z.2 0).1) then
    match activity i (Z.2 0).1 with
    | some p => p.castSucc
    | none => Fin.last s
  else Fin.last s

def sourceColumn [NeZero s] (activity : I → Fin q₂ → Option (Fin s))
    (i : I) (Z : RawColumn q₁ q₂ s Y) : Y :=
  Z.1 (sourcePosition activity i Z)

/-- Every raw entry requests exactly one base entry. -/
def baseRequest [NeZero s] (activity : I → Fin q₂ → Option (Fin s))
    (k : RawRow q₁ q₂ s X I) (Z : RawColumn q₁ q₂ s Y) : X × Y :=
  match k with
  | .inl (p, z) => ((z (Z.2 p).1).2, head (Z.2 p).2 (z (Z.2 p).1).1)
  | .inr (i, u) => (u, sourceColumn activity i Z)

def raw [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) :
    RawRow q₁ q₂ s X I → RawColumn q₁ q₂ s Y → Bool :=
  fun k Z => R (baseRequest activity k Z).1 (baseRequest activity k Z).2

@[simp] theorem raw_template [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (p : Fin s) (z : Template q₁ q₂ X) (Z : RawColumn q₁ q₂ s Y) :
    raw R activity (.inl (p, z)) Z = M₂ R (Z.2 p) z := rfl

@[simp] theorem raw_source [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (i : I) (u : X) (Z : RawColumn q₁ q₂ s Y) :
    raw R activity (.inr (i, u)) Z = R u (sourceColumn activity i Z) := rfl

theorem raw_template_eq_interlace [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) :
    (fun k Z => raw (q₁ := q₁) R activity (.inl k) Z) =
      fun k Z => fullInterlace (T R) s k Z.2 := rfl

/-- Tags remain distinct input labels even when their raw columns coincide. -/
inductive TaggedColumn (q₁ q₂ s : ℕ) (Y : Type*) where
  | unrestricted : RawColumn q₁ q₂ s Y → TaggedColumn q₁ q₂ s Y
  | fixedTail : (Fin s → OuterColumn q₁ q₂ s Y) → TaggedColumn q₁ q₂ s Y
  | diagonal : OuterColumn q₁ q₂ s Y → TaggedColumn q₁ q₂ s Y
  deriving Fintype

def forgetTag (ξ₀ : Tail s Y) : TaggedColumn q₁ q₂ s Y → RawColumn q₁ q₂ s Y
  | .unrestricted Z => Z
  | .fixedTail js => (ξ₀, js)
  | .diagonal j => (tail j.2, fun _ => j)

theorem forgetTag_surjective (ξ₀ : Tail s Y) :
    Function.Surjective (forgetTag (q₁ := q₁) (q₂ := q₂) ξ₀) :=
  fun Z => ⟨.unrestricted Z, rfl⟩

/-- The source matrix is the transpose of the tagged raw matrix. -/
def N [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    TaggedColumn q₁ q₂ s Y → RawRow q₁ q₂ s X I → Bool :=
  fun Z k => raw R activity k (forgetTag ξ₀ Z)

@[simp] theorem N_unrestricted [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (Z : RawColumn q₁ q₂ s Y) (k : RawRow q₁ q₂ s X I) :
    N R activity ξ₀ (.unrestricted Z) k = raw R activity k Z := rfl

theorem sourcePosition_offDiagonal [NeZero s]
    (activity : I → Fin q₂ → Option (Fin s)) (i : I)
    (Z : RawColumn q₁ q₂ s Y) (h : ¬ ∀ p, (Z.2 p).1 = (Z.2 0).1) :
    sourcePosition activity i Z = Fin.last s := by
  simp [sourcePosition, h]

theorem sourcePosition_diagonal [NeZero s]
    (activity : I → Fin q₂ → Option (Fin s)) (i : I)
    (j : OuterColumn q₁ q₂ s Y) (ξ₀ : Tail s Y) :
    sourcePosition activity i (forgetTag ξ₀ (.diagonal j)) =
      (activity i j.1).elim (Fin.last s) Fin.castSucc := by
  cases h : activity i j.1 <;> simp [sourcePosition, forgetTag, h]

/-- The reference restriction is literally the full raw transpose. -/
theorem reference_eq_transpose [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    (fun Z k => N (q₁ := q₁) R activity ξ₀ (.unrestricted Z) k) =
      fun Z k => raw R activity k Z := rfl

/-- The two final interlaces in the actual successor, without lower-bound
or profile assumptions. Their widths are public construction parameters. -/
def successor [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) (w Q : ℕ) :
    (Fin Q → Fin w × TaggedColumn q₁ q₂ s Y) →
      (Fin Q × (Fin w → RawRow q₁ q₂ s X I)) → Bool :=
  let W := fun z a => fullInterlace (N R activity ξ₀) w a z
  fun z a => fullInterlace W Q a z

end Paper2.SourceMatrix
