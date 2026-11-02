import CurrentAdditive.V39RecursiveTable
import Paper2.RequestSelectActual

/-! Current two-tag labels in the existing physical parser's layout.
The old fixed-tail constructor is never produced by these maps.  Redundant
tag bits are representation only: the semantic carrier is still the exact
v39 carrier.  The physical result below selects stored labels; it does not
implement the later current edge-activity calculation. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39PhysicalSelect

open Paper2 Paper2.SourceMatrix Paper2.RecursiveLabelCodecScratch
open CurrentAdditive.V39RecursiveGenerator
open CurrentAdditive.V39RecursiveTable
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource

variable {n p₀ q₁ q₂ s w Q : ℕ}

def outerMap {A B : Type} (f : A → B) (j : OuterColumn q₁ q₂ s A) :
    OuterColumn q₁ q₂ s B := (j.1, fun p => f (j.2 p))

def rawColumnMap {A B : Type} (f : A → B) (Z : RawColumn q₁ q₂ s A) :
    RawColumn q₁ q₂ s B := (fun p => f (Z.1 p), fun p => outerMap f (Z.2 p))

def tagMap {A B : Type} (f : A → B) : V38Matrix.TaggedColumn q₁ q₂ s A →
    Paper2.SourceMatrix.TaggedColumn q₁ q₂ s B
  | .inl Z => .unrestricted (rawColumnMap f Z)
  | .inr j => .diagonal (outerMap f j)

def rawRowMap {A B I : Type} (f : A → B) : RawRow q₁ q₂ s A I → RawRow q₁ q₂ s B I
  | .inl (p, z) => .inl (p, fun a => ((z a).1, f (z a).2))
  | .inr (i, u) => .inr (i, f u)

abbrev OldRow (n p₀ q₁ q₂ s w Q k : ℕ) :=
  Paper2.RecursiveEntries.Row (Fin p₀ → Bool) (Fin p₀)
    (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k
abbrev OldColumn (n p₀ q₁ q₂ s w Q k : ℕ) :=
  Paper2.RecursiveEntries.Column (Fin p₀ → Bool) (Fin p₀)
    (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k

/-- A structural injection, with no carrier enumeration or extra label. -/
def embedding (n p₀ q₁ q₂ s w Q : ℕ) : (k : ℕ) →
    (Row n p₀ q₁ q₂ s w Q k → OldRow n p₀ q₁ q₂ s w Q k) ×
      (Column n p₀ q₁ q₂ s w Q k → OldColumn n p₀ q₁ q₂ s w Q k)
  | 0 => (id, id)
  | k + 1 =>
    let e := embedding n p₀ q₁ q₂ s w Q k
    ((fun x t => ((x t).1, tagMap e.2 (x t).2)),
      fun y => (y.1, fun i => rawRowMap e.1 (y.2 i)))

theorem outerMap_injective {A B : Type} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (outerMap (q₁ := q₁) (q₂ := q₂) (s := s) f) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun p : OuterColumn q₁ q₂ s B => p.1) h
  · funext p
    exact hf (congrFun (congrArg Prod.snd h) p)

theorem rawColumnMap_injective {A B : Type} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (rawColumnMap (q₁ := q₁) (q₂ := q₂) (s := s) f) := by
  intro x y h
  apply Prod.ext
  · funext p; exact hf (congrFun (congrArg Prod.fst h) p)
  · funext p; exact outerMap_injective f hf (congrFun (congrArg Prod.snd h) p)

theorem tagMap_injective {A B : Type} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (tagMap (q₁ := q₁) (q₂ := q₂) (s := s) f) := by
  intro x y h
  cases x with
  | inl x => cases y with
    | inl y => exact congrArg Sum.inl (rawColumnMap_injective f hf (SourceMatrix.TaggedColumn.unrestricted.inj h))
    | inr y => cases h
  | inr x => cases y with
    | inl y => cases h
    | inr y => exact congrArg Sum.inr (outerMap_injective f hf (SourceMatrix.TaggedColumn.diagonal.inj h))

theorem rawRowMap_injective {A B I : Type} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (rawRowMap (q₁ := q₁) (q₂ := q₂) (s := s) (I := I) f) := by
  intro x y h
  cases x with
  | inl x => cases y with
    | inl y =>
      apply congrArg Sum.inl
      have he := Sum.inl.inj h
      apply Prod.ext
      · exact congrArg (fun p : Fin s × Template q₁ q₂ B => p.1) he
      · funext a
        have hp := congrFun (congrArg Prod.snd he) a
        apply Prod.ext
        · exact congrArg (fun p : InnerRow q₁ B => p.1) hp
        · exact hf (congrArg Prod.snd hp)
    | inr y => cases h
  | inr x => cases y with
    | inl y => cases h
    | inr y =>
      have he := Sum.inr.inj h
      apply congrArg Sum.inr
      apply Prod.ext
      · exact congrArg (fun p : I × B => p.1) he
      · exact hf (congrArg Prod.snd he)

theorem embedding_injective (n p₀ q₁ q₂ s w Q k : ℕ) :
    Function.Injective (embedding n p₀ q₁ q₂ s w Q k).1 ∧
      Function.Injective (embedding n p₀ q₁ q₂ s w Q k).2 := by
  induction k with
  | zero => exact ⟨Function.injective_id, Function.injective_id⟩
  | succ k ih =>
    constructor
    · intro x y h
      funext t
      have he := congrFun h t
      apply Prod.ext
      · exact congrArg (fun z : Fin w × SourceMatrix.TaggedColumn q₁ q₂ s
          (OldColumn n p₀ q₁ q₂ s w Q k) => z.1) he
      · exact tagMap_injective _ ih.2 (congrArg Prod.snd he)
    · intro x y h
      apply Prod.ext
      · exact congrArg (fun z : OldColumn n p₀ q₁ q₂ s w Q (k + 1) => z.1) h
      · funext i
        exact rawRowMap_injective _ ih.1 (congrFun (congrArg Prod.snd h) i)

theorem tagMap_no_fixedTail {A B : Type} (f : A → B)
    (Z : V38Matrix.TaggedColumn q₁ q₂ s A)
    (js : Fin s → OuterColumn q₁ q₂ s B) : tagMap f Z ≠ .fixedTail js := by
  cases Z <;> intro h <;> cases h

theorem forgetTag_map {A B : Type} (f : A → B) (ξ : Tail s B)
    (Z : V38Matrix.TaggedColumn q₁ q₂ s A) :
    Paper2.SourceMatrix.forgetTag ξ (tagMap f Z) = rawColumnMap f (eraseTag Z) := by
  cases Z <;> rfl

theorem baseRequest_map [NeZero s] {A B C D I : Type} (f : A → B) (g : C → D)
    (activity : I → Fin q₂ → Option (Fin s))
    (k : RawRow q₁ q₂ s A I) (Z : RawColumn q₁ q₂ s C) :
    baseRequest activity (rawRowMap f k) (rawColumnMap g Z) =
      (f (baseRequest activity k Z).1, g (baseRequest activity k Z).2) := by
  cases k <;> rfl

theorem request_embedding [NeZero s]
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Paper2.RecursiveEntries.Tails (Fin p₀ → Bool) (Fin p₀)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q (k + 1))
    (y : Column n p₀ q₁ q₂ s w Q (k + 1)) :
    Paper2.RecursiveEntries.request activity ξ k
      ((embedding n p₀ q₁ q₂ s w Q (k + 1)).1 x)
      ((embedding n p₀ q₁ q₂ s w Q (k + 1)).2 y) =
      ((embedding n p₀ q₁ q₂ s w Q k).1 (request activity k x y).1,
        (embedding n p₀ q₁ q₂ s w Q k).2 (request activity k x y).2) := by
  change baseRequest activity (rawRowMap _ _) (Paper2.SourceMatrix.forgetTag _ (tagMap _ _)) = _
  rw [forgetTag_map, baseRequest_map]
  rfl

theorem seedRequest_embedding [NeZero s]
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Paper2.RecursiveEntries.Tails (Fin p₀ → Bool) (Fin p₀)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q k)
    (y : Column n p₀ q₁ q₂ s w Q k) :
    Paper2.RecursiveEntries.seedRequest activity ξ k
      ((embedding n p₀ q₁ q₂ s w Q k).1 x)
      ((embedding n p₀ q₁ q₂ s w Q k).2 y) = seedRequest activity k x y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Paper2.RecursiveEntries.seedRequest activity ξ k
      (Paper2.RecursiveEntries.request activity ξ k _ _).1
      (Paper2.RecursiveEntries.request activity ξ k _ _).2 = _
    rw [request_embedding]
    exact ih (request activity k x y).1 (request activity k x y).2

/-- Physical parser-compatible bytes.  These are distinct from the minimal
semantic codec in V39RecursiveTable; no equality of those layouts is claimed. -/
def rowWord (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q k) : List Bool :=
  (defaultCarrierCodecs n p₀ s q₁ q₂ w Q k).1.encode
    ((embedding n p₀ q₁ q₂ s w Q k).1 x)
def columnWord (k : ℕ) (y : Column n p₀ q₁ q₂ s w Q k) : List Bool :=
  (defaultCarrierCodecs n p₀ s q₁ q₂ w Q k).2.encode
    ((embedding n p₀ q₁ q₂ s w Q k).2 y)

theorem decode_rowWord (k : ℕ) (x : Row n p₀ q₁ q₂ s w Q k) (suffix : List Bool) :
    (defaultCarrierCodecs n p₀ s q₁ q₂ w Q k).1.decode (rowWord k x ++ suffix) =
      some ((embedding n p₀ q₁ q₂ s w Q k).1 x, suffix) :=
  (defaultCarrierCodecs n p₀ s q₁ q₂ w Q k).1.roundtrip _ suffix

theorem decode_columnWord (k : ℕ) (y : Column n p₀ q₁ q₂ s w Q k) (suffix : List Bool) :
    (defaultCarrierCodecs n p₀ s q₁ q₂ w Q k).2.decode (columnWord k y ++ suffix) =
      some ((embedding n p₀ q₁ q₂ s w Q k).2 y, suffix) :=
  (defaultCarrierCodecs n p₀ s q₁ q₂ w Q k).2.roundtrip _ suffix

theorem codec_encode_injective {A : Type} (c : PrefixCodec A) : Function.Injective c.encode := by
  intro x y h
  have he := c.roundtrip x []
  rw [h, c.roundtrip] at he
  exact (congrArg Prod.fst (Option.some.inj he)).symm

theorem rowWord_injective (n p₀ q₁ q₂ s w Q k : ℕ) :
    Function.Injective (rowWord (n := n) (p₀ := p₀) (q₁ := q₁)
      (q₂ := q₂) (s := s) (w := w) (Q := Q) k) :=
  (codec_encode_injective _).comp (embedding_injective n p₀ q₁ q₂ s w Q k).1

theorem columnWord_injective (n p₀ q₁ q₂ s w Q k : ℕ) :
    Function.Injective (columnWord (n := n) (p₀ := p₀) (q₁ := q₁)
      (q₂ := q₂) (s := s) (w := w) (Q := Q) k) :=
  (codec_encode_injective _).comp (embedding_injective n p₀ q₁ q₂ s w Q k).2

/-- Instantiate the existing fixed parser on the current labels. All fields
of the starting and halting banks are literal words, and the bound counts
the actual transition sequence. No activity or promise assumption occurs. -/
theorem physical_select [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p₀) (hs : 4 ≤ s) (k : ℕ)
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
    ∃ t ≤ Paper2.RequestSelect.clock (columnWord (k + 1) y)
        y.1.val (x y.1).1.val E G cs rs, ∃ v,
      ((advance Paper2.RequestSelect.program)^[t])
        (⟨some Paper2.RequestSelect.startLabel, Paper2.RequestSelect.startControl,
          Paper2.RequestSelect.mk [] []
            (Paper2.RequestSelect.vec (rowWord (k + 1) x) (columnWord (k + 1) y)
              (encodeCode E) (encodeCode G) [] [] [])⟩ :
          Turing.TM2.Cfg (fun _ : Paper2.RequestSelect.Stack => Bool) _ _) =
        ⟨none, v,
          Paper2.RequestSelect.mk
            ((taggedColumnCodec q₁ q₂ s C.2).encode
              (tagMap (embedding n p₀ q₁ q₂ s w Q k).2 (x y.1).2))
            (rrow.encode (rawRowMap (embedding n p₀ q₁ q₂ s w Q k).1 (y.2 (x y.1).1)))
            (Paper2.RequestSelect.vec (rowWord (k + 1) x) (columnWord (k + 1) y)
              (encodeCode E) (encodeCode G) (List.replicate y.1.val true)
              ((piCodec rrow w).encode ty.2) (List.replicate (x y.1).1.val true))⟩ := by
  exact Paper2.RequestSelectActual.select_run hp hs k
    ((embedding n p₀ q₁ q₂ s w Q (k + 1)).1 x)
    ((embedding n p₀ q₁ q₂ s w Q (k + 1)).2 y)

#print axioms embedding_injective
#print axioms tagMap_no_fixedTail
#print axioms request_embedding
#print axioms seedRequest_embedding
#print axioms decode_rowWord
#print axioms decode_columnWord
#print axioms rowWord_injective
#print axioms columnWord_injective
#print axioms physical_select

end CurrentAdditive.V39PhysicalSelect
