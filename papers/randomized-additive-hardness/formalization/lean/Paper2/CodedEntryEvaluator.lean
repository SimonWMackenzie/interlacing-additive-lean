import Paper2.RecursiveLabelCodec
import Paper2.CanonicalDefaultSource

/-! A structural bit-list interface to the actual recursive entry evaluator.
The parser rejects malformed labels and trailing bits. This file does not
claim a machine-model running time or parse external graph bytes. -/

namespace Paper2.CodedEntryEvaluatorScratch

open RecursiveEntries RecursiveLabelCodecScratch SourceProfileParameters

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩

private theorem canonicalWidthPos (L : ℕ) :
    0 < ParameterizedCanonicalSource.restorationWidth L := by
  unfold ParameterizedCanonicalSource.restorationWidth
    RestorationWidthScheduleScratch.width
  positivity

private theorem canonicalCoverPos (n m L Δ : ℕ) (γ : ℚ) :
    0 < ParameterizedCanonicalSource.coverWidth n m L Δ γ := by
  unfold ParameterizedCanonicalSource.coverWidth SourceOverheadBounds.actualQ
    SourceRationalScheduleScratch.publicQ
  exact RestorationPublicQScratch.publicQ_pos _ _

def decodeExact {α : Type} (ca : PrefixCodec α) (bits : List Bool) : Option α := do
  let (x, rest) ← ca.decode bits
  if rest.isEmpty then some x else none

theorem decodeExact_encode {α : Type} (ca : PrefixCodec α) (x : α) :
    decodeExact ca (ca.encode x) = some x := by
  have hr : ca.decode (ca.encode x) = some (x, []) := by
    simpa using ca.roundtrip x []
  simp [decodeExact, hr]

theorem decodeExact_reject_trailing {α : Type} (ca : PrefixCodec α)
    (x : α) (suffix : List Bool) (h : suffix ≠ []) :
    decodeExact ca (ca.encode x ++ suffix) = none := by
  simp [decodeExact, ca.roundtrip, h]

/-- Parsing precedes the existing recursive evaluator; no second source
entry definition is substituted. -/
def codedEntry {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ} [NeZero s]
    (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (ci : PrefixCodec I) (k : ℕ)
    (rowBits columnBits : List Bool) : Option Bool := do
  let codecs := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k
  let x ← decodeExact codecs.1 rowBits
  let y ← decodeExact codecs.2 columnBits
  pure (RecursiveEntries.evaluate F activity ξ k x y)

theorem codedEntry_encoded {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ} [NeZero s]
    (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (ci : PrefixCodec I) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q k)
    (y : Column X₀ Y₀ I s q₁ q₂ w Q k) :
    codedEntry F activity ξ cx₀ cy₀ ci k
      ((carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).1.encode x)
      ((carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).2.encode y) =
        some (RecursiveEntries.matrix F activity ξ k x y) := by
  simp [codedEntry, decodeExact_encode, RecursiveEntries.evaluate_eq_matrix]

theorem codedEntry_encoded_succ {X₀ Y₀ I : Type}
    {s q₁ q₂ w Q : ℕ} [NeZero s]
    (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (ci : PrefixCodec I) (k : ℕ)
    (x : Row X₀ Y₀ I s q₁ q₂ w Q (k + 1))
    (y : Column X₀ Y₀ I s q₁ q₂ w Q (k + 1)) :
    codedEntry F activity ξ cx₀ cy₀ ci (k + 1)
      ((carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci (k + 1)).1.encode x)
      ((carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci (k + 1)).2.encode y) =
        some (RecursiveEntries.matrix F activity ξ k
          (RecursiveEntries.request activity ξ k x y).1
          (RecursiveEntries.request activity ξ k x y).2) := by
  rw [codedEntry_encoded, RecursiveEntries.matrix_succ_entry]

theorem codedEntry_reject_bad_row {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ}
    [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (ci : PrefixCodec I) (k : ℕ) (rowBits columnBits : List Bool)
    (hbad : decodeExact (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).1
      rowBits = none) :
    codedEntry F activity ξ cx₀ cy₀ ci k rowBits columnBits = none := by
  simp [codedEntry, hbad]

theorem codedEntry_reject_bad_column {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ}
    [NeZero s] (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (ci : PrefixCodec I) (k : ℕ) (rowBits columnBits : List Bool)
    (hbad : decodeExact (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).2
      columnBits = none) :
    codedEntry F activity ξ cx₀ cy₀ ci k rowBits columnBits = none := by
  simp [codedEntry, hbad]

/-- Every accepted pair decodes to actual carriers and its answer is the
existing full-product matrix entry on precisely those carriers. -/
theorem codedEntry_sound {X₀ Y₀ I : Type} {s q₁ q₂ w Q : ℕ} [NeZero s]
    (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (ci : PrefixCodec I) (k : ℕ) (rowBits columnBits : List Bool)
    (b : Bool)
    (h : codedEntry F activity ξ cx₀ cy₀ ci k rowBits columnBits = some b) :
    ∃ x y,
      decodeExact (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).1 rowBits = some x ∧
      decodeExact (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).2 columnBits = some y ∧
      b = RecursiveEntries.matrix F activity ξ k x y := by
  unfold codedEntry at h
  cases hr : decodeExact (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).1 rowBits with
  | none => simp [hr] at h
  | some x =>
      cases hc : decodeExact (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).2 columnBits with
      | none => simp [hr, hc] at h
      | some y =>
          simp only [hr, hc, Option.pure_def, Option.bind_eq_bind,
            Option.bind_some] at h
          exact ⟨x, y, rfl, rfl,
            by simpa [RecursiveEntries.evaluate_eq_matrix] using h.symm⟩

/-- The actual public graph widths; the quotient identity is public and
proof-irrelevant, and the graph is supplied as an indexed edge map. -/
def codedCanonicalEntry {n m : ℕ} (L Δ : ℕ) (γ : ℚ)
    (edge : Fin m → Bool → Fin n) (hn : 0 < n)
    (hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) *
        ParameterizedCanonicalSource.rep L m)
    (k : ℕ) (rowBits columnBits : List Bool) : Option Bool := by
  let s := width L
  let q₁ := s - 2
  let q₂ := outerWidth L
  let w := ParameterizedCanonicalSource.restorationWidth L
  let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
  let p := LookupSeed.width L
  letI : NeZero s := ⟨by dsimp [s, width]; positivity⟩
  have hw : 0 < w := canonicalWidthPos L
  have hQ : 0 < Q := canonicalCoverPos n m L Δ γ
  exact codedEntry (LookupSeed.matrix p)
    (SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega) hq)
    (CanonicalDefaultSource.canonicalDefaultTails L n w Q hn hw hQ)
    (piCodec boolCodec p) (finCodec p) (defaultItemCodec n s)
    k rowBits columnBits

theorem codedCanonicalEntry_encoded {n m : ℕ} (L Δ : ℕ) (γ : ℚ)
    (edge : Fin m → Bool → Fin n) (hn : 0 < n)
    (hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) *
        ParameterizedCanonicalSource.rep L m)
    (k : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin n))
      (width L) (width L - 2) (outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k)
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin n))
      (width L) (width L - 2) (outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k) :
    codedCanonicalEntry L Δ γ edge hn hq k
      ((scheduledCarrierCodecs n m L Δ γ k).1.encode x)
      ((scheduledCarrierCodecs n m L Δ γ k).2.encode y) =
    some (RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
      (SourceActiveRank.scanAtCanonical edge
        (by have := SourceProfiles.width_ge_four L; omega) hq)
      (CanonicalDefaultSource.canonicalDefaultTails L n
        (ParameterizedCanonicalSource.restorationWidth L)
        (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
        hn (canonicalWidthPos L) (canonicalCoverPos n m L Δ γ))
      k x y) := by
  let s := width L
  let q₁ := s - 2
  let q₂ := outerWidth L
  let w := ParameterizedCanonicalSource.restorationWidth L
  let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
  let p := LookupSeed.width L
  have hw : 0 < w := canonicalWidthPos L
  have hQ : 0 < Q := canonicalCoverPos n m L Δ γ
  have h := codedEntry_encoded (LookupSeed.matrix p)
    (SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega) hq)
    (CanonicalDefaultSource.canonicalDefaultTails L n w Q hn hw hQ)
    (piCodec boolCodec p) (finCodec p) (defaultItemCodec n s) k x y
  simpa only [codedCanonicalEntry, scheduledCarrierCodecs,
    defaultCarrierCodecs, s, q₁, q₂, w, Q, p] using h

theorem codedCanonicalEntry_reject_bad_row {n m : ℕ} (L Δ : ℕ) (γ : ℚ)
    (edge : Fin m → Bool → Fin n) (hn : 0 < n)
    (hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) *
        ParameterizedCanonicalSource.rep L m)
    (k : ℕ) (rowBits columnBits : List Bool)
    (hbad : decodeExact (scheduledCarrierCodecs n m L Δ γ k).1 rowBits = none) :
    codedCanonicalEntry L Δ γ edge hn hq k rowBits columnBits = none := by
  simp only [scheduledCarrierCodecs, defaultCarrierCodecs] at hbad
  simp only [codedCanonicalEntry, codedEntry, hbad]
  rfl

theorem codedCanonicalEntry_reject_bad_column {n m : ℕ} (L Δ : ℕ) (γ : ℚ)
    (edge : Fin m → Bool → Fin n) (hn : 0 < n)
    (hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) *
        ParameterizedCanonicalSource.rep L m)
    (k : ℕ) (rowBits columnBits : List Bool)
    (hbad : decodeExact (scheduledCarrierCodecs n m L Δ γ k).2 columnBits = none) :
    codedCanonicalEntry L Δ γ edge hn hq k rowBits columnBits = none := by
  simp only [scheduledCarrierCodecs, defaultCarrierCodecs] at hbad
  simp only [codedCanonicalEntry, codedEntry, hbad]
  cases decodeExact
    (carrierCodecs (width L) (width L - 2) (outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
      (piCodec boolCodec (LookupSeed.width L))
      (finCodec (LookupSeed.width L))
      (defaultItemCodec n (width L)) k).1 rowBits <;> rfl

end Paper2.CodedEntryEvaluatorScratch
