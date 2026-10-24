import CurrentAdditive.IndexedIncomingFromMass
import CurrentAdditive.DeterministicIndexedTemplates

/-! Appendix I `det:incoming`: every selected protected image value is
realized by an original tagged row in the actual transposed internal matrix. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The exact two tagged constructors that realize a protected `J₂` image
value at one original outer position and template bin. -/
def ProtectedColumnRealizes (p : Fin s) (j : J src) : Column src → Prop
  | .ordinary _ => False
  | .fixedTail js => src.outer.decode js p = j
  | .diagonal j' => j' = j

theorem protectedImage_has_original_column (w : ℕ)
    (R : Set (Fin w × Column src)) (b : Bool) (i : Fin w)
    (p : Fin s) (j : J src)
    (hj : j ∈ protectedImage src w R b i p) :
    ∃ Z : Column src, (i, Z) ∈ R ∧ ProtectedColumnRealizes src p j Z := by
  cases b with
  | true =>
      exact ⟨.diagonal j, by simpa [protectedImage] using hj, rfl⟩
  | false =>
      obtain ⟨js, hjs, hdec⟩ := hj
      exact ⟨.fixedTail js, hjs, hdec⟩

noncomputable def incomingOriginalColumn (w : ℕ)
    (R : Set (Fin w × Column src)) (b : Bool) (i : Fin w)
    (p : Fin s) (j : J src)
    (hj : j ∈ protectedImage src w R b i p) : Column src :=
  Classical.choose (protectedImage_has_original_column src w R b i p j hj)

theorem incomingOriginalColumn_survives (w : ℕ)
    (R : Set (Fin w × Column src)) (b : Bool) (i : Fin w)
    (p : Fin s) (j : J src)
    (hj : j ∈ protectedImage src w R b i p) :
    (i, incomingOriginalColumn src w R b i p j hj) ∈ R :=
  (Classical.choose_spec (protectedImage_has_original_column src w R b i p j hj)).1

theorem incomingOriginalColumn_realizes (w : ℕ)
    (R : Set (Fin w × Column src)) (b : Bool) (i : Fin w)
    (p : Fin s) (j : J src)
    (hj : j ∈ protectedImage src w R b i p) :
    ProtectedColumnRealizes src p j
      (incomingOriginalColumn src w R b i p j hj) :=
  (Classical.choose_spec (protectedImage_has_original_column src w R b i p j hj)).2

/-- On a fixed template flag, both protected tags give exactly the same
`A(γ,z)` entry for the original selector address `(i,α)`. -/
theorem indexed_incoming_entry
    {μI : PositiveRationalLaw I} {w : ℕ}
    (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (md : streams.metadataStream.Label)
    (base : streams.baseStream.Label) (sel : streams.selectorStream.Label)
    (i : Fin w) (p : Fin s)
    (hflag : streams.metadataStream.decode md i = .inl p)
    (j : J src) (Z : Column src)
    (hZ : ProtectedColumnRealizes src p j Z) :
    W src streams R₀ activity ξ₀ (md, (base, sel)) (i, Z) =
      A src R₀ j.2 (src.inner.decode
        (streams.selectorStream.decode sel i) j.1) := by
  cases Z with
  | ordinary Z => cases hZ
  | fixedTail js =>
      dsimp [ProtectedColumnRealizes] at hZ
      simp [W, InternalStreams.decode, hflag, B, decodeRow,
        decodeColumn, SourceMatrix.raw, SourceMatrix.baseRequest,
        A, M₁, SourceMatrix.M₁, innerWord, gammaWord,
        outerWord, hZ]
  | diagonal j' =>
      dsimp [ProtectedColumnRealizes] at hZ
      subst j'
      simp [W, InternalStreams.decode, hflag, B, decodeRow,
        decodeColumn, SourceMatrix.raw, SourceMatrix.baseRequest,
        A, M₁, SourceMatrix.M₁, innerWord, gammaWord,
        outerWord]

#print axioms indexed_incoming_entry

end CurrentAdditive.DeterministicIndexedMatrix.Sources
