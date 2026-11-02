import Paper2.AModelTape
import Paper2.RecursiveSamplingTape
import Paper2.TotalFiniteConstructor
import Paper2.AEndpointDA1

/-!
# Paper A (lock v12), lane `owner:a-model-1`, segment 4b: the reduction's tape law is the uniform law

Author decision D-A1 (27 September 2026, `AUTHOR_DECISIONS_2026-09-27.md`, option (c)): "the tape
is uniform over a fixed polynomial length R(|input|), and the machine reads a prefix." BRIEF
section 2, D-A1 (c): "Needs the tape-law bridge `uniformTape` pushforward = `tapeListLaw` /
`serializedTapeLaw`. The weights are `(1/2)^r` on both sides."

Lock v12 `sections/01-introduction.tex:90-91` ("Time, random-bit count, and output length are
polynomial in the encoding length of $\Phi$ on every tape") and `06-reduction.tex` T23
(`thm:uniform-reduction`, "number of random bits ... on every tape").

Results (admitted objects reused by exact name, never edited):
* `serializedTapeLaw_prob_uniform`: the admitted `RecursiveSamplingTape.serializedTapeLaw B R N`,
  read through its literal bit list, is `uniformTape (bitCount B R N)` read through `List.ofFn`;
  `tapeListLaw_prob_uniform` is the same for `RecursiveSamplingMaterialization.tapeListLaw`.
* `prob_of_uniformExact`: any law satisfying the admitted D-A1 predicate `AEndpoint.uniformExact`
  is `uniformTape r` on its words, `r` its exact word length.
* `experiment_uniformExact` / `experiment_prob_uniform`: for EVERY public-schedule input (not
  only T10 graphs), the actual law of `TotalFiniteConstructorScratch.experiment` (scheduled branch:
  `tapeListLaw`; fallback: the point mass on `[]`) is the uniform law on its exact tape length; the
  admitted `AEndpoint.DA1_uniformExact` is the T10 instance of the first.
* `experiment_prob_prefix`: the same experiment is the law of the length-`r` PREFIX of a uniform
  tape of any length `R ≥ r` (D-A1 (c): the reduction reads a prefix of the composed tape).

No ledger row is closed.
-/

namespace Paper2.AModel

open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions

/-- The literal bit list of `(vectorEquivFin).symm t` is `List.ofFn t`. -/
theorem vector_symm_val {n : ℕ} (t : Fin n → Bool) :
    ((Equiv.vectorEquivFin Bool n).symm t).val = List.ofFn t :=
  List.Vector.toList_ofFn t

/-- **Bridge: `serializedTapeLaw` is the uniform law on its exact length** (weights `(1/2)^r` on
both sides), for every event of the literal tape word. -/
theorem serializedTapeLaw_prob_uniform (B R N : ℕ) (F : List Bool → Prop) :
    (RecursiveSamplingTape.serializedTapeLaw B R N).prob (fun b => F b.val) =
      (uniformTape (RecursiveSamplingTape.bitCount B R N)).prob (fun t => F (List.ofFn t)) := by
  symm
  have h := prob_equiv (uniformTape (RecursiveSamplingTape.bitCount B R N))
    (RecursiveSamplingTape.serializedTapeLaw B R N)
    (Equiv.vectorEquivFin Bool (RecursiveSamplingTape.bitCount B R N)).symm
    (fun _ => rfl) (fun b => F b.val)
  rw [← h]
  congr 1
  funext t
  exact congrArg F (vector_symm_val t).symm

/-- The same bridge for the admitted `RecursiveSamplingMaterialization.tapeListLaw` (definitionally
a `serializedTapeLaw`). -/
theorem tapeListLaw_prob_uniform (V : Type) [Fintype V] (s q₁ q₂ w Q p k mX mY : ℕ)
    (F : List Bool → Prop) :
    (RecursiveSamplingMaterialization.tapeListLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun b => F b.val) =
      (uniformTape (RecursiveSamplingMaterialization.inputBitCount V s q₁ q₂ w Q p k mX mY)).prob
        (fun t => F (List.ofFn t)) :=
  serializedTapeLaw_prob_uniform _ _ _ F

/-- **A law satisfying the admitted D-A1 predicate `AEndpoint.uniformExact` is the uniform law
on its exact word length**, for every event of the word. -/
theorem prob_of_uniformExact {τ : Type} [inst : Fintype τ] (μ : FiniteLaw τ)
    (bits : τ → List Bool) (h : AEndpoint.uniformExact τ inst μ bits) :
    ∃ r : ℕ, (∀ t, (bits t).length = r) ∧ ∀ F : List Bool → Prop,
      μ.prob (fun t => F (bits t)) = (uniformTape r).prob (fun s => F (List.ofFn s)) := by
  obtain ⟨r, hlen, hinj, hsurj, hw⟩ := h
  refine ⟨r, hlen, fun F => ?_⟩
  let f : τ → List.Vector Bool r := fun t => ⟨bits t, hlen t⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun v => ?_⟩
    obtain ⟨t, ht⟩ := hsurj v.val v.property
    exact ⟨t, Subtype.ext ht⟩
  let e : τ ≃ (Fin r → Bool) := (Equiv.ofBijective f hbij).trans (Equiv.vectorEquivFin Bool r)
  have he : ∀ t, List.ofFn (e t) = bits t := by
    intro t
    have h1 : (Equiv.vectorEquivFin Bool r).symm (e t) = f t := by
      simp [e]
    have h2 := vector_symm_val (e t)
    rw [h1] at h2
    exact h2.symm
  have hmain := prob_equiv μ (uniformTape r) e (fun t => (hw t).symm)
    (fun s => F (List.ofFn s))
  rw [← hmain]
  congr 1
  funext t
  rw [he]

/-- The actual experiment law of the public-schedule constructor satisfies `uniformExact`, for
every input of the constructor (general form of the admitted `AEndpoint.DA1_uniformExact`). -/
theorem experiment_uniformExact {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) :
    AEndpoint.uniformExact (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.Tape
      (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeFintype
      (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeLaw
      (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.tapeBits := by
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · rw [TotalFiniteConstructorScratch.experiment_good _ _ _ _ _ hc]
    unfold AEndpoint.uniformExact
    exact ⟨_, fun t => t.property, Subtype.val_injective, fun w hw => ⟨⟨w, hw⟩, rfl⟩,
      fun _ => rfl⟩
  · rw [TotalFiniteConstructorScratch.experiment_bad _ _ _ _ _ hc]
    unfold AEndpoint.uniformExact
    refine ⟨0, fun _ => rfl, fun _ _ _ => rfl, fun w hw => ⟨(), ?_⟩, fun _ => ?_⟩
    · exact (List.eq_nil_of_length_eq_zero hw).symm
    · show (1 : ℝ) = (1 / 2 : ℝ) ^ 0
      simp

/-- **Bridge for the reduction's own tape law**: the actual experiment law (`select` /
`tapeListLaw` / `serializedTapeLaw`, or the fallback point mass) is `uniformTape r` on its exact
tape length `r`, for every event of the tape word. -/
theorem experiment_prob_uniform {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) :
    ∃ r : ℕ,
      (∀ t, ((TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.tapeBits t).length = r) ∧
      ∀ F : List Bool → Prop,
        @FiniteLaw.prob _ (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeFintype
            (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeLaw
            (fun t => F ((TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.tapeBits t)) =
          (uniformTape r).prob (fun s => F (List.ofFn s)) :=
  @prob_of_uniformExact _ (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeFintype _ _
    (experiment_uniformExact hn edge Δ γ k)

/-- **The reduction reads a prefix** (D-A1 (c)): the actual experiment law is the law of the
length-`r` prefix of a uniform tape of ANY length `R ≥ r`. -/
theorem experiment_prob_prefix {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) :
    ∃ r : ℕ,
      (∀ t, ((TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.tapeBits t).length = r) ∧
      ∀ R : ℕ, r ≤ R → ∀ F : List Bool → Prop,
        @FiniteLaw.prob _ (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeFintype
            (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeLaw
            (fun t => F ((TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.tapeBits t)) =
          (uniformTape R).prob (fun s => F ((List.ofFn s).take r)) := by
  obtain ⟨r, hlen, hF⟩ := experiment_prob_uniform hn edge Δ γ k
  exact ⟨r, hlen, fun R hR F => by rw [hF F, uniformTape_take_prob hR F]⟩

end Paper2.AModel

#print axioms Paper2.AModel.serializedTapeLaw_prob_uniform
#print axioms Paper2.AModel.tapeListLaw_prob_uniform
#print axioms Paper2.AModel.prob_of_uniformExact
#print axioms Paper2.AModel.experiment_uniformExact
#print axioms Paper2.AModel.experiment_prob_uniform
#print axioms Paper2.AModel.experiment_prob_prefix
