import Paper2.SuccessSplit
import Paper2.GeneratorFullSample
import Paper2.CodeSampleOutputDecoder

/-! The successful word as the codec encoding of an actually reachable
sample: `bytes = (ofFn (C.2.encode ∘ ys)).flatten ++ (ofFn (C.1.encode ∘ xs)).flatten`
with `(ys, xs)` produced by the same `samples` program, and each label word
produced by its own code. This is the value-level input of the fetch
theorems (`cs := ofFn (C.2.encode ∘ ys)`, `rs := ofFn (C.1.encode ∘ xs)`). -/

namespace Paper2.SuccessCodec

open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveRequestCodeShape
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling

theorem produces_prod {A B : Type*} (p : Program A) (q : Program B) (a : A) (b : B)
    (h : Produces (prod p q) (a, b)) : Produces p a ∧ Produces q b := by
  unfold prod at h
  obtain ⟨a', ha', hm⟩ := (produces_bind p _).mp h
  obtain ⟨b', hb', he⟩ := (produces_map _ q).mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨ha', hb'⟩

theorem produces_iid {A : Type*} (p : Program A) :
    ∀ (n : Nat) (f : Fin n → A), Produces (iid p n) f → ∀ i, Produces p (f i)
  | 0, _, _, i => i.elim0
  | n + 1, f, h, i => by
      change Produces (Program.bind p (fun a => Program.map (Fin.cons a) (iid p n))) f at h
      obtain ⟨a, ha, hm⟩ := (produces_bind p _).mp h
      obtain ⟨g, hg, rfl⟩ := (produces_map _ _).mp hm
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simpa using produces_iid p n g hg j

theorem tupleWord_eq_flatten {A : Type} (ca : PrefixCodec A) :
    ∀ (n : Nat) (f : Fin n → A),
      CodeSampleOutputDecoder.tupleWord ca n f = (List.ofFn (fun i => ca.encode (f i))).flatten
  | 0, _ => rfl
  | n + 1, f => by
      simp only [CodeSampleOutputDecoder.tupleWord, List.ofFn_succ, List.flatten_cons]
      rw [tupleWord_eq_flatten ca n (Fin.tail f)]
      rfl

theorem success_codec {n p s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s) (k mX mY : ℕ) (bytes : List Bool)
    (h : Produces (meaning (seedSampleCode n p s q₁ q₂ w Q k mX mY)) bytes) :
    ∃ (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k)
      (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k),
      Produces (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) hs
          (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp)
          k mX mY) (ys, xs) ∧
      bytes = (List.ofFn (fun j => (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (ys j))).flatten ++
        (List.ofFn (fun i => (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode (xs i))).flatten ∧
      (∀ j, Produces (meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
        ((defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (ys j))) ∧
      (∀ i, Produces (meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).1)
        ((defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode (xs i))) := by
  rw [seedSampleCode_exact hp hs k mX mY] at h
  obtain ⟨⟨ys, xs⟩, hv, rfl⟩ := (produces_map _ _).mp h
  have hpair := produces_prod _ _ ys xs hv
  obtain ⟨hr, hc⟩ := seedRecursiveCodes_exact (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hp hs k
  refine ⟨ys, xs, hv, ?_, ?_, ?_⟩
  · change (piCodec _ mY).encode ys ++ (piCodec _ mX).encode xs = _
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      CodeSampleOutputDecoder.piCodec_encode_tupleWord,
      tupleWord_eq_flatten, tupleWord_eq_flatten]
    rfl
  · intro j
    rw [hc]
    exact (produces_map _ _).mpr ⟨ys j, produces_iid _ mY ys hpair.1 j, rfl⟩
  · intro i
    rw [hr]
    exact (produces_map _ _).mpr ⟨xs i, produces_iid _ mX xs hpair.2 i, rfl⟩

#print axioms produces_prod
#print axioms produces_iid
#print axioms success_codec

end Paper2.SuccessCodec
