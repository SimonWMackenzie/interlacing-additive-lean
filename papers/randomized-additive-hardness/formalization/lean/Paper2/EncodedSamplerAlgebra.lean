import Paper2.RecursiveSamplingLaws
import Paper2.RecursiveLabelCodec

/-! Exact syntax-level sequencing of actual recursive sampling programs under
the production label codecs. This is stronger than equality of output laws. -/

namespace Paper2.EncodedSamplerAlgebra

open RecursiveSamplingProgram RecursiveSamplingLaws
open RecursiveLabelCodecScratch

namespace Program

variable {A B C : Type}

theorem bind_assoc (p : Program A) (f : A → Program B) (g : B → Program C) :
    Program.bind (Program.bind p f) g =
      Program.bind p (fun a => Program.bind (f a) g) := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [Program.bind_draw]
      congr 1
      funext i
      exact ih i

theorem bind_pure_right (p : Program A) :
    Program.bind p Program.pure = p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [Program.bind_draw]
      congr 1
      funext i
      exact ih i

theorem map_bind (p : Program A) (f : A → Program B) (g : B → C) :
    Program.map g (Program.bind p f) =
      Program.bind p (fun a => Program.map g (f a)) := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [Program.bind_draw, Program.map_draw]
      congr 1
      funext i
      exact ih i

theorem bind_map (p : Program A) (f : A → B) (g : B → Program C) :
    Program.bind (Program.map f p) g =
      Program.bind p (fun a => g (f a)) := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [Program.map_draw, Program.bind_draw]
      congr 1
      funext i
      exact ih i

theorem map_map (p : Program A) (f : A → B) (g : B → C) :
    Program.map g (Program.map f p) = Program.map (g ∘ f) p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [Program.map_draw]
      congr 1
      funext i
      exact ih i

theorem map_id (p : Program A) : Program.map id p = p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [Program.map_draw]
      congr 1
      funext i
      exact ih i

end Program

theorem prodCodec_encode {A B : Type} (ca : PrefixCodec A)
    (cb : PrefixCodec B) (a : A) (b : B) :
    (prodCodec ca cb).encode (a, b) = ca.encode a ++ cb.encode b := rfl

theorem piCodec_encode_cons {A : Type} (ca : PrefixCodec A)
    (n : ℕ) (a : A) (tail : Fin n → A) :
    (piCodec ca (n + 1)).encode (Fin.cons a tail) =
      ca.encode a ++ (piCodec ca n).encode tail := by
  simp [piCodec, transportCodec, prodCodec]

theorem encoded_prod {A B : Type} (ca : PrefixCodec A)
    (cb : PrefixCodec B) (p : Program A) (q : Program B) :
    Program.map (prodCodec ca cb).encode (RecursiveSamplingLaws.prod p q) =
      Program.bind (Program.map ca.encode p)
        (fun xs => Program.map (fun ys => xs ++ ys) (Program.map cb.encode q)) := by
  rw [RecursiveSamplingLaws.prod, Program.map_bind, Program.bind_map]
  congr 1
  funext a
  rw [Program.map_map]
  rw [Program.map_map]
  congr 1

/-- A first-order list-output program that draws one encoded coordinate at a
time and concatenates in the same head-to-tail order as `iid`. -/
def repeatedConcat (p : Program (List Bool)) : (n : ℕ) → Program (List Bool)
  | 0 => .pure []
  | n + 1 => Program.bind p
      (fun xs => Program.map (fun ys => xs ++ ys) (repeatedConcat p n))

theorem encoded_iid {A : Type} (ca : PrefixCodec A)
    (p : Program A) (n : ℕ) :
    Program.map (piCodec ca n).encode (RecursiveSamplingLaws.iid p n) =
      repeatedConcat (Program.map ca.encode p) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [RecursiveSamplingLaws.iid, repeatedConcat,
        Program.map_bind, Program.bind_map]
      congr 1
      funext a
      rw [Program.map_map]
      rw [← ih]
      rw [Program.map_map]
      congr 1

#print axioms Program.bind_assoc
#print axioms Program.bind_pure_right
#print axioms Program.map_bind
#print axioms Program.bind_map
#print axioms Program.map_map
#print axioms Program.map_id
#print axioms prodCodec_encode
#print axioms piCodec_encode_cons
#print axioms encoded_prod
#print axioms encoded_iid

end Paper2.EncodedSamplerAlgebra
