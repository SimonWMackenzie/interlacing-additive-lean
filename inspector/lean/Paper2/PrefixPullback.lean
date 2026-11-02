import NPCC.Control

/-!
# Live protocol prefixes under input duplication

Source: Paper 2, frozen `2026-09-22-protocol-labels-v12`, Appendix A,
`cl:rational-laws` applied to the protocol conclusion of `cl:separation`.

Precomposing every local message with an input map preserves the actual
transcript. More importantly, the live Alice-prefix property on any finite
rectangle is equivalent to that on its image rectangle. No injectivity or
ambient surjectivity is needed: repeated input labels and empty rectangles
are both allowed. The surjective full-carrier case is a corollary, not an
assumed duplication interface.
-/

namespace Paper2.PrefixPullback

open Workspace.Types.Protocol

variable {X Y A B Z : Type*}

/-- A message depending only on the image input partitions exactly the image
of the corresponding retained row groups. -/
theorem image_filter_precompose [DecidableEq X] (f : A → X)
    (R : Finset A) (p : X → Prop) [DecidablePred p] :
    (R.filter (fun a => p (f a))).image f = (R.image f).filter p := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hp⟩
  · rintro ⟨⟨a, ha, rfl⟩, hp⟩
    exact ⟨a, ⟨ha, hp⟩, rfl⟩

/-- Pullback preserves and reflects the first `k` Alice bits on live paths.
The original rectangle is the actual image of the new rectangle. -/
theorem firstKRowBitsOn_pullback_iff_image [DecidableEq X] [DecidableEq Y]
    (f : A → X) (g : B → Y) (R : Finset A) (C : Finset B)
    (k : ℕ) (P : Protocol X Y Z) :
    NPCC.Protocol.FirstKRowBitsOn R C k (NPCC.Protocol.pullback f g P) ↔
      NPCC.Protocol.FirstKRowBitsOn (R.image f) (C.image g) k P := by
  classical
  induction k generalizing R C P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => simp [NPCC.Protocol.pullback, NPCC.Protocol.FirstKRowBitsOn]
      | bNode b l r => simp [NPCC.Protocol.pullback, NPCC.Protocol.FirstKRowBitsOn]
      | aNode a l r =>
          simp only [NPCC.Protocol.pullback, NPCC.Protocol.FirstKRowBitsOn]
          rw [ih, ih]
          have hfalse :
              (R.filter (fun x => a (f x) = false)).image f =
                (R.image f).filter (fun x => a x = false) :=
            image_filter_precompose f R (fun x : X => a x = false)
          have htrue :
              (R.filter (fun x => a (f x) = true)).image f =
                (R.image f).filter (fun x => a x = true) :=
            image_filter_precompose f R (fun x : X => a x = true)
          rw [hfalse, htrue]

/-- A convenient interface when the image rectangles have already been
identified by exact surjectivity onto retained sets. -/
theorem firstKRowBitsOn_pullback_iff_of_image_eq
    [DecidableEq X] [DecidableEq Y]
    (f : A → X) (g : B → Y) (R : Finset A) (C : Finset B)
    (S : Finset X) (T : Finset Y)
    (hR : R.image f = S) (hC : C.image g = T)
    (k : ℕ) (P : Protocol X Y Z) :
    NPCC.Protocol.FirstKRowBitsOn R C k (NPCC.Protocol.pullback f g P) ↔
      NPCC.Protocol.FirstKRowBitsOn S T k P := by
  rw [firstKRowBitsOn_pullback_iff_image, hR, hC]

/-- Duplicating every original input reflects as well as preserves the live
prefix property on the full input space. -/
theorem firstKRowBitsOn_pullback_iff_of_surjective
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (f : A → X) (g : B → Y)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (k : ℕ) (P : Protocol X Y Z) :
    NPCC.Protocol.FirstKRowBitsOn Finset.univ Finset.univ k
        (NPCC.Protocol.pullback f g P) ↔
      NPCC.Protocol.FirstKRowBitsOn Finset.univ Finset.univ k P := by
  classical
  rw [firstKRowBitsOn_pullback_iff_image]
  rw [Finset.image_univ_of_surjective hf, Finset.image_univ_of_surjective hg]

/-- Input maps preserve the row-prefix code, including its explicit junk
value when a leaf or Bob node appears too early. -/
theorem prefixCodeRaw_pullback (f : A → X) (g : B → Y)
    (k : ℕ) (P : Protocol X Y Z) (a : A) :
    NPCC.Protocol.prefixCodeRaw k (NPCC.Protocol.pullback f g P) a =
      NPCC.Protocol.prefixCodeRaw k P (f a) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => rfl
      | bNode b l r => rfl
      | aNode q l r =>
          cases h : q (f a) <;>
            simp [NPCC.Protocol.pullback, NPCC.Protocol.prefixCodeRaw, h, ih]

/-- Actual transcripts are preserved even when both players speak. -/
theorem actualPrefixCodeRaw_pullback (f : A → X) (g : B → Y)
    (k : ℕ) (P : Protocol X Y Z) (a : A) (b : B) :
    NPCC.Protocol.actualPrefixCodeRaw k (NPCC.Protocol.pullback f g P) a b =
      NPCC.Protocol.actualPrefixCodeRaw k P (f a) (g b) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => rfl
      | aNode q l r =>
          cases h : q (f a) <;>
            simp [NPCC.Protocol.pullback, NPCC.Protocol.actualPrefixCodeRaw, h, ih]
      | bNode q l r =>
          cases h : q (g b) <;>
            simp [NPCC.Protocol.pullback, NPCC.Protocol.actualPrefixCodeRaw, h, ih]

/-- The actual speaker trace is unchanged, not merely the bit string. -/
theorem actualSideListRaw_pullback (f : A → X) (g : B → Y)
    (k : ℕ) (P : Protocol X Y Z) (a : A) (b : B) :
    NPCC.Protocol.actualSideListRaw k (NPCC.Protocol.pullback f g P) a b =
      NPCC.Protocol.actualSideListRaw k P (f a) (g b) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P with
      | leaf z => rfl
      | aNode q l r =>
          cases h : q (f a) <;>
            simp [NPCC.Protocol.pullback, NPCC.Protocol.actualSideListRaw, h, ih]
      | bNode q l r =>
          cases h : q (g b) <;>
            simp [NPCC.Protocol.pullback, NPCC.Protocol.actualSideListRaw, h, ih]

/-- The number of bits sent on each actual execution is unchanged. -/
theorem evalDepth_pullback (f : A → X) (g : B → Y)
    (P : Protocol X Y Z) (a : A) (b : B) :
    NPCC.Protocol.evalDepth (NPCC.Protocol.pullback f g P) a b =
      NPCC.Protocol.evalDepth P (f a) (g b) := by
  induction P with
  | leaf z => rfl
  | aNode q l r ihl ihr =>
      simp only [NPCC.Protocol.pullback, NPCC.Protocol.evalDepth, ihl, ihr]
  | bNode q l r ihl ihr =>
      simp only [NPCC.Protocol.pullback, NPCC.Protocol.evalDepth, ihl, ihr]

end Paper2.PrefixPullback
