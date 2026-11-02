import CurrentAdditive.V38OneStep

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

namespace CurrentAdditive.V38Resource

open Paper2 Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open CurrentAdditive.V38OneStep

variable {X Y V : Type*} {q₁ q₂ s w Q : ℕ}

theorem alphabet_prod_le {B C : Type*} (p : Program B) (q : Program C) :
    (RecursiveSamplingLaws.prod p q).maxAlphabet ≤
      max p.maxAlphabet q.maxAlphabet := by
  apply Program.maxAlphabet_bind_le
  intro a
  simp only [Program.maxAlphabet_map]
  exact le_rfl

theorem alphabet_iid_le {B : Type*} (p : Program B) (n : ℕ) :
    (RecursiveSamplingLaws.iid p n).maxAlphabet ≤ p.maxAlphabet := by
  induction n with
  | zero => simpa [RecursiveSamplingLaws.iid] using p.maxAlphabet_pos
  | succ n ih =>
      change (Program.bind p (fun a =>
        Program.map (Fin.cons (α := fun _ : Fin (n + 1) => B) a)
          (RecursiveSamplingLaws.iid p n))).maxAlphabet ≤ _
      have h := Program.maxAlphabet_bind_le p
        (fun a => Program.map (Fin.cons (α := fun _ : Fin (n + 1) => B) a)
          (RecursiveSamplingLaws.iid p n))
        p.maxAlphabet (by intro a; simpa using ih)
      simpa using h

theorem alphabet_outer_le [NeZero q₂] (p : Program Y) (A : ℕ)
    (hq₂ : q₂ ≤ A) (hp : p.maxAlphabet ≤ A) :
    (Paper2.RecursiveSampling.outer (q₁ := q₁) (q₂ := q₂) (s := s) p).maxAlphabet ≤ A := by
  exact (alphabet_prod_le _ _).trans (max_le
    (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using hq₂)
    ((alphabet_iid_le p _).trans hp))

theorem alphabet_raw_le [NeZero q₂] (p : Program Y) (A : ℕ)
    (hq₂ : q₂ ≤ A) (hp : p.maxAlphabet ≤ A) :
    (Paper2.RecursiveSampling.raw (q₁ := q₁) (q₂ := q₂) (s := s) p).maxAlphabet ≤ A := by
  exact (alphabet_prod_le _ _).trans (max_le
    ((alphabet_iid_le p _).trans hp)
    ((alphabet_iid_le _ _).trans (alphabet_outer_le p A hq₂ hp)))

theorem alphabet_tagged_le [NeZero q₂] (p : Program Y) (A : ℕ)
    (h256 : 256 ≤ A) (hq₂ : q₂ ≤ A) (hp : p.maxAlphabet ≤ A) :
    (V38OneStep.tagged (q₁ := q₁) (q₂ := q₂) (s := s) p).maxAlphabet ≤ A := by
  change max 256 (Finset.univ.sup (fun t : Fin 256 =>
    (if t.val < 255 then
      Program.map Sum.inl (Paper2.RecursiveSampling.raw
        (q₁ := q₁) (q₂ := q₂) (s := s) p)
    else Program.map Sum.inr (Paper2.RecursiveSampling.outer
        (q₁ := q₁) (q₂ := q₂) (s := s) p)).maxAlphabet)) ≤ A
  apply max_le h256
  apply Finset.sup_le
  intro t ht
  split_ifs <;> rw [Program.maxAlphabet_map]
  · exact alphabet_raw_le p A hq₂ hp
  · exact alphabet_outer_le p A hq₂ hp

theorem alphabet_templateRow_le [NeZero q₁] [NeZero s]
    (p : Program X) (A : ℕ) (hs : s ≤ A) (hq₁ : q₁ ≤ A)
    (hp : p.maxAlphabet ≤ A) :
    (Paper2.RecursiveSampling.templateRow (q₁ := q₁) (q₂ := q₂)
      (s := s) p).maxAlphabet ≤ A := by
  apply (alphabet_prod_le _ _).trans
  apply max_le
  · simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using hs
  · apply (alphabet_iid_le _ _).trans
    exact (alphabet_prod_le _ _).trans (max_le
      (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using hq₁) hp)

theorem alphabet_vertexItems_le [NeZero (4 * s)]
    (p : Program V) (A : ℕ) (h4s : 4 * s ≤ A)
    (hp : p.maxAlphabet ≤ A) :
    (V38OneStep.vertexItems (s := s) p).maxAlphabet ≤ A :=
  (alphabet_prod_le _ _).trans (max_le
    (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using h4s) hp)

theorem alphabet_auxiliaryItems_le [NeZero (4 * s)] [NeZero (s - 3)]
    (A : ℕ) (h4s : 4 * s ≤ A) (hs3 : s - 3 ≤ A) :
    (V38OneStep.auxiliaryItems (s := s)).maxAlphabet ≤ A :=
  (alphabet_prod_le _ _).trans (max_le
    (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using h4s)
    (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using hs3))

theorem alphabet_rawRows_le [NeZero q₁] [NeZero s]
    [NeZero (4 * s)] [NeZero (s - 3)]
    (pV : Program V) (pX : Program X) (A : ℕ)
    (h512 : 512 ≤ A) (hs : s ≤ A) (hq₁ : q₁ ≤ A)
    (h4s : 4 * s ≤ A) (hs3 : s - 3 ≤ A)
    (hV : pV.maxAlphabet ≤ A) (hX : pX.maxAlphabet ≤ A) :
    (V38OneStep.rawRows (q₁ := q₁) (q₂ := q₂) (s := s) pV pX).maxAlphabet ≤ A := by
  rw [V38OneStep.rawRows, Program.maxAlphabet_map]
  change max 512 (Finset.univ.sup (fun t : Fin 512 =>
    (if t.val < 510 then
      Program.map Sum.inl (Paper2.RecursiveSampling.templateRow pX)
     else if t.val = 510 then
      Program.map (fun k => Sum.inr (Sum.inl k.1, k.2))
        (Paper2.RecursiveSampling.itemRow (V38OneStep.vertexItems pV) pX)
     else Program.map (fun k => Sum.inr (Sum.inr k.1, k.2))
        (Paper2.RecursiveSampling.itemRow V38OneStep.auxiliaryItems pX)).maxAlphabet)) ≤ A
  apply max_le h512
  apply Finset.sup_le
  intro t ht
  split_ifs <;> rw [Program.maxAlphabet_map]
  · exact alphabet_templateRow_le pX A hs hq₁ hX
  · exact (alphabet_prod_le _ _).trans
      (max_le (alphabet_vertexItems_le pV A h4s hV) hX)
  · exact (alphabet_prod_le _ _).trans
      (max_le (alphabet_auxiliaryItems_le A h4s hs3) hX)

theorem alphabet_successorRow_le [NeZero q₂] [NeZero w]
    (pY : Program Y) (A : ℕ)
    (h256 : 256 ≤ A) (hq₂ : q₂ ≤ A) (hw : w ≤ A)
    (hY : pY.maxAlphabet ≤ A) :
    (V38OneStep.successorRow (q₁ := q₁) (q₂ := q₂)
      (s := s) (w := w) (Q := Q) pY).maxAlphabet ≤ A := by
  apply (alphabet_iid_le _ _).trans
  exact (alphabet_prod_le _ _).trans (max_le
    (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using hw)
    (alphabet_tagged_le pY A h256 hq₂ hY))

theorem alphabet_successorColumn_le [NeZero q₁] [NeZero s]
    [NeZero (4 * s)] [NeZero (s - 3)] [NeZero Q]
    (pV : Program V) (pX : Program X) (A : ℕ)
    (h512 : 512 ≤ A) (hs : s ≤ A) (hq₁ : q₁ ≤ A)
    (h4s : 4 * s ≤ A) (hs3 : s - 3 ≤ A) (hQ : Q ≤ A)
    (hV : pV.maxAlphabet ≤ A) (hX : pX.maxAlphabet ≤ A) :
    (V38OneStep.successorColumn (q₁ := q₁) (q₂ := q₂)
      (s := s) (w := w) (Q := Q) pV pX).maxAlphabet ≤ A := by
  exact (alphabet_prod_le _ _).trans (max_le
    (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using hQ)
    ((alphabet_iid_le _ _).trans
      (alphabet_rawRows_le pV pX A h512 hs hq₁ h4s hs3 hV hX)))

theorem alphabet_fullSample_le [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)]
    [NeZero w] [NeZero Q]
    (m : ℕ) (pV : Program V) (pX : Program X) (pY : Program Y)
    (A : ℕ) (h512 : 512 ≤ A) (hs : s ≤ A)
    (hq₁ : q₁ ≤ A) (hq₂ : q₂ ≤ A)
    (h4s : 4 * s ≤ A) (hs3 : s - 3 ≤ A)
    (hw : w ≤ A) (hQ : Q ≤ A)
    (hV : pV.maxAlphabet ≤ A)
    (hX : pX.maxAlphabet ≤ A) (hY : pY.maxAlphabet ≤ A) :
    (V38OneStep.fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY).maxAlphabet ≤ A := by
  exact (alphabet_prod_le _ _).trans (max_le
    ((alphabet_iid_le _ _).trans
      (alphabet_successorRow_le pY A (by omega) hq₂ hw hY))
    ((alphabet_iid_le _ _).trans
      (alphabet_successorColumn_le pV pX A h512 hs hq₁ h4s hs3 hQ hV hX)))

end CurrentAdditive.V38Resource
