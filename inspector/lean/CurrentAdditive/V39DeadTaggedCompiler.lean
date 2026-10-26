import CurrentAdditive.V39GeneratorCode
import Paper2.CodeTaggedCompiler
import EthInapproximability.CurrentPaper.BitMachineRawSequence

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39DeadTaggedCompiler

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
open Paper2.RecursiveSamplingProgram Paper2.EncodedSamplerAlgebra
open CurrentAdditive.V39GeneratorCode

/-- A separate physical-construction representation. The second arm is
stored dead syntax: its interval is empty for every legal ticket. -/
def deadTaggedCode (q₁ q₂ s : ℕ) (c : Code) : Code :=
  .branch3 256 255 255
    (.append (.emit [false]) (rawCode q₁ q₂ s c))
    (.append (.emit [true, false]) (fixedTailCode q₁ q₂ s c))
    (.append (.emit [true, true]) (outerCode q₁ q₂ s c))

theorem no_middle_ticket (t : Fin 256) : ¬ (¬ t.val < 255 ∧ t.val < 255) := by omega

theorem equal_cut_meaning (n cut : ℕ) (a b c d : Code) :
    meaning (.branch3 n cut cut a b c) = meaning (.branch3 n cut cut a d c) := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [meaning]
    congr 1
    funext t
    by_cases ht : t.val < cut <;> simp only [ht, ↓reduceIte]

theorem deadTagged_meaning (q₁ q₂ s : ℕ) (c : Code) :
    meaning (deadTaggedCode q₁ q₂ s c) =
      meaning (currentTaggedCode q₁ q₂ s c) :=
  equal_cut_meaning 256 255 _ _ _ _

theorem deadTagged_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (f : Y → List Bool) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map f p) :
    meaning (deadTaggedCode q₁ q₂ s c) =
      Program.map (tagWord q₁ q₂ s f) (V38OneStep.tagged p) := by
  rw [deadTagged_meaning]
  exact currentTagged_exact f p c hc

def oldHeader : List Bool := [true, false, false] ++ unary 256 ++ unary 254 ++ unary 255
def newHeader : List Bool := [true, false, false] ++ unary 256 ++ unary 255 ++ unary 255

def children (q₁ q₂ s : ℕ) (c : Code) : List Bool :=
  encodeCode (.append (.emit [false]) (rawCode q₁ q₂ s c)) ++
    encodeCode (.append (.emit [true, false]) (fixedTailCode q₁ q₂ s c)) ++
    encodeCode (.append (.emit [true, true]) (outerCode q₁ q₂ s c))

theorem old_serialization (q₁ q₂ s : ℕ) (c : Code) :
    encodeCode (taggedCode q₁ q₂ s c) = oldHeader ++ children q₁ q₂ s c := by
  simp only [taggedCode, encodeCode, oldHeader, children, List.append_assoc]

theorem current_serialization (q₁ q₂ s : ℕ) (c : Code) :
    encodeCode (deadTaggedCode q₁ q₂ s c) = newHeader ++ children q₁ q₂ s c := by
  simp only [deadTaggedCode, encodeCode, newHeader, children, List.append_assoc]

theorem header_lengths : oldHeader.length = 771 ∧ newHeader.length = 772 := by
  simp [oldHeader, newHeader, unary_length]

def discard {Λ σ : Type} (n : ℕ)
    (next : TM2.Stmt (fun _ : Fin 8 => Bool) Λ σ) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Λ σ :=
  match n with
  | 0 => next
  | n + 1 => pop 7 (fun v _ => v) (discard n next)

def prepend {Λ σ : Type} (bits : List Bool)
    (next : TM2.Stmt (fun _ : Fin 8 => Bool) Λ σ) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Λ σ :=
  bits.foldl (fun stmt bit => push 7 (fun _ => bit) stmt) next

private theorem update_twice (S : Fin 8 → List Bool) (a b : List Bool) :
    Function.update (Function.update S 7 a) 7 b = Function.update S 7 b := by
  funext i
  by_cases hi : i = 7 <;> simp [Function.update, hi]

theorem discard_correct {Λ σ : Type} (bits rest : List Bool)
    (next : TM2.Stmt (fun _ : Fin 8 => Bool) Λ σ) (v : σ)
    (S : Fin 8 → List Bool) (hS : S 7 = bits ++ rest) :
    TM2.stepAux (discard bits.length next) v S =
      TM2.stepAux next v (Function.update S 7 rest) := by
  induction bits generalizing S with
  | nil =>
    simp only [List.nil_append] at hS
    change TM2.stepAux next v S = TM2.stepAux next v (Function.update S 7 rest)
    rw [← hS, Function.update_eq_self]
  | cons b bits ih =>
    simp only [List.length_cons, discard, TM2.stepAux]
    rw [ih (Function.update S 7 (S 7).tail) (by simp [hS])]
    rw [update_twice]

theorem prepend_correct {Λ σ : Type} (bits : List Bool)
    (next : TM2.Stmt (fun _ : Fin 8 => Bool) Λ σ) (v : σ) (S : Fin 8 → List Bool) :
    TM2.stepAux (prepend bits next) v S =
      TM2.stepAux next v (Function.update S 7 (bits ++ S 7)) := by
  induction bits generalizing next S with
  | nil => simp [prepend, Function.update_eq_self]
  | cons b bits ih =>
    simp only [prepend, List.foldl_cons]
    rw [show bits.foldl (fun stmt bit => push 7 (fun _ => bit) stmt) (push 7 (fun _ => b) next) =
      prepend bits (push 7 (fun _ => b) next) by rfl, ih]
    simp only [TM2.stepAux, Function.update_self, update_twice, List.cons_append]

/-- A fixed finite controller replaces 771 constant header bits by 772
constant header bits. All variable code bytes and all other banks survive. -/
def patchProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 8 => Bool) Unit Unit :=
  discard oldHeader.length (prepend newHeader halt)

theorem patch_run (S : Fin 8 → List Bool) (rest : List Bool)
    (hS : S 7 = oldHeader ++ rest) :
    ((advance patchProgram)^[1])
      (⟨some (), (), S⟩ : TM2.Cfg (fun _ : Fin 8 => Bool) Unit Unit) =
        ⟨none, (), Function.update S 7 (newHeader ++ rest)⟩ := by
  change TM2.stepAux (patchProgram ()) () S = _
  rw [patchProgram, discard_correct oldHeader rest _ () S hS, prepend_correct]
  simp only [TM2.stepAux, Function.update_self, update_twice]

def program := BitMachineRawSequence.program Paper2.TaggedCompiler.program patchProgram
  () (none : Paper2.TaggedCompiler.Control) ()

/-- The complete new physical tagged-code builder, including construction
of its stored dead arm, executes in the old polynomial clock plus two.
The complete final bank and exact serialized current datum are identified. -/
theorem physical_deadTagged (q₁ q₂ s : ℕ) (c : Code) :
    ∃ t ≤ Paper2.TaggedCompiler.taggedClock q₁ q₂ s c + 2,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (Paper2.TaggedCompiler.Label.outerInit .third)),
          ((none : Paper2.TaggedCompiler.Control), ()),
          Paper2.TaggedCompiler.inputs q₁ q₂ s c⟩ : TM2.Cfg (fun _ : Fin 8 => Bool) _ _) =
        ⟨none, (none, ()),
          Function.update (Paper2.TaggedCompiler.inputs q₁ q₂ s c) 7
            (encodeCode (deadTaggedCode q₁ q₂ s c))⟩ := by
  have ha := Paper2.TaggedCompiler.run_tagged q₁ q₂ s c
  have hb := patch_run (Function.update (Paper2.TaggedCompiler.inputs q₁ q₂ s c) 7
    (encodeCode (taggedCode q₁ q₂ s c))) (children q₁ q₂ s c)
    (by simp only [Function.update_self, old_serialization])
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    Paper2.TaggedCompiler.program patchProgram (Paper2.TaggedCompiler.Label.outerInit .third)
    () none none () () (Paper2.TaggedCompiler.inputs q₁ q₂ s c)
    (Function.update (Paper2.TaggedCompiler.inputs q₁ q₂ s c) 7
      (encodeCode (taggedCode q₁ q₂ s c)))
    (Function.update (Paper2.TaggedCompiler.inputs q₁ q₂ s c) 7
      (encodeCode (deadTaggedCode q₁ q₂ s c)))
    (Paper2.TaggedCompiler.taggedClock q₁ q₂ s c) 1 ha (by
      simpa only [update_twice, ← current_serialization] using hb)
  exact ⟨t, by omega, hr⟩

#print axioms deadTagged_exact
#print axioms patch_run
#print axioms physical_deadTagged

end CurrentAdditive.V39DeadTaggedCompiler
