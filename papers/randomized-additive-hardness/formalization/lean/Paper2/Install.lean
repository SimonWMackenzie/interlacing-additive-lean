import Paper2.SuccessOrient

/-! Unit 3, segment (2), first part: the installation interface of `SuccessOrient.startBank`.

`SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word` is the count-free bank
`SuccessOrient.startBank 0 0 0 0 0 0 0 0 0 0 []` with exactly eleven cells written:
compiler cells 12 (q₂), 16 (q₁), 17 (s), 18 (n), 31 (w), 32 (Q), 63 (p), 64 (unary k),
`countXCell` (mX), `countYCell` (mY) and draw cell 0 (the tape word). This is the analogue of
`RepJoin.preJHm_off` that an installer needs: a program that starts from the count-free bank and
copies produced unary counts into these eleven cells ends exactly at `startBank`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.StartInstall

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open SamplerParameterBank

noncomputable section

instance instDecC : DecidableEq ConsumerStack := inferInstance
instance instDecP : DecidableEq Private := inferInstance
instance instDecPre : DecidableEq SuccessOrient.PreStack := @instDecidableEqSum _ _ instDecC instDecP
instance instDecSO : DecidableEq SuccessOrient.Stack := @instDecidableEqSum _ _ instDecPre inferInstance

def u (n : ℕ) : List Bool := List.replicate n true

/-- A consumer cell viewed in the success start bank. -/
def pc (x : ConsumerStack) : SuccessOrient.Stack := .inl (.inl x)

/-- The count-free start bank. -/
def blank : SuccessOrient.Stack → List Bool := SuccessOrient.startBank 0 0 0 0 0 0 0 0 0 0 []

/-- The eleven installed cells. -/
def cells : List SuccessOrient.Stack :=
  [pc (compilerCell 12), pc (compilerCell 16), pc (compilerCell 17), pc (compilerCell 18),
    pc (compilerCell 31), pc (compilerCell 32), pc (compilerCell 63), pc (compilerCell 64),
    pc countXCell, pc countYCell, pc (drawCell 0)]

theorem mainBank_off (tape tape' : List Bool) (i : Fin 16) (hi : i ≠ 0) :
    DrawParameterLoader.initialBank tape 0 0 0 (.inl i) =
      DrawParameterLoader.initialBank tape' 0 0 0 (.inl i) := by
  simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank, hi]

theorem publicBase_off (n s q₁ q₂ w Q p : ℕ) (fuel : List Bool) (i : Fin 65)
    (h12 : i ≠ 12) (h16 : i ≠ 16) (h17 : i ≠ 17) (h18 : i ≠ 18) (h31 : i ≠ 31) (h32 : i ≠ 32)
    (h63 : i ≠ 63) (h64 : i ≠ 64) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel i =
      CodeRecursiveSeedPrep.publicBase 0 0 0 0 0 0 0 [] i := by
  simp [CodeRecursiveSeedPrep.publicBase, h12, h16, h17, h18, h31, h32, h63, h64]

/-- Off the eleven cells the start bank does not depend on the counts or the tape. -/
theorem startBank_off (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (x : SuccessOrient.Stack)
    (hx : x ∉ cells) :
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word x = blank x := by
  rcases x with (c | pv) | f
  · -- consumer cells
    have hc : ∀ y, c = y → pc y ∉ cells → True := fun _ _ _ => trivial
    clear hc
    show initial n p s q₁ q₂ w Q k mX mY word 0 0 c = initial 0 0 0 0 0 0 0 0 0 0 [] 0 0 c
    rcases c with (y | z) | wr
    · rcases y with i | r
      · have e1 := initial_compiler n p s q₁ q₂ w Q k mX mY word 0 0 i
        have e2 := initial_compiler 0 0 0 0 0 0 0 0 0 0 [] 0 0 i
        simp only [compilerCell] at e1 e2
        rw [e1, e2]
        simp only [cells, pc, compilerCell, List.mem_cons, Sum.inl.injEq, List.not_mem_nil,
          countXCell, countYCell, drawCell, reduceCtorEq, or_false, not_or] at hx
        obtain ⟨h12, h16, h17, h18, h31, h32, h63, h64⟩ := hx
        exact publicBase_off _ _ _ _ _ _ _ _ i h12 h16 h17 h18 h31 h32 h63 h64
      · rw [initial_sample, initial_sample]
        show bank CodeGeneratorSampleTransfer.compilerSlots
            (CodeGeneratorSampleTransfer.foreign mX mY) _ (.inr r) =
          bank CodeGeneratorSampleTransfer.compilerSlots
            (CodeGeneratorSampleTransfer.foreign 0 0) _ (.inr r)
        rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk),
          bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
        rcases r with r | f
        · rfl
        · simp only [cells, pc, compilerCell, List.mem_cons, Sum.inl.injEq, List.not_mem_nil,
            countXCell, countYCell, drawCell, reduceCtorEq, or_false, not_or, Sum.inr.injEq,
            false_or] at hx
          fin_cases f
          · exact absurd rfl hx.1
          · exact absurd rfl hx.2
          · rfl
    · rw [initial_consumer, initial_consumer]
      rcases z with j | f
      · show CodeAdminDraw.foreign word 0 0 j = CodeAdminDraw.foreign [] 0 0 j
        rcases j with (i | lc) | o
        · have hi : i ≠ 0 := by
            intro hi0
            subst hi0
            exact hx (by simp [cells, pc, drawCell, CodeHeaderDraw.d])
          exact mainBank_off word [] i hi
        · rfl
        · rfl
      · rfl
    · rfl
  · rfl
  · rfl

/-- At the eleven cells the start bank holds the installed words; the count-free bank holds `[]`. -/
theorem startBank_cells (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) :
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 12)) = u q₂ ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 16)) = u q₁ ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 17)) = u s ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 18)) = u n ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 31)) = u w ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 32)) = u Q ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 63)) = u p ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (compilerCell 64)) = u k ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc countXCell) = u mX ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc countYCell) = u mY ∧
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (pc (drawCell 0)) = word := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 12).trans (publicBase_q2 _ _ _ _ _ _ _ _)
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 16).trans (publicBase_q1 _ _ _ _ _ _ _ _)
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 17).trans (publicBase_s _ _ _ _ _ _ _ _)
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 18).trans (publicBase_n _ _ _ _ _ _ _ _)
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 31).trans (publicBase_w _ _ _ _ _ _ _ _)
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 32).trans (publicBase_Q _ _ _ _ _ _ _ _)
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 63).trans (publicBase_p _ _ _ _ _ _ _ _)
  · exact (initial_compiler _ _ _ _ _ _ _ _ _ _ _ _ _ 64).trans (publicBase_k _ _ _ _ _ _ _ _)
  · exact initial_countX _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact initial_countY _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact (initial_draw _ _ _ _ _ _ _ _ _ _ _ _ _ 0).trans
      (by simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank])

/-- The installation identity: the start bank is the count-free bank with the eleven cells written. -/
theorem startBank_install (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) :
    SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word =
      Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update blank
        (pc (compilerCell 12)) (u q₂)) (pc (compilerCell 16)) (u q₁)) (pc (compilerCell 17)) (u s))
        (pc (compilerCell 18)) (u n)) (pc (compilerCell 31)) (u w)) (pc (compilerCell 32)) (u Q))
        (pc (compilerCell 63)) (u p)) (pc (compilerCell 64)) (u k)) (pc countXCell) (u mX))
        (pc countYCell) (u mY)) (pc (drawCell 0)) word := by
  obtain ⟨c12, c16, c17, c18, c31, c32, c63, c64, cX, cY, cD⟩ :=
    startBank_cells n p s q₁ q₂ w Q k mX mY word
  funext x
  simp only [Function.update_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 <;> subst_vars <;>
    first
    | assumption
    | exact startBank_off n p s q₁ q₂ w Q k mX mY word x (by
        simp only [cells, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1⟩)

end

end Paper2.StartInstall

#print axioms Paper2.StartInstall.startBank_off
#print axioms Paper2.StartInstall.startBank_cells
#print axioms Paper2.StartInstall.startBank_install
