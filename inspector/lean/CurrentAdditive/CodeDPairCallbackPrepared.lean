import CurrentAdditive.CodeDPairCallbackForeign

/-! Charged cleanup of the selector's two scratch words before the exact
source/alphabet pair callback. -/

namespace CurrentAdditive.CodeDPairCallbackPrepared

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDPairCallbackProgram
open CurrentAdditive.CodeDPairCallbackForeign
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.CodeDCanonicalSourceV2
open Turing BitMachineEncoding

abbrev Stack := Fin 15

inductive Label where
  | clear0 | clear5 | core (l : CodeDPairCallbackProgram.Label)
  deriving DecidableEq, Fintype

abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .clear0 => BitMachineClearBank.clearStep 0 .clear0 .clear5
  | .clear5 => BitMachineClearBank.clearStep 5 .clear5
      (.core (.copy (.inl .scan)))
  | .core l => BitMachineInline.stmt Label.core (fun v => ((), v))
      Prod.snd none (CodeDPairCallbackProgram.program l)

def run (t : Nat) (c : Config) : Config :=
  ((advance program)^[t]) c

def prepared (S : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update S 0 []) 5 []

theorem clear_prefix (S : Stack → List Bool) :
    run ((S 0).length + 1 + ((S 5).length + 1))
      ⟨some .clear0, ((), none), S⟩ =
      ⟨some (.core (.copy (.inl .scan))), ((), none), prepared S⟩ := by
  have h0 := BitMachineClearBank.clear_one_run program 0 .clear0 .clear5
    (by rfl) () S
  have h5 := BitMachineClearBank.clear_one_run program 5 .clear5
    (.core (.copy (.inl .scan))) (by rfl) ()
    (Function.update S 0 [])
  have hlen : (Function.update S 0 []) 5 = S 5 := by simp
  rw [hlen] at h5
  change ((advance program)^[_ + _]) _ = _
  rw [Nat.add_comm ((S 0).length + 1) ((S 5).length + 1),
    Function.iterate_add_apply, h0, h5]
  rfl

theorem core_inline (c : CodeDPairCallbackProgram.Config) (t : Nat)
    (h : (CodeDPairCallbackProgram.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.core
        (fun v => ((), v)) none c) =
      BitMachineInline.cfg Label.core (fun v => ((), v)) none
        (CodeDPairCallbackProgram.run t c) := by
  exact BitMachineInline.outputs Label.core (fun v => ((), v))
    Prod.snd (by intro v; rfl) none
    CodeDPairCallbackProgram.program program (by intro l; rfl)
    c t h

theorem run_add {c d : Config} {a : Nat}
    (h : run a c = d) (b : Nat) :
    run (a+b) c = run b d := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run b) h

theorem pair_from_selected (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (foreign : Stack → List Bool)
    (scratch0 scratch5 : List Bool) :
    ∃ t ≤ scratch0.length + scratch5.length + 2 +
        CodeDPairCallbackRun.fixedBudget x y output,
      ∃ S : Stack → List Bool,
        run t
          ⟨some .clear0, ((), none),
            Function.update
              (Function.update
                (initialWithForeign x y output foreign).stk 0 scratch0)
              5 scratch5⟩ =
          ⟨none, ((), none), S⟩ ∧
        S 9 = output ++ EncodedCommunication.field
          (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)) ∧
        S 12 = encodeEntry x ∧ S 8 = foreign 8 ∧
        S 10 = foreign 10 ∧ S 13 = foreign 13 := by
  let S₀ := Function.update
    (Function.update (initialWithForeign x y output foreign).stk 0 scratch0)
    5 scratch5
  have hzero : (initialWithForeign x y output foreign).stk 0 = [] := by
    change BitMachineStackEmbedding.bank locate foreign
      (fun j => CodeDPairCallbackRun.initialBank x y output (locate j))
      (locate ⟨0, by decide⟩) = []
    rw [BitMachineStackEmbedding.bank_at]
    simp [CodeDPairCallbackRun.initialBank, locate]
  have hfive : (initialWithForeign x y output foreign).stk 5 = [] := by
    change BitMachineStackEmbedding.bank locate foreign
      (fun j => CodeDPairCallbackRun.initialBank x y output (locate j))
      (locate ⟨5, by decide⟩) = []
    rw [BitMachineStackEmbedding.bank_at]
    simp [CodeDPairCallbackRun.initialBank, locate]
  have hprep : prepared S₀ =
      (initialWithForeign x y output foreign).stk := by
    funext j
    by_cases hj0 : j = 0
    · subst j
      simp [prepared, S₀, hzero]
    · by_cases hj5 : j = 5
      · subst j
        simp [prepared, S₀, hfive]
      · simp [prepared, S₀, Function.update_of_ne hj0,
          Function.update_of_ne hj5]
  obtain ⟨t, ht, S, hr, h9, h12, h8, h10, h13⟩ :=
    one_pair_foreign x y output foreign
  have hcore : (CodeDPairCallbackProgram.run t
      (initialWithForeign x y output foreign)).l = none := by
    rw [hr]
  obtain ⟨u, hu, hinline⟩ := core_inline
    (initialWithForeign x y output foreign) t hcore
  have hprefix := clear_prefix S₀
  have h0 : S₀ 0 = scratch0 := by simp [S₀]
  have h5 : S₀ 5 = scratch5 := by simp [S₀]
  rw [h0, h5, hprep] at hprefix
  have hfull := run_add hprefix u
  have hinline' : run u
      ⟨some (.core (.copy (.inl .scan))), ((), none),
        (initialWithForeign x y output foreign).stk⟩ =
      ⟨none, ((), none), S⟩ := by
    simpa [BitMachineInline.cfg, hr] using hinline
  have htotal := hfull.trans hinline'
  refine ⟨scratch0.length + 1 + (scratch5.length + 1) + u, ?_, S,
    ?_, h9, h12, h8, h10, h13⟩
  · omega
  · simpa [S₀] using htotal

#print axioms pair_from_selected

end CurrentAdditive.CodeDPairCallbackPrepared
