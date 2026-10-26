import Paper2.YaoEvents
import Paper2.YaoLowerBoundProbability
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Unit 5 segment Y6, part 2 (lane a-yao-owner-2): embedded unary tools for
the Yao prelude, each an exact whole-bank run of an ADMITTED program:

* `copy_append_run`: the admitted `ExactParameterBranchInstall.copyProgram`
  on a nonempty target (the admitted `BitMachineCopy.run_correct` prepends);
* `push_const_run`: the admitted `SourceClauseFixedUnary.program` pushing a
  fixed number of marks onto an arbitrary word (admitted `run_from`);
* `pow_run`: the admitted `MatrixUnaryPower.program` embedded by
  `BitMachineStackEmbedding.stmt` (admitted `unary_power_run`);
* `drop_run`: a one-instruction program popping one mark (new, trivial).

Arithmetic identities used by the payload-count stage:
`alice_div_three`, `alice_mod_three` (from the admitted `aliceNodes_closed`),
and `payloadCount_eq` (unfolding the admitted `payloadCount`). -/

noncomputable section

namespace Paper2.YaoPrelude

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

variable {K : Type*} [DecidableEq K]

/-- The admitted copy program onto an arbitrary target: the copy is prepended. -/
theorem copy_append_run (ι : Fin 3 ↪ K) (S : K → List Bool) (bits target : List Bool)
    (hsource : S (ι 0) = bits) (htarget : S (ι 1) = target) (hscratch : S (ι 2) = []) :
    ∃ t ≤ 2 * bits.length + 2,
      ((advance (ExactParameterBranchInstall.copyProgram ι))^[t])
        (⟨some .scan, none, S⟩ :
          TM2.Cfg (fun _ : K => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, Function.update S (ι 1) (bits ++ target)⟩ := by
  classical
  let c := BitMachineCopy.cfg (some .scan) none bits target []
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, BitMachineCopy.cfg, BitMachineCopy.stackContents,
      hsource, htarget, hscratch]
  have hhalt : (((advance BitMachineCopy.program)^[2 * bits.length + 2]) c).l = none := by
    change (BitMachineCopy.run (2 * bits.length + 2) c).l = none
    rw [show c = BitMachineCopy.cfg (some .scan) none bits target [] from rfl,
      BitMachineCopy.run_correct]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S
    id id id (by intro v; rfl) none
    BitMachineCopy.program (ExactParameterBranchInstall.copyProgram ι) (by intro l; rfl)
    c (2 * bits.length + 2) hhalt
  have hlocal : ((advance BitMachineCopy.program)^[2 * bits.length + 2]) c =
      BitMachineCopy.cfg none none bits (bits ++ target) [] :=
    BitMachineCopy.run_correct none bits target
  rw [hlocal] at he
  change ((advance (ExactParameterBranchInstall.copyProgram ι))^[t])
      ⟨some .scan, none, BitMachineStackEmbedding.bank ι S c.stk⟩ =
      ⟨none, none,
        BitMachineStackEmbedding.bank ι S
          (BitMachineCopy.cfg none none bits (bits ++ target) []).stk⟩ at he
  have hupdate : (BitMachineCopy.cfg none none bits (bits ++ target) []).stk =
      Function.update c.stk 1 (bits ++ target) := by
    funext k
    fin_cases k <;> rfl
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨t, ht, he⟩

/-- The admitted fixed-unary writer pushes `N` marks onto any word. -/
theorem push_const_run (target : K) (S : K → List Bool) (N : ℕ) (suffix : List Bool)
    (h : S target = suffix) :
    ((advance (SourceClauseFixedUnary.program target N))^[N + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label N), (), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (SourceClauseFixedUnary.Label N) Unit) =
      ⟨none, (), Function.update S target (List.replicate N true ++ suffix)⟩ := by
  have hr := SourceClauseFixedUnary.run_from target S (0 : SourceClauseFixedUnary.Label N) N
    (by simp) suffix
  have hs : Function.update S target (List.replicate (0 : Fin (N + 1)).val true ++ suffix) = S := by
    funext x
    by_cases hx : x = target
    · subst hx; simp [h]
    · simp [Function.update, hx]
  simpa only [SourceClauseFixedUnary.state, hs] using hr

/-- A one-instruction program: pop one mark from `target`, then halt. -/
def dropProgram (target : K) : Unit → TM2.Stmt (fun _ : K => Bool) Unit Unit :=
  fun _ => TM2.Stmt.pop target (fun v _ => v) TM2.Stmt.halt

theorem drop_run (target : K) (S : K → List Bool) (w : List Bool) (h : S target = w) :
    ((advance (dropProgram target))^[1])
      (⟨some (), (), S⟩ : TM2.Cfg (fun _ : K => Bool) Unit Unit) =
      ⟨none, (), Function.update S target w.tail⟩ := by
  simp [advance, TM2.step, TM2.stepAux, dropProgram, h]

/-- The admitted unary power-of-two constructor on four selected ambient cells:
exponent `ι (inr ())` preserved, output `ι (inl 0)`, work cells back to `[]`. -/
def powProgram (ι : MatrixUnaryPower.Stack ↪ K) (l : MatrixUnaryPower.Label) :
    TM2.Stmt (fun _ : K => Bool) MatrixUnaryPower.Label MatrixUnaryPower.Control :=
  BitMachineStackEmbedding.stmt ι id id id none (MatrixUnaryPower.program l)

theorem pow_run (ι : MatrixUnaryPower.Stack ↪ K) (S : K → List Bool) (a : ℕ)
    (hx : S (ι (.inr ())) = List.replicate a true) (h0 : S (ι (.inl 0)) = [])
    (h1 : S (ι (.inl 1)) = []) (h2 : S (ι (.inl 2)) = []) :
    ∃ t ≤ 4 * 2 ^ a + 5 * a + 7,
      ((advance (powProgram ι))^[t])
        (⟨some (.inr false), ((false, false), none), S⟩ :
          TM2.Cfg (fun _ : K => Bool) MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none, ((false, false), none),
          Function.update S (ι (.inl 0)) (List.replicate (2 ^ a) true)⟩ := by
  classical
  obtain ⟨n, hn, hr⟩ := MatrixUnaryPower.unary_power_run a
  let c := MatrixUnaryPower.cfg (some (.inr false)) ((false, false), none) [] [] []
    (List.replicate a true)
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    rcases k with k | k
    · fin_cases k <;> simp [c, MatrixUnaryPower.cfg, MatrixUnaryPower.contents,
        MatrixBinaryAddress.stackContents, h0, h1, h2]
    · cases k; simp [c, MatrixUnaryPower.cfg, MatrixUnaryPower.contents, hx]
  have hhalt : (((advance MatrixUnaryPower.program)^[n]) c).l = none := by
    change (MatrixUnaryPower.run n c).l = none
    rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S id id id (fun _ => rfl) none
    MatrixUnaryPower.program (powProgram ι) (by intro l; rfl) c n hhalt
  have hlocal : ((advance MatrixUnaryPower.program)^[n]) c =
      MatrixUnaryPower.cfg none ((false, false), none) (List.replicate (2 ^ a) true) [] []
        (List.replicate a true) := hr
  rw [hlocal] at he
  change ((advance (powProgram ι))^[t])
      ⟨some (.inr false), ((false, false), none), BitMachineStackEmbedding.bank ι S c.stk⟩ =
      ⟨none, ((false, false), none), BitMachineStackEmbedding.bank ι S
        (MatrixUnaryPower.cfg none ((false, false), none) (List.replicate (2 ^ a) true) [] []
          (List.replicate a true)).stk⟩ at he
  have hupdate : (MatrixUnaryPower.cfg none ((false, false), none)
      (List.replicate (2 ^ a) true) [] [] (List.replicate a true)).stk =
      Function.update c.stk (.inl 0) (List.replicate (2 ^ a) true) := by
    funext k
    rcases k with k | k
    · fin_cases k <;> simp [c, MatrixUnaryPower.cfg, MatrixUnaryPower.contents,
        MatrixBinaryAddress.stackContents]
    · cases k; simp [c, MatrixUnaryPower.cfg, MatrixUnaryPower.contents]
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨t, ht.trans hn, he⟩

/-! ## Arithmetic identities -/

theorem alice_div_three (r : ℕ) : (2 + 2 ^ (2 * r + 2)) / 3 = Paper2.Yao.aliceNodes r + 1 := by
  have h := Paper2.Yao.aliceNodes_closed r
  omega

theorem alice_mod_three (r : ℕ) : (2 + 2 ^ (2 * r + 2)) % 3 = 0 := by
  have h := Paper2.Yao.aliceNodes_closed r
  omega

/-- The exponent built by the prelude, for `1 ≤ t`. -/
theorem exponent_eq (t b : ℕ) (ht : 1 ≤ t) :
    6 * t - 4 + (b + b) = 2 * (b + 3 * t - 3) + 2 := by
  omega

/-- The admitted payload count as the ceiling quotient the prelude computes. -/
theorem payloadCount_eq (t b lambda : ℕ) :
    payloadCount t b lambda =
      (2 ^ (b + (t - 4)) +
          (lambda + 2 ^ b * (2 ^ t * 2 ^ t + 1) *
            (Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1)) - 1) / 2 ^ (b + (t - 4)) := by
  unfold payloadCount Paper2.Yao.payloadSampleCount Paper2.Yao.payloadDelta
  congr 1
  omega

#print axioms copy_append_run
#print axioms push_const_run
#print axioms drop_run
#print axioms pow_run
#print axioms alice_div_three
#print axioms alice_mod_three
#print axioms exponent_eq
#print axioms payloadCount_eq

end Paper2.YaoPrelude

end
