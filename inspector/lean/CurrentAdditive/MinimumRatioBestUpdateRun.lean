import CurrentAdditive.MinimumRatioBestUpdate

namespace CurrentAdditive.MinimumRatioBestUpdate

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

theorem low_ne (i j : Fin 32) (h : i ≠ j) : low i ≠ low j := by
  intro he
  apply h
  apply Fin.ext
  simpa [low] using congrArg Fin.val he

theorem positive_read (S : Bank) (v : Control) :
    advance program
      (⟨some .positive, v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some .best,
        (((S (low 15)).head?, v.1.2.1, v.1.2.2), v.2),
        Function.update S (low 15) (S (low 15)).tail⟩ := by
  cases h : S (low 15) with
  | nil => simp [advance, program, TM2.step, TM2.stepAux, h]
  | cons b bs => simp [advance, program, TM2.step, TM2.stepAux, h]

theorem best_read (S : Bank) (v : Control) :
    advance program
      (⟨some .best, v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some .less,
        ((v.1.1, (S (low 9)).head?, v.1.2.2), v.2), S⟩ := by
  cases h : S (low 9) with
  | nil =>
      simp [advance, program, TM2.step, TM2.stepAux, h]
  | cons b bs =>
      simp [advance, program, TM2.step, TM2.stepAux, h]

theorem less_read (S : Bank) (v : Control) :
    advance program
      (⟨some .less, v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨bif v.1.1.isSome &&
          (!v.1.2.1.isSome || (S (low 18)).head?.isSome) then
          some .clear else none,
        ((v.1.1, v.1.2.1, (S (low 18)).head?), v.2),
        Function.update S (low 18) (S (low 18)).tail⟩ := by
  cases h : S (low 18) with
  | nil =>
      simp [advance, program, TM2.step, TM2.stepAux, h]
      cases hpos : v.1.1 <;> cases hbest : v.1.2.1 <;> simp_all
  | cons b bs =>
      simp [advance, program, TM2.step, TM2.stepAux, h]
      cases hpos : v.1.1 <;> simp_all

theorem tests_run (S : Bank) :
    ((advance program)^[3])
      (⟨some .positive, initial, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨bif (S (low 15)).head?.isSome &&
          (!(S (low 9)).head?.isSome || (S (low 18)).head?.isSome) then
          some .clear else none,
        (((S (low 15)).head?, (S (low 9)).head?,
          (S (low 18)).head?), none),
        Function.update
          (Function.update S (low 15) (S (low 15)).tail)
          (low 18) (S (low 18)).tail⟩ := by
  have h159 : low 15 ≠ low 9 := low_ne 15 9 (by decide)
  have h1518 : low 15 ≠ low 18 := low_ne 15 18 (by decide)
  rw [show (3:Nat) = 1+1+1 by omega,
    Function.iterate_add_apply, Function.iterate_add_apply]
  simp only [Function.iterate_one, positive_read, best_read, less_read]
  simp [Function.update_of_ne, h159.symm, h1518.symm, initial]

theorem clear_run (S : Bank) (v : Control) :
    ((advance program)^[(S (low 9)).length + 1])
      (⟨some .clear, v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some (.copy .scan), initial, Function.update S (low 9) []⟩ := by
  generalize hb : S (low 9) = bits
  induction bits generalizing S v with
  | nil =>
      simp [advance, program, TM2.step, TM2.stepAux, hb]
  | cons bit bits ih =>
      have hstep : advance program
          (⟨some .clear, v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨some .clear, (v.1, some bit),
            Function.update S (low 9) bits⟩ := by
        simp [advance, program, TM2.step, TM2.stepAux, hb]
      rw [List.length_cons, Function.iterate_succ_apply, hstep]
      have hrec := ih (Function.update S (low 9) bits)
        (v.1, some bit) (Function.update_self (low 9) bits S)
      simpa [Function.update_idem] using hrec

theorem copy_run (S : Bank) (bits : List Bool)
    (h16 : S (low 16) = bits)
    (h9 : S (low 9) = [])
    (h21 : S (low 21) = []) :
    ∃ u ≤ 2*bits.length+2,
      ((advance program)^[u])
        (⟨some (.copy .scan), initial, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨some .finish, initial,
          Function.update S (low 9) bits⟩ := by
  let c := BitMachineCopy.cfg (some .scan) none bits [] []
  have hbank : BitMachineStackEmbedding.bank copySlots S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, copySlots, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, h16, h9, h21]
  have hhalt : (((advance BitMachineCopy.program)^[2*bits.length+2]) c).l = none := by
    change (BitMachineCopy.run (2*bits.length+2) c).l = none
    rw [show c = BitMachineCopy.cfg (some .scan) none bits [] [] from rfl,
      BitMachineCopy.run_correct]
    rfl
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs copySlots S
    Label.copy (fun b => ((none,none,none),b)) Prod.snd
    (fun b => rfl) (some .finish)
    BitMachineCopy.program program
    (by intro l; rfl)
    c (2*bits.length+2) hhalt
  have hlocal : ((advance BitMachineCopy.program)^[2*bits.length+2]) c =
      BitMachineCopy.cfg none none bits bits [] := by
    change BitMachineCopy.run (2*bits.length+2) c = _
    simpa only [List.append_nil] using BitMachineCopy.run_correct none bits []
  rw [hlocal] at hr
  change ((advance program)^[u])
      ⟨some (.copy .scan), initial,
        BitMachineStackEmbedding.bank copySlots S c.stk⟩ =
      ⟨some .finish, initial,
        BitMachineStackEmbedding.bank copySlots S
          (BitMachineCopy.cfg none none bits bits []).stk⟩ at hr
  have hupdate : (BitMachineCopy.cfg none none bits bits []).stk =
      Function.update c.stk 1 bits := by
    funext k
    fin_cases k <;> rfl
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update, hbank] at hr
  exact ⟨u, hu, by simpa [copySlots] using hr⟩

theorem finish_run (S : Bank) :
    advance program
      (⟨some .finish, initial, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, initial,
        Function.update S (low 9) (true :: S (low 9))⟩ := by
  simp [advance, program, TM2.step, TM2.stepAux]

theorem replace_run (S : Bank) (v : Control) (candidate : List Bool)
    (h16 : S (low 16) = candidate)
    (h21 : S (low 21) = []) :
    ∃ u ≤ (S (low 9)).length + 1 + (2*candidate.length+2) + 1,
      ((advance program)^[u])
        (⟨some .clear, v, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, initial,
        Function.update S (low 9) (true :: candidate)⟩ := by
  let T := Function.update S (low 9) []
  have h16' : T (low 16) = candidate := by
    simpa [T, Function.update_of_ne,
      (low_ne 9 16 (by decide)).symm] using h16
  have h21' : T (low 21) = [] := by
    simpa [T, Function.update_of_ne,
      (low_ne 9 21 (by decide)).symm] using h21
  have h9' : T (low 9) = [] := by simp [T]
  obtain ⟨b,hb,hrB⟩ := copy_run T candidate h16' h9' h21'
  have hrA := clear_run S v
  have hrC := finish_run (Function.update T (low 9) candidate)
  refine ⟨(S (low 9)).length + 1 + b + 1, ?_, ?_⟩
  · omega
  · rw [show (S (low 9)).length + 1 + b + 1 =
        1 + (b + ((S (low 9)).length + 1)) by omega,
      Function.iterate_add_apply, Function.iterate_add_apply]
    simp only [Function.iterate_one]
    rw [hrA]
    change advance program
      (((advance program)^[b])
        (⟨some (.copy .scan), initial, T⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _)) = _
    rw [hrB, hrC]
    simp [T]

noncomputable def readBank (S : Bank) : Bank :=
  Function.update
    (Function.update S (low 15) (S (low 15)).tail)
    (low 18) (S (low 18)).tail

noncomputable def shouldReplace (S : Bank) : Bool :=
  (S (low 15)).head?.isSome &&
    (!(S (low 9)).head?.isSome || (S (low 18)).head?.isSome)

noncomputable def chosenBest (S : Bank) : List Bool :=
  if shouldReplace S then true :: S (low 16) else S (low 9)

theorem shouldReplace_eq (S : Bank) :
    shouldReplace S =
      ((S (low 15)).head?.isSome &&
        ((S (low 9)).head?.isNone || (S (low 18)).head?.isSome)) := by
  cases hp : (S (low 15)).head? <;>
    cases hb : (S (low 9)).head? <;>
    cases hc : (S (low 18)).head? <;>
    simp [shouldReplace, hp, hb, hc]

theorem readBank_at (S : Bank) (j : Fin 32)
    (h15 : j ≠ 15) (h18 : j ≠ 18) :
    readBank S (low j) = S (low j) := by
  simp [readBank, Function.update_of_ne,
    (low_ne 15 j (Ne.symm h15)).symm,
    (low_ne 18 j (Ne.symm h18)).symm]

theorem update_run (S : Bank)
    (h21 : S (low 21) = []) :
    ∃ u ≤ 3 + (S (low 9)).length + 1 +
        (2*(S (low 16)).length+2) + 1,
      ((advance program)^[u])
        (⟨some .positive, initial, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, if shouldReplace S then initial else
          (((S (low 15)).head?, (S (low 9)).head?,
            (S (low 18)).head?), none),
        Function.update (readBank S) (low 9) (chosenBest S)⟩ := by
  let T := readBank S
  have h9 : T (low 9) = S (low 9) :=
    readBank_at S 9 (by decide) (by decide)
  have h16 : T (low 16) = S (low 16) :=
    readBank_at S 16 (by decide) (by decide)
  have h21' : T (low 21) = [] := by
    change readBank S (low 21) = []
    rw [readBank_at S 21 (by decide) (by decide)]
    exact h21
  by_cases hd : shouldReplace S = true
  · let vRead : Control := (((S (low 15)).head?, (S (low 9)).head?,
          (S (low 18)).head?), none)
    obtain ⟨v,hv,hr⟩ := replace_run T vRead (S (low 16)) h16 h21'
    refine ⟨v+3, ?_, ?_⟩
    · rw [h9] at hv
      omega
    · rw [Function.iterate_add_apply]
      have ht := tests_run S
      have hdec : ((S (low 15)).head?.isSome &&
          ((S (low 9)).head?.isNone || (S (low 18)).head?.isSome)) = true := by
        simpa only [shouldReplace_eq] using hd
      rw [ht]
      simpa [hdec, T, vRead, chosenBest, hd] using hr
  · refine ⟨3, by omega, ?_⟩
    have ht := tests_run S
    rw [ht]
    have hf : shouldReplace S = false := by
      cases h : shouldReplace S <;> simp_all
    have hdec : ((S (low 15)).head?.isSome &&
        ((S (low 9)).head?.isNone || (S (low 18)).head?.isSome)) = false := by
      simpa only [shouldReplace_eq] using hf
    simp [hdec, hf, chosenBest]
    change T = Function.update T (low 9) (S (low 9))
    rw [← h9]
    simp

end CurrentAdditive.MinimumRatioBestUpdate
