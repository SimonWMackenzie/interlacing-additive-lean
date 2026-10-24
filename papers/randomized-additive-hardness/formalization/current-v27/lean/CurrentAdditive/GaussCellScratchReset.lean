import CurrentAdditive.GaussFetchedArithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussCellScratchReset
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussFetchedArithmetic

/-- Every local working stack, excluding the physical inputs and answer.
Inputs i7,matrix8,r9,pivot10,caller context11..14,j19,c20 survive. -/
def resetBank (i : Fin 52) : Bank :=
  ⟨if i.val<7 then i.val else if i.val<11 then i.val+8
    else if i.val<19 then i.val+10 else i.val+12,by
      have hi:=i.isLt
      split_ifs <;> omega⟩
inductive Label where
  | clear : Fin 52 → Label
  | finish | done
  deriving DecidableEq,Fintype
abbrev Control := Unit × Option Bool

def next (i : Fin 52) : Label :=
  if h : i.val+1<52 then .clear ⟨i.val+1,h⟩ else .finish

def labels (i : Fin 53) : Label :=
  if h : i.val<52 then .clear ⟨i.val,h⟩ else .finish

def program : Label → TM2.Stmt (fun _ : Bank => Bool) Label Control
  | .clear i => BitMachineClearBank.clearStep (resetBank i) (.clear i) (next i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

theorem bank_inj : Function.Injective resetBank := by
  intro i j h
  have hv:=congrArg (fun z : Bank => z.val) h
  change (if i.val<7 then i.val else if i.val<11 then i.val+8 else if i.val<19 then i.val+10 else i.val+12) =
    (if j.val<7 then j.val else if j.val<11 then j.val+8 else if j.val<19 then j.val+10 else j.val+12) at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem label_next (i : Fin 52) :
    labels i.castSucc = .clear i ∧ labels i.succ = next i := by
  fin_cases i <;> simp [labels,next]

noncomputable def clock (S : Bank → List Bool) : Nat :=
  (∑ i, (S (resetBank i)).length)+54

theorem physical_reset (S : Bank → List Bool) :
    ((advance program)^[clock S])
      (⟨some (.clear 0),((),none),S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none,((),none),BitMachineClearBank.cleared resetBank S⟩ := by
  have hmain : ((advance program)^[(∑ i, (S (resetBank i)).length)+52+1])
      (⟨some (labels 0),((),none),S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨some .done,((),none),BitMachineClearBank.cleared resetBank S⟩ := by
    apply BitMachineClearBank.clear_bank_run program id .done
      52 resetBank bank_inj labels
    · intro i
      obtain ⟨hi,hn⟩ := label_next i
      rw [hi,hn]
      rfl
    · simp [labels,program]
  unfold clock
  rw [show (∑ i, (S (resetBank i)).length)+54 =
    ((∑ i, (S (resetBank i)).length)+52+1)+1 by omega,
    Function.iterate_succ_apply']
  rw [show (⟨some (.clear 0),((),none),S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
    ⟨some (labels 0),((),none),S⟩ from rfl,hmain]
  rfl

def retained (i : Fin 64) : Prop :=
  i.val=7 ∨ i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 ∨ i.val=12 ∨
    i.val=13 ∨ i.val=14 ∨ i.val=19 ∨ i.val=20 ∨ i.val=29 ∨ i.val=30
instance (i : Fin 64) : Decidable (retained i) := inferInstanceAs (Decidable (_ ∨ _))

theorem reset_range (i : Fin 64) :
    (∃ j, resetBank j = lower i) ↔ ¬ retained i := by
  constructor
  · rintro ⟨j,hj⟩
    have hv:=congrArg (fun z : Bank => z.val) hj
    change (if j.val<7 then j.val else if j.val<11 then j.val+8 else if j.val<19 then j.val+10 else j.val+12)=i.val at hv
    unfold retained
    split_ifs at hv <;> omega
  · intro hp
    unfold retained at hp
    by_cases h7 : i.val<7
    · exact ⟨⟨i.val,by omega⟩,Fin.ext (by simp [resetBank,lower,h7])⟩
    by_cases h19 : i.val<19
    · refine ⟨⟨i.val-8,by omega⟩,Fin.ext ?_⟩
      change (if i.val-8<7 then i.val-8 else if i.val-8<11 then i.val-8+8 else if i.val-8<19 then i.val-8+10 else i.val-8+12)=i.val
      split_ifs <;> omega
    by_cases h29 : i.val<29
    · refine ⟨⟨i.val-10,by omega⟩,Fin.ext ?_⟩
      change (if i.val-10<7 then i.val-10 else if i.val-10<11 then i.val-10+8 else if i.val-10<19 then i.val-10+10 else i.val-10+12)=i.val
      split_ifs <;> omega
    · refine ⟨⟨i.val-12,by omega⟩,Fin.ext ?_⟩
      change (if i.val-12<7 then i.val-12 else if i.val-12<11 then i.val-12+8 else if i.val-12<19 then i.val-12+10 else i.val-12+12)=i.val
      split_ifs <;> omega


theorem reset_lower (j : Fin 52) : ∃ i : Fin 64, lower i = resetBank j := by
  have hj : (resetBank j).val < 64 := by
    have hj:=j.isLt
    change (if j.val<7 then j.val else if j.val<11 then j.val+8 else if j.val<19 then j.val+10 else j.val+12)<64
    split_ifs <;> omega
  exact ⟨⟨(resetBank j).val,hj⟩,Fin.ext rfl⟩

theorem restore_eq (S U : Bank → List Bool) (answer : List Bool)
    (hclean : ∀ i : Fin 64, ¬ retained i → S (lower i) = [])
    (hkeep : ∀ i : Fin 64, retained i → U (lower i) = S (lower i))
    (hforeign : ∀ z : Bank, (¬ ∃ i : Fin 64, lower i = z) → U z = S z) :
    BitMachineClearBank.cleared resetBank
      (Function.update U slots.target answer) =
      Function.update S slots.target answer := by
  have htarget : slots.target=lower 29 := rfl
  funext z
  by_cases hz : z=slots.target
  · subst z
    have hnot : ¬ ∃ j, resetBank j = slots.target := by
      rw [htarget,reset_range]
      simp [retained]
    simp [BitMachineClearBank.cleared,hnot]
  rw [Function.update_of_ne hz]
  by_cases hlow : ∃ i : Fin 64, lower i=z
  · obtain ⟨i,rfl⟩ := hlow
    by_cases hp : retained i
    · have hnot : ¬∃j,resetBank j=lower i := by rw [reset_range]; exact not_not_intro hp
      simp only [BitMachineClearBank.cleared,if_neg hnot,Function.update_of_ne hz]
      exact hkeep i hp
    · have hy : ∃j,resetBank j=lower i := (reset_range i).2 hp
      simpa [BitMachineClearBank.cleared,hy] using (hclean i hp).symm
  · have hnot : ¬∃j,resetBank j=z := by
      rintro ⟨j,hj⟩
      obtain ⟨i,hi⟩ := reset_lower j
      exact hlow ⟨i,hi.trans hj⟩
    simp only [BitMachineClearBank.cleared,if_neg hnot,Function.update_of_ne hz]
    exact hforeign z hlow

#print axioms restore_eq
#print axioms physical_reset
end CurrentAdditive.GaussCellScratchReset
