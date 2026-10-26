import CurrentAdditive.GaussParsedState32
import CurrentAdditive.GaussStepParseRun32
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast
import EthInapproximability.CurrentPaper.BitMachineRawSequence

namespace CurrentAdditive.GaussNextFieldsPrepare64
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := Fin 64
abbrev ResetLabel := Fin 31 ⊕ Unit
abbrev ResetControl := Unit × Option Bool

def resetBank (i : Fin 30) : Bank :=
  if h : i.val < 20 then ⟨i.val,by omega⟩
  else if h' : i.val < 21 then ⟨i.val+1,by omega⟩
  else ⟨i.val+2,by have hi:=i.isLt; omega⟩

theorem resetBank_injective : Function.Injective resetBank := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  unfold resetBank at hv
  split_ifs at hv <;> simp only at hv <;> omega

theorem resetBank_range (z : Bank) :
    (∃ i,resetBank i=z) ↔ z.val < 32 ∧ z.val≠20 ∧ z.val≠22 := by
  constructor
  · rintro ⟨i,rfl⟩
    unfold resetBank
    split_ifs <;> simp only <;> have hi:=i.isLt <;> omega
  · rintro ⟨hz,h20,h22⟩
    by_cases h : z.val < 20
    · refine ⟨⟨z.val,by omega⟩,?_⟩
      apply Fin.ext
      simp [resetBank,h]
    · by_cases h' : z.val < 22
      · have he : z.val=21 := by omega
        refine ⟨20,?_⟩
        apply Fin.ext
        simp [resetBank,he]
      · refine ⟨⟨z.val-2,by omega⟩,?_⟩
        apply Fin.ext
        simp [resetBank,show ¬z.val-2 < 20 by omega,
          show ¬z.val-2 < 21 by omega]
        omega

def resetProgram : ResetLabel → TM2.Stmt (fun _ : Bank => Bool) ResetLabel ResetControl
  | .inl i => if h : i.val < 30 then BitMachineClearBank.clearStep
      (resetBank ⟨i.val,h⟩) (.inl i) (.inl ⟨i.val+1,by omega⟩)
    else BitMachineClearBank.finishStep id (.inr ())
  | .inr () => .halt

def resetClock (S : Bank → List Bool) : Nat := ∑ i : Fin 30,(S (resetBank i)).length+32

theorem physical_reset (S : Bank → List Bool) :
    ((advance resetProgram)^[resetClock S])
      (⟨some (.inl 0),((),none),S⟩ : TM2.Cfg (fun _ : Bank => Bool) ResetLabel ResetControl) =
      ⟨none,((),none),BitMachineClearBank.cleared resetBank S⟩ := by
  have h := BitMachineClearBank.clear_bank_run resetProgram id (.inr ()) 30
    resetBank resetBank_injective Sum.inl
    (by intro i; simp [resetProgram,i.isLt]; rfl) (by simp [resetProgram]) () S
  unfold resetClock
  rw [show (∑ i : Fin 30,(S (resetBank i)).length)+32=
    ((∑ i : Fin 30,(S (resetBank i)).length)+30+1)+1 by omega,
    Function.iterate_succ_apply',h]
  rfl

def prepared (S : Bank → List Bool) : Bank → List Bool :=
  Function.update (BitMachineClearBank.cleared resetBank S) 30 (S 56)

def copyProgram := SourceClausePreservingBroadcast.program (56 : Bank) 63 [30]
def program := BitMachineRawSequence.program resetProgram copyProgram .scan ((),none) ((),none)
abbrev Label := BitMachineRawSequence.Label ResetLabel SourceClausePreservingBroadcast.Label
abbrev Control := BitMachineRawSequence.Control ResetControl (Unit × Option Bool)
def start : Label := BitMachineRawSequence.leftLabel (.inl 0)
def control : Control := (((),none),((),none))
def clock (S : Bank → List Bool) : Nat := resetClock S+2*(S 56).length+4

theorem physical_prepare (S : Bank → List Bool) (h63 : S 63=[]) :
    ∃ t≤clock S,((advance program)^[t])
      (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control) =
      ⟨none,control,prepared S⟩ := by
  let R := BitMachineClearBank.cleared resetBank S
  have h56 : R 56=S 56 := by
    simp only [R,BitMachineClearBank.cleared,resetBank_range]
    simp
  have h30 : R 30=[] := by
    simp only [R,BitMachineClearBank.cleared,resetBank_range]
    simp
  have hs : R 63=[] := by
    simp only [R,BitMachineClearBank.cleared,resetBank_range]
    simpa using h63
  have hcopy := SourceClausePreservingBroadcast.run_halt (56 : Bank) 63 [30]
    (by decide) (by decide) (by decide) (by decide) (S 56) R h56 hs
  have hresult : SourceClausePreservingBroadcast.result 56 63 [30] (S 56) R=prepared S := by
    funext z
    by_cases h : z=30
    · subst z
      rw [SourceClausePreservingBroadcast.target_written 56 63 [30]
        (by decide) (by decide) (by decide) (S 56) R 30 (by simp)]
      simp [prepared,R,h30]
    · have hp := SourceClausePreservingBroadcast.other_preserved
        (56 : Bank) 63 [30] (S 56) R z
      by_cases h56' : z=56
      · subst z
        rw [SourceClausePreservingBroadcast.source_restored 56 63 [30]
          (by decide) (S 56) R]
        simp [prepared,R,h56]
      · by_cases h63' : z=63
        · subst z
          rw [SourceClausePreservingBroadcast.temp_empty 56 63 [30] (S 56) R]
          simp only [prepared,Function.update_of_ne (by decide : (63 : Bank)≠30)]
          exact hs.symm
        · rw [hp h56' h63' (by simpa using h)]
          simp [prepared,h,R]
  rw [hresult] at hcopy
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs resetProgram copyProgram
    (.inl 0) .scan ((),none) ((),none) ((),none) ((),none)
    S R (prepared S) (resetClock S) (2*(S 56).length+3) (physical_reset S) hcopy
  exact ⟨t,by unfold clock; omega,he⟩

def foreign (tag matrix : List Bool) (z : Fin 32) : List Bool :=
  if z=20 then tag else if z=22 then matrix else []

theorem prepared_low {m k : Nat} (s : GaussControlTrace.State m k)
    (S : Bank → List Bool) (tag matrix : List Bool)
    (h56 : S 56=GaussControlTrace.statePacket s) (h20 : S 20=tag) (h22 : S 22=matrix) :
    (fun z : Fin 32 => prepared S ⟨z.val,by omega⟩)=
      (GaussStepParseRun32.raw s (foreign tag matrix)).stk := by
  funext z
  change prepared S ⟨z.val,by omega⟩=
    BitMachineStackEmbedding.bank GaussParsedState32.locate (foreign tag matrix)
      (BitMachineBankCodec.parserCfg (K := 4) (some (.scan 0)) none
        (fun _ => []) (GaussControlTrace.statePacket s) [] []).stk z
  by_cases hz : ∃ q,GaussParsedState32.locate q=z
  · obtain ⟨q,rfl⟩ := hz
    rw [BitMachineStackEmbedding.bank_at]
    cases q with
    | inl q => fin_cases q <;>
      simp [prepared,BitMachineClearBank.cleared,resetBank_range,
        GaussParsedState32.locate,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr q => fin_cases q <;>
      simp [prepared,BitMachineClearBank.cleared,resetBank_range,
        GaussParsedState32.locate,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,h56]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hz]
    have h30 : z≠30 := by
      intro he
      apply hz
      subst z
      exact ⟨.inr 0,rfl⟩
    by_cases h20z : z=20
    · subst z
      simpa [prepared,BitMachineClearBank.cleared,resetBank_range,foreign] using h20
    · by_cases h22z : z=22
      · subst z
        simpa [prepared,BitMachineClearBank.cleared,resetBank_range,foreign] using h22
      · have hz30 : z.val≠30 := fun he => h30 (Fin.ext he)
        have hz20 : z.val≠20 := fun he => h20z (Fin.ext he)
        have hz22 : z.val≠22 := fun he => h22z (Fin.ext he)
        have he : ∃ i,resetBank i=(⟨z.val,by omega⟩ : Bank) :=
          (resetBank_range _).2 ⟨z.isLt,hz20,hz22⟩
        have hne : (⟨z.val,by omega⟩ : Bank)≠30 := fun he => hz30 (congrArg Fin.val he)
        simp [prepared,BitMachineClearBank.cleared,he,foreign,h20z,h22z,hne]

#print axioms physical_prepare
#print axioms prepared_low
end
end CurrentAdditive.GaussNextFieldsPrepare64
