import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.MatrixStage4Digits
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Private physical prefix for variable-bin Stage--4 column scalars. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarPrefix

open Turing BitMachineEncoding
open MatrixStage4ScalarPreparationOps

abbrev Stack := Fin 40

def inputBank (a s q L rx cy : ℕ) : Stack → List Bool :=
  fun j =>
    if j = 0 then List.replicate a true else
    if j = 1 then List.replicate s true else
    if j = 2 then List.replicate q true else
    if j = 3 then List.replicate L true else
    if j = 4 then List.replicate rx true else
    if j = 5 then List.replicate cy true else []

def powerSlots : MatrixUnaryPower.Stack ↪ Stack :=
  ⟨fun k => match k with
    | .inl 0 => 6
    | .inl 1 => 30
    | .inl _ => 31
    | .inr () => 0,
    by decide⟩

def powerProgram := unaryPowerProgram powerSlots

def poweredBank (S : Stack → List Bool) (a : ℕ) : Stack → List Bool :=
  Function.update S 6 (List.replicate (2^a) true)

theorem power_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 4*2^a + 5*a + 7,
      ((advance powerProgram)^[t])
        (⟨some (.inr false), ((false,false),none), inputBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none, ((false,false),none),
          poweredBank (inputBank a s q L rx cy) a⟩ := by
  simpa [powerProgram, powerSlots, poweredBank, inputBank] using
    unary_power_run powerSlots (inputBank a s q L rx cy) a
      (by simp [powerSlots, inputBank])
      (by simp [powerSlots, inputBank])
      (by simp [powerSlots, inputBank])
      (by simp [powerSlots, inputBank])

inductive PopLabel where
  | first | second
  deriving DecidableEq, Fintype

def popProgram : PopLabel → TM2.Stmt (fun _ : Stack => Bool) PopLabel Unit
  | .first => .pop 6 (fun _ _ => ()) (.goto (fun _ => .second))
  | .second => .pop 6 (fun _ _ => ()) .halt

theorem pop_run (S : Stack → List Bool) :
    ((advance popProgram)^[2])
      (⟨some .first, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) PopLabel Unit) =
      ⟨none, (), Function.update S 6 ((S 6).drop 2)⟩ := by
  change advance popProgram (advance popProgram
    (⟨some .first, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) PopLabel Unit)) = _
  simp only [advance, TM2.step, TM2.stepAux, popProgram,
    Option.getD_some]
  congr 1
  funext j
  by_cases hj : j = 6
  · subst j
    cases h : S 6 with
    | nil => rfl
    | cons _ xs =>
      cases xs with
      | nil => rfl
      | cons _ ys => rfl
  · simp [Function.update_of_ne hj]

def qoneBank (S : Stack → List Bool) (a : ℕ) : Stack → List Bool :=
  Function.update S 6 (List.replicate (Construction.qOne a) true)

theorem pop_power_run (a s q L rx cy : ℕ) :
    ((advance popProgram)^[2])
      (⟨some .first, (), poweredBank (inputBank a s q L rx cy) a⟩ :
        TM2.Cfg (fun _ : Stack => Bool) PopLabel Unit) =
      ⟨none, (), qoneBank (inputBank a s q L rx cy) a⟩ := by
  rw [pop_run]
  congr 1
  funext j
  by_cases hj : j = 6
  · subst j
    simp [qoneBank, poweredBank, Construction.qOne, List.drop_replicate]
  · simp [qoneBank, poweredBank, Function.update_of_ne hj]

def qoneProgram := BitMachineRawSequence.program powerProgram popProgram
  PopLabel.first ((false,false),none) ()

theorem qone_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 4*2^a + 5*a + 10,
      ((advance qoneProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inr false)),
          (((false,false),none),()), inputBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label MatrixUnaryPower.Label PopLabel)
            (MatrixUnaryPower.Control × Unit)) =
        ⟨none, (((false,false),none),()),
          qoneBank (inputBank a s q L rx cy) a⟩ := by
  obtain ⟨tp, htp, hp⟩ := power_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    powerProgram popProgram (.inr false) PopLabel.first
    ((false,false),none) ((false,false),none) () ()
    (inputBank a s q L rx cy)
    (poweredBank (inputBank a s q L rx cy) a)
    (qoneBank (inputBank a s q L rx cy) a)
    tp 2 hp (pop_power_run a s q L rx cy)
  exact ⟨t, by omega, by simpa only [qoneProgram] using hr⟩

def copyQSlots : Fin 3 ↪ Stack := ⟨![6,7,30], by decide⟩
def copySSlots : Fin 3 ↪ Stack := ⟨![1,7,30], by decide⟩
def copyQProgram := copyProgram copyQSlots
def copySProgram := copyProgram copySSlots

def copiedQBank (S : Stack → List Bool) (a : ℕ) : Stack → List Bool :=
  Function.update S 7 (List.replicate (Construction.qOne a) true)

def copiedSBank (S : Stack → List Bool) (a s : ℕ) : Stack → List Bool :=
  Function.update S 7 (List.replicate (Construction.qOne a + s) true)

theorem copy_q_run (a s q L rx cy : ℕ) :
    ((advance copyQProgram)^[2 * Construction.qOne a + 2])
      (⟨some .scan, none, qoneBank (inputBank a s q L rx cy) a⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, copiedQBank (qoneBank (inputBank a s q L rx cy) a) a⟩ := by
  have hr := copy_run copyQSlots (qoneBank (inputBank a s q L rx cy) a)
    (by simp [copyQSlots, qoneBank, inputBank])
  have hsource : (qoneBank (inputBank a s q L rx cy) a) (copyQSlots 0) =
      List.replicate (Construction.qOne a) true := by
    simp [qoneBank, copyQSlots]
  rw [hsource] at hr
  simpa [copyQProgram, copyQSlots, copiedQBank,
    qoneBank, inputBank] using hr

theorem copy_s_run (a s q L rx cy : ℕ) :
    ((advance copySProgram)^[2*s+2])
      (⟨some .scan, none,
          copiedQBank (qoneBank (inputBank a s q L rx cy) a) a⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none,
        copiedSBank (qoneBank (inputBank a s q L rx cy) a) a s⟩ := by
  let S := copiedQBank (qoneBank (inputBank a s q L rx cy) a) a
  have hr := copy_run copySSlots S
    (by simp [S, copySSlots, copiedQBank, qoneBank, inputBank])
  have hsource : S (copySSlots 0) = List.replicate s true := by
    simp [S, copySSlots, copiedQBank, qoneBank, inputBank]
  rw [hsource] at hr
  have hbank : Function.update S (copySSlots 1)
      (List.replicate s true ++ S (copySSlots 1)) =
      copiedSBank (qoneBank (inputBank a s q L rx cy) a) a s := by
    funext j
    by_cases hj : j = 7
    · subst j
      simp [S, copySSlots, copiedSBank, copiedQBank,
        List.replicate_append_replicate,
        Nat.add_comm s (Construction.qOne a)]
    · simp [S, copySSlots, copiedSBank, copiedQBank,
        Function.update_of_ne hj]
  simpa only [copySProgram, S, List.length_replicate, hbank] using hr

inductive PushLabel where | push
  deriving DecidableEq, Fintype

def pushProgram : PushLabel → TM2.Stmt (fun _ : Stack => Bool) PushLabel Unit
  | .push => .push 7 (fun _ => true) .halt

def lengthBank (S : Stack → List Bool) (a s : ℕ) : Stack → List Bool :=
  Function.update S 7 (List.replicate (Construction.firstLength a s) true)

theorem push_length_run (a s q L rx cy : ℕ) :
    (advance pushProgram)
      (⟨some .push, (),
        copiedSBank (qoneBank (inputBank a s q L rx cy) a) a s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) PushLabel Unit) =
      ⟨none, (), lengthBank (qoneBank (inputBank a s q L rx cy) a) a s⟩ := by
  simp only [advance, TM2.step, TM2.stepAux, pushProgram,
    Option.getD_some]
  congr 1
  funext j
  by_cases hj : j = 7
  · subst j
    simp only [lengthBank, copiedSBank, Function.update_self,
      Construction.firstLength]
    rw [show Construction.qOne a + (s + 1) =
      (Construction.qOne a + s) + 1 by omega, List.replicate_succ]
  · simp [lengthBank, copiedSBank, Function.update_of_ne hj]

def copyPairProgram := BitMachineRawSequence.program copyQProgram copySProgram
  BitMachineCopy.Label.scan none none

theorem copy_pair_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2 * Construction.qOne a + 2*s + 5,
      ((advance copyPairProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,none), qoneBank (inputBank a s q L rx cy) a⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
            (Option Bool × Option Bool)) =
        ⟨none, (none,none),
          copiedSBank (qoneBank (inputBank a s q L rx cy) a) a s⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    copyQProgram copySProgram BitMachineCopy.Label.scan
    BitMachineCopy.Label.scan none none none none
    (qoneBank (inputBank a s q L rx cy) a)
    (copiedQBank (qoneBank (inputBank a s q L rx cy) a) a)
    (copiedSBank (qoneBank (inputBank a s q L rx cy) a) a s)
    (2 * Construction.qOne a + 2) (2*s+2)
    (copy_q_run a s q L rx cy) (copy_s_run a s q L rx cy)
  exact ⟨t, by omega, by simpa only [copyPairProgram] using hr⟩

def lengthProgram := BitMachineRawSequence.program copyPairProgram pushProgram
  PushLabel.push (none,none) ()

theorem length_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2 * Construction.qOne a + 2*s + 7,
      ((advance lengthProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),()), qoneBank (inputBank a s q L rx cy) a⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
              PushLabel)
            ((Option Bool × Option Bool) × Unit)) =
        ⟨none, ((none,none),()),
          lengthBank (qoneBank (inputBank a s q L rx cy) a) a s⟩ := by
  obtain ⟨tp,htp,hp⟩ := copy_pair_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    copyPairProgram pushProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    PushLabel.push (none,none) (none,none) () ()
    (qoneBank (inputBank a s q L rx cy) a)
    (copiedSBank (qoneBank (inputBank a s q L rx cy) a) a s)
    (lengthBank (qoneBank (inputBank a s q L rx cy) a) a s)
    tp 1 hp (by simpa only [Function.iterate_one] using
      push_length_run a s q L rx cy)
  exact ⟨t, by omega, by simpa only [lengthProgram] using hr⟩

#print axioms power_run
#print axioms pop_power_run
#print axioms qone_run
#print axioms length_run

end EthInapproximability.CurrentPaper.ColumnScalarPrefix
