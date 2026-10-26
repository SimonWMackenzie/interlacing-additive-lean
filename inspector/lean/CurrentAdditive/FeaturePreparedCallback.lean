import CurrentAdditive.FeaturePrependPrepared
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-! One fixed physical control for the prepared three-word feature-prepend callback. -/

namespace CurrentAdditive.FeaturePreparedCallback

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec
open Turing Turing.TM2.Stmt BitMachineEncoding

noncomputable section

private noncomputable abbrev F := SourceListMachineWriter.framingMachine true

abbrev PStack := BitMachineBankSerialize.Stack 2
abbrev CStack := FeatureCountFieldSuccessor.Stack
abbrev JStack := FeaturePreparedJoin.Stack
abbrev Stack := PStack ⊕ (CStack ⊕ (Fin F.stackCount ⊕ (JStack ⊕ Fin 1)))

inductive CopyKind where
  | pair | header | framedPair | suffix
  deriving DecidableEq, Fintype

inductive Label where
  | pair : BitMachineBankSerialize.Label 2 → Label
  | count : FeatureCountFieldSuccessor.Label → Label
  | frame : Fin F.labelCount → Label
  | join : FeaturePreparedJoin.Label → Label
  | copyScan : CopyKind → Label
  | copyRestore : CopyKind → Label
  | startCount | startFrame | startJoin
  deriving DecidableEq, Fintype

abbrev StageControl := Option Bool ⊕
  (FeatureCountFieldSuccessor.Control ⊕
    (Fin F.controlCount ⊕ FeaturePreparedJoin.Control))
abbrev Control := StageControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def pairSlots : PStack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def countSlots : CStack ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)⟩
def frameSlots : Fin F.stackCount ↪ Stack :=
  ⟨fun k => .inr (.inr (.inl k)), by intro a b h; exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))⟩
def joinSlots : JStack ↪ Stack :=
  ⟨fun k => .inr (.inr (.inr (.inl k))), by intro a b h; exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))⟩

def pairOutput : Stack := pairSlots (.inr 2)
def countSource : Stack := countSlots 0
def countOutput : Stack := countSlots 2
noncomputable def frameInput : Stack := frameSlots F.input
noncomputable def frameOutput : Stack := frameSlots F.output
def joinHeader : Stack := joinSlots 0
def joinPair : Stack := joinSlots 1
def joinSuffix : Stack := joinSlots 2
def joinOutput : Stack := joinSlots 4
def temp : Stack := .inr (.inr (.inr (.inr 0)))


noncomputable def source : CopyKind → Stack
  | .pair => pairOutput
  | .header => countOutput
  | .framedPair => frameOutput
  | .suffix => countSource

noncomputable def target : CopyKind → Stack
  | .pair => frameInput
  | .header => joinHeader
  | .framedPair => joinPair
  | .suffix => joinSuffix

def next : CopyKind → Label
  | .pair => .startCount
  | .header => .copyScan .framedPair
  | .framedPair => .copyScan .suffix
  | .suffix => .startJoin

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .pair l => BitMachineStackEmbedding.stmt pairSlots Label.pair
      (fun v => (.inl v,none))
      (fun v => match v.1 with | .inl x => x | _ => none)
      (some (.copyScan .pair)) (BitMachineBankSerialize.program 2 l)
  | .count l => BitMachineStackEmbedding.stmt countSlots Label.count
      (fun v => (.inr (.inl v),none))
      (fun v => match v.1 with | .inr (.inl x) => x | _ => (true,none))
      (some .startFrame) (FeatureCountFieldSuccessor.program l)
  | .frame l => BitMachineStackEmbedding.stmt frameSlots Label.frame
      (fun v => (.inr (.inr (.inl v)),none))
      (fun v => match v.1 with | .inr (.inr (.inl x)) => x | _ => F.initial)
      (some (.copyScan .header)) (F.program l)
  | .join l => BitMachineStackEmbedding.stmt joinSlots Label.join
      (fun v => (.inr (.inr (.inr v)),none))
      (fun v => match v.1 with | .inr (.inr (.inr x)) => x | _ => ((),none))
      none (FeaturePreparedJoin.program l)
  | .copyScan i => BitMachineBroadcast.scanStep (source i) temp
      (.copyScan i) (.copyRestore i)
  | .copyRestore i => BitMachineBroadcast.restoreStep temp [target i]
      (.copyRestore i) (next i)
  | .startCount => load (fun _ => (.inr (.inl (true,none)),none))
      (goto (fun _ => .count .read))
  | .startFrame => load (fun _ => (.inr (.inr (.inl F.initial)),none))
      (goto (fun _ => .frame F.start))
  | .startJoin => load (fun _ => (.inr (.inr (.inr ((),none))),none))
      (goto (fun _ => .join .suffixScan))

def initialBank (j y : Nat) (c : List (Nat × Nat)) : Stack → List Bool :=
  fun k => if k = pairSlots (.inl 0) then j.bits else
    if k = pairSlots (.inl 1) then y.bits else
      if k = countSource then encodeFeature c else []

def initialCfg (j y : Nat) (c : List (Nat × Nat)) : Config :=
  ⟨some (.pair (.emit 0)), (.inl none,none), initialBank j y c⟩

def run (t : Nat) (z : Config) : Config := ((advance program)^[t]) z

theorem run_add (t u : Nat) (z : Config) :
    run (t+u) z = run u (run t z) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t z

private def pCfg (j y : Nat) :=
  BitMachineBankSerialize.cfg (some (.emit 0)) none
    (pairBank (j,y)) [] [] []

private theorem pair_initial (j y : Nat) (c : List (Nat × Nat)) :
    initialCfg j y c =
      BitMachineStackEmbedding.cfg pairSlots (initialBank j y c)
        Label.pair (fun v : Option Bool => (.inl v,none))
        (some (.copyScan .pair)) (pCfg j y) := by
  unfold initialCfg BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  symm
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  cases k with
  | inl k => fin_cases k <;> simp [initialBank, pCfg, pairBank,
      BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents,
      pairSlots, countSource]
  | inr k => fin_cases k <;> simp [initialBank, pCfg,
      BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents,
      pairSlots, countSource, countSlots]

private def pairAfter (j y : Nat) (c : List (Nat × Nat)) (t : Nat) :
    Stack → List Bool :=
  BitMachineStackEmbedding.bank pairSlots (initialBank j y c)
    (BitMachineBankSerialize.run t (pCfg j y)).stk

theorem pair_phase (j y : Nat) (c : List (Nat × Nat)) :
    ∃ t ≤ 2*(encodePair (j,y)).length+2,
      ∃ v : Option Bool, ∃ S : Stack → List Bool,
        run t (initialCfg j y c) =
          ⟨some (.copyScan .pair),(.inl v,none),S⟩ ∧
        S pairOutput = encodePair (j,y) ∧
        S countSource = encodeFeature c ∧
        (∀ k, (¬ ∃ p : PStack, pairSlots p = k) →
          S k = initialBank j y c k) := by
  obtain ⟨t,remaining,ht,hr⟩ :=
    CylinderPairWriter.physical_pair (j,y) [] []
  have hh : (BitMachineBankSerialize.run t (pCfg j y)).l = none := by
    change (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (pairBank (j,y)) [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs pairSlots
    (initialBank j y c) Label.pair
    (fun v : Option Bool => (.inl v,none))
    (fun v : Control => match v.1 with | .inl x => x | _ => none)
    (by intro v; rfl) (some (.copyScan .pair))
    (BitMachineBankSerialize.program 2) program (by intro l; rfl)
    (pCfg j y) t hh
  refine ⟨u,hu.trans ht,
    (BitMachineBankSerialize.run t (pCfg j y)).var,
    pairAfter j y c t,?_,?_,?_,?_⟩
  · rw [← pair_initial] at he
    have hh' : (((advance (BitMachineBankSerialize.program 2))^[t])
      (pCfg j y)).l = none := hh
    simpa only [run, pairAfter, BitMachineBankSerialize.run,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh'] using he
  · have ho := congrArg (fun z => z.stk (.inr 2)) hr
    simpa [pairAfter, pairOutput, pairSlots, pCfg,
      BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents] using
      (BitMachineStackEmbedding.bank_at pairSlots (initialBank j y c)
        (BitMachineBankSerialize.run t (pCfg j y)).stk (.inr 2)).trans ho
  · unfold pairAfter
    rw [BitMachineStackEmbedding.bank_outside]
    · simp [initialBank, countSource, countSlots, pairSlots]
    · rintro ⟨k,hk⟩
      cases hk
  · intro k hk
    exact BitMachineStackEmbedding.bank_outside pairSlots
      (initialBank j y c)
      (BitMachineBankSerialize.run t (pCfg j y)).stk k hk

theorem copy_phase (i : CopyKind) (v : StageControl)
    (S : Stack → List Bool) (bits : List Bool)
    (hs : S (source i) = bits) (ht : S (target i) = [])
    (htmp : S temp = []) :
    run (2*bits.length+2)
      ⟨some (.copyScan i),(v,none),S⟩ =
      ⟨some (next i),(v,none),
        BitMachineBroadcast.copied (source i) temp [target i] bits S⟩ := by
  apply BitMachineBroadcast.broadcast_run program (source i) temp
    (by cases i <;> simp [source, temp, pairOutput, countOutput,
      countSource, frameOutput, pairSlots, countSlots, frameSlots])
    [target i] (by simp)
    (by cases i <;> simp [source, target, pairOutput, countOutput,
      countSource, frameOutput, frameInput, joinHeader, joinPair,
      joinSuffix, pairSlots, countSlots, frameSlots, joinSlots])
    (by cases i <;> simp [target, temp, frameInput, joinHeader,
      joinPair, joinSuffix, frameSlots, joinSlots])
    (.copyScan i) (.copyRestore i) (next i) rfl rfl
    v none bits S hs htmp

theorem copied_target (i : CopyKind) (S : Stack → List Bool)
    (bits : List Bool) (ht : S (target i) = []) :
    BitMachineBroadcast.copied (source i) temp [target i] bits S
      (target i) = bits := by
  have h₁ : target i ≠ source i := by
    cases i <;> simp [source, target, pairOutput, countOutput,
      countSource, frameOutput, frameInput, joinHeader, joinPair,
      joinSuffix, pairSlots, countSlots, frameSlots, joinSlots]
  have h₂ : target i ≠ temp := by
    cases i <;> simp [target, temp, frameInput, joinHeader,
      joinPair, joinSuffix, frameSlots, joinSlots]
  simp [BitMachineBroadcast.copied, ht, h₁, h₂]

theorem copied_temp (i : CopyKind) (S : Stack → List Bool)
    (bits : List Bool) :
    BitMachineBroadcast.copied (source i) temp [target i] bits S temp = [] := by
  simp [BitMachineBroadcast.copied]

theorem copied_outside (i : CopyKind) (S : Stack → List Bool)
    (bits : List Bool) (k : Stack)
    (hk₁ : k ≠ source i) (hk₂ : k ≠ target i) (hk₃ : k ≠ temp) :
    BitMachineBroadcast.copied (source i) temp [target i] bits S k = S k := by
  simp [BitMachineBroadcast.copied, BitMachineBroadcast.prepend,
    hk₁, hk₂, hk₃]

theorem pair_copy_phase (j y : Nat) (c : List (Nat × Nat)) :
    ∃ t ≤ 4*(encodePair (j,y)).length+4,
      ∃ v : Option Bool, ∃ T : Stack → List Bool,
        run t (initialCfg j y c) =
          ⟨some .startCount,(.inl v,none),
            BitMachineBroadcast.copied (source .pair) temp [target .pair]
              (encodePair (j,y)) T⟩ ∧
        T pairOutput = encodePair (j,y) ∧
        (∀ k, (¬ ∃ p : PStack, pairSlots p = k) →
          T k = initialBank j y c k) := by
  obtain ⟨t,ht,v,T,hphase,hpair,_,houtside⟩ := pair_phase j y c
  have htarget : T (target .pair) = [] := by
    rw [houtside]
    · simp [initialBank, target, frameInput, frameSlots, pairSlots,
        countSource, countSlots]
    · rintro ⟨p,hp⟩
      cases hp
  have htemp : T temp = [] := by
    rw [houtside]
    · simp [initialBank, temp, pairSlots, countSource, countSlots]
    · rintro ⟨p,hp⟩
      cases hp
  have hc := copy_phase .pair (.inl v) T (encodePair (j,y))
    (by simpa [source] using hpair) htarget htemp
  refine ⟨t+(2*(encodePair (j,y)).length+2), by omega,
    v,T,?_,hpair,houtside⟩
  rw [run_add, hphase]
  exact hc

private theorem feature_old_bytes (c : List (Nat × Nat)) :
    encodeFeature c =
      EncodedCommunication.natField c.length ++ FeaturePrependPrepared.oldSuffix c := by
  simp [encodeFeature, CodeDCodecV2.encodeItems, SourceListEncoding.encode,
    FeaturePrependPrepared.oldSuffix]

theorem count_phase (c : List (Nat × Nat))
    (S : Stack → List Bool)
    (hsource : S countSource = encodeFeature c)
    (hacc : S (countSlots 1) = [])
    (hout : S countOutput = []) :
    ∃ t ≤ 6*((encodeFeature c).length+1),
      ∃ v : FeatureCountFieldSuccessor.Control, ∃ T : Stack → List Bool,
        run t ⟨some (.count .read),(.inr (.inl (true,none)),none),S⟩ =
          ⟨some .startFrame,(.inr (.inl v),none),T⟩ ∧
        T countSource = FeaturePrependPrepared.oldSuffix c ∧
        T countOutput = EncodedCommunication.natField (c.length+1) ∧
        (∀ k, (¬ ∃ p : CStack, countSlots p = k) → T k = S k) := by
  let q := FeatureCountFieldSuccessor.cfg (some .read) (true,none)
    (encodeFeature c) [] []
  have henc := feature_old_bytes c
  obtain ⟨t,ht,hh,hsrc,hout'⟩ :=
    FeatureCountFieldSuccessor.canonical_run c.length
      (FeaturePrependPrepared.oldSuffix c)
  have hq : q = FeatureCountFieldSuccessor.cfg (some .read) (true,none)
      (EncodedCommunication.natField c.length ++
        FeaturePrependPrepared.oldSuffix c) [] [] := by
    simp [q, henc]
  have hhalt : (FeatureCountFieldSuccessor.run t q).l = none := by
    rw [hq]
    exact hh
  have hstart :
      (⟨some (.count .read),(.inr (.inl (true,none)),none),S⟩ : Config) =
      BitMachineStackEmbedding.cfg countSlots S Label.count
        (fun v : FeatureCountFieldSuccessor.Control => (.inr (.inl v),none))
        (some .startFrame) q := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg
    congr 1
    symm
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k
    · simpa [q, FeatureCountFieldSuccessor.cfg, countSource] using hsource.symm
    · simpa [q, FeatureCountFieldSuccessor.cfg] using hacc.symm
    · simpa [q, FeatureCountFieldSuccessor.cfg, countOutput] using hout.symm
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs countSlots S
    Label.count
    (fun v : FeatureCountFieldSuccessor.Control => (.inr (.inl v),none))
    (fun v : Control => match v.1 with | .inr (.inl x) => x | _ => (true,none))
    (by intro v; rfl) (some .startFrame)
    FeatureCountFieldSuccessor.program program (by intro l; rfl)
    q t (by simpa only [FeatureCountFieldSuccessor.run] using hhalt)
  let T := BitMachineStackEmbedding.bank countSlots S
    (FeatureCountFieldSuccessor.run t q).stk
  refine ⟨u, hu.trans (by simpa [henc] using ht),
    (FeatureCountFieldSuccessor.run t q).var,T,?_,?_,?_,?_⟩
  · rw [← hstart] at he
    have hh' : (((advance FeatureCountFieldSuccessor.program)^[t]) q).l = none := hhalt
    simpa only [run, T, FeatureCountFieldSuccessor.run,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh'] using he
  · simpa only [T] using
      (BitMachineStackEmbedding.bank_at countSlots S
        (FeatureCountFieldSuccessor.run t q).stk (0 : CStack)).trans
        (by rw [hq]; exact hsrc)
  · simpa only [T] using
      (BitMachineStackEmbedding.bank_at countSlots S
        (FeatureCountFieldSuccessor.run t q).stk (2 : CStack)).trans
        (by rw [hq]; exact hout')
  · intro k hk
    exact BitMachineStackEmbedding.bank_outside countSlots S
      (FeatureCountFieldSuccessor.run t q).stk k hk

#print axioms count_phase

theorem frame_phase (j y : Nat) (S : Stack → List Bool)
    (hinput : S frameInput = encodePair (j,y))
    (hother : ∀ k : Fin F.stackCount, k ≠ F.input → S (frameSlots k) = []) :
    ∃ t ≤ (UnaryBinaryEncoding.coefficient+7)*
      ((encodePair (j,y)).length+1)^2,
      ∃ v : Fin F.controlCount, ∃ T : Stack → List Bool,
        run t ⟨some (.frame F.start),(.inr (.inr (.inl F.initial)),none),S⟩ =
          ⟨some (.copyScan .header),(.inr (.inr (.inl v)),none),T⟩ ∧
        T frameOutput = FeaturePrependPrepared.pairField j y ∧
        (∀ k, (¬ ∃ p : Fin F.stackCount, frameSlots p = k) → T k = S k) := by
  let bits := encodePair (j,y)
  let bound := (UnaryBinaryEncoding.coefficient+7)*(bits.length+1)^2
  have hrun := BitMachine.outputsWithin_at_bound F
    (FeaturePairPrepared.pair_frame_outputs j y)
  have hh : (F.run bound (F.init bits)).l = none := hrun.1
  have ho : (F.run bound (F.init bits)).stk F.output =
      FeaturePrependPrepared.pairField j y := by
    simpa [bits, bound, FeaturePrependPrepared.pairField] using hrun.2
  have hstart :
      (⟨some (.frame F.start),(.inr (.inr (.inl F.initial)),none),S⟩ : Config) =
      BitMachineStackEmbedding.cfg frameSlots S Label.frame
        (fun v : Fin F.controlCount => (.inr (.inr (.inl v)),none))
        (some (.copyScan .header)) (F.init bits) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg
    congr 1
    symm
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    by_cases hk : k = F.input
    · subst k
      simpa [BitMachine.Machine.init, frameInput] using hinput.symm
    · simpa [BitMachine.Machine.init, hk] using (hother k hk).symm
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs frameSlots S
    Label.frame
    (fun v : Fin F.controlCount => (.inr (.inr (.inl v)),none))
    (fun v : Control => match v.1 with | .inr (.inr (.inl x)) => x | _ => F.initial)
    (by intro v; rfl) (some (.copyScan .header))
    F.program program (by intro l; rfl) (F.init bits) bound hh
  let T := BitMachineStackEmbedding.bank frameSlots S
    (F.run bound (F.init bits)).stk
  refine ⟨u,hu,(F.run bound (F.init bits)).var,T,?_,?_,?_⟩
  · rw [← hstart] at he
    have hh' : (((advance F.program)^[bound]) (F.init bits)).l = none := hh
    simpa only [run, T, BitMachine.Machine.run, BitMachine.Machine.step,
      advance, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hh'] using he
  · exact (BitMachineStackEmbedding.bank_at frameSlots S
      (F.run bound (F.init bits)).stk F.output).trans ho
  · intro k hk
    exact BitMachineStackEmbedding.bank_outside frameSlots S
      (F.run bound (F.init bits)).stk k hk

#print axioms frame_phase

theorem join_phase (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool)
    (hheader : S joinHeader = EncodedCommunication.natField (c.length+1))
    (hpair : S joinPair = FeaturePrependPrepared.pairField j y)
    (hsuffix : S joinSuffix = FeaturePrependPrepared.oldSuffix c)
    (htemp : S (joinSlots 3) = []) (hout : S joinOutput = []) :
    ∃ t ≤ 2*((EncodedCommunication.natField (c.length+1)).length+
        (FeaturePrependPrepared.pairField j y).length+
        (FeaturePrependPrepared.oldSuffix c).length)+7,
      ∃ v : FeaturePreparedJoin.Control, ∃ T : Stack → List Bool,
        run t ⟨some (.join .suffixScan),
          (.inr (.inr (.inr ((),none))),none),S⟩ =
          ⟨none,(.inr (.inr (.inr v)),none),T⟩ ∧
        T joinOutput = encodeFeature ((j,y)::c) := by
  let header := EncodedCommunication.natField (c.length+1)
  let pair := FeaturePrependPrepared.pairField j y
  let suffix := FeaturePrependPrepared.oldSuffix c
  let bound := 2*suffix.length+2 + (2*pair.length+2) +
    (2*header.length+2) + 1
  let q : TM2.Cfg (fun _ : JStack => Bool)
      FeaturePreparedJoin.Label FeaturePreparedJoin.Control :=
    ⟨some .suffixScan,((),none),FeaturePreparedJoin.initialBank header pair suffix⟩
  have hrun := FeaturePreparedJoin.prepared_run header pair suffix
  have hh : (FeaturePreparedJoin.run bound q).l = none := hrun.1
  have ho : (FeaturePreparedJoin.run bound q).stk 4 =
      encodeFeature ((j,y)::c) := by
    simpa only [FeaturePrependPrepared.encodeFeature_cons] using hrun.2
  have hstart :
      (⟨some (.join .suffixScan),
        (.inr (.inr (.inr ((),none))),none),S⟩ : Config) =
      BitMachineStackEmbedding.cfg joinSlots S Label.join
        (fun v : FeaturePreparedJoin.Control => (.inr (.inr (.inr v)),none))
        none q := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg
    congr 1
    symm
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k
    · simpa [q, FeaturePreparedJoin.initialBank, joinHeader] using hheader.symm
    · simpa [q, FeaturePreparedJoin.initialBank, joinPair] using hpair.symm
    · simpa [q, FeaturePreparedJoin.initialBank, joinSuffix] using hsuffix.symm
    · simpa [q, FeaturePreparedJoin.initialBank] using htemp.symm
    · simpa [q, FeaturePreparedJoin.initialBank, joinOutput] using hout.symm
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs joinSlots S
    Label.join
    (fun v : FeaturePreparedJoin.Control => (.inr (.inr (.inr v)),none))
    (fun v : Control => match v.1 with | .inr (.inr (.inr x)) => x | _ => ((),none))
    (by intro v; rfl) none
    FeaturePreparedJoin.program program (by intro l; rfl)
    q bound (by simpa only [FeaturePreparedJoin.run] using hh)
  let T := BitMachineStackEmbedding.bank joinSlots S
    (FeaturePreparedJoin.run bound q).stk
  refine ⟨u,by dsimp [bound,header,pair,suffix] at hu ⊢; omega,
    (FeaturePreparedJoin.run bound q).var,T,?_,?_⟩
  · rw [← hstart] at he
    have hh' : (((advance FeaturePreparedJoin.program)^[bound]) q).l = none := hh
    simpa only [run, T, FeaturePreparedJoin.run,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh'] using he
  · exact (BitMachineStackEmbedding.bank_at joinSlots S
      (FeaturePreparedJoin.run bound q).stk (4 : JStack)).trans ho

#print axioms join_phase

def ReadyCount (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) : Prop :=
  S countSource = encodeFeature c ∧
  S (countSlots 1) = [] ∧ S countOutput = [] ∧
  S frameInput = encodePair (j,y) ∧
  (∀ k : Fin F.stackCount, k ≠ F.input → S (frameSlots k) = []) ∧
  (∀ k : JStack, S (joinSlots k) = []) ∧ S temp = []

def ReadyFrame (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) : Prop :=
  S countSource = FeaturePrependPrepared.oldSuffix c ∧
  S countOutput = EncodedCommunication.natField (c.length+1) ∧
  S frameInput = encodePair (j,y) ∧
  (∀ k : Fin F.stackCount, k ≠ F.input → S (frameSlots k) = []) ∧
  (∀ k : JStack, S (joinSlots k) = []) ∧ S temp = []

def ReadyCopies (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) : Prop :=
  S countSource = FeaturePrependPrepared.oldSuffix c ∧
  S countOutput = EncodedCommunication.natField (c.length+1) ∧
  S frameOutput = FeaturePrependPrepared.pairField j y ∧
  (∀ k : JStack, S (joinSlots k) = []) ∧ S temp = []

def ReadyCopyPair (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) : Prop :=
  S joinHeader = EncodedCommunication.natField (c.length+1) ∧
  S frameOutput = FeaturePrependPrepared.pairField j y ∧
  S countSource = FeaturePrependPrepared.oldSuffix c ∧
  S joinPair = [] ∧ S joinSuffix = [] ∧
  S (joinSlots 3) = [] ∧ S joinOutput = [] ∧ S temp = []

def ReadyCopySuffix (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) : Prop :=
  S joinHeader = EncodedCommunication.natField (c.length+1) ∧
  S joinPair = FeaturePrependPrepared.pairField j y ∧
  S countSource = FeaturePrependPrepared.oldSuffix c ∧
  S joinSuffix = [] ∧ S (joinSlots 3) = [] ∧
  S joinOutput = [] ∧ S temp = []

def ReadyJoin (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) : Prop :=
  S joinHeader = EncodedCommunication.natField (c.length+1) ∧
  S joinPair = FeaturePrependPrepared.pairField j y ∧
  S joinSuffix = FeaturePrependPrepared.oldSuffix c ∧
  S (joinSlots 3) = [] ∧ S joinOutput = []

theorem copy_pair_ready (j y : Nat) (c : List (Nat × Nat))
    (T : Stack → List Bool)
    (hpair : T pairOutput = encodePair (j,y))
    (houtside : ∀ k, (¬ ∃ p : PStack, pairSlots p = k) →
      T k = initialBank j y c k) :
    ReadyCount j y c
      (BitMachineBroadcast.copied (source .pair) temp [target .pair]
        (encodePair (j,y)) T) := by
  let R := BitMachineBroadcast.copied (source .pair) temp [target .pair]
    (encodePair (j,y)) T
  have hT (k : Stack) (hk : ¬ ∃ p : PStack, pairSlots p = k) :
      T k = initialBank j y c k := houtside k hk
  have hR (k : Stack) (h₁ : k ≠ source .pair)
      (h₂ : k ≠ target .pair) (h₃ : k ≠ temp) : R k = T k :=
    copied_outside .pair T (encodePair (j,y)) k h₁ h₂ h₃
  have htarget : T (target .pair) = [] := by
    rw [hT]
    · simp [initialBank, target, frameInput, frameSlots,
        pairSlots, countSource, countSlots]
    · rintro ⟨p,hp⟩; cases hp
  dsimp [ReadyCount]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change R countSource = encodeFeature c
    rw [hR, hT]
    · simp [initialBank, countSource, countSlots, pairSlots]
    · rintro ⟨p,hp⟩; cases hp
    · simp [countSource, countSlots, source, pairOutput, pairSlots]
    · simp [countSource, countSlots, target, frameInput, frameSlots]
    · simp [countSource, countSlots, temp]
  · change R (countSlots 1) = []
    rw [hR, hT]
    · simp [initialBank, countSlots, pairSlots, countSource]
    · rintro ⟨p,hp⟩; cases hp
    · simp [countSlots, source, pairOutput, pairSlots]
    · simp [countSlots, target, frameInput, frameSlots]
    · simp [countSlots, temp]
  · change R countOutput = []
    rw [hR, hT]
    · simp [initialBank, countOutput, countSlots, pairSlots, countSource]
    · rintro ⟨p,hp⟩; cases hp
    · simp [countOutput, countSlots, source, pairOutput, pairSlots]
    · simp [countOutput, countSlots, target, frameInput, frameSlots]
    · simp [countOutput, countSlots, temp]
  · exact copied_target .pair T (encodePair (j,y)) htarget
  · intro k hk
    change R (frameSlots k) = []
    rw [hR, hT]
    · simp [initialBank, frameSlots, pairSlots, countSource, countSlots]
    · rintro ⟨p,hp⟩; cases hp
    · simp [frameSlots, source, pairOutput, pairSlots]
    · simpa [target, frameInput] using hk
    · simp [frameSlots, temp]
  · intro k
    change R (joinSlots k) = []
    rw [hR, hT]
    · simp [initialBank, joinSlots, pairSlots, countSource, countSlots]
    · rintro ⟨p,hp⟩; cases hp
    · simp [joinSlots, source, pairOutput, pairSlots]
    · simp [joinSlots, target, frameInput, frameSlots]
    · simp [joinSlots, temp]
  · exact copied_temp .pair T (encodePair (j,y))

theorem initial_to_count (j y : Nat) (c : List (Nat × Nat)) :
    ∃ t ≤ 4*(encodePair (j,y)).length+5,
      ∃ S : Stack → List Bool,
        run t (initialCfg j y c) =
          ⟨some (.count .read),(.inr (.inl (true,none)),none),S⟩ ∧
        ReadyCount j y c S := by
  obtain ⟨t,ht,v,T,hr,hpair,houtside⟩ := pair_copy_phase j y c
  let S := BitMachineBroadcast.copied (source .pair) temp [target .pair]
    (encodePair (j,y)) T
  refine ⟨t+1,by omega,S,?_,copy_pair_ready j y c T hpair houtside⟩
  rw [run_add, hr]
  simp [S, run, program, advance, TM2.step, TM2.stepAux]

#print axioms initial_to_count

theorem count_ready_frame (j y : Nat) (c : List (Nat × Nat))
    (S T : Stack → List Bool)
    (hready : ReadyCount j y c S)
    (hsource : T countSource = FeaturePrependPrepared.oldSuffix c)
    (hheader : T countOutput = EncodedCommunication.natField (c.length+1))
    (houtside : ∀ k, (¬ ∃ p : CStack, countSlots p = k) → T k = S k) :
    ReadyFrame j y c T := by
  rcases hready with ⟨_,_,_,hframe,hother,hjoin,htemp⟩
  refine ⟨hsource,hheader,?_,?_,?_,?_⟩
  · rw [houtside]
    · exact hframe
    · rintro ⟨p,hp⟩; cases hp
  · intro k hk
    rw [houtside]
    · exact hother k hk
    · rintro ⟨p,hp⟩; cases hp
  · intro k
    rw [houtside]
    · exact hjoin k
    · rintro ⟨p,hp⟩; cases hp
  · rw [houtside]
    · exact htemp
    · rintro ⟨p,hp⟩; cases hp

theorem initial_to_frame (j y : Nat) (c : List (Nat × Nat)) :
    ∃ t ≤ 4*(encodePair (j,y)).length+6 +
      6*((encodeFeature c).length+1),
      ∃ S : Stack → List Bool,
        run t (initialCfg j y c) =
          ⟨some (.frame F.start),(.inr (.inr (.inl F.initial)),none),S⟩ ∧
        ReadyFrame j y c S := by
  obtain ⟨t₁,ht₁,S₁,h₁,r₁⟩ := initial_to_count j y c
  obtain ⟨t₂,ht₂,v,S₂,h₂,hsource,hheader,houtside⟩ :=
    count_phase c S₁ r₁.1 r₁.2.1 r₁.2.2.1
  refine ⟨t₁+t₂+1,by omega,S₂,?_,
    count_ready_frame j y c S₁ S₂ r₁ hsource hheader houtside⟩
  rw [run_add (t₁+t₂) 1, run_add t₁ t₂, h₁, h₂]
  simp [run, program, advance, TM2.step, TM2.stepAux]

#print axioms initial_to_frame

theorem frame_ready_copies (j y : Nat) (c : List (Nat × Nat))
    (S T : Stack → List Bool)
    (hready : ReadyFrame j y c S)
    (hpair : T frameOutput = FeaturePrependPrepared.pairField j y)
    (houtside : ∀ k, (¬ ∃ p : Fin F.stackCount, frameSlots p = k) → T k = S k) :
    ReadyCopies j y c T := by
  rcases hready with ⟨hsource,hheader,_,_,hjoin,htemp⟩
  refine ⟨?_,?_,hpair,?_,?_⟩
  · rw [houtside]
    · exact hsource
    · rintro ⟨p,hp⟩; cases hp
  · rw [houtside]
    · exact hheader
    · rintro ⟨p,hp⟩; cases hp
  · intro k
    rw [houtside]
    · exact hjoin k
    · rintro ⟨p,hp⟩; cases hp
  · rw [houtside]
    · exact htemp
    · rintro ⟨p,hp⟩; cases hp

theorem initial_to_copies (j y : Nat) (c : List (Nat × Nat)) :
    ∃ t ≤ 4*(encodePair (j,y)).length+6 +
      6*((encodeFeature c).length+1) +
      (UnaryBinaryEncoding.coefficient+7)*((encodePair (j,y)).length+1)^2,
      ∃ v : Fin F.controlCount, ∃ S : Stack → List Bool,
        run t (initialCfg j y c) =
          ⟨some (.copyScan .header),(.inr (.inr (.inl v)),none),S⟩ ∧
        ReadyCopies j y c S := by
  obtain ⟨t₁,ht₁,S₁,h₁,r₁⟩ := initial_to_frame j y c
  obtain ⟨t₂,ht₂,v,S₂,h₂,hpair,houtside⟩ :=
    frame_phase j y S₁ r₁.2.2.1 r₁.2.2.2.1
  refine ⟨t₁+t₂,by omega,v,S₂,?_,
    frame_ready_copies j y c S₁ S₂ r₁ hpair houtside⟩
  rw [run_add, h₁]
  exact h₂

#print axioms initial_to_copies

theorem copy_header_ready (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) (h : ReadyCopies j y c S) :
    ReadyCopyPair j y c
      (BitMachineBroadcast.copied (source .header) temp [target .header]
        (EncodedCommunication.natField (c.length+1)) S) := by
  rcases h with ⟨hsource,hheader,hpair,hjoin,htemp⟩
  let T := BitMachineBroadcast.copied (source .header) temp [target .header]
    (EncodedCommunication.natField (c.length+1)) S
  have hpres (k : Stack) (h₁ : k ≠ source .header)
      (h₂ : k ≠ target .header) (h₃ : k ≠ temp) : T k = S k :=
    copied_outside .header S _ k h₁ h₂ h₃
  change T joinHeader = _ ∧ T frameOutput = _ ∧
    T countSource = _ ∧ T joinPair = [] ∧ T joinSuffix = [] ∧
    T (joinSlots 3) = [] ∧ T joinOutput = [] ∧ T temp = []
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact copied_target .header S _ (by simpa [target,joinHeader] using hjoin 0)
  · rw [hpres]
    · exact hpair
    all_goals simp [source,target,frameOutput,countOutput,
      frameSlots,countSlots,joinHeader,joinSlots,temp]
  · rw [hpres]
    · exact hsource
    all_goals simp [source,target,countSource,countOutput,
      countSlots,joinHeader,joinSlots,temp]
  · rw [hpres]
    · exact hjoin 1
    all_goals simp [source,target,joinPair,joinHeader,
      countOutput,countSlots,joinSlots,temp]
  · rw [hpres]
    · exact hjoin 2
    all_goals simp [source,target,joinSuffix,joinHeader,
      countOutput,countSlots,joinSlots,temp]
  · rw [hpres]
    · exact hjoin 3
    all_goals simp [source,target,joinHeader,
      countOutput,countSlots,joinSlots,temp]
  · rw [hpres]
    · exact hjoin 4
    all_goals simp [source,target,joinOutput,joinHeader,
      countOutput,countSlots,joinSlots,temp]
  · exact copied_temp .header S _

#print axioms copy_header_ready

theorem copy_framed_ready (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) (h : ReadyCopyPair j y c S) :
    ReadyCopySuffix j y c
      (BitMachineBroadcast.copied (source .framedPair) temp [target .framedPair]
        (FeaturePrependPrepared.pairField j y) S) := by
  rcases h with ⟨hheader,hpair,hsource,hempty,hss,htmpj,hout,htemp⟩
  let T := BitMachineBroadcast.copied (source .framedPair) temp
    [target .framedPair] (FeaturePrependPrepared.pairField j y) S
  have hpres (k : Stack) (h₁ : k ≠ source .framedPair)
      (h₂ : k ≠ target .framedPair) (h₃ : k ≠ temp) : T k = S k :=
    copied_outside .framedPair S _ k h₁ h₂ h₃
  change T joinHeader = _ ∧ T joinPair = _ ∧
    T countSource = _ ∧ T joinSuffix = [] ∧
    T (joinSlots 3) = [] ∧ T joinOutput = [] ∧ T temp = []
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hpres]
    · exact hheader
    all_goals simp [source,target,frameOutput,frameSlots,
      joinHeader,joinPair,joinSlots,temp]
  · exact copied_target .framedPair S _ (by simpa [target,joinPair] using hempty)
  · rw [hpres]
    · exact hsource
    all_goals simp [source,target,countSource,countSlots,
      frameOutput,frameSlots,joinPair,joinSlots,temp]
  · rw [hpres]
    · exact hss
    all_goals simp [source,target,joinSuffix,joinPair,
      frameOutput,frameSlots,joinSlots,temp]
  · rw [hpres]
    · exact htmpj
    all_goals simp [source,target,joinPair,
      frameOutput,frameSlots,joinSlots,temp]
  · rw [hpres]
    · exact hout
    all_goals simp [source,target,joinOutput,joinPair,
      frameOutput,frameSlots,joinSlots,temp]
  · exact copied_temp .framedPair S _

theorem copy_suffix_ready (j y : Nat) (c : List (Nat × Nat))
    (S : Stack → List Bool) (h : ReadyCopySuffix j y c S) :
    ReadyJoin j y c
      (BitMachineBroadcast.copied (source .suffix) temp [target .suffix]
        (FeaturePrependPrepared.oldSuffix c) S) := by
  rcases h with ⟨hheader,hpair,hsource,hempty,htmpj,hout,htemp⟩
  let T := BitMachineBroadcast.copied (source .suffix) temp [target .suffix]
    (FeaturePrependPrepared.oldSuffix c) S
  have hpres (k : Stack) (h₁ : k ≠ source .suffix)
      (h₂ : k ≠ target .suffix) (h₃ : k ≠ temp) : T k = S k :=
    copied_outside .suffix S _ k h₁ h₂ h₃
  change T joinHeader = _ ∧ T joinPair = _ ∧
    T joinSuffix = _ ∧ T (joinSlots 3) = [] ∧ T joinOutput = []
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hpres]
    · exact hheader
    all_goals simp [source,target,countSource,countSlots,
      joinHeader,joinSuffix,joinSlots,temp]
  · rw [hpres]
    · exact hpair
    all_goals simp [source,target,countSource,countSlots,
      joinPair,joinSuffix,joinSlots,temp]
  · exact copied_target .suffix S _ (by simpa [target,joinSuffix] using hempty)
  · rw [hpres]
    · exact htmpj
    all_goals simp [source,target,countSource,countSlots,
      joinSuffix,joinSlots,temp]
  · rw [hpres]
    · exact hout
    all_goals simp [source,target,countSource,countSlots,
      joinOutput,joinSuffix,joinSlots,temp]

#print axioms copy_framed_ready
#print axioms copy_suffix_ready

theorem copy_chain (j y : Nat) (c : List (Nat × Nat))
    (v : Fin F.controlCount) (S : Stack → List Bool)
    (hready : ReadyCopies j y c S) :
    ∃ t ≤ 2*(EncodedCommunication.natField (c.length+1)).length+2 +
      (2*(FeaturePrependPrepared.pairField j y).length+2) +
      (2*(FeaturePrependPrepared.oldSuffix c).length+2),
      ∃ T : Stack → List Bool,
        run t ⟨some (.copyScan .header),
          (.inr (.inr (.inl v)),none),S⟩ =
          ⟨some .startJoin,(.inr (.inr (.inl v)),none),T⟩ ∧
        ReadyJoin j y c T := by
  let header := EncodedCommunication.natField (c.length+1)
  let pair := FeaturePrependPrepared.pairField j y
  let suffix := FeaturePrependPrepared.oldSuffix c
  let S₁ := BitMachineBroadcast.copied (source .header) temp
    [target .header] header S
  let S₂ := BitMachineBroadcast.copied (source .framedPair) temp
    [target .framedPair] pair S₁
  let S₃ := BitMachineBroadcast.copied (source .suffix) temp
    [target .suffix] suffix S₂
  have h₁ : ReadyCopyPair j y c S₁ :=
    copy_header_ready j y c S hready
  have h₂ : ReadyCopySuffix j y c S₂ :=
    copy_framed_ready j y c S₁ h₁
  have h₃ : ReadyJoin j y c S₃ :=
    copy_suffix_ready j y c S₂ h₂
  have r₁ := copy_phase .header (.inr (.inr (.inl v))) S header
    (by simpa [header,source] using hready.2.1)
    (by simpa [header,target] using hready.2.2.2.1 0)
    hready.2.2.2.2
  have r₂ := copy_phase .framedPair (.inr (.inr (.inl v))) S₁ pair
    (by simpa [pair,source] using h₁.2.1)
    (by simpa [pair,target] using h₁.2.2.2.1)
    h₁.2.2.2.2.2.2.2
  have r₃ := copy_phase .suffix (.inr (.inr (.inl v))) S₂ suffix
    (by simpa [suffix,source] using h₂.2.2.1)
    (by simpa [suffix,target] using h₂.2.2.2.1)
    h₂.2.2.2.2.2.2
  refine ⟨(2*header.length+2)+(2*pair.length+2)+
    (2*suffix.length+2), by rfl,S₃,?_,h₃⟩
  rw [show (2*header.length+2)+(2*pair.length+2)+
    (2*suffix.length+2) =
    (2*header.length+2)+((2*pair.length+2)+(2*suffix.length+2)) by omega]
  rw [run_add (2*header.length+2) ((2*pair.length+2)+(2*suffix.length+2)),
    r₁]
  change run ((2*pair.length+2)+(2*suffix.length+2))
    ⟨some (.copyScan .framedPair),(.inr (.inr (.inl v)),none),S₁⟩ = _
  rw [run_add, r₂]
  exact r₃

#print axioms copy_chain

def preparedClock (j y : Nat) (c : List (Nat × Nat)) : Nat :=
  let pairBytes := encodePair (j,y)
  let header := EncodedCommunication.natField (c.length+1)
  let pairField := FeaturePrependPrepared.pairField j y
  let suffix := FeaturePrependPrepared.oldSuffix c
  (4*pairBytes.length+6 + 6*((encodeFeature c).length+1) +
    (UnaryBinaryEncoding.coefficient+7)*(pairBytes.length+1)^2) +
  ((2*header.length+2)+(2*pairField.length+2)+(2*suffix.length+2)) +
  1 + (2*(header.length+pairField.length+suffix.length)+7)

theorem pair_prepend_prepared_run (j y : Nat) (c : List (Nat × Nat)) :
    ∃ t ≤ preparedClock j y c,
      let z := run t (initialCfg j y c)
      z.l = none ∧ z.stk joinOutput = encodeFeature ((j,y)::c) := by
  obtain ⟨t₁,ht₁,v,S₁,h₁,r₁⟩ := initial_to_copies j y c
  obtain ⟨t₂,ht₂,S₂,h₂,r₂⟩ := copy_chain j y c v S₁ r₁
  obtain ⟨t₃,ht₃,v₃,S₃,h₃,hout⟩ :=
    join_phase j y c S₂ r₂.1 r₂.2.1 r₂.2.2.1
      r₂.2.2.2.1 r₂.2.2.2.2
  refine ⟨t₁+t₂+1+t₃,?_,?_,?_⟩
  · dsimp [preparedClock]
    omega
  · rw [show t₁+t₂+1+t₃ = (t₁+t₂)+(1+t₃) by omega,
      run_add, run_add t₁ t₂, h₁, h₂]
    change (run (1+t₃)
      (⟨some .startJoin,(.inr (.inr (.inl v)),none),S₂⟩ : Config)).l = none
    rw [run_add 1 t₃]
    have hstart : run 1
      (⟨some .startJoin,(.inr (.inr (.inl v)),none),S₂⟩ : Config) =
      ⟨some (.join .suffixScan),
        (.inr (.inr (.inr ((),none))),none),S₂⟩ := by
      simp [run, program, advance, TM2.step, TM2.stepAux]
    rw [hstart,h₃]
  · rw [show t₁+t₂+1+t₃ = (t₁+t₂)+(1+t₃) by omega,
      run_add, run_add t₁ t₂, h₁, h₂]
    change (run (1+t₃)
      (⟨some .startJoin,(.inr (.inr (.inl v)),none),S₂⟩ : Config)).stk
      joinOutput = encodeFeature ((j,y)::c)
    rw [run_add 1 t₃]
    have hstart : run 1
      (⟨some .startJoin,(.inr (.inr (.inl v)),none),S₂⟩ : Config) =
      ⟨some (.join .suffixScan),
        (.inr (.inr (.inr ((),none))),none),S₂⟩ := by
      simp [run, program, advance, TM2.step, TM2.stepAux]
    rw [hstart,h₃]
    exact hout

#print axioms pair_prepend_prepared_run

def preparedSize (j y : Nat) (c : List (Nat × Nat)) : Nat :=
  j.bits.length + y.bits.length + (encodeFeature c).length + 1

theorem prepared_clock_poly (j y : Nat) (c : List (Nat × Nat)) :
    preparedClock j y c ≤
      (10*(UnaryBinaryEncoding.coefficient+100))*
        (preparedSize j y c)^2 := by
  let p := encodePair (j,y)
  let e := encodeFeature c
  let h := EncodedCommunication.natField (c.length+1)
  let f := FeaturePrependPrepared.pairField j y
  let s := FeaturePrependPrepared.oldSuffix c
  let N := preparedSize j y c
  have hN : 1 ≤ N := by dsimp [N,preparedSize]; omega
  have hp : p.length ≤ 2*N := by
    have hl := CylinderPairWriter.pair_length (j,y)
    have hl' : p.length = 2*(j.bits.length+y.bits.length)+2 := by
      simpa [p] using hl
    rw [hl']
    dsimp [N,preparedSize]
    omega
  have he : e.length ≤ N := by dsimp [e,N,preparedSize]; omega
  have hs : s.length ≤ N := by
    have hl := congrArg List.length (feature_old_bytes c)
    simp only [List.length_append] at hl
    dsimp [s,N,preparedSize]
    omega
  have hh : h.length ≤ N+1 := by
    have hl := congrArg List.length (feature_old_bytes c)
    simp only [List.length_append] at hl
    have hsucc := UnaryBinaryEncoding.successor_length c.length.bits
    rw [BinarySuccessorMachine.successor_bits] at hsucc
    change (EncodedCommunication.natField (c.length+1)).length ≤ N+1
    simp only [EncodedCommunication.natField,
      EncodedCommunication.field_length] at hl ⊢
    dsimp [N,preparedSize]
    omega
  have hf : f.length ≤ 7*N := by
    have hbits := UnaryBinaryEncoding.bits_length_le p.length
    have hfield := EncodedCommunication.field_length p.length.bits
    change (EncodedCommunication.natField p.length ++ p).length ≤ 7*N
    simp only [List.length_append, EncodedCommunication.natField]
    rw [hfield]
    omega
  have hp3 : p.length+1 ≤ 3*N := by omega
  have hsq : (p.length+1)^2 ≤ 9*N^2 := by
    have hx := Nat.pow_le_pow_left hp3 2
    nlinarith
  have hmul := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+7) hsq
  have hlin : 4*p.length + 6*e.length +
      4*(h.length+f.length+s.length)+26 ≤ 80*N^2 := by
    have hn2 : N ≤ N^2 := by nlinarith
    omega
  dsimp [preparedClock,p,h,f,s,e]
  nlinarith

#print axioms prepared_clock_poly

#print axioms pair_copy_phase

#print axioms copy_phase

#print axioms pair_phase

end
end CurrentAdditive.FeaturePreparedCallback
