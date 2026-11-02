import CurrentAdditive.CylinderPairWriter
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-! Physical pair serialization with a disjoint old-feature register. -/

namespace CurrentAdditive.FeaturePairPrepared

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec
open Turing BitMachineEncoding

abbrev Stack := BitMachineBankSerialize.Stack 2 ⊕ Fin 1
abbrev Label := BitMachineBankSerialize.Label 2
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def slots : BitMachineBankSerialize.Stack 2 ↪ Stack :=
  ⟨Sum.inl, Sum.inl_injective⟩

def program (l : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt slots id id id none
    (BitMachineBankSerialize.program 2 l)

def initialBank (j y : Nat) (c : List (Nat × Nat)) :
    Stack → List Bool :=
  Sum.elim
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (pairBank (j,y)) [] [] []).stk
    ![encodeFeature c]

theorem pair_prepared (j y : Nat) (c : List (Nat × Nat)) :
    ∃ t ≤ 2*(encodePair (j,y)).length+2,
      let z := ((advance program)^[t])
        (⟨some (.emit 0),none,initialBank j y c⟩ : Config)
      z.l = none ∧ z.stk (.inl (.inr 2)) = encodePair (j,y) ∧
        z.stk (.inr 0) = encodeFeature c := by
  obtain ⟨t,remaining,ht,hr⟩ :=
    CylinderPairWriter.physical_pair (j,y) [] []
  have hh := congrArg (fun z => z.l) hr
  change (BitMachineBankSerialize.run t
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (pairBank (j,y)) [] [] [])).l = none at hh
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs slots
    (initialBank j y c) id id id (by intro v; rfl) none
    (BitMachineBankSerialize.program 2) program (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (pairBank (j,y)) [] [] []) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u,hu.trans ht,?_⟩
  change _ ∧ _ ∧ _
  have hstart : BitMachineStackEmbedding.cfg slots (initialBank j y c)
      id id none
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (pairBank (j,y)) [] [] []) =
      (⟨some (.emit 0),none,initialBank j y c⟩ : Config) := by
    unfold BitMachineStackEmbedding.cfg
      BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
    congr 1
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    cases k with
    | inl k => rfl
    | inr k => rfl
  rw [hstart] at he
  unfold BitMachineBankSerialize.run at hr
  rw [hr] at he
  constructor
  · exact congrArg (fun z => z.l) he
  constructor
  · have hk := congrArg (fun z => z.stk (.inl (.inr 2))) he
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] at hk
    rw [← show slots (.inr 2) = (.inl (.inr 2) : Stack) by rfl,
      BitMachineStackEmbedding.bank_at] at hk
    simpa [BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents] using hk
  · have houtside : ¬ ∃ k : BitMachineBankSerialize.Stack 2,
        slots k = (.inr 0 : Stack) := by
      rintro ⟨k,hk⟩
      cases hk
    have hk := congrArg (fun z => z.stk (.inr 0)) he
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] at hk
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ houtside] at hk
    simpa [initialBank] using hk

theorem pair_frame_outputs (j y : Nat) :
    (SourceListMachineWriter.framingMachine true).OutputsWithin
      (encodePair (j,y))
      (EncodedCommunication.natField (encodePair (j,y)).length ++
        encodePair (j,y))
      ((UnaryBinaryEncoding.coefficient+7)*
        ((encodePair (j,y)).length+1)^2) := by
  simpa only [SourceListMachineWriter.result,
    Bool.true_eq, ↓reduceIte] using
    SourceListMachineWriter.outputs true (encodePair (j,y))

#print axioms pair_prepared
#print axioms pair_frame_outputs

end CurrentAdditive.FeaturePairPrepared
