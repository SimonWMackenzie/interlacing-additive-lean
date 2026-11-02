import CurrentAdditive.MinimumRatioCallbackLayout
import CurrentAdditive.CodeDUpdateRequestABI
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 4096

/-! Actual two-field serialization for one ratio pair.
The projected mass is consumed from bank24 and the coefficient from bank21. The exact pair
appears on bank28. Every other bank is preserved. -/

namespace CurrentAdditive.RatioPairSerializer

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout

def words (x y : List Bool) : BitMachineBankSerialize.Bank 2 := ![x,y]
def bytes (x y : List Bool) : List Bool :=
  EncodedCommunication.field x ++ EncodedCommunication.field y

theorem pair_serialize (x y : List Bool) :
    BitMachineBankSerialize.run (x.length+1+(y.length+1)+(bytes x y).length+2)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y) [] [] []) =
      BitMachineBankSerialize.cfg none none (fun _ => []) [] [] (bytes x y) := by
  let S0 := words x y
  let S1 := Function.update S0 0 []
  let S2 := Function.update S1 1 []
  have hx := BitMachineBankSerialize.emit_word (0 : Fin 2) none S0 x [] [] []
    (by simp [S0,words])
  have hy := BitMachineBankSerialize.emit_word (1 : Fin 2) none S1 y []
    (EncodedCommunication.field x).reverse [] (by simp [S1,S0,words])
  have h2 : S2 = (fun _ => []) := by
    funext i; fin_cases i <;> simp [S2,S1,S0,words]
  have hfirst : BitMachineBankSerialize.run (x.length+1+(y.length+1))
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y) [] [] []) =
      BitMachineBankSerialize.cfg (some (.emit 2)) none S2 [] (bytes x y).reverse [] := by
    rw [BitMachineBankSerialize.run_add]
    rw [show BitMachineBankSerialize.run (x.length+1)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y) [] [] []) =
      BitMachineBankSerialize.cfg (some (.emit 1)) none S1 []
        (EncodedCommunication.field x).reverse [] by
          simpa only [S0,S1,List.append_nil] using hx]
    rw [show BitMachineBankSerialize.run (y.length+1)
      (BitMachineBankSerialize.cfg (some (.emit 1)) none S1 []
        (EncodedCommunication.field x).reverse []) =
      BitMachineBankSerialize.cfg (some (.emit 2)) none S2 []
        ((EncodedCommunication.field y).reverse ++ (EncodedCommunication.field x).reverse) [] by
          simpa only [S2] using hy]
    simp [bytes,List.reverse_append]
  rw [show x.length+1+(y.length+1)+(bytes x y).length+2 =
      (x.length+1+(y.length+1))+(1+((bytes x y).reverse.length+1)) by simp; omega,
    BitMachineBankSerialize.run_add,hfirst,BitMachineBankSerialize.run_add]
  have he : BitMachineBankSerialize.run 1
      (BitMachineBankSerialize.cfg (some (.emit 2)) none S2 [] (bytes x y).reverse []) =
      BitMachineBankSerialize.cfg (some .finish) none S2 [] (bytes x y).reverse [] := by
    simpa only [BitMachineBankSerialize.run,Function.iterate_one] using
      BitMachineBankSerialize.emit_end S2 [] (bytes x y).reverse []
  rw [he,BitMachineBankSerialize.finish_run,h2]
  simp

def localSlot : BitMachineBankSerialize.Stack 2 → Fin 32 :=
  Sum.elim ![24,21] ![26,27,28]

noncomputable def locate : BitMachineBankSerialize.Stack 2 ↪ Stack where
  toFun i := low (localSlot i)
  inj' := by
    intro a b h
    have hh := congrArg Fin.val h
    cases a with
    | inl a => cases b with
      | inl b => fin_cases a <;> fin_cases b <;> simp_all [localSlot,low]
      | inr b => fin_cases a <;> fin_cases b <;> simp_all [localSlot,low]
    | inr a => cases b with
      | inl b => fin_cases a <;> fin_cases b <;> simp_all [localSlot,low]
      | inr b => fin_cases a <;> fin_cases b <;> simp_all [localSlot,low]

abbrev Label := BitMachineBankSerialize.Label 2 ⊕ Unit
abbrev Control := Option Bool

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (BitMachineBankSerialize.program 2 l)
  | .inr () => .halt

noncomputable def result (S : Bank) (x y : List Bool) : Bank :=
  Function.update (Function.update (Function.update S
    (locate (.inl 0)) []) (locate (.inl 1)) [])
    (locate (.inr 2)) (bytes x y)

theorem serialize_request (S : Bank) (x y : List Bool)
    (hx : S (locate (.inl 0)) = x)
    (hy : S (locate (.inl 1)) = y)
    (hblank : ∀ i : Fin 3, S (locate (.inr i)) = []) :
    ∃ t ≤ x.length+1+(y.length+1)+(bytes x y).length+3,
      ((advance program)^[t])
        (⟨some (.inl (.emit 0)), none, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, none, result S x y⟩ := by
  let c := BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y) [] [] []
  have hinit : BitMachineStackEmbedding.bank locate S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · simpa [c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,words] using hx.symm
      · simpa [c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,words] using hy.symm
    | inr i => fin_cases i <;> simpa [c,BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents] using (hblank _).symm
  have hr := pair_serialize x y
  let n := x.length+1+(y.length+1)+(bytes x y).length+2
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs locate S Sum.inl id id
    (by intro v; rfl) (some (.inr ())) (BitMachineBankSerialize.program 2)
    program (by intro l; rfl) c n
    (by change (BitMachineBankSerialize.run n c).l = none; rw [hr]; rfl)
  change ((advance program)^[u])
    (BitMachineStackEmbedding.cfg locate S Sum.inl id (some (.inr ())) c) = _ at he
  change ((advance (BitMachineBankSerialize.program 2))^[n]) c = _ at hr
  rw [hr] at he
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,hinit,id_eq] at he
  have hout : BitMachineStackEmbedding.bank locate S
      (BitMachineBankSerialize.contents (fun _ : Fin 2 => []) [] []
        (bytes x y)) = result S x y := by
    funext j
    by_cases hj : ∃ i, locate i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [BitMachineStackEmbedding.bank_at]
      cases i with
      | inl i => fin_cases i <;> simp [result,BitMachineBankSerialize.contents,
          Function.update_apply,locate.injective.eq_iff]
      | inr i => fin_cases i <;> simp [result,BitMachineBankSerialize.contents,
          Function.update_apply,locate.injective.eq_iff,hblank]
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ j hj]
      have hn (i) : j ≠ locate i := by intro hh; exact hj ⟨i,hh.symm⟩
      simp [result,Function.update_of_ne,hn]
  simp only [c,BitMachineBankSerialize.cfg] at he
  rw [hout] at he
  refine ⟨u+1,by dsimp only [n] at hu; omega,?_⟩
  rw [Function.iterate_succ_apply',he]
  rfl

theorem bytes_pair (weight coeff : CodeDCodec.RawRat) :
    bytes (CodeDCodec.encodeRawRat weight) (CodeDCodec.encodeRawRat coeff) =
      CodeDPairProductTargetV2.pairBytes weight coeff := by
  simp [bytes,CodeDPairProductTargetV2.pairBytes,CodeDPairProductTargetV2.pairBank,
    BitMachineBankCodec.encode_eq_list,List.ofFn_succ]

#print axioms serialize_request

end CurrentAdditive.RatioPairSerializer
