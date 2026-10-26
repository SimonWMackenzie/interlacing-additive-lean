import CurrentAdditive.MinimumRatioCallbackLayout
import CurrentAdditive.CodeDUpdateRequestABI
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 4096

/-! Actual three-field serialization for one arithmetic update request.
The old source entry is consumed from bank 6, the copied selected scalar from
bank 29, and the coefficient fetched from Gauss from bank 21. The exact request
appears on bank 28. Bank 25 can retain the original selected scalar. -/

namespace CurrentAdditive.RatioRequestSerializer

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout

def words (x y z : List Bool) : BitMachineBankSerialize.Bank 3 := ![x,y,z]

def bytes (x y z : List Bool) : List Bool :=
  EncodedCommunication.field x ++ EncodedCommunication.field y ++
    EncodedCommunication.field z

theorem triple_serialize (x y z : List Bool) :
    BitMachineBankSerialize.run
      (x.length+1+(y.length+1)+(z.length+1)+(bytes x y z).length+2)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (words x y z) [] [] []) =
      BitMachineBankSerialize.cfg none none (fun _ => []) [] [] (bytes x y z) := by
  open BitMachineBankSerialize in
  let S0 := words x y z
  let S1 := Function.update S0 0 []
  let S2 := Function.update S1 1 []
  let S3 := Function.update S2 2 []
  have hx := BitMachineBankSerialize.emit_word (0 : Fin 3) none S0 x [] [] []
    (by simp [S0,words])
  have hy := BitMachineBankSerialize.emit_word (1 : Fin 3) none S1 y []
    (EncodedCommunication.field x).reverse [] (by simp [S1,S0,words])
  have hz := BitMachineBankSerialize.emit_word (2 : Fin 3) none S2 z []
    ((EncodedCommunication.field y).reverse ++
      (EncodedCommunication.field x).reverse) [] (by simp [S2,S1,S0,words])
  have hx' : BitMachineBankSerialize.run (x.length+1)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y z) [] [] []) =
      BitMachineBankSerialize.cfg (some (.emit 1)) none S1 []
        (EncodedCommunication.field x).reverse [] := by
    simpa only [S0,S1,List.append_nil] using hx
  have hy' : BitMachineBankSerialize.run (y.length+1)
      (BitMachineBankSerialize.cfg (some (.emit 1)) none S1 []
        (EncodedCommunication.field x).reverse []) =
      BitMachineBankSerialize.cfg (some (.emit 2)) none S2 []
        ((EncodedCommunication.field y).reverse ++
          (EncodedCommunication.field x).reverse) [] := by
    simpa only [S2] using hy
  have hz' : BitMachineBankSerialize.run (z.length+1)
      (BitMachineBankSerialize.cfg (some (.emit 2)) none S2 []
        ((EncodedCommunication.field y).reverse ++
          (EncodedCommunication.field x).reverse) []) =
      BitMachineBankSerialize.cfg (some (.emit 3)) none S3 []
        ((EncodedCommunication.field z).reverse ++
          ((EncodedCommunication.field y).reverse ++
            (EncodedCommunication.field x).reverse)) [] := by
    simpa only [S3] using hz
  have h3 : S3 = (fun _ => []) := by
    funext i
    fin_cases i <;> simp [S3,S2,S1,S0,words]
  have hfirst : BitMachineBankSerialize.run
      (x.length+1+(y.length+1)+(z.length+1))
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y z) [] [] []) =
      BitMachineBankSerialize.cfg (some (.emit 3)) none S3 []
        (bytes x y z).reverse [] := by
    rw [BitMachineBankSerialize.run_add
      (x.length+1+(y.length+1)) (z.length+1),
      BitMachineBankSerialize.run_add (x.length+1) (y.length+1)]
    rw [hx',hy',hz']
    simp [bytes,List.reverse_append,List.append_assoc,S3,S2,S1,S0]
  rw [show x.length+1+(y.length+1)+(z.length+1)+(bytes x y z).length+2 =
      (x.length+1+(y.length+1)+(z.length+1)) +
        (1+((bytes x y z).reverse.length+1)) by simp; omega,
    BitMachineBankSerialize.run_add,hfirst,BitMachineBankSerialize.run_add]
  have he := BitMachineBankSerialize.emit_end S3 [] (bytes x y z).reverse []
  have he' : BitMachineBankSerialize.run 1
      (BitMachineBankSerialize.cfg (some (.emit 3)) none S3 []
        (bytes x y z).reverse []) =
      BitMachineBankSerialize.cfg (some .finish) none S3 []
        (bytes x y z).reverse [] := by
    simpa only [BitMachineBankSerialize.run,Function.iterate_one] using he
  rw [he',BitMachineBankSerialize.finish_run,h3]
  simp

def localSlot : BitMachineBankSerialize.Stack 3 → Fin 32 :=
  Sum.elim ![6,29,21] ![26,27,28]

noncomputable def locate : BitMachineBankSerialize.Stack 3 ↪ Stack where
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

abbrev Label := BitMachineBankSerialize.Label 3 ⊕ Unit
abbrev Control := Option Bool

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (BitMachineBankSerialize.program 3 l)
  | .inr () => .halt

noncomputable def result (S : Bank) (x y z : List Bool) : Bank :=
  Function.update (Function.update (Function.update (Function.update S
    (locate (.inl 0)) []) (locate (.inl 1)) []) (locate (.inl 2)) [])
    (locate (.inr 2)) (bytes x y z)

theorem serialize_request (S : Bank) (x y z : List Bool)
    (hx : S (locate (.inl 0)) = x)
    (hy : S (locate (.inl 1)) = y)
    (hz : S (locate (.inl 2)) = z)
    (hblank : ∀ i : Fin 3, S (locate (.inr i)) = []) :
    ∃ t ≤ x.length+1+(y.length+1)+(z.length+1)+(bytes x y z).length+3,
      ((advance program)^[t])
        (⟨some (.inl (.emit 0)), none, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, none, result S x y z⟩ := by
  let c := BitMachineBankSerialize.cfg (some (.emit 0)) none (words x y z) [] [] []
  have hinit : BitMachineStackEmbedding.bank locate S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · simpa [c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,words] using hx.symm
      · simpa [c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,words] using hy.symm
      · simpa [c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,words] using hz.symm
    | inr i => fin_cases i <;> simpa [c,BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents] using (hblank _).symm
  have hr := triple_serialize x y z
  let n := x.length+1+(y.length+1)+(z.length+1)+(bytes x y z).length+2
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs locate S Sum.inl id id
    (by intro v; rfl) (some (.inr ())) (BitMachineBankSerialize.program 3)
    program (by intro l; rfl) c n
    (by change (BitMachineBankSerialize.run n c).l = none; rw [hr]; rfl)
  change ((advance program)^[u])
    (BitMachineStackEmbedding.cfg locate S Sum.inl id (some (.inr ())) c) = _ at he
  change ((advance (BitMachineBankSerialize.program 3))^[n]) c = _ at hr
  rw [hr] at he
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,hinit,id_eq] at he
  have hout : BitMachineStackEmbedding.bank locate S
      (BitMachineBankSerialize.contents (fun _ : Fin 3 => []) [] []
        (bytes x y z)) = result S x y z := by
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

theorem bytes_request (old : CodeDSourceCodecV2.Entry) (lambda coeff : ℚ) :
    bytes (CodeDSourceCodecV2.encodeEntry old)
      (CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat lambda))
      (CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat coeff)) =
    CodeDUpdateProductPairFields.requestPacket old lambda coeff := by
  simp [bytes,CodeDUpdateProductPairFields.requestPacket,
    BitMachineBankCodec.encode_eq_list,List.ofFn_succ,List.append_assoc]

#print axioms serialize_request

end CurrentAdditive.RatioRequestSerializer
