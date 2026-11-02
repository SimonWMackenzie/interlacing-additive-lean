import CurrentAdditive.GaussPivotBodySplit32

/-!
Physical Bank2 serialization of the recorded pivot pair `(r,c)` from the
old unary cursors on banks 17 and 18. The selected search row on bank 21 is
not part of this pair. Output bank 28 receives the exact pair packet.
-/

namespace CurrentAdditive.GaussPivotPairEmit32

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Label := BitMachineBankSerialize.Label 2 ⊕ Unit
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : BitMachineBankSerialize.Stack 2 ↪ Stack where
  toFun
    | .inl i => ![17, 18] i
    | .inr i => ![29, 30, 28] i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => fin_cases a <;> fin_cases b <;> simp_all
      | inr b => fin_cases a <;> fin_cases b <;> simp_all
    | inr a =>
      cases b with
      | inl b => fin_cases a <;> fin_cases b <;> simp_all
      | inr b => fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (BitMachineBankSerialize.program 2 l)
  | .inr () => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 2 => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

def pairBank (r c : Nat) : BitMachineBankSerialize.Bank 2 :=
  fun j => if j = 0 then List.replicate r true
    else List.replicate c true

theorem pairBank_packet {m k : Nat} (p : Fin m × Fin k) :
    BitMachineBankSerialize.encode (List.ofFn
      (pairBank p.1.val p.2.val)) =
    CurrentAdditive.GaussControlTrace.pivotPacket p := by
  unfold CurrentAdditive.GaussControlTrace.pivotPacket
  rw [BitMachineBankCodec.encode_eq_list]
  rfl

theorem physical_pair {m k : Nat} (p : Fin m × Fin k)
    (foreign : Stack → List Bool) :
    ∃ t ≤ 2 * (CurrentAdditive.GaussControlTrace.pivotPacket p).length + 2,
      ∃ S' : BitMachineBankSerialize.Bank 2,
      run t (frame foreign
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (pairBank p.1.val p.2.val) [] [] [])) =
        frame foreign
          (BitMachineBankSerialize.cfg none none S' [] []
            (CurrentAdditive.GaussControlTrace.pivotPacket p)) := by
  obtain ⟨t, S', ht, hr⟩ :=
    BitMachineBankSerialize.serialize
      (pairBank p.1.val p.2.val) [] []
  have hh : (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (pairBank p.1.val p.2.val) [] [] [])).l = none := by
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl) (some (.inr ()))
    (BitMachineBankSerialize.program 2) program (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (pairBank p.1.val p.2.val) [] [] []) t hh
  refine ⟨u, ?_, S', ?_⟩
  · rw [← pairBank_packet p]
    exact hu.trans ht
  · change run u (frame foreign _) =
      frame foreign (BitMachineBankSerialize.run t _) at he
    rw [hr] at he
    simpa only [List.append_nil, pairBank_packet] using he

theorem output_28 {m k : Nat} (p : Fin m × Fin k)
    (foreign : Stack → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    (frame foreign
      (BitMachineBankSerialize.cfg none none S' [] []
        (CurrentAdditive.GaussControlTrace.pivotPacket p))).stk 28 =
      CurrentAdditive.GaussControlTrace.pivotPacket p := by
  exact BitMachineStackEmbedding.bank_at locate foreign _ (.inr 2)

#print axioms physical_pair
#print axioms output_28

end CurrentAdditive.GaussPivotPairEmit32
