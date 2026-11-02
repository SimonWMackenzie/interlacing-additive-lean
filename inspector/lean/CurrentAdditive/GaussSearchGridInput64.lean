import CurrentAdditive.GaussPhysicalPrepSearchClock
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-!
Physical bridge between the existing Gauss pivot search and the raw grid
writer. The four fields are old matrix, row, selected pivot, column. The
serializer consumes only these four fields; the pivot tag and full original
state stay in their search-frame banks. No rewritten matrix is assumed here.

Source: selected v39, appendices/support.tex, exact linear-algebra paragraph
and fixed column/row/pivot-order paragraph. This is the literal input adapter,
not a completed whole Gauss loop.
-/

namespace CurrentAdditive.GaussSearchGridInput64

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64
abbrev Local := BitMachineBankSerialize.Stack 4

def location : Local ↪ Bank where
  toFun := Sum.elim (fun i => ![8,53,19,55] i) (fun i => ![60,61,62] i)
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

def words (S : Bank → List Bool) : Fin 4 → List Bool :=
  fun i => S (location (.inl i))

def program (l : BitMachineBankSerialize.Label 4) :=
  BitMachineStackEmbedding.stackStmt location
    (BitMachineBankSerialize.program 4 l)

def packet (S : Bank → List Bool) : List Bool :=
  BitMachineBankCodec.encode (words S)

def initial (S : Bank → List Bool) :
    TM2.Cfg (fun _ : Bank => Bool) (BitMachineBankSerialize.Label 4) (Option Bool) :=
  ⟨some (.emit 0), none, S⟩

private theorem inline_id {K L V : Type*} [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) L V) :
    BitMachineInline.stmt id id id none q = q := by
  induction q <;> simp [BitMachineInline.stmt, *]

/-- Actual finite-stack serialization, including every payload and framing
bit. The tag and original-state banks are outside its stack embedding. -/
theorem physical_serialize (S : Bank → List Bool)
    (h60 : S 60 = []) (h61 : S 61 = []) (h62 : S 62 = []) :
    ∃ t ≤ 2 * (packet S).length + 2,
      let out := ((advance program)^[t]) (initial S)
      out.l = none ∧ out.stk 62 = packet S ∧
      out.stk 20 = S 20 ∧ out.stk 56 = S 56 ∧ out.stk 58 = S 58 := by
  let w := words S
  obtain ⟨t, sf, ht, hr⟩ := BitMachineBankSerialize.serialize w [] []
  let c := BitMachineBankSerialize.cfg (some (.emit 0)) none w [] [] []
  have hhalt : (((advance (BitMachineBankSerialize.program 4))^[t]) c).l = none := by
    change (BitMachineBankSerialize.run t c).l = none
    change (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none w [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs location S
    id id id (by intro v; rfl) none
    (BitMachineBankSerialize.program 4) program
    (by intro l; simp [program, BitMachineStackEmbedding.stmt, inline_id])
    c t hhalt
  have hstart : BitMachineStackEmbedding.cfg location S id id none c = initial S := by
    have hb : BitMachineStackEmbedding.bank location S c.stk = S := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro j
      cases j with
      | inl j => rfl
      | inr j =>
          fin_cases j <;>
            simp [c, BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents,
              location, h60, h61, h62]
    simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, c, BitMachineBankSerialize.cfg, initial] using
      congrArg (fun bank => (⟨some (.emit 0),none,bank⟩ :
        TM2.Cfg (fun _ : Bank => Bool) (BitMachineBankSerialize.Label 4) (Option Bool))) hb
  have hfinish : ((advance program)^[u]) (initial S) =
      BitMachineStackEmbedding.cfg location S id id none
        (BitMachineBankSerialize.cfg none none sf [] []
          (BitMachineBankSerialize.encode (List.ofFn w))) := by
    rw [hstart] at he
    change ((advance program)^[u]) (initial S) =
      BitMachineStackEmbedding.cfg location S id id none
        (BitMachineBankSerialize.run t c) at he
    have hr' : BitMachineBankSerialize.run t c =
        BitMachineBankSerialize.cfg none none sf [] []
          (BitMachineBankSerialize.encode (List.ofFn w)) := by
      simpa only [c, List.append_nil] using hr
    rw [hr'] at he
    exact he
  have hpacket : BitMachineBankSerialize.encode (List.ofFn w) = packet S := by
    simp [packet, BitMachineBankCodec.encode_eq_list,
      BitMachineBankSerialize.encode, w]
  have ht' : t ≤ 2 * (packet S).length + 2 := by
    rw [← hpacket]
    exact ht
  refine ⟨u, hu.trans ht', ?_⟩
  dsimp only
  rw [hfinish]
  constructor
  · rfl
  constructor
  · change (BitMachineStackEmbedding.bank location S _)
      (location (.inr 2)) = _
    rw [BitMachineStackEmbedding.bank_at]
    simpa [BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents] using hpacket
  · constructor
    · apply BitMachineStackEmbedding.bank_outside
      rintro ⟨j,hj⟩
      cases j <;> rename_i j <;> fin_cases j <;> simp [location] at hj
    · constructor
      · apply BitMachineStackEmbedding.bank_outside
        rintro ⟨j,hj⟩
        cases j <;> rename_i j <;> fin_cases j <;> simp [location] at hj
      · apply BitMachineStackEmbedding.bank_outside
        rintro ⟨j,hj⟩
        cases j <;> rename_i j <;> fin_cases j <;> simp [location] at hj

#print axioms physical_serialize

end
end CurrentAdditive.GaussSearchGridInput64
