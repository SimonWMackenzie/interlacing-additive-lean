import CurrentAdditive.GaussPackedParse64
import CurrentAdditive.GaussOneFetchProgram64
import CurrentAdditive.GaussTypedGetterBridge
import EthInapproximability.CurrentPaper.BitMachineRawSequence

set_option maxHeartbeats 1000000

/-! Literal Bank3 parser followed by the checked fixed Fin64 cell getter. -/

namespace CurrentAdditive.GaussPackedFetch64

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.GaussPhysical
open CurrentAdditive.CodeDCodec
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def packet {m k : Nat} (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    BitMachineBankCodec.Bank 3 :=
  ![encodeTypedMatrix B, List.replicate i.val true, List.replicate j.val true]

def input {m k : Nat} (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    List Bool := BitMachineBankCodec.encode (packet B i j)

noncomputable def initialStack (word : List Bool) : Stack → List Bool :=
  (GaussPackedParse64.frame (fun _ => [])
    (parserCfg (K := 3) (some (.scan 0)) none (fun _ => []) word [] [])).stk

noncomputable def parsedStack (bank : BitMachineBankCodec.Bank 3) : Stack → List Bool :=
  (GaussPackedParse64.frame (fun _ => [])
    (parserCfg none (some true) bank [] [] [])).stk

def fetchControl : GaussOneFetchProgram64.Control :=
  (((((), none), ((), none)), ((), none)), GaussOneFetchProgram64.getterControl)

def program := BitMachineRawSequence.program
  GaussPackedParse64.program GaussOneFetchProgram64.program
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0))))
  (none : GaussPackedParse64.Control) fetchControl

abbrev Label := BitMachineRawSequence.Label
  GaussPackedParse64.Label GaussOneFetchProgram64.Label
abbrev Control := BitMachineRawSequence.Control
  GaussPackedParse64.Control GaussOneFetchProgram64.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def initial (word : List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel (.inl (.scan 0))),
    (none, fetchControl), initialStack word⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem parsed_input (bank : BitMachineBankCodec.Bank 3) :
    ∃ t ≤ 7 * ((BitMachineBankCodec.encode bank).length + 1),
      GaussPackedParse64.run t
        ⟨some (.inl (.scan 0)), none,
          initialStack (BitMachineBankCodec.encode bank)⟩ =
        ⟨none, some true, parsedStack bank⟩ := by
  obtain ⟨t, ht, hr⟩ := GaussPackedParse64.parse_encoded bank (fun _ => [])
  refine ⟨t, ht, ?_⟩
  simpa only [initialStack, parsedStack, GaussPackedParse64.frame,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg] using hr

theorem parsed_at (bank : BitMachineBankCodec.Bank 3) (p : Fin 3) :
    parsedStack bank (GaussPackedParse64.locate (.inl p)) = bank p := by
  exact GaussPackedParse64.parsed_field bank (fun _ => []) p

theorem parsed_63 (bank : BitMachineBankCodec.Bank 3) :
    parsedStack bank 63 = [] := by
  unfold parsedStack GaussPackedParse64.frame
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg]
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨q, hq⟩
  cases q with
  | inl q => fin_cases q <;> simp [GaussPackedParse64.locate] at hq
  | inr q => fin_cases q <;> simp [GaussPackedParse64.locate] at hq

theorem canonical_fetch_bank38 {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    ∃ t ≤ 7 * ((input B i j).length + 1) +
      GaussOneFetchProgram64.preparationClock
        (parsedStack (packet B i j)) i.val j.val +
      140 * ((encodeTypedMatrix B).length + 1)^3 + 2,
      (run t (initial (input B i j))).l = none ∧
      (run t (initial (input B i j))).stk 38 =
        encodeRawRat (rawOfRat (B i j)) := by
  let bank := packet B i j
  let S := parsedStack bank
  let rowPre := (GaussTypedGetterBridge.rowWords B).take i.val
  let rowSuffix := (GaussTypedGetterBridge.rowWords B).drop (i.val+1)
  let cellPre := (GaussTypedGetterBridge.cellWords B i).take j.val
  let cellSuffix := (GaussTypedGetterBridge.cellWords B i).drop (j.val+1)
  let cell := encodeRawRat (rawOfRat (B i j))
  obtain ⟨hm, hri, hcj⟩ := GaussTypedGetterBridge.typed_decomposition B i j
  have hmat : S 8 = encodeTypedMatrix B := by
    simpa [S, bank, packet, GaussPackedParse64.locate] using parsed_at bank 0
  have hrow : S 15 = List.replicate i.val true := by
    simpa [S, bank, packet, GaussPackedParse64.locate] using parsed_at bank 1
  have hcol : S 16 = List.replicate j.val true := by
    simpa [S, bank, packet, GaussPackedParse64.locate] using parsed_at bank 2
  obtain ⟨tp, htp, hpr⟩ := parsed_input bank
  obtain ⟨tg, htg, hgh, hcell, _⟩ :=
    GaussOneFetchProgram64.canonical_one_fetch
      rowPre rowSuffix cellPre cellSuffix cell S
      (by rw [hmat, hm]) (by rw [hri]; exact hrow)
      (by rw [hcj]; exact hcol) (parsed_63 bank)
  let endGetter := GaussOneFetchProgram64.run tg
    (GaussOneFetchProgram64.initial S)
  have hget : ((advance GaussOneFetchProgram64.program)^[tg])
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.clear 0)))),
        fetchControl, S⟩ :
        GaussOneFetchProgram64.Config) =
      ⟨none, endGetter.var, endGetter.stk⟩ := by
    change endGetter = _
    have hh : endGetter.l = none := hgh
    cases hc : endGetter with
    | mk l v T =>
        cases l with
        | none => rfl
        | some l =>
            rw [hc] at hh
            contradiction
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    GaussPackedParse64.program GaussOneFetchProgram64.program
    (.inl (.scan 0))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.clear 0))))
    none (some true)
    fetchControl endGetter.var
    (initialStack (input B i j)) S endGetter.stk tp tg
    (by simpa [input, S, bank] using hpr) hget
  have heq : run t (initial (input B i j)) =
      ⟨none, (none, endGetter.var), endGetter.stk⟩ := by
    simpa [run, initial, program] using hfull
  refine ⟨t, ?_, ?_, ?_⟩
  · change tp ≤ 7 * ((input B i j).length + 1) at htp
    rw [← hm] at htg
    rw [hri, hcj] at htg
    change tg ≤ GaussOneFetchProgram64.preparationClock
      (parsedStack (packet B i j)) i.val j.val +
      140 * ((encodeTypedMatrix B).length + 1)^3 + 1 at htg
    omega
  · rw [heq]
  · rw [heq]
    exact hcell

#print axioms canonical_fetch_bank38

end CurrentAdditive.GaussPackedFetch64
