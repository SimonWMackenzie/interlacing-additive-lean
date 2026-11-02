import EthInapproximability.CurrentPaper.SignedMidpointCap
import EthInapproximability.CurrentPaper.BitMachineInline

/-!
# The physical cap and signed comparison in one program

On canonical physical input banks containing a signed answer, unary threshold
and unary separation, this single finite program first writes `2Y+k` cells,
then runs the signed midpoint comparator. It charges both runs. Framing from
an approximation output and source table remains a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointCapCompare

open Turing BitMachineEncoding

abbrev Label := SignedMidpointCap.Label ⊕ SignedMidpointMachine.Label
abbrev Control := SignedMidpointCap.Control × SignedMidpointMachine.Control
abbrev Stack := Fin 5
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def capEmbed (v : SignedMidpointCap.Control) : Control :=
  (v, SignedMidpointPacket.initial)

def compareEmbed (v : SignedMidpointMachine.Control) : Control := (none, v)

def program : Label → Statement
  | .inl l => BitMachineInline.stmt Sum.inl capEmbed Prod.fst
      (some (.inr SignedMidpointPacket.start)) (SignedMidpointCap.program l)
  | .inr l => BitMachineInline.stmt Sum.inr compareEmbed Prod.snd none
      (SignedMidpointMachine.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 5) 4 (.inl .double)
    (none, SignedMidpointPacket.initial) program

def inputBank (answer : List Bool) (threshold separation : ℕ) :
    Fin 5 → List Bool :=
  ![answer, List.replicate threshold true, List.replicate separation true, [], []]

def inputPacket (answer : List Bool) (threshold separation : ℕ) : List Bool :=
  BitMachineBankCodec.encode (inputBank answer threshold separation)

def capFrame (c : SignedMidpointCap.Config) : Config :=
  BitMachineInline.cfg Sum.inl capEmbed
    (some (.inr SignedMidpointPacket.start)) c

def compareFrame (c : SignedMidpointMachine.Config) : Config :=
  BitMachineInline.cfg Sum.inr compareEmbed none c

theorem cap_prefix (answer : List Bool) (threshold separation : ℕ) :
    ∃ t ≤ 3*threshold+separation+3,
      run t (capFrame (SignedMidpointCap.cfg (some .double) none answer
        (List.replicate threshold true) (List.replicate separation true) [] [])) =
      compareFrame (SignedMidpointMachine.cfg
        (some SignedMidpointPacket.start) SignedMidpointPacket.initial
        answer (List.replicate (2*threshold+separation) true) [] [] []) := by
  let c := SignedMidpointCap.cfg (some .double) none answer
    (List.replicate threshold true) (List.replicate separation true) [] []
  have hh : (SignedMidpointCap.run (3*threshold+separation+3) c).l = none := by
    rw [SignedMidpointCap.cap_run]
    rfl
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs
    (Sum.inl : SignedMidpointCap.Label → Label) capEmbed Prod.fst
    (by intro v; rfl)
    (some (.inr SignedMidpointPacket.start)) SignedMidpointCap.program program
    (by intro l; rfl) c (3*threshold+separation+3) hh
  refine ⟨t,ht,?_⟩
  change ((advance program)^[t])
    (BitMachineInline.cfg Sum.inl capEmbed
      (some (.inr SignedMidpointPacket.start)) c) = _
  rw [hr]
  have hc := SignedMidpointCap.cap_run answer threshold separation
  change ((advance SignedMidpointCap.program)^[3*threshold+separation+3]) c = _ at hc
  rw [hc]
  rfl

theorem compare_suffix (answer : ℤ) (cap : List Bool) :
    ∃ t ≤ SignedMidpointSemantics.fuel (EncodedETHTail.encodeInteger answer) cap,
      (run t (compareFrame (SignedMidpointMachine.cfg
        (some SignedMidpointPacket.start) SignedMidpointPacket.initial
        (EncodedETHTail.encodeInteger answer) cap [] [] []))).l = none ∧
      (run t (compareFrame (SignedMidpointMachine.cfg
        (some SignedMidpointPacket.start) SignedMidpointPacket.initial
        (EncodedETHTail.encodeInteger answer) cap [] [] []))).stk 4 =
        [decide (2*answer < (cap.length : ℤ))] := by
  let c := SignedMidpointMachine.cfg (some SignedMidpointPacket.start)
    SignedMidpointPacket.initial (EncodedETHTail.encodeInteger answer) cap [] [] []
  have hh : (SignedMidpointMachine.run
    (SignedMidpointSemantics.fuel (EncodedETHTail.encodeInteger answer) cap) c).l = none :=
    SignedMidpointSemantics.halt_encodeInteger answer cap
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs
    (Sum.inr : SignedMidpointMachine.Label → Label) compareEmbed Prod.snd
    (by intro v; rfl)
    none SignedMidpointMachine.program program (by intro l; rfl) c
    (SignedMidpointSemantics.fuel (EncodedETHTail.encodeInteger answer) cap) hh
  refine ⟨t,ht,?_,?_⟩
  · change (((advance program)^[t])
      (BitMachineInline.cfg Sum.inr compareEmbed none c)).l = none
    rw [hr]
    change (((advance SignedMidpointMachine.program)^[SignedMidpointSemantics.fuel
      (EncodedETHTail.encodeInteger answer) cap]) c).l = none at hh
    simp only [BitMachineInline.cfg, hh]
  · change (((advance program)^[t])
      (BitMachineInline.cfg Sum.inr compareEmbed none c)).stk 4 = _
    rw [hr]
    have ho := SignedMidpointSemantics.result_encodeInteger answer cap
    change (((advance SignedMidpointMachine.program)^[SignedMidpointSemantics.fuel
      (EncodedETHTail.encodeInteger answer) cap]) c).stk 4 = _ at ho
    simpa only [BitMachineInline.cfg] using ho

theorem comparison_run (answer : ℤ) (threshold separation : ℕ) :
    ∃ t ≤ 3*threshold+separation+3 +
        SignedMidpointSemantics.fuel (EncodedETHTail.encodeInteger answer)
          (List.replicate (2*threshold+separation) true),
      (run t (capFrame (SignedMidpointCap.cfg (some .double) none
        (EncodedETHTail.encodeInteger answer) (List.replicate threshold true)
        (List.replicate separation true) [] []))).l = none ∧
      (run t (capFrame (SignedMidpointCap.cfg (some .double) none
        (EncodedETHTail.encodeInteger answer) (List.replicate threshold true)
        (List.replicate separation true) [] []))).stk 4 =
          [decide (2*answer < (2*threshold+separation : ℤ))] := by
  let cap := List.replicate (2*threshold+separation) true
  let c := capFrame (SignedMidpointCap.cfg (some .double) none
    (EncodedETHTail.encodeInteger answer) (List.replicate threshold true)
    (List.replicate separation true) [] [])
  obtain ⟨a,ha,hA⟩ := cap_prefix (EncodedETHTail.encodeInteger answer)
    threshold separation
  obtain ⟨b,hb,hBhalt,hBout⟩ := compare_suffix answer cap
  dsimp [cap] at hb
  dsimp [cap] at hBout
  refine ⟨a+b, by omega, ?_, ?_⟩
  · change (run (a+b) c).l = none
    rw [show run (a+b) c = run b (run a c) by
      simp only [run, Nat.add_comm a b, Function.iterate_add_apply], hA]
    exact hBhalt
  · change (run (a+b) c).stk 4 = _
    rw [show run (a+b) c = run b (run a c) by
      simp only [run, Nat.add_comm a b, Function.iterate_add_apply], hA]
    simpa only [List.length_replicate, Int.natCast_add, Int.natCast_mul] using hBout

end EthInapproximability.CurrentPaper.SignedMidpointCapCompare
