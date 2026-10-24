import CurrentAdditive.GaussPacketSerialize
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
One fixed four-phase TM2 controller installs the four prepared state words
from banks 4--7 into banks 0--3. The source words are restored after each
copy, and bank 15 is used as an emptied scratch stack. This is the charged
routing stage immediately before Bank4 serialization.
-/

namespace CurrentAdditive.GaussStateAssemble16

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 16
abbrev Control := Unit × Option Bool

def src (p : Fin 4) : Stack := ⟨p.val + 4, by omega⟩
def dst (p : Fin 4) : Stack := ⟨p.val, by omega⟩
def temp : Stack := 15

inductive Label where
  | copy (p : Fin 4) (l : SourceClausePreservingBroadcast.Label)
  | done
  | serialize (l : BitMachineBankSerialize.Label 4)
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def next (p : Fin 4) : Option Label :=
  if h : p.val < 3 then some (.copy ⟨p.val + 1, by omega⟩ .scan)
  else some .done

def serSlot : (Fin 4 ⊕ Fin 3) ↪ Stack where
  toFun
    | .inl p => dst p
    | .inr q => ⟨q.val + 12, by omega⟩
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have he : a.val = b.val := by
          simpa [dst] using congrArg (fun z : Stack => z.val) h
        exact congrArg Sum.inl (Fin.ext he)
      | inr b =>
        have he := congrArg (fun z : Stack => z.val) h
        simp [dst] at he
        omega
    | inr a =>
      cases b with
      | inl b =>
        have he := congrArg (fun z : Stack => z.val) h
        simp [dst] at he
        omega
      | inr b =>
        have he : a.val = b.val := by
          have hv := congrArg (fun z : Stack => z.val) h
          simp at hv
          omega
        exact congrArg Sum.inr (Fin.ext he)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy p l =>
      BitMachineInline.stmt (Label.copy p) id id (next p)
        (SourceClausePreservingBroadcast.program (src p) temp [dst p] l)
  | .done => goto (fun _ => .serialize (.emit 0))
  | .serialize l =>
      BitMachineStackEmbedding.stmt serSlot Label.serialize
        (fun v => ((), v)) Prod.snd none
        (BitMachineBankSerialize.program 4 l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n + u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

theorem copy_phase (p : Fin 4) (bits : List Bool)
    (S : Stack → List Bool) (hbits : S (src p) = bits)
    (htemp : S temp = []) :
    ∃ u ≤ 2 * bits.length + 3,
      run u ⟨some (.copy p .scan), ((), none), S⟩ =
        ⟨next p, ((), none),
          SourceClausePreservingBroadcast.result
            (src p) temp [dst p] bits S⟩ := by
  have hsrc : src p ≠ temp := by
    intro h
    have he := congrArg (fun j : Stack => j.val) h
    dsimp [src, temp] at he
    omega
  have hnot : src p ∉ [dst p] := by
    simp only [List.mem_singleton]
    intro h
    have he := congrArg (fun j : Stack => j.val) h
    dsimp [src, dst] at he
    omega
  have htmp : temp ∉ [dst p] := by
    simp only [List.mem_singleton]
    intro h
    have he := congrArg (fun j : Stack => j.val) h
    dsimp [temp, dst] at he
    omega
  have hcore := SourceClausePreservingBroadcast.run_halt
    (src p) temp [dst p] hsrc (by simp) hnot htmp bits S hbits htemp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Label.copy p) id id (by intro v; rfl) (next p)
    (SourceClausePreservingBroadcast.program (src p) temp [dst p])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2 * bits.length + 3) (by rw [hcore])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa only [BitMachineInline.cfg] using hr

def initialBank (w : Fin 4 → List Bool) : Stack → List Bool :=
  fun j =>
    if j = 4 then w 0 else
    if j = 5 then w 1 else
    if j = 6 then w 2 else
    if j = 7 then w 3 else []

def after0 (w : Fin 4 → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (src 0) temp [dst 0]
    (w 0) (initialBank w)
def after1 (w : Fin 4 → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (src 1) temp [dst 1]
    (w 1) (after0 w)
def after2 (w : Fin 4 → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (src 2) temp [dst 2]
    (w 2) (after1 w)
def after3 (w : Fin 4 → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (src 3) temp [dst 3]
    (w 3) (after2 w)

private theorem initial_source (w : Fin 4 → List Bool) (p : Fin 4) :
    initialBank w (src p) = w p := by
  fin_cases p <;> simp [initialBank, src]

private theorem initial_temp (w : Fin 4 → List Bool) :
    initialBank w temp = [] := by
  simp [initialBank, temp]

private theorem after0_source1 (w : Fin 4 → List Bool) :
    after0 w (src 1) = w 1 := by
  simp [after0, SourceClausePreservingBroadcast.result,
    BitMachineBroadcast.prepend, initialBank, src, dst, temp]

private theorem after1_source2 (w : Fin 4 → List Bool) :
    after1 w (src 2) = w 2 := by
  simp [after1, after0, SourceClausePreservingBroadcast.result,
    BitMachineBroadcast.prepend, initialBank, src, dst, temp]

private theorem after2_source3 (w : Fin 4 → List Bool) :
    after2 w (src 3) = w 3 := by
  simp [after2, after1, after0,
    SourceClausePreservingBroadcast.result,
    BitMachineBroadcast.prepend, initialBank, src, dst, temp]

private theorem after0_temp (w : Fin 4 → List Bool) :
    after0 w temp = [] := by
  exact SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
private theorem after1_temp (w : Fin 4 → List Bool) :
    after1 w temp = [] := by
  exact SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
private theorem after2_temp (w : Fin 4 → List Bool) :
    after2 w temp = [] := by
  exact SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

def clock (w : Fin 4 → List Bool) : Nat :=
  (2 * (w 0).length + 3) + (2 * (w 1).length + 3) +
  (2 * (w 2).length + 3) + (2 * (w 3).length + 3)

theorem physical_four_copies (w : Fin 4 → List Bool) :
    ∃ t ≤ clock w,
      run t ⟨some (.copy 0 .scan), ((), none), initialBank w⟩ =
        ⟨some .done, ((), none), after3 w⟩ := by
  obtain ⟨t0, h0, hr0⟩ := copy_phase 0 (w 0) (initialBank w)
    (initial_source w 0) (initial_temp w)
  have hs0 : run t0 ⟨some (.copy 0 .scan), ((), none), initialBank w⟩ =
      ⟨some (.copy 1 .scan), ((), none), after0 w⟩ := by
    simpa [next, after0] using hr0
  obtain ⟨t1, h1, hr1⟩ := copy_phase 1 (w 1) (after0 w)
    (after0_source1 w) (after0_temp w)
  have hs1 : run t1 ⟨some (.copy 1 .scan), ((), none), after0 w⟩ =
      ⟨some (.copy 2 .scan), ((), none), after1 w⟩ := by
    simpa [next, after1] using hr1
  obtain ⟨t2, h2, hr2⟩ := copy_phase 2 (w 2) (after1 w)
    (after1_source2 w) (after1_temp w)
  have hs2 : run t2 ⟨some (.copy 2 .scan), ((), none), after1 w⟩ =
      ⟨some (.copy 3 .scan), ((), none), after2 w⟩ := by
    simpa [next, after2] using hr2
  obtain ⟨t3, h3, hr3⟩ := copy_phase 3 (w 3) (after2 w)
    (after2_source3 w) (after2_temp w)
  have hs3 : run t3 ⟨some (.copy 3 .scan), ((), none), after2 w⟩ =
      ⟨some .done, ((), none), after3 w⟩ := by
    simpa [next, after3] using hr3
  refine ⟨t0 + t1 + t2 + t3, ?_, ?_⟩
  · unfold clock
    omega
  · rw [show t0 + t1 + t2 + t3 = ((t0 + t1) + t2) + t3 by omega]
    exact (((run_add hs0 t1).trans hs1 |> fun h => run_add h t2).trans hs2
      |> fun h => run_add h t3).trans hs3

theorem installed_word (w : Fin 4 → List Bool) (p : Fin 4) :
    after3 w (dst p) = w p := by
  fin_cases p <;>
    simp [after3, after2, after1, after0,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend, initialBank, src, dst, temp]

def outputBank (w : Fin 4 → List Bool) : Fin 4 → List Bool :=
  fun p => after3 w (dst p)

theorem outputBank_eq (w : Fin 4 → List Bool) : outputBank w = w := by
  funext p
  exact installed_word w p

private theorem after3_extra_empty (w : Fin 4 → List Bool)
    (q : Fin 3) : after3 w (serSlot (.inr q)) = [] := by
  fin_cases q <;>
    simp [after3, after2, after1, after0,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend, initialBank, src, dst, temp, serSlot]

def serializeCore (w : Fin 4 → List Bool) :=
  BitMachineBankSerialize.cfg (some (.emit 0)) none (outputBank w) [] [] []

noncomputable def serializeFrame (w : Fin 4 → List Bool) : Config :=
  BitMachineStackEmbedding.cfg serSlot (after3 w) Label.serialize
    (fun v => ((), v)) none (serializeCore w)

theorem serializeFrame_eq (w : Fin 4 → List Bool) :
    serializeFrame w =
      ⟨some (.serialize (.emit 0)), ((), none), after3 w⟩ := by
  unfold serializeFrame serializeCore
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    BitMachineBankSerialize.cfg]
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro j
  cases j with
  | inl p =>
      simp [BitMachineBankSerialize.contents, outputBank, serSlot]
  | inr q =>
      simpa [BitMachineBankSerialize.contents] using
        (after3_extra_empty w q).symm

theorem physical_serialize (w : Fin 4 → List Bool) :
    ∃ t ≤ 2 * (BitMachineBankCodec.encode w).length + 2,
      (run t (serializeFrame w)).l = none ∧
      (run t (serializeFrame w)).stk 14 =
        BitMachineBankCodec.encode w := by
  obtain ⟨t, S', ht, hcore⟩ :=
    BitMachineBankSerialize.serialize (outputBank w) [] []
  have hcore' : BitMachineBankSerialize.run t (serializeCore w) =
      BitMachineBankSerialize.cfg none none S' [] []
        (BitMachineBankSerialize.encode (List.ofFn (outputBank w)) ++ []) := by
    simpa only [serializeCore] using hcore
  have hh : (BitMachineBankSerialize.run t (serializeCore w)).l = none := by
    rw [hcore']
    rfl
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    serSlot (after3 w) Label.serialize (fun v => ((), v)) Prod.snd
    (by intro v; rfl) none (BitMachineBankSerialize.program 4)
    program (by intro l; rfl) (serializeCore w) t hh
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa [BitMachineBankCodec.encode_eq_list,
      BitMachineBankSerialize.encode, outputBank_eq] using hu.trans ht
  · change run u (serializeFrame w) = _ at hr
    rw [hr]
    change (BitMachineStackEmbedding.cfg serSlot (after3 w)
      Label.serialize (fun v => ((), v)) none
      (BitMachineBankSerialize.run t (serializeCore w))).l = none
    rw [hcore']
    rfl
  · change run u (serializeFrame w) = _ at hr
    rw [hr]
    change (BitMachineStackEmbedding.cfg serSlot (after3 w)
      Label.serialize (fun v => ((), v)) none
      (BitMachineBankSerialize.run t (serializeCore w))).stk
      (serSlot (.inr (2 : Fin 3))) = _
    rw [hcore']
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      BitMachineBankSerialize.cfg,
      BitMachineStackEmbedding.bank_at,
      BitMachineBankSerialize.contents, Sum.elim_inr]
    simp [BitMachineBankCodec.encode_eq_list,
      BitMachineBankSerialize.encode, outputBank_eq]

theorem physical_state_packet_one_run {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k) :
    ∃ t ≤ clock (CurrentAdditive.GaussControlTrace.stateBank s) + 1 +
        2 * (CurrentAdditive.GaussControlTrace.statePacket s).length + 2,
      (run t ⟨some (.copy 0 .scan), ((), none),
        initialBank (CurrentAdditive.GaussControlTrace.stateBank s)⟩).l = none ∧
      (run t ⟨some (.copy 0 .scan), ((), none),
        initialBank (CurrentAdditive.GaussControlTrace.stateBank s)⟩).stk 14 =
        CurrentAdditive.GaussControlTrace.statePacket s := by
  let w := CurrentAdditive.GaussControlTrace.stateBank s
  obtain ⟨a, ha, hcopy⟩ := physical_four_copies w
  have hdone : run 1 ⟨some .done, ((), none), after3 w⟩ =
      serializeFrame w := by
    rw [serializeFrame_eq]
    rfl
  obtain ⟨b, hb, hhalt, hpacket⟩ := physical_serialize w
  have hstart : run (a + 1)
      ⟨some (.copy 0 .scan), ((), none), initialBank w⟩ =
      serializeFrame w := (run_add hcopy 1).trans hdone
  have hfinal := run_add hstart b
  refine ⟨a + 1 + b, ?_, ?_, ?_⟩
  · change a + 1 + b ≤ clock w + 1 + 2 *
      (BitMachineBankCodec.encode w).length + 2
    omega
  · change (run (a + 1 + b)
      ⟨some (.copy 0 .scan), ((), none), initialBank w⟩).l = none
    rw [hfinal]
    exact hhalt
  · change (run (a + 1 + b)
      ⟨some (.copy 0 .scan), ((), none), initialBank w⟩).stk 14 =
      BitMachineBankCodec.encode w
    rw [hfinal]
    exact hpacket

theorem physical_state_fields {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k) :
    ∃ t ≤ clock (CurrentAdditive.GaussControlTrace.stateBank s),
      run t ⟨some (.copy 0 .scan), ((), none),
        initialBank (CurrentAdditive.GaussControlTrace.stateBank s)⟩ =
        ⟨some .done, ((), none),
          after3 (CurrentAdditive.GaussControlTrace.stateBank s)⟩ ∧
      BitMachineBankCodec.encode
        (outputBank (CurrentAdditive.GaussControlTrace.stateBank s)) =
        CurrentAdditive.GaussControlTrace.statePacket s := by
  obtain ⟨t, ht, hr⟩ := physical_four_copies
    (CurrentAdditive.GaussControlTrace.stateBank s)
  exact ⟨t, ht, hr, by
    rw [outputBank_eq]
    rfl⟩

#print axioms physical_four_copies
#print axioms installed_word
#print axioms outputBank_eq
#print axioms physical_state_fields
#print axioms physical_serialize
#print axioms physical_state_packet_one_run

#print axioms copy_phase

end CurrentAdditive.GaussStateAssemble16
