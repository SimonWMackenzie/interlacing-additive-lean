import CurrentAdditive.CodeDSourceCopy15
import CurrentAdditive.CodeDSourceBank2Field15
import CurrentAdditive.CodeDAlphabetBank2Field15
import CurrentAdditive.CodeDPairWeights15
import CurrentAdditive.CodeDFramePair15
import CurrentAdditive.CodeDAppendAtEnd15
import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! One fixed fifteen-stack program for a source/alphabet entry pair.
The six literal phases copy the preserved source record, parse both Bank2
records, serialize their rational-weight product request, frame it as one
V2 list item, and append it after the existing output. -/

namespace CurrentAdditive.CodeDPairCallbackProgram

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 15
abbrev Control := Option Bool

inductive Label
  | copy (l : CodeDSourceCopy15.Label)
  | source (l : CodeDSourceBank2Field15.Label)
  | alphabet (l : CodeDAlphabetBank2Field15.Label)
  | pair (l : CodeDPairWeights15.Label)
  | clearPayload
  | frame (l : CodeDFramePair15.Label)
  | append (l : CodeDAppendAtEnd15.Label)
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy l => BitMachineInline.stmt Label.copy id id
      (some (.source (.inl (.scan 0)))) (CodeDSourceCopy15.program l)
  | .source l => BitMachineInline.stmt Label.source id id
      (some (.alphabet (.inl (.scan 0)))) (CodeDSourceBank2Field15.program l)
  | .alphabet l => BitMachineInline.stmt Label.alphabet id id
      (some (.pair (.inl (.emit 0)))) (CodeDAlphabetBank2Field15.program l)
  | .pair l => BitMachineInline.stmt Label.pair id id
      (some .clearPayload) (CodeDPairWeights15.program l)
  | .clearPayload => .pop 5 (fun _ b => b)
      (.branch Option.isSome
        (.load (fun _ => none) (.goto (fun _ => .clearPayload)))
        (.load (fun _ => none) (.goto (fun _ => .frame (.inl (.emit 0))))))
  | .frame l => BitMachineInline.stmt Label.frame id id
      (some (.append .saveScan)) (CodeDFramePair15.program l)
  | .append l => BitMachineInline.stmt Label.append Prod.snd
      (fun b => ((), b)) none (CodeDAppendAtEnd15.program l)

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

private theorem nonhalt_before
    {L V : Type*} (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (c : TM2.Cfg (fun _ : Stack => Bool) L V) (t : Nat)
    (hfinal : (((advance P)^[t]) c).l ≠ none) :
    ∀ k < t, (((advance P)^[k]) c).l ≠ none := by
  intro k hk hnone
  have htime : (t-k) + k = t := by omega
  have heq : ((advance P)^[t]) c =
      ((advance P)^[t-k]) (((advance P)^[k]) c) := by
    calc
      ((advance P)^[t]) c = ((advance P)^[(t-k)+k]) c := by rw [htime]
      _ = ((advance P)^[t-k]) (((advance P)^[k]) c) :=
        Function.iterate_add_apply _ _ _ _
  rw [BitMachineSubroutine.run_halted P _ hnone] at heq
  exact hfinal (heq ▸ hnone)

private theorem inline_some
    {L V : Type*} (labels : L → Label) (embed : V → Control)
    (read : Control → V) (hread : Function.LeftInverse read embed)
    (next : Option Label)
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (hP : ∀ l, program (labels l) =
      BitMachineInline.stmt labels embed read next (P l))
    (c : TM2.Cfg (fun _ : Stack => Bool) L V)
    (t : Nat) (d : TM2.Cfg (fun _ : Stack => Bool) L V)
    (hr : ((advance P)^[t]) c = d) (hd : d.l ≠ none) :
    run t (BitMachineInline.cfg labels embed next c) =
      BitMachineInline.cfg labels embed next d := by
  have hn := nonhalt_before P c t (by rw [hr]; exact hd)
  change ((advance program)^[t]) _ = _
  rw [BitMachineInline.run_until labels embed read hread next P program hP c t hn, hr]

theorem copy_phase (record : List Bool) (foreign : Stack → List Bool) :
    ∃ t ≤ 2*record.length+2,
      run t (BitMachineInline.cfg Label.copy id
        (some (.source (.inl (.scan 0))))
        (CodeDSourceCopy15.frame foreign
          (BitMachineCopy.cfg (some .scan) none record [] []))) =
      BitMachineInline.cfg Label.copy id
        (some (.source (.inl (.scan 0))))
        (CodeDSourceCopy15.frame foreign
          (BitMachineCopy.cfg none none record record [])) := by
  obtain ⟨t, ht, hr⟩ := CodeDSourceCopy15.copy_source record foreign
  refine ⟨t, ht, ?_⟩
  exact inline_some Label.copy id id (by intro v; rfl)
    (some (.source (.inl (.scan 0)))) CodeDSourceCopy15.program
    (by intro l; rfl) _ t _ hr (by
      simp [CodeDSourceCopy15.frame, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        BitMachineCopy.cfg])

theorem source_phase (bank : BitMachineBankCodec.Bank 2)
    (foreign : Stack → List Bool) (output : List Bool) :
    ∃ t ≤ 5*((BitMachineBankCodec.encode bank).length+1),
      run t (BitMachineInline.cfg Label.source id
        (some (.alphabet (.inl (.scan 0))))
        (CodeDSourceBank2Field15.frame foreign
          (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => [])
            (BitMachineBankCodec.encode bank) [] output))) =
      BitMachineInline.cfg Label.source id
        (some (.alphabet (.inl (.scan 0))))
        (CodeDSourceBank2Field15.frame foreign
          (BitMachineBankCodec.parserCfg none (some true) bank [] [] output)) := by
  obtain ⟨t, ht, hr⟩ := CodeDSourceBank2Field15.parse_record bank foreign output
  refine ⟨t, ht, ?_⟩
  exact inline_some Label.source id id (by intro v; rfl)
    (some (.alphabet (.inl (.scan 0)))) CodeDSourceBank2Field15.program
    (by intro l; rfl) _ t _ hr (by
      simp [CodeDSourceBank2Field15.frame, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        BitMachineBankCodec.parserCfg])

theorem alphabet_phase (bank : BitMachineBankCodec.Bank 2)
    (foreign : Stack → List Bool) (output : List Bool) :
    ∃ t ≤ 5*((BitMachineBankCodec.encode bank).length+1),
      run t (BitMachineInline.cfg Label.alphabet id
        (some (.pair (.inl (.emit 0))))
        (CodeDAlphabetBank2Field15.frame foreign
          (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => [])
            (BitMachineBankCodec.encode bank) [] output))) =
      BitMachineInline.cfg Label.alphabet id
        (some (.pair (.inl (.emit 0))))
        (CodeDAlphabetBank2Field15.frame foreign
          (BitMachineBankCodec.parserCfg none (some true) bank [] [] output)) := by
  obtain ⟨t, ht, hr⟩ := CodeDAlphabetBank2Field15.parse_record bank foreign output
  refine ⟨t, ht, ?_⟩
  exact inline_some Label.alphabet id id (by intro v; rfl)
    (some (.pair (.inl (.emit 0)))) CodeDAlphabetBank2Field15.program
    (by intro l; rfl) _ t _ hr (by
      simp [CodeDAlphabetBank2Field15.frame, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        BitMachineBankCodec.parserCfg])

theorem pair_phase (x y : CodeDCodec.RawRat)
    (foreign : Stack → List Bool) (suffix : List Bool) :
    ∃ t ≤ 2*(CodeDPairProductTargetV2.pairBytes x y).length+2,
      ∃ S' : BitMachineBankSerialize.Bank 2,
        run t (BitMachineInline.cfg Label.pair id
          (some .clearPayload)
          (CodeDPairWeights15.frame foreign
            (BitMachineBankSerialize.cfg (some (.emit 0)) none
              (CodeDPairWeights15.pairBank x y) [] [] suffix))) =
        BitMachineInline.cfg Label.pair id
          (some .clearPayload)
          (CodeDPairWeights15.frame foreign
            (BitMachineBankSerialize.cfg none none S' [] []
              (CodeDPairProductTargetV2.pairBytes x y ++ suffix))) := by
  obtain ⟨t, ht, S', hr⟩ := CodeDPairWeights15.emit_pair x y foreign suffix
  refine ⟨t, ht, S', ?_⟩
  exact inline_some Label.pair id id (by intro v; rfl)
    (some .clearPayload) CodeDPairWeights15.program
    (by intro l; rfl) _ t _ hr (by
      simp [CodeDPairWeights15.frame, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        BitMachineBankSerialize.cfg])

theorem pair_phase_cleared (x y : CodeDCodec.RawRat)
    (foreign : Stack → List Bool) :
    ∃ t ≤ 2*(CodeDPairProductTargetV2.pairBytes x y).length+2,
      run t (BitMachineInline.cfg Label.pair id
        (some .clearPayload)
        (CodeDPairWeights15.frame foreign
          (BitMachineBankSerialize.cfg (some (.emit 0)) none
            (CodeDPairWeights15.pairBank x y) [] [] []))) =
      BitMachineInline.cfg Label.pair id
        (some .clearPayload)
        (CodeDPairWeights15.frame foreign
          (BitMachineBankSerialize.cfg none none
            (CodeDPairSerializerClear.cleared
              (CodeDPairWeights15.pairBank x y)) [] []
            (CodeDPairProductTargetV2.pairBytes x y))) := by
  obtain ⟨t, ht, hr⟩ := CodeDPairWeights15.emit_pair_cleared x y foreign
  refine ⟨t, ht, ?_⟩
  exact inline_some Label.pair id id (by intro v; rfl)
    (some .clearPayload) CodeDPairWeights15.program
    (by intro l; rfl) _ t _ hr (by
      simp [CodeDPairWeights15.frame, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        BitMachineBankSerialize.cfg])

theorem frame_phase (request : List Bool)
    (foreign : Stack → List Bool) (suffix : List Bool) :
    ∃ t ≤ 2*(EncodedCommunication.field request).length+2,
      ∃ S' : BitMachineBankSerialize.Bank 1,
        run t (BitMachineInline.cfg Label.frame id
          (some (.append .saveScan))
          (CodeDFramePair15.frame foreign
            (BitMachineBankSerialize.cfg (some (.emit 0)) none
              (CodeDFramePair15.oneBank request) [] [] suffix))) =
        BitMachineInline.cfg Label.frame id
          (some (.append .saveScan))
          (CodeDFramePair15.frame foreign
            (BitMachineBankSerialize.cfg none none S' [] []
              (EncodedCommunication.field request ++ suffix))) := by
  obtain ⟨t, ht, S', hr⟩ := CodeDFramePair15.emit_field request foreign suffix
  refine ⟨t, ht, S', ?_⟩
  exact inline_some Label.frame id id (by intro v; rfl)
    (some (.append .saveScan)) CodeDFramePair15.program
    (by intro l; rfl) _ t _ hr (by
      simp [CodeDFramePair15.frame, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        BitMachineBankSerialize.cfg])

theorem append_phase (foreign : Stack → List Bool)
    (output payload : List Bool) (h11 : foreign 11 = [])
    (h14 : foreign 14 = []) :
    run (4 * output.length + 2 * payload.length + 6)
      (BitMachineInline.cfg Label.append Prod.snd none
        (⟨some .saveScan, ((), none),
          CodeDAppendAtEnd15.initialBank foreign output payload⟩ :
          CodeDAppendAtEnd15.Config)) =
      BitMachineInline.cfg Label.append Prod.snd none
        (⟨some .done, ((), none),
          Function.update
            (Function.update
              (Function.update
                (CodeDAppendAtEnd15.initialBank foreign output payload) 9 []) 5 [])
            9 (output ++ payload)⟩ : CodeDAppendAtEnd15.Config) := by
  have hr := CodeDAppendAtEnd15.append_run foreign output payload h11 h14
  exact inline_some Label.append Prod.snd (fun b => ((),b))
    (by intro v; cases v; rfl) none CodeDAppendAtEnd15.program
    (by intro l; rfl) _ _ _ hr (by simp)

theorem run_add {c d : Config} {t : Nat} (h : run t c = d) (u : Nat) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

theorem step_copy_done (S : Stack → List Bool) :
    advance program ⟨some (.copy (.inr ())), none, S⟩ =
      ⟨some (.source (.inl (.scan 0))), none, S⟩ := by
  rfl

theorem step_source_done (S : Stack → List Bool) :
    advance program ⟨some (.source (.inr ())), some true, S⟩ =
      ⟨some (.alphabet (.inl (.scan 0))), none, S⟩ := by
  rfl

theorem step_alphabet_done (S : Stack → List Bool) :
    advance program ⟨some (.alphabet (.inr ())), some true, S⟩ =
      ⟨some (.pair (.inl (.emit 0))), none, S⟩ := by
  rfl

theorem step_pair_done (S : Stack → List Bool) :
    advance program ⟨some (.pair (.inr ())), none, S⟩ =
      ⟨some .clearPayload, none, S⟩ := by
  rfl

theorem clear_payload_run (S : Stack → List Bool) :
    run ((S 5).length + 1) ⟨some .clearPayload, none, S⟩ =
      ⟨some (.frame (.inl (.emit 0))), none,
        Function.update S 5 []⟩ := by
  generalize hs : S 5 = bits
  induction bits generalizing S with
  | nil =>
      have hstep : advance program ⟨some .clearPayload, none, S⟩ =
          ⟨some (.frame (.inl (.emit 0))), none,
            Function.update S 5 []⟩ := by
        simp [advance, TM2.step, program, TM2.stepAux, hs,
          Function.update_eq_self]
      simpa [run, Function.iterate_one] using hstep
  | cons b bits ih =>
      have hstep : advance program ⟨some .clearPayload, none, S⟩ =
          ⟨some .clearPayload, none, Function.update S 5 bits⟩ := by
        simp [advance, TM2.step, program, TM2.stepAux, hs]
      rw [List.length_cons, show bits.length + 1 + 1 = (bits.length + 1) + 1 by omega]
      change run (bits.length + 1)
        (advance program ⟨some .clearPayload, none, S⟩) = _
      rw [hstep]
      simpa [Function.update_idem] using
        ih (Function.update S 5 bits) (Function.update_self 5 bits S)

theorem step_frame_done (S : Stack → List Bool) :
    advance program ⟨some (.frame (.inr ())), none, S⟩ =
      ⟨some (.append .saveScan), none, S⟩ := by
  rfl

theorem step_append_done (S : Stack → List Bool) :
    advance program ⟨some (.append .done), none, S⟩ =
      ⟨none, none, S⟩ := by
  rfl

#print axioms step_append_done

end CurrentAdditive.CodeDPairCallbackProgram
