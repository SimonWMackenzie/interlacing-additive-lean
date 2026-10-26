import Paper2.SamplerFallbackJoin
import Paper2.SeqIf
import Paper2.CodeSampleOutputDecoder

/-! Status-preserving handoff from the no-preloaded fallback program into the
physical orientation of the successful sampled word.

One fixed program: the no-preloaded producer/fallback program
`SamplerFallbackJoin.program` runs on the left part of the bank; then one
transition reads the fallback's *actual* terminal status bit from finite
control (`true` exactly for `CodeTableFallback.embedInterpreter`, `false`
for `embedWriter`). On failure the composite halts with the printed zero
table and the fallback's own final control. On success it runs the checked
orientation `CodeSampleOutputDecoder.program` with its source aliased to the
fallback output cell (retained) and writes the forward successful word
into a fresh cell. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessOrient

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorStateSize

abbrev PreStack := SamplerParameterBank.Stack
abbrev Stack := PreStack ⊕ Fin 2

def preSlots : PreStack ↪ Stack := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

/-- The fallback's output cell inside the ambient bank. -/
def outCell : Stack :=
  .inl (.inl (CodeFallbackEntryBank.fallbackSlots CodeTableFallback.outputSlot))

def orientSlot : Fin 3 → Stack
  | 0 => outCell
  | 1 => .inr 0
  | _ => .inr 1

theorem orientSlot_injective : Function.Injective orientSlot := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [orientSlot, outCell]

def orientSlots : Fin 3 ↪ Stack := ⟨orientSlot, orientSlot_injective⟩

def preProgram := fun l => stackStmt preSlots (SamplerFallbackJoin.program l)
def orientProgram :=
  fun l => stackStmt orientSlots (CodeSampleOutputDecoder.program l)

/-- Label and control types of a fixed program (type-level projections). -/
@[reducible] def LabelOf {L V K : Type*}
    (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type _ := L
@[reducible] def ControlOf {L V K : Type*}
    (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type _ := V

abbrev PreLabel := LabelOf SamplerFallbackJoin.program
abbrev PreControl := ControlOf SamplerFallbackJoin.program

/-- The status bit of the fallback's final control (`true` exactly for
`CodeTableFallback.embedInterpreter`). -/
def status (v : PreControl) : Bool := v.2.2.1.2

theorem status_interpreter (u : _) (v : CodeFullPadding.Control) :
    status (u, (CodeFallbackFullJoin.prepControl,
      CodeTableFallback.embedInterpreter v)) = true := rfl
theorem status_writer (u : _) (v : CodeTableFallback.WriterControl) :
    status (u, (CodeFallbackFullJoin.prepControl,
      CodeTableFallback.embedWriter v)) = false := rfl

def program := SeqIf.program preProgram status orientProgram (.copy .scan)
  SamplerFallbackJoin.startControl (none : Option Bool)

abbrev SLabel := SeqIf.Label PreLabel CodeSampleOutputDecoder.Label
abbrev SControl := SeqIf.Control PreControl (Option Bool)

def startLabel := SamplerFallbackJoin.labelOf program
  (SeqIf.leftLabel SamplerFallbackJoin.startLabel)
def startControl := (SamplerFallbackJoin.startControl, (none : Option Bool))

def startBank (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    Stack → List Bool :=
  Sum.elim (SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY tape)
    (fun _ => [])

theorem bank_pre (X Z : PreStack → List Bool) (Y : Fin 2 → List Bool) :
    bank preSlots (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext j
  cases j with
  | inl j => exact bank_at preSlots _ Z j
  | inr j => exact bank_outside preSlots _ Z (.inr j) (by rintro ⟨k, hk⟩; cases hk)

abbrev Bv := SamplerFallbackJoin.Bv
abbrev Rv := SamplerFallbackJoin.Rv
abbrev Nv := SamplerFallbackJoin.Nv
abbrev root := SamplerFallbackJoin.root

/-- The ambient bank right after the fallback program halts. -/
def fallbackBank (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (B R : Nat) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool) : Stack → List Bool :=
  Sum.elim (Sum.elim (CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY
    word B R d) G) (fun _ => [])

theorem fallbackBank_out (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (B R : Nat) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool) :
    fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G outCell =
      d.stk CodeTableFallback.outputSlot := by
  show bank CodeFallbackEntryBank.fallbackSlots _ d.stk
    (CodeFallbackEntryBank.fallbackSlots CodeTableFallback.outputSlot) = _
  exact bank_at _ _ _ _

/-- Result predicate: on success the forward successful word is in cell
`.inr 1` (the reversed original retained in `outCell`); on failure the bank
is exactly the fallback's final bank (zero table printed). -/
def Result (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool) (B R : Nat)
    (result : Option (List Bool)) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool)
    (c : TM2.Cfg (fun _ : Stack => Bool) SLabel SControl) : Prop :=
  match result with
  | some bytes =>
      c = ⟨none, (SamplerFallbackJoin.startControl, none),
        Function.update (fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G)
          (.inr 1) bytes⟩ ∧
      fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G outCell = bytes.reverse
  | none =>
      c = ⟨none, ((SamplerParameterJoin.startControl,
          (CodeFallbackFullJoin.prepControl, d.var)), none),
        fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G⟩

def outputTime (result : Option (List Bool)) : Nat :=
  match result with
  | some bytes => 3 * bytes.length + 4
  | none => 1

theorem run (n p s q₁ q₂ w Q k mX mY : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q)
    (tape : CappedSampler.Adaptive.Tape (Bv n p s q₁ q₂ w Q)
      (Rv p s q₁ q₂ w Q k mX mY) (Nv p s q₁ q₂ w Q k mX mY)) :
    let word := (RecursiveSamplingTape.writeTape (Bv n p s q₁ q₂ w Q)
      (Rv p s q₁ q₂ w Q k mX mY) (Nv p s q₁ q₂ w Q k mX mY) tape).val
    let result := GeneratorCode.run (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY)
      (le_refl _) (Nv p s q₁ q₂ w Q k mX mY)
      (initialBounded (root n p s q₁ q₂ w Q k mX mY)
        (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
          hn hp hs hq₁ hq₂ hw hQ)) tape
    ∃ (t : Nat) (d : CodeTableFallback.Config)
      (G : SamplerParameterBank.Private → List Bool),
      t ≤ SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + outputTime result ∧
      d.l = none ∧ G (.inr (.inr 0)) = [] ∧
      CodeFallbackAllOutcomes.Outcome mX mY result d ∧
      Result n p s q₁ q₂ w Q k mX mY word (Bv n p s q₁ q₂ w Q)
        (Rv p s q₁ q₂ w Q k mX mY) result d G
        (((advance program)^[t])
          ⟨some startLabel, startControl,
            startBank n p s q₁ q₂ w Q k mX mY word⟩) := by
  intro word result
  obtain ⟨t₀, ht₀, d, G, hd, hG, hrun, hout⟩ :=
    SamplerFallbackJoin.every_tape_halts_no_preload n p s q₁ q₂ w Q k mX mY
      hn hp hs hq₁ hq₂ hw hQ tape
  let W := fallbackBank n p s q₁ q₂ w Q k mX mY word (Bv n p s q₁ q₂ w Q)
    (Rv p s q₁ q₂ w Q k mX mY) d G
  have hpre : ((advance preProgram)^[t₀])
      (⟨some SamplerFallbackJoin.startLabel, SamplerFallbackJoin.startControl,
        Sum.elim (SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word)
          (fun _ => [])⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (SamplerParameterJoin.startControl,
        (CodeFallbackFullJoin.prepControl, d.var)), W⟩ := by
    have hr := BitMachineStackRun.run preSlots
      (Sum.elim (SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word)
        (fun _ : Fin 2 => []))
      SamplerFallbackJoin.program
      (⟨some SamplerFallbackJoin.startLabel, SamplerFallbackJoin.startControl,
        SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word⟩ :
        TM2.Cfg (fun _ : PreStack => Bool) _ _) t₀
    rw [hrun] at hr
    simp only [stackCfg, bank_pre] at hr
    exact hr
  have houtR : CodeFallbackAllOutcomes.Outcome mX mY result d := hout
  cases hres : result with
  | none =>
    have hgoal : CodeFallbackAllOutcomes.Outcome mX mY none d := by
      rw [← hres]; exact houtR
    have hout' := hgoal
    simp only [CodeFallbackAllOutcomes.Outcome] at hout'
    obtain ⟨a, wc, hdeq⟩ := hout'
    have hst : status (SamplerParameterJoin.startControl,
        (CodeFallbackFullJoin.prepControl, d.var)) = false := by
      rw [hdeq]; rfl
    obtain ⟨t, ht, hr⟩ := SeqIf.runs_stop preProgram status orientProgram
      (.copy .scan) SamplerFallbackJoin.startControl none
      SamplerFallbackJoin.startLabel SamplerFallbackJoin.startControl
      (SamplerParameterJoin.startControl, (CodeFallbackFullJoin.prepControl, d.var))
      _ W t₀ hpre hst
    refine ⟨t, d, G, ?_, hd, hG, hgoal, ?_⟩
    · simp only [outputTime]; omega
    · simp only [Result]
      exact hr
  | some bytes =>
    have hgoal : CodeFallbackAllOutcomes.Outcome mX mY (some bytes) d := by
      rw [← hres]; exact houtR
    have hout' := hgoal
    simp only [CodeFallbackAllOutcomes.Outcome] at hout'
    obtain ⟨a, hdeq, hobs, _htape⟩ := hout'
    have hst : status (SamplerParameterJoin.startControl,
        (CodeFallbackFullJoin.prepControl, d.var)) = true := by
      rw [hdeq]; rfl
    have hW0 : W outCell = d.stk CodeTableFallback.outputSlot :=
      fallbackBank_out n p s q₁ q₂ w Q k mX mY word _ _ d G
    have hWout : W outCell = bytes.reverse := by
      rw [hW0, hdeq]
      change a.stk CodeHeaderDraw.output = bytes.reverse
      unfold CodeFullRun.observed at hobs
      split_ifs at hobs with hdone
      simp only [Option.some.injEq] at hobs
      rw [← hobs, List.reverse_reverse]
    obtain ⟨tor, htor, hor⟩ := CodeSampleOutputDecoder.orient_run bytes.reverse
    have hor' : ((advance orientProgram)^[tor])
        (⟨some (.copy .scan), none, W⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, none, Function.update W (.inr 1) bytes⟩ := by
      have hr := BitMachineStackRun.run orientSlots W CodeSampleOutputDecoder.program
        (CodeSampleOutputDecoder.cfg (some (.copy .scan)) none bytes.reverse [] []) tor
      change ((advance CodeSampleOutputDecoder.program)^[tor]) _ = _ at hor
      rw [hor] at hr
      have hstart : bank orientSlots W
          (BitMachineCopy.stackContents bytes.reverse [] []) = W := by
        apply bank_eq_self
        intro j
        fin_cases j
        · exact hWout.symm
        · rfl
        · rfl
      have hend : bank orientSlots W
          (BitMachineCopy.stackContents bytes.reverse [] bytes.reverse.reverse) =
          Function.update W (.inr 1) bytes := by
        rw [List.reverse_reverse]
        have : BitMachineCopy.stackContents bytes.reverse [] bytes =
            Function.update (fun j => W (orientSlots j)) 2 bytes := by
          funext j
          fin_cases j
          · exact hWout.symm
          · rfl
          · rfl
        rw [this, bank_update, bank_restrict]
        rfl
      simp only [stackCfg, CodeSampleOutputDecoder.cfg] at hr
      rw [hstart, hend] at hr
      exact hr
    obtain ⟨t, ht, hr⟩ := SeqIf.runs_ok preProgram status orientProgram
      (.copy .scan) SamplerFallbackJoin.startControl none
      SamplerFallbackJoin.startLabel SamplerFallbackJoin.startControl
      (SamplerParameterJoin.startControl, (CodeFallbackFullJoin.prepControl, d.var))
      none _ W _ t₀ tor hpre hst hor'
    refine ⟨t, d, G, ?_, hd, hG, hgoal, ?_⟩
    · simp only [outputTime, List.length_reverse] at htor ⊢
      omega
    · simp only [Result]
      exact ⟨hr, hWout⟩

end

#print axioms run

end Paper2.SuccessOrient
