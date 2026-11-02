import Paper2.SamplerParameterJoin
import Paper2.CodeFallbackAllOutcomes
import Paper2.CodeFullRunConsumer
import Paper2.GeneratorPositive

/-! No-preloaded-B/R all-outcomes endpoint.

The fixed program first runs the joined public-parameter producer
(`SamplerParameterJoin.program`), which writes the physically produced
`B = clog₂ (alphabetCap …)` and `R = rejectionAttemptCap (drawCap …)` into
the consumer cells `d 11`, `d 12`, and then runs the admitted
`CodeFallbackFullJoin.program` on the consumer region. The only initial
data are the raw public unary counts and the written random tape word; the
consumer cap cells start empty. The outcome predicate is the admitted
`CodeFallbackAllOutcomes.Outcome` of the actual `GeneratorCode.run` on the
same tape. The source alphabet/draw bounds and code positivity are
discharged from the checked production lemmas for positive raw counts. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048

namespace Paper2.SamplerFallbackJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorStateSize
open Paper2.SamplerParameterBank

def consumerSlots : ConsumerStack ↪ Stack :=
  ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

def fallbackProgram :=
  fun l => stackStmt consumerSlots (CodeFallbackFullJoin.program l)

/-- Type-directed identity: fixes a label's type from the program. -/
def labelOf {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (l : L) : L := l

def fallbackStart := labelOf CodeFallbackFullJoin.program
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              CodeGeneratorSampleJoin.compilerStart))))))

def fallbackControl0 :=
  (CodeFallbackFullJoin.prepControl, CodeFallbackFullJoin.fallbackControl)

def program := BitMachineRawSequence.program SamplerParameterJoin.program
  fallbackProgram fallbackStart SamplerParameterJoin.startControl fallbackControl0

def startLabel := labelOf program
  (BitMachineRawSequence.leftLabel SamplerParameterJoin.startLabel)
def startControl := (SamplerParameterJoin.startControl, fallbackControl0)

/-! ### Public values -/

abbrev root (n p s q₁ q₂ w Q k mX mY : Nat) : Code :=
  CodeFallbackSourceResult.sampleRoot n p s q₁ q₂ w Q k mX mY
abbrev Mv (n p s q₁ q₂ w Q : Nat) := SamplerParameterJoin.M n p s q₁ q₂ w Q
abbrev Bv (n p s q₁ q₂ w Q : Nat) := SamplerParameterJoin.B n p s q₁ q₂ w Q
abbrev Rv (p s q₁ q₂ w Q k mX mY : Nat) := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
abbrev Nv (p s q₁ q₂ w Q k mX mY : Nat) :=
  RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY

theorem root_eq (n p s q₁ q₂ w Q k mX mY : Nat) :
    root n p s q₁ q₂ w Q k mX mY =
      GeneratorFullSample.seedSampleCode n p s q₁ q₂ w Q k mX mY := rfl

/-- Source alphabet bound for the same sample code, from the checked
production lemma (the activity and tails arguments of that lemma are fixed
canonical defaults; the bound does not depend on them). -/
theorem alphabet_bound (n p s q₁ q₂ w Q k mX mY : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q) :
    (meaning (root n p s q₁ q₂ w Q k mX mY)).maxAlphabet ≤
      Mv n p s q₁ q₂ w Q := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero s := ⟨by omega⟩
  haveI : NeZero q₁ := ⟨by omega⟩
  haveI : NeZero q₂ := ⟨by omega⟩
  haveI : NeZero w := ⟨by omega⟩
  haveI : NeZero Q := ⟨by omega⟩
  rw [root_eq]
  exact CodeFullRunConsumer.seed_sample_code_alphabet_cap hp hs
    (fun _ _ => none)
    (RecursiveEntries.defaultTails (fun _ : Fin p => false) (⟨0, hp⟩ : Fin p)
      ((⟨0, by omega⟩, .inl ⟨0, hn⟩) : SourceConstruction.Items s (Fin n))
      hq₂ hw hQ)
    k mX mY

theorem draw_bound (n p s q₁ q₂ w Q k mX mY : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q) :
    (meaning (root n p s q₁ q₂ w Q k mX mY)).maxDraws ≤
      Nv p s q₁ q₂ w Q k mX mY := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero q₁ := ⟨by omega⟩
  haveI : NeZero q₂ := ⟨by omega⟩
  haveI : NeZero w := ⟨by omega⟩
  haveI : NeZero Q := ⟨by omega⟩
  rw [root_eq]
  exact CodeFullRunConsumer.seed_sample_code_draw_cap hp hs k mX mY

theorem root_positive (n p s q₁ q₂ w Q k mX mY : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q) :
    GeneratorPositive.Positive (root n p s q₁ q₂ w Q k mX mY) := by
  have h := GeneratorPositive.positive_seedRecursiveCodes n p s q₁ q₂ w Q k
    hn hp hs hq₁ hq₂ hw hQ
  exact ⟨GeneratorPositive.positive_copies mY _ h.2,
    GeneratorPositive.positive_copies mX _ h.1⟩

theorem R_pos (p s q₁ q₂ w Q k mX mY : Nat) : 0 < Rv p s q₁ q₂ w Q k mX mY := by
  show 0 < SamplerNRProducer.R s q₁ q₂ w Q p k mX mY
  rw [SamplerNRProducer.R_eq]
  omega

theorem bank_consumer (X Y : ConsumerStack → List Bool) (G : Private → List Bool) :
    bank consumerSlots (Sum.elim X G) Y = Sum.elim Y G := by
  funext j
  cases j with
  | inl j => exact bank_at consumerSlots _ Y j
  | inr j => exact bank_outside consumerSlots _ Y (.inr j) (by rintro ⟨k, hk⟩; cases hk)

def fallbackCap (n p s q₁ q₂ w Q k mX mY : Nat) : Nat :=
  CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY +
    max ((codeSize (root n p s q₁ q₂ w Q k mX mY)+1) *
        CodeFullRepeatPublic.repeatStepCap (root n p s q₁ q₂ w Q k mX mY)
          (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY) +
        Nv p s q₁ q₂ w Q k mX mY *
          (Rv p s q₁ q₂ w Q k mX mY * Bv n p s q₁ q₂ w Q) + 4)
      (CodeTableFallback.sourceFailureCap (root n p s q₁ q₂ w Q k mX mY)
        (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY) mX mY + 1)

def clock (n p s q₁ q₂ w Q k mX mY : Nat) : Nat :=
  SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY + 1 +
    fallbackCap n p s q₁ q₂ w Q k mX mY

/-- For every capped random tape of the produced shape, the fixed program
started with only raw public counts and the written tape word (both cap
cells empty) halts, and its consumer region is the admitted fallback
final bank whose configuration satisfies the source outcome predicate for
the actual `GeneratorCode.run` on the same tape. -/
theorem every_tape_halts_no_preload (n p s q₁ q₂ w Q k mX mY : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hw : 0 < w) (hQ : 0 < Q)
    (tape : CappedSampler.Adaptive.Tape (Bv n p s q₁ q₂ w Q)
      (Rv p s q₁ q₂ w Q k mX mY) (Nv p s q₁ q₂ w Q k mX mY)) :
    ∃ t ≤ clock n p s q₁ q₂ w Q k mX mY,
      ∃ (d : CodeTableFallback.Config) (G : Private → List Bool),
        d.l = none ∧ G (.inr (.inr 0)) = [] ∧
        ((advance program)^[t])
          (⟨some startLabel, startControl,
            SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY
              (RecursiveSamplingTape.writeTape (Bv n p s q₁ q₂ w Q)
                (Rv p s q₁ q₂ w Q k mX mY) (Nv p s q₁ q₂ w Q k mX mY) tape).val⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, (SamplerParameterJoin.startControl,
              (CodeFallbackFullJoin.prepControl, d.var)),
            Sum.elim (CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY
              (RecursiveSamplingTape.writeTape (Bv n p s q₁ q₂ w Q)
                (Rv p s q₁ q₂ w Q k mX mY) (Nv p s q₁ q₂ w Q k mX mY) tape).val
              (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY) d) G⟩ ∧
        CodeFallbackAllOutcomes.Outcome mX mY
          (GeneratorCode.run (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY)
            (le_refl _) (Nv p s q₁ q₂ w Q k mX mY)
            (initialBounded (root n p s q₁ q₂ w Q k mX mY)
              (alphabet_bound n p s q₁ q₂ w Q k mX mY hn hp hs hq₁ hq₂ hw hQ))
            tape) d := by
  let word := (RecursiveSamplingTape.writeTape (Bv n p s q₁ q₂ w Q)
    (Rv p s q₁ q₂ w Q k mX mY) (Nv p s q₁ q₂ w Q k mX mY) tape).val
  obtain ⟨t₁, G, ht₁, h₁, hG⟩ :=
    SamplerParameterJoin.run n p s q₁ q₂ w Q k mX mY word
  obtain ⟨t₂, ht₂, d, hd, hruns, hout⟩ :=
    CodeFallbackAllOutcomes.every_tape_halts_with_source_outcome
      n p s q₁ q₂ w Q k mX mY (Mv n p s q₁ q₂ w Q) (Bv n p s q₁ q₂ w Q)
      (Rv p s q₁ q₂ w Q k mX mY) (Nv p s q₁ q₂ w Q k mX mY)
      (by omega)
      (alphabet_bound n p s q₁ q₂ w Q k mX mY hn hp hs hq₁ hq₂ hw hQ)
      (le_refl _) (R_pos p s q₁ q₂ w Q k mX mY)
      (root_positive n p s q₁ q₂ w Q k mX mY hn hp hs hq₁ hq₂ hw hQ)
      (draw_bound n p s q₁ q₂ w Q k mX mY hn hp hs hq₁ hq₂ hw hQ)
      tape
  have h₂ := BitMachineStackRun.run consumerSlots
    (Sum.elim (initial n p s q₁ q₂ w Q k mX mY word
      (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY)) G)
    CodeFallbackFullJoin.program
    (⟨some fallbackStart, fallbackControl0,
      CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY word
        (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY)⟩ :
      TM2.Cfg (fun _ : CodeFallbackFullJoin.Stack => Bool) _ _) t₂
  rw [show ((advance CodeFallbackFullJoin.program)^[t₂])
      (⟨some fallbackStart, fallbackControl0,
        CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY word
          (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY)⟩ :
        TM2.Cfg (fun _ : CodeFallbackFullJoin.Stack => Bool) _ _) = _ from hruns] at h₂
  simp only [stackCfg, bank_consumer] at h₂
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    SamplerParameterJoin.program fallbackProgram
    SamplerParameterJoin.startLabel fallbackStart
    SamplerParameterJoin.startControl SamplerParameterJoin.finalControl
    fallbackControl0 (CodeFallbackFullJoin.prepControl, d.var)
    (SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word)
    (Sum.elim (initial n p s q₁ q₂ w Q k mX mY word
      (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY)) G)
    (Sum.elim (CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY word
      (Bv n p s q₁ q₂ w Q) (Rv p s q₁ q₂ w Q k mX mY) d) G)
    t₁ t₂ h₁ h₂
  refine ⟨t, ?_, d, G, hd, hG, hr, hout⟩
  have ht₂' : t₂ ≤ fallbackCap n p s q₁ q₂ w Q k mX mY := ht₂
  simp only [clock]
  omega

end

#print axioms alphabet_bound
#print axioms draw_bound
#print axioms root_positive
#print axioms every_tape_halts_no_preload

end Paper2.SamplerFallbackJoin
