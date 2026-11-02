import Paper2.SuccessXfer

/-! Unit 3, segments (5) and (6): ONE fixed program for the success branch, from the raw
success start bank to the encoded selected output.

`succProg = SuccessOrient.program ; (SuccessXfer.xfer ; WEntry.tableHeader)` on the joint bank
`SuccessXfer.JT` (each part placed by a fixed stack embedding, every handoff charged by the
production `BitMachineRawSequence`). Start bank:

* the admitted `SuccessOrient.startBank … word` (raw public unary counts and the written tape
  word `word = (select …).tapeBits tp`, literally the selected tape's bits);
* `preJH g r k thr output`: the header-join bank whose writer cells are the master region
  `restL g r`, unary `k`, the output prefix `output` and the unary threshold `thr`, every other
  cell BLANK; in particular it does not contain the sample, the codes, or `mX`/`mY`
  (`preJH_eq_blank`: it is the owner-8 writer entry bank with the six transfer destinations
  blanked, for EVERY sample);
* one blank scratch cell.

`success_run`: on a selected tape of the scheduled branch where the physical generator returns
`some bytes`, the program halts within an explicit clock with the success bank beside a
header bank whose output cell is `EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ output`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessRun

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling RecursiveRequestCodeShape
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)
open Paper2.SuccessXfer (OS JT dsts blank finJH wAux auxFw auxMy auxRc auxCc xfer xLmax
  rowsCell)

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The fixed writer cells before the transfer: master region and unary `K`, all else blank. -/
def auxPre (g : EncodedGraph.Graph) (r K : ℕ) : WEntry.Aux → List Bool :=
  Sum.elim (Paper2.RLoop.restL (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r)
    (Sum.elim ![[], [], [], [], List.replicate K true]
      (Sum.elim (fun _ => []) ![[], []]))

/-- The header-join start bank before the transfer (sample-free). -/
def preJH (g : EncodedGraph.Graph) (r K thr : ℕ) (output : List Bool) :
    JH WEntry.Kw → List Bool :=
  hjIn (MatrixTableWriter.ready
    (fun i => auxPre (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r K
      (WEntry.eqv.symm i)) 0 0 0 0 0 0 [] output).contents thr

theorem preJH_aux (g : EncodedGraph.Graph) (r K thr : ℕ) (output : List Bool) (a : WEntry.Aux) :
    preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r K thr output (wAux a) =
      auxPre (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r K a := by
  change auxPre g r K (WEntry.eqv.symm (WEntry.eqv a)) = _
  rw [Equiv.symm_apply_apply]

theorem preJH_eq_blank (g : EncodedGraph.Graph) (r K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (thr : ℕ) (output : List Bool) :
    preJH (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r K thr output =
      blank (finJH g r K mX mY xs ys thr output) := by
  funext a
  by_cases ha : ∃ i, dsts i = a
  · obtain ⟨i, rfl⟩ := ha
    rw [SuccessXfer.blank_dst]
    fin_cases i
    · exact preJH_aux g r K thr output auxFw
    · exact preJH_aux g r K thr output auxCc
    · exact preJH_aux g r K thr output auxRc
    · exact preJH_aux g r K thr output auxMy
    · rfl
    · rfl
  · rw [SuccessXfer.blank_off _ _ ha]
    rcases a with ((c | e) | h)
    · rcases c with c | c
      · obtain ⟨b, rfl⟩ := WEntry.eqv.surjective c
        change auxPre g r K (WEntry.eqv.symm (WEntry.eqv b)) =
          WEntry.auxBank g r K mX mY xs ys (WEntry.eqv.symm (WEntry.eqv b))
        rw [Equiv.symm_apply_apply]
        rcases b with b | (b | (b | b))
        · rfl
        · fin_cases b
          · rfl
          · rfl
          · exact absurd ⟨2, rfl⟩ ha
          · exact absurd ⟨1, rfl⟩ ha
          · rfl
        · rfl
        · fin_cases b
          · exact absurd ⟨0, rfl⟩ ha
          · exact absurd ⟨3, rfl⟩ ha
      · fin_cases c <;> rfl
    · cases e
      · exact absurd ⟨5, rfl⟩ ha
      · exact absurd ⟨4, rfl⟩ ha
      all_goals rfl
    · rfl

/-- Placements into the joint bank. -/
def oE : OS ↪ JT := ⟨Sum.inl, Sum.inl_injective⟩
def hE : JH WEntry.Kw ↪ JT :=
  ⟨fun a => .inr (.inl a), fun _ _ h => Sum.inl_injective (Sum.inr_injective h)⟩

theorem bank_oE (X : OS → List Bool) (Y : JH WEntry.Kw ⊕ Fin 1 → List Bool)
    (Z : OS → List Bool) : bank oE (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext c
  rcases c with c | c
  · exact bank_at oE _ Z c
  · exact bank_outside oE _ Z (.inr c) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_hE (X : OS → List Bool) (Y : JH WEntry.Kw → List Bool) (Z : JH WEntry.Kw → List Bool) :
    bank hE (Sum.elim X (Sum.elim Y (fun _ : Fin 1 => []))) Z =
      Sum.elim X (Sum.elim Z (fun _ : Fin 1 => [])) := by
  funext c
  rcases c with c | c | c
  · exact bank_outside hE _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at hE _ Z c
  · exact bank_outside hE _ Z (.inr (.inr c)) (by rintro ⟨k, hk⟩; cases hk)

def orientL := fun l => stackStmt oE (SuccessOrient.program l)
def headerL := fun l => stackStmt hE (WEntry.tableHeader l)

/-- The header start control (that of `WEntry.table_header`). -/
def hCtl := ((WEntry.wCtl, (none : Option Bool)), ((none : Option Bool), HeaderA.progCtl))

/-- Transfer then writer/header: ONE fixed program. -/
def tailProg := BitMachineRawSequence.program xfer headerL
  (SamplerFallbackJoin.labelOf WEntry.tableHeader (BitMachineRawSequence.leftLabel
    (.inr (.copy .rows)))) (none : Option Bool) hCtl

end

end Paper2.SuccessRun
