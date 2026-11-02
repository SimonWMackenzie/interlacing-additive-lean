import Paper2.FullSched
import Paper2.SamplerParameterJoin
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Paper2.PublicBitCountIdentity
import Paper2.A3H3Size

/-! A private physical splice from the graph-byte front to the exact-tape
preparation bank. No source owner or production module is changed. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048

namespace Paper2.FrontPreparedCut

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def prepSlots : SamplerParameterBank.Stack ↪ FullFront.JF :=
  ⟨fun j => .inr (.inr (.inl (.inl j))), by intro a b h; simpa using h⟩

def prepProgram := fun l => stackStmt prepSlots (SamplerParameterJoin.preparedCleanupProgram l)

theorem exitBankG_restrict (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : Nat) (word : List Bool)
    (FL : CountFront.LK → List Bool) (FQ : CountFront.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : Nat) (j : SamplerParameterBank.Stack) :
    SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word j =
      FullFront.exitBankG g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY (prepSlots j) := by
  cases j <;> rfl

theorem exitBankG_prep (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : Nat) (word : List Bool)
    (FL : CountFront.LK → List Bool) (FQ : CountFront.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : Nat) :
    bank prepSlots
      (FullFront.exitBankG g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY)
      (SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word) =
    FullFront.exitBankG g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY := by
  apply bank_eq_self
  exact exitBankG_restrict g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY

def prepBd (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool) : Nat :=
  let Bv := SamplerParameterJoin.B n p s q₁ q₂ w Q
  let Rv := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
  let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  let D := Nv * (Rv * Bv)
  SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY +
    MatrixAddressMachine.exactTime Rv Bv 0 +
    MatrixAddressMachine.exactTime Nv (Rv * Bv) 0 +
    D + word.length + Rv * Bv + D +
    (D + word.length + 4) * BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram +
    (D + word.length + 4) * BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram + 14

/-- The physical count preparation and exact tape cut, lifted into the raw-count
bank installed by the graph-byte front. Every consumer cell agrees with the
original fallback entry bank on precisely the selected tape prefix. -/
theorem lift_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : Nat) (word : List Bool)
    (FL : CountFront.LK → List Bool) (FQ : CountFront.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : Nat) :
    let E := FullFront.exitBankG g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY
    let Bv := SamplerParameterJoin.B n p s q₁ q₂ w Q
    let Rv := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    let D := Nv * (Rv * Bv)
    ∃ t ≤ prepBd n p s q₁ q₂ w Q k mX mY word,
      ∃ H : FullFront.JF → List Bool,
        ((advance prepProgram)^[t])
          (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
            (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)), E⟩ :
            TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
          ⟨none,
            (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none)), H⟩ ∧
        ∀ c : SamplerParameterBank.ConsumerStack,
          H (prepSlots (.inl c)) =
            SamplerParameterBank.initial n p s q₁ q₂ w Q k mX mY (word.take D) Bv Rv c := by
  dsimp
  obtain ⟨t, F, H, ht, hr, -, -, -, -, -, -, hcons⟩ :=
    SamplerParameterJoin.prepared_cleanup_run n p s q₁ q₂ w Q k mX mY word
  let E := FullFront.exitBankG g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY
  have hlift := BitMachineStackRun.run prepSlots E
    SamplerParameterJoin.preparedCleanupProgram
    (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)),
      SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word⟩ :
      TM2.Cfg (fun _ : SamplerParameterBank.Stack => Bool) _ _) t
  rw [hr] at hlift
  simp only [stackCfg] at hlift
  rw [exitBankG_prep g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY] at hlift
  refine ⟨t, ht, bank prepSlots E H, ?_, ?_⟩
  · exact hlift
  · intro c
    rw [bank_at]
    exact hcons c

def frontMX (a b Δ : Nat) (g : EncodedGraph.Graph) (k : Nat) : Nat :=
  FullFront.mXV
    (TMFront.thrVal k ![FullFront.pV g, FullFront.sV g, FullFront.q2V g,
      FullFront.wV g, FullFront.QV a b Δ g]) k (FullFront.Lg g)

def frontMY (a b Δ : Nat) (g : EncodedGraph.Graph) (k : Nat) : Nat :=
  FullFront.mYV
    (TMFront.thrVal k ![FullFront.pV g, FullFront.sV g, FullFront.q2V g,
      FullFront.wV g, FullFront.QV a b Δ g]) k

def frontD (a b Δ : Nat) (g : EncodedGraph.Graph) (k : Nat) : Nat :=
  SamplerNRProducer.N (FullFront.sV g) (FullFront.q1V g)
    (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g)
    (FullFront.pV g) k (frontMX a b Δ g k) (frontMY a b Δ g k) *
  (SamplerParameterJoin.R (FullFront.pV g) (FullFront.sV g)
    (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
    (FullFront.QV a b Δ g) k (frontMX a b Δ g k) (frontMY a b Δ g k) *
   SamplerParameterJoin.B g.vertices (FullFront.pV g) (FullFront.sV g)
    (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
    (FullFront.QV a b Δ g))

def fullPrepProgram (a b Δ : Nat) :=
  BitMachineRawSequence.program (FullFront.full a b Δ) prepProgram
    (.inl (.inl (.inl SamplerParameterJoin.startLabel)))
    FullFront.fullCtl
    (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))

/-- A single fixed physical program parses the encoded graph and public
schedule, prepares B/R/N and D=N(RB), cuts the raw random word to exactly D
bits, and cleans the consumer residue. The resulting consumer region is the
literal selected-tape fallback entry bank. -/
theorem full_prepared_run (a b Δ : Nat) (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : Nat) (word : List Bool) :
    let p := FullFront.pV g
    let s := FullFront.sV g
    let q₁ := FullFront.q1V g
    let q₂ := FullFront.q2V g
    let w := FullFront.wV g
    let Q := FullFront.QV a b Δ g
    let mX := frontMX a b Δ g k
    let mY := frontMY a b Δ g k
    let Bv := SamplerParameterJoin.B g.vertices p s q₁ q₂ w Q
    let Rv := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    let D := Nv * (Rv * Bv)
    ∃ t ≤ FullFront.fullBd a b Δ g k word +
      prepBd g.vertices p s q₁ q₂ w Q k mX mY word + 1,
      ∃ H : FullFront.JF → List Bool,
        ((advance (fullPrepProgram a b Δ))^[t])
          (⟨some (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ)),
            (FullFront.fullCtl,
              (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))),
            FullFront.F0 (FullFront.X0 g k word)⟩ :
            TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
          ⟨none,
            (FullFront.fullCtl,
              (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none))), H⟩ ∧
        ∀ c : SamplerParameterBank.ConsumerStack,
          H (prepSlots (.inl c)) =
            SamplerParameterBank.initial g.vertices p s q₁ q₂ w Q k mX mY
              (word.take D) Bv Rv c := by
  dsimp
  obtain ⟨tf, htf, vc, FL, FQ, FT, FM, hf, _, _, _, _⟩ :=
    FullFront.full_run a b Δ g hg k word
  obtain ⟨tp, htp, H, hp, hcons⟩ :=
    lift_run g hg k word FL FQ FT FM g.vertices
      (FullFront.pV g) (FullFront.sV g) (FullFront.q1V g)
      (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g)
      (frontMX a b Δ g k) (frontMY a b Δ g k)
  have hf' : ((advance (FullFront.full a b Δ))^[tf])
      (⟨some (FullFront.fullStart a b Δ), FullFront.fullCtl,
        FullFront.F0 (FullFront.X0 g k word)⟩ :
        TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
      ⟨none, vc, FullFront.exitBankG g hg k word FL FQ FT FM g.vertices
        (FullFront.pV g) (FullFront.sV g) (FullFront.q1V g)
        (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g)
        (frontMX a b Δ g k) (frontMY a b Δ g k)⟩ := by
    simpa only [FullFront.exitBank, frontMX, frontMY] using hf
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (FullFront.full a b Δ) prepProgram
    (FullFront.fullStart a b Δ)
    (.inl (.inl (.inl SamplerParameterJoin.startLabel)))
    FullFront.fullCtl vc
    (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))
    (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none))
    (FullFront.F0 (FullFront.X0 g k word))
    (FullFront.exitBankG g hg k word FL FQ FT FM g.vertices
      (FullFront.pV g) (FullFront.sV g) (FullFront.q1V g)
      (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g)
      (frontMX a b Δ g k) (frontMY a b Δ g k))
    H tf tp hf' hp
  refine ⟨t, ?_, H, ?_, ?_⟩
  · exact ht.trans (by omega)
  · exact hr
  · exact hcons

/-- A long enough fixed external tape yields exactly the typed capped-sampler
tape represented by the physically retained prefix. This is a semantic
repackaging after the charged physical cut, not a hidden machine operation. -/
theorem selected_tape (B R N : Nat) (word : List Bool)
    (hlen : N * (R * B) ≤ word.length) :
    ∃ tape : CappedSampler.Adaptive.Tape B R N,
      (RecursiveSamplingTape.writeTape B R N tape).val =
        word.take (N * (R * B)) := by
  let bits : RecursiveSamplingTape.SerializedTape B R N :=
    ⟨word.take (N * (R * B)), by
      simp [List.length_take, Nat.min_eq_left hlen, RecursiveSamplingTape.bitCount]⟩
  refine ⟨RecursiveSamplingTape.readTape B R N bits, ?_⟩
  rw [RecursiveSamplingTape.writeTape_readTape]

/-- On the scheduled branch, the physically multiplied count agrees with the
selected output's announced input-bit count, not merely an upper bound. -/
theorem frontD_eq_selected_inputBits (Δ : Nat) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : Nat)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ) :
    frontD γ.num.toNat γ.den Δ g k =
      (TotalFiniteConstructorScratch.select hn
        (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits := by
  let L := Nat.clog 2 g.vertices
  let r := ParameterizedCanonicalSource.restorationDepth L
  let q := ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length L Δ γ
  have hb := FullFront.budget_sched Δ γ hγ hΔ g hn hm k
  have hmX : frontMX γ.num.toNat γ.den Δ g k =
      SourceRecursiveNoSampling.sourceRows L r q k := by
    change FullFront.mXV
      (TMFront.thrVal k ![FullFront.pV g, FullFront.sV g, FullFront.q2V g,
        FullFront.wV g, FullFront.QV γ.num.toNat γ.den Δ g])
      k (FullFront.Lg g) = _
    rw [hb, MProducer.rows_eq]
    rfl
  have hmY : frontMY γ.num.toNat γ.den Δ g k =
      SourceRecursiveNoSampling.sourceCols L r q k := by
    change FullFront.mYV
      (TMFront.thrVal k ![FullFront.pV g, FullFront.sV g, FullFront.q2V g,
        FullFront.wV g, FullFront.QV γ.num.toNat γ.den Δ g]) k = _
    rw [hb, MProducer.cols_eq]
    rfl
  rw [TotalFiniteConstructorScratch.select_good hn
    (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc]
  change frontD γ.num.toNat γ.den Δ g k =
    RecursiveSamplingMaterialization.inputBitCount (Fin g.vertices)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ)
      (LookupSeed.width L) k
      (SourceRecursiveNoSampling.sourceRows L r q k)
      (SourceRecursiveNoSampling.sourceCols L r q k)
  unfold frontD
  rw [FullFront.pV_eq, FullFront.sV_eq, FullFront.q1V_eq,
    FullFront.q2V_eq, FullFront.wV_eq,
    FullFront.QV_eq Δ γ hγ hΔ g hn hm, hmX, hmY]
  exact (Paper2.FixedTape.PublicCount.bitCount_eq_producer_product
    g.vertices (LookupSeed.width L) (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ)
    k (SourceRecursiveNoSampling.sourceRows L r q k)
    (SourceRecursiveNoSampling.sourceCols L r q k)).symm

theorem frontD_le_selected_bound (Δ : Nat) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : Nat) (hk : 1 ≤ k)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ) :
    frontD γ.num.toNat γ.den Δ g k ≤ (g.vertices + 2) ^ (160 * (k + 1)) := by
  rw [frontD_eq_selected_inputBits Δ γ hγ hΔ g hg hn hm k hc]
  exact (TotalFiniteResourcesScratch.selected_announced_counts_le hn
    (CanonicalEdgeTape.graphEdge g hg) Δ γ k hk).2

/-- For each fixed gap parameter `k`, the physical count fits a fixed
monomial in the encoded graph packet length. The unary vertex field is charged
by the graph encoding, including isolated vertices. -/
theorem frontD_le_graph_monomial (Δ : Nat) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : Nat) (hk : 1 ≤ k)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ) :
    frontD γ.num.toNat γ.den Δ g k ≤
      ((EncodedGraph.encode g).length + 1) ^ (160 * (k + 1)) := by
  have hbase : g.vertices + 2 ≤ (EncodedGraph.encode g).length + 1 := by
    have h := EncodedGraph.encode_length_lower g
    omega
  exact (frontD_le_selected_bound Δ γ hγ hΔ g hg hn hm k hk hc).trans
    (Nat.pow_le_pow_left hbase _)


def fallbackSlots : CodeFallbackFullJoin.Stack ↪ FullFront.JF :=
  ⟨fun c => prepSlots (.inl c), by intro a b h; simpa [prepSlots] using h⟩

def fallbackProgram := fun l => stackStmt fallbackSlots (CodeFallbackFullJoin.program l)

/-- An actual checked fallback computation continues from the *same* cleaned
consumer cells, retaining all graph-front and preparation residue outside that
region. This is pure physical transport of the source run. -/
theorem fallback_lift_run (n p s q₁ q₂ w Q k mX mY B R : Nat)
    (word : List Bool) (H : FullFront.JF → List Bool)
    (hH : ∀ c : CodeFallbackFullJoin.Stack,
      H (fallbackSlots c) = CodeFallbackEntryJoin.initial
        n p s q₁ q₂ w Q k mX mY word B R c)
    (t : Nat) (d : CodeTableFallback.Config)
    (hRun : CodeFallbackAllOutcomes.Runs t n p s q₁ q₂ w Q k mX mY word B R d) :
    ((advance fallbackProgram)^[t])
      (⟨some SamplerFallbackJoin.fallbackStart,
        SamplerFallbackJoin.fallbackControl0, H⟩ :
        TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
      ⟨none, (CodeFallbackFullJoin.prepControl, d.var),
        bank fallbackSlots H
          (CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY word B R d)⟩ := by
  have hr := BitMachineStackRun.run fallbackSlots H CodeFallbackFullJoin.program
    (⟨some SamplerFallbackJoin.fallbackStart,
      SamplerFallbackJoin.fallbackControl0,
      CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY word B R⟩ :
      TM2.Cfg (fun _ : CodeFallbackFullJoin.Stack => Bool) _ _) t
  change ((advance CodeFallbackFullJoin.program)^[t])
    (⟨some SamplerFallbackJoin.fallbackStart,
      SamplerFallbackJoin.fallbackControl0,
      CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY word B R⟩ :
      TM2.Cfg (fun _ : CodeFallbackFullJoin.Stack => Bool) _ _) =
    ⟨none, (CodeFallbackFullJoin.prepControl, d.var),
      CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY word B R d⟩ at hRun
  rw [hRun] at hr
  simp only [stackCfg] at hr
  rw [bank_eq_self fallbackSlots H _ (fun c => (hH c).symm)] at hr
  exact hr

/-- On an arbitrary external word long enough to cover the physically
computed public count, the admitted fallback *machine* runs on precisely the
cut prefix. The only hypotheses are positivity of the source parameters and
the already-proved exact consumer-bank identity. -/
theorem fallback_selected_run (n p s q₁ q₂ w Q k mX mY : Nat)
    (hn : 0 < n) (hp : 0 < p) (hs : 4 ≤ s) (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂) (hw : 0 < w) (hQ : 0 < Q)
    (word : List Bool)
    (hlen : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY *
      (SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY *
        SamplerParameterJoin.B n p s q₁ q₂ w Q) ≤ word.length)
    (H : FullFront.JF → List Bool)
    (hH : ∀ c : CodeFallbackFullJoin.Stack,
      H (fallbackSlots c) = CodeFallbackEntryJoin.initial
        n p s q₁ q₂ w Q k mX mY
        (word.take (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY *
          (SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY *
            SamplerParameterJoin.B n p s q₁ q₂ w Q)))
        (SamplerParameterJoin.B n p s q₁ q₂ w Q)
        (SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY) c) :
    let Bv := SamplerParameterJoin.B n p s q₁ q₂ w Q
    let Rv := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    let D := Nv * (Rv * Bv)
    ∃ tape : CappedSampler.Adaptive.Tape Bv Rv Nv,
      (RecursiveSamplingTape.writeTape Bv Rv Nv tape).val = word.take D ∧
      ∃ t ≤ SamplerFallbackJoin.fallbackCap n p s q₁ q₂ w Q k mX mY,
        ∃ d : CodeTableFallback.Config,
          ((advance fallbackProgram)^[t])
            (⟨some SamplerFallbackJoin.fallbackStart,
              SamplerFallbackJoin.fallbackControl0, H⟩ :
              TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
            ⟨none, (CodeFallbackFullJoin.prepControl, d.var),
              bank fallbackSlots H
                (CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY
                  (word.take D) Bv Rv d)⟩ ∧
          CodeFallbackAllOutcomes.Outcome mX mY
            (GeneratorCode.run Bv Rv (le_refl _) Nv
              (GeneratorStateSize.initialBounded
                (SamplerFallbackJoin.root n p s q₁ q₂ w Q k mX mY)
                (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
                  hn hp hs hq₁ hq₂ hw hQ)) tape) d := by
  dsimp
  let Bv := SamplerParameterJoin.B n p s q₁ q₂ w Q
  let Rv := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
  let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  let D := Nv * (Rv * Bv)
  obtain ⟨tape, hword⟩ := selected_tape Bv Rv Nv word hlen
  have hab := SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
    hn hp hs hq₁ hq₂ hw hQ
  have hdraw := SamplerFallbackJoin.draw_bound n p s q₁ q₂ w Q k mX mY
    hn hp hs hq₁ hq₂ hw hQ
  have hpositive := SamplerFallbackJoin.root_positive n p s q₁ q₂ w Q k mX mY
    hn hp hs hq₁ hq₂ hw hQ
  obtain ⟨t, ht, d, _, hrun, hout⟩ :=
    CodeFallbackAllOutcomes.every_tape_halts_with_source_outcome
      n p s q₁ q₂ w Q k mX mY
      (SamplerFallbackJoin.Mv n p s q₁ q₂ w Q) Bv Rv Nv
      (by omega) hab (le_refl _) (SamplerFallbackJoin.R_pos p s q₁ q₂ w Q k mX mY)
      hpositive hdraw tape
  have hrun' : CodeFallbackAllOutcomes.Runs t n p s q₁ q₂ w Q k mX mY
      (word.take D) Bv Rv d := by
    simpa only [hword] using hrun
  refine ⟨tape, hword, t, ?_, d, ?_, ?_⟩
  · simpa only [SamplerFallbackJoin.fallbackCap, SamplerFallbackJoin.root,
      SamplerFallbackJoin.Bv, SamplerFallbackJoin.Rv, SamplerFallbackJoin.Nv]
      using ht
  · exact fallback_lift_run n p s q₁ q₂ w Q k mX mY Bv Rv
      (word.take D) H hH t d hrun'
  · exact hout

def fullFallbackProgram (a b Δ : Nat) :=
  BitMachineRawSequence.program (fullPrepProgram a b Δ) fallbackProgram
    SamplerFallbackJoin.fallbackStart
    (FullFront.fullCtl,
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)))
    SamplerFallbackJoin.fallbackControl0

/-- The graph-byte front, physically selected exact tape, and actual capped
fallback run form one fixed sequenced controller. No fixed-gap comparison or
matrix serialization is asserted here. -/
theorem full_fallback_selected_run (a b Δ : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (k : Nat) (word : List Bool)
    (hn : 0 < g.vertices)
    (hp : 0 < FullFront.pV g) (hs : 4 ≤ FullFront.sV g)
    (hq₁ : 0 < FullFront.q1V g) (hq₂ : 0 < FullFront.q2V g)
    (hw : 0 < FullFront.wV g) (hQ : 0 < FullFront.QV a b Δ g)
    (hlen : SamplerNRProducer.N (FullFront.sV g) (FullFront.q1V g)
      (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g)
      (FullFront.pV g) k (frontMX a b Δ g k) (frontMY a b Δ g k) *
      (SamplerParameterJoin.R (FullFront.pV g) (FullFront.sV g)
        (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
        (FullFront.QV a b Δ g) k (frontMX a b Δ g k) (frontMY a b Δ g k) *
       SamplerParameterJoin.B g.vertices (FullFront.pV g) (FullFront.sV g)
        (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
        (FullFront.QV a b Δ g)) ≤ word.length) :
    let p := FullFront.pV g
    let s := FullFront.sV g
    let q₁ := FullFront.q1V g
    let q₂ := FullFront.q2V g
    let w := FullFront.wV g
    let Q := FullFront.QV a b Δ g
    let mX := frontMX a b Δ g k
    let mY := frontMY a b Δ g k
    let Bv := SamplerParameterJoin.B g.vertices p s q₁ q₂ w Q
    let Rv := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    let D := Nv * (Rv * Bv)
    ∃ t ≤ FullFront.fullBd a b Δ g k word +
        prepBd g.vertices p s q₁ q₂ w Q k mX mY word + 1 +
        SamplerFallbackJoin.fallbackCap g.vertices p s q₁ q₂ w Q k mX mY + 1,
      ∃ tape : CappedSampler.Adaptive.Tape Bv Rv Nv,
        ∃ d : CodeTableFallback.Config,
          ∃ H : FullFront.JF → List Bool,
            (RecursiveSamplingTape.writeTape Bv Rv Nv tape).val = word.take D ∧
            ((advance (fullFallbackProgram a b Δ))^[t])
              (⟨some (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ))),
                ((FullFront.fullCtl,
                  (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))),
                  SamplerFallbackJoin.fallbackControl0),
                FullFront.F0 (FullFront.X0 g k word)⟩ :
                TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
              ⟨none,
                ((FullFront.fullCtl,
                  (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))),
                  (CodeFallbackFullJoin.prepControl, d.var)), H⟩ ∧
            CodeFallbackAllOutcomes.Outcome mX mY
              (GeneratorCode.run Bv Rv (le_refl _) Nv
                (GeneratorStateSize.initialBounded
                  (SamplerFallbackJoin.root g.vertices p s q₁ q₂ w Q k mX mY)
                  (SamplerFallbackJoin.alphabet_bound g.vertices p s q₁ q₂ w Q k mX mY
                    hn hp hs hq₁ hq₂ hw hQ)) tape) d := by
  dsimp
  obtain ⟨t₁, ht₁, H₁, h₁, hcons⟩ := full_prepared_run a b Δ g hg k word
  obtain ⟨tape, hword, t₂, ht₂, d, h₂, hout⟩ := fallback_selected_run
    g.vertices (FullFront.pV g) (FullFront.sV g) (FullFront.q1V g)
    (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g) k
    (frontMX a b Δ g k) (frontMY a b Δ g k)
    hn hp hs hq₁ hq₂ hw hQ word hlen H₁ (fun c => hcons c)
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (fullPrepProgram a b Δ) fallbackProgram
    (BitMachineRawSequence.leftLabel (FullFront.fullStart a b Δ))
    SamplerFallbackJoin.fallbackStart
    (FullFront.fullCtl,
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)))
    (FullFront.fullCtl,
      (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none)))
    SamplerFallbackJoin.fallbackControl0
    (CodeFallbackFullJoin.prepControl, d.var)
    (FullFront.F0 (FullFront.X0 g k word)) H₁
    (bank fallbackSlots H₁
      (CodeFallbackSourceResult.finalBank g.vertices (FullFront.pV g) (FullFront.sV g)
        (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
        (FullFront.QV a b Δ g) k (frontMX a b Δ g k) (frontMY a b Δ g k)
        (word.take (SamplerNRProducer.N (FullFront.sV g) (FullFront.q1V g)
          (FullFront.q2V g) (FullFront.wV g) (FullFront.QV a b Δ g)
          (FullFront.pV g) k (frontMX a b Δ g k) (frontMY a b Δ g k) *
          (SamplerParameterJoin.R (FullFront.pV g) (FullFront.sV g)
            (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
            (FullFront.QV a b Δ g) k (frontMX a b Δ g k) (frontMY a b Δ g k) *
            SamplerParameterJoin.B g.vertices (FullFront.pV g) (FullFront.sV g)
              (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
              (FullFront.QV a b Δ g))))
        (SamplerParameterJoin.B g.vertices (FullFront.pV g) (FullFront.sV g)
          (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
          (FullFront.QV a b Δ g))
        (SamplerParameterJoin.R (FullFront.pV g) (FullFront.sV g)
          (FullFront.q1V g) (FullFront.q2V g) (FullFront.wV g)
          (FullFront.QV a b Δ g) k (frontMX a b Δ g k) (frontMY a b Δ g k)) d))
    t₁ t₂ h₁ h₂
  refine ⟨t, ?_, tape, d, _, hword, hr, hout⟩
  omega

#print axioms full_prepared_run
#print axioms selected_tape
#print axioms fallback_lift_run
#print axioms fallback_selected_run
#print axioms full_fallback_selected_run
#print axioms frontD_eq_selected_inputBits
#print axioms frontD_le_selected_bound
#print axioms frontD_le_graph_monomial

end

end Paper2.FrontPreparedCut
