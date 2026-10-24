import Paper2.SuccessOrient
import Paper2.SuccessCodec

/-! Segment 2, residue item (1): the checked indexed label fetch
(`FetchIndexed.col_fetch` / `row_fetch`) joined to the actual bank left by
`SuccessOrient.program` on a successful sample.

* The forward successful word is the orientation output cell `.inr 1`.
* The serialized column / row codes are the codes retained by
  `CodeSampleAssembly.final` at cells 6 / 1 (`sampleCell 6`, `sampleCell 1`);
  the fallback program never writes there (outside `fallbackSlots`).
* The unary column count `mY` is the fallback writer's retained `cols` cell
  (`CodeTableFallback.writerData mX mY`, unchanged on success).
* The fetch scratch (the `FetchLabel` bank including the label cell) and the
  unary index cell are fresh blank / supplied cells beside that bank.

The fetched label word is identified with the codec encoding of the sampled
label via `SuccessCodec.success_codec`: `C.2.encode (ys y)` for a column and
`C.1.encode (xs x)` for a row, where `bytes` is literally the columns-first
concatenation of those encodings. No prefix-code decoding argument is needed:
the fetch theorems hold for every decomposition into produced words, and the
program is deterministic. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessFetchJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveRequestCodeShape
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling
open OutputSkipper (Shape)

/-! ### Generic lift of the fetch programs into an ambient bank -/

def lblF : FetchIndexed.Stack := .inl FetchLabel.lblC

theorem FB_blank (fw cc rc my idx : List Bool) (j : FetchIndexed.Inner) :
    FetchIndexed.FB [] [] [] [] fw cc rc my idx (.inl j) = [] := by
  rcases j with ((j | j) | j) <;> fin_cases j <;> rfl

theorem FB_lbl (O code cnt lbl fw cc rc my idx : List Bool) :
    FetchIndexed.FB O code cnt lbl fw cc rc my idx =
      Function.update (FetchIndexed.FB O code cnt [] fw cc rc my idx) lblF lbl := by
  funext j; rcases j with (((j | j) | j) | j) | j <;> first | (fin_cases j <;> rfl) | rfl

section Lift

variable {J : Type*} [DecidableEq J]

theorem start_bank (e : FetchIndexed.Stack ↪ J) (W : J → List Bool) (fw idx : List Bool)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = fw) (hidx : W (e FetchIndexed.idxC) = idx) :
    bank e W (FetchIndexed.FB [] [] [] [] fw (W (e FetchIndexed.ccC))
      (W (e FetchIndexed.rcC)) (W (e FetchIndexed.myC)) idx) = W := by
  apply bank_eq_self
  intro j
  rcases j with j | j
  · rw [hin j, FB_blank]
  · fin_cases j
    · exact hfw.symm
    · rfl
    · rfl
    · rfl
    · exact hidx.symm

theorem lift_col (e : FetchIndexed.Stack ↪ J) (W : J → List Bool)
    (col : Code) (hcol : Shape col) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, Produces (meaning col) c) (O : List Bool) (y : Nat) (hy : y < cs.length)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = cs.flatten ++ O)
    (hcc : W (e FetchIndexed.ccC) = encodeCode col)
    (hidx : W (e FetchIndexed.idxC) = List.replicate y true) :
    ∃ t ≤ FetchIndexed.colBound col cs y O, ∃ v,
      ((advance (fun l => stackStmt e (FetchIndexed.colProgram l)))^[t])
        (⟨some FetchIndexed.colStart, FetchIndexed.colControl, W⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update W (e lblF) (cs.getD y [])⟩ := by
  obtain ⟨t, ht, v, hr⟩ := FetchIndexed.col_fetch col hcol cs hcs O y hy
    (W (e FetchIndexed.ccC)) (W (e FetchIndexed.rcC)) (W (e FetchIndexed.myC)) hcc
  refine ⟨t, ht, v, ?_⟩
  have hstart := start_bank e W (cs.flatten ++ O) (List.replicate y true) hin hfw hidx
  have hend : bank e W (FetchIndexed.FB [] [] [] (cs.getD y []) (cs.flatten ++ O)
      (W (e FetchIndexed.ccC)) (W (e FetchIndexed.rcC)) (W (e FetchIndexed.myC))
      (List.replicate y true)) = Function.update W (e lblF) (cs.getD y []) := by
    rw [FB_lbl, bank_update, hstart]
  have h := BitMachineStackRun.run e W FetchIndexed.colProgram
    (⟨some FetchIndexed.colStart, FetchIndexed.colControl,
      FetchIndexed.FB [] [] [] [] (cs.flatten ++ O) (W (e FetchIndexed.ccC))
        (W (e FetchIndexed.rcC)) (W (e FetchIndexed.myC)) (List.replicate y true)⟩ :
      TM2.Cfg (fun _ : FetchIndexed.Stack => Bool) _ _) t
  rw [hr] at h
  simp only [stackCfg] at h
  rw [hstart, hend] at h
  exact h

theorem lift_row (e : FetchIndexed.Stack ↪ J) (W : J → List Bool)
    (col row : Code) (hcol : Shape col) (hrow : Shape row) (cs rs : List (List Bool))
    (hcs : ∀ c ∈ cs, Produces (meaning col) c) (hrs : ∀ r ∈ rs, Produces (meaning row) r)
    (O : List Bool) (x : Nat) (hx : x < rs.length)
    (hin : ∀ j, W (e (.inl j)) = [])
    (hfw : W (e FetchIndexed.fwC) = cs.flatten ++ rs.flatten ++ O)
    (hcc : W (e FetchIndexed.ccC) = encodeCode col)
    (hrc : W (e FetchIndexed.rcC) = encodeCode row)
    (hmy : W (e FetchIndexed.myC) = List.replicate cs.length true)
    (hidx : W (e FetchIndexed.idxC) = List.replicate x true) :
    ∃ t ≤ FetchIndexed.rowBound col row cs rs x O, ∃ v,
      ((advance (fun l => stackStmt e (FetchIndexed.rowProgram l)))^[t])
        (⟨some FetchIndexed.rowStart, FetchIndexed.rowControl, W⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update W (e lblF) (rs.getD x [])⟩ := by
  obtain ⟨t, ht, v, hr⟩ := FetchIndexed.row_fetch col row hcol hrow cs rs hcs hrs O x hx
    (W (e FetchIndexed.ccC)) (W (e FetchIndexed.rcC)) hcc hrc
  refine ⟨t, ht, v, ?_⟩
  have hstart0 := start_bank e W (cs.flatten ++ rs.flatten ++ O) (List.replicate x true)
    hin hfw hidx
  rw [hmy] at hstart0
  have hend : bank e W (FetchIndexed.FB [] [] [] (rs.getD x []) (cs.flatten ++ rs.flatten ++ O)
      (W (e FetchIndexed.ccC)) (W (e FetchIndexed.rcC)) (List.replicate cs.length true)
      (List.replicate x true)) = Function.update W (e lblF) (rs.getD x []) := by
    rw [FB_lbl, bank_update, hstart0]
  have h := BitMachineStackRun.run e W FetchIndexed.rowProgram
    (⟨some FetchIndexed.rowStart, FetchIndexed.rowControl,
      FetchIndexed.FB [] [] [] [] (cs.flatten ++ rs.flatten ++ O) (W (e FetchIndexed.ccC))
        (W (e FetchIndexed.rcC)) (List.replicate cs.length true) (List.replicate x true)⟩ :
      TM2.Cfg (fun _ : FetchIndexed.Stack => Bool) _ _) t
  rw [hr] at h
  simp only [stackCfg] at h
  rw [hstart0, hend] at h
  exact h

end Lift

/-! ### The retained cells of the actual post-orientation bank -/

abbrev OStack := SuccessOrient.Stack

/-- A cell of `CodeSampleAssembly`'s twelve-cell bank inside the ambient
orientation bank. -/
def sampleCell (i : CodeSampleAssembly.Stack) : OStack :=
  .inl (.inl (.inl (CodeSampleInterpreterLoader.sampleSlots
    (CodeGeneratorSampleTransfer.sample i))))

def fwCell : OStack := .inr 1
def colCodeCell : OStack := sampleCell 6
def rowCodeCell : OStack := sampleCell 1
def colsCell : OStack := .inl (.inl CodeFallbackDimensionLoader.cols)

theorem fallbackBank_sample (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (B R : Nat) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool) (i : CodeSampleAssembly.Stack) :
    SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G (sampleCell i) =
      CodeSampleAssembly.final mX mY (seedRecursiveCodes n p s q₁ q₂ w Q k).1
        (seedRecursiveCodes n p s q₁ q₂ w Q k).2 i := by
  change CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY word B R d
    (.inl (CodeSampleInterpreterLoader.sampleSlots (CodeGeneratorSampleTransfer.sample i))) = _
  unfold CodeFallbackSourceResult.finalBank
  rw [bank_outside]
  · change CodeFallbackDimensionLoader.afterY _ mX mY _ = _
    unfold CodeFallbackDimensionLoader.afterY CodeFallbackDimensionLoader.afterX
    rw [Function.update_of_ne (by simp [CodeFallbackDimensionLoader.cols]),
      Function.update_of_ne (by simp [CodeFallbackDimensionLoader.rows])]
    change CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY _ _ word B R
      (CodeSampleInterpreterLoader.sampleSlots (CodeGeneratorSampleTransfer.sample i)) = _
    unfold CodeSampleInterpreterJoin.finalBank CodeSampleInterpreterLoader.loadedBank
    rw [Function.update_of_ne (by simp [CodeSampleInterpreterLoader.target,
      CodeSampleInterpreterLoader.sampleSlots, CodeSampleInterpreterLoader.consumerSlots])]
    unfold CodeSampleInterpreterLoader.initialBank
    rw [bank_at]
    unfold CodeGeneratorSampleJoin.afterAssembly CodeGeneratorSampleTransfer.sample
    rw [bank_at]
  · rintro ⟨j, hj⟩
    rcases j with j | j <;>
      simp [CodeFallbackEntryBank.fallbackSlots, CodeFallbackEntryBank.fallbackSlot,
        CodeSampleInterpreterLoader.sampleSlots,
        CodeSampleInterpreterLoader.consumerSlots] at hj

theorem fallbackBank_colCode (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (B R : Nat) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool) :
    SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G colCodeCell =
      encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).2 := by
  rw [colCodeCell, fallbackBank_sample]
  rfl

theorem fallbackBank_rowCode (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (B R : Nat) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool) :
    SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G rowCodeCell =
      encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).1 := by
  rw [rowCodeCell, fallbackBank_sample]
  rfl

theorem fallbackBank_cols (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (B R : Nat) (d : CodeTableFallback.Config)
    (G : SamplerParameterBank.Private → List Bool) (a : CodeFullPadding.Config)
    (hd : d.stk = Sum.elim a.stk (CodeTableFallback.writerData mX mY).contents) :
    SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word B R d G colsCell =
      List.replicate mY true := by
  change CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY word B R d
    (CodeFallbackEntryBank.fallbackSlots (.inr (.inr .cols))) = _
  unfold CodeFallbackSourceResult.finalBank
  rw [bank_at, hd]
  rfl

/-! ### The joined ambient bank -/

abbrev Stack := OStack ⊕ (FetchLabel.Stack ⊕ Fin 1)

def idxCell : Stack := .inr (.inr 0)
def lblCell : Stack := .inr (.inl FetchLabel.lblC)

def embFun : FetchIndexed.Stack → Stack
  | .inl j => .inr (.inl j)
  | .inr j => (![.inl fwCell, .inl colCodeCell, .inl rowCodeCell, .inl colsCell,
      idxCell] : Fin 5 → Stack) j

theorem embFun_injective : Function.Injective embFun := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [embFun] using h
  · fin_cases b <;> simp [embFun, idxCell, fwCell, colCodeCell, rowCodeCell, colsCell] at h
  · fin_cases a <;> simp [embFun, idxCell, fwCell, colCodeCell, rowCodeCell, colsCell] at h
  · fin_cases a <;> fin_cases b <;>
      simp_all [embFun, idxCell, fwCell, colCodeCell, rowCodeCell, colsCell, sampleCell,
        CodeSampleInterpreterLoader.sampleSlots, CodeGeneratorSampleTransfer.sample,
        CodeGeneratorSampleTransfer.sampleSlots, CodeFallbackDimensionLoader.cols]

def emb : FetchIndexed.Stack ↪ Stack := ⟨embFun, embFun_injective⟩

theorem emb_lbl : emb lblF = lblCell := rfl

/-- The joined column / row fetch programs (fixed; the `FetchIndexed`
programs relabelled into the ambient bank). -/
def colProgram := fun l => stackStmt emb (FetchIndexed.colProgram l)
def rowProgram := fun l => stackStmt emb (FetchIndexed.rowProgram l)

/-- The actual bank at the end of `SuccessOrient.program` on success. -/
def post (n p s q₁ q₂ w Q k mX mY : Nat) (word : List Bool)
    (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
    (bytes : List Bool) : OStack → List Bool :=
  Function.update
    (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word
      (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) d G)
    (.inr 1) bytes

/-- The post-orientation bank beside the blank fetch scratch and a unary
index cell holding the requested coordinate. -/
def amb (S : OStack → List Bool) (i : Nat) : Stack → List Bool :=
  Sum.elim S (Sum.elim (fun _ => []) (fun _ => List.replicate i true))

theorem success_fetch (n p s q₁ q₂ w Q k mX mY : Nat)
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s)
    (tape : CappedSampler.Adaptive.Tape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY))
    (bytes : List Bool)
    (hres : GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
      (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
        (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
          (NeZero.pos n) hp hs (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
          (NeZero.pos Q))) tape = some bytes) :
    let word := (RecursiveSamplingTape.writeTape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      tape).val
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    ∃ (t₀ : Nat) (d : CodeTableFallback.Config)
      (G : SamplerParameterBank.Private → List Bool)
      (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k)
      (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k),
      t₀ ≤ SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + (3 * bytes.length + 4) ∧
      ((advance SuccessOrient.program)^[t₀])
          ⟨some SuccessOrient.startLabel, SuccessOrient.startControl,
            SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word⟩ =
        ⟨none, (SamplerFallbackJoin.startControl, none),
          post n p s q₁ q₂ w Q k mX mY word d G bytes⟩ ∧
      Produces (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) hs
          (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp)
          k mX mY) (ys, xs) ∧
      bytes = (List.ofFn (fun j => C.2.encode (ys j))).flatten ++
        (List.ofFn (fun i => C.1.encode (xs i))).flatten ∧
      (∀ y : Fin mY, ∃ t ≤ FetchIndexed.colBound c.2 (List.ofFn (fun j => C.2.encode (ys j)))
          y.val (List.ofFn (fun i => C.1.encode (xs i))).flatten, ∃ v,
        ((advance colProgram)^[t])
          (⟨some FetchIndexed.colStart, FetchIndexed.colControl,
            amb (post n p s q₁ q₂ w Q k mX mY word d G bytes) y.val⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, v, Function.update (amb (post n p s q₁ q₂ w Q k mX mY word d G bytes) y.val)
            lblCell (C.2.encode (ys y))⟩) ∧
      (∀ x : Fin mX, ∃ t ≤ FetchIndexed.rowBound c.2 c.1
          (List.ofFn (fun j => C.2.encode (ys j))) (List.ofFn (fun i => C.1.encode (xs i)))
          x.val [], ∃ v,
        ((advance rowProgram)^[t])
          (⟨some FetchIndexed.rowStart, FetchIndexed.rowControl,
            amb (post n p s q₁ q₂ w Q k mX mY word d G bytes) x.val⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, v, Function.update (amb (post n p s q₁ q₂ w Q k mX mY word d G bytes) x.val)
            lblCell (C.1.encode (xs x))⟩) := by
  intro word C c
  obtain ⟨t₀, d, G, ht₀, _hdl, _hG, hout, hresult⟩ :=
    SuccessOrient.run n p s q₁ q₂ w Q k mX mY (NeZero.pos n) hp hs (NeZero.pos q₁)
      (NeZero.pos q₂) (NeZero.pos w) (NeZero.pos Q) tape
  rw [hres] at ht₀ hout hresult
  obtain ⟨hc, _hrev⟩ := hresult
  obtain ⟨a, hd, _hobs, _htape⟩ := hout
  have hprod := OutputSkipper.run_produces _ _ (le_refl _) _ _ _ tape bytes hres
  obtain ⟨ys, xs, hsam, hbytes, hcolP, hrowP⟩ :=
    SuccessCodec.success_codec hp hs k mX mY bytes hprod
  have hshape := OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)
  let cs := List.ofFn (fun j => C.2.encode (ys j))
  let rs := List.ofFn (fun i => C.1.encode (xs i))
  have hcs : ∀ u ∈ cs, Produces (meaning c.2) u := by
    intro u hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact hcolP j
  have hrs : ∀ u ∈ rs, Produces (meaning c.1) u := by
    intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hrowP i
  have hd' : d.stk = Sum.elim a.stk (CodeTableFallback.writerData mX mY).contents := by
    rw [hd]
  let P := post n p s q₁ q₂ w Q k mX mY word d G bytes
  have hPfw : P fwCell = bytes := by simp [P, post, fwCell]
  have hPcc : P colCodeCell = encodeCode c.2 := by
    simp only [P, post]
    rw [Function.update_of_ne (by simp [colCodeCell, sampleCell]), fallbackBank_colCode]
  have hPrc : P rowCodeCell = encodeCode c.1 := by
    simp only [P, post]
    rw [Function.update_of_ne (by simp [rowCodeCell, sampleCell]), fallbackBank_rowCode]
  have hPmy : P colsCell = List.replicate mY true := by
    simp only [P, post]
    rw [Function.update_of_ne (by simp [colsCell]), fallbackBank_cols _ _ _ _ _ _ _ _ _ _ _ _ _
      d G a hd']
  refine ⟨t₀, d, G, ys, xs, ?_, hc, hsam, hbytes, ?_, ?_⟩
  · simpa [SuccessOrient.outputTime] using ht₀
  · intro y
    have hy : y.val < cs.length := by simp [cs]
    obtain ⟨t, ht, v, hr⟩ := lift_col emb (amb P y.val) c.2 hshape.2 cs hcs rs.flatten y.val hy
      (fun j => rfl) (by change P fwCell = _; rw [hPfw, hbytes])
      (by change P colCodeCell = _; exact hPcc) rfl
    have hget : cs.getD y.val [] = C.2.encode (ys y) := by
      simp [cs, List.getD_eq_getElem?_getD]
    rw [hget, emb_lbl] at hr
    exact ⟨t, ht, v, hr⟩
  · intro x
    have hx : x.val < rs.length := by simp [rs]
    obtain ⟨t, ht, v, hr⟩ := lift_row emb (amb P x.val) c.2 c.1 hshape.2 hshape.1 cs rs
      hcs hrs [] x.val hx
      (fun j => rfl) (by change P fwCell = _; rw [hPfw, hbytes, List.append_nil])
      (by change P colCodeCell = _; exact hPcc) (by change P rowCodeCell = _; exact hPrc)
      (by change P colsCell = _; rw [hPmy]; simp [cs]) rfl
    have hget : rs.getD x.val [] = C.1.encode (xs x) := by
      simp [rs, List.getD_eq_getElem?_getD]
    rw [hget, emb_lbl] at hr
    exact ⟨t, ht, v, hr⟩

end

#print axioms FB_lbl
#print axioms lift_col
#print axioms lift_row
#print axioms fallbackBank_sample
#print axioms fallbackBank_colCode
#print axioms fallbackBank_rowCode
#print axioms fallbackBank_cols
#print axioms success_fetch

end Paper2.SuccessFetchJoin
