import EthInapproximability.CurrentPaper.MatrixExactInstanceSequence
import EthInapproximability.CurrentPaper.LiteralUnaryBinaryCall
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! # Physical unary header conversion on the exact-NP writer bank

Three disjoint finite-stack counter workspaces convert unary row count, column
count and threshold into canonical binary words. Their output registers become
the three actual source registers of the instance serializer. The threshold
unary word is still an input; rows and columns are the scalar writer's output.
-/

namespace EthInapproximability.CurrentPaper.MatrixExactComputableUnaryHeaderSequence

open Turing BitMachineEncoding

abbrev counter := LiteralUnaryBinaryCall.counter
abbrev Local := BitMachineIteration.Stack counter
abbrev Base := MatrixScalarTableSequence.Stack
abbrev Stack := Base ⊕ ((Fin 3 × Local) ⊕ Unit)

def fuel : Fin 3 → Stack
  | 0 => .inl (.inl (.inr .rows))
  | 1 => .inl (.inl (.inr .cols))
  | _ => .inr (.inr ())

def result (p : Fin 3) : Stack :=
  .inr (.inl (p, .inl counter.input))

def localSlots (p : Fin 3) : Local ↪ Stack where
  toFun k := if k = .inr 0 then fuel p else .inr (.inl (p,k))
  inj' := by
    intro x y h
    by_cases hx : x = .inr (0 : Fin 2)
    · subst x
      by_cases hy : y = .inr (0 : Fin 2)
      · exact hy.symm
      · simp only [ite_true, ite_false, hy] at h
        fin_cases p <;> cases h
    · by_cases hy : y = .inr (0 : Fin 2)
      · subst y
        simp only [ite_true, ite_false, hx] at h
        fin_cases p <;> cases h
      · simp only [hx, hy, ite_false, Sum.inr.injEq] at h
        exact congrArg Prod.snd (Sum.inl.inj h)

def binary (p : Fin 3) : Stack := result p

def headerSlots : MatrixInstanceEncoding.Stack ↪ Stack where
  toFun k := match k with
    | .inl j => binary j
    | .inr j => match j.val with
      | 0 => .inr (.inr ())
      | 1 => .inl (.inl (.inr .temp))
      | _ => .inl (.inl (.inr .output))
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            simp only [binary, result, Sum.inr.injEq, Sum.inl.injEq,
              Prod.mk.injEq] at h
            exact congrArg Sum.inl h.1
        | inr y => fin_cases y <;> cases h
    | inr x =>
        cases y with
        | inl y => fin_cases x <;> cases h
        | inr y => fin_cases x <;> fin_cases y <;> first | rfl | cases h

def initial (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) : Stack → List Bool
  | .inl k => MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data k
  | .inr (.inl _) => []
  | .inr (.inr ()) => List.replicate threshold true

def afterTable (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    Stack → List Bool
  | .inl k => MatrixScalarTableSequence.finalFrame a d N₁ N₂ n data table k
  | .inr (.inl _) => []
  | .inr (.inr ()) => List.replicate threshold true

def afterRows (a d N₁ N₂ n rows threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update (afterTable a d N₁ N₂ n threshold data table)
      (fuel 0) []) (binary 0) rows.bits

def afterCols (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update (afterRows a d N₁ N₂ n rows threshold data table)
      (fuel 1) []) (binary 1) cols.bits

def afterConversion (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update (afterCols a d N₁ N₂ n rows cols threshold data table)
      (fuel 2) []) (binary 2) threshold.bits

noncomputable def finished (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool)
    (S' : BitMachineBankSerialize.Bank 3) : Stack → List Bool :=
  BitMachineStackEmbedding.bank headerSlots
    (afterConversion a d N₁ N₂ n rows cols threshold data table)
    (BitMachineBankSerialize.contents S' [] []
      (EncodedCommunication.natField rows ++
        EncodedCommunication.natField cols ++
        EncodedCommunication.natField threshold ++ table))

theorem finished_output (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool)
    (S' : BitMachineBankSerialize.Bank 3) :
    finished a d N₁ N₂ n rows cols threshold data table S'
      (.inl (.inl (.inr .output))) =
      EncodedCommunication.natField rows ++
        EncodedCommunication.natField cols ++
        EncodedCommunication.natField threshold ++ table := by
  change BitMachineStackEmbedding.bank headerSlots _ _ (headerSlots (.inr 2)) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

def conversionProgram (p : Fin 3) (l : BitMachineIteration.Label counter) :
    TM2.Stmt (fun _ : Stack => Bool) (BitMachineIteration.Label counter)
      (BitMachineIteration.Control counter) :=
  BitMachineStackEmbedding.stackStmt (localSlots p)
    (BitMachineIteration.program counter l)

theorem final_local_updates (word : List Bool) :
    (BitMachineIteration.finished counter word.length.bits).stk =
      Function.update
        (Function.update (BitMachineIteration.ready counter [] word).stk
          (.inr 0) [])
        (.inl counter.input) word.length.bits := by
  rw [LiteralUnaryBinaryCall.initial_bank, LiteralUnaryBinaryCall.final_bank]
  funext k
  by_cases ho : k = .inl counter.input
  · subst k
    simp
  · by_cases hf : k = .inr (0 : Fin 2)
    · subst k
      simp [ho]
    · simp [ho, hf]

/-- One actual unary-to-binary call at phase `p`, with every nonselected stack
framed. The input hypothesis is an explicit local-bank check, not a runtime
oracle. -/
theorem conversion_run (p : Fin 3) (S : Stack → List Bool) (word : List Bool)
    (hbank : ∀ k : Local,
      (BitMachineIteration.ready counter [] word).stk k = S (localSlots p k)) :
    ∃ t ≤ LiteralUnaryBinaryCall.coefficient * (word.length + 1) ^ 2,
      ((advance (conversionProgram p))^[t])
        (⟨some (.inr .testFuel), (counter.initial, none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (counter.initial, none),
          Function.update (Function.update S (fuel p) [])
            (binary p) word.length.bits⟩ := by
  obtain ⟨t, ht, hr⟩ := LiteralUnaryBinaryCall.raw_run word
  have he := BitMachineStackRun.run (localSlots p) S
    (BitMachineIteration.program counter)
    (BitMachineIteration.ready counter [] word) t
  change ((advance (conversionProgram p))^[t])
      (BitMachineStackEmbedding.stackCfg (localSlots p) S
        (BitMachineIteration.ready counter [] word)) =
    BitMachineStackEmbedding.stackCfg (localSlots p) S
      (BitMachineIteration.run counter t
        (BitMachineIteration.ready counter [] word)) at he
  rw [hr] at he
  have hs : BitMachineStackEmbedding.bank (localSlots p) S
      (BitMachineIteration.ready counter [] word).stk = S :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ hbank
  have hout : BitMachineStackEmbedding.bank (localSlots p) S
      (BitMachineIteration.finished counter word.length.bits).stk =
      Function.update (Function.update S (fuel p) [])
        (binary p) word.length.bits := by
    rw [final_local_updates, BitMachineStackEmbedding.bank_update,
      BitMachineStackEmbedding.bank_update, hs]
    have hf : localSlots p (.inr (0 : Fin 2)) = fuel p := by
      simp [localSlots]
    have ho : localSlots p (.inl counter.input) = binary p := by
      simp [localSlots, binary, result]
    rw [hf, ho]
  refine ⟨t, ht, ?_⟩
  simp only [BitMachineStackEmbedding.stackCfg] at he
  rw [hs, hout] at he
  exact he

theorem phase_disjoint {p q : Fin 3} (hpq : p ≠ q) (k : Local) :
    localSlots p k ≠ fuel q ∧ localSlots p k ≠ binary q := by
  constructor <;> intro h
  · fin_cases p <;> fin_cases q <;> try exact (hpq rfl).elim
    · cases k with
      | inl j => cases h
      | inr j => fin_cases j <;> simp [localSlots, fuel] at h
    all_goals
      cases k with
      | inl j => cases h
      | inr j => fin_cases j <;> simp [localSlots, fuel] at h
  · cases k with
    | inl j =>
        simp [localSlots, binary, result, hpq] at h
    | inr j =>
        fin_cases j
        · fin_cases p <;> cases h
        · simp [localSlots, binary, result, hpq] at h

theorem conversion_bank (p : Fin 3) (S : Stack → List Bool)
    (word : List Bool) (hf : S (fuel p) = word)
    (he : ∀ k : Local, k ≠ .inr 0 → S (localSlots p k) = []) :
    ∀ k : Local,
      (BitMachineIteration.ready counter [] word).stk k = S (localSlots p k) := by
  rw [LiteralUnaryBinaryCall.initial_bank]
  intro k
  by_cases hk : k = .inr (0 : Fin 2)
  · subst k
    simpa [localSlots] using hf.symm
  · simp [hk, he k hk]

theorem phase_preserved {p q : Fin 3} (hpq : p ≠ q)
    (S : Stack → List Bool) (word : List Bool) (k : Local) :
    (Function.update (Function.update S (fuel p) [])
      (binary p) word) (localSlots q k) = S (localSlots q k) := by
  have hd := phase_disjoint (p := q) (q := p) (Ne.symm hpq) k
  rw [Function.update_of_ne hd.2, Function.update_of_ne hd.1]

theorem afterTable_fuel (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool)
    (p : Fin 3) :
    afterTable a d N₁ N₂ n threshold data table (fuel p) =
      List.replicate
        (if p = 0 then 4*N₂+n else if p = 1 then 8*(d*N₁)^4 else threshold) true := by
  fin_cases p <;> rfl

theorem afterTable_local_empty (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool)
    (p : Fin 3) (k : Local) (hk : k ≠ .inr 0) :
    afterTable a d N₁ N₂ n threshold data table (localSlots p k) = [] := by
  cases k with
  | inl k => simp [localSlots, afterTable]
  | inr k =>
      fin_cases k
      · exact (hk rfl).elim
      · simp [localSlots, afterTable]

theorem rows_bank (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∀ k : Local,
      (BitMachineIteration.ready counter []
        (List.replicate (4*N₂+n) true)).stk k =
        afterTable a d N₁ N₂ n threshold data table (localSlots 0 k) := by
  apply conversion_bank
  · simpa using afterTable_fuel a d N₁ N₂ n threshold data table 0
  · exact afterTable_local_empty a d N₁ N₂ n threshold data table 0

theorem cols_bank (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∀ k : Local,
      (BitMachineIteration.ready counter []
        (List.replicate (8*(d*N₁)^4) true)).stk k =
        afterRows a d N₁ N₂ n (4*N₂+n) threshold data table (localSlots 1 k) := by
  have hpre := conversion_bank (1 : Fin 3)
    (afterTable a d N₁ N₂ n threshold data table)
    (List.replicate (8*(d*N₁)^4) true)
    (by simpa using afterTable_fuel a d N₁ N₂ n threshold data table 1)
    (afterTable_local_empty a d N₁ N₂ n threshold data table 1)
  intro k
  rw [hpre k]
  exact (phase_preserved (p := 0) (q := 1) (by decide)
    (afterTable a d N₁ N₂ n threshold data table)
    (4*N₂+n).bits k).symm

theorem threshold_bank (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∀ k : Local,
      (BitMachineIteration.ready counter []
        (List.replicate threshold true)).stk k =
        afterCols a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4) threshold
          data table (localSlots 2 k) := by
  have hpre := conversion_bank (2 : Fin 3)
    (afterTable a d N₁ N₂ n threshold data table)
    (List.replicate threshold true)
    (by simpa using afterTable_fuel a d N₁ N₂ n threshold data table 2)
    (afterTable_local_empty a d N₁ N₂ n threshold data table 2)
  intro k
  rw [hpre k]
  rw [afterCols, phase_preserved (p := 1) (q := 2) (by decide),
    afterRows, phase_preserved (p := 0) (q := 2) (by decide)]

abbrev ConversionLabel := BitMachineIteration.Label counter
abbrev ConversionControl := BitMachineIteration.Control counter
def idle : ConversionControl := (counter.initial, none)
def conversionStart : ConversionLabel := .inr .testFuel

def program01 := BitMachineRawSequence.program
  (conversionProgram 0) (conversionProgram 1) conversionStart idle idle

def program012 := BitMachineRawSequence.program
  program01 (conversionProgram 2) conversionStart (idle, idle) idle

theorem conversions_run (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∃ t ≤ LiteralUnaryBinaryCall.coefficient * (4*N₂+n+1)^2 +
        LiteralUnaryBinaryCall.coefficient * (8*(d*N₁)^4+1)^2 +
        LiteralUnaryBinaryCall.coefficient * (threshold+1)^2 + 2,
      ((advance program012)^[t])
        (⟨some (.inl (.inl conversionStart)),
          ((idle, idle), idle),
          afterTable a d N₁ N₂ n threshold data table⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((idle, idle), idle),
          afterConversion a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
            threshold data table⟩ := by
  obtain ⟨tr, htr, hr⟩ := conversion_run 0
    (afterTable a d N₁ N₂ n threshold data table)
    (List.replicate (4*N₂+n) true) (rows_bank a d N₁ N₂ n threshold data table)
  obtain ⟨tc, htc, hc⟩ := conversion_run 1
    (afterRows a d N₁ N₂ n (4*N₂+n) threshold data table)
    (List.replicate (8*(d*N₁)^4) true)
    (cols_bank a d N₁ N₂ n threshold data table)
  obtain ⟨tt, htt, ht⟩ := conversion_run 2
    (afterCols a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4) threshold data table)
    (List.replicate threshold true)
    (threshold_bank a d N₁ N₂ n threshold data table)
  have hr' : ((advance (conversionProgram 0))^[tr])
      (⟨some conversionStart, idle,
        afterTable a d N₁ N₂ n threshold data table⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, idle, afterRows a d N₁ N₂ n (4*N₂+n) threshold data table⟩ := by
    simpa only [conversionStart, idle, afterRows, List.length_replicate] using hr
  have hc' : ((advance (conversionProgram 1))^[tc])
      (⟨some conversionStart, idle,
        afterRows a d N₁ N₂ n (4*N₂+n) threshold data table⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, idle,
        afterCols a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
          threshold data table⟩ := by
    simpa only [conversionStart, idle, afterCols, List.length_replicate] using hc
  have ht' : ((advance (conversionProgram 2))^[tt])
      (⟨some conversionStart, idle,
        afterCols a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
          threshold data table⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, idle,
        afterConversion a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
          threshold data table⟩ := by
    simpa only [conversionStart, idle, afterConversion, List.length_replicate] using ht
  have hrc : ∃ t ≤ tr + tc + 1,
      ((advance program01)^[t])
        (⟨some (.inl conversionStart), (idle, idle),
          afterTable a d N₁ N₂ n threshold data table⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (idle, idle),
          afterCols a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
            threshold data table⟩ := by
    exact BitMachineRawSequence.runs
      (conversionProgram 0) (conversionProgram 1) conversionStart conversionStart
      idle idle idle idle
      (afterTable a d N₁ N₂ n threshold data table)
      (afterRows a d N₁ N₂ n (4*N₂+n) threshold data table)
      (afterCols a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4) threshold data table)
      tr tc hr' hc'
  obtain ⟨trc, htrc, hrc⟩ := hrc
  obtain ⟨t, htotal, hrun⟩ := BitMachineRawSequence.runs
    program01 (conversionProgram 2) (.inl conversionStart) conversionStart
    (idle, idle) (idle, idle) idle idle
    (afterTable a d N₁ N₂ n threshold data table)
    (afterCols a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4) threshold data table)
    (afterConversion a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
      threshold data table)
    trc tt hrc ht'
  simp only [List.length_replicate] at htr htc htt
  exact ⟨t, by omega, hrun⟩

abbrev BaseLabel := MatrixExactInstanceSequence.BaseLabel
abbrev BaseControl := MatrixExactInstanceSequence.BaseControl

def baseSlots : Base ↪ Stack :=
  ⟨Sum.inl, by intro x y h; exact Sum.inl.inj h⟩

def baseProgram (l : BaseLabel) :
    TM2.Stmt (fun _ : Stack => Bool) BaseLabel BaseControl :=
  BitMachineStackEmbedding.stackStmt baseSlots
    (MatrixScalarTableSequence.program l)

theorem base_run {a d N₁ N₂ n threshold : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    ∃ t ≤ 200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1) +
        MatrixTableRuntimeBounds.bound a d N₁ N₂ n + 1,
      ∃ state,
        ((advance baseProgram)^[t])
          (⟨some (.inl (.inl (.inr false))),
            (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
            initial a d N₁ N₂ n threshold
              (MatrixMaterialization.storeBits C₁ C₂ v)⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, (MatrixScalarParameters.idle, state),
            afterTable a d N₁ N₂ n threshold
              (MatrixMaterialization.storeBits C₁ C₂ v)
              (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
                (n := n) (MatrixMaterialization.storeBits C₁ C₂ v) ha)⟩ := by
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let table := MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
    (n := n) data ha
  obtain ⟨t, ht, state, hr⟩ :=
    MatrixScalarTableSequence.scalar_write_run ha C₁ C₂ v cap
  have he := BitMachineStackRun.run baseSlots
    (initial a d N₁ N₂ n threshold data)
    MatrixScalarTableSequence.program
    (⟨some (.inl (.inl (.inr false))),
      (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
      MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data⟩ :
      TM2.Cfg (fun _ : Base => Bool) _ _) t
  change ((advance baseProgram)^[t]) _ =
    BitMachineStackEmbedding.stackCfg baseSlots
      (initial a d N₁ N₂ n threshold data)
      (((advance MatrixScalarTableSequence.program)^[t])
        (⟨some (.inl (.inl (.inr false))),
          (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
          MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data⟩ :
          TM2.Cfg (fun _ : Base => Bool) _ _)) at he
  rw [hr] at he
  have hstart : BitMachineStackEmbedding.bank baseSlots
      (initial a d N₁ N₂ n threshold data)
      (MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data) =
      initial a d N₁ N₂ n threshold data := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    rfl
  have hfinal : BitMachineStackEmbedding.bank baseSlots
      (initial a d N₁ N₂ n threshold data)
      (MatrixScalarTableSequence.finalFrame a d N₁ N₂ n data table) =
      afterTable a d N₁ N₂ n threshold data table := by
    funext k
    cases k with
    | inl j =>
        change BitMachineStackEmbedding.bank baseSlots _ _ (baseSlots j) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
    | inr j =>
        rw [BitMachineStackEmbedding.bank_outside]
        · cases j with
          | inl j => rfl
          | inr j => cases j; rfl
        · intro ⟨j, hj⟩
          cases hj
  refine ⟨t, ht, state, ?_⟩
  simp only [BitMachineStackEmbedding.stackCfg, hstart] at he
  rw [hfinal] at he
  exact he

abbrev HeaderLabel := MatrixInstanceEncoding.Label
abbrev HeaderControl := Option Bool

def headerProgram (l : HeaderLabel) :
    TM2.Stmt (fun _ : Stack => Bool) HeaderLabel HeaderControl :=
  BitMachineStackEmbedding.stackStmt headerSlots
    (MatrixInstanceEncoding.program l)

theorem header_input_bank (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∀ k : MatrixInstanceEncoding.Stack,
      (MatrixInstanceEncoding.initial rows cols threshold [] table []).stk k =
        afterConversion a d N₁ N₂ n rows cols threshold data table
          (headerSlots k) := by
  intro k
  cases k with
  | inl j =>
      fin_cases j <;>
        simp [MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, MatrixInstanceEncoding.binaryBank,
          headerSlots, afterConversion, afterCols, afterRows,
          binary, result, fuel]
  | inr j =>
      fin_cases j <;>
        simp [MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, headerSlots,
          afterConversion, afterCols, afterRows, afterTable,
          MatrixScalarTableSequence.finalFrame, MatrixTableWriter.Data.contents,
          MatrixTableWriter.Data.foreign, MatrixTableWriter.ready,
          fuel, binary, result]

theorem header_run (a d N₁ N₂ n rows cols threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∃ t ≤ 2 * (EncodedCommunication.natField rows ++
        EncodedCommunication.natField cols ++
        EncodedCommunication.natField threshold).length + 2,
      ∃ S' : BitMachineBankSerialize.Bank 3,
        ((advance headerProgram)^[t])
          (⟨some (.emit 0), none,
            afterConversion a d N₁ N₂ n rows cols threshold data table⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, none,
            finished a d N₁ N₂ n rows cols threshold data table S'⟩ := by
  obtain ⟨t, S', ht, hr⟩ :=
    MatrixInstanceEncoding.encode_run rows cols threshold [] table []
  have he := BitMachineStackRun.run headerSlots
    (afterConversion a d N₁ N₂ n rows cols threshold data table)
    MatrixInstanceEncoding.program
    (MatrixInstanceEncoding.initial rows cols threshold [] table []) t
  change ((advance headerProgram)^[t]) _ =
    BitMachineStackEmbedding.stackCfg headerSlots
      (afterConversion a d N₁ N₂ n rows cols threshold data table)
      (MatrixInstanceEncoding.run t
        (MatrixInstanceEncoding.initial rows cols threshold [] table [])) at he
  rw [hr] at he
  have hstart : BitMachineStackEmbedding.bank headerSlots
      (afterConversion a d N₁ N₂ n rows cols threshold data table)
      (MatrixInstanceEncoding.initial rows cols threshold [] table []).stk =
      afterConversion a d N₁ N₂ n rows cols threshold data table :=
    BitMachineStackEmbedding.bank_eq_self _ _ _
      (header_input_bank a d N₁ N₂ n rows cols threshold data table)
  refine ⟨t, ht, S', ?_⟩
  simp only [BitMachineStackEmbedding.stackCfg,
    MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
    List.append_nil, finished] at he ⊢
  simp only [MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
    List.append_nil] at hstart
  rw [hstart] at he
  exact he

def baseCost (a d N₁ N₂ n : ℕ) : ℕ :=
  200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1) +
    MatrixTableRuntimeBounds.bound a d N₁ N₂ n + 1

def conversionCost (d N₁ N₂ n threshold : ℕ) : ℕ :=
  LiteralUnaryBinaryCall.coefficient * (4*N₂+n+1)^2 +
    LiteralUnaryBinaryCall.coefficient * (8*(d*N₁)^4+1)^2 +
    LiteralUnaryBinaryCall.coefficient * (threshold+1)^2 + 2

def headerCost (rows cols threshold : ℕ) : ℕ :=
  2 * (EncodedCommunication.natField rows ++
    EncodedCommunication.natField cols ++
    EncodedCommunication.natField threshold).length + 2

abbrev Conversion012Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label ConversionLabel ConversionLabel) ConversionLabel
abbrev Conversion012Control := ((ConversionControl × ConversionControl) × ConversionControl)
abbrev TailLabel := BitMachineRawSequence.Label Conversion012Label HeaderLabel
abbrev TailControl := Conversion012Control × HeaderControl

def conversion012Start : Conversion012Label := .inl (.inl conversionStart)
def conversion012Idle : Conversion012Control := ((idle, idle), idle)
def tailStart : TailLabel := .inl conversion012Start
def tailIdle : TailControl := (conversion012Idle, none)

def tailProgram := BitMachineRawSequence.program
  program012 headerProgram (.emit 0) conversion012Idle none

theorem tail_run (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (table : List Bool) :
    ∃ t ≤ conversionCost d N₁ N₂ n threshold +
        headerCost (4*N₂+n) (8*(d*N₁)^4) threshold + 1,
      ∃ S' : BitMachineBankSerialize.Bank 3,
        ((advance tailProgram)^[t])
          (⟨some tailStart, tailIdle,
            afterTable a d N₁ N₂ n threshold data table⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, tailIdle,
            finished a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
              threshold data table S'⟩ := by
  obtain ⟨tc, htc, hc⟩ := conversions_run a d N₁ N₂ n threshold data table
  obtain ⟨th, hth, S', hh⟩ := header_run a d N₁ N₂ n
    (4*N₂+n) (8*(d*N₁)^4) threshold data table
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    program012 headerProgram conversion012Start (.emit 0)
    conversion012Idle conversion012Idle none none
    (afterTable a d N₁ N₂ n threshold data table)
    (afterConversion a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
      threshold data table)
    (finished a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
      threshold data table S') tc th hc hh
  refine ⟨t, ?_, S', hr⟩
  simp only [conversionCost, headerCost] at htc hth ⊢
  omega

abbrev Label := BitMachineRawSequence.Label BaseLabel TailLabel
abbrev Control := BaseControl × TailControl

def program := BitMachineRawSequence.program
  baseProgram tailProgram tailStart
  (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial) tailIdle

/-- One fixed finite Boolean-stack controller performs scalar initialization,
all matrix entries, three unary-to-binary conversions, and the complete
instance serializer. Its only remaining initial payloads are the three
literal arrays, five unary scalar inputs and unary threshold. -/
theorem scalar_write_encode_unary_run {a d N₁ N₂ n threshold : ℕ}
    (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    ∃ t ≤ baseCost a d N₁ N₂ n +
        conversionCost d N₁ N₂ n threshold +
        headerCost (4*N₂+n) (8*(d*N₁)^4) threshold + 2,
      ∃ S' : BitMachineBankSerialize.Bank 3,
        ((advance program)^[t])
          (⟨some (.inl (.inl (.inl (.inr false)))),
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), tailIdle),
            initial a d N₁ N₂ n threshold
              (MatrixMaterialization.storeBits C₁ C₂ v)⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), tailIdle),
            finished a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
              threshold (MatrixMaterialization.storeBits C₁ C₂ v)
              (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
                (n := n) (MatrixMaterialization.storeBits C₁ C₂ v) ha) S'⟩ := by
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let table := MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂)
    (n := n) data ha
  obtain ⟨tb, htb, state, hb⟩ := base_run (threshold := threshold) ha C₁ C₂ v cap
  obtain ⟨tt, htt, S', ht⟩ := tail_run a d N₁ N₂ n threshold data table
  obtain ⟨t, htotal, hrun⟩ := BitMachineRawSequence.runs
    baseProgram tailProgram (.inl (.inl (.inr false))) tailStart
    (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial)
    (MatrixScalarParameters.idle, state) tailIdle tailIdle
    (initial a d N₁ N₂ n threshold data)
    (afterTable a d N₁ N₂ n threshold data table)
    (finished a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
      threshold data table S') tb tt hb ht
  exact ⟨t, by simp only [baseCost] at htb ⊢; omega, S', hrun⟩

/-- The output stack of the single controller is exactly the executable
encoded graph instance. This is a prepared-payload endpoint: the source and
both sampled-family arrays plus unary scalar words are still physical input
cells, with their separate producers to be composed upstream. -/
theorem encoded_graph_output (s : ℕ) (hs : 2 ^ 21 ≤ s)
    (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤
      baseCost (ExactParameters.firstExponent s) (ExactParameters.dimension s)
        (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
        (5*g.vertices) +
      conversionCost (ExactParameters.dimension s)
        (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
        (5*g.vertices)
        (ExactParameters.firstExponent s + 1 + ExactParameters.dimensionLog s + 2) +
      2 * (EncodedCommunication.encodeInstance
        (ExecutableExactReduction.instanceAt s hs
          (EncodedGraph.endpoints g hg))).length + 4,
      ∃ S : Stack → List Bool,
        ((advance program)^[t])
          (⟨some (.inl (.inl (.inl (.inr false)))),
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), tailIdle),
            initial (ExactParameters.firstExponent s) (ExactParameters.dimension s)
              (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
              (5*g.vertices)
              (ExactParameters.firstExponent s + 1 + ExactParameters.dimensionLog s + 2)
              (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,
            ((MatrixScalarParameters.idle,
              MatrixScalarTableSequence.writerInitial), tailIdle), S⟩ ∧
        S (.inl (.inl (.inr .output))) =
          EncodedCommunication.encodeInstance
            (ExecutableExactReduction.instanceAt s hs
              (EncodedGraph.endpoints g hg)) := by
  let e := EncodedGraph.endpoints g hg
  let a := ExactParameters.firstExponent s
  let d := ExactParameters.dimension s
  let N₁ := ExactParameters.firstListSize s
  let N₂ := ExactParameters.secondListSize s
  let n := 5*g.vertices
  let threshold := a + 1 + ExactParameters.dimensionLog s + 2
  have h := scalar_write_encode_unary_run (threshold := threshold)
    (ExecutableExactReduction.alphabet_valid s hs)
    (ExecutableExactReduction.firstFamily s)
    (ExecutableExactReduction.secondFamily s)
    (ExactConstruction.sourceVectors d e)
    (ExactConstruction.sourceVectors_cap d e)
  obtain ⟨t, ht, S', hr⟩ := h
  let table := ExecutableExactReduction.literalTable s hs e
  let S := finished a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
    threshold (ExecutableExactReduction.payload s e) table S'
  have henc :
      EncodedCommunication.natField (4*N₂+n) ++
        EncodedCommunication.natField (8*(d*N₁)^4) ++
        EncodedCommunication.natField threshold ++ table =
      EncodedCommunication.encodeInstance
        (ExecutableExactReduction.instanceAt s hs e) := by
    simp only [EncodedCommunication.encodeInstance,
      ExecutableExactReduction.instanceAt, ExactEncodedReduction.rowCount,
      ExactEncodedReduction.columnCount, table, a, d, N₁, N₂, n, threshold]
  have hlen : (EncodedCommunication.natField (4*N₂+n) ++
        EncodedCommunication.natField (8*(d*N₁)^4) ++
        EncodedCommunication.natField threshold).length ≤
      (EncodedCommunication.encodeInstance
        (ExecutableExactReduction.instanceAt s hs e)).length := by
    rw [← henc]
    simp only [List.length_append]
    omega
  refine ⟨t, ?_, S, ?_, ?_⟩
  · simp only [headerCost] at ht
    simp only [a, d, N₁, N₂, n, threshold, e] at ht hlen ⊢
    omega
  · simpa only [ExecutableExactReduction.literalTable,
      ExecutableExactReduction.payload] using hr
  · rw [show S (.inl (.inl (.inr .output))) =
        EncodedCommunication.natField (4*N₂+n) ++
          EncodedCommunication.natField (8*(d*N₁)^4) ++
          EncodedCommunication.natField threshold ++ table from
      finished_output a d N₁ N₂ n (4*N₂+n) (8*(d*N₁)^4)
        threshold (ExecutableExactReduction.payload s e) table S']
    exact henc

end EthInapproximability.CurrentPaper.MatrixExactComputableUnaryHeaderSequence
