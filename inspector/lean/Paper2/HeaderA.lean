import EthInapproximability.CurrentPaper.MatrixExactUnaryHeaderSequence

/-! Unit 3, segment (5), reviewer G2: the encoded output header
`natField rows ++ natField cols ++ natField threshold` placed BEFORE the table
word, i.e. the literal `EncodedCommunication.encodeInstance` layout that the
consumer `EncodedSelectedOutput.outputBits` (= `encodeInstance (selectedInstance …)`)
prescribes.

ONE fixed program `prog` on its own bank `HB = (Fin 3 × Local) ⊕ Fin 6`:
three unary-to-binary conversions (the admitted `SourceUnaryBinaryCall`
counter program `BitMachineIteration.program counter`, placed by `localSlots p`
exactly as in the admitted `MatrixExactUnaryHeaderSequence`, with the admitted
`final_local_updates`), then the admitted instance serializer
`MatrixInstanceEncoding.program` (placed by `headerSlots`), which prepends the
three self-delimiting fields to the table word on the output cell. The stage
is branch-independent: it reads only unary `rows`, `cols`, `threshold` and the
table word, so it serves the success and the fallback branch alike once their
banks supply those four cells (their producers are NOT bound here). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.HeaderA

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication

abbrev counter := MatrixExactUnaryHeaderSequence.counter
abbrev Local := MatrixExactUnaryHeaderSequence.Local
abbrev HB := (Fin 3 × Local) ⊕ Fin 6

def fuel (p : Fin 3) : HB := .inr ⟨p.val, by omega⟩
def binary (p : Fin 3) : HB := .inl (p, .inl counter.input)
def srcH : HB := .inr 3
def tmpH : HB := .inr 4
def outH : HB := .inr 5

def localSlots (p : Fin 3) : Local ↪ HB where
  toFun k := if k = .inr 0 then fuel p else .inl (p, k)
  inj' := by
    intro x y h
    by_cases hx : x = .inr (0 : Fin 2) <;> by_cases hy : y = .inr (0 : Fin 2)
    · rw [hx, hy]
    · simp [hx, hy, fuel] at h
    · simp [hx, hy, fuel] at h
    · simpa [hx, hy] using h

def headerSlotsF : MatrixInstanceEncoding.Stack → HB
  | .inl j => binary j
  | .inr j => (![srcH, tmpH, outH] : Fin 3 → HB) j

theorem headerSlotsF_injective : Function.Injective headerSlotsF := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [headerSlotsF, binary] using h
  · fin_cases b <;> simp [headerSlotsF, binary, srcH, tmpH, outH] at h
  · fin_cases a <;> simp [headerSlotsF, binary, srcH, tmpH, outH] at h
  · fin_cases a <;> fin_cases b <;> simp_all [headerSlotsF, srcH, tmpH, outH]

def headerSlots : MatrixInstanceEncoding.Stack ↪ HB := ⟨headerSlotsF, headerSlotsF_injective⟩

def convP (p : Fin 3) (l : BitMachineIteration.Label counter) :
    TM2.Stmt (fun _ : HB => Bool) (BitMachineIteration.Label counter)
      (BitMachineIteration.Control counter) :=
  stackStmt (localSlots p) (BitMachineIteration.program counter l)

def hdrP (l : MatrixInstanceEncoding.Label) :
    TM2.Stmt (fun _ : HB => Bool) MatrixInstanceEncoding.Label (Option Bool) :=
  stackStmt headerSlots (MatrixInstanceEncoding.program l)

abbrev idle := MatrixExactUnaryHeaderSequence.idle
abbrev cStart := MatrixExactUnaryHeaderSequence.conversionStart

def p01 := BitMachineRawSequence.program (convP 0) (convP 1) cStart idle idle
def p012 := BitMachineRawSequence.program p01 (convP 2) cStart (idle, idle) idle
/-- The header stage: ONE fixed program. -/
def prog := BitMachineRawSequence.program p012 hdrP (.emit 0) ((idle, idle), idle)
  (none : Option Bool)
def progStart : BitMachineRawSequence.Label (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label MatrixExactUnaryHeaderSequence.ConversionLabel
      MatrixExactUnaryHeaderSequence.ConversionLabel)
    MatrixExactUnaryHeaderSequence.ConversionLabel) MatrixInstanceEncoding.Label :=
  .inl (.inl (.inl cStart))
def progCtl := (((idle, idle), idle), (none : Option Bool))

/-- Entry bank: unary `rows`, `cols`, `threshold` in the three fuel cells, the
table word (followed by an arbitrary suffix) in the output cell, all else blank. -/
def Hin (rows cols thr : ℕ) (table suffix : List Bool) : HB → List Bool
  | .inl _ => []
  | .inr j => (![List.replicate rows true, List.replicate cols true, List.replicate thr true,
      [], [], table ++ suffix] : Fin 6 → List Bool) j

theorem conv_run (p : Fin 3) (S : HB → List Bool) (word : List Bool)
    (hf : S (fuel p) = word) (he : ∀ k : Local, k ≠ .inr 0 → S (localSlots p k) = []) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (word.length + 1) ^ 2,
      ((advance (convP p))^[t])
        (⟨some cStart, idle, S⟩ : TM2.Cfg (fun _ : HB => Bool) _ _) =
        ⟨none, idle, Function.update (Function.update S (fuel p) []) (binary p)
          word.length.bits⟩ := by
  have hbank : ∀ k : Local,
      (BitMachineIteration.ready counter [] word).stk k = S (localSlots p k) := by
    rw [SourceUnaryBinaryCall.initial_bank]
    intro k
    by_cases hk : k = .inr (0 : Fin 2)
    · subst k
      simpa [localSlots] using hf.symm
    · simp [hk, he k hk]
  obtain ⟨t, ht, hr⟩ := SourceUnaryBinaryCall.raw_run word
  have hh := BitMachineStackRun.run (localSlots p) S
    (BitMachineIteration.program counter)
    (BitMachineIteration.ready counter [] word) t
  change ((advance (convP p))^[t])
      (stackCfg (localSlots p) S (BitMachineIteration.ready counter [] word)) =
    stackCfg (localSlots p) S
      (BitMachineIteration.run counter t (BitMachineIteration.ready counter [] word)) at hh
  rw [hr] at hh
  have hs : bank (localSlots p) S (BitMachineIteration.ready counter [] word).stk = S :=
    bank_eq_self _ _ _ hbank
  have hout : bank (localSlots p) S (BitMachineIteration.finished counter word.length.bits).stk =
      Function.update (Function.update S (fuel p) []) (binary p) word.length.bits := by
    rw [MatrixExactUnaryHeaderSequence.final_local_updates, bank_update, bank_update, hs]
    have hf' : localSlots p (.inr (0 : Fin 2)) = fuel p := by simp [localSlots]
    have ho : localSlots p (.inl counter.input) = binary p := by simp [localSlots, binary]
    rw [hf', ho]
  refine ⟨t, ht, ?_⟩
  simp only [stackCfg] at hh
  rw [hs, hout] at hh
  exact hh

/-- Segment (5): the header stage as ONE run. -/
theorem header_run (rows cols thr : ℕ) (table suffix : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (rows + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (cols + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 +
        (2 * (natField rows ++ natField cols ++ natField thr).length + 2) + 3,
      ∃ v F,
        ((advance prog)^[t]) (⟨some progStart, progCtl, Hin rows cols thr table suffix⟩ :
          TM2.Cfg (fun _ : HB => Bool) _ _) = ⟨none, v, F⟩ ∧
        F outH = natField rows ++ natField cols ++ natField thr ++ table ++ suffix := by
  let S0 := Hin rows cols thr table suffix
  obtain ⟨t0, ht0, r0⟩ := conv_run 0 S0 (List.replicate rows true) rfl
    (by intro k hk; simp [S0, localSlots, hk, Hin])
  let S1 := Function.update (Function.update S0 (fuel 0) []) (binary 0)
    (List.replicate rows true).length.bits
  obtain ⟨t1, ht1, r1⟩ := conv_run 1 S1 (List.replicate cols true)
    (by simp [S1, S0, fuel, binary, Hin])
    (by intro k hk; simp [S1, S0, localSlots, hk, fuel, binary, Hin])
  let S2 := Function.update (Function.update S1 (fuel 1) []) (binary 1)
    (List.replicate cols true).length.bits
  obtain ⟨t2, ht2, r2⟩ := conv_run 2 S2 (List.replicate thr true)
    (by simp [S2, S1, S0, fuel, binary, Hin])
    (by intro k hk; simp [S2, S1, S0, localSlots, hk, fuel, binary, Hin])
  let S3 := Function.update (Function.update S2 (fuel 2) []) (binary 2)
    (List.replicate thr true).length.bits
  -- the serializer
  obtain ⟨t4, S', ht4, hr4⟩ := MatrixInstanceEncoding.encode_run rows cols thr [] table suffix
  have hin : ∀ k : MatrixInstanceEncoding.Stack,
      (MatrixInstanceEncoding.initial rows cols thr [] table suffix).stk k = S3 (headerSlots k) := by
    intro k
    rcases k with j | j
    · fin_cases j <;>
        simp [MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, MatrixInstanceEncoding.binaryBank, headerSlots,
          headerSlotsF, S3, S2, S1, S0, fuel, binary, Hin]
    · fin_cases j <;>
        simp [MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, headerSlots, headerSlotsF, srcH, tmpH, outH,
          S3, S2, S1, S0, fuel, binary, Hin]
  have hh := BitMachineStackRun.run headerSlots S3 MatrixInstanceEncoding.program
    (MatrixInstanceEncoding.initial rows cols thr [] table suffix) t4
  change ((advance hdrP)^[t4])
      (stackCfg headerSlots S3 (MatrixInstanceEncoding.initial rows cols thr [] table suffix)) =
    stackCfg headerSlots S3
      (MatrixInstanceEncoding.run t4 (MatrixInstanceEncoding.initial rows cols thr [] table suffix))
    at hh
  rw [hr4] at hh
  have hs : bank headerSlots S3 (MatrixInstanceEncoding.initial rows cols thr [] table suffix).stk =
      S3 := bank_eq_self _ _ _ hin
  simp only [stackCfg] at hh
  rw [hs] at hh
  change ((advance hdrP)^[t4]) (⟨some (.emit 0), none, S3⟩ : TM2.Cfg (fun _ : HB => Bool) _ _) =
    ⟨none, none, bank headerSlots S3 (BitMachineBankSerialize.contents S' [] []
      (natField rows ++ natField cols ++ natField thr ++ table ++ suffix))⟩ at hh
  -- sequencing
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (convP 0) (convP 1) cStart cStart
    idle idle idle idle _ _ _ _ _ r0 r1
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs p01 (convP 2)
    (BitMachineRawSequence.leftLabel cStart) cStart (idle, idle) (idle, idle) idle idle
    _ _ _ _ _ q1 r2
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs p012 hdrP
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel cStart)) (.emit 0)
    ((idle, idle), idle) ((idle, idle), idle) (none : Option Bool) none _ _ _ _ _ q2 hh
  refine ⟨u3, ?_, _, _, q3, ?_⟩
  · simp only [List.length_replicate] at ht0 ht1 ht2
    omega
  · show bank headerSlots S3 _ (headerSlots (.inr 2)) = _
    rw [bank_at]
    rfl

/-- The same output as the literal consumer word `encodeInstance i ++ suffix`. -/
theorem header_instance (i : Instance) (suffix : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (i.rows + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (i.cols + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (i.threshold + 1) ^ 2 +
        (2 * (natField i.rows ++ natField i.cols ++ natField i.threshold).length + 2) + 3,
      ∃ v F,
        ((advance prog)^[t]) (⟨some progStart, progCtl,
          Hin i.rows i.cols i.threshold i.table suffix⟩ :
          TM2.Cfg (fun _ : HB => Bool) _ _) = ⟨none, v, F⟩ ∧
        F outH = encodeInstance i ++ suffix := by
  obtain ⟨t, ht, v, F, h1, h2⟩ := header_run i.rows i.cols i.threshold i.table suffix
  exact ⟨t, ht, v, F, h1, by rw [h2]; simp [encodeInstance, List.append_assoc]⟩

end

#print axioms headerSlotsF_injective
#print axioms conv_run
#print axioms header_run
#print axioms header_instance

end Paper2.HeaderA
