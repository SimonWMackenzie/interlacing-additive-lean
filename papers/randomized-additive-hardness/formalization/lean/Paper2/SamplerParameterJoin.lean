import Paper2.SamplerParameterBank
import Paper2.AffineMultiplyAdd
import Paper2.NPLoops
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Joined physical public-parameter producer and B/R adapter.

One fixed controller on `ConsumerStack ⊕ Private` starts from the admitted
consumer bank with *no* preloaded cap words,
`CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY tape 0 0`, beside a
blank private region. It

1. copies the raw unary `q₁,q₂,s,w,Q,n,p` from the consumer's compiler cells
   into the private alphabet/bit-width bank (seven source-preserving copies);
2. runs `SamplerBitWidthMachine.program` there (M = alphabetCap, B = clog₂ M);
3. copies the raw unary `s,q₁,q₂,w,Q,p,k,mX,mY` into the private draw bank
   (nine source-preserving copies);
4. runs `SamplerNRProducer.program` there (N = drawCap, R = 13 + clog₂ N);
5. copies B and R into the consumer cells `d 11` and `d 12`.

The consumer region ends *exactly* equal to
`CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY tape B R` for the
produced `B = clog₂ (alphabetCap …)` and `R = rejectionAttemptCap (drawCap …)`;
the tape cell is never a copy target or an embedded-machine cell. Both
producer streams use the same raw counts read from the same consumer cells.
The private region keeps the producers' residue (existential), and the copy
scratch cell is blank at the end. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048

namespace Paper2.SamplerParameterJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.SamplerParameterBank

/-! ### Copy specifications -/

theorem inj_cp (c : ConsumerStack) (q : Private) (hq : q ≠ .inr (.inr 0)) :
    Function.Injective ![(.inl c : Stack), (.inr q : Stack), scr] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [scr]

theorem inj_pc (q : Private) (c : ConsumerStack) (hq : q ≠ .inr (.inr 0)) :
    Function.Injective ![(.inr q : Stack), (.inl c : Stack), scr] := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [scr]

/-- Sources for the bit-width bank, in its order q₁,q₂,s,w,Q,n,p. -/
def bwSrc : Fin 7 → ConsumerStack :=
  ![compilerCell 16, compilerCell 12, compilerCell 17, compilerCell 31,
    compilerCell 32, compilerCell 18, compilerCell 63]
def bwTarget (i : Fin 7) : Private := .inl (.inl ⟨i.val, by omega⟩)
def bwSpec (i : Fin 7) : Fin 3 ↪ Stack :=
  ⟨![.inl (bwSrc i), .inr (bwTarget i), scr],
    inj_cp _ _ (by simp [bwTarget])⟩
def bwList : List (Fin 3 ↪ Stack) := List.ofFn bwSpec

/-- Sources for the draw bank, in its order s,q₁,q₂,w,Q,p,k,mX,mY. -/
def nrSrc : Fin 9 → ConsumerStack :=
  ![compilerCell 17, compilerCell 16, compilerCell 12, compilerCell 31,
    compilerCell 32, compilerCell 63, compilerCell 64, countXCell, countYCell]
def nrTarget (i : Fin 9) : Private := .inr (.inl (.inl ⟨i.val, by omega⟩))
def nrSpec (i : Fin 9) : Fin 3 ↪ Stack :=
  ⟨![.inl (nrSrc i), .inr (nrTarget i), scr],
    inj_cp _ _ (by simp [nrTarget])⟩
def nrList : List (Fin 3 ↪ Stack) := List.ofFn nrSpec

def bOut : Private := .inl SamplerBitWidthMachine.logOutput
def rOut : Private := .inr (.inl (.inl 23))
def specB : Fin 3 ↪ Stack := ⟨![.inr bOut, .inl cellB, scr],
  inj_pc _ _ (by simp [bOut])⟩
def specR : Fin 3 ↪ Stack := ⟨![.inr rOut, .inl cellR, scr],
  inj_pc _ _ (by simp [rOut])⟩
def brList : List (Fin 3 ↪ Stack) := [specB, specR]

theorem bwSlots_eq (k : SamplerBitWidthMachine.Stack) :
    bwSlots k = .inr (.inl k) := rfl
theorem nrSlots_eq (k : SamplerNRProducer.Stack) :
    nrSlots k = .inr (.inr (.inl k)) := rfl

/-! ### Programs -/

def pA := CopyList.program bwList
def pB := fun l => stackStmt bwSlots (SamplerBitWidthMachine.program l)
def pC := CopyList.program nrList
def pD := fun l => stackStmt nrSlots (SamplerNRProducer.program l)
def pE := CopyList.program brList

def bwStart : SamplerBitWidthMachine.Label :=
  .inl (.inl (SamplerAlphabetMachine.first SamplerAlphabetMachine.slots))
def bwControl : SamplerBitWidthMachine.Control :=
  (((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots), none),
    ETHParameterScaleMachineLogCopy.copyControl none)

def cA := CopyList.initialControl bwList
def pAB := BitMachineRawSequence.program pA pB bwStart cA bwControl
def cAB := (cA, bwControl)
def pABC := BitMachineRawSequence.program pAB pC (CopyList.first nrList) cAB
  (CopyList.initialControl nrList)
def cABC := (cAB, CopyList.initialControl nrList)
def pABCD := BitMachineRawSequence.program pABC pD SamplerNRProducer.startLabel
  cABC SamplerNRProducer.startControl
def cABCD := (cABC, SamplerNRProducer.startControl)
def program := BitMachineRawSequence.program pABCD pE (CopyList.first brList)
  cABCD (CopyList.initialControl brList)

abbrev NRLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label DrawCoefficients.Label SamplerAffineInit.Label)
        SamplerLoopDraw.Label)
      ETHParameterScaleMachineLogCopy.Label)
    (SourceClauseFixedUnary.Label 13))
  BitMachineCopy.Label

def startLabel := BitMachineRawSequence.leftLabel (LB := CopyList.Label brList)
  (BitMachineRawSequence.leftLabel (LB := NRLabel)
    (BitMachineRawSequence.leftLabel (LB := CopyList.Label nrList)
      (BitMachineRawSequence.leftLabel (LB := SamplerBitWidthMachine.Label)
        (CopyList.first bwList))))
def startControl := (cABCD, CopyList.initialControl brList)
def finalControl := (cABCD, CopyList.initialControl brList)

/-! ### Public values and clock -/

def M (n p s q₁ q₂ w Q : Nat) : Nat :=
  RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q n p
def B (n p s q₁ q₂ w Q : Nat) : Nat := Nat.clog 2 (M n p s q₁ q₂ w Q)
def R (p s q₁ q₂ w Q k mX mY : Nat) : Nat :=
  SamplerNRProducer.R s q₁ q₂ w Q p k mX mY

def bwClock (n p s q₁ q₂ w Q : Nat) : Nat :=
  (515 + 30 + 2 * (q₁ + q₂ + 4*s + w + Q + n + p)) +
    (2 * M n p s q₁ q₂ w Q + 2) +
    (2 * M n p s q₁ q₂ w Q + 2 +
      (UnaryBinaryEncoding.coefficient + 6) * (M n p s q₁ q₂ w Q + 1)^2) + 2

def clock (n p s q₁ q₂ w Q k mX mY : Nat) : Nat :=
  (2*(q₁+q₂+s+w+Q+n+p) + 22) + 1 + bwClock n p s q₁ q₂ w Q + 1 +
    (2*(s+q₁+q₂+w+Q+p+k+mX+mY) + 28) + 1 +
    SamplerNRProducer.clock s q₁ q₂ w Q p k mX mY + 1 +
    ((2 * B n p s q₁ q₂ w Q + 3) + (2 * R p s q₁ q₂ w Q k mX mY + 3) + 1)

/-- The no-preloaded start bank: consumer bank with empty `B`/`R` words and a
blank private region. -/
def startBank (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    Stack → List Bool :=
  Sum.elim (initial n p s q₁ q₂ w Q k mX mY tape 0 0) (fun _ => [])

/-! ### Source values of the copies -/

theorem bwSrc_value (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) (i : Fin 7) :
    initial n p s q₁ q₂ w Q k mX mY tape 0 0 (bwSrc i) =
      SamplerAlphabetMachine.input q₁ q₂ s w Q n p ⟨i.val, by omega⟩ := by
  fin_cases i <;>
    simp [bwSrc, initial_compiler, publicBase_q1, publicBase_q2, publicBase_s,
      publicBase_w, publicBase_Q, publicBase_n, publicBase_p,
      SamplerAlphabetMachine.input]

theorem nrSrc_value (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) (i : Fin 9) :
    initial n p s q₁ q₂ w Q k mX mY tape 0 0 (nrSrc i) =
      DrawCoefficients.initialBank s q₁ q₂ w Q p k mX mY ⟨i.val, by omega⟩ := by
  fin_cases i <;>
    simp [nrSrc, initial_compiler, initial_countX, initial_countY,
      publicBase_q1, publicBase_q2, publicBase_s, publicBase_w, publicBase_Q,
      publicBase_p, publicBase_k, DrawCoefficients.initialBank,
      DrawCoefficients.unary]

theorem bw_fresh :
    (∀ x ∈ bwList, ∀ y ∈ bwList, y 1 ≠ x 0) ∧
      (bwList.map (fun x => x 1)).Nodup := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    simp [bwSpec]
  · rw [bwList, List.map_ofFn, List.nodup_ofFn]
    intro i j h
    simp only [Function.comp_apply, bwSpec, Function.Embedding.coeFn_mk,
      Matrix.cons_val_one, Matrix.cons_val_zero, bwTarget, Sum.inr.injEq,
      Sum.inl.injEq, Fin.mk.injEq] at h
    exact Fin.ext h

theorem nr_fresh :
    (∀ x ∈ nrList, ∀ y ∈ nrList, y 1 ≠ x 0) ∧
      (nrList.map (fun x => x 1)).Nodup := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    simp [nrSpec]
  · rw [nrList, List.map_ofFn, List.nodup_ofFn]
    intro i j h
    simp only [Function.comp_apply, nrSpec, Function.Embedding.coeFn_mk,
      Matrix.cons_val_one, Matrix.cons_val_zero, nrTarget, Sum.inr.injEq,
      Sum.inl.injEq, Fin.mk.injEq] at h
    exact Fin.ext h

theorem br_fresh :
    (∀ x ∈ brList, ∀ y ∈ brList, y 1 ≠ x 0) ∧
      (brList.map (fun x => x 1)).Nodup := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    simp only [brList, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [specB, specR]
  · simp [brList, specB, specR, cellB, cellR, drawCell, CodeHeaderDraw.d]

theorem scr_of_mem_bw : ∀ x ∈ bwList, x 2 = scr := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  rfl
theorem scr_of_mem_nr : ∀ x ∈ nrList, x 2 = scr := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  rfl
theorem scr_of_mem_br : ∀ x ∈ brList, x 2 = scr := by
  intro x hx
  simp only [brList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

theorem bw_target_ne_inl (x) (hx : x ∈ bwList) (c : ConsumerStack) :
    x 1 ≠ (.inl c : Stack) := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  simp [bwSpec]
theorem nr_target_ne_inl (x) (hx : x ∈ nrList) (c : ConsumerStack) :
    x 1 ≠ (.inl c : Stack) := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  simp [nrSpec]

/-! ### The whole run -/

theorem run_with_N (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    ∃ (t : Nat) (G : Private → List Bool),
      t ≤ clock n p s q₁ q₂ w Q k mX mY ∧
      ((advance program)^[t])
        (⟨some startLabel, startControl,
          startBank n p s q₁ q₂ w Q k mX mY tape⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, finalControl,
          Sum.elim (initial n p s q₁ q₂ w Q k mX mY tape
            (B n p s q₁ q₂ w Q) (R p s q₁ q₂ w Q k mX mY)) G⟩ ∧
      G (.inr (.inl (.inl 22))) =
        List.replicate (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) true ∧
      G (.inr (.inr 0)) = [] := by
  let I0 := initial n p s q₁ q₂ w Q k mX mY tape 0 0
  let W0 := startBank n p s q₁ q₂ w Q k mX mY tape
  have hW0c : ∀ c, W0 (.inl c) = I0 c := fun _ => rfl
  have hW0p : ∀ q : Private, W0 (.inr q) = [] := fun _ => rfl
  -- phase A: seven copies into the bit-width bank
  obtain ⟨tA, htA, hA⟩ := CopyList.run scr bwList W0 rfl scr_of_mem_bw
  obtain ⟨hA1, hA2⟩ := CopyList.apply_fresh bwList W0 bw_fresh.1 bw_fresh.2
    (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      rfl)
  set W1 := CopyList.apply W0 bwList with hW1def
  have hW1_inl : ∀ c, W1 (.inl c) = I0 c := fun c =>
    hA2 (.inl c) (fun x hx => bw_target_ne_inl x hx c)
  have hW1_bw : ∀ kk, SamplerBitWidthMachine.initial q₁ q₂ s w Q n p kk =
      W1 (bwSlots kk) := by
    intro kk
    rcases kk with i | y
    · by_cases hi : i.val < 7
      · have hmem : bwSpec ⟨i.val, hi⟩ ∈ bwList :=
          List.mem_ofFn.mpr ⟨_, rfl⟩
        have h := hA1 _ hmem
        have hcell : bwSpec ⟨i.val, hi⟩ 1 = bwSlots (.inl i) := rfl
        rw [hcell] at h
        rw [h]
        change _ = I0 (bwSrc ⟨i.val, hi⟩)
        rw [show I0 (bwSrc ⟨i.val, hi⟩) = _ from
          bwSrc_value n p s q₁ q₂ w Q k mX mY tape ⟨i.val, hi⟩]
        rfl
      · rw [hA2 (bwSlots (.inl i)) (by
          intro x hx
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
          simp only [bwSpec, Function.Embedding.coeFn_mk, Matrix.cons_val_one,
            Matrix.cons_val_zero, bwTarget, bwSlots_eq, ne_eq, Sum.inr.injEq,
            Sum.inl.injEq]
          intro h
          apply hi
          rw [← h]
          exact j.isLt)]
        change SamplerAlphabetMachine.input q₁ q₂ s w Q n p i = []
        have hi' : i = 7 ∨ i = 8 := by
          rcases i with ⟨v, hv⟩
          simp only [Fin.ext_iff] at *
          omega
        rcases hi' with rfl | rfl <;> rfl
    · rw [hA2 (bwSlots (.inr y)) (by
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        simp [bwSpec, bwTarget, bwSlots_eq])]
      rfl
  -- phase B: the bit-width machine on the private bank
  obtain ⟨tB, F, vB, htB, hB, hFM, hFB, hFraw⟩ :=
    SamplerBitWidthMachine.exact_bit_width q₁ q₂ s w Q n p
  let W2 := bank bwSlots W1 F
  have hB' : ((advance pB)^[tB])
      (⟨some bwStart, bwControl, W1⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots,
        none), vB), W2⟩ := by
    have hr := BitMachineStackRun.run bwSlots W1 SamplerBitWidthMachine.program
      (⟨some bwStart, bwControl, SamplerBitWidthMachine.initial q₁ q₂ s w Q n p⟩ :
        TM2.Cfg (fun _ : SamplerBitWidthMachine.Stack => Bool) _ _) tB
    rw [show ((advance SamplerBitWidthMachine.program)^[tB])
        (⟨some bwStart, bwControl, SamplerBitWidthMachine.initial q₁ q₂ s w Q n p⟩ :
          TM2.Cfg (fun _ : SamplerBitWidthMachine.Stack => Bool) _ _) = _ from hB] at hr
    have hstart : bank bwSlots W1 (SamplerBitWidthMachine.initial q₁ q₂ s w Q n p) = W1 :=
      bank_eq_self bwSlots W1 _ hW1_bw
    simp only [stackCfg, hstart] at hr
    exact hr
  have hW2_out : ∀ j, (¬ ∃ kk, bwSlots kk = j) → W2 j = W1 j :=
    fun j hj => bank_outside bwSlots W1 F j hj
  have hW2_inl : ∀ c, W2 (.inl c) = I0 c := fun c => by
    rw [hW2_out (.inl c) (by rintro ⟨kk, hk⟩; cases hk), hW1_inl]
  have hW2_nr : ∀ kk, W2 (nrSlots kk) = [] := by
    intro kk
    rw [hW2_out (nrSlots kk) (by rintro ⟨k', hk⟩; cases hk)]
    rw [hA2 (nrSlots kk) (by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      simp [bwSpec, bwTarget, nrSlots_eq])]
    rfl
  have hW2_scr : W2 scr = [] := by
    rw [hW2_out scr (by rintro ⟨k', hk⟩; cases hk)]
    rw [hA2 scr (by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      simp [bwSpec, bwTarget, scr])]
    rfl
  have hW2_B : W2 (.inr bOut) = List.replicate (B n p s q₁ q₂ w Q) true := by
    change bank bwSlots W1 F (bwSlots SamplerBitWidthMachine.logOutput) = _
    rw [bank_at]
    exact hFB
  -- phase C: nine copies into the draw bank
  obtain ⟨tC, htC, hC⟩ := CopyList.run scr nrList W2 hW2_scr scr_of_mem_nr
  obtain ⟨hC1, hC2⟩ := CopyList.apply_fresh nrList W2 nr_fresh.1 nr_fresh.2
    (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hW2_nr _)
  set W3 := CopyList.apply W2 nrList with hW3def
  have hW3_inl : ∀ c, W3 (.inl c) = I0 c := fun c => by
    rw [hC2 (.inl c) (fun x hx => nr_target_ne_inl x hx c), hW2_inl]
  have hW3_bOut : W3 (.inr bOut) = List.replicate (B n p s q₁ q₂ w Q) true := by
    rw [hC2 (.inr bOut) (by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      simp [nrSpec, nrTarget, bOut])]
    exact hW2_B
  have hW3_nr : ∀ kk, SamplerNRProducer.initialBank s q₁ q₂ w Q p k mX mY kk =
      W3 (nrSlots kk) := by
    intro kk
    rcases kk with j | y
    · by_cases hj : j.val < 9
      · have hmem : nrSpec ⟨j.val, hj⟩ ∈ nrList := List.mem_ofFn.mpr ⟨_, rfl⟩
        have h := hC1 _ hmem
        have hcell : nrSpec ⟨j.val, hj⟩ 1 = nrSlots (.inl j) := rfl
        rw [hcell] at h
        rw [h]
        change _ = W2 (.inl (nrSrc ⟨j.val, hj⟩))
        rw [hW2_inl, show I0 (nrSrc ⟨j.val, hj⟩) = _ from
          nrSrc_value n p s q₁ q₂ w Q k mX mY tape ⟨j.val, hj⟩]
        rfl
      · rw [hC2 (nrSlots (.inl j)) (by
          intro x hx
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
          simp only [nrSpec, Function.Embedding.coeFn_mk, Matrix.cons_val_one,
            Matrix.cons_val_zero, nrTarget, nrSlots_eq, ne_eq, Sum.inr.injEq,
            Sum.inl.injEq]
          intro h
          apply hj
          rw [← h]
          exact i.isLt), hW2_nr]
        change DrawCoefficients.initialBank s q₁ q₂ w Q p k mX mY j = []
        have h0 : j ≠ 0 := by intro h; subst h; simp at hj
        have h1 : j ≠ 1 := by intro h; subst h; simp at hj
        have h2 : j ≠ 2 := by intro h; subst h; simp at hj
        have h3 : j ≠ 3 := by intro h; subst h; simp at hj
        have h4 : j ≠ 4 := by intro h; subst h; simp at hj
        have h5 : j ≠ 5 := by intro h; subst h; simp at hj
        have h6 : j ≠ 6 := by intro h; subst h; simp at hj
        have h7 : j ≠ 7 := by intro h; subst h; simp at hj
        have h8 : j ≠ 8 := by intro h; subst h; simp at hj
        simp [DrawCoefficients.initialBank, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    · rw [hC2 (nrSlots (.inr y)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        simp [nrSpec, nrTarget, nrSlots_eq]), hW2_nr]
      rfl
  have hW3_scr : W3 scr = [] := by
    rw [hC2 scr (by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      simp [nrSpec, nrTarget, scr])]
    exact hW2_scr
  -- phase D: the draw-count/rejection producer on the private bank
  obtain ⟨tD, G, htD, hD, hG23, hG22, _hGraw⟩ :=
    SamplerNRProducer.run s q₁ q₂ w Q p k mX mY
  let W4 := bank nrSlots W3 G
  have hD' : ((advance pD)^[tD])
      (⟨some SamplerNRProducer.startLabel, SamplerNRProducer.startControl, W3⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (SamplerNRProducer.c12345, none), W4⟩ := by
    have hr := BitMachineStackRun.run nrSlots W3 SamplerNRProducer.program
      (⟨some SamplerNRProducer.startLabel, SamplerNRProducer.startControl,
        SamplerNRProducer.initialBank s q₁ q₂ w Q p k mX mY⟩ :
        TM2.Cfg (fun _ : SamplerNRProducer.Stack => Bool) _ _) tD
    rw [hD] at hr
    have hstart : bank nrSlots W3 (SamplerNRProducer.initialBank s q₁ q₂ w Q p k mX mY) = W3 :=
      bank_eq_self nrSlots W3 _ hW3_nr
    simp only [stackCfg, hstart] at hr
    exact hr
  have hW4_out : ∀ j, (¬ ∃ kk, nrSlots kk = j) → W4 j = W3 j :=
    fun j hj => bank_outside nrSlots W3 G j hj
  have hW4_inl : ∀ c, W4 (.inl c) = I0 c := fun c => by
    rw [hW4_out (.inl c) (by rintro ⟨kk, hk⟩; cases hk), hW3_inl]
  have hW4_scr : W4 scr = [] := by
    rw [hW4_out scr (by rintro ⟨kk, hk⟩; cases hk)]
    exact hW3_scr
  have hW4_bOut : W4 (.inr bOut) = List.replicate (B n p s q₁ q₂ w Q) true := by
    rw [hW4_out (.inr bOut) (by rintro ⟨kk, hk⟩; cases hk)]
    exact hW3_bOut
  have hW4_rOut : W4 (.inr rOut) = List.replicate (R p s q₁ q₂ w Q k mX mY) true := by
    change bank nrSlots W3 G (nrSlots (.inl 23)) = _
    rw [bank_at]
    exact hG23
  have hW4_nOut : W4 (nrSlots (.inl 22)) =
      List.replicate (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) true := by
    change bank nrSlots W3 G (nrSlots (.inl 22)) = _
    rw [bank_at]
    exact hG22
  -- phase E: copy B and R into the consumer cells d 11 and d 12
  obtain ⟨tE, htE, hE⟩ := CopyList.run scr brList W4 hW4_scr scr_of_mem_br
  obtain ⟨hE1, hE2⟩ := CopyList.apply_fresh brList W4 br_fresh.1 br_fresh.2
    (by
      intro x hx
      simp only [brList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · change W4 (.inl cellB) = []
        rw [hW4_inl]
        exact initial_cellB_zero n p s q₁ q₂ w Q k mX mY tape
      · change W4 (.inl cellR) = []
        rw [hW4_inl]
        exact initial_cellR_zero n p s q₁ q₂ w Q k mX mY tape)
  set W5 := CopyList.apply W4 brList with hW5def
  have hW5B : W5 (.inl cellB) = List.replicate (B n p s q₁ q₂ w Q) true := by
    have h := hE1 specB (by simp [brList])
    change W5 (.inl cellB) = W4 (.inr bOut) at h
    rw [h, hW4_bOut]
  have hW5R : W5 (.inl cellR) = List.replicate (R p s q₁ q₂ w Q k mX mY) true := by
    have h := hE1 specR (by simp [brList])
    change W5 (.inl cellR) = W4 (.inr rOut) at h
    rw [h, hW4_rOut]
  have hcellBR : cellB ≠ cellR := by
    simp [cellB, cellR, drawCell, CodeHeaderDraw.d]
  have hfinal : W5 = Sum.elim (initial n p s q₁ q₂ w Q k mX mY tape
      (B n p s q₁ q₂ w Q) (R p s q₁ q₂ w Q k mX mY)) (fun q => W5 (.inr q)) := by
    funext j
    rcases j with c | q
    · change W5 (.inl c) = initial n p s q₁ q₂ w Q k mX mY tape
        (B n p s q₁ q₂ w Q) (R p s q₁ q₂ w Q k mX mY) c
      rw [initial_BR]
      by_cases hR : c = cellR
      · subst hR
        rw [Function.update_self]
        exact hW5R
      · rw [Function.update_of_ne hR]
        by_cases hB : c = cellB
        · subst hB
          rw [Function.update_self]
          exact hW5B
        · rw [Function.update_of_ne hB]
          rw [hE2 (.inl c) (by
            intro x hx
            simp only [brList, List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · intro h
              exact hB (Sum.inl_injective h).symm
            · intro h
              exact hR (Sum.inl_injective h).symm)]
          exact hW4_inl c
    · rfl
  have hW5_scr : W5 scr = [] := by
    rw [hE2 scr (by
      intro x hx
      simp only [brList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [specB, specR, scr])]
    exact hW4_scr
  -- sequence the five phases
  obtain ⟨sAB, hsAB, rAB⟩ := BitMachineRawSequence.runs pA pB
    (CopyList.first bwList) bwStart cA cA bwControl
    ((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots, none), vB)
    W0 W1 W2 tA tB hA hB'
  obtain ⟨sABC, hsABC, rABC⟩ := BitMachineRawSequence.runs pAB pC
    (BitMachineRawSequence.leftLabel (CopyList.first bwList))
    (CopyList.first nrList) cAB
    (cA, ((SamplerAlphabetMachine.initialControl SamplerAlphabetMachine.slots, none), vB))
    (CopyList.initialControl nrList) (CopyList.initialControl nrList)
    W0 W2 W3 sAB tC rAB hC
  obtain ⟨sABCD, hsABCD, rABCD⟩ := BitMachineRawSequence.runs pABC pD
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (CopyList.first bwList)))
    SamplerNRProducer.startLabel cABC cABC
    SamplerNRProducer.startControl (SamplerNRProducer.c12345, none)
    W0 W3 W4 sABC tD rABC hD'
  obtain ⟨t, ht, r⟩ := BitMachineRawSequence.runs pABCD pE
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (CopyList.first bwList))))
    (CopyList.first brList) cABCD (cABC, (SamplerNRProducer.c12345, none))
    (CopyList.initialControl brList) (CopyList.initialControl brList)
    W0 W4 W5 sABCD tE rABCD hE
  refine ⟨t, fun q => W5 (.inr q), ?_, ?_, ?_, hW5_scr⟩
  · -- clock
    have hA' : CopyList.cost W0 bwList = 2*(q₁+q₂+s+w+Q+n+p) + 22 := by
      rw [CopyList.cost_fresh bwList W0 bw_fresh.1]
      simp only [bwList, List.ofFn_succ, List.ofFn_zero, CopyList.freshCost]
      simp only [bwSpec, Function.Embedding.coeFn_mk, Matrix.cons_val_zero]
      simp only [hW0c, I0, bwSrc_value]
      simp [SamplerAlphabetMachine.input]
      ring
    have hC' : CopyList.cost W2 nrList = 2*(s+q₁+q₂+w+Q+p+k+mX+mY) + 28 := by
      rw [CopyList.cost_fresh nrList W2 nr_fresh.1]
      simp only [nrList, List.ofFn_succ, List.ofFn_zero, CopyList.freshCost]
      simp only [nrSpec, Function.Embedding.coeFn_mk, Matrix.cons_val_zero]
      simp only [hW2_inl, I0, nrSrc_value]
      simp [DrawCoefficients.initialBank, DrawCoefficients.unary]
      ring
    have hE' : CopyList.cost W4 brList =
        (2 * B n p s q₁ q₂ w Q + 3) + (2 * R p s q₁ q₂ w Q k mX mY + 3) + 1 := by
      rw [CopyList.cost_fresh brList W4 br_fresh.1]
      simp only [brList, CopyList.freshCost, specB, specR,
        Function.Embedding.coeFn_mk, Matrix.cons_val_zero]
      rw [hW4_bOut, hW4_rOut]
      simp
      ring
    have htB' : tB ≤ bwClock n p s q₁ q₂ w Q := htB
    rw [hA'] at htA
    rw [hC'] at htC
    rw [hE'] at htE
    simp only [clock]
    omega
  · rw [← hfinal]
    exact r
  · change W5 (nrSlots (.inl 22)) = _
    rw [hE2 (nrSlots (.inl 22)) (by
      intro x hx
      simp only [brList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [specB, specR, nrSlots])]
    exact hW4_nOut

/-- Backward-compatible projection of `run_with_N`: the existing production
interface did not expose the producer's physical unary draw-count cell. -/
theorem run (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    ∃ (t : Nat) (G : Private → List Bool),
      t ≤ clock n p s q₁ q₂ w Q k mX mY ∧
      ((advance program)^[t])
        (⟨some startLabel, startControl,
          startBank n p s q₁ q₂ w Q k mX mY tape⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, finalControl,
          Sum.elim (initial n p s q₁ q₂ w Q k mX mY tape
            (B n p s q₁ q₂ w Q) (R p s q₁ q₂ w Q k mX mY)) G⟩ ∧
      G (.inr (.inr 0)) = [] := by
  obtain ⟨t, G, ht, hr, _, hs⟩ := run_with_N n p s q₁ q₂ w Q k mX mY tape
  exact ⟨t, G, ht, hr, hs⟩

/-! ### Physical production of the exact random-bit count

The producer's consumer bank has spare draw-loader cells. Two actual embedded
unary multipliers use those cells as scratch and output; no count is inserted
by a bank update at the machine boundary. -/

def bitCountSlot (i : Fin 16) : Stack := .inl (drawCell i)
def nSlot : Stack := nrSlots (.inl 22)

theorem initial_replace_tape (n p s q₁ q₂ w Q k mX mY Bv Rv : Nat)
    (tape tape' : List Bool) :
    initial n p s q₁ q₂ w Q k mX mY tape' Bv Rv =
      Function.update (initial n p s q₁ q₂ w Q k mX mY tape Bv Rv)
        (drawCell 0) tape' := by
  funext j
  by_cases hj : j = drawCell 0
  · subst j
    rw [Function.update_self, initial_tape]
  · rw [Function.update_of_ne hj]
    rcases j with (y | z) | x
    · rw [initial_sample, initial_sample]
    · rcases z with c | f
      · rcases c with (i | l) | c
        · by_cases hi : i = 0
          · subst i
            exact False.elim (hj rfl)
          · change initial n p s q₁ q₂ w Q k mX mY tape' Bv Rv (drawCell i) =
                initial n p s q₁ q₂ w Q k mX mY tape Bv Rv (drawCell i)
            rw [initial_draw, initial_draw]
            simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank, hi]
        · rw [initial_consumer, initial_consumer]
          rfl
        · rw [initial_consumer, initial_consumer]
          rfl
      · rw [initial_consumer, initial_consumer]
        rfl
    · rw [initial_writer, initial_writer]

theorem initial_spare_draw (n p s q₁ q₂ w Q k mX mY Bv Rv : Nat)
    (tape : List Bool) (i : Fin 16)
    (hi0 : i ≠ 0) (hi11 : i ≠ 11) (hi12 : i ≠ 12) :
    initial n p s q₁ q₂ w Q k mX mY tape Bv Rv (drawCell i) = [] := by
  rw [initial_draw]
  simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank,
    hi0, hi11, hi12]

def mulRBSlots : Fin 6 ↪ Stack where
  toFun := ![bitCountSlot 12, bitCountSlot 11, bitCountSlot 2,
    bitCountSlot 3, bitCountSlot 6, bitCountSlot 7]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [bitCountSlot, drawCell, CodeHeaderDraw.d] at h ⊢

def mulNRBSlots : Fin 6 ↪ Stack where
  toFun := ![nSlot, bitCountSlot 7, bitCountSlot 9,
    bitCountSlot 13, bitCountSlot 14, bitCountSlot 15]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [nSlot, nrSlots, bitCountSlot, drawCell, CodeHeaderDraw.d] at h ⊢

def mulRBProgram := MatrixStage4ScalarPreparationOps.multiplyProgram mulRBSlots
def mulNRBProgram := MatrixStage4ScalarPreparationOps.multiplyProgram mulNRBSlots
def bitCountProgram := BitMachineRawSequence.program mulRBProgram mulNRBProgram
  MatrixAddressMachine.Label.outer false false
def preparedBitCountProgram := BitMachineRawSequence.program program bitCountProgram
  (.inl MatrixAddressMachine.Label.outer) finalControl (false, false)

theorem bitCount_run (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (G : Private → List Bool)
    (hN : G (.inr (.inl (.inl 22))) =
      List.replicate (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) true) :
    let Bv := B n p s q₁ q₂ w Q
    let Rv := R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    let S : Stack → List Bool := Sum.elim
      (initial n p s q₁ q₂ w Q k mX mY tape Bv Rv) G
    let T := Function.update S (bitCountSlot 7) (List.replicate (Rv * Bv) true)
    let U := Function.update T (bitCountSlot 15)
      (List.replicate (Nv * (Rv * Bv)) true)
    ∃ t ≤ MatrixAddressMachine.exactTime Rv Bv 0 +
      MatrixAddressMachine.exactTime Nv (Rv * Bv) 0 + 2,
      ((advance bitCountProgram)^[t])
        (⟨some (.inl MatrixAddressMachine.Label.outer), (false, false), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (false, false), U⟩ ∧
      U (bitCountSlot 15) = List.replicate (Nv * (Rv * Bv)) true ∧
      U (bitCountSlot 7) = List.replicate (Rv * Bv) true ∧
      U (bitCountSlot 0) = tape ∧
      U (bitCountSlot 3) = [] ∧
      U (bitCountSlot 2) = [] ∧
      (∀ c : ConsumerStack, c ≠ drawCell 7 → c ≠ drawCell 15 →
        U (.inl c) = initial n p s q₁ q₂ w Q k mX mY tape Bv Rv c) := by
  dsimp
  let Bv := B n p s q₁ q₂ w Q
  let Rv := R p s q₁ q₂ w Q k mX mY
  let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  let S : Stack → List Bool := Sum.elim
    (initial n p s q₁ q₂ w Q k mX mY tape Bv Rv) G
  let T := Function.update S (bitCountSlot 7) (List.replicate (Rv * Bv) true)
  let U := Function.update T (bitCountSlot 15)
    (List.replicate (Nv * (Rv * Bv)) true)
  have hblank (i : Fin 16) (hi : i ≠ 0) (hi11 : i ≠ 11) (hi12 : i ≠ 12) :
      S (bitCountSlot i) = [] := by
    change initial n p s q₁ q₂ w Q k mX mY tape Bv Rv (drawCell i) = []
    rw [initial_draw]
    simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank,
      hi, hi11, hi12]
  have hR : S (mulRBSlots 0) = List.replicate Rv true := by
    change initial n p s q₁ q₂ w Q k mX mY tape Bv Rv (drawCell 12) = _
    rw [initial_draw]
    simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
  have hB : S (mulRBSlots 1) = List.replicate Bv true := by
    change initial n p s q₁ q₂ w Q k mX mY tape Bv Rv (drawCell 11) = _
    rw [initial_draw]
    simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
  have hfirst := MatrixStage4ScalarPreparationOps.multiply_run mulRBSlots S Rv Bv
    hR hB (hblank 2 (by decide) (by decide) (by decide))
    (hblank 3 (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide))
  have h7 : S (bitCountSlot 7) = [] :=
    hblank 7 (by decide) (by decide) (by decide)
  have hfirst' : ((advance mulRBProgram)^[MatrixAddressMachine.exactTime Rv Bv 0])
      (⟨some .outer, false, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, false, T⟩ := by
    simpa only [mulRBProgram, show mulRBSlots 5 = bitCountSlot 7 from rfl,
      h7, List.append_nil, T] using hfirst
  have hN' : T (mulNRBSlots 0) = List.replicate Nv true := by
    change Function.update S (bitCountSlot 7) _ nSlot = _
    rw [Function.update_of_ne (by simp [nSlot, nrSlots, bitCountSlot])]
    exact hN
  have h7' : T (mulNRBSlots 1) = List.replicate (Rv * Bv) true := by
    exact Function.update_self ..
  have h9 : T (mulNRBSlots 2) = [] := by
    change Function.update S (bitCountSlot 7) _ (bitCountSlot 9) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    exact hblank 9 (by decide) (by decide) (by decide)
  have h13 : T (mulNRBSlots 3) = [] := by
    change Function.update S (bitCountSlot 7) _ (bitCountSlot 13) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    exact hblank 13 (by decide) (by decide) (by decide)
  have h14 : T (mulNRBSlots 4) = [] := by
    change Function.update S (bitCountSlot 7) _ (bitCountSlot 14) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    exact hblank 14 (by decide) (by decide) (by decide)
  have h15 : T (mulNRBSlots 5) = [] := by
    change Function.update S (bitCountSlot 7) _ (bitCountSlot 15) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    exact hblank 15 (by decide) (by decide) (by decide)
  have hsecond := MatrixStage4ScalarPreparationOps.multiply_run mulNRBSlots T Nv
    (Rv * Bv) hN' h7' h9 h13 h14
  have hsecond' : ((advance mulNRBProgram)^[
      MatrixAddressMachine.exactTime Nv (Rv * Bv) 0])
      (⟨some .outer, false, T⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, false, U⟩ := by
    have h15' : T (bitCountSlot 15) = [] := h15
    simpa only [mulNRBProgram, show mulNRBSlots 5 = bitCountSlot 15 from rfl,
      h15', List.append_nil, U] using hsecond
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs mulRBProgram mulNRBProgram
    MatrixAddressMachine.Label.outer MatrixAddressMachine.Label.outer false false
    false false S T U (MatrixAddressMachine.exactTime Rv Bv 0)
    (MatrixAddressMachine.exactTime Nv (Rv * Bv) 0) hfirst' hsecond'
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [Bv, Rv, Nv] at ht ⊢
    omega
  · exact hr
  · exact Function.update_self ..
  · change Function.update T (bitCountSlot 15) _ (bitCountSlot 7) = _
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    exact Function.update_self ..
  · change Function.update T (bitCountSlot 15) _ (bitCountSlot 0) = tape
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    change Function.update S (bitCountSlot 7) _ (bitCountSlot 0) = tape
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    change initial n p s q₁ q₂ w Q k mX mY tape Bv Rv (drawCell 0) = tape
    exact initial_tape ..
  · change Function.update T (bitCountSlot 15) _ (bitCountSlot 3) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    change Function.update S (bitCountSlot 7) _ (bitCountSlot 3) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    exact hblank 3 (by decide) (by decide) (by decide)
  · change Function.update T (bitCountSlot 15) _ (bitCountSlot 2) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    change Function.update S (bitCountSlot 7) _ (bitCountSlot 2) = []
    rw [Function.update_of_ne (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])]
    exact hblank 2 (by decide) (by decide) (by decide)
  · intro c hc7 hc15
    change Function.update T (bitCountSlot 15) _ (.inl c) = _
    rw [Function.update_of_ne (by
      change (Sum.inl c : Stack) ≠ Sum.inl (drawCell 15)
      exact fun h => hc15 (Sum.inl_injective h))]
    change Function.update S (bitCountSlot 7) _ (.inl c) = _
    rw [Function.update_of_ne (by
      change (Sum.inl c : Stack) ≠ Sum.inl (drawCell 7)
      exact fun h => hc7 (Sum.inl_injective h))]
    rfl

/-- One fixed physical controller, starting with raw public unary counts and
an arbitrary tape, produces the exact scheduled unary bit count. Both the
parameter preparation and the two multiplication phases are charged. -/
theorem prepared_bitCount_run (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    let Bv := B n p s q₁ q₂ w Q
    let Rv := R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    ∃ (t : Nat) (F : Stack → List Bool),
      t ≤ clock n p s q₁ q₂ w Q k mX mY +
        MatrixAddressMachine.exactTime Rv Bv 0 +
        MatrixAddressMachine.exactTime Nv (Rv * Bv) 0 + 3 ∧
      ((advance preparedBitCountProgram)^[t])
        (⟨some (.inl startLabel), (startControl, (false, false)),
          startBank n p s q₁ q₂ w Q k mX mY tape⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (finalControl, (false, false)), F⟩ ∧
      F (bitCountSlot 15) = List.replicate (Nv * (Rv * Bv)) true ∧
      F (bitCountSlot 7) = List.replicate (Rv * Bv) true ∧
      F (bitCountSlot 0) = tape ∧
      F (bitCountSlot 3) = [] ∧
      F (bitCountSlot 2) = [] ∧
      (∀ c : ConsumerStack, c ≠ drawCell 7 → c ≠ drawCell 15 →
        F (.inl c) = initial n p s q₁ q₂ w Q k mX mY tape Bv Rv c) := by
  dsimp
  let Bv := B n p s q₁ q₂ w Q
  let Rv := R p s q₁ q₂ w Q k mX mY
  let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  obtain ⟨tp, G, htp, hp, hN, _⟩ := run_with_N n p s q₁ q₂ w Q k mX mY tape
  obtain ⟨tc, htc, hc, hout, h7, htape, h3, h2, hframe⟩ := bitCount_run n p s q₁ q₂ w Q k mX mY
    tape G hN
  let S : Stack → List Bool := Sum.elim
    (initial n p s q₁ q₂ w Q k mX mY tape Bv Rv) G
  let T := Function.update S (bitCountSlot 7) (List.replicate (Rv * Bv) true)
  let F := Function.update T (bitCountSlot 15)
    (List.replicate (Nv * (Rv * Bv)) true)
  have hp' : ((advance program)^[tp])
      (⟨some startLabel, startControl,
        startBank n p s q₁ q₂ w Q k mX mY tape⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, finalControl, S⟩ := hp
  have hc' : ((advance bitCountProgram)^[tc])
      (⟨some (.inl MatrixAddressMachine.Label.outer), (false, false), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (false, false), F⟩ := hc
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs program bitCountProgram
    startLabel (.inl MatrixAddressMachine.Label.outer) startControl finalControl
    (false, false) (false, false)
    (startBank n p s q₁ q₂ w Q k mX mY tape) S F tp tc hp' hc'
  refine ⟨t, F, ?_, ?_, hout, h7, htape, h3, h2, hframe⟩
  · dsimp only [Bv, Rv, Nv] at htc ⊢
    omega
  · exact hr

/-! ### Charged cut and order restoration -/

inductive CutLabel | cut | clear | restore | done
  deriving DecidableEq, Fintype

def cutProgram : CutLabel → TM2.Stmt (fun _ : Stack => Bool) CutLabel
    (Option Bool × Unit)
  | .cut => NPOwner1.cutStmt (bitCountSlot 15) (bitCountSlot 0)
      (bitCountSlot 3) .cut .clear
  | .clear => Paper2.Unit4Shell.Loops.moveStmt (bitCountSlot 0) (bitCountSlot 2)
      .clear .restore
  | .restore => Paper2.Unit4Shell.Loops.moveStmt (bitCountSlot 3) (bitCountSlot 0)
      .restore .done
  | .done => .halt

def preparedCutProgram := BitMachineRawSequence.program preparedBitCountProgram
  cutProgram CutLabel.cut (finalControl, (false, false)) (none, ())

/-- The exact random prefix is physically cut, the unused suffix is consumed,
and the retained prefix is reversed back into tape order. The count and
discarded suffix remain in explicitly identified residue cells for the
subsequent cleanup phase. -/
theorem cut_run (count : Nat) (tape : List Bool) (S : Stack → List Bool)
    (hcount : S (bitCountSlot 15) = List.replicate count true)
    (htape : S (bitCountSlot 0) = tape)
    (hcut : S (bitCountSlot 3) = []) :
    ∃ (t : Nat) (F : Stack → List Bool),
      t ≤ count + tape.length + 4 ∧
      ((advance cutProgram)^[t])
        (⟨some CutLabel.cut, (none, ()), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (none, ()), F⟩ ∧
      F (bitCountSlot 0) = tape.take count ∧
      F (bitCountSlot 3) = [] ∧
      (∀ c, c ≠ bitCountSlot 0 → c ≠ bitCountSlot 2 →
        c ≠ bitCountSlot 3 → c ≠ bitCountSlot 15 → F c = S c) := by
  let u := bitCountSlot 15
  let m := bitCountSlot 0
  let o := bitCountSlot 3
  let junk := bitCountSlot 2
  have hum : u ≠ m := by simp [u, m, bitCountSlot, drawCell, CodeHeaderDraw.d]
  have huo : u ≠ o := by simp [u, o, bitCountSlot, drawCell, CodeHeaderDraw.d]
  have hmo : m ≠ o := by simp [m, o, bitCountSlot, drawCell, CodeHeaderDraw.d]
  have hmj : m ≠ junk := by simp [m, junk, bitCountSlot, drawCell, CodeHeaderDraw.d]
  have hoj : o ≠ junk := by simp [o, junk, bitCountSlot, drawCell, CodeHeaderDraw.d]
  obtain ⟨tc, vc, U', htc, hc⟩ := NPOwner1.cut_loop cutProgram u m o
    CutLabel.cut CutLabel.clear hum huo hmo rfl count tape S none () hcount htape
  let S1 := Function.update
    (Function.update (Function.update S o ((tape.take count).reverse ++ S o)) m
      (tape.drop count)) u U'
  have hc' : ((advance cutProgram)^[tc])
      (⟨some CutLabel.cut, (none, ()), S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some CutLabel.clear, (vc, ()), S1⟩ := hc
  have hS1m : S1 m = tape.drop count := by
    simp only [S1, Function.update_of_ne hum.symm, Function.update_self]
  have hS1o : S1 o = (tape.take count).reverse := by
    have hSo : S o = [] := hcut
    simp only [S1, Function.update_of_ne huo.symm, Function.update_of_ne hmo.symm,
      Function.update_self, hSo, List.append_nil]
  obtain hclear := Paper2.Unit4Shell.Loops.move_loop cutProgram m junk
    CutLabel.clear CutLabel.restore hmj rfl (tape.drop count) S1 vc () hS1m
  let S2 := Function.update
    (Function.update S1 junk ((tape.drop count).reverse ++ S1 junk)) m []
  have hclear' : ((advance cutProgram)^[(tape.drop count).length + 1])
      (⟨some CutLabel.clear, (vc, ()), S1⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some CutLabel.restore, (none, ()), S2⟩ := hclear
  have hS2o : S2 o = (tape.take count).reverse := by
    rw [show S2 o = S1 o from by
      simp only [S2, Function.update_of_ne hmo.symm, Function.update_of_ne hoj]]
    exact hS1o
  have hS2m : S2 m = [] := Function.update_self ..
  obtain hrestore := Paper2.Unit4Shell.Loops.move_loop cutProgram o m
    CutLabel.restore CutLabel.done hmo.symm rfl (tape.take count).reverse S2 none () hS2o
  let S3 := Function.update
    (Function.update S2 m ((tape.take count).reverse.reverse ++ S2 m)) o []
  have hrestore' : ((advance cutProgram)^[(tape.take count).reverse.length + 1])
      (⟨some CutLabel.restore, (none, ()), S2⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some CutLabel.done, (none, ()), S3⟩ := hrestore
  have hdone := Paper2.Unit4Shell.Loops.halt_step cutProgram CutLabel.done rfl
    (none, ()) S3
  have hchain := Paper2.Unit4Shell.Loops.iter_chain
    (Paper2.Unit4Shell.Loops.iter_chain
      (Paper2.Unit4Shell.Loops.iter_chain hc' hclear') hrestore')
    (show (advance cutProgram)^[1]
      (⟨some CutLabel.done, (none, ()), S3⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (none, ()), S3⟩ from by exact hdone)
  refine ⟨tc + ((tape.drop count).length + 1) +
    ((tape.take count).reverse.length + 1) + 1, S3, ?_, hchain, ?_, ?_, ?_⟩
  · have hsplit : (tape.take count).length + (tape.drop count).length = tape.length := by
      rw [← List.length_append, List.take_append_drop]
    simp only [List.length_reverse]
    omega
  · change S3 m = tape.take count
    simp only [S3, Function.update_of_ne hmo, Function.update_self,
      hS2m, List.append_nil, List.reverse_reverse]
  · exact Function.update_self ..
  · intro c h0 h2 h3 h15
    have hc0 : c ≠ m := h0
    have hc2 : c ≠ junk := h2
    have hc3 : c ≠ o := h3
    have hc15 : c ≠ u := h15
    simp only [S3, S2, S1, Function.update_of_ne hc0,
      Function.update_of_ne hc2, Function.update_of_ne hc3,
      Function.update_of_ne hc15]

/-- The preparation, both multiplications, and the exact prefix cut form one
finite physical program. In particular no arbitrary extension of the random
tape is passed to the sampler: the output tape is exactly the selected prefix. -/
theorem prepared_cut_run (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    let Bv := B n p s q₁ q₂ w Q
    let Rv := R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    let D := Nv * (Rv * Bv)
    ∃ (t : Nat) (F : Stack → List Bool),
      t ≤ clock n p s q₁ q₂ w Q k mX mY +
        MatrixAddressMachine.exactTime Rv Bv 0 +
        MatrixAddressMachine.exactTime Nv (Rv * Bv) 0 +
        D + tape.length + 8 ∧
      ((advance preparedCutProgram)^[t])
        (⟨some (.inl (.inl startLabel)),
          ((startControl, (false, false)), (none, ())),
          startBank n p s q₁ q₂ w Q k mX mY tape⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((finalControl, (false, false)), (none, ())), F⟩ ∧
      F (bitCountSlot 0) = tape.take D ∧
      (F (bitCountSlot 2)).length ≤
        (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram ∧
      F (bitCountSlot 3) = [] ∧
      F (bitCountSlot 7) = List.replicate (Rv * Bv) true ∧
      (F (bitCountSlot 15)).length ≤
        D + (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram ∧
      (∀ c : ConsumerStack, c ≠ drawCell 0 → c ≠ drawCell 2 →
        c ≠ drawCell 3 → c ≠ drawCell 7 → c ≠ drawCell 15 →
        F (.inl c) = initial n p s q₁ q₂ w Q k mX mY tape Bv Rv c) := by
  dsimp
  let Bv := B n p s q₁ q₂ w Q
  let Rv := R p s q₁ q₂ w Q k mX mY
  let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  let D := Nv * (Rv * Bv)
  obtain ⟨tp, S, htp, hp, hD, h7, htape, h3, h2, hframe⟩ :=
    prepared_bitCount_run n p s q₁ q₂ w Q k mX mY tape
  obtain ⟨tc, F, htc, hc, hFtape, hF3, hcutframe⟩ := cut_run D tape S hD htape h3
  have hF2len : (F (bitCountSlot 2)).length ≤
      (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram := by
    have hg := BitMachineStackGrowth.run_growth cutProgram
      (⟨some CutLabel.cut, (none, ()), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) tc (bitCountSlot 2)
    rw [hc] at hg
    change (F (bitCountSlot 2)).length ≤
      (S (bitCountSlot 2)).length + BitMachineStackGrowth.perStep cutProgram * tc at hg
    calc
      (F (bitCountSlot 2)).length ≤
          (S (bitCountSlot 2)).length + BitMachineStackGrowth.perStep cutProgram * tc := hg
      _ = BitMachineStackGrowth.perStep cutProgram * tc := by simp [h2]
      _ ≤ BitMachineStackGrowth.perStep cutProgram * (D + tape.length + 4) :=
        Nat.mul_le_mul_left _ htc
      _ = (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram :=
        Nat.mul_comm _ _
  have hF15len : (F (bitCountSlot 15)).length ≤
      D + (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram := by
    have hg := BitMachineStackGrowth.run_growth cutProgram
      (⟨some CutLabel.cut, (none, ()), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) tc (bitCountSlot 15)
    rw [hc] at hg
    change (F (bitCountSlot 15)).length ≤
      (S (bitCountSlot 15)).length + BitMachineStackGrowth.perStep cutProgram * tc at hg
    calc
      (F (bitCountSlot 15)).length ≤
          (S (bitCountSlot 15)).length + BitMachineStackGrowth.perStep cutProgram * tc := hg
      _ = D + BitMachineStackGrowth.perStep cutProgram * tc := by
        rw [hD, List.length_replicate]
      _ ≤ D + BitMachineStackGrowth.perStep cutProgram * (D + tape.length + 4) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ htc) _
      _ = D + (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram := by
        rw [Nat.mul_comm]
  have hF7 : F (bitCountSlot 7) = List.replicate (Rv * Bv) true := by
    exact (hcutframe (bitCountSlot 7)
      (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])
      (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])
      (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])
      (by simp [bitCountSlot, drawCell, CodeHeaderDraw.d])).trans h7
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs preparedBitCountProgram
    cutProgram (.inl startLabel) CutLabel.cut (startControl, (false, false))
    (finalControl, (false, false)) (none, ()) (none, ())
    (startBank n p s q₁ q₂ w Q k mX mY tape) S F tp tc hp hc
  refine ⟨t, F, ?_, ?_, hFtape, hF2len, hF3, hF7, hF15len, ?_⟩
  · dsimp only [Bv, Rv, Nv, D] at htp htc ⊢
    omega
  · exact hr
  · intro c h0 h2 h3 h7 h15
    have hnot (i : Fin 16) (h : c ≠ drawCell i) :
        (Sum.inl c : Stack) ≠ bitCountSlot i := by
      change (Sum.inl c : Stack) ≠ Sum.inl (drawCell i)
      exact fun e => h (Sum.inl_injective e)
    exact (hcutframe (.inl c) (hnot 0 h0) (hnot 2 h2)
      (hnot 3 h3) (hnot 15 h15)).trans (hframe c h7 h15)

/-! ### Charged cleanup of consumer residue -/

def cleanupCells : Fin 3 → Stack :=
  ![bitCountSlot 2, bitCountSlot 7, bitCountSlot 15]

theorem cleanupCells_injective : Function.Injective cleanupCells := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [cleanupCells, bitCountSlot, drawCell, CodeHeaderDraw.d] at h ⊢

inductive CleanupLabel | first | second | third | finish | done
  deriving DecidableEq, Fintype

def cleanupLabel : Fin 4 → CleanupLabel :=
  ![.first, .second, .third, .finish]

def cleanupProgram : CleanupLabel → TM2.Stmt (fun _ : Stack => Bool)
    CleanupLabel (Unit × Option Bool)
  | .first => BitMachineClearBank.clearStep (cleanupCells 0) .first .second
  | .second => BitMachineClearBank.clearStep (cleanupCells 1) .second .third
  | .third => BitMachineClearBank.clearStep (cleanupCells 2) .third .finish
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

def preparedCleanupProgram := BitMachineRawSequence.program preparedCutProgram
  cleanupProgram CleanupLabel.first
  ((finalControl, (false, false)), (none, ())) ((), none)

/-- Every residual bit in the discarded suffix, intermediate product, and
remaining unary count is explicitly popped. All other bank cells survive. -/
theorem cleanup_run (S : Stack → List Bool) :
    ((advance cleanupProgram)^[
      (∑ i : Fin 3, (S (cleanupCells i)).length) + 5])
      (⟨some CleanupLabel.first, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared cleanupCells S⟩ := by
  have hsteps : ∀ i : Fin 3,
      cleanupProgram (cleanupLabel i.castSucc) =
      BitMachineClearBank.clearStep (cleanupCells i)
        (cleanupLabel i.castSucc) (cleanupLabel i.succ) := by
    intro i
    fin_cases i <;> rfl
  have hfinish : cleanupProgram (cleanupLabel (Fin.last 3)) =
      BitMachineClearBank.finishStep id CleanupLabel.done := rfl
  have hclear := BitMachineClearBank.clear_bank_run cleanupProgram id
    CleanupLabel.done 3 cleanupCells cleanupCells_injective cleanupLabel
    hsteps hfinish () S
  have hdone : advance cleanupProgram
      (⟨some CleanupLabel.done, ((), none),
        BitMachineClearBank.cleared cleanupCells S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared cleanupCells S⟩ := by
    simp [BitMachineEncoding.advance, TM2.step, cleanupProgram]
  have hchain := Paper2.Unit4Shell.Loops.iter_chain hclear
    (show (advance cleanupProgram)^[1]
      (⟨some CleanupLabel.done, ((), none),
        BitMachineClearBank.cleared cleanupCells S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared cleanupCells S⟩ from by
        exact hdone)
  simpa only [Nat.reduceAdd, Nat.add_assoc] using hchain

/-- A single physical program prepares the public counts, selects and cuts the
exact random prefix, restores its order, and drains all three consumer residue
cells. The cleanup clock is bounded by the original tape length and public
count, using a growth bound only for the shallow cut controller. -/
theorem prepared_cleanup_run (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    let Bv := B n p s q₁ q₂ w Q
    let Rv := R p s q₁ q₂ w Q k mX mY
    let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
    let D := Nv * (Rv * Bv)
    ∃ (t : Nat) (F H : Stack → List Bool),
      t ≤ clock n p s q₁ q₂ w Q k mX mY +
        MatrixAddressMachine.exactTime Rv Bv 0 +
        MatrixAddressMachine.exactTime Nv (Rv * Bv) 0 +
        D + tape.length +
        Rv * Bv + D +
        (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram +
        (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram + 14 ∧
      ((advance preparedCleanupProgram)^[t])
        (⟨some (.inl (.inl (.inl startLabel))),
          (((startControl, (false, false)), (none, ())), ((), none)),
          startBank n p s q₁ q₂ w Q k mX mY tape⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((finalControl, (false, false)), (none, ())), ((), none)), H⟩ ∧
      H = BitMachineClearBank.cleared cleanupCells F ∧
      H (bitCountSlot 0) = tape.take D ∧
      H (bitCountSlot 2) = [] ∧
      H (bitCountSlot 3) = [] ∧
      H (bitCountSlot 7) = [] ∧
      H (bitCountSlot 15) = [] ∧
      (∀ c : ConsumerStack,
        H (.inl c) = initial n p s q₁ q₂ w Q k mX mY (tape.take D) Bv Rv c) := by
  dsimp
  let Bv := B n p s q₁ q₂ w Q
  let Rv := R p s q₁ q₂ w Q k mX mY
  let Nv := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  let D := Nv * (Rv * Bv)
  obtain ⟨tp, F, htp, hp, hF0, hF2len, hF3, hF7, hF15len, hFframe⟩ :=
    prepared_cut_run n p s q₁ q₂ w Q k mX mY tape
  have hsum : (∑ i : Fin 3, (F (cleanupCells i)).length) ≤
      Rv * Bv + D +
      (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram +
      (D + tape.length + 4) * BitMachineStackGrowth.perStep cutProgram := by
    have heq : (∑ i : Fin 3, (F (cleanupCells i)).length) =
        (F (bitCountSlot 2)).length + (F (bitCountSlot 7)).length +
          (F (bitCountSlot 15)).length := by
      simp [Fin.sum_univ_succ, cleanupCells, Nat.add_assoc]
    rw [heq, hF7, List.length_replicate]
    dsimp only [Bv, Rv, Nv, D] at hF2len hF15len ⊢
    omega
  let H := BitMachineClearBank.cleared cleanupCells F
  have hc := cleanup_run F
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs preparedCutProgram
    cleanupProgram (.inl (.inl startLabel)) CleanupLabel.first
    ((startControl, (false, false)), (none, ()))
    ((finalControl, (false, false)), (none, ())) ((), none) ((), none)
    (startBank n p s q₁ q₂ w Q k mX mY tape) F H tp
    ((∑ i : Fin 3, (F (cleanupCells i)).length) + 5) hp hc
  refine ⟨t, F, H, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [Bv, Rv, Nv, D] at htp hsum ⊢
    omega
  · exact hr
  · change BitMachineClearBank.cleared cleanupCells F (bitCountSlot 0) = _
    rw [BitMachineClearBank.cleared_foreign cleanupCells F (bitCountSlot 0)]
    · exact hF0
    · intro i
      fin_cases i <;> simp [cleanupCells, bitCountSlot, drawCell, CodeHeaderDraw.d]
  · exact BitMachineClearBank.cleared_bank cleanupCells F 0
  · change BitMachineClearBank.cleared cleanupCells F (bitCountSlot 3) = _
    rw [BitMachineClearBank.cleared_foreign cleanupCells F (bitCountSlot 3)]
    · exact hF3
    · intro i
      fin_cases i <;> simp [cleanupCells, bitCountSlot, drawCell, CodeHeaderDraw.d]
  · exact BitMachineClearBank.cleared_bank cleanupCells F 1
  · exact BitMachineClearBank.cleared_bank cleanupCells F 2
  · intro c
    by_cases h0 : c = drawCell 0
    · subst c
      change BitMachineClearBank.cleared cleanupCells F (bitCountSlot 0) = _
      rw [BitMachineClearBank.cleared_foreign cleanupCells F (bitCountSlot 0)]
      · rw [hF0, initial_tape]
      · intro i
        fin_cases i <;> simp [cleanupCells, bitCountSlot, drawCell, CodeHeaderDraw.d]
    by_cases h2 : c = drawCell 2
    · subst c
      change BitMachineClearBank.cleared cleanupCells F (cleanupCells 0) = _
      rw [BitMachineClearBank.cleared_bank cleanupCells F 0]
      exact (initial_spare_draw n p s q₁ q₂ w Q k mX mY Bv Rv (tape.take D) 2
        (by decide) (by decide) (by decide)).symm
    by_cases h3 : c = drawCell 3
    · subst c
      change BitMachineClearBank.cleared cleanupCells F (bitCountSlot 3) = _
      rw [BitMachineClearBank.cleared_foreign cleanupCells F (bitCountSlot 3)]
      · rw [hF3]
        exact (initial_spare_draw n p s q₁ q₂ w Q k mX mY Bv Rv (tape.take D) 3
          (by decide) (by decide) (by decide)).symm
      · intro i
        fin_cases i <;> simp [cleanupCells, bitCountSlot, drawCell, CodeHeaderDraw.d]
    by_cases h7 : c = drawCell 7
    · subst c
      change BitMachineClearBank.cleared cleanupCells F (cleanupCells 1) = _
      rw [BitMachineClearBank.cleared_bank cleanupCells F 1]
      exact (initial_spare_draw n p s q₁ q₂ w Q k mX mY Bv Rv (tape.take D) 7
        (by decide) (by decide) (by decide)).symm
    by_cases h15 : c = drawCell 15
    · subst c
      change BitMachineClearBank.cleared cleanupCells F (cleanupCells 2) = _
      rw [BitMachineClearBank.cleared_bank cleanupCells F 2]
      exact (initial_spare_draw n p s q₁ q₂ w Q k mX mY Bv Rv (tape.take D) 15
        (by decide) (by decide) (by decide)).symm
    have hforeign : H (.inl c) = F (.inl c) := by
      change BitMachineClearBank.cleared cleanupCells F (.inl c) = F (.inl c)
      apply BitMachineClearBank.cleared_foreign cleanupCells F (.inl c)
      intro i
      fin_cases i
      · change Sum.inl (drawCell 2) ≠ Sum.inl c
        exact fun e => h2 (Sum.inl_injective e).symm
      · change Sum.inl (drawCell 7) ≠ Sum.inl c
        exact fun e => h7 (Sum.inl_injective e).symm
      · change Sum.inl (drawCell 15) ≠ Sum.inl c
        exact fun e => h15 (Sum.inl_injective e).symm
    rw [hforeign, hFframe c h0 h2 h3 h7 h15]
    rw [initial_replace_tape n p s q₁ q₂ w Q k mX mY Bv Rv tape (tape.take D),
      Function.update_of_ne h0]

end

#print axioms run
#print axioms run_with_N
#print axioms bitCount_run
#print axioms prepared_bitCount_run
#print axioms cut_run
#print axioms prepared_cut_run
#print axioms cleanup_run
#print axioms prepared_cleanup_run

end Paper2.SamplerParameterJoin
