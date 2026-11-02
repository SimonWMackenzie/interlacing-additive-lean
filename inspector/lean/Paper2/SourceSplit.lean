import Paper2.RawRowSplit

/-! Unit 3, segment (3), first piece (PARTIAL segment): the source-row split.
After the raw-row dispatch (`TagDispatch.ifProgram`) has popped the sum bit
`true` of a source raw row `.inr (i, u)`, the raw-row cell holds
`(prodCodec (defaultItemCodec n s) C.1).encode (i, u)` =
`unary i.1 ++ [kind bit] ++ unary (value) ++ C.1.encode u`.
ONE fixed program (read unary, move one bit, read unary; generic in the
ambient bank) leaves exactly `C.1.encode u` — the row half of
`baseRequest activity (.inr (i, u)) Z` — in the raw-row cell and the three
item fields as separate unary / one-bit cells (the operand form taken by the
fixed endpoint-rank controller). The column half (`sourceColumn`) is NOT in
this file. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.SourceSplit

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)

variable {J : Type*} [DecidableEq J]

/-- Move the head bit of `src` onto `dst`. -/
def moveBit (src dst : J) : Unit → TM2.Stmt (fun _ : J => Bool) Unit (Option Bool) :=
  fun _ => pop src (fun _ b => b) (push dst (fun v => v.getD false) halt)

theorem moveBit_run (src dst : J) (hne : src ≠ dst) (S : J → List Bool) (v : Option Bool)
    (b : Bool) (rest : List Bool) (hS : S src = b :: rest) :
    ((advance (moveBit src dst))^[1]) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : J => Bool) Unit (Option Bool)) =
      ⟨none, some b, Function.update (Function.update S src rest) dst (b :: S dst)⟩ := by
  have h1 : Function.update S src rest dst = S dst := Function.update_of_ne (Ne.symm hne) _ _
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, moveBit, hS, h1]

def s1 (src a k : J) := BitMachineRawSequence.program (RawRowSplit.readU src a) (moveBit src k)
  () (none : Option Bool) (none : Option Bool)
/-- The split: ONE fixed program for fixed cell names. -/
def program (src a k x : J) := BitMachineRawSequence.program (s1 src a k)
  (RawRowSplit.readU src x) () ((none : Option Bool), (none : Option Bool)) (none : Option Bool)

theorem split_run (src a k x : J) (h1 : src ≠ a) (h2 : src ≠ k) (h3 : src ≠ x)
    (h4 : a ≠ k) (h5 : a ≠ x) (h6 : k ≠ x)
    (va vx : ℕ) (b : Bool) (T : List Bool) (S : J → List Bool)
    (hS : S src = List.replicate va true ++ false :: (b :: (List.replicate vx true ++ false :: T)))
    (ha : S a = []) (hk : S k = []) (hx : S x = []) :
    ∃ t ≤ (va + 1) + 1 + (vx + 1) + 2, ∃ v,
      ((advance (program src a k x))^[t])
        (⟨some (leftLabel (leftLabel ())), (((none : Option Bool), (none : Option Bool)),
          (none : Option Bool)), S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update (Function.update (Function.update (Function.update S src T)
          a (List.replicate va true)) k [b]) x (List.replicate vx true)⟩ := by
  have r1 := RawRowSplit.readU_run src a h1 va (b :: (List.replicate vx true ++ false :: T)) []
    S none hS ha
  rw [List.append_nil] at r1
  let S1 := Function.update (Function.update S src (b :: (List.replicate vx true ++ false :: T)))
    a (List.replicate va true)
  have hS1 : S1 src = b :: (List.replicate vx true ++ false :: T) := by
    simp only [S1]; rw [Function.update_of_ne h1, Function.update_self]
  have r2 := moveBit_run src k h2 S1 none b _ hS1
  have hk1 : S1 k = [] := by
    simp only [S1]; rw [Function.update_of_ne h4.symm, Function.update_of_ne h2.symm, hk]
  rw [hk1] at r2
  let S2 := Function.update (Function.update S1 src (List.replicate vx true ++ false :: T)) k [b]
  have hS2 : S2 src = List.replicate vx true ++ false :: T := by
    simp only [S2]; rw [Function.update_of_ne h2, Function.update_self]
  have hx2 : S2 x = [] := by
    simp only [S2, S1]
    rw [Function.update_of_ne h6.symm, Function.update_of_ne h3.symm,
      Function.update_of_ne h5.symm, Function.update_of_ne h3.symm, hx]
  have r3 := RawRowSplit.readU_run src x h3 vx T [] S2 none hS2 hx2
  rw [List.append_nil] at r3
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (RawRowSplit.readU src a) (moveBit src k)
    () () none (some false) none (some b) _ _ _ _ _ r1 r2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs (s1 src a k) (RawRowSplit.readU src x)
    (leftLabel ()) () ((none : Option Bool), (none : Option Bool)) _ none (some false)
    _ _ _ _ _ q1 r3
  refine ⟨u2, by omega, (((none : Option Bool), (none : Option Bool)), some false), ?_⟩
  refine q2.trans ?_
  congr 1
  -- bank algebra: collapse the repeated updates of `src`
  funext y
  simp only [S2, S1, Function.update_apply]
  by_cases hy1 : y = x
  · subst hy1; simp [h3.symm, h5.symm, h6.symm]
  · by_cases hy2 : y = k
    · subst hy2; simp [hy1, h2.symm, h4.symm]
    · by_cases hy3 : y = a
      · subst hy3; simp [hy1, hy2, h1.symm]
      · by_cases hy4 : y = src
        · subst hy4; simp [hy1, hy2, hy3]
        · simp [hy1, hy2, hy3, hy4]

/-- The actual source raw row after the sum bit: exact encoding. -/
theorem source_word {n p s q₁ q₂ w Q : ℕ} (k : ℕ)
    (i : SourceConstruction.Items s (Fin n))
    (u : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k) :
    (prodCodec (defaultItemCodec n s) (defaultCarrierCodecs n p s q₁ q₂ w Q k).1).encode (i, u) =
      List.replicate i.1.val true ++ false ::
        ((i.2.isRight) :: (List.replicate (Sum.elim (fun v : Fin n => v.val)
          (fun a : Fin (s - 3) => a.val) i.2) true ++ false ::
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode u)) := by
  obtain ⟨a, b⟩ := i
  cases b with
  | inl v => simp [prodCodec, defaultItemCodec, sumCodec, finCodec]
  | inr c => simp [prodCodec, defaultItemCodec, sumCodec, finCodec]

end

#print axioms moveBit_run
#print axioms split_run
#print axioms source_word

end Paper2.SourceSplit
