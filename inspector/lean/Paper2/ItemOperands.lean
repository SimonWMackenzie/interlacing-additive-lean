import Paper2.SourceSplit
import Paper2.CanonicalEndpointRankBridge

/-! Unit 3, segment (1): the source item's operands for the physical scan,
from the actual source raw-row word after its sum bit.

ONE fixed program: one charged push of the terminator `false` on cell `x`,
then the production `SourceSplit.program` (reused by name). From
`src = unary i.1 ++ false :: kind :: unary value ++ false :: T` it leaves the
unary item group in `a` (the `ig` operand of `ScanSelect`), the item-kind bit
in `k` (the `RankRun` kind cell), the terminated item value
`unaryWord value` in `x` (the `RankRun` operand) and `T` in `src`.
`item_operands` instantiates `T` with the level row word through the
production `SourceSplit.source_word`. Generic in the ambient bank. -/

namespace Paper2.ItemOperands

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open RecursiveLabelCodecScratch RecursiveEntries

variable {J : Type*} [DecidableEq J]

def pushF (x : J) : Unit → TM2.Stmt (fun _ : J => Bool) Unit (Option Bool) :=
  fun _ => push x (fun _ => false) halt

def program (src a k x : J) := BitMachineRawSequence.program (pushF x)
  (SourceSplit.program src a k x) (leftLabel (leftLabel ())) (none : Option Bool)
  (((none : Option Bool), (none : Option Bool)), (none : Option Bool))

theorem split_run' (src a k x : J) (h1 : src ≠ a) (h2 : src ≠ k) (h3 : src ≠ x)
    (h4 : a ≠ k) (h5 : a ≠ x) (h6 : k ≠ x)
    (va vx : ℕ) (b : Bool) (T : List Bool) (S : J → List Bool)
    (hS : S src = List.replicate va true ++ false :: (b :: (List.replicate vx true ++ false :: T)))
    (ha : S a = []) (hk : S k = []) (hx : S x = []) :
    ∃ t ≤ 1 + ((va + 1) + 1 + (vx + 1) + 2) + 1, ∃ v,
      ((advance (program src a k x))^[t])
        (⟨some (leftLabel ()), ((none : Option Bool), (((none : Option Bool),
          (none : Option Bool)), (none : Option Bool))), S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update (Function.update (Function.update (Function.update S src T)
          a (List.replicate va true)) k [b]) x (CanonicalEndpointRankMachine.unaryWord vx)⟩ := by
  have r0 : ((advance (pushF x))^[1]) (⟨some (), (none : Option Bool), S⟩ :
      TM2.Cfg (fun _ : J => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update S x (false :: S x)⟩ := rfl
  rw [hx] at r0
  let S0 := Function.update S x [false]
  have r1 := RawRowSplit.readU_run src a h1 va (b :: (List.replicate vx true ++ false :: T)) []
    S0 none (by simp only [S0]; rw [Function.update_of_ne h3, hS])
    (by simp only [S0]; rw [Function.update_of_ne h5, ha])
  rw [List.append_nil] at r1
  let S1 := Function.update (Function.update S0 src (b :: (List.replicate vx true ++ false :: T)))
    a (List.replicate va true)
  have hS1 : S1 src = b :: (List.replicate vx true ++ false :: T) := by
    simp only [S1]; rw [Function.update_of_ne h1, Function.update_self]
  have r2 := SourceSplit.moveBit_run src k h2 S1 none b _ hS1
  have hk1 : S1 k = [] := by
    simp only [S1, S0]
    rw [Function.update_of_ne h4.symm, Function.update_of_ne h2.symm, Function.update_of_ne h6, hk]
  rw [hk1] at r2
  let S2 := Function.update (Function.update S1 src (List.replicate vx true ++ false :: T)) k [b]
  have hS2 : S2 src = List.replicate vx true ++ false :: T := by
    simp only [S2]; rw [Function.update_of_ne h2, Function.update_self]
  have hx2 : S2 x = [false] := by
    simp only [S2, S1, S0]
    rw [Function.update_of_ne h6.symm, Function.update_of_ne h3.symm,
      Function.update_of_ne h5.symm, Function.update_of_ne h3.symm, Function.update_self]
  have r3 := RawRowSplit.readU_run src x h3 vx T [false] S2 none hS2 hx2
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (RawRowSplit.readU src a)
    (SourceSplit.moveBit src k) () () none (some false) none (some b) _ _ _ _ _ r1 r2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs (SourceSplit.s1 src a k)
    (RawRowSplit.readU src x) (leftLabel ()) () ((none : Option Bool), (none : Option Bool)) _
    none (some false) _ _ _ _ _ q1 r3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs (pushF x) (SourceSplit.program src a k x)
    () (leftLabel (leftLabel ())) none none
    (((none : Option Bool), (none : Option Bool)), (none : Option Bool))
    (((none : Option Bool), (none : Option Bool)), some false) S S0 _ 1 u2 r0 q2
  refine ⟨u3, by omega, ((none : Option Bool), (((none : Option Bool), (none : Option Bool)),
    some false)), q3.trans ?_⟩
  congr 1
  funext y
  simp only [S2, S1, S0, Function.update_apply]
  by_cases hy1 : y = x
  · subst hy1; simp [h3.symm, h5.symm, h6.symm, CanonicalEndpointRankMachine.unaryWord]
  · by_cases hy2 : y = k
    · subst hy2; simp [hy1, h2.symm, h4.symm]
    · by_cases hy3 : y = a
      · subst hy3; simp [hy1, hy2, h1.symm]
      · by_cases hy4 : y = src
        · subst hy4; simp [hy1, hy2, hy3]
        · simp [hy1, hy2, hy3, hy4]

/-- On the actual source raw-row word (production `SourceSplit.source_word`):
unary group, kind bit `i.2.isRight`, terminated item value, and the encoded
row half `u` left in `src`. -/
theorem item_operands {n p s q₁ q₂ w Q : ℕ} (k : ℕ)
    (i : SourceConstruction.Items s (Fin n))
    (u : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)
    (src a kc x : J) (h1 : src ≠ a) (h2 : src ≠ kc) (h3 : src ≠ x)
    (h4 : a ≠ kc) (h5 : a ≠ x) (h6 : kc ≠ x) (S : J → List Bool)
    (hS : S src = (prodCodec (defaultItemCodec n s)
      (defaultCarrierCodecs n p s q₁ q₂ w Q k).1).encode (i, u))
    (ha : S a = []) (hk : S kc = []) (hx : S x = []) :
    ∃ t ≤ 1 + ((i.1.val + 1) + 1 + (CanonicalEndpointRankBridge.itemValue i.2 + 1) + 2) + 1, ∃ v,
      ((advance (program src a kc x))^[t])
        (⟨some (leftLabel ()), ((none : Option Bool), (((none : Option Bool),
          (none : Option Bool)), (none : Option Bool))), S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, Function.update (Function.update (Function.update (Function.update S src
          ((defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode u))
          a (List.replicate i.1.val true)) kc [i.2.isRight]) x
          (CanonicalEndpointRankMachine.unaryWord (CanonicalEndpointRankBridge.itemValue i.2))⟩ := by
  have hw := SourceSplit.source_word (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w)
    (Q := Q) k i u
  have hval : Sum.elim (fun v : Fin n => v.val) (fun a : Fin (s - 3) => a.val) i.2 =
      CanonicalEndpointRankBridge.itemValue i.2 := by
    cases i.2 <;> rfl
  rw [hw, hval] at hS
  exact split_run' src a kc x h1 h2 h3 h4 h5 h6 i.1.val _ i.2.isRight _ S hS ha hk hx

#print axioms split_run'
#print axioms item_operands

end

end Paper2.ItemOperands
