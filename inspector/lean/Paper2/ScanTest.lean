import Paper2.ScanSelect
import Paper2.ScanCoordDecode

/-! Unit 3, segment (1): ONE fixed program for the coordinate decoding, group
test and padding test of `SourceActiveRank.scanAtCanonical`, and its value
identity with the production scan (through `ScanCoordDecode`).

`testProg` = `ScanDecodeMachine.program` ; `ScanSelect.prog` (production
`BitMachineRawSequence.program`, charged handoff). From unary outer
coordinate `a`, unary `r` (repetition), unary `m` (edge count) and unary item
group `ig`, it halts with exact bank `DT`: answer bit
`decide (0 < m ∧ a / r / 3 / m = ig)` in cell 13, the decoded edge index
`a / r / 3 % m` in cell 8 and the label index `a / r % 3` in cell 5.

`scan_test`: the bit is `false` exactly when the canonical scan is forced to
`none` (other group, padding, or `m = 0`); when it is `true`, the scan equals
the production endpoint-rank semantics at the decoded edge occurrence and
label. The endpoint-rank controller run itself, the endpoint fetch from the
public graph bytes, the operand words and the dispatch on the label/item kind
are NOT part of this program. -/

namespace Paper2.ScanTest

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open Paper2.ScanDecodeMachine (K u D0 DF decodeBound startCtl)
open SourceItems SourceActiveRank CanonicalSourceLabels
open CanonicalEndpointRankBridge CanonicalEndpointRankMachine

def testProg := BitMachineRawSequence.program ScanDecodeMachine.program ScanSelect.prog
  .peek startCtl ((none : Option Bool), (none : Option Bool))

/-- Exit bank of the test. -/
def DT (a r m ig : ℕ) : K → List Bool :=
  ![[], u r, u m, u 3, [], u (a / r % 3), [], [], u (a / r / 3 % m), [], [], u (a % r), [],
    [decide (0 < m ∧ a / r / 3 / m = ig)]]

theorem F_DF (a r m ig : ℕ) (b : Bool) :
    ScanSelect.F (DF a r m ig) b =
      ![[], u r, u m, u 3, [], u (a / r % 3), [], [], u (a / r / 3 % m), [], [], u (a % r), [],
        [b]] := by
  funext x
  fin_cases x <;> rfl

theorem test_run (a r m ig : ℕ) :
    ∃ t ≤ decodeBound a r m + (a / r / 3 / m + ig + 4) + 1, ∃ c,
      ((advance testProg)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel (leftLabel ())))),
          (startCtl, ((none : Option Bool), (none : Option Bool))), D0 a r m ig⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, c, DT a r m ig⟩ := by
  obtain ⟨t1, ht1, h1⟩ := ScanDecodeMachine.decode_run a r m ig
  obtain ⟨t2, ht2, c2, h2⟩ := ScanSelect.select_run (a / r / 3 / m) ig m (DF a r m ig)
    ((none : Option Bool), (none : Option Bool)) rfl rfl rfl
  rw [F_DF] at h2
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs ScanDecodeMachine.program ScanSelect.prog
    (leftLabel (leftLabel (leftLabel ()))) .peek startCtl startCtl
    ((none : Option Bool), (none : Option Bool)) c2 (D0 a r m ig) (DF a r m ig) _ t1 t2 h1 h2
  exact ⟨t, by omega, _, h⟩

/-- Value identity: the physical answer bit decides exactly the `none` cases
of the canonical scan, and in the selected case the scan is the production
endpoint-rank semantics at the decoded occurrence `a / r / 3 % m` and label
`a / r % 3`. -/
theorem scan_test {s n m r q₂ : ℕ} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * r)
    (ig : Fin (4 * s)) (z : Fin n ⊕ Fin (s - 3)) (a : Fin q₂) :
    (DT a.val r m ig.val 13 = [false] →
      scanAtCanonical edge hs hq (ig, z) a = none) ∧
    (∀ hm : 0 < m, DT a.val r m ig.val 13 = [true] →
      Option.map Fin.val (scanAtCanonical edge hs hq (ig, z) a) =
        let e : Fin m := ⟨a.val / r / 3 % m, Nat.mod_lt _ hm⟩
        let tag := optionBoolIndex.symm ⟨a.val / r % 3, Nat.mod_lt _ (by norm_num)⟩
        if semanticActive (kindOfTag tag) (itemKindOf z)
            (edge e false).val (edge e true).val (itemValue z) then
          some (semanticRank (kindOfTag tag) (itemKindOf z)
            (edge e false).val (edge e true).val (itemValue z))
        else none) := by
  constructor
  · intro h
    apply ScanCoordDecode.scan_none edge hs hq ig z a
    intro hsel
    have : DT a.val r m ig.val 13 = [true] := by
      simp only [DT]
      show [decide (0 < m ∧ a.val / r / 3 / m = ig.val)] = [true]
      simp [hsel]
    rw [this] at h
    simp at h
  · intro hm h
    have hsel : a.val / r / 3 / m = ig.val := by
      have h' : [decide (0 < m ∧ a.val / r / 3 / m = ig.val)] = [true] := h
      simp at h'
      exact h'.2
    exact ScanCoordDecode.scan_selected edge hs hq ig z a _ _ hsel rfl (by simp)

#print axioms test_run
#print axioms scan_test

end

end Paper2.ScanTest
