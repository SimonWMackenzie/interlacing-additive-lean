import CurrentAdditive.IndexedCodeDSelectedRecord

/-! A second physical indexed V2 getter reads one symbol code from the
word field of the selected canonical Code D record. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext

def codeDWordIndex {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q) : Fin (canonicalEntry out[j]).word.length :=
  p.cast (canonicalEntry_length out[j]).symm

theorem codeDWord_get {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q) :
    (canonicalEntry out[j]).word[codeDWordIndex out j p] =
      (out[j].1 p).bits := by
  simp [codeDWordIndex, canonicalEntry]

theorem codeDWord_split {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q) :
    (canonicalEntry out[j]).word =
      (canonicalEntry out[j]).word.take p.val ++
        (out[j].1 p).bits ::
          (canonicalEntry out[j]).word.drop (p.val + 1) := by
  let k := codeDWordIndex out j p
  have hk : k.val < (canonicalEntry out[j]).word.length := k.isLt
  have h := List.take_append_drop k.val (canonicalEntry out[j]).word
  rw [List.drop_eq_getElem_cons hk] at h
  calc
    (canonicalEntry out[j]).word =
        (canonicalEntry out[j]).word.take p.val ++
          (canonicalEntry out[j]).word[codeDWordIndex out j p] ::
            (canonicalEntry out[j]).word.drop (p.val + 1) := by
              simpa only [k, codeDWordIndex] using h.symm
    _ = _ := by rw [codeDWord_get]

theorem indexed_codeD_coordinate_getter_run {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q) :
    let pre := (canonicalEntry out[j]).word.take p.val
    let word := (out[j].1 p).bits
    let suffix := (canonicalEntry out[j]).word.drop (p.val + 1)
    let source := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
    ∃ t ≤ 2 * source.length + 5 +
        (4 * (pre ++ word :: suffix).length.bits.length + 6 +
          IndexedFieldProgram.fieldCost (pre ++ [word])),
      PreservingV2Program.run t (PreservingV2Program.initial source p.val) =
        ⟨none,
         PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none)),
         ![SourceListEncoding.fields suffix, [], [], [], [],
           List.replicate word.length true, word, [], source, []]⟩ := by
  dsimp only
  let pre := (canonicalEntry out[j]).word.take p.val
  let word := (out[j].1 p).bits
  let suffix := (canonicalEntry out[j]).word.drop (p.val + 1)
  have hsplit : (canonicalEntry out[j]).word = pre ++ word :: suffix :=
    codeDWord_split out j p
  have hpre : pre.length = p.val := by
    simp [pre, canonicalEntry_length]
  have henc : CodeDCodecV2.encodeItems (canonicalEntry out[j]).word =
      SourceListEncoding.encode (pre ++ word :: suffix) := by
    change SourceListEncoding.encode (canonicalEntry out[j]).word =
      SourceListEncoding.encode (pre ++ word :: suffix)
    rw [hsplit]
  have hrun := PreservingV2Program.select_preserving pre word suffix
  simpa only [hpre, ← henc] using hrun

#print axioms codeDWord_get
#print axioms indexed_codeD_coordinate_getter_run

end CurrentAdditive.IndexedExecutableStepRecovery
