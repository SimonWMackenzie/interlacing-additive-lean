import CurrentAdditive.V42GeneratedEmbedding
import CurrentAdditive.V42GeneratedIteration

namespace CurrentAdditive.V42GeneratedRank

open Paper2 Paper2.SourceMatrix Paper2.RankLeaves Workspace.Types.CommComplexity
open V42Schedule V39GeneratedConstruction

local instance rankSNZ (k : ℕ) : NeZero (s k) := ⟨(s_pos k).ne'⟩
local instance rankQ₂NZ (k : ℕ) : NeZero (q₂ k (4*k)) := ⟨(q₂_pos k (4*k)).ne'⟩
local instance rankWNZ (k : ℕ) : NeZero (w k) := ⟨(w_pos k).ne'⟩
local instance rankQNZ (k : ℕ) : NeZero (Q k) := ⟨(Q_pos k).ne'⟩

variable {k ni : ℕ} [NeZero (q₁ k)]

theorem numberedStep_rank (hk : 2 ≤ k) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k (4*k)) → Option (Fin (s k)))
    (hI : ni ≤ 2*s k*q₂ k (4*k)) (R : NumberedMatrix) :
    (realMatrix (V42GeneratedConstruction.numberedStep k (4*k) hk μI activity R).entry).rank ≤
      2^(40*k)*(realMatrix R.entry).rank := by
  let src := sourceData (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k)
    (executableCodeD 8192) R.rowLaw R.colLaw
  let st := SourceData.streams (w := w k) (executableCodeD 8192) src (μI := μI)
  let out := SourceData.final (w := w k) (Q := Q k) (executableCodeD 8192) src
  have hs := V42GeneratedConstruction.s_ge_four k hk
  have he : q₁ k+2=s k := by unfold q₁; omega
  have h := V42GeneratedEmbedding.numbered_rank_le src st out R.entry activity hI he
    k (4*k+2*k) (8*k) (24*k) rfl rfl rfl rfl
  simpa only [show k+k+(4*k+2*k)+8*k+24*k=40*k by omega] using h

theorem numberedIterate_rank (hk : 2 ≤ k) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k (4*k)) → Option (Fin (s k)))
    (hI : ni ≤ 2*s k*q₂ k (4*k)) (rounds : ℕ) (R : NumberedMatrix) :
    (realMatrix (V42GeneratedConstruction.numberedIterate k (4*k) hk μI activity rounds R).entry).rank ≤
      2^(rounds*(40*k))*(realMatrix R.entry).rank := by
  induction rounds with
  | zero =>
    simp only [V42GeneratedConstruction.numberedIterate,executableIterate,NumberedMatrix.iterate,
      Nat.rec_zero,Nat.zero_mul,pow_zero,one_mul]
    exact Nat.le_refl _
  | succ rounds ih =>
    have h := numberedStep_rank hk μI activity hI
      (V42GeneratedConstruction.numberedIterate k (4*k) hk μI activity rounds R)
    apply h.trans
    have hmul := Nat.mul_le_mul_left (2^(40*k)) ih
    have he : 2^(40*k)*(2^(rounds*(40*k))*(realMatrix R.entry).rank)=
        2^((rounds+1)*(40*k))*(realMatrix R.entry).rank := by
      rw [←mul_assoc,←pow_add]
      congr 2
      ring
    exact hmul.trans_eq he

theorem storedIterate_rank (hk : 2 ≤ k) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k (4*k)) → Option (Fin (s k)))
    (hI : ni ≤ 2*s k*q₂ k (4*k)) (rounds : ℕ) (R : StoredMatrix) :
    (realMatrix (V42GeneratedConstruction.storedIterate k (4*k) hk μI activity rounds R).entry).rank ≤
      2^(rounds*(40*k))*(realMatrix R.entry).rank := by
  have h := numberedIterate_rank hk μI activity hI rounds R.numbered
  have he := V42GeneratedConstruction.storedIterate_numbered k (4*k) hk μI activity rounds R
  change (realMatrix (V42GeneratedConstruction.storedIterate k (4*k) hk μI activity rounds R).numbered.entry).rank ≤ _
  rw [he]
  exact h

theorem numberedIterate_upper (hk : 2 ≤ k) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k (4*k)) → Option (Fin (s k)))
    (rounds : ℕ) (R : NumberedMatrix) :
    D (V42GeneratedConstruction.numberedIterate k (4*k) hk μI activity rounds R).entry ≤
      D R.entry+rounds*(40*k+1) := by
  induction rounds with
  | zero =>
    simp only [V42GeneratedConstruction.numberedIterate,executableIterate,NumberedMatrix.iterate,
      Nat.rec_zero,Nat.zero_mul,Nat.add_zero]
    exact Nat.le_refl _
  | succ rounds ih =>
    have h := V42GeneratedConstruction.numberedStep_upper k (4*k) hk μI activity
      (V42GeneratedConstruction.numberedIterate k (4*k) hk μI activity rounds R)
    rw [V42GeneratedConstruction.generated_overhead] at h
    apply h.trans
    have hh := Nat.add_le_add_right ih (40*k+1)
    convert hh using 1 <;> ring

theorem item_count (k n : ℕ) (hk : 2 ≤ k) (hn : n ≤ V42PublicSchedule.generatedN k) :
    4*s k*(n+(s k-3)) ≤ 2*s k*q₂ k (4*k) := by
  have hs := V42GeneratedConstruction.s_ge_four k hk
  have hn' : n ≤ (s k)^4 := hn
  have h45 : (s k)^4 ≤ (s k)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h15 : s k ≤ (s k)^5 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ s k) (by decide : 1 ≤ 5)
  have hq : q₂ k (4*k)=(s k)^6 := (V42PublicSchedule.generated_recipe k).1
  have hlast : 4*(s k)^5 ≤ (s k)^6 := by
    calc 4*(s k)^5 ≤ s k*(s k)^5 := Nat.mul_le_mul_right _ hs
         _ = (s k)^6 := by ring
  have hkey : 2*(n+(s k-3)) ≤ q₂ k (4*k) := by rw [hq]; omega
  have h := Nat.mul_le_mul_left (2*s k) hkey
  nlinarith only [h]

omit [NeZero (q₁ k)] in
theorem graphRun_rank {n m rep : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (hnN : n ≤ V42PublicSchedule.generatedN k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (rounds : ℕ) :
    (realMatrix (V42GeneratedConstruction.graphRun k (4*k) hk hn hwidth edge (4*k) rounds).entry).rank ≤
      2^(V42GeneratedNo.generatedB k rounds-1) := by
  have hs := V42GeneratedConstruction.s_ge_four k hk
  letI : NeZero (q₁ k) := ⟨by unfold q₁; omega⟩
  have h := storedIterate_rank hk (LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn)
    (graphActivity (by omega) hwidth edge) (item_count k n hk hnN) rounds (storedLookupSeed (4*k))
  have hseed : (realMatrix (storedLookupSeed (4*k)).entry).rank ≤ LookupSeed.width (4*k) := by
    simpa only [Fintype.card_fin] using
      (realMatrix (storedLookupSeed (4*k)).entry).rank_le_card_width
  have he : 2^(rounds*(40*k))*LookupSeed.width (4*k)=2^(V42GeneratedNo.generatedB k rounds-1) := by
    rw [LookupSeed.width,←pow_add]
    congr 1
    unfold V42GeneratedNo.generatedB
    omega
  exact (h.trans (Nat.mul_le_mul_left _ hseed)).trans_eq he

#print axioms numberedStep_rank
#print axioms storedIterate_rank
#print axioms graphRun_rank
#print axioms numberedIterate_upper

end CurrentAdditive.V42GeneratedRank

