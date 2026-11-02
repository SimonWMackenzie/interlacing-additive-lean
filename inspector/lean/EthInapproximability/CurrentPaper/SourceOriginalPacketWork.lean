import EthInapproximability.CurrentPaper.SourceOriginalPacketWriter

/-! Summed literal work of the original-n packet writer over sparse branches. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalPacketWork

def work (n : ℕ) (words : List (List Bool)) : ℕ :=
  (words.map fun word => 4*n+3*word.length+6).sum

theorem work_le_count (n L : ℕ) (words : List (List Bool))
    (h : ∀ word ∈ words, word.length ≤ L) :
    work n words ≤ words.length * (4*n+3*L+6) := by
  induction words with
  | nil => simp [work]
  | cons word words ih =>
      have hw := h word (by simp)
      have htail : ∀ x ∈ words, x.length ≤ L := by
        intro x hx
        exact h x (by simp [hx])
      have ht := ih htail
      simp only [work, List.map_cons, List.sum_cons, List.length_cons] at *
      calc
        4*n+3*word.length+6 + (words.map fun x => 4*n+3*x.length+6).sum ≤
            (4*n+3*L+6) + words.length*(4*n+3*L+6) := by
              apply Nat.add_le_add
              · omega
              · exact ht
        _ = (words.length+1)*(4*n+3*L+6) := by ring

def sparseWork {η : ℚ} (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) : ℕ :=
  work f.val.variables
    ((S.branches f).map fun g => EncodedCNF.encode g.val)

/-- Original n occurs linearly once in each physical per-branch run. The
possibly exponential branch count is one outer multiplier, not a polynomial
argument. -/
theorem sparseWork_le_count {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) (hn : 1 ≤ f.val.variables) :
    sparseWork S f ≤ (S.branches f).length *
      (4*f.val.variables +
        3*((8*S.density+3)*f.val.variables*(f.val.variables.size+1))+6) := by
  unfold sparseWork
  have h := work_le_count f.val.variables
    ((8*S.density+3)*f.val.variables*(f.val.variables.size+1))
    ((S.branches f).map fun g => EncodedCNF.encode g.val) ?_
  · simpa only [List.length_map] using h
  · intro word hw
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hw
    exact S.branch_encoded_length f hn g hg

end EthInapproximability.CurrentPaper.SourceOriginalPacketWork
