import EthInapproximability.CurrentPaper.ClockH

/-! Lane owner:b-weighted-level-11, unit 2, segment 4b-ii-6 (second piece): every field of the
admitted entry input `MatrixWeightedEntrySemantic.actualInput` is bounded by the two protected
carrier counts `PC = |ProtectedColumns a s q (Fin cy)|` and `PR = |ProtectedRows s L nv nb (Fin rx)|`
(`inputScale_le`), provided both are positive. -/

namespace EthInapproximability.CurrentPaper.ClockI

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Construction MatrixStage4Codes MatrixStage4Digits WeightedDuplication ClockH

noncomputable section

theorem fields_len (K : ℕ) : ∀ rs : List ℕ, (∀ r ∈ rs, r < K) →
    (MatrixWeightedRowOrderLookup.fields rs).length ≤ rs.length * K
  | [], _ => by simp [MatrixWeightedRowOrderLookup.fields]
  | r :: rs, h => by
    have ih := fields_len K rs (fun x hx => h x (by simp [hx]))
    have hr := h r (by simp)
    have e1 : MatrixWeightedRowOrderLookup.fields (r :: rs) =
        EncodedGraph.unary r ++ MatrixWeightedRowOrderLookup.fields rs := by
      simp [MatrixWeightedRowOrderLookup.fields]
    have e2 : (EncodedGraph.unary r).length = r + 1 := by simp [EncodedGraph.unary]
    rw [e1, List.length_append, e2, List.length_cons, Nat.succ_mul]
    omega

theorem orderWord_len {nv nb : ℕ} (order : ItemOrder nv nb) :
    (MatrixWeightedRowOrderLookup.orderWord order).length ≤ (nv + nb) * (nv + nb) := by
  unfold MatrixWeightedRowOrderLookup.orderWord
  have h := fields_len (nv + nb) (List.ofFn fun j : Fin (nv + nb) => (order j).val) (by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨j, rfl⟩ := hr
    exact (order j).isLt)
  simpa using h

theorem card_secondRows (a s q cy : ℕ) :
    Fintype.card (SecondRows a s q (Fin cy)) = binBase a s q cy := by
  simp [SecondRows, FirstColumns, binBase, wordBase]

theorem card_rawColumns (a s q cy : ℕ) :
    Fintype.card (RawColumns a s q (Fin cy)) = cols a s q cy := by
  simp [RawColumns, ThirdColumns, SecondRows, FirstColumns, cols]

theorem uniform_eq (a s q cy : ℕ) :
    uniformCopies (Y := Fin cy) a s q = binBase a s q cy ^ s := by
  unfold uniformCopies; rw [card_secondRows]

theorem card_PC (a s q cy : ℕ) :
    Fintype.card (ProtectedColumns a s q (Fin cy)) =
      184 * cols a s q cy * binBase a s q cy * binBase a s q cy ^ s := by
  rw [show Fintype.card (ProtectedColumns a s q (Fin cy)) =
      184 * Fintype.card (RawColumns a s q (Fin cy)) * Fintype.card (SecondRows a s q (Fin cy)) *
        uniformCopies (Y := Fin cy) a s q from card_columns _ _ _]
  rw [card_rawColumns, card_secondRows, uniform_eq]

theorem card_rawRows (s L nv nb rx : ℕ) :
    Fintype.card (RawRows s L nv nb (Fin rx)) = s * L + (nv * rx + nb * rx) := by
  simp [RawRows, ThirdRows, VertexRows, AuxiliaryRows]

theorem card_template (s L : ℕ) : Fintype.card (TemplateSupport.{0} s L) = s * L := by
  simp [TemplateSupport, ThirdRows]

theorem card_vertexRows (nv rx : ℕ) : Fintype.card (VertexRows nv (Fin rx)) = nv * rx := by
  simp [VertexRows]

theorem card_auxRows (nb rx : ℕ) : Fintype.card (AuxiliaryRows nb (Fin rx)) = nb * rx := by
  simp [AuxiliaryRows]

theorem card_PR (s L nv nb rx : ℕ) :
    Fintype.card (ProtectedRows s L nv nb (Fin rx)) =
      2 ^ 22 * (s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx) := by
  rw [show Fintype.card (ProtectedRows s L nv nb (Fin rx)) =
      2 ^ 22 * Fintype.card (RawRows s L nv nb (Fin rx)) * Fintype.card (TemplateSupport.{0} s L) *
        Fintype.card (VertexRows nv (Fin rx)) * Fintype.card (AuxiliaryRows nb (Fin rx)) from card_rows _ _ _ _]
  rw [card_rawRows, card_template, card_vertexRows, card_auxRows]

theorem pos_factors {A B C D : ℕ} (h : 0 < A * B * C * D) : 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D := by
  refine ⟨Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_⟩ <;>
    intro h0 <;> simp [h0] at h

theorem le_prod4_left {A B C D : ℕ} (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) : A ≤ A * B * C * D := by
  have h1 : A ≤ A * B := Nat.le_mul_of_pos_right _ hB
  have h2 : A * B ≤ A * B * C := Nat.le_mul_of_pos_right _ hC
  have h3 : A * B * C ≤ A * B * C * D := Nat.le_mul_of_pos_right _ hD
  omega

variable {rx cy : ℕ}

theorem inputScale_le (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool) (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (x y : ℕ)
    (hPC : 0 < Fintype.card (ProtectedColumns a s q (Fin cy)))
    (hPR : 0 < Fintype.card (ProtectedRows s L nv nb (Fin rx))) :
    MatrixWeightedEntryEnvelope.inputScale
        (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order vectors cap) x y ≤
      1 + x + y + 8 * Fintype.card (ProtectedColumns a s q (Fin cy)) +
        12 * Fintype.card (ProtectedRows s L nv nb (Fin rx)) +
        Fintype.card (ProtectedColumns a s q (Fin cy)) *
          Fintype.card (ProtectedRows s L nv nb (Fin rx)) +
        Fintype.card (ProtectedRows s L nv nb (Fin rx)) *
          Fintype.card (ProtectedRows s L nv nb (Fin rx)) := by
  set d := MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs family order vectors cap with hd
  set PC := Fintype.card (ProtectedColumns a s q (Fin cy)) with hPCd
  set PR := Fintype.card (ProtectedRows s L nv nb (Fin rx)) with hPRd
  -- column side
  have hPCe : PC = 184 * cols a s q cy * binBase a s q cy * binBase a s q cy ^ s := card_PC a s q cy
  have hpc := hPC
  rw [hPCe] at hpc
  obtain ⟨-, hcols, hbin, hbinS⟩ := pos_factors hpc
  have hcolsPC : cols a s q cy ≤ PC := by
    rw [hPCe]
    have := le_prod4_left (A := cols a s q cy) (B := binBase a s q cy) (C := binBase a s q cy ^ s)
      (D := 1) hbin hbinS Nat.one_pos
    calc cols a s q cy ≤ cols a s q cy * binBase a s q cy * binBase a s q cy ^ s * 1 := this
      _ ≤ 184 * cols a s q cy * binBase a s q cy * binBase a s q cy ^ s := by
        rw [Nat.mul_one]
        have h184 : cols a s q cy * binBase a s q cy * binBase a s q cy ^ s ≤
            184 * (cols a s q cy * binBase a s q cy * binBase a s q cy ^ s) := Nat.le_mul_of_pos_left _ (by norm_num)
        calc _ ≤ _ := h184
          _ = _ := by ring
  have hbinPC : 182 * binBase a s q cy ≤ PC := by
    rw [hPCe]
    have h1 : 1 ≤ cols a s q cy * binBase a s q cy ^ s := Nat.mul_pos hcols hbinS
    have e : 184 * cols a s q cy * binBase a s q cy * binBase a s q cy ^ s =
        184 * binBase a s q cy * (cols a s q cy * binBase a s q cy ^ s) := by ring
    rw [e]
    have := Nat.mul_le_mul_left (184 * binBase a s q cy) h1
    omega
  have hfullB : cols a s q cy * (182 * binBase a s q cy) ≤ PC := by
    rw [hPCe]
    have h1 : cols a s q cy * (182 * binBase a s q cy) ≤
        cols a s q cy * (182 * binBase a s q cy) * binBase a s q cy ^ s := Nat.le_mul_of_pos_right _ hbinS
    have e : 184 * cols a s q cy * binBase a s q cy * binBase a s q cy ^ s =
        cols a s q cy * (182 * binBase a s q cy) * binBase a s q cy ^ s +
          2 * (cols a s q cy * binBase a s q cy * binBase a s q cy ^ s) := by ring
    omega
  have hunif : binBase a s q cy ^ s ≤ PC := by
    rw [hPCe]
    have h1 : 1 ≤ 184 * cols a s q cy * binBase a s q cy := by
      have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 184) hcols) hbin
      omega
    have := Nat.mul_le_mul_right (binBase a s q cy ^ s) h1
    omega
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · simp [binBase, h0] at hbin
    · exact h0
  have hword : wordBase a s cy ≤ binBase a s q cy := by
    unfold binBase; exact Nat.le_mul_of_pos_left _ hq
  have hcy : cy ≤ cols a s q cy := by
    have hpow : 0 < cy ^ (s + 1) := by
      rcases Nat.eq_zero_or_pos (cy ^ (s + 1)) with h0 | h0
      · simp [cols, h0] at hcols
      · exact h0
    have hcy0 : 0 < cy := by
      rcases Nat.eq_zero_or_pos cy with h0 | h0
      · simp [h0] at hpow
      · exact h0
    have h1 : cy ≤ cy ^ (s + 1) := by
      calc cy = cy ^ 1 := (pow_one cy).symm
        _ ≤ cy ^ (s + 1) := Nat.pow_le_pow_right hcy0 (by omega)
    have h2 : cy ^ (s + 1) ≤ cols a s q cy := by
      unfold cols
      have hb : 0 < (q * cy ^ firstLength a s) ^ s := by
        have := hbinS; simpa [binBase, wordBase] using this
      exact Nat.le_mul_of_pos_right _ hb
    omega
  -- row side
  have hPRe : PR = 2 ^ 22 * (s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx) :=
    card_PR s L nv nb rx
  have hpr := hPR
  rw [hPRe] at hpr
  have hpr4 : 0 < (s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx) := by
    have e : 2 ^ 22 * (s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx) =
        2 ^ 22 * ((s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx)) := by ring
    rw [e] at hpr
    exact Nat.pos_of_mul_pos_left hpr
  obtain ⟨hX, hT, hV, hB⟩ := pos_factors hpr4
  have hP4 : (s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx) ≤ PR := by
    rw [hPRe]
    have e : 2 ^ 22 * (s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx) =
        2 ^ 22 * ((s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx)) := by ring
    rw [e]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  have hXle : s * L + (nv * rx + nb * rx) ≤ PR := le_trans (le_prod4_left hT hV hB) hP4
  have hTle : s * L ≤ PR := by
    have : (s * L + (nv * rx + nb * rx)) * (s * L) * (nv * rx) * (nb * rx) =
        (s * L) * (s * L + (nv * rx + nb * rx)) * (nv * rx) * (nb * rx) := by ring
    exact le_trans (le_prod4_left hX hV hB) (this ▸ hP4)
  have hVle : nv * rx ≤ s * L + (nv * rx + nb * rx) := by omega
  have hBle : nb * rx ≤ s * L + (nv * rx + nb * rx) := by omega
  have hrx : 0 < rx := by
    rcases Nat.eq_zero_or_pos rx with h0 | h0
    · simp [h0] at hV
    · exact h0
  have hnv : nv ≤ nv * rx := Nat.le_mul_of_pos_right _ hrx
  have hnb : nb ≤ nb * rx := Nat.le_mul_of_pos_right _ hrx
  have hnvpos : 0 < nv := by
    rcases Nat.eq_zero_or_pos nv with h0 | h0
    · simp [h0] at hV
    · exact h0
  have hrxle : rx ≤ nv * rx := Nat.le_mul_of_pos_left _ hnvpos
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · simp [h0] at hT
    · exact h0
  have hsle : s ≤ s * L := Nat.le_mul_of_pos_right _ hLpos
  have hrow4 : 0 < Fintype.card (RawRows s L nv nb (Fin rx)) * Fintype.card (TemplateSupport.{0} s L) *
      Fintype.card (VertexRows nv (Fin rx)) * Fintype.card (AuxiliaryRows nb (Fin rx)) := by
    rw [card_rawRows, card_template, card_vertexRows, card_auxRows]; exact hpr4
  have hbd (i : Fin 4) :
      Fintype.card (rowSupport (RawRows s L nv nb (Fin rx)) (TemplateSupport.{0} s L)
          (VertexRows nv (Fin rx)) (AuxiliaryRows nb (Fin rx)) i) *
        copies (rowSupport (RawRows s L nv nb (Fin rx)) (TemplateSupport.{0} s L)
          (VertexRows nv (Fin rx)) (AuxiliaryRows nb (Fin rx))) rowWeight i ≤ PR :=
    boundary_le _ _ _ _ i
  have hdv (i : Fin 4) :
      copies (rowSupport (RawRows s L nv nb (Fin rx)) (TemplateSupport.{0} s L)
          (VertexRows nv (Fin rx)) (AuxiliaryRows nb (Fin rx))) rowWeight i ≤ PR :=
    divisor_le _ _ _ _ hrow4 i
  have hc0 := card_rowSupport (RawRows s L nv nb (Fin rx)) (TemplateSupport.{0} s L)
    (VertexRows nv (Fin rx)) (AuxiliaryRows nb (Fin rx)) 0
  have hc1 := card_rowSupport (RawRows s L nv nb (Fin rx)) (TemplateSupport.{0} s L)
    (VertexRows nv (Fin rx)) (AuxiliaryRows nb (Fin rx)) 1
  have hc2 := card_rowSupport (RawRows s L nv nb (Fin rx)) (TemplateSupport.{0} s L)
    (VertexRows nv (Fin rx)) (AuxiliaryRows nb (Fin rx)) 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hc0 hc1 hc2
  have hb0 := hbd 0
  have hb1 := hbd 1
  have hb2 := hbd 2
  rw [hc0] at hb0
  rw [hc1] at hb1
  rw [hc2] at hb2
  -- the fields
  have f_unif : d.uniform ≤ PC := by
    show uniformCopies (Y := Fin cy) a s q ≤ PC
    rw [uniform_eq]; exact hunif
  have f_fullB : d.fullBoundary ≤ PC := by
    show Fintype.card (RawColumns a s q (Fin cy)) * (182 * Fintype.card (SecondRows a s q (Fin cy))) ≤ PC
    rw [card_rawColumns, card_secondRows]; exact hfullB
  have f_fullD : d.fullDivisor ≤ PC := by
    show 182 * Fintype.card (SecondRows a s q (Fin cy)) ≤ PC
    rw [card_secondRows]; exact hbinPC
  have f_diagD : d.diagonalDivisor ≤ PC := by
    show 2 * Fintype.card (RawColumns a s q (Fin cy)) ≤ PC
    rw [card_rawColumns]
    have h1 : cols a s q cy ≤ cols a s q cy * binBase a s q cy := Nat.le_mul_of_pos_right _ hbin
    have e : cols a s q cy * (182 * binBase a s q cy) = 182 * (cols a s q cy * binBase a s q cy) := by ring
    have := hfullB
    omega
  have f_nb : d.nb ≤ PR := by show nb ≤ PR; omega
  have f_spr : d.stagePrefixRows ≤ PR := by show s * L ≤ PR; exact hTle
  have f_rx : d.rx ≤ PR := by show rx ≤ PR; omega
  have f_nv : d.nv ≤ PR := by show nv ≤ PR; omega
  have f_rw : d.rawWidth ≤ PC := by show cols a s q cy ≤ PC; exact hcolsPC
  have f_wb : d.wordBase ≤ PC := by
    show wordBase a s cy ≤ PC
    omega
  have f_cy : d.cy ≤ PC := by show cy ≤ PC; omega
  have f_s : d.s ≤ PR := by show s ≤ PR; omega
  have f_bb : d.binBase ≤ PC := by show binBase a s q cy ≤ PC; omega
  have f_rb1 : d.rowBoundary₁ ≤ PR := hb0
  have f_rb2 : d.rowBoundary₂ ≤ PR := hb1
  have f_rb3 : d.rowBoundary₃ ≤ PR := hb2
  have f_rd0 : d.rowDivisor₀ ≤ PR := hdv 0
  have f_rd1 : d.rowDivisor₁ ≤ PR := hdv 1
  have f_rd2 : d.rowDivisor₂ ≤ PR := hdv 2
  have f_rd3 : d.rowDivisor₃ ≤ PR := hdv 3
  have f_raw : d.rawBits.length ≤ PC * PR := by
    show (rawTable R a s q L nv nb hs family order vectors cap).length ≤ PC * PR
    rw [rawTable_length]
    have e : rows s L nv nb rx = s * L + (nv * rx + nb * rx) := by unfold rows; ring
    rw [e, Nat.mul_comm PC PR]
    exact Nat.mul_le_mul hXle hcolsPC
  have f_ord : d.orderBits.length ≤ PR * PR := by
    show (MatrixWeightedRowOrderLookup.orderWord order).length ≤ PR * PR
    have h1 := orderWord_len order
    have h2 : nv + nb ≤ PR := by omega
    exact le_trans h1 (Nat.mul_le_mul h2 h2)
  unfold MatrixWeightedEntryEnvelope.inputScale
  omega

#print axioms inputScale_le

end
end EthInapproximability.CurrentPaper.ClockI
