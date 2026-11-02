import Paper2.YaoT26Draft

/-! Unit 5 segment Y12-size (lane a-yao-clone-owner-1): the size and time
bounds of the composed Yao source in the lock's form (lock v12 Y:77-90
`yao:source`: "a deterministic polynomial-time reduction ... The polynomial
depends on t"; YA:92-116 `yao:clones`: "Each vertex gives KS clones; each edge
gives at most (KS)^K edges").

* `cloneTime_le`: the public clock of the physical clone machine is at most
  `cloneConst K M * (|input code| + 1)^2`, with `M^K` kept symbolic (never
  evaluated; at `t = 4` it is `2^5888`).
* `sourceTime_poly` / `draft_yao_source_polytime`: HYP-parametric in the
  admitted DRAFT record `G : GLSourceDraft t` (X05 / AD-1, NOT adopted, never
  instantiated), the composed source machine runs within `c * (n+1)^d` and the
  map input ↦ Option B code of the clone source is `BitMachine.Polytime`.
* `draft_yao_source_sizes`: vertex count `max 1 (v*(K*S))`, edge count
  `≤ e*(K*S)^K`, `v + e + 2 ≤ |input| + G.time input * pushBound`, and a
  polynomial bound on the output code length.

DRAFT: everything depends on AD-1 and D-A2 through the record's fields. -/

namespace Paper2.YaoT26Size

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoCloneMachine
open Paper2.YaoCloneSource
open Paper2.YaoSourceCodec
open Paper2.YaoX05Draft
open Paper2.YaoT26Draft

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

variable {K : ℕ}

/-! ## Lengths of the clone machine's blocks -/

theorem length_field (x : ℕ) : (field x).length = x + 1 := by
  simp [field]

theorem length_liftBlock_le (M V : ℕ) (l : Fin K → ℕ) (hl : ∀ j, l j ≤ V)
    (r : Fin K → Fin M) : (liftBlock M l r).length ≤ K * (M * (V + 1)) := by
  unfold liftBlock
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc ∑ j : Fin K, (List.length ∘ fun j => field (l j * M + (r j).val)) j
      ≤ ∑ _j : Fin K, M * (V + 1) := by
        apply Finset.sum_le_sum
        intro j _
        simp only [Function.comp_apply, length_field]
        have h1 : l j * M ≤ V * M := Nat.mul_le_mul_right M (hl j)
        have h2 := (r j).isLt
        nlinarith
    _ = K * (M * (V + 1)) := by simp

theorem length_goodLifts_le (M : ℕ) (l : Fin K → ℕ) : (goodLifts M l).length ≤ M ^ K :=
  (List.length_filter_le _ _).trans (length_allFuns M K).le

theorem length_edgeBlock_le (M V : ℕ) (l : Fin K → ℕ) (hl : ∀ j, l j ≤ V) :
    (edgeBlock M l).length ≤ M ^ K * (K * (M * (V + 1))) := by
  unfold edgeBlock
  rw [List.length_flatMap]
  have hs := List.sum_le_card_nsmul ((goodLifts M l).map fun r => (liftBlock M l r).length)
    (K * (M * (V + 1))) (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
      exact length_liftBlock_le M V l hl r)
  rw [List.length_map, smul_eq_mul] at hs
  exact hs.trans (Nat.mul_le_mul_right _ (length_goodLifts_le M l))

theorem length_flatMap_edgeBlock_le (M V : ℕ) (ls : List (Fin K → ℕ))
    (hV : ∀ l ∈ ls, ∀ j, l j ≤ V) :
    (ls.flatMap (edgeBlock M)).length ≤ ls.length * (M ^ K * (K * (M * (V + 1)))) := by
  rw [List.length_flatMap]
  have hs := List.sum_le_card_nsmul (ls.map fun l => (edgeBlock M l).length)
    (M ^ K * (K * (M * (V + 1)))) (by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      exact length_edgeBlock_le M V l (hV l hl))
  rwa [List.length_map, smul_eq_mul] at hs

theorem sum_goodLifts_le (M : ℕ) (ls : List (Fin K → ℕ)) :
    (ls.map (fun l => (goodLifts M l).length)).sum ≤ ls.length * M ^ K := by
  have hs := List.sum_le_card_nsmul (ls.map fun l => (goodLifts M l).length) (M ^ K) (by
    intro x hx
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
    exact length_goodLifts_le M l)
  rwa [List.length_map, smul_eq_mul] at hs

theorem occInput_length_ge (v : ℕ) (ls : List (Fin K → ℕ)) :
    v + 1 + (ls.length + 1) ≤ (occInput v ls).length := by
  simp [occInput, unaryNat]
  omega

/-- The per-edge cost is linear in the label bound. -/
theorem edgeCost_le (K M V : ℕ) :
    edgeCost K M V ≤ (5 + 2 * K + 6 * K * K + M ^ K * (2 * K + 3)) * (V + 1) := by
  unfold edgeCost
  generalize M ^ K = P
  nlinarith [Nat.zero_le (P * V), Nat.zero_le (K * K), Nat.zero_le V]

/-- The constant of the clone clock (depends on `K, M` only; `M^K` symbolic). -/
def cloneConst (K M : ℕ) : ℕ :=
  7 + (5 + 2 * K + 6 * K * K + M ^ K * (2 * K + 3)) + M ^ K * (K * M) + M ^ K + M

/-- The public clone clock is quadratic in the input code length. -/
theorem cloneTime_le (M v : ℕ) (ls : List (Fin K → ℕ)) (hV : ∀ l ∈ ls, ∀ j, l j ≤ v) :
    cloneTime K M v v ls ≤ cloneConst K M * ((occInput v ls).length + 1) ^ 2 := by
  have hn := occInput_length_ge v ls
  have hB := length_flatMap_edgeBlock_le M v ls hV
  have hG := sum_goodLifts_le M ls
  have hE := edgeCost_le K M v
  unfold cloneTime cloneConst
  generalize (occInput v ls).length = n at hn ⊢
  generalize (ls.flatMap (edgeBlock M)).length = B at hB ⊢
  generalize (ls.map (fun l => (goodLifts M l).length)).sum = G at hG ⊢
  generalize edgeCost K M v = E at hE ⊢
  generalize ls.length = e at hn hB hG ⊢
  generalize 5 + 2 * K + 6 * K * K + M ^ K * (2 * K + 3) = A at hE ⊢
  generalize M ^ K = P at hB hG ⊢
  -- N := n + 1, Q := N * N
  have hvN : v + 1 ≤ n + 1 := by omega
  have heN : e ≤ n + 1 := by omega
  have hQ1 : 1 ≤ (n + 1) * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNQ : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have t3 : e * E ≤ A * ((n + 1) * (n + 1)) :=
    calc e * E ≤ (n + 1) * (A * (n + 1)) :=
          Nat.mul_le_mul heN (hE.trans (Nat.mul_le_mul_left A hvN))
      _ = A * ((n + 1) * (n + 1)) := by ring
  have t4 : B ≤ P * (K * M) * ((n + 1) * (n + 1)) :=
    calc B ≤ e * (P * (K * (M * (v + 1)))) := hB
      _ ≤ (n + 1) * (P * (K * (M * (n + 1)))) :=
          Nat.mul_le_mul heN (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ hvN)))
      _ = P * (K * M) * ((n + 1) * (n + 1)) := by ring
  have t5 : G ≤ P * ((n + 1) * (n + 1)) :=
    calc G ≤ e * P := hG
      _ ≤ (n + 1) * P := Nat.mul_le_mul_right _ heN
      _ ≤ ((n + 1) * (n + 1)) * P := Nat.mul_le_mul_right _ hNQ
      _ = P * ((n + 1) * (n + 1)) := by ring
  have t6 : v * M ≤ M * ((n + 1) * (n + 1)) :=
    calc v * M ≤ (n + 1) * M := Nat.mul_le_mul_right _ (by omega)
      _ ≤ ((n + 1) * (n + 1)) * M := Nat.mul_le_mul_right _ hNQ
      _ = M * ((n + 1) * (n + 1)) := by ring
  have t1 : v + 1 ≤ (n + 1) * (n + 1) := hvN.trans hNQ
  have t2 : e + 1 ≤ (n + 1) * (n + 1) := by omega
  rw [sq]
  nlinarith [t1, t2, t3, t4, t5, t6, hQ1]

/-! ## The composed source (HYP-parametric in the DRAFT record) -/

theorem labelsOf_le {t : ℕ} (x : DraftOccSource t) :
    ∀ l ∈ labelsOf x, ∀ j, l j ≤ x.1 := by
  intro l hl j
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  exact (x.2.2 i j).isLt.le

/-- The clone stage of the composed source, in the occurrence code length. -/
theorem clone_stage_le {t : ℕ} (x : DraftOccSource t) :
    cloneTime (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * forbiddenColours t) x.1 x.1 (labelsOf x) ≤
      cloneConst (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * forbiddenColours t) *
        ((draftOccEncode x).length + 1) ^ 2 := by
  rw [draftOccEncode_eq]
  exact cloneTime_le _ _ _ (labelsOf_le x)

/-- The occurrence code produced by the record is at most linear in its clock. -/
theorem occ_length_le {t : ℕ} (G : GLSourceDraft t) (input : List Bool) :
    (draftOccEncode (G.output input)).length ≤
      input.length + G.time input * G.machine.pushBound :=
  BitMachine.output_length_bound G.machine (G.runs input)

/-- Y12-size, time: the composed source machine runs in polynomial time
(the polynomial depends on `t` through the record and the clone constant). -/
theorem sourceTime_poly {t : ℕ} (G : GLSourceDraft t) :
    ∃ c d : ℕ, ∀ input, sourceTime G input ≤ c * (input.length + 1) ^ d := by
  obtain ⟨c0, d0, hp⟩ := G.poly
  refine ⟨c0 + 2 * (1 + c0 * G.machine.pushBound) +
      cloneConst (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * forbiddenColours t) *
        (1 + c0 * G.machine.pushBound) ^ 2, (d0 + 1) * 2, fun input => ?_⟩
  have hm := occ_length_le G input
  have hc := clone_stage_le (G.output input)
  have hT := hp input
  unfold sourceTime
  rw [pow_mul]
  generalize G.machine.pushBound = P0 at hm ⊢
  generalize cloneConst (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * forbiddenColours t) = C at hc ⊢
  generalize (draftOccEncode (G.output input)).length = m at hm hc ⊢
  generalize cloneTime (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * forbiddenColours t) (G.output input).1
    (G.output input).1 (labelsOf (G.output input)) = CT at hc ⊢
  generalize G.time input = T at hm hT ⊢
  generalize input.length = L at hm hT ⊢
  have hB1 : 1 ≤ L + 1 := by omega
  have hBX : L + 1 ≤ (L + 1) ^ (d0 + 1) := Nat.le_self_pow (by omega) _
  have hBd : (L + 1) ^ d0 ≤ (L + 1) ^ (d0 + 1) := Nat.pow_le_pow_right hB1 (by omega)
  have hX1 : 1 ≤ (L + 1) ^ (d0 + 1) := Nat.one_le_pow _ _ (by omega)
  generalize (L + 1) ^ (d0 + 1) = X at hBX hBd hX1 ⊢
  generalize (L + 1) ^ d0 = Y at hT hBd
  have hTX : T ≤ c0 * X := hT.trans (Nat.mul_le_mul_left _ hBd)
  have hm1 : m + 1 ≤ (1 + c0 * P0) * X := by
    have h1 : T * P0 ≤ c0 * X * P0 := Nat.mul_le_mul_right _ hTX
    have h2 : (1 + c0 * P0) * X = X + c0 * X * P0 := by ring
    omega
  have hm2 : (m + 1) ^ 2 ≤ ((1 + c0 * P0) * X) ^ 2 := Nat.pow_le_pow_left hm1 2
  have hXX : X ≤ X ^ 2 := by nlinarith
  generalize 1 + c0 * P0 = k at hm1 hm2 ⊢
  have tc : CT ≤ C * k ^ 2 * X ^ 2 :=
    calc CT ≤ C * (m + 1) ^ 2 := hc
      _ ≤ C * (k * X) ^ 2 := Nat.mul_le_mul_left _ hm2
      _ = C * k ^ 2 * X ^ 2 := by ring
  have tt : T ≤ c0 * X ^ 2 := hTX.trans (Nat.mul_le_mul_left _ hXX)
  have tm : m + 1 ≤ k * X ^ 2 := hm1.trans (Nat.mul_le_mul_left _ hXX)
  nlinarith [tc, tt, tm]

/-- Y12-size, the lock's form of `yao:source`: a deterministic polynomial-time
reduction (the admitted `BitMachine.Polytime`) from input words to the Option B
code of the clone source, HYP-parametric in the DRAFT record. -/
theorem draft_yao_source_polytime {t : ℕ} (G : GLSourceDraft t) :
    BitMachine.Polytime
      (fun input => encode (cloneSource t (forbiddenColours t) (G.output input))) := by
  obtain ⟨c, d, h⟩ := sourceTime_poly G
  exact ⟨sourceMachine G, c, d, fun input =>
    BitMachine.outputsWithin_mono _ (draft_yao_source G input).1 (h input)⟩

/-- Y12-size, sizes (YA:92-116 and Y:77-90): each vertex gives `K*S` clones
(isolated vertex added if needed), each occurrence edge at most `(K*S)^K`
edges, the occurrence sizes are bounded by the record's output length, and the
output code has polynomial length. -/
theorem draft_yao_source_sizes {t : ℕ} (G : GLSourceDraft t) (input : List Bool) :
    (cloneSource t (forbiddenColours t) (G.output input)).1 =
        max 1 ((G.output input).1 * (2 ^ t * 2 ^ t * forbiddenColours t)) ∧
      (cloneSource t (forbiddenColours t) (G.output input)).2.1 ≤
        (G.output input).2.1 * (2 ^ t * 2 ^ t * forbiddenColours t) ^ (2 ^ t * 2 ^ t) ∧
      (G.output input).1 + (G.output input).2.1 + 2 ≤
        input.length + G.time input * G.machine.pushBound ∧
      (encode (cloneSource t (forbiddenColours t) (G.output input))).length ≤
        input.length + sourceTime G input * (sourceMachine G).pushBound := by
  obtain ⟨h1, _, h3⟩ := cloneSource_sizes t (forbiddenColours t) (G.output input)
  refine ⟨h1, h3, ?_, BitMachine.output_length_bound _ (draft_yao_source G input).1⟩
  have hge := occInput_length_ge (G.output input).1 (labelsOf (G.output input))
  rw [← draftOccEncode_eq, length_labelsOf] at hge
  have := occ_length_le G input
  omega

/-- Y12-size, polynomial output length. -/
theorem draft_yao_source_length_poly {t : ℕ} (G : GLSourceDraft t) :
    ∃ c d : ℕ, ∀ input,
      (encode (cloneSource t (forbiddenColours t) (G.output input))).length ≤
        c * (input.length + 1) ^ d := by
  obtain ⟨c, d, h⟩ := sourceTime_poly G
  refine ⟨1 + c * (sourceMachine G).pushBound, d + 1, fun input => ?_⟩
  have hl := (draft_yao_source_sizes G input).2.2.2
  have hs := h input
  generalize (sourceMachine G).pushBound = p at hl ⊢
  generalize sourceTime G input = T at hl hs
  generalize (encode (cloneSource t (forbiddenColours t) (G.output input))).length = o at hl
  generalize input.length = L at hl hs ⊢
  have hB : L + 1 ≤ (L + 1) ^ (d + 1) := Nat.le_self_pow (by omega) _
  have hd : (L + 1) ^ d ≤ (L + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : T * p ≤ c * (L + 1) ^ (d + 1) * p :=
    Nat.mul_le_mul_right _ (hs.trans (Nat.mul_le_mul_left _ hd))
  have h3 : (1 + c * p) * (L + 1) ^ (d + 1) = (L + 1) ^ (d + 1) + c * (L + 1) ^ (d + 1) * p := by
    ring
  omega

#print axioms cloneTime_le
#print axioms sourceTime_poly
#print axioms draft_yao_source_polytime
#print axioms draft_yao_source_sizes
#print axioms draft_yao_source_length_poly

end Paper2.YaoT26Size
