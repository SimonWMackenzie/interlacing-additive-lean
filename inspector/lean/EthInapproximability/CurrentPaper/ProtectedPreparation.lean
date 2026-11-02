import EthInapproximability.CurrentPaper.ProtectedProfiles
import EthInapproximability.CurrentPaper.ActualPrefix
import EthInapproximability.CurrentPaper.ProtocolSeparation

/-!
# The actual first prefix in a dense protected restriction

Source: frozen v8 `A-stage4-details.tex`,
`lem:paper-protected-preparation`, first paragraph.

The retained reference columns give one common selector tuple set. The
template-column copies are projected with bin labels intact. We pull back
the original protocol without pruning: reachable separation on this actual
restriction forces the prefix of the original tree, including graph rows.
The second-matrix robustness and scalar deletion/routing gates remain
upstream inputs; no protected-matrix hardness is assumed.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedPreparation

open scoped BigOperators Classical
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction JointTransfer ProtectedProfiles ProtocolSeparation ActualPrefix
open EthInapproximability.ParameterizedNP.TerminalStateRealization

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- A total section of an actual retained image; the default is irrelevant
on that image. It does not prune a protocol pulled back along it. -/
def imageSection {A B : Type*} [Nonempty A] [DecidableEq B]
    (S : Finset A) (f : A → B) (b : B) : A :=
  if h : b ∈ S.image f then (Finset.mem_image.mp h).choose else Classical.ofNonempty

theorem imageSection_mem {A B : Type*} [Nonempty A] [DecidableEq B]
    (S : Finset A) (f : A → B) {b : B} (hb : b ∈ S.image f) :
    imageSection S f b ∈ S := by
  simp only [imageSection, dif_pos hb]
  exact (Finset.mem_image.mp hb).choose_spec.1

theorem imageSection_apply {A B : Type*} [Nonempty A] [DecidableEq B]
    (S : Finset A) (f : A → B) {b : B} (hb : b ∈ S.image f) :
    f (imageSection S f b) = b := by
  simp only [imageSection, dif_pos hb]
  exact (Finset.mem_image.mp hb).choose_spec.2

/-- Deleting at most `(1-x)` times a group's size leaves an `x` fraction
of that group. Deletions are measured in the original physical carrier. -/
theorem retained_group_count {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset A) {x : ℝ}
    (hloss : ((Finset.univ \ S).card : ℝ) ≤ (1 - x) * T.card) :
    x * T.card ≤ ((S ∩ T).card : ℝ) := by
  have hsub : T \ S ⊆ Finset.univ \ S :=
    Finset.sdiff_subset_sdiff (Finset.subset_univ T) (Finset.Subset.refl S)
  have hc : ((T \ S).card : ℝ) ≤ (Finset.univ \ S).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hp := Finset.card_inter_add_card_sdiff T S
  have hpR : ((S ∩ T).card : ℝ) + (T \ S).card = T.card := by
    exact_mod_cast (by simpa [Finset.inter_comm] using hp)
  nlinarith

/-- Projecting all retained template copies contains every projected label
from the same bin. Consequently no per-bin density is lost. -/
theorem template_fibre_count (s L nv nb : ℕ) (hs : 0 < s) (hL : 0 < L)
    (B : Finset (ProtectedRows s L nv nb X)) (i : Fin s) :
    ((B ∩ templateBin s L nv nb i).image (templateQuotient hL)).card ≤
      (((B ∩ templateRows s L nv nb).image (templatePair s L nv nb hs hL)).filter
        (fun r => r.1 = i)).card := by
  let S := (B ∩ templateBin (X := X) s L nv nb i).image (templateQuotient hL)
  have hinj : Function.Injective (fun z : Fin L => (i, z)) := fun _ _ h => congrArg Prod.snd h
  rw [← Finset.card_image_of_injective S hinj]
  apply Finset.card_le_card
  intro r hr
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨c, hc, hcz⟩ := Finset.mem_image.mp hz
  obtain ⟨b, _, hbc⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hc).2
  subst c
  rcases b with ⟨z', k⟩
  have htemplate : templateEmbedding s L nv nb i (z', k) ∈ templateRows (X := X) s L nv nb :=
    Finset.mem_image.mpr ⟨((i, z'), k), Finset.mem_univ _, rfl⟩
  have hpair : templatePair s L nv nb hs hL (templateEmbedding s L nv nb i (z', k)) = (i, z) := by
    have hz' : z' = z := by simpa only [quotient_template] using hcz
    simp only [templatePair, rawRow_template, hz']
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
    ⟨templateEmbedding s L nv nb i (z', k), Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hc).1, htemplate⟩, hpair⟩, rfl⟩

/-- The literal retained duplicate supplies a full `s`-bin classical
restriction on common tuple columns. All losses are cardinalities of
physical inputs in the original carriers. -/
theorem dense_template_bracket [Nonempty X] [Nonempty Y]
    (a s q L nv nb : ℕ) (hs : 0 < s) (hq : 0 < q) (hL : 0 < L)
    (hv : 0 < nv) (hb : 0 < nb)
    (A : Finset (ProtectedColumns a s q Y)) (B : Finset (ProtectedRows s L nv nb X))
    {x z : ℝ}
    (hrowLoss : ∀ i : Fin s, ((Finset.univ \ B).card : ℝ) ≤
      (1 - x) * (templateBin (X := X) s L nv nb i).card)
    (hcolLoss : ((Finset.univ \ A).card : ℝ) ≤
      (1 - z) * (referenceRows (Y := Y) a s q).card) :
    ((B ∩ templateRows s L nv nb).image (templatePair s L nv nb hs hL),
      (A ∩ referenceRows a s q).image selectorTuple) ∈
      bracketGE (Fin L) (SecondRows a s q Y) s x z := by
  letI := secondRows_nonempty (Y := Y) a s q hq
  constructor
  · intro i _
    rw [Nat.ceil_le]
    have hret := retained_group_count B (templateBin (X := X) s L nv nb i) (hrowLoss i)
    have hden := regularOn_density_transfer (template_regular (X := X) s L nv nb hL i)
      (template_labels_pos s L nv nb hs hL hv hb)
      (Finset.inter_subset_right (s₁ := B) (s₂ := templateBin (X := X) s L nv nb i))
    have hbin : (0 : ℝ) < (templateBin (X := X) s L nv nb i).card := by
      rw [template_bin_card]
      exact_mod_cast Nat.mul_pos hL (template_labels_pos s L nv nb hs hL hv hb)
    have hquot : x ≤ (((B ∩ templateBin (X := X) s L nv nb i).image
        (templateQuotient hL)).card : ℝ) / Fintype.card (Fin L) :=
      ((le_div_iff₀ hbin).2 hret).trans hden
    have hLreal : (0 : ℝ) < Fintype.card (Fin L) := by simpa using (Nat.cast_pos.mpr hL : (0 : ℝ) < L)
    have hc := (le_div_iff₀ hLreal).mp hquot
    have hf : (((B ∩ templateBin s L nv nb i).image (templateQuotient hL)).card : ℝ) ≤
        (((B ∩ templateRows s L nv nb).image (templatePair s L nv nb hs hL)).filter
          (fun r => r.1 = i)).card := by exact_mod_cast template_fibre_count s L nv nb hs hL B i
    have hh : (Fintype.card (Fin L) : ℝ) * x ≤
        (((B ∩ templateBin s L nv nb i).image (templateQuotient hL)).card : ℝ) := by
      simpa only [mul_comm] using hc
    exact hh.trans hf
  · rw [Nat.ceil_le]
    have hret := retained_group_count A (referenceRows (Y := Y) a s q) hcolLoss
    have hden := reference_common_density a s q hq (A ∩ referenceRows a s q)
      Finset.inter_subset_right
    have hreg := reference_tuple_regular (Y := Y) a s q
    have href : (0 : ℝ) < (referenceRows (Y := Y) a s q).card := by
      rw [referenceRows, Finset.card_image_of_injective _ (referenceEmbedding a s q).injective,
        Finset.card_univ, Fintype.card_prod]
      exact_mod_cast Nat.mul_pos Fintype.card_pos (reference_labels_pos a s q hq)
    have hquot := ((le_div_iff₀ href).2 hret).trans hden
    have hfull : (0 : ℝ) < Fintype.card (ThirdColumns a s q Y) := by exact_mod_cast Fintype.card_pos
    have hc := (le_div_iff₀ hfull).mp hquot
    simpa only [ThirdColumns, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_comm] using hc

/-- Reachable classical separation, on an actual restriction, forces the
syntactic prefix of the ORIGINAL protocol. No query is removed, and the
charged suffix bound therefore also applies to its graph rows. -/
theorem actual_prefix_from_bracket {A B U V : Type*}
    [Fintype U] [Fintype V] [Nonempty U] [Nonempty V]
    (f : U → V → Bool) {b k : ℕ} {x z : ℝ}
    (hrobust : IsRobustAt f b) (hk : 1 ≤ k) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z)
    (hgap : 2 ^ k * ⌈(Fintype.card U : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ <
      ⌈(Fintype.card U : ℝ) * x⌉₊)
    (E : Finset (Fin (2 ^ k) × U)) (T : Finset (Fin (2 ^ k) → V))
    (hET : (E, T) ∈ bracketGE U V (2 ^ k) x z)
    (φ : Fin (2 ^ k) × U → A) (ψ : (Fin (2 ^ k) → V) → B)
    (P : Protocol A B Bool) (hcost : P.cost ≤ D f + k)
    (hcomp : ∀ r ∈ E, ∀ c ∈ T, P.eval (φ r) (ψ c) = interlaceFun f (2 ^ k) r c) :
    AllAlice k P ∧
      NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k))) E
        (fun r => Protocol.prefixCodeRaw k P (φ r))
        ⌈(Fintype.card U : ℝ) * x⌉₊
        ⌈(Fintype.card U : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ ∧
      (∀ j, (Protocol.rowSubtreeAtRaw k P j).cost + k ≤ P.cost) ∧
      (∀ r c, (Protocol.rowSubtreeAtRaw k P (Protocol.prefixCodeRaw k P r)).eval r c =
        P.eval r c) := by
  let Q := Protocol.pullback φ ψ P
  have hQcost : Q.cost ≤ D f + k := by simpa only [Q, Protocol.pullback_cost] using hcost
  have hQcomp : ∀ r ∈ E, ∀ c ∈ T, Q.eval r c = interlaceFun f (2 ^ k) r c := by
    intro r hr c hc
    simpa only [Q, Protocol.pullback_eval] using hcomp r hr c hc
  obtain ⟨hprefix, hnw, hcodes⟩ := classicalSeparationOn hrobust hk hx1 hz hgap E T hET Q hQcost hQcomp
  have hT : T.Nonempty := by
    have hzpos : 0 < z := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 18 / 25) hz
    have hceil : 0 < ⌈(Fintype.card V : ℝ) ^ (2 ^ k) * z⌉₊ :=
      Nat.ceil_pos.mpr (mul_pos (pow_pos (by exact_mod_cast Fintype.card_pos (α := V)) _) hzpos)
    exact Finset.card_pos.mp (lt_of_lt_of_le hceil hET.2)
  have hactual := allAlice_of_pullback_codes φ ψ E T k P hprefix hT hcodes
  refine ⟨hactual, ?_, fun j => hactual.subtree_cost j, fun r c => hactual.subtree_eval r c⟩
  have heq : (fun r => Protocol.prefixCodeRaw k P (φ r)) = Protocol.prefixCodeRaw k Q := by
    funext r
    exact (Protocol.prefixCodeRaw_pullback φ ψ k P r).symm
  rw [heq]
  exact hnw

/-- The dense restriction forces an actual prefix in the literal transpose
of `N`. The conclusion quantifies over every original row, not just the
template rows used to prove separation. -/
theorem protected_prefix [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) (a k q L nv nb : ℕ)
    (hs : 0 < 2 ^ k) (hq : 0 < q) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ 2 ^ k)
    {b : ℕ} {x z : ℝ}
    (hrobust : IsRobustAt (fun j d => secondMatrix R a (2 ^ k) q L family d j) b)
    (hk : 1 ≤ k) (hx1 : x ≤ 1) (hz : (18 / 25 : ℝ) ≤ z)
    (hgap : 2 ^ k * ⌈(Fintype.card (Fin L) : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ <
      ⌈(Fintype.card (Fin L) : ℝ) * x⌉₊)
    (A : Finset (ProtectedColumns a (2 ^ k) q Y))
    (B : Finset (ProtectedRows (2 ^ k) L nv nb X))
    (hrowLoss : ∀ i : Fin (2 ^ k), ((Finset.univ \ B).card : ℝ) ≤
      (1 - x) * (templateBin (X := X) (2 ^ k) L nv nb i).card)
    (hcolLoss : ((Finset.univ \ A).card : ℝ) ≤
      (1 - z) * (referenceRows (Y := Y) a (2 ^ k) q).card)
    (P : Protocol (ProtectedRows (2 ^ k) L nv nb X) (ProtectedColumns a (2 ^ k) q Y) Bool)
    (hcost : P.cost ≤ D (fun j d => secondMatrix R a (2 ^ k) q L family d j) + k)
    (hcomp : ∀ r ∈ B, ∀ c ∈ A,
      P.eval r c = protectedMatrix R a (2 ^ k) q L nv nb hs family order vectors cap c r) :
    AllAlice k P ∧
      (∀ j, (Protocol.rowSubtreeAtRaw k P j).cost + k ≤ P.cost) ∧
      (∀ r c, (Protocol.rowSubtreeAtRaw k P (Protocol.prefixCodeRaw k P r)).eval r c =
        P.eval r c) ∧
      ∃ φ : ThirdRows (2 ^ k) L → ProtectedRows (2 ^ k) L nv nb X,
        (∀ r ∈ (B ∩ templateRows (2 ^ k) L nv nb).image
          (templatePair (2 ^ k) L nv nb hs hL),
          φ r ∈ B ∩ templateRows (2 ^ k) L nv nb ∧
            templatePair (2 ^ k) L nv nb hs hL (φ r) = r) ∧
        NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ k)))
          ((B ∩ templateRows (2 ^ k) L nv nb).image (templatePair (2 ^ k) L nv nb hs hL))
          (fun r => Protocol.prefixCodeRaw k P (φ r))
          ⌈(Fintype.card (Fin L) : ℝ) * x⌉₊
          ⌈(Fintype.card (Fin L) : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  letI := secondRows_nonempty (Y := Y) a (2 ^ k) q hq
  have htemplate : 0 < (templateRows (X := X) (2 ^ k) L nv nb).card := by
    rw [template_rows_card]
    exact Nat.mul_pos (Nat.mul_pos hs hL) (template_labels_pos _ _ _ _ hs hL hv hb)
  letI : Nonempty (ProtectedRows (2 ^ k) L nv nb X) :=
    ⟨(Finset.card_pos.mp htemplate).choose⟩
  have href : 0 < (referenceRows (Y := Y) a (2 ^ k) q).card := by
    rw [referenceRows, Finset.card_image_of_injective _ (referenceEmbedding a (2 ^ k) q).injective,
      Finset.card_univ, Fintype.card_prod]
    exact Nat.mul_pos Fintype.card_pos (reference_labels_pos a (2 ^ k) q hq)
  letI : Nonempty (ProtectedColumns a (2 ^ k) q Y) := ⟨(Finset.card_pos.mp href).choose⟩
  let BT := B ∩ templateRows (X := X) (2 ^ k) L nv nb
  let AR := A ∩ referenceRows (Y := Y) a (2 ^ k) q
  let E := BT.image (templatePair (2 ^ k) L nv nb hs hL)
  let T := AR.image selectorTuple
  let φ := imageSection BT (templatePair (2 ^ k) L nv nb hs hL)
  let ψ := imageSection AR selectorTuple
  have hET : (E, T) ∈ bracketGE (Fin L) (SecondRows a (2 ^ k) q Y) (2 ^ k) x z :=
    dense_template_bracket a (2 ^ k) q L nv nb hs hq hL hv hb A B hrowLoss hcolLoss
  have hcalc : ∀ r ∈ E, ∀ c ∈ T,
      P.eval (φ r) (ψ c) =
        interlaceFun (fun j d => secondMatrix R a (2 ^ k) q L family d j) (2 ^ k) r c := by
    intro r hr c hc
    have hrmem : φ r ∈ BT := imageSection_mem BT _ hr
    have hcmem : ψ c ∈ AR := imageSection_mem AR _ hc
    have hrval : templatePair (2 ^ k) L nv nb hs hL (φ r) = r := imageSection_apply BT _ hr
    have hcval : selectorTuple (ψ c) = c := imageSection_apply AR _ hc
    rw [hcomp _ (Finset.mem_inter.mp hrmem).1 _ (Finset.mem_inter.mp hcmem).1,
      template_entry_all R a (2 ^ k) q L nv nb hs hL family order vectors cap _ _
        (Finset.mem_inter.mp hrmem).2, hrval, hcval]
    rfl
  obtain ⟨hpref, hnw, hbudget, heval⟩ := actual_prefix_from_bracket
    (fun j d => secondMatrix R a (2 ^ k) q L family d j)
    hrobust hk hx1 hz hgap E T hET φ ψ P hcost hcalc
  refine ⟨hpref, hbudget, heval, φ, ?_, hnw⟩
  intro r hr
  exact ⟨imageSection_mem BT _ hr, imageSection_apply BT _ hr⟩

end EthInapproximability.CurrentPaper.ProtectedPreparation
