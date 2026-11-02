import CurrentAdditive.V40MidpointRequestClock

noncomputable section
namespace CurrentAdditive.V40MidpointAmbient

open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
open EncodedCommunication
open V40MidpointRequest

variable {J : Type*} [DecidableEq J]
abbrev Ambient (J : Type*) := J ⊕ V40MidpointRequest.Stack

def locateFn (b k printed : J) (i : V40MidpointRequest.Stack) : Ambient J :=
  if i = low 0 then .inl b else if i = low 1 then .inl k else
    if i = low 5 then .inl printed else .inr i

def locate (b k printed : J) (hbk : b ≠ k) (hbp : b ≠ printed) (hkp : k ≠ printed) :
    V40MidpointRequest.Stack ↪ Ambient J :=
  ⟨locateFn b k printed, by
    intro i j he
    unfold locateFn at he
    split_ifs at he <;> simp_all⟩

def initial (S : J → List Bool) : Ambient J → List Bool := Sum.elim S (fun _ => [])

def final (S : J → List Bool) (B k : ℕ) (word : List Bool) : Ambient J → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (initial S) (.inr (low 2)) (List.replicate (2*B+k) true))
        (.inr (low 3)) (natField (2*B+k)))
      (.inr (low 6)) (AFront.Projection.matrixPart word))
    (.inr (low 7)) (natField (2*B+k) ++ AFront.Projection.matrixPart word)

def program (b k printed : J) (hbk : b ≠ k) (hbp : b ≠ printed) (hkp : k ≠ printed) :=
  fun l => stackStmt (locate b k printed hbk hbp hkp) (V40MidpointRequest.program l)

theorem locate_low_other (b k printed : J) (hbk : b ≠ k) (hbp : b ≠ printed)
    (hkp : k ≠ printed) (j : Fin 32) (h0 : j ≠ 0) (h1 : j ≠ 1) (h5 : j ≠ 5) :
    locate b k printed hbk hbp hkp (low j) = .inr (low j) := by
  simp [locate, locateFn, h0, h1, h5]

theorem locate_high (b k printed : J) (hbk : b ≠ k) (hbp : b ≠ printed)
    (hkp : k ≠ printed) (i : V40MidpointRequest.Stack) (hi : 32 ≤ i.val) :
    locate b k printed hbk hbp hkp i = .inr i := by
  simp only [locate, Function.Embedding.coeFn_mk, locateFn,
    if_neg (high_ne_low i hi 0), if_neg (high_ne_low i hi 1), if_neg (high_ne_low i hi 5)]

theorem frame_final (b k printed : J) (hbk : b ≠ k) (hbp : b ≠ printed)
    (hkp : k ≠ printed) (S : J → List Bool) (B K : ℕ) (word : List Bool) :
    let ι := locate b k printed hbk hbp hkp
    let A := initial S
    bank ι A (V40MidpointRequest.final (fun i => A (ι i)) B K word) = final S B K word := by
  intro ι A
  simp only [V40MidpointRequest.final, bank_update, bank_restrict]
  have h2 := locate_low_other b k printed hbk hbp hkp 2 (by decide) (by decide) (by decide)
  have h3 := locate_low_other b k printed hbk hbp hkp 3 (by decide) (by decide) (by decide)
  have h6 := locate_low_other b k printed hbk hbp hkp 6 (by decide) (by decide) (by decide)
  have h7 := locate_low_other b k printed hbk hbp hkp 7 (by decide) (by decide) (by decide)
  simp only [ι, h2, h3, h6, h7] <;> rfl

/-- The raw caller bank is retained exactly. The only source-side facts are
the checked B, k and encoded-word readbacks; no execution or comparison
certificate is an argument. Fresh work is allocated in the new summand. -/
theorem outputs (b k printed : J) (hbk : b ≠ k) (hbp : b ≠ printed)
    (hkp : k ≠ printed) (S : J → List Bool) (B K : ℕ) (word : List Bool)
    (hb : S b = List.replicate B true) (hk : S k = List.replicate K true)
    (hp : S printed = word) :
    ∃ t ≤ V40MidpointRequest.clock B K word,
      ((advance (program b k printed hbk hbp hkp))^[t])
        (⟨some V40MidpointRequest.start, V40MidpointRequest.control, initial S⟩ :
          TM2.Cfg (fun _ : Ambient J => Bool) _ _) =
        ⟨none, V40MidpointRequest.control, final S B K word⟩ := by
  let ι := locate b k printed hbk hbp hkp
  let A := initial S
  let native : V40MidpointRequest.Bank := fun i => A (ι i)
  have hlow (j : Fin 32) (h0 : j ≠ 0) (h1 : j ≠ 1) (h5 : j ≠ 5) :
      native (low j) = [] := by
    rw [show native (low j) = A (ι (low j)) from rfl,
      locate_low_other b k printed hbk hbp hkp j h0 h1 h5]
    rfl
  obtain ⟨t, ht, hr⟩ := V40MidpointRequest.outputs native B K word
    (by simpa [native, A, ι, locate, locateFn, initial] using hb)
    (by simpa [native, A, ι, locate, locateFn, initial] using hk)
    (by simpa [native, A, ι, locate, locateFn, initial] using hp)
    (hlow 2 (by decide) (by decide) (by decide))
    (hlow 3 (by decide) (by decide) (by decide))
    (hlow 4 (by decide) (by decide) (by decide))
    (hlow 6 (by decide) (by decide) (by decide))
    (hlow 7 (by decide) (by decide) (by decide))
    (by intro i hi; change A (ι i) = []; rw [locate_high b k printed hbk hbp hkp i hi]; rfl)
  have he := BitMachineStackRun.run ι A V40MidpointRequest.program
    (⟨some V40MidpointRequest.start, V40MidpointRequest.control, native⟩ :
      TM2.Cfg (fun _ : V40MidpointRequest.Stack => Bool) _ _) t
  rw [hr] at he
  change ((advance (program b k printed hbk hbp hkp))^[t])
    ⟨some V40MidpointRequest.start, V40MidpointRequest.control, bank ι A native⟩ =
    ⟨none, V40MidpointRequest.control,
      bank ι A (V40MidpointRequest.final native B K word)⟩ at he
  have hs : bank ι A native = A := bank_restrict ι A
  rw [hs, frame_final b k printed hbk hbp hkp S B K word] at he
  exact ⟨t, ht, he⟩

theorem final_raw (S : J → List Bool) (B k : ℕ) (word : List Bool) (j : J) :
    final S B k word (.inl j) = S j := by simp [final, Function.update, initial]

theorem final_request (S : J → List Bool) (B k : ℕ) (i : Instance) :
    final S B k (encodeInstance i) (.inr (low 7)) =
      natField (2*B+k) ++ Paper2.AModel.matrixWord i.rows i.cols i.table := by
  simp only [final, Function.update_self, AFront.Projection.matrixPart_encodeInstance]
  rfl

#print axioms outputs
#print axioms final_raw
#print axioms final_request

end CurrentAdditive.V40MidpointAmbient
