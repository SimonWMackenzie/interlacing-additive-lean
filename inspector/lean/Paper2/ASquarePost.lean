import Paper2.ASquarePostHeader
import Paper2.ASquareInstanceWrite
import Paper2.ASquareT24

/-!
# U17 segments 3-4: the square post machine, `SquarePost` proved, T01/T24 square closed
(lane owner:a-square-2)

Private, 26 September 2026. Paper A lock v12 (`01-introduction.tex:92`, `06-reduction.tex:83-86`,
`115-116`, `144-150`).

Segment 3: ONE fixed program `full` on the ambient stacks (`SqParse.Stack`), sequenced by the
admitted `BitMachineRawSequence.runs`:
`parser` (SqParse) ; `SideWrite.program` (a-square-owner-1, frozen: the unary side joined with the
admitted square writer), inlined at the writer's own 20 stacks by the admitted stack embedding ;
`header` (SqHeader). The `BitMachine.Machine` is the admitted `BitMachineEncoding.ofFinite` of this
program with input stack = writer slot 2 and output stack = the writer output stack, exactly the
conventions of `BitMachine.Machine.init` / `OutputsWithin` used by `ASquare.SquarePost`.

Segment 4: `squarePost : SquarePost squareMachine squareCP squareEP` (the literal contract of
`ASquare.lean:83`: every VALID instance; the contract says nothing about malformed words, and
nothing is claimed about them), with `squareCP = 10^15`, `squareEP = 12`; hence `T01_square` and
`T24_square` hold with no open machine contract (`T01_square_closed`, `T24_square_closed`).
Does not close a ledger row.
-/

namespace Paper2.ASquare.Post

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.Unit4Post

/-! ## Segment 3: the joined program -/

def ιL : WStack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩

def sSW := fun l => BitMachineStackEmbedding.stackStmt ιL (SideWrite.program l)

abbrev ML := BitMachineRawSequence.Label SideWrite.Label HLabel
abbrev MV := BitMachineRawSequence.Control SideWrite.Control HControl
def mid := BitMachineRawSequence.program sSW header hstart SideWrite.initial hinit
def mstart : ML := BitMachineRawSequence.leftLabel SideWrite.start
def minit : MV := (SideWrite.initial, hinit)

abbrev FLabel := BitMachineRawSequence.Label PLabel ML
abbrev FControl := BitMachineRawSequence.Control PControl MV
/-- **The square post program**: parser ; side ; writer ; header. -/
def full := BitMachineRawSequence.program parser mid mstart pinit minit
def fstart : FLabel := BitMachineRawSequence.leftLabel pstart
def finit : FControl := (pinit, minit)

/-- The side and writer stage on the ambient bank (valid instances). -/
theorem stage_sw (I : EncodedCommunication.Instance) (hI : I.Valid) (x : Fin 8 → List Bool) :
    ∃ t ≤ Side.sideBound I.rows I.cols +
        MatrixTableWriter.writerBound (SquarePadding.side I.rows I.cols)
          (SquarePadding.side I.rows I.cols)
          (Unit4Shell.SquareWriter.callbackBound (SquarePadding.side I.rows I.cols)
            (SquarePadding.side I.rows I.cols) I.rows I.cols (I.rows * I.cols)) + 1, ∃ v,
      ((advance sSW)^[t])
        ⟨some SideWrite.start, SideWrite.initial,
          pbank (List.replicate I.rows true) (List.replicate I.cols true) I.table x⟩ =
      ⟨none, v, hbank (Unit4Shell.SquareWriter.persistentBank I.rows I.cols I.table)
        (2 ^ SquarePadding.exponent I.rows I.cols) (2 ^ SquarePadding.exponent I.rows I.cols)
        ((squareInstance I).table ++ []) x⟩ := by
  obtain ⟨t, ht, v, h⟩ := InstanceWrite.instance_write I hI []
  refine ⟨t, ht, v, ?_⟩
  rw [pbank, pb_eq]
  exact embed_run ιL SideWrite.program SideWrite.start SideWrite.initial v _ _ _ _ t h
    (fun _ => rfl) (fun _ => rfl)
    (by
      intro j hj
      rcases j with k | i
      · exact absurd rfl (hj k)
      · rfl)

/-- The printed square word, in the header's form. -/
theorem encode_square (I : EncodedCommunication.Instance) :
    EncodedCommunication.encodeInstance (squareInstance I) =
      EncodedCommunication.natField (2 ^ SquarePadding.exponent I.rows I.cols) ++
        EncodedCommunication.natField (2 ^ SquarePadding.exponent I.rows I.cols) ++
        EncodedCommunication.natField I.threshold ++ ((squareInstance I).table ++ []) := by
  rw [List.append_nil]
  rfl

/-- The explicit total clock. -/
def fullBound (r c thr : ℕ) : ℕ :=
  parseBound r c thr +
    (Side.sideBound r c +
      MatrixTableWriter.writerBound (SquarePadding.side r c) (SquarePadding.side r c)
        (Unit4Shell.SquareWriter.callbackBound (SquarePadding.side r c) (SquarePadding.side r c)
          r c (r * c)) + 1 +
      headerBound (SquarePadding.exponent r c) thr + 1) + 1

/-- **Segment 3 (the join, raw form).** On the encoded word of every VALID instance, the ONE
fixed program `full`, started with the word in writer slot 2 and every other stack empty, halts
within `fullBound` steps with exactly `encodeInstance (squareInstance I)` on the writer output
stack; the persistent bank is `persistentBank I.rows I.cols I.table`, every other stack is empty
except the admitted serializer's consumed bank `S'` (extra stacks 3, 4, 5). -/
theorem full_run (I : EncodedCommunication.Instance) (hI : I.Valid) :
    ∃ t ≤ fullBound I.rows I.cols I.threshold, ∃ (v : FControl) (S' : BitMachineBankSerialize.Bank 3),
      ((advance full)^[t])
        ⟨some fstart, finit, pbank [] [] (EncodedCommunication.encodeInstance I) ext0⟩ =
      ⟨none, v, hbank (Unit4Shell.SquareWriter.persistentBank I.rows I.cols I.table) 0 0
        (EncodedCommunication.encodeInstance (squareInstance I))
        (ext [] [] [] (S' 0) (S' 1) (S' 2) [] [])⟩ := by
  obtain ⟨r, c, thr, bits⟩ := I
  obtain ⟨tp, htp, vp, hp⟩ := parse_run r c thr bits
  obtain ⟨ts, hts, vs, hs⟩ := stage_sw ⟨r, c, thr, bits⟩ hI
    (ext thr.bits.reverse [] [] [] [] [] [] [])
  obtain ⟨th, hth, vh, S', hh⟩ := header_run
    (Unit4Shell.SquareWriter.persistentBank r c bits) (SquarePadding.exponent r c) thr
    ((squareInstance ⟨r, c, thr, bits⟩).table ++ [])
  obtain ⟨tm, htm, em⟩ := BitMachineRawSequence.runs sSW header SideWrite.start hstart
    SideWrite.initial vs hinit vh _ _ _ ts th hs hh
  obtain ⟨tf, htf, ef⟩ := BitMachineRawSequence.runs parser mid pstart mstart pinit vp minit
    (SideWrite.initial, vh) _ _ _ tp tm hp em
  have hb : tf ≤ fullBound r c thr := by
    try simp only at hts
    unfold fullBound
    omega
  rw [encode_square]
  exact ⟨tf, hb, _, S', ef⟩

/-! ## The machine and its input/output conventions -/

/-- **The square post machine** (one fixed finite program). -/
noncomputable def squareMachine : BitMachine.Machine :=
  BitMachineEncoding.ofFinite (slot 2) outS fstart finit full

theorem rawInit_bank (word : List Bool) :
    (fun k : Stack => if k = slot 2 then word else []) = pbank [] [] word ext0 := by
  funext j
  rcases j with ((k | k) | k) | k <;> fin_cases k <;> rfl

theorem full_outputs (I : EncodedCommunication.Instance) (hI : I.Valid) :
    squareMachine.OutputsWithin (EncodedCommunication.encodeInstance I)
      (EncodedCommunication.encodeInstance (squareInstance I))
      (fullBound I.rows I.cols I.threshold) := by
  obtain ⟨t, ht, v, S', e⟩ := full_run I hI
  have hi : rawInit (slot 2) fstart finit (EncodedCommunication.encodeInstance I) =
      ⟨some fstart, finit, pbank [] [] (EncodedCommunication.encodeInstance I) ext0⟩ := by
    unfold rawInit
    exact congrArg (fun S => (⟨some fstart, finit, S⟩ : TM2.Cfg (fun _ : Stack => Bool) FLabel FControl))
      (rawInit_bank _)
  apply outputsWithin_of_raw_run (slot 2) outS fstart finit full
    (EncodedCommunication.encodeInstance I)
    (EncodedCommunication.encodeInstance (squareInstance I)) t _ ht
  · rw [hi, e]
  · first | (rw [hi, e]; done) | (rw [hi, e]; rfl)

/-! ## The polynomial clock -/

theorem natField_pow_length (E thr : ℕ) :
    (EncodedCommunication.natField (2 ^ E) ++ EncodedCommunication.natField (2 ^ E) ++
      EncodedCommunication.natField thr).length = 4 * E + 7 + 2 * thr.bits.length := by
  simp only [List.length_append, EncodedCommunication.natField,
    EncodedCommunication.field_length, Bits.pow_bits, List.length_replicate,
    List.length_singleton]
  omega

theorem fullBound_le (I : EncodedCommunication.Instance) (hI : I.Valid) :
    fullBound I.rows I.cols I.threshold ≤
      10 ^ 15 * ((EncodedCommunication.encodeInstance I).length + 1) ^ 12 := by
  obtain ⟨r, c, thr, bits⟩ := I
  obtain ⟨hr0, hc0, hlen⟩ := hI
  simp only at hr0 hc0 hlen ⊢
  unfold fullBound
  have hW := EncodedCommunication.encodeInstance_length ⟨r, c, thr, bits⟩
  simp only at hW
  set W := (EncodedCommunication.encodeInstance ⟨r, c, thr, bits⟩).length with hWdef
  set X := W + 1 with hXdef
  have hX : 1 ≤ X := by omega
  have hrc : r ≤ r * c := Nat.le_mul_of_pos_right r hc0
  have hcr : c ≤ r * c := Nat.le_mul_of_pos_left c hr0
  have hr : r ≤ X := by omega
  have hc : c ≤ X := by omega
  have hlr : r.bits.length ≤ X := by omega
  have hlc : c.bits.length ≤ X := by omega
  have hlt : thr.bits.length ≤ X := by omega
  set E := SquarePadding.exponent r c with hEdef
  have hS : 2 ^ E ≤ 2 * (r + c) := Unit4Shell.SquareWriter.side_le_two_sum (n := c) hr0
  have hS4 : 2 ^ E ≤ 4 * X := by omega
  have hEE : E < 2 ^ E := Nat.lt_two_pow_self
  have hE4 : E ≤ 4 * X := by omega
  -- powers of X
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX4 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right hX (by norm_num)
  have hX12a : X ^ 4 ≤ X ^ 12 := Nat.pow_le_pow_right hX (by norm_num)
  have hX12b : 1 ≤ X ^ 12 := Nat.one_le_pow _ _ hX
  -- parser
  have hpar : parseBound r c thr ≤ 33 * X := by unfold parseBound; omega
  -- side
  have hside : Side.sideBound r c ≤ 1440 * X ^ 2 := by
    have h1 := Side.sideBound_le r c
    have h2 : (r + c + 1) ^ 2 ≤ (3 * X) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : (3 * X) ^ 2 = 9 * X ^ 2 := by ring
    omega
  -- writer
  have hwr : MatrixTableWriter.writerBound (SquarePadding.side r c) (SquarePadding.side r c)
      (Unit4Shell.SquareWriter.callbackBound (SquarePadding.side r c) (SquarePadding.side r c)
        r c (r * c)) ≤ 116815047494580 * X ^ 12 := by
    have h1 := Unit4Shell.SquareWriter.square_clock_polynomial (n := c) hr0
    set s := r + c with hs
    have hs2 : s ≤ 2 * X := by omega
    have hq : 5 * s + s ^ 2 + 1 ≤ 15 * X ^ 2 := by nlinarith [Nat.mul_le_mul hs2 hs2]
    have hq2 : (5 * s + s ^ 2 + 1) ^ 2 ≤ (15 * X ^ 2) ^ 2 := Nat.pow_le_pow_left hq 2
    have hq3 : (15 * X ^ 2) ^ 2 = 225 * X ^ 4 := by ring
    have hin : 4 * s + 80 * (5 * s + s ^ 2 + 1) ^ 2 + 1 ≤ 18009 * X ^ 4 := by omega
    have hcube : (4 * s + 80 * (5 * s + s ^ 2 + 1) ^ 2 + 1) ^ 3 ≤ (18009 * X ^ 4) ^ 3 :=
      Nat.pow_le_pow_left hin 3
    have hc3 : (18009 * X ^ 4) ^ 3 = 5840752374729 * X ^ 12 := by ring
    omega
  -- header
  have hhdr : headerBound E thr ≤ 300 * X ^ 2 := by
    unfold headerBound
    rw [natField_pow_length]
    have h1 : (3 * 2 ^ E + 5) * (E + 1) ≤ (12 * X + 5) * (4 * X + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (12 * X + 5) * (4 * X + 1) ≤ 85 * X ^ 2 := by nlinarith [hX2]
    omega
  omega

/-- The explicit constants. -/
def squareCP : ℕ := 10 ^ 15
def squareEP : ℕ := 12

/-- **Segment 4: `SquarePost` proved** for the ONE fixed machine `squareMachine` with the explicit
constants `squareCP = 10^15`, `squareEP = 12`. -/
theorem squarePost : SquarePost squareMachine squareCP squareEP := by
  intro I hI
  exact BitMachine.outputsWithin_mono _ (full_outputs I hI) (fullBound_le I hI)

#print axioms stage_sw
#print axioms full_run
#print axioms full_outputs
#print axioms fullBound_le
#print axioms squarePost

end Paper2.ASquare.Post

/-! ## Segment 4: T01 and T24 (square option) with no open machine contract -/

namespace Paper2.ASquare

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEndpoint

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **T01, square option, closed machine.** `T01_square` instantiated with the fixed post machine
`Post.squareMachine` and `Post.squarePost`; every other premise exactly as `ASquare.T01_square`. -/
theorem T01_square_closed (TM : TapeModel) (hDA1 : DA1 D B TM)
    (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hA3 : Unit4Shell.Shells.H_A3 B.degreeBound (sourceGap D B)) (k : ℕ) (hk : 1 ≤ k) :
    T01Square D B TM L k :=
  T01_square D B TM hDA1 L hDA2 hA3 k hk Post.squareMachine Post.squareCP Post.squareEP
    Post.squarePost

/-- **T24, square option, closed machine.** `T24_square` instantiated with the fixed post machine;
every other premise exactly as `ASquareT24.T24_square`. -/
theorem T24_square_closed (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hA3 : Unit4Shell.Shells.H_A3 B.degreeBound (sourceGap D B))
    (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    T24Square D B L cs c :=
  T24_square D B L hDA2 hA3 cs c hc0 hc Post.squareMachine Post.squareCP Post.squareEP
    Post.squarePost

#print axioms T01_square_closed
#print axioms T24_square_closed

end Paper2.ASquare
