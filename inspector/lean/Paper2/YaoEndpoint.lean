import Paper2.YaoClockPoly
import Paper2.YaoMaterializationBounds

/-! Unit 5 segment Y9 (lane a-yao-owner-3): the machine clauses of T30
(`yao:lift`), U21 (`yao:counts`, machine schedule) and U22 (`yao:dimensions`,
machine costs except source / clone complexity), obtained by EXACT reuse of the
admitted `YaoMaterialization` / `YaoMaterializationBounds` declarations
(`materialize_yes_bound`, `materialize_no_success`, `materialize_length_le`,
`serializedTape_length_le`) with the physical machine now in hand:

* the machine is the ONE fixed program `yaoFramed t lambda` per `(t, lambda)` of
  segment Y8 (`physical_yao_framed`), charged only with the code `encode x` and
  the raw tape `bits.val`;
* its clock is polynomial in `|encode x| + |bits.val|` (segment Y9-clock,
  `frameClock_poly_input`);
* the printed word is `encodeInstance (yaoInstanceDraft t lambda x bits)`.

Scope (stated as premises, never hidden):
* the lock's `t ≥ 4` is a hypothesis of every theorem here;
* valid upstream code only (root ruling R-Y2): the machine's input is the code
  `encode x` of a genuine source `x : YaoSource t`; malformed words are outside
  the scope;
* `0 < x.1` (nonempty vertex set, YA:113) where the printed word must decode;
* `yaoInstanceDraft` / `yaoLanguageDraft` are DRAFTs (R-Y3 format, pending
  D-A4 / D-Y3); nothing here adopts them.

No T25 / T26 / T30 / U21 / U22 row is closed by this file: the source reduction
(T26 / X05), the clone machine and the randomized-algorithm packaging (D-A1) are
outside it. -/

noncomputable section

namespace Paper2.YaoEndpoint

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.Yao
open Paper2.YaoLookup
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoMaterialization
open Paper2.YaoSourceCodec
open Paper2.YaoMachine
open Paper2.YaoFrame

/-- T30 machine clause (`yao:lift`, "for fixed `t, lambda`, construction takes
polynomial time on every tape and prints `O_{t,lambda}(|V| H^4)` entries"):
ONE fixed program per `(t, lambda)`, one polynomial, every valid source code and
every tape; the run halts with the exact final bank whose output cell holds the
printed instance, and the printed table has the admitted quartic length bound. -/
theorem yao_lift_machine (t lambda : ℕ) (ht : 4 ≤ t) :
    ∃ C d : ℕ, ∀ (x : YaoSource t) (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda),
      (∃ total ≤ C * ((encode x).length + bits.val.length + 1) ^ d, ∃ c',
        ((advance (yaoFramed t lambda))^[total])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel)),
            framedControl t lambda, framedInit lambda x bits.val⟩ :
            TM2.Cfg (fun _ : FStack t lambda => Bool) _ _) =
          ⟨none, c', framedOut lambda x bits⟩) ∧
      framedOut lambda x bits (.inl (.inr .output)) =
        encodeInstance (yaoInstanceDraft t lambda x bits) ∧
      (yaoInstanceDraft t lambda x bits).table.length ≤
        x.1 * (16 * Paper2.YaoResources.entryCoefficient t lambda) * (max 1 x.2.1) ^ 4 := by
  obtain ⟨C, d, hC⟩ := Paper2.YaoClockPoly.frameClock_poly_input t lambda (by omega)
  refine ⟨C, d, fun x bits => ⟨?_, framedOut_output lambda x bits,
    materialize_length_le t lambda (by omega) x.2.2 bits⟩⟩
  obtain ⟨total, htot, c', hrun⟩ := physical_yao_framed t lambda (by omega) x bits
  exact ⟨total, htot.trans (hC x bits), c', hrun⟩

/-- T30 YES clause on the printed word: a balanced source colouring puts the
machine's output word in the DRAFT language (`Dalt .alice ≤ B`), on every tape.
Exact reuse of the admitted `materialize_yes_bound`. -/
theorem yao_lift_yes (t lambda : ℕ) (ht : 4 ≤ t) (x : YaoSource t) (hv : 0 < x.1)
    (colour : Fin x.1 → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤ colourFiberCard (fun i => colour (x.2.2 e i)) c)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    framedOut lambda x bits (.inl (.inr .output)) ∈ yaoLanguageDraft := by
  rw [framedOut_output, framed_language_iff lambda x hv bits]
  exact materialize_yes_bound t lambda (by omega) x.2.2 colour hbalanced bits

/-- T30 NO clause on the printed word: if the source has no proper
`S`-colouring, then with probability at least `1 - 2^(1-lambda)` over the exact
serialized tape law, the machine's output word decodes to an instance whose
table has `Dalt .alice ≥ threshold + 2t - 6`.  Exact reuse of the admitted
`materialize_no_success`. -/
theorem yao_lift_no (t lambda : ℕ) (ht : 4 ≤ t) (hlambda : 0 < lambda)
    (x : YaoSource t) (hv : 0 < x.1)
    (hno : ∀ colour : Fin x.1 → Fin (2 ^ (2 ^ t - 1)), ∃ e c, ∀ i, colour (x.2.2 e i) = c) :
    1 - 2 * (1 / 2 : ℝ) ^ lambda ≤
      (serializedTapeLaw t (paddedEdgeBits x.2.1) lambda).prob (fun bits =>
        ∃ i, decodeInstance (framedOut lambda x bits (.inl (.inr .output))) = some i ∧
          i.threshold + 2 * t - 6 ≤
            Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) := by
  have key : (fun bits : SerializedTape t (paddedEdgeBits x.2.1) lambda =>
        ∃ i, decodeInstance (framedOut lambda x bits (.inl (.inr .output))) = some i ∧
          i.threshold + 2 * t - 6 ≤
            Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) =
      (fun bits => (2 * paddedEdgeBits x.2.1 + 4 * t + 2) + 2 * t - 6 ≤
          Dalt .alice (materialize t lambda x.2.2 bits).matrix) := by
    funext bits
    apply propext
    rw [framedOut_output, decode_framed lambda x hv bits]
    constructor
    · rintro ⟨i, hi, hc⟩
      cases Option.some.inj hi
      simpa only [yaoInstanceDraft, Paper2.EncodedSelectedOutput.tableGame_eq_matrix] using hc
    · intro hc
      refine ⟨yaoInstanceDraft t lambda x bits, rfl, ?_⟩
      simpa only [yaoInstanceDraft, Paper2.EncodedSelectedOutput.tableGame_eq_matrix] using hc
  rw [key]
  exact materialize_no_success t lambda ht hlambda x.2.2 hno

/-- U21 / U22 machine clauses: the header the machine prints (decoded from its
output word) carries exactly the lock's dimensions `|Rows| = |V| N_A`,
`|Cols| = q H N_B` and threshold `B = 2b + 4t + 2`; the table is the admitted
`materialize` object with the admitted quartic bound; the charged tape has
exactly `tapeBitCount` bits with the admitted cubic bound.  All counts are
produced inside the one fixed program from the code (Y6 prelude, Y8 header);
nothing is supplied. -/
theorem yao_dimensions_machine (t lambda : ℕ) (ht : 4 ≤ t) (x : YaoSource t) (hv : 0 < x.1)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    decodeInstance (framedOut lambda x bits (.inl (.inr .output))) =
        some (yaoInstanceDraft t lambda x bits) ∧
      (yaoInstanceDraft t lambda x bits).rows =
        x.1 * selectorCount t (paddedEdgeBits x.2.1) lambda ∧
      (yaoInstanceDraft t lambda x bits).cols =
        2 ^ (t - 1) * paddedEdgeCount x.2.1 * payloadCount t (paddedEdgeBits x.2.1) lambda ∧
      (yaoInstanceDraft t lambda x bits).threshold = 2 * paddedEdgeBits x.2.1 + 4 * t + 2 ∧
      (yaoInstanceDraft t lambda x bits).table = (materialize t lambda x.2.2 bits).bits ∧
      (yaoInstanceDraft t lambda x bits).table.length ≤
        x.1 * (16 * Paper2.YaoResources.entryCoefficient t lambda) * (max 1 x.2.1) ^ 4 ∧
      bits.val.length = tapeBitCount t (paddedEdgeBits x.2.1) lambda ∧
      bits.val.length ≤ (8 * Paper2.YaoResources.bitCoefficient t lambda) * (max 1 x.2.1) ^ 3 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, materialize_length_le t lambda (by omega) x.2.2 bits,
    bits.property, serializedTape_length_le t x.2.1 lambda (by omega) bits⟩
  rw [framedOut_output]
  exact decode_framed lambda x hv bits

end Paper2.YaoEndpoint

end

#print axioms Paper2.YaoEndpoint.yao_lift_machine
#print axioms Paper2.YaoEndpoint.yao_lift_yes
#print axioms Paper2.YaoEndpoint.yao_lift_no
#print axioms Paper2.YaoEndpoint.yao_dimensions_machine
