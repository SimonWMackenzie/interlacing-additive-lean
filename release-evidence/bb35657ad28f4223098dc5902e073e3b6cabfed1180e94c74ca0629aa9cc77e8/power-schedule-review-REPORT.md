# Independent review: variable unary power and resource printer

Date: 2 November 2026. Reviewer: power-schedule worker, independent of
the unary-power constructor. Result: **accepted as concrete producer
components at the exact interfaces below; no correctness findings**.
Both pinned source snapshots independently compiled with Lean 4.30.0,
followed by the additional independent stack/boundary audit.

This review does not certify the full v43 endpoint. Root retains source
correspondence, production integration and fresh dependency replay.

## Exact accepted interfaces

`CurrentV43.PowerMachine.machine` is one fixed finite Boolean-stack
machine, independent of input base `b` and exponent `e`. Its physical
input is a bank encoding of two unary words. For every `b,e : Nat`,
without arithmetic or machine-result hypotheses:

```lean
machine.OutputsWithin (input b e)
  (List.replicate (b^e) true) (clock b e)
```

Here `input b e` has exactly `2*(b+e)+2` bits, and

```lean
clock b e = 20*(input b e).length+6*b+6*e+40+
  MatrixWeightedPower.powerBound b e
clock b e <= 256*(b+e+b^e+1)^3
```

For `2<=b`, the additional accepted bound is
`clock b e <= b^(3*e+17)`. This hypothesis is correctly restricted: the
zero/one bases still satisfy the general output-sensitive bound.
The name `outputs_polynomial` denotes this polynomial in input plus
output size; it is not an input-length polynomial-time claim for
arbitrary variable exponents.

`CurrentV43.PowerMachine.resourceMachine C` is a fixed physical machine
for each fixed `C`. It takes the same bank encoding of unary `n,K` and
outputs `List.replicate ((n+2)^(C*(K+1))) true`. The accepted bounds are

```lean
resourceClock C n K <= 512*(n+K+C+(n+2)^(C*(K+1))+1)^3
```

and, when `1<=C`,

```lean
resourceClock C n K <= (n+2)^((3*C+16)*(K+1))
```

No `OutputsWithin` premise or assumed callback remains in either final
producer theorem. The interfaces promise canonical two-field inputs;
they do not declare an all-word result or clock on malformed encodings.

## Statement and implementation read-back

The public input fields are physically projected by two existing field
machines, copied by the existing fork controller, and packed as the
literal separated word `true^b ++ false :: true^e`. The parser consumes
that word, writes the unary base and exponent, and physically pushes one
accumulator mark. The accumulator is not supplied by a constructor.

The eight-cell parser bank is exactly
`[[true], true^b, [], [], [], [], true^e, []]`. The existing seven-stack
`MatrixWeightedPower.program` embeds into cells 0--6; cell 7 is the
consumed parser input. The embedding is injective. Its starting bank
equality is proved against the entire bank, and the final arithmetic
bank has no unspecified cell.

The independent `full_exit_bank` lemma proves the final eight cells are
exactly
`[true^(b^e), true^b, [], [], [], [], [], []]`. The base is intentionally
retained; all four arithmetic scratch cells, the exponent cell and the
parser input are empty. Unpairing scratch belongs to a disjoint region
of the composed machine, whose composition theorem initializes the
power machine's private cells empty. No residue is assumed away.

The only finite control consists of finite parser labels, the existing
finite arithmetic labels and Boolean tuples. The data `b,e,n,K` occur
on physical stacks. The resource adapter computes `n+2` and `C*(K+1)`
through existing literal expression machines, then calls the same
separated power machine. Fixed `C` selects a program, not a runtime
natural-number register.

The charged clock identity includes both field projections, fork work,
separated-word construction, the two linear composition transfers,
parser work, one handoff, and `powerBound`. In particular the unpair
cost is `20*input.length+3*b+3*e+33`; transfer and parser costs bring it
to the displayed final `20*input.length+6*b+6*e+40+powerBound`.

The upstream power proof handles base zero explicitly in its polynomial
cap bound. Its initial accumulator is one; empty exponent fuel yields
one, and positive exponent fuel with zero base yields zero. No
positivity premise was lost in the adapter.

## Independent checks

`CurrentV43/PowerMachine.lean` and `CurrentV43/ResourcePower.lean` here
are immutable copied snapshots, with hashes equal to their author's
stable files. They were replayed sequentially into this private object
tree, with this directory first in `LEAN_PATH` and the repository's
existing dependency object paths following. This is a fresh compile of
the two candidate modules, not a clean rebuild of every dependency.

`PowerMachineAudit.lean` additionally checks noninput blank initialization,
the complete eight-cell final bank, and these actual-machine boundary
instances: `0^0`, `0^(e+1)`, `b^0`, `1^e`, resource `C=0`, and resource
`n=K=0`. All 16 printed axiom sets are exactly
`[propext, Classical.choice, Quot.sound]`.

Successful logs: `replay.log`, `resource-replay.log`, `audit.log`.
The replay contains only two harmless unused-simp-argument warnings.
The initial audit attempt had an ambiguous unqualified name `outputs`;
it was qualified without changing either reviewed source. That failed
attempt is preserved as `audit-initial.log`.

No production file, shared build, Git state or other worker's source was
changed. No private compiler remains running.

## SHA256 identities

| File | SHA256 |
| --- | --- |
| `CurrentV43/PowerMachine.lean` | `E569493D11BCC29D402095831EC66E6A13B9918FE1B65AEBC25962CA68EE42A4` |
| `CurrentV43/ResourcePower.lean` | `D593936E25BBD194DEFA8A7303E4959143577E0CB56B82629DE0B77A033D1FB1` |
| `PowerMachineAudit.lean` | `5C2720B64159CC6C9DDEE391DA4A54849AE96E2BB5E7D0E59EAB0534D1E8AE4F` |
| `replay.log` | `3449FE8337493F6D69E90440CA45DFC3F461460679F6947E17367614D0FF3DC7` |
| `resource-replay.log` | `7C127F78FB45C52DDD160A59585BC605819FD0F549489EC2667D75EC54CACF12` |
| `audit.log` | `5221B8296EBD03EA6281B9A0E44783AC47C39C801E963A07D50BC82CB620958B` |
