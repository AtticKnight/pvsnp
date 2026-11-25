# AUDIT: the reading list of the definitions root

**Status: not yet human-audited.** No person has signed this list, so the campaign's page
(<https://make.fun/desk/pvsnp>) shows "not yet human-audited" beside every unit of this campaign.

A unit's statement is checked by the Lean kernels: a credited unit means its file was checked
against the posted statement, nothing more. What a statement *means* rests on the definitions it
mentions. This file is that surface: every definition of this tree a statement may mention, in
reading order, each with the sentence it formalises and where that sentence comes from. A person
who has read the Lean source of each entry below and agrees that it says what its sentence says
can sign the list; that signature is what turns the label off.

The source is `PvsNP/Defs/*.lean`, module `PvsNP.Defs`. A definitions module imports only Mathlib
and other definitions modules and holds definitions only: no theorem and no axiom.

## How to read it

- Every entry names a Lean declaration by its full name. Read the declaration and its docstring
  in the module named in the section heading.
- "Rests on" names the Mathlib declarations the entry unfolds to. They are Mathlib's, pinned at
  commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`lakefile.toml`), and part of what a signer
  reads.
- "Choices" names where the Lean differs from the textbook sentence, and why the difference does
  not change the class.
- Sources: Sipser, *Introduction to the Theory of Computation* (3rd ed.); Arora and Barak,
  *Computational Complexity: A Modern Approach* (2009). The sentences below are this project's
  wording of the textbook notion, with the section it comes from.

## 1. Writing inputs and answers (`PvsNP.Defs.Encoding`)

Every problem here is a language over the binary alphabet. A problem about other objects
(formulas, graphs) states its own encoding into binary strings, and that encoding is part of the
statement that uses it, read with that statement, not here.

- `PvsNP.encodeString`: a binary string is written as itself, one symbol per bit. Rests on
  `Computability.encodingList`.
- `PvsNP.encodePair`: a pair of binary strings `(x, w)` is written as `x` followed by `w`, over
  the alphabet `Bool ⊕ Bool` (bits of `x` tagged `Sum.inl`, of `w` tagged `Sum.inr`); its length
  is `x.length + w.length`. Rests on `Computability.encodingProd`, `Computability.encodingList`.
- `PvsNP.encodeAnswer`: a yes/no answer `b` is written as the one-symbol string `[b]`. Rests on
  `Computability.encodeBool`.

## 2. Polynomial-time computability (`PvsNP.Defs.Machine`)

- `PvsNP.PolyTimeComputable ea eb f`: "f is computable in polynomial time": some Turing machine,
  given the written input `ea a`, halts with the written output `eb (f a)` within `q(|ea a|)`
  steps for a fixed polynomial `q` (Sipser §7.4, polynomial time computable function; Arora and
  Barak §1.2 and §1.5). Rests on `Turing.TM2ComputableInPolyTime`, `Turing.TM2ComputableAux`,
  `Turing.FinTM2`, `Turing.TM2OutputsInTime`, `Turing.initList`, `Turing.haltList`,
  `Turing.FinTM2.step`, `Turing.TM2.step`, `Turing.TM2.Stmt`, `StateTransition.EvalsToInTime`,
  `StateTransition.EvalsTo`, `Polynomial.eval`.
  - Choices: the machine is Mathlib's multi-stack machine (finitely many stacks, one holding the
    input and one the output), not a single tape. A machine with two or more stacks simulates a
    multitape Turing machine with polynomial overhead and the other way round, so the polynomial
    classes are the same; the single-tape notions of section 4 exist so that this can be stated
    and checked as units. A step executes one of the machine's finitely many statements, a bounded
    number of elementary stack operations: a constant factor. On halting the machine must hold
    exactly the output on its output stack, every other stack empty and its internal state reset
    (`Turing.haltList`): stricter than the textbook, at polynomial cost.

## 3. The classes (`PvsNP.Defs.Classes`, `PvsNP.Defs.Reductions`)

A language is Mathlib's `Language Bool`, a set of binary strings; its complement `Lᶜ` is every
binary string not in it.

- `PvsNP.PolyTimeDecidable L`: "L is decidable in polynomial time": some yes/no function on
  strings that answers yes exactly on the members of `L` is computable in polynomial time
  (Sipser §7.2). Rests on `PvsNP.PolyTimeComputable`, `PvsNP.encodeString`, `PvsNP.encodeAnswer`,
  `Language`.
- `PvsNP.P`: "P is the class of languages decidable in polynomial time by a deterministic Turing
  machine" (Sipser §7.2; Arora and Barak §1.5).
- `PvsNP.PolyTimeVerifier L V p`: "V is a polynomial-time verifier for L": `V` runs in polynomial
  time on (input, certificate) pairs, and `x ∈ L` exactly when some certificate `w` with
  `|w| ≤ p(|x|)` makes `V` accept `(x, w)` (Sipser §7.3; Arora and Barak Definition 2.1).
  - Choices: `p` is a `Polynomial ℕ`, written out, never any function bounded by a polynomial: an
    arbitrary bound could hide an undecidable set of lengths and put undecidable languages in NP.
    Natural-number coefficients lose nothing: every polynomial bound is dominated by one with
    natural coefficients. `V`'s time is polynomial in `|x| + |w|`, so with `|w| ≤ p(|x|)` it is
    polynomial in `|x|`. The certificate length is at most `p(|x|)`, not exactly: the same class.
- `PvsNP.NP`: "NP is the class of languages that have polynomial-time verifiers" (Sipser §7.3;
  Arora and Barak Definition 2.1).
- `PvsNP.coNP`: "coNP is the class of languages whose complement is in NP" (Arora and Barak §2.6).
- `PvsNP.KarpReducible L₁ L₂`: "L₁ is polynomial-time many-one (Karp) reducible to L₂": some
  polynomial-time computable function `f` on strings has `x ∈ L₁ ⇔ f(x) ∈ L₂` for every `x`
  (Sipser §7.4, polynomial time mapping reducibility; Arora and Barak §2.2).
- `PvsNP.NPHard L`: "L is NP-hard: every language in NP is polynomial-time reducible to L", with
  Karp reductions (Sipser §7.4; Arora and Barak §2.2).
- `PvsNP.NPComplete L`: "L is NP-complete: L is in NP and NP-hard" (Sipser §7.4; Arora and Barak
  §2.2).

## 4. The single-tape side (`PvsNP.Defs.SingleTape`)

The textbook classes are defined with single-tape machines. These names state the bridge between
them and the classes of section 3; each mirrors its section 3 counterpart with
`PvsNP.SingleTape.PolyTimeComputable` in place of `PvsNP.PolyTimeComputable`.

- `PvsNP.SingleTape.Machine A B`: "a single-tape Turing machine has a finite set of states with a
  start state, a finite tape alphabet with a blank, an input alphabet that does not contain the
  blank, and a transition function" (Sipser §3.1). Its fields: `Γ` (tape alphabet), `Λ` (states),
  `blank` (the blank, `Γ`'s `default`), `start` (the start state, `Λ`'s `default`), `fintypeΓ`,
  `fintypeΛ` (both finite), `inp` and `out` (the tape symbols of input and output letters),
  `inp_injective`, `out_injective`, `inp_ne_blank`, `out_ne_blank` (letters are distinct symbols,
  none the blank) and `δ` (the transition function). Rests on `Turing.TM0.Machine`,
  `Turing.TM0.Stmt`, `Turing.Dir`.
  - Choices: Mathlib's machine either writes a symbol or moves the head in one step; the
    textbook's does both. One textbook step is at most two of these: a factor of two. It halts
    when `δ` answers `none` rather than in accept and reject states; deciders answer `[true]` or
    `[false]` on the tape instead.
- `PvsNP.SingleTape.Machine.inhabitedΓ`, `PvsNP.SingleTape.Machine.inhabitedΛ`: the blank and the
  start state, as Lean's `default`.
- `PvsNP.SingleTape.Machine.Cfg`: a configuration: the state and the tape. Rests on
  `Turing.TM0.Cfg`, `Turing.Tape`.
- `PvsNP.SingleTape.Machine.step`: one step; `none` when the machine halts. Rests on
  `Turing.TM0.step`, `Turing.Tape.move`, `Turing.Tape.write`.
- `PvsNP.SingleTape.Machine.init`: "the machine starts in its start state with the input on the
  leftmost cells of an otherwise blank tape, the head on the first input cell" (Sipser §3.1; the
  tape here is infinite both ways, the cells left of the input blank). Rests on `Turing.TM0.init`,
  `Turing.Tape.mk₁`.
- `PvsNP.SingleTape.Machine.Shows c r`: the output: in `c`, the cells from the head rightwards
  hold `r` followed by a symbol that is no output letter. Rests on `Turing.Tape.right₀`,
  `Turing.ListBlank.nth`.
- `PvsNP.SingleTape.Machine.OutputsInTime s r t`: started on `s`, the machine halts within `t`
  steps with the output `r`. Rests on `StateTransition.EvalsToInTime`.
- `PvsNP.SingleTape.PolyTimeComputable ea eb f`: "f is computable in polynomial time on a
  single-tape Turing machine" (Sipser §7.4).
- `PvsNP.SingleTape.PolyTimeDecidable`, `PvsNP.SingleTape.P`, `PvsNP.SingleTape.PolyTimeVerifier`,
  `PvsNP.SingleTape.NP`, `PvsNP.SingleTape.coNP`, `PvsNP.SingleTape.KarpReducible`,
  `PvsNP.SingleTape.NPHard`, `PvsNP.SingleTape.NPComplete`: the sentences of section 3, on
  single-tape machines (Sipser §7.2, §7.3, §7.4).

## 5. The vendored reading list (`CookLevin`)

A statement may also name the definitions of the vendored library `CookLevin` (`vendor/CookLevin/`,
taken from github.com/DominicBreuker/cook-levin-lean at commit
`fb3e61c989d021f8a641a8d99155b953c62a1b74`; `VENDORED.md` names every file changed to build it
here). One group of units is the bridge between its single-tape machine model and Mathlib's TM2.
The names below are that library's own reading list: every definition its headline
`CookLevin.cook_levin : CookLevin.NPcomplete SATStr` (module `CookLevin.Theorem`) is stated with, in
the upstream reading order. The list is not written by hand here: upstream's
`CookLevin/ReadingList.lean` recomputes it from the statement with `#assert_statement_surface` on
every build of the tree, and the build fails unless it is exactly this set. Read each in the module
named in its group; upstream's `GUIDE.md` (at the same commit) explains them.

- The claim (`CookLevin.Basic.StringTM`): `CookLevin.NPcomplete`, `CookLevin.NPhard`,
  `CookLevin.inNP`, `CookLevin.reducesPoly`, `CookLevin.computesInTime`,
  `CookLevin.decidesPairInTime`, `CookLevin.stringTape`, `CookLevin.pairTape`, `CookLevin.symbolsOf`,
  `CookLevin.outputString`.
- Turing machines (`CookLevin.Basic.MachineSemantics`, `CookLevin.Basic.Definitions`): `FlatTM`,
  `flatTM`, its fields `FlatTM.sig`, `FlatTM.tapes`, `FlatTM.states`, `FlatTM.start`, `FlatTM.halt`,
  `FlatTM.trans`; `FlatTMTransEntry` and its fields `FlatTMTransEntry.src_state`,
  `FlatTMTransEntry.src_tape_vals`, `FlatTMTransEntry.dst_state`, `FlatTMTransEntry.dst_write_vals`,
  `FlatTMTransEntry.move_dirs`; `TMMove` and its constructors `TMMove.Lmove`, `TMMove.Rmove`,
  `TMMove.Nmove`; `FlatTMConfig` and its fields `FlatTMConfig.state_idx`, `FlatTMConfig.tapes`;
  `initFlatConfig`, `currentTapeSymbol`, `writeCurrentTapeSymbol`, `moveTapeHead`, `tapeStep`,
  `entryMatchesConfig`, `applyTransitionEntry`, `stepFlatTM`, `haltingStateReached`, `runFlatTM`,
  `validFlatTM`, `flatTMTransEntryValid`, `flatTMOptionSymbolsBounded`.
- Polynomials (`CookLevin.Basic.Definitions`): `inOPoly`, `inO`.
- SAT (`CookLevin.Basic.Definitions`, `CookLevin.SAT.SAT`): `var`, `literal`, `clause`, `cnf`,
  `assgn`, `evalVar`, `evalLiteral`, `evalClause`, `evalCnf`, `satisfiesCnf`, `SAT`.
- SAT as a language of bit strings (`CookLevin.SAT.SATStr`, `CookLevin.Lang.SerializeStr`,
  `CookLevin.SAT.CnfWellFormed`, `CookLevin.SAT.CnfSerialize`): `SATStr`, `SATStr.cnfOf`,
  `CookLevin.Lang.strBits`, `CnfWellFormed.parseTotal`, `CnfWellFormed.wfCnfB`,
  `CnfWellFormed.scanRun`, `CnfWellFormed.scanStep`, `CnfSerialize.decCnf`,
  `CnfSerialize.decCnfAux`, `CnfSerialize.decClause`, `CnfSerialize.scanUnary`.

These are full Lean names: upstream declares most of its machine model and SAT names outside the
`CookLevin` namespace, and the vendored copy keeps every name as upstream has it. The campaign's
reading list is section 1 to 4's declarations and structure fields followed by these 68 names.
The same label applies: no person has read and signed this section either.

## What this list does not cover

- Lean's kernel and Mathlib's definitions beyond the ones named above (`List`, `Bool`, `Set`,
  `Polynomial`, …): trusted as Lean and Mathlib.
- Each unit's statement: it is posted with its own text, its source sentence and a read-back, and
  read on its own.
- The rest of the vendored library: its theorems, and every definition of it outside section 5. A
  statement naming one is refused (`off_reading_list`).

## Prior art

The definitions are this project's own. Two earlier works were read while writing them, and the
module headers name the definitions that follow them, with the source and commit, and how they
were modified:

- formal-conjectures, `FormalConjecturesForMathlib/Computability/Complexity.lean`, at commit
  `1d3feb7ddcfd6d922c49a96b5134dba488b7de1c` (github.com/google-deepmind/formal-conjectures):
  the `Nonempty (Turing.TM2ComputableInPolyTime …)` form, the verifier form of NP and the
  complement form of coNP.
- pequalnp-proofs, `lean/PEqualNP/Defs/Base.lean`, at commit
  `8df87a862bd9a618faecf10ba65bff72706442c9` (github.com/brilliant-hq/pequalnp-proofs): deciding a
  language by a yes/no function, and the shape of Karp reducibility, NP-hardness and
  NP-completeness. This tree is not byte-compatible with that repository's definitions.
