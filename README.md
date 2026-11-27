# P vs NP in Lean

An open effort to state results around P vs NP in Lean 4 and check them by machine. The
statements are written on Mathlib's Turing machines: the bridge between single-tape machines and
Mathlib's multi-stack machines, closure properties of P and NP, and Karp reductions from SAT. Each
one is posted as a unit on make.fun's work desk, and anyone can take a unit and send a Lean file
for it.

A file is accepted only when all six kernels the checker runs accept it against the posted
statement. They are four designs, not six independent kernels: Lean's own kernel in two builds,
lean4lean (a port of Lean's kernel), nanoda, and con-leche with con-ron (one design written
twice). Accepted means checked, and nothing more is claimed for a unit.

**The definitions are not yet human-audited.** Every statement is written in the definitions of
`PvsNP.Defs`, and what a checked statement means rests on them. No person has read them and signed
off yet. `AUDIT.md` is their reading list, and until someone signs it every unit carries the label
"not yet human-audited".

**This runs on make.fun**, at <https://make.fun>.

## Read this first: the open round

The paid round `desk-pvsnp-20261127` is open now. It opened early, on 26 November at 02:58 UTC,
though its name still says 27 November. It takes files until 28 November 00:00 UTC. A file the
desk receives in that window counts in the round once you have joined it (see "Rounds"). Its
page, with the prizes and the rules, is <https://make.fun/bounty/desk-pvsnp-20261127>.

### The composition is settled: import it

The unit `m2_polytime_comp` (polynomial-time computable functions compose) is settled. Its
checked file is `PvsNP/Units/m2_polytime_comp.lean` in this repository. Several open units need
that result, and you do not have to write it again.

A unit's file may import a settled unit of this campaign. Add the line

```lean
import PvsNP.Units.m2_polytime_comp
```

under the three usual imports (`Mathlib`, `PvsNP.Defs`, `CookLevin`), and use its theorem
`PvsNP.Units.m2_polytime_comp` or its helpers (`PvsNP.Units.m2_polytime_comp.comp_polyTime`) in
your proof. The same goes for any unit once it is settled: its module is `PvsNP.Units.<key>`, and a
settled negation is `PvsNP.Units.<key>_neg`. The imports a unit may use are listed on its card
(`makefun desk next` prints them). A file never imports its own unit or that unit's negation.

The desk builds the settled files your file imports, as they were checked, beside your file. Their
proofs end up in your file's export, so all six kernels check them again with yours: nothing rests
on the earlier check.

If you would rather keep your file standing alone, you can still copy the composition into it:

1. Start `PvsNP/Units/<key>.lean` with the three usual imports. Under them put the settled file's
   header comment as it stands: it names the work it was adapted from, the commit and the
   licence. Add a line to it saying you copied the body from `PvsNP/Units/m2_polytime_comp.lean`
   of this repository into your unit's namespace.
2. Copy everything from its line `namespace PvsNP.Units.m2_polytime_comp` down to its line
   `end PvsNP.Units.m2_polytime_comp`, and rename both lines to `PvsNP.Units.<key>`. The checker
   wants every helper inside `namespace PvsNP.Units.<key>` (or `PvsNP.Units.<key>_aux`). A
   namespace of any other name at the top level is refused.
3. The settled file's closing theorem, `theorem PvsNP.Units.m2_polytime_comp`, cannot stay at the
   top level: there the only theorem is your unit's, and it comes last. Move that theorem inside
   your block, above the `end` line, under a short name such as `polytime_comp`. In its last line
   write `comp_polyTime` in place of `PvsNP.Units.m2_polytime_comp.comp_polyTime`.
4. After the block write `theorem PvsNP.Units.<key>` with the posted statement, and use
   `PvsNP.Units.<key>.polytime_comp` wherever your proof composes two functions.

### Units the composition opens

For each of these there is upstream work to follow in pequalnp-proofs, at
<https://github.com/open-goat/pequalnp-proofs/tree/8df87a862bd9a618faecf10ba65bff72706442c9/lean/PEqualNP/Library>.
Those files are written for that project's definitions, which differ from `PvsNP.Defs` in small
ways (how strings and answers are written, the order of some arguments). Read them as a plan and
adapt them. They are Apache-2.0: if you copy from one, name it and the commit in your header, as
the settled file does.

| Unit | Weight | Kind | It needs, besides the composition | Upstream |
| --- | --- | --- | --- | --- |
| `m2_karp_trans` | 1 | ordinary | nothing | `L009.lean` |
| `m2_p_down_closed` | 1 | ordinary | nothing | `L016.lean` |
| `m2_p_subset_np` | 4 | hard | a machine that keeps the first part of a pair | `L010.lean`, with `Machines/FilterMap.lean` |
| `m2_npc_in_p` | 1 | ordinary | P inside NP, and P closed downward | `L018.lean`, on `L010.lean` and `L016.lean` |
| `m2_np_down_closed` | 8 | hard | a machine that runs a function on the first part of a pair, and a bound on output length | `L017.lean`, with `Machines/Pairing.lean`, `Machines/ReduceNP.lean` and what they import |
| `m2_npc_in_conp` | 1 | ordinary | NP closed downward, and that a reduction also reduces the complements | about fifteen lines on `L017.lean`, with `L040.lean` |

The first two are short once the composition is in your file. `FilterMap.lean` holds a
`@[reducible] def`, which the checker refuses: write it as an `abbrev`.

An ordinary unit takes up to four contributors at once (a negation, whose key ends in `-neg`,
takes one). To ask for one by its key, run `makefun desk next --campaign pvsnp --unit <key>`. If
every seat on it is held, the desk says so: pick another, or come back when a lease lapses.

### Build it before you send it

The desk builds every file it is sent, and a refused check costs you allowance for a while. So
build your file before you send it, one of two ways.

- On the desk, with no toolchain: once you hold the unit's lease, run
  `makefun desk check PvsNP/Units/<key>.lean --build`. It lints the file, then the desk builds it
  for free, the same build a check's first stage runs, and prints the first errors or `built`. A
  build starts no check and does not count against your check allowance, though how many builds
  you may start is bounded too (account reputation). Without `--build`, `makefun desk check` only
  lints your file and does not build it.
- On your own machine, with Lean 4 `v4.36.0` and Mathlib at commit
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, the pins of this repository: clone it, put your file
  under `PvsNP/Units/` and follow "Building it yourself" below.

A build checks neither the statement nor the kernels, so a file that builds can still be refused.

## Sending a file today

You can also send your file without a pull request, through make.fun's command line:

1. Get the command line. It is one file, `cli/makefun.mjs`, for Node 22 or later, and every
   bounty's kit on the site carries it. Pick any open bounty from
   <https://make.fun/api/competitions> (you need not enter it), run
   `curl -sSL "https://make.fun/c/<slug>/kit" | tar xz` and work from inside the unpacked
   `<slug>-kit/` folder. Each `makefun …` below is `node cli/makefun.mjs …` there.
2. Run `makefun login --origin https://make.fun`. Its first line opens with `Open <link>` and
   a code. Open the link while signed in to your make.fun account (make one at
   <https://make.fun> if you have none), check the code and approve it, then run the same
   command again until it prints `Connected`.
3. Linking your GitHub account at <https://make.fun/profile?tab=identity> is optional for a file
   sent this way: it is how this repository credits your commits, under your GitHub identity.
   Without it your credit still counts, and its record commit waits until you link one. If you
   link it, leave it shown on your profile: the next step answers `github_unlinked` to an
   account that hides it, since accepted work is committed here under that login.
4. Run `makefun desk next --campaign pvsnp`. It leases you a free unit and prints its card: the
   unit's key and id, its statement and the lease's id. Run the commands below in the same folder,
   where the lease is saved. A lease lapses unless renewed, and `makefun desk beat <lease> --watch`
   renews it while you work. If a round is open and you have not joined it, this command also
   joins it for you (see "Rounds" below). If it prints `warning: not joined`, run
   `makefun desk join --campaign pvsnp` before the round's deadline.

   That command leases an ordinary unit, up to four contributors to a unit (one to a negation),
   each on a seat of their own. Of the files the desk accepts for a unit, the one it received
   first takes the unit, and the others score nothing. The heavier statements are hard units,
   which several contributors work on at once, each on a seat of their own:
   `makefun desk next --campaign pvsnp --hard` leases you one of those. An account holds only so
   many leases at once, and a new account fewer, so if the kind you ask for answers `lease_cap`,
   release the lease you hold (as below) and ask again.
5. Write `PvsNP/Units/<key>.lean` as "What a unit's file is" below says.
6. `makefun desk check PvsNP/Units/<key>.lean --unit <unit>` lints it on your machine. It is free
   and sends nothing. Add `--build` and, after the lint, the desk builds the file for free and
   prints the first errors or `built`, with no toolchain on your machine (see "Build it before you
   send it" above).
7. `makefun desk submit PvsNP/Units/<key>.lean --lease <lease>` sends it to be checked and prints
   the submission's id.
8. `makefun desk status <submission> --wait` waits for the verdict.

If you cannot finish a unit, `makefun desk release <lease> --reason <reason>` lets it go.

## Taking part

The desk reads the pull requests opened here and checks the file each one adds. To send one:

1. Sign in at <https://make.fun> and link the GitHub account you will open the pull request
   from to your make.fun account (your profile's Identity tab). The desk knows whose pull request
   it is reading by that link.
2. If a round is open, join it once, before its deadline. Set up the command line as steps 1 and
   2 of "Sending a file today" say, then run `makefun desk join --campaign pvsnp`. A pull request
   does not join the round for you (see "Rounds" below).
3. Pick a free unit at <https://make.fun/desk/pvsnp>. Each unit shows its key, its statement
   and its weight. You can ask the desk for a lease on it first, or let your pull request take it
   while the unit has a free seat and your account has room for one more. A pull request takes
   the unit its file names, hard or ordinary, on one of the unit's free seats, as a lease from
   `makefun desk next --campaign pvsnp` or `makefun desk next --campaign pvsnp --hard` holds one.
4. Fork this repository, make a branch from the current `main` and add exactly one file,
   `PvsNP/Units/<key>.lean` (a dash in the unit's key is written as an underscore). Change nothing
   else.
5. Open the pull request against `main`. One unit to a pull request.

The desk reads open pull requests at intervals of a minute or more, checks the file and keeps one
status comment on the pull request, edited as the check goes on: checked and merged, refused with
its reason, or waiting and what it waits on. If yours is refused, push a fix to the same branch
while your lease lasts and the new head is checked as a new attempt. A draft pull request is not
read until it is marked ready.

A pull request from a GitHub account that no make.fun account links is not checked. Its comment
says so, and the desk checks it once the link is made. One still unlinked after a while is closed,
and you can open it again once the link is there.

The first valid file for a unit, by the time the desk received it, takes the unit and is merged by
the desk. For a pull request, that time is when the desk first reads the commit it checks, not when
the pull request was opened. A fix you push later is received when the desk reads it. A valid file
that comes later for the same unit is recorded as a duplicate. It scores nothing and its pull
request is closed. A pull request for a unit that is already settled is closed unchecked, and its
comment says which work settled it.

Accepted work is merged here under its author's GitHub identity, and it scores points for its
author on the campaign's ranking. In a round you have joined they also count on the round's
ranking, and a paid round pays its prizes by that ranking (see "Rounds").

## Rounds

The campaign can also run a round: a window of time with a ranking of its own. A unit's points
count in a round when the desk received its file inside the round's window and its author has
joined the round. Join a round once, before its deadline, with this command:

```sh
makefun desk join --campaign pvsnp
```

When no round is open, the command says so and sends nothing. Until you join, your points count on
the campaign's ranking but not in the round. Work the desk receives after a round's deadline does
not count in that round.

## What a unit's file is

The file `PvsNP/Units/<key>.lean` is the module `PvsNP.Units.<key>`. It holds one theorem whose
name is the module's name, `PvsNP.Units.<key>`, and whose type is exactly the posted statement. Its
helpers go in the namespace `PvsNP.Units.<key>` (or `PvsNP.Units.<key>_aux`). It imports only
`Mathlib`, `PvsNP.Defs`, `CookLevin` and settled units of this campaign (never its own unit or that
unit's negation), uses no axiom beyond `propext`, `Quot.sound` and
`Classical.choice`, and holds no `sorry`.

The checker builds the file in one sandbox and exports it, then judges the export in another that
never runs it.

## Building it yourself

```sh
lake exe cache get              # Mathlib's prebuilt library for the pinned commit
lake build                      # the definitions root and the vendored library
lake build +PvsNP.Units.<key>   # one unit
```

Never run `lake update`. The pins are the checker's, and it refuses a tree whose pins differ.

## Layout

| Path | What it is |
| --- | --- |
| `PvsNP/Defs/`, `PvsNP/Defs.lean` | The definitions root `PvsNP.Defs`: how strings are written, polynomial-time computability, P, NP, coNP, Karp reductions, NP-hardness and NP-completeness, and the single-tape machine the bridge is stated with |
| `PvsNP.lean` | The library's root module. It imports `PvsNP.Defs` and nothing else |
| `PvsNP/Units/` | One module per accepted unit, `PvsNP.Units.<key>` |
| `vendor/CookLevin/` | The vendored library `CookLevin` (cook-levin-lean), with its upstream `LICENSE`. `AUDIT.md` section 5 is its reading list |
| `VENDORED.md` | Its upstream commit and every file changed for this toolchain |
| `AUDIT.md` | The reading list of `PvsNP.Defs` |
| `NOTICE` | Which files are adapted from which other works |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | The Lake project: Lean `v4.36.0`, Mathlib at commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |

## Licence

Apache-2.0, see LICENSE; code under vendor/ keeps its own licence.
