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

**This runs on a preview site for now**, at <https://dev.make.fun>.

## Sending a file today

You can also send your file without a pull request, through make.fun's command line:

1. Get the command line. It is one file, `cli/makefun.mjs`, for Node 22 or later, and every
   bounty's kit on the site carries it. Pick any open bounty from
   <https://dev.make.fun/api/competitions> (you need not enter it), run
   `curl -sSL "https://dev.make.fun/c/<slug>/kit" | tar xz` and work from inside the unpacked
   `<slug>-kit/` folder. Each `makefun …` below is `node cli/makefun.mjs …` there.
2. Run `makefun login --origin https://dev.make.fun`. Its first line opens with `Open <link>` and
   a code. Open the link while signed in to your make.fun account (make one at
   <https://dev.make.fun> if you have none), check the code and approve it, then run the same
   command again until it prints `Connected`.
3. Link your GitHub account at <https://dev.make.fun/profile?tab=identity> and leave it shown on
   your profile. The desk asks for it even for a file sent this way, because accepted work will be
   committed here under that GitHub identity. Until it is linked, the next step answers
   `github_unlinked`.
4. Run `makefun desk next --campaign pvsnp`. It leases you a free unit and prints its card: the
   unit's key and id, its statement and the lease's id. Run the commands below in the same folder,
   where the lease is saved. A lease lapses unless renewed, and `makefun desk beat <lease> --watch`
   renews it while you work.
5. Write `PvsNP/Units/<key>.lean` as "What a unit's file is" below says.
6. `makefun desk check PvsNP/Units/<key>.lean --unit <unit>` lints it on your machine. It is free
   and sends nothing.
7. `makefun desk submit PvsNP/Units/<key>.lean --lease <lease>` sends it to be checked and prints
   the submission's id.
8. `makefun desk status <submission> --wait` waits for the verdict.

If you cannot finish a unit, `makefun desk release <lease> --reason <reason>` lets it go.

## Taking part

The desk reads the pull requests opened here and checks the file each one adds. To send one:

1. Sign in at <https://dev.make.fun> and link the GitHub account you will open the pull request
   from to your make.fun account (your profile's Identity tab). The desk knows whose pull request
   it is reading by that link.
2. Pick a free unit at <https://dev.make.fun/desk/pvsnp>. Each unit shows its key, its statement
   and its weight. You can ask the desk for a lease on it first, or let your pull request take it
   while the unit is free and your account has room for one more.
3. Fork this repository, make a branch from the current `main` and add exactly one file,
   `PvsNP/Units/<key>.lean` (a dash in the unit's key is written as an underscore). Change nothing
   else.
4. Open the pull request against `main`. One unit to a pull request.

The desk reads open pull requests at intervals of a minute or more, checks the file and keeps one
status comment on the pull request, edited as the check goes on: checked and merged, refused with
its reason, or waiting and what it waits on. If yours is refused, push a fix to the same branch
while your lease lasts and the new head is checked as a new attempt. A draft pull request is not
read until it is marked ready.

A pull request from a GitHub account that no make.fun account links is not checked. Its comment
says so, and the desk checks it once the link is made. One still unlinked after a while is closed,
and you can open it again once the link is there.

The first valid file for a unit, by the time the desk received it, takes the unit and is merged by
the desk. A valid file that comes later for the same unit is recorded as a duplicate. It scores
nothing and its pull request is closed. A pull request for a unit that is already settled is closed
unchecked, and its comment says which work settled it.

Accepted work is merged here under its author's GitHub identity, and it scores points for its
author on the campaign's ranking. Points are all it earns for now: there is no paid round.

## What a unit's file is

The file `PvsNP/Units/<key>.lean` is the module `PvsNP.Units.<key>`. It holds one theorem whose
name is the module's name, `PvsNP.Units.<key>`, and whose type is exactly the posted statement. Its
helpers go in the namespace `PvsNP.Units.<key>` (or `PvsNP.Units.<key>_aux`). It imports only
`Mathlib`, `PvsNP.Defs` and `CookLevin`, uses no axiom beyond `propext`, `Quot.sound` and
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
