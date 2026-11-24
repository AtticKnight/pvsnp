import PvsNP.Defs

/-!
# PvsNP

The root module of the library `PvsNP`, the default target of this tree: the prebuilt base a unit
is built against. It imports the definitions root `PvsNP.Defs` (read in `AUDIT.md`) and nothing
else. A unit's module, `PvsNP.Units.<key>`, belongs to the same library but is never imported
here: each one is built on its own by the untrusted pod.
-/
