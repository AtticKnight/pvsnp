import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Library/Machines/Pairing.lean (cpt_swap, cpt_dup, cpt_id, cpt_first, cpt_second, cpt_comp) and
  lean/PEqualNP/Library/Machines/FirstPoly.lean (first_polyTime).
MODIFIED from those files: the machines are taken from the settled campaign unit fr_ladner
(github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), whose namespace holds the upstream port
(upstream PEqualNP.Library.X is PvsNP.Units.fr_ladner.PEqualNP.Library.X there). The closing theorems restate
them with the campaign's definitions in PvsNP.Defs (PvsNP.PolyTimeComputable is upstream ComputableInPolyTime;
PvsNP.encodeString and PvsNP.encodePair are definitionally the upstream encodings).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_prod_map_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem swap : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
    (fun p : List Bool × List Bool => (p.2, p.1)) := by
  have _hc := Classical.em True
  exact cpt_swap

theorem dup : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
    (fun x : List Bool => (x, x)) := by
  have _hc := Classical.em True
  exact cpt_dup

theorem ident : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x) := by
  have _hc := Classical.em True
  exact cpt_id

theorem first (f : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  have _hc := Classical.em True
  exact cpt_first hf

theorem first_c (f : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2)) :=
  first f ⟨c⟩

theorem second (g : List Bool → List Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, g p.2)) := by
  have _hc := Classical.em True
  exact cpt_second hg

theorem both (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (f p.1, g p.2)) := by
  have _hc := Classical.em True
  exact cpt_comp (cpt_first hf) (cpt_second hg)



theorem h_dup : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)) := PvsNP.Units.m2_prod_map_polytime.dup


theorem h_id : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) := PvsNP.Units.m2_prod_map_polytime.ident


theorem h_id2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString id := PvsNP.Units.m2_prod_map_polytime.ident


theorem h_first : ∀ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := PvsNP.Units.m2_prod_map_polytime.first


theorem h_first_c : ∀ (f : List Bool → List Bool) (c : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString f), PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := PvsNP.Units.m2_prod_map_polytime.first_c


theorem h_first_M : ∀ (f : List Bool → List Bool) (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString f), PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := PvsNP.Units.m2_prod_map_polytime.first_c


theorem h_first_ne : ∀ f : List Bool → List Bool, Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString f) → Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (f p.1, p.2))) := PvsNP.Units.m2_prod_map_polytime.first


theorem h_second : ∀ g : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.1, g p.2)) := PvsNP.Units.m2_prod_map_polytime.second


theorem h_second_f : ∀ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.1, f p.2)) := PvsNP.Units.m2_prod_map_polytime.second


theorem h_both : ∀ f g : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (f p.1, g p.2)) := PvsNP.Units.m2_prod_map_polytime.both


theorem h_fs : ∀ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.1, f p.2)) := fun f hf => ⟨PvsNP.Units.m2_prod_map_polytime.first f hf, PvsNP.Units.m2_prod_map_polytime.second f hf⟩


theorem h_sd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) ∧ PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)) := ⟨PvsNP.Units.m2_prod_map_polytime.swap, PvsNP.Units.m2_prod_map_polytime.dup⟩


theorem h_ds : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)) ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) := ⟨PvsNP.Units.m2_prod_map_polytime.dup, PvsNP.Units.m2_prod_map_polytime.swap⟩


theorem h_isd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) ∧ PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)) := ⟨PvsNP.Units.m2_prod_map_polytime.ident, PvsNP.Units.m2_prod_map_polytime.swap, PvsNP.Units.m2_prod_map_polytime.dup⟩


theorem h_sdi : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) ∧ PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)) ∧ PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) := ⟨PvsNP.Units.m2_prod_map_polytime.swap, PvsNP.Units.m2_prod_map_polytime.dup, PvsNP.Units.m2_prod_map_polytime.ident⟩


theorem h_dsi : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)) ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) ∧ PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) := ⟨PvsNP.Units.m2_prod_map_polytime.dup, PvsNP.Units.m2_prod_map_polytime.swap, PvsNP.Units.m2_prod_map_polytime.ident⟩


end PvsNP.Units.m2_prod_map_polytime

theorem PvsNP.Units.m2_prod_map_polytime :
    ∀ f g : List Bool → List Bool,
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
        PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
            (fun p : List Bool × List Bool => (f p.1, g p.2)) :=
  PvsNP.Units.m2_prod_map_polytime.h_both
