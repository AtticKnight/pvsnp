import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_pair_fork_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem cpt_unpairB_pair :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair unpairB := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  exact PvsNP.Units.m2_pair_build_polytime _ _ h1 h2

end PvsNP.Units.m2_tm_pair_fork_polytime

/-- Pairing two polynomial-time functions on pairs takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_pair_fork_polytime :
    ∀ f g : List Bool × List Bool → List Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString f →
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair (fun p : List Bool × List Bool => (f p, g p)) := by
  intro f g hf hg
  have hfu : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => f (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB s)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_tm_pair_fork_polytime.cpt_unpairB_pair hf
  have hgu : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => g (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB s)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.m2_tm_pair_fork_polytime.cpt_unpairB_pair hg
  have hbuild := PvsNP.Units.m2_pair_build_polytime _ _ hfu hgu
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun a : List Bool × List Bool =>
        (f (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB a.1 a.2)),
         g (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB a.1 a.2)))) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB hbuild
  simpa only [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB, Prod.mk.eta] using hcomp
