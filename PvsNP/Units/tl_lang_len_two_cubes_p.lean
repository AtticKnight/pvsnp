import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.tl_lang_len_square_p
import PvsNP.Units.tl_lang_len_pow_p

/-
Built on the settled units PvsNP.Units.fr_ladner, m2_take_drop_length_polytime, m2_len_le_polytime,
m2_bounded_unary_search_polytime, tl_lang_len_square_p and tl_lang_len_pow_p of github.com/makedotfun/pvsnp.
|x| = a^3 + b^3 iff for some a ≤ |x|: a^3 ≤ |x| and the length of x.drop (a^3) is a cube.
-/

namespace PvsNP.Units.tl_lang_len_two_cubes_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

def sq (p : List Bool × List Bool) : List Bool := mulU (mulU p.2 p.2) p.2

def rem (p : List Bool × List Bool) : List Bool := p.1.drop (sq p).length

def leF (p : List Bool × List Bool) : List Bool :=
  if decide ((sq p).length ≤ p.1.length) then [true] else []

def cuF (g : List Bool → Bool) (p : List Bool × List Bool) : List Bool :=
  if g (rem p) then [true] else []

def Fv (g : List Bool → Bool) (p : List Bool × List Bool) : List Bool :=
  if leF p = [] then [] else cuF g p

def V (g : List Bool → Bool) (p : List Bool × List Bool) : Bool := !(Fv g p).isEmpty

theorem sq_length (p : List Bool × List Bool) : (sq p).length = p.2.length ^ 3 := by
  unfold sq
  rw [PvsNP.Units.tl_lang_len_square_p.mulU_length_eq,
    PvsNP.Units.tl_lang_len_square_p.mulU_length_eq]
  ring

theorem cpt_V (g : List Bool → Bool)
    (hg : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool g) :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (V g) := by
  have hcu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun u : List Bool => mulU (mulU u u) u) :=
    cpt_mulU2 (cpt_mulU2 cpt_id cpt_id) cpt_id
  have hsq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) sq := by
    have h := cpt_comp cpt_snd hcu
    exact h
  have hp1 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (sq p, p.1)) :=
    cpt_pairG hsq cpt_fst
  have hdrop : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun q : List Bool × List Bool => q.2.drop q.1.length) := by
    rw [encodePair_eq]; exact PvsNP.Units.m2_take_drop_length_polytime.2
  have hrem : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) rem := by
    have h := cpt_comp hp1 hdrop
    exact h
  have hle0 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length)) := by
    rw [encodePair_eq]; exact PvsNP.Units.m2_len_le_polytime
  have hle : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => decide ((sq p).length ≤ p.1.length)) := by
    have h := cpt_comp hp1 hle0
    exact h
  have hleF : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) leF := by
    have h := cpt_bitFlag hle
    exact h
  have hg2 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun p : List Bool × List Bool => g (rem p)) := by
    have h := cpt_comp hrem hg
    exact h
  have hcuF : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (cuF g) := by
    have h := cpt_bitFlag hg2
    exact h
  have hp2 : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (leF p, cuF g p)) :=
    cpt_pairG hleF hcuF
  have hF : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x) (Fv g) := by
    have h := cpt_comp hp2 cpt_ifNonempty
    exact h
  have h := cpt_comp hF PvsNP.Units.tl_lang_len_square_p.cpt_nonEmpty
  exact h

theorem V_poly (g : List Bool → Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer g) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (V g) := by
  rw [← encodePair_eq]; exact cpt_V g hg

theorem V_iff (g : List Bool → Bool) (p : List Bool × List Bool) :
    V g p = true ↔ ((sq p).length ≤ p.1.length ∧ g (rem p) = true) := by
  unfold V Fv leF cuF
  by_cases h1 : (sq p).length ≤ p.1.length <;> by_cases h2 : g (rem p) = true <;> simp [h1, h2]

end PvsNP.Units.tl_lang_len_two_cubes_p

theorem PvsNP.Units.tl_lang_len_two_cubes_p :
    ({x : List Bool | ∃ a b : ℕ, a ^ 3 + b ^ 3 = x.length} : Language Bool) ∈ PvsNP.P := by
  obtain ⟨g, hg, hgL⟩ := PvsNP.Units.tl_lang_len_pow_p
  have hg' : ∀ y : List Bool, g y = true ↔ ∃ k : ℕ, y.length = k ^ 3 := fun y => (hgL y).symm
  have hS := PvsNP.Units.m2_bounded_unary_search_polytime (PvsNP.Units.tl_lang_len_two_cubes_p.V g)
    (PvsNP.Units.tl_lang_len_two_cubes_p.V_poly g hg)
  refine ⟨_, hS, fun x => ?_⟩
  change (∃ a b : ℕ, a ^ 3 + b ^ 3 = x.length) ↔
    (List.range (x.length + 1)).any (fun i => PvsNP.Units.tl_lang_len_two_cubes_p.V g (x, List.replicate i true)) = true
  rw [List.any_eq_true]
  simp only [List.mem_range, PvsNP.Units.tl_lang_len_two_cubes_p.V_iff, PvsNP.Units.tl_lang_len_two_cubes_p.rem,
    PvsNP.Units.tl_lang_len_two_cubes_p.sq_length, List.length_replicate, hg', List.length_drop]
  constructor
  · rintro ⟨a, b, h⟩
    have ha : a ≤ a ^ 3 := by
      cases a with
      | zero => omega
      | succ a' => exact Nat.le_self_pow (by norm_num) _
    exact ⟨a, by omega, by omega, b, by omega⟩
  · rintro ⟨i, _, hle, k, hk⟩
    exact ⟨i, k, by omega⟩
