import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_transducer_polytime

namespace PvsNP.Units.tc_closure_pshuffle_p

def pick (q : Bool) : List Bool → List Bool
  | [] => []
  | b::bs => (if q then [b] else []) ++ pick (!q) bs

theorem poly (q : Bool) : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (pick q) := by
  apply PvsNP.Units.m2_transducer_polytime Bool (fun s b => (!s, if s then some b else none)) (fun _ => none) pick _ _ q
  · intro s; rfl
  · intro s b xs; cases s <;> rfl

def even (x : List Bool) := x.foldl (fun q _ => !q) true = true

theorem unzip (x : List Bool) (he : even x) :
    (pick true x).length = (pick false x).length ∧
      x = (List.zipWith (fun a b => [a,b]) (pick true x) (pick false x)).flatten := by
  match x with
  | [] => exact ⟨rfl,rfl⟩
  | [_] => contradiction
  | a::b::xs =>
    obtain ⟨hlen, hz⟩ := unzip xs he
    simp [pick, hlen, hz.symm]

theorem recover (u v : List Bool) (h : u.length = v.length) :
    let x := (List.zipWith (fun a b => [a,b]) u v).flatten
    even x ∧ pick true x = u ∧ pick false x = v := by
  induction u generalizing v with
  | nil => cases v <;> simp_all [even,pick]
  | cons a us ih =>
    cases v with
    | nil => simp at h
    | cons b vs =>
      obtain ⟨he, hu, hv⟩ := ih vs (by simpa using h)
      exact ⟨he, congrArg (a :: ·) hu, congrArg (b :: ·) hv⟩

end PvsNP.Units.tc_closure_pshuffle_p

theorem PvsNP.Units.tc_closure_pshuffle_p :
∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P →
  ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧ x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PvsNP.P := by
  intro L R hL hR
  let A : Language Bool := {x | tc_closure_pshuffle_p.pick true x ∈ L}
  let B : Language Bool := {x | tc_closure_pshuffle_p.pick false x ∈ R}
  let E : Language Bool := {x | tc_closure_pshuffle_p.even x}
  have hA := m2_p_down_closed A L ⟨_, tc_closure_pshuffle_p.poly true, fun _ => Iff.rfl⟩ hL
  have hB := m2_p_down_closed B R ⟨_, tc_closure_pshuffle_p.poly false, fun _ => Iff.rfl⟩ hR
  have heP : E ∈ PvsNP.P := m2_dfa_in_p Bool (fun q _ => !q) true id
  have result := m2_p_inter E (A ⊓ B) heP (m2_p_inter A B hA hB)
  have eqLang : ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧ x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L ∧ v ∈ R} : Language Bool) = E ⊓ (A ⊓ B) := by
    ext x
    constructor
    · rintro ⟨u,v,h,rfl,hu,hv⟩
      obtain ⟨he,h1,h2⟩ := tc_closure_pshuffle_p.recover u v h
      refine ⟨he, ?_, ?_⟩
      · change tc_closure_pshuffle_p.pick true _ ∈ L
        rwa [h1]
      · change tc_closure_pshuffle_p.pick false _ ∈ R
        rwa [h2]
    · rintro ⟨he,h1,h2⟩
      obtain ⟨hl,hz⟩ := tc_closure_pshuffle_p.unzip x he
      exact ⟨_,_,hl,hz,h1,h2⟩
  rw [eqLang]
  exact result
