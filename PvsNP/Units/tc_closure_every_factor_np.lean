import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_all_prefixes
import PvsNP.Units.m2_np_reverse_closed

namespace PvsNP.Units.tc_closure_every_factor_np

/-- Every factor of `x` is in `L` exactly when, for every prefix `y` of `x.reverse`, every prefix
of `y.reverse` is in `L`: the prefixes of `x.reverse` are the reverses of the suffixes of `x`, and
a factor is a prefix of a suffix. -/
theorem factor_iff (L : Language Bool) (x : List Bool) :
    (∀ y : List Bool, y <+: x.reverse → ∀ w : List Bool, w <+: y.reverse → w ∈ L) ↔
      ∀ w : List Bool, w <:+: x → w ∈ L := by
  constructor
  · intro h w hw
    obtain ⟨s, u, hsu⟩ := hw
    let t := w ++ u
    have hwt : w <+: t := ⟨u, rfl⟩
    have htx : t <:+ x := ⟨s, by rw [← hsu, List.append_assoc]⟩
    have ht : t.reverse <+: x.reverse := List.reverse_prefix.2 htx
    exact h t.reverse ht w (by rw [List.reverse_reverse]; exact hwt)
  · intro h y hy w hw
    have hy' : y.reverse <:+ x := by
      have : y.reverse.reverse <+: x.reverse := by rw [List.reverse_reverse]; exact hy
      exact List.reverse_prefix.1 this
    exact h w (hw.isInfix.trans hy'.isInfix)

end PvsNP.Units.tc_closure_every_factor_np

/-- NP is closed under "every factor is in `L`" (TM2): every factor of `x` in `L` says every
suffix of `x` has all its prefixes in `L`, and "every suffix" is "every prefix" read through
reversal. So the language is built from `L` by the settled `m2_np_all_prefixes` and
`m2_np_reverse_closed`, twice each. -/
theorem PvsNP.Units.tc_closure_every_factor_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have h1 := PvsNP.Units.m2_np_all_prefixes L hL
  have h2 := PvsNP.Units.m2_np_reverse_closed _ h1
  have h3 := PvsNP.Units.m2_np_all_prefixes _ h2
  have h4 := PvsNP.Units.m2_np_reverse_closed _ h3
  have e : ({x : List Bool | x.reverse ∈ ({x : List Bool | ∀ y : List Bool, y <+: x →
      y ∈ ({x : List Bool | x.reverse ∈ ({x : List Bool | ∀ y : List Bool, y <+: x → y ∈ L} :
        Language Bool)} : Language Bool)} : Language Bool)} : Language Bool) =
      ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) := by
    ext x
    exact PvsNP.Units.tc_closure_every_factor_np.factor_iff L x
  exact (congrArg (fun S : Language Bool => S ∈ PvsNP.NP) e).mp h4
