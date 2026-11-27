import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_tm_answer_as_string

open Turing

/-- The two output encodings agree: `encodeAnswer b = [b]` (Mathlib's `encodeBool = pure`)
and `encodeString [b] = [b]` (Mathlib's `encodingList` has `encode := id`). -/
theorem encode_answer (b : Bool) : PvsNP.encodeAnswer b = PvsNP.encodeString [b] := rfl

end PvsNP.Units.m2_tm_answer_as_string

/-- A `Bool`-valued function and its `[f x]`-valued twin are polytime-computable by the very
same machine: the input encoding is the same on both sides, and the output encodings agree
(`encodeAnswer (f a) = [f a] = encodeString [f a]`), so the same `tm`, the same `time`
polynomial and the same `outputsFun` witness both sides. -/
theorem PvsNP.Units.m2_tm_answer_as_string :
    ∀ f : List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f ↔
        PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
          (fun x : List Bool => [f x]) := by
  intro f
  constructor
  · rintro ⟨M⟩
    refine ⟨⟨M.toTM2ComputableAux, M.time, fun a => ?_⟩⟩
    show Turing.TM2OutputsInTime M.toTM2ComputableAux.tm
        (List.map M.toTM2ComputableAux.inputAlphabet.invFun (PvsNP.encodeString a))
        (Option.some (List.map M.toTM2ComputableAux.outputAlphabet.invFun
          (PvsNP.encodeString [f a])))
        (M.time.eval (PvsNP.encodeString a).length)
    rw [← PvsNP.Units.m2_tm_answer_as_string.encode_answer (f a)]
    exact M.outputsFun a
  · rintro ⟨M⟩
    refine ⟨⟨M.toTM2ComputableAux, M.time, fun a => ?_⟩⟩
    show Turing.TM2OutputsInTime M.toTM2ComputableAux.tm
        (List.map M.toTM2ComputableAux.inputAlphabet.invFun (PvsNP.encodeString a))
        (Option.some (List.map M.toTM2ComputableAux.outputAlphabet.invFun
          (PvsNP.encodeAnswer (f a))))
        (M.time.eval (PvsNP.encodeString a).length)
    rw [PvsNP.Units.m2_tm_answer_as_string.encode_answer (f a)]
    exact M.outputsFun a
