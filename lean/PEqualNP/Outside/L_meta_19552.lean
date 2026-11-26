import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19552

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [5, 8]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [8, 19]⟩, ⟨.or, [12, 15]⟩,
    ⟨.or, [3, 13]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [2, 10]⟩,
    ⟨.or, [22, 26]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [15, 28]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [24, 28]⟩,
    ⟨.or, [3, 21]⟩, ⟨.or, [6, 26]⟩, ⟨.or, [16, 29]⟩, ⟨.and, [33, 32]⟩, ⟨.and, [31, 27]⟩,
    ⟨.and, [18, 25]⟩, ⟨.and, [34, 30]⟩, ⟨.and, [16, 23]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [40, 37]⟩,
    ⟨.or, [41, 38]⟩, ⟨.or, [42, 39]⟩], 43⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19552

theorem PEqualNP.Outside.L_meta_19552 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0xc3b478740f9a8b65 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨PEqualNP.Outside.L_meta_19552.witness, PEqualNP.Outside.L_meta_19552.legal, by decide, ?_⟩
  decide +kernel
