import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19555

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [2, 9]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [2, 8]⟩,
    ⟨.or, [5, 18]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [9, 10]⟩,
    ⟨.or, [10, 24]⟩, ⟨.or, [5, 26]⟩, ⟨.or, [6, 25]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [29, 30]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [20, 30]⟩, ⟨.or, [6, 22]⟩, ⟨.or, [19, 29]⟩, ⟨.or, [21, 32]⟩,
    ⟨.and, [28, 31]⟩, ⟨.and, [33, 35]⟩, ⟨.and, [34, 36]⟩, ⟨.and, [17, 27]⟩, ⟨.or, [37, 38]⟩,
    ⟨.or, [41, 39]⟩, ⟨.or, [42, 40]⟩], 43⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19555

theorem PEqualNP.Outside.L_meta_19555 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x2e87c9d235786996 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨PEqualNP.Outside.L_meta_19555.witness, PEqualNP.Outside.L_meta_19555.legal, by decide, ?_⟩
  decide +kernel
