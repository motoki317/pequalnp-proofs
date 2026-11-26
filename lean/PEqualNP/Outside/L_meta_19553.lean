import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19553

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 15]⟩,
    ⟨.or, [9, 10]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [18, 26]⟩,
    ⟨.and, [21, 30]⟩, ⟨.and, [20, 28]⟩, ⟨.and, [19, 27]⟩, ⟨.and, [17, 29]⟩, ⟨.and, [16, 31]⟩,
    ⟨.and, [23, 25]⟩, ⟨.and, [22, 24]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩,
    ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩], 46⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19553

theorem PEqualNP.Outside.L_meta_19553 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x2e87c9d235786996 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  refine ⟨PEqualNP.Outside.L_meta_19553.witness, PEqualNP.Outside.L_meta_19553.legal, by decide, ?_⟩
  decide +kernel
