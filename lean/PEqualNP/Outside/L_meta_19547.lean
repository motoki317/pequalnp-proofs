import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19547

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [2, 7]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [0, 18]⟩,
    ⟨.or, [2, 3]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [13, 14]⟩,
    ⟨.or, [11, 12]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [26, 29]⟩,
    ⟨.and, [6, 28]⟩, ⟨.and, [5, 31]⟩, ⟨.and, [20, 25]⟩, ⟨.and, [19, 24]⟩, ⟨.and, [0, 30]⟩,
    ⟨.and, [22, 29]⟩, ⟨.and, [21, 27]⟩, ⟨.and, [7, 23]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [40, 34]⟩,
    ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 39]⟩], 46⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19547

theorem PEqualNP.Outside.L_meta_19547 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x4eb463b8a3475c99 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  refine ⟨PEqualNP.Outside.L_meta_19547.witness, PEqualNP.Outside.L_meta_19547.legal, by decide, ?_⟩
  decide +kernel
