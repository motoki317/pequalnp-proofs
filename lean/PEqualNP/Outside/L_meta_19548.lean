import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19548

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [2, 15]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [2, 8]⟩,
    ⟨.or, [17, 20]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [1, 13]⟩,
    ⟨.or, [4, 18]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [26, 30]⟩,
    ⟨.or, [16, 25]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [4, 33]⟩, ⟨.or, [27, 30]⟩, ⟨.and, [23, 31]⟩,
    ⟨.and, [29, 35]⟩, ⟨.and, [32, 34]⟩, ⟨.and, [22, 24]⟩, ⟨.or, [36, 37]⟩, ⟨.or, [40, 38]⟩,
    ⟨.or, [41, 39]⟩], 42⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19548

theorem PEqualNP.Outside.L_meta_19548 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0x4eb463b8a3475c99 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨PEqualNP.Outside.L_meta_19548.witness, PEqualNP.Outside.L_meta_19548.legal, by decide, ?_⟩
  decide +kernel
