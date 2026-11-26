import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19550

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [7, 10]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [6, 20]⟩,
    ⟨.or, [0, 11]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [5, 17]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [7, 12]⟩,
    ⟨.or, [12, 25]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [8, 23]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [3, 14]⟩,
    ⟨.or, [1, 13]⟩, ⟨.or, [26, 32]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [3, 32]⟩, ⟨.or, [5, 29]⟩,
    ⟨.or, [19, 35]⟩, ⟨.or, [15, 35]⟩, ⟨.and, [6, 38]⟩, ⟨.and, [37, 22]⟩, ⟨.and, [27, 30]⟩,
    ⟨.and, [33, 36]⟩, ⟨.and, [34, 31]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [44, 41]⟩, ⟨.or, [45, 42]⟩,
    ⟨.or, [46, 43]⟩], 47⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19550

theorem PEqualNP.Outside.L_meta_19550 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0xc3b478740f9a8b65 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  refine ⟨PEqualNP.Outside.L_meta_19550.witness, PEqualNP.Outside.L_meta_19550.legal, by decide, ?_⟩
  decide +kernel
