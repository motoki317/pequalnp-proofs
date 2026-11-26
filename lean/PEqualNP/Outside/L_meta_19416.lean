import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19416

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [10, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19416

theorem PEqualNP.Outside.L_meta_19416 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide ((v : ℕ) < ![5, 5, 3, 3, 2] u)) 6 := by
  refine ⟨PEqualNP.Outside.L_meta_19416.witness, PEqualNP.Outside.L_meta_19416.legal, by decide, ?_⟩
  decide +kernel
