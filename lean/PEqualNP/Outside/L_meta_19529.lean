import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19529
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (u.val = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, Fin.ext_iff, eq_comm]

theorem gR {n : ℕ} (u v : Fin n) (j : ℕ) (hj : j < n) :
    (oneEach u v).getD (n + j) false = decide (v.val = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, hj, Fin.ext_iff, eq_comm]

theorem gB (l vs : List Bool) (t : ℕ) : (l ++ vs).getD (l.length + t) false = vs.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem gB0 (l vs : List Bool) : (l ++ vs).getD l.length false = vs.getD 0 false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

end PEqualNP.Outside.L_meta_19529

open PEqualNP.Outside.L_meta_19529 PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19529 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u : ℕ) = 0 ∨ (v : ℕ) = 0 ∨ ((u : ℕ) ≠ n - 1 ∧ (v : ℕ) ≠ n - 1))) C := by
  intro n hn
  refine ⟨⟨[⟨.or, [n - 1, n + (n - 1)]⟩, ⟨.not, [n + n]⟩, ⟨.or, [0, n + 0]⟩,
    ⟨.or, [n + n + 2, n + n + 1]⟩], n + n + 3⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (oneEach u v).length = n + n := by simp [oneEach]
    have h0 := gL u v 0 (by omega)
    have h1 := gL u v (n - 1) (by omega)
    have ha := gR u v 0 (by omega)
    have hb := gR u v (n - 1) (by omega)
    generalize oneEach u v = l at hl h0 h1 ha hb
    have i0 : 0 < l.length := by omega
    have ia : n + 0 < l.length := by omega
    rw [show n + n = l.length from hl.symm]
    simp only [Circuit.eval, Circuit.wires, List.foldl, List.map, List.append_assoc, List.cons_append,
      List.nil_append, List.getD_append _ _ _ _ i0,
      List.getD_append _ _ _ _ ia, gB, gB0, h0, h1, ha, hb, GateOp.eval,
      List.getD_cons_zero, List.getD_cons_succ, List.any_cons,
      List.any_nil, List.headD_cons, id, Bool.or_false]
    by_cases k0 : u.val = 0 <;> by_cases k1 : u.val = n - 1 <;> by_cases ka : v.val = 0 <;>
      by_cases kb : v.val = n - 1 <;> simp [k0, k1, ka, kb]
