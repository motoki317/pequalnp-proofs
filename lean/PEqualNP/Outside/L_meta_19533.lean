import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19533
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

end PEqualNP.Outside.L_meta_19533

open PEqualNP.Outside.L_meta_19533 PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19533 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ 1 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val + 2 ≤ n))) C := by
  intro n hn
  refine ⟨⟨[⟨.or, [0, n + 0]⟩, ⟨.and, [0, n + 0]⟩, ⟨.not, [n + n + 1]⟩, ⟨.or, [1, n + (n - 1)]⟩,
    ⟨.not, [n + n + 3]⟩, ⟨.or, [n + n, n + n + 4]⟩, ⟨.and, [n + n + 2, n + n + 5]⟩], n + n + 6⟩,
    ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (oneEach u v).length = n + n := by simp [oneEach]
    have h0 := gL u v 0 (by omega)
    have h1 := gL u v 1 (by omega)
    have ha := gR u v 0 (by omega)
    have hb : (oneEach u v).getD (n + (n - 1)) false = decide (v.val + 1 = n) :=
      (gR u v (n - 1) (by omega)).trans (decide_eq_decide.mpr (by omega))
    generalize oneEach u v = l at hl h0 h1 ha hb
    have i0 : 0 < l.length := by omega
    have i1 : 1 < l.length := by omega
    have ia : n + 0 < l.length := by omega
    have ib : n + (n - 1) < l.length := by omega
    rw [show n + n = l.length from hl.symm]
    simp only [Circuit.eval, Circuit.wires, List.foldl, List.map, List.append_assoc, List.cons_append,
      List.nil_append, List.getD_append _ _ _ _ i0, List.getD_append _ _ _ _ i1,
      List.getD_append _ _ _ _ ia, List.getD_append _ _ _ _ ib, gB, gB0, h0, h1, ha, hb, GateOp.eval,
      List.getD_cons_zero, List.getD_cons_succ, List.all_cons, List.all_nil, List.any_cons,
      List.any_nil, List.headD_cons, id, Bool.and_true, Bool.or_false]
    by_cases k0 : u.val = 0 <;> by_cases k1 : u.val = 1 <;> by_cases ka : v.val = 0 <;>
      by_cases kb : v.val + 1 = n <;> simp [k0, k1, ka, kb] <;> omega
