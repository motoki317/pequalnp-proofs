import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19535

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_app_ge (l l2 : List Bool) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l2).getD i false = l2.getD (i - l.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_row {n : ℕ} (u v a : Fin n) :
    (oneEach u v).getD a.val false = decide (a = u) := by
  unfold oneEach
  rw [getD_app_lt _ _ _ (by simp), ofFn_getD _ a.val a.isLt]

theorem oneEach_col {n : ℕ} (u v b : Fin n) :
    (oneEach u v).getD (n + b.val) false = decide (b = v) := by
  unfold oneEach
  rw [getD_app_ge _ _ _ (by simp), List.length_ofFn, ofFn_getD _ (n + b.val - n) (by omega)]
  congr 1
  simp [Fin.ext_iff]

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

def Mono (e : List Gate) : Prop :=
  ∀ g ∈ e, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Reach (gs : List Gate) (c : ℕ) (gs' : List Gate) : Prop :=
  ∃ e, gs' = gs ++ e ∧ Mono e ∧ e.length ≤ c

theorem reach_refl (gs : List Gate) : Reach gs 0 gs := by
  refine ⟨[], (List.append_nil gs).symm, ?_, Nat.le_refl 0⟩
  intro g hg
  cases hg

theorem reach_trans {gs gs1 gs2 : List Gate} {c1 c2 c : ℕ} (h1 : Reach gs c1 gs1)
    (h2 : Reach gs1 c2 gs2) (hc : c1 + c2 ≤ c) : Reach gs c gs2 := by
  obtain ⟨e1, rfl, m1, l1⟩ := h1
  obtain ⟨e2, rfl, m2, l2⟩ := h2
  refine ⟨e1 ++ e2, List.append_assoc _ _ _, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact m1 g h
    · exact m2 g h
  · rw [List.length_append]; omega

def Has (n : ℕ) (gs : List Gate) (w : ℕ) (f : Fin n → Fin n → Bool) : Prop :=
  w < n + n + gs.length ∧ ∀ u v : Fin n, (W gs (oneEach u v)).getD w false = f u v

theorem has_reach {n : ℕ} {gs gs' : List Gate} {c w : ℕ} {f : Fin n → Fin n → Bool}
    (h : Reach gs c gs') (hw : Has n gs w f) : Has n gs' w f := by
  obtain ⟨e, rfl, _, _⟩ := h
  refine ⟨by rw [List.length_append]; have := hw.1; omega, fun u v => ?_⟩
  rw [W_append, W_prefix e _ w (by rw [W_length, oneEach_length]; exact hw.1)]
  exact hw.2 u v

theorem has_congr {n : ℕ} {gs : List Gate} {w : ℕ} {f g : Fin n → Fin n → Bool}
    (h : ∀ u v, f u v = g u v) (hw : Has n gs w f) : Has n gs w g :=
  ⟨hw.1, fun u v => (hw.2 u v).trans (h u v)⟩

theorem has_row {n : ℕ} (gs : List Gate) (a : Fin n) :
    Has n gs a.val (fun u _ => decide (a = u)) := by
  refine ⟨by have := a.isLt; omega, fun u v => ?_⟩
  rw [W_prefix gs _ _ (by rw [oneEach_length]; have := a.isLt; omega), oneEach_row]

theorem has_col {n : ℕ} (gs : List Gate) (b : Fin n) :
    Has n gs (n + b.val) (fun _ v => decide (b = v)) := by
  refine ⟨by have := b.isLt; omega, fun u v => ?_⟩
  rw [W_prefix gs _ _ (by rw [oneEach_length]; have := b.isLt; omega), oneEach_col]

theorem has_or {n : ℕ} {gs : List Gate} {a b : ℕ} {f g : Fin n → Fin n → Bool}
    (ha : Has n gs a f) (hb : Has n gs b g) :
    ∃ gs' w, Reach gs 1 gs' ∧ Has n gs' w (fun u v => f u v || g u v) := by
  refine ⟨gs ++ [⟨GateOp.or, [a, b]⟩], n + n + gs.length, ⟨_, rfl, ?_, Nat.le_refl 1⟩, ?_,
    fun u v => ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  · rw [List.length_append, List.length_singleton]; omega
  · rw [W_snoc, step_last _ _ _ (by rw [W_length, oneEach_length])]
    show GateOp.or.eval [(W gs (oneEach u v)).getD a false, (W gs (oneEach u v)).getD b false] = _
    rw [ha.2 u v, hb.2 u v, eval_or2]

theorem has_and {n : ℕ} {gs : List Gate} {a b : ℕ} {f g : Fin n → Fin n → Bool}
    (ha : Has n gs a f) (hb : Has n gs b g) :
    ∃ gs' w, Reach gs 1 gs' ∧ Has n gs' w (fun u v => f u v && g u v) := by
  refine ⟨gs ++ [⟨GateOp.and, [a, b]⟩], n + n + gs.length, ⟨_, rfl, ?_, Nat.le_refl 1⟩, ?_,
    fun u v => ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Or.inl rfl, Nat.le_refl 2⟩
  · rw [List.length_append, List.length_singleton]; omega
  · rw [W_snoc, step_last _ _ _ (by rw [W_length, oneEach_length])]
    show GateOp.and.eval [(W gs (oneEach u v)).getD a false, (W gs (oneEach u v)).getD b false] = _
    rw [ha.2 u v, hb.2 u v, eval_and2]

theorem or_dec (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] (h : (p ∨ q) ↔ r) :
    (decide p || decide q) = decide r := by
  rw [← Bool.decide_or]
  exact decide_eq_decide.mpr h

theorem colrun {n : ℕ} (a : ℕ) : ∀ (j : ℕ) (gs : List Gate), a + j < n →
    ∃ gs', Reach gs j gs' ∧ ∀ i, i ≤ j →
      ∃ w, Has n gs' w (fun _ v => decide (a ≤ v.val ∧ v.val ≤ a + i)) := by
  intro j
  induction j with
  | zero =>
    intro gs h
    refine ⟨gs, reach_refl gs, fun i hi => ⟨n + a, ?_⟩⟩
    have hi0 : i = 0 := by omega
    subst hi0
    refine has_congr (fun u v => ?_) (has_col gs ⟨a, by omega⟩)
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff]
    show a = v.val ↔ _
    omega
  | succ j ih =>
    intro gs h
    obtain ⟨gs1, r1, h1⟩ := ih gs (by omega)
    obtain ⟨w1, hw1⟩ := h1 j (Nat.le_refl j)
    obtain ⟨gs2, w2, r2, hw2⟩ := has_or hw1 (has_col gs1 ⟨a + (j + 1), h⟩)
    refine ⟨gs2, reach_trans r1 r2 (Nat.le_refl _), fun i hi => ?_⟩
    by_cases hij : i ≤ j
    · obtain ⟨w, hw⟩ := h1 i hij
      exact ⟨w, has_reach r2 hw⟩
    · have hi1 : i = j + 1 := by omega
      subst hi1
      refine ⟨w2, has_congr (fun u v => ?_) hw2⟩
      apply or_dec
      rw [Fin.ext_iff]
      show _ ∨ a + (j + 1) = v.val ↔ _
      omega

theorem rowrun {n : ℕ} (a : ℕ) : ∀ (j : ℕ) (gs : List Gate), a + j < n →
    ∃ gs', Reach gs j gs' ∧ ∀ i, i ≤ j →
      ∃ w, Has n gs' w (fun u _ => decide (a ≤ u.val ∧ u.val ≤ a + i)) := by
  intro j
  induction j with
  | zero =>
    intro gs h
    refine ⟨gs, reach_refl gs, fun i hi => ⟨a, ?_⟩⟩
    have hi0 : i = 0 := by omega
    subst hi0
    refine has_congr (fun u v => ?_) (has_row gs ⟨a, by omega⟩)
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff]
    show a = u.val ↔ _
    omega
  | succ j ih =>
    intro gs h
    obtain ⟨gs1, r1, h1⟩ := ih gs (by omega)
    obtain ⟨w1, hw1⟩ := h1 j (Nat.le_refl j)
    obtain ⟨gs2, w2, r2, hw2⟩ := has_or hw1 (has_row gs1 ⟨a + (j + 1), h⟩)
    refine ⟨gs2, reach_trans r1 r2 (Nat.le_refl _), fun i hi => ?_⟩
    by_cases hij : i ≤ j
    · obtain ⟨w, hw⟩ := h1 i hij
      exact ⟨w, has_reach r2 hw⟩
    · have hi1 : i = j + 1 := by omega
      subst hi1
      refine ⟨w2, has_congr (fun u v => ?_) hw2⟩
      apply or_dec
      rw [Fin.ext_iff]
      show _ ∨ a + (j + 1) = u.val ↔ _
      omega

theorem main : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u.val = 0 ∧ 1 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val + 2 ≤ n))) (2 * n + 1) := by
  intro n hn
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hl : n - 1 < n := by omega
  obtain ⟨gs1, r1, p1⟩ := colrun (n := n) 1 (n - 3) [] (by omega)
  obtain ⟨wm, hm⟩ := p1 (n - 3) (Nat.le_refl _)
  obtain ⟨gs2, r2, p2⟩ := rowrun (n := n) 2 (n - 3) gs1 (by omega)
  obtain ⟨wr, hr⟩ := p2 (n - 3) (Nat.le_refl _)
  obtain ⟨gs3, wp, r3, hp⟩ := has_or (has_reach r2 hm) (has_col gs2 ⟨n - 1, hl⟩)
  obtain ⟨gs4, wq, r4, hq⟩ := has_or (has_reach (reach_trans r2 r3 (Nat.le_refl _)) hm)
    (has_col gs3 ⟨0, h0⟩)
  obtain ⟨gs5, w5, r5, h5⟩ := has_and (has_row gs4 ⟨0, h0⟩) (has_reach r4 hp)
  obtain ⟨gs6, w6, r6, h6⟩ := has_and (has_row gs5 ⟨1, h1⟩) (has_col gs5 ⟨0, h0⟩)
  obtain ⟨gs7, w7, r7, h7⟩ := has_and
    (has_reach (reach_trans (reach_trans (reach_trans r3 r4 (Nat.le_refl _)) r5 (Nat.le_refl _))
      r6 (Nat.le_refl _)) hr)
    (has_reach (reach_trans r5 r6 (Nat.le_refl _)) hq)
  obtain ⟨gs8, w8, r8, h8⟩ := has_or (has_reach (reach_trans r6 r7 (Nat.le_refl _)) h5)
    (has_reach r7 h6)
  obtain ⟨gs9, w9, r9, h9⟩ := has_or h8 (has_reach r8 h7)
  obtain ⟨e, he, hmono, hlen⟩ := reach_trans (reach_trans (reach_trans (reach_trans (reach_trans
    (reach_trans (reach_trans (reach_trans r1 r2 (Nat.le_refl _)) r3 (Nat.le_refl _)) r4
    (Nat.le_refl _)) r5 (Nat.le_refl _)) r6 (Nat.le_refl _)) r7 (Nat.le_refl _)) r8
    (Nat.le_refl _)) r9 (Nat.le_refl _)
  subst he
  refine ⟨⟨gs9, w9⟩, fun g hg => hmono g hg, ?_, ?_⟩
  · show gs9.length ≤ _
    omega
  · intro u v
    rw [eval_W]
    show (W gs9 (oneEach u v)).getD w9 false = _
    rw [h9.2 u v]
    have hu := u.isLt
    have hv := v.isLt
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff]
    omega

end PEqualNP.Outside.L_meta_19535

theorem PEqualNP.Outside.L_meta_19535 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u.val = 0 ∧ 1 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val + 2 ≤ n))) (2 * n + 1) :=
  PEqualNP.Outside.L_meta_19535.main
