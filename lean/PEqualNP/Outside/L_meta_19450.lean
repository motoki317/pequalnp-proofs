import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19450

theorem ifp {c : Prop} [Decidable c] (hc : c) {α : Type} {t e : α} : (if c then t else e) = t := by
  simp [hc]

theorem ifn {c : Prop} [Decidable c] (hc : ¬ c) {α : Type} {t e : α} : (if c then t else e) = e := by
  simp [hc]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

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

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

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

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [ifp ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [ifn ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ifp hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [ifn hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ifp (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ifp hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ifn hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ifp hlt]; exact h⟩

theorem val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ifp hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ifn hlt] at h'; cases h'
  · intro h i hi
    rw [ifp (h i hi).1]; exact (h i hi).2

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem andOrOnly_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := h.1

theorem monotone2_len {C : Circuit} (h : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length ≤ 2 := (h g hg).2

theorem isAO2_len {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length = 2 := h.2.2 g hg

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [ifp hi, ifp hi]
            exact ih i hi
          · rw [ifn hi, ifn hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ag_gat (gs : List Gate) (k : ℕ) : Gate := gs.getD k ⟨GateOp.or, []⟩

def ag_val (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun q => w.getD q false)

theorem ag_gat_eq (gs : List Gate) (k : ℕ) (hk : k < gs.length) : ag_gat gs k = gs[k] :=
  List.getD_eq_getElem _ _ hk

theorem ag_gat_set_eq (gs : List Gate) (i : ℕ) (g : Gate) (hi : i < gs.length) :
    ag_gat (gs.set i g) i = g := by
  unfold ag_gat
  rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hi)]
  simp

theorem ag_gat_set_ne (gs : List Gate) (i k : ℕ) (g : Gate) (h : k ≠ i) :
    ag_gat (gs.set i g) k = ag_gat gs k := by
  unfold ag_gat
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem ag_gat_of (gs : List Gate) (k : ℕ) (g : Gate) (h : gs[k]? = some g) : ag_gat gs k = g := by
  unfold ag_gat
  rw [List.getD_eq_getElem?_getD, h]
  rfl

theorem ag_W_take (gs : List Gate) (x : List Bool) (k q : ℕ) (hk : k ≤ gs.length)
    (hq : q < x.length + k) :
    (W (gs.take k) x).getD q false = (W gs x).getD q false := by
  have e : W gs x = W (gs.drop k) (W (gs.take k) x) := by
    rw [← W_append, List.take_append_drop]
  rw [e, W_prefix (gs.drop k) (W (gs.take k) x) q
    (by rw [W_length, List.length_take]; omega)]

theorem ag_W_fix (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ q ∈ (ag_gat gs k).inputs, q < x.length + k) :
    (W gs x).getD (x.length + k) false = ag_val (ag_gat gs k) (W gs x) := by
  have e : W gs x = W (gs.drop (k + 1)) (step (W (gs.take k) x) (ag_gat gs k)) := by
    rw [ag_gat_eq gs k hk, ← W_cons, ← List.drop_eq_getElem_cons hk, ← W_append,
      List.take_append_drop]
  have hl : (W (gs.take k) x).length = x.length + k := by
    rw [W_length, List.length_take]; omega
  have h2 : (step (W (gs.take k) x) (ag_gat gs k)).getD (x.length + k) false
      = ag_val (ag_gat gs k) (W (gs.take k) x) := by
    show ((W (gs.take k) x) ++ [ag_val (ag_gat gs k) (W (gs.take k) x)]).getD (x.length + k) false = _
    rw [← hl]
    exact getD_app_len _ _
  conv_lhs => rw [e]
  rw [W_prefix _ _ _ (by rw [step_len]; omega), h2]
  unfold ag_val
  congr 1
  apply List.map_congr_left
  intro q hq
  exact ag_W_take gs x k q (le_of_lt hk) (hr q hq)

theorem agree_stepP (w w' : List Bool) (g g' : Gate) (P : ℕ → Prop) (hl : w'.length = w.length)
    (h : ∀ q, ¬ P q → w'.getD q false = w.getD q false)
    (hv : P w.length ∨ ag_val g' w' = ag_val g w) :
    ∀ q, ¬ P q → (step w' g').getD q false = (step w g).getD q false := by
  intro q hq
  show (w' ++ [ag_val g' w']).getD q false = (w ++ [ag_val g w]).getD q false
  by_cases h1 : q < w.length
  · rw [getD_app_lt w' _ q (by omega), getD_app_lt w _ q h1]
    exact h q hq
  · by_cases h2 : q = w.length
    · have e1 : (w ++ [ag_val g w]).getD q false = ag_val g w := by
        rw [h2]; exact getD_app_len w _
      have e2 : (w' ++ [ag_val g' w']).getD q false = ag_val g' w' := by
        rw [h2, ← hl]; exact getD_app_len w' _
      rw [e1, e2]
      rcases hv with hv | hv
      · rw [h2] at hq
        exact absurd hv hq
      · exact hv
    · have e1 : (w ++ [ag_val g w]).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      have e2 : (w' ++ [ag_val g' w']).length ≤ q := by
        rw [List.length_append, List.length_singleton]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none e1, List.getElem?_eq_none e2]

theorem agreeP2 (x x' : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hx : x'.length = x.length) (hlen : gs'.length = gs.length)
    (hin : ∀ q, ¬ P q → x'.getD q false = x.getD q false)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x').getD q false = (W (gs.take k) x).getD q false) →
      ag_val (ag_gat gs' k) (W (gs'.take k) x') = ag_val (ag_gat gs k) (W (gs.take k) x)) :
    ∀ k, k ≤ gs.length → ∀ q, ¬ P q →
      (W (gs'.take k) x').getD q false = (W (gs.take k) x).getD q false := by
  intro k
  induction k with
  | zero =>
    intro _ q hq
    simp only [List.take_zero]
    exact hin q hq
  | succ k ih =>
    intro hk
    have hk1 : k < gs.length := by omega
    have hk2 : k < gs'.length := by omega
    have IH := ih (by omega)
    rw [List.take_succ_eq_append_getElem hk1, List.take_succ_eq_append_getElem hk2,
      W_append, W_append, W_single, W_single, ← ag_gat_eq gs k hk1, ← ag_gat_eq gs' k hk2]
    have l1 : (W (gs.take k) x).length = x.length + k := by
      rw [W_length, List.length_take]; omega
    have l2 : (W (gs'.take k) x').length = x.length + k := by
      rw [W_length, List.length_take, hx]; omega
    refine agree_stepP _ _ _ _ P (by omega) IH ?_
    by_cases hP : P (x.length + k)
    · left
      rw [l1]
      exact hP
    · right
      exact hstep k hk1 hP IH

theorem agreeP2_full (x x' : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hx : x'.length = x.length) (hlen : gs'.length = gs.length)
    (hin : ∀ q, ¬ P q → x'.getD q false = x.getD q false)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x').getD q false = (W (gs.take k) x).getD q false) →
      ag_val (ag_gat gs' k) (W (gs'.take k) x') = ag_val (ag_gat gs k) (W (gs.take k) x)) :
    ∀ q, ¬ P q → (W gs' x').getD q false = (W gs x).getD q false := by
  intro q hq
  have h := agreeP2 x x' gs gs' P hx hlen hin hstep gs.length le_rfl q hq
  rwa [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at h

theorem agreeP_full (x : List Bool) (gs gs' : List Gate) (P : ℕ → Prop)
    (hlen : gs'.length = gs.length)
    (hstep : ∀ k < gs.length, ¬ P (x.length + k) →
      (∀ q, ¬ P q → (W (gs'.take k) x).getD q false = (W (gs.take k) x).getD q false) →
      ag_val (ag_gat gs' k) (W (gs'.take k) x) = ag_val (ag_gat gs k) (W (gs.take k) x)) :
    ∀ q, ¬ P q → (W gs' x).getD q false = (W gs x).getD q false :=
  agreeP2_full x x gs gs' P rfl hlen (fun _ _ => rfl) hstep

theorem agree_full (x : List Bool) (gs gs' : List Gate) (i m p : ℕ) (hp : p = x.length + i)
    (hlen : gs'.length = gs.length)
    (hsame : ∀ k, k ≠ i → k ≠ m → ag_gat gs' k = ag_gat gs k)
    (hread : ∀ k < gs.length, k ≠ m → p ∉ (ag_gat gs k).inputs)
    (hval : (∀ q, q ≠ p → (W (gs'.take m) x).getD q false = (W (gs.take m) x).getD q false) →
      ag_val (ag_gat gs' m) (W (gs'.take m) x) = ag_val (ag_gat gs m) (W (gs.take m) x)) :
    ∀ q, q ≠ p → (W gs' x).getD q false = (W gs x).getD q false := by
  refine agreeP_full x gs gs' (fun q => q = p) hlen ?_
  intro k hk hP IH
  have hP' : x.length + k ≠ p := hP
  have hki : k ≠ i := fun h => hP' (by omega)
  by_cases hkm : k = m
  · subst hkm
    exact hval IH
  · rw [hsame k hki hkm]
    unfold ag_val
    congr 1
    apply List.map_congr_left
    intro r hr
    apply IH
    intro hre
    have hre' : r = p := hre
    rw [hre'] at hr
    exact hread k hk hkm hr

theorem agree_closed (x x' : List Bool) (gs gs' : List Gate) (B : ℕ → Prop)
    (hx : x'.length = x.length) (hlen : gs'.length = gs.length)
    (hin : ∀ q, ¬ B q → x'.getD q false = x.getD q false)
    (hch : ∀ k < gs.length, ¬ B (x.length + k) → ag_gat gs' k = ag_gat gs k)
    (hrd : ∀ k < gs.length, ¬ B (x.length + k) → ∀ i ∈ (ag_gat gs k).inputs, ¬ B i) :
    ∀ q, ¬ B q → (W gs' x').getD q false = (W gs x).getD q false := by
  refine agreeP2_full x x' gs gs' B hx hlen hin ?_
  intro k hk hB IH
  rw [hch k hk hB]
  unfold ag_val
  congr 1
  apply List.map_congr_left
  intro i hi
  exact IH i (hrd k hk hB i hi)

def ag_rd (L : ℕ) (gs : List Gate) (z w : ℕ) : Prop :=
  ∃ k < gs.length, w = L + k ∧ z ∈ (ag_gat gs k).inputs

theorem agree_cone (x x' : List Bool) (gs : List Gate) (y : ℕ) (hx : x'.length = x.length)
    (h : ∀ q < x.length, Relation.ReflTransGen (ag_rd x.length gs) q y →
      x'.getD q false = x.getD q false) :
    (W gs x').getD y false = (W gs x).getD y false := by
  refine agree_closed x x' gs gs (fun q => ¬ Relation.ReflTransGen (ag_rd x.length gs) q y) hx rfl
    ?_ (fun _ _ _ => rfl) ?_ y (fun hn => hn Relation.ReflTransGen.refl)
  · intro q hq
    by_cases hql : q < x.length
    · exact h q hql (by by_contra hc; exact hq hc)
    · rw [getD_ge x' q (by omega), getD_ge x q (by omega)]
  · intro k hk hB i hi hn
    exact hB (fun hr => hn (Relation.ReflTransGen.head ⟨k, hk, rfl, hi⟩ hr))

theorem agree_cone_val (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) (y : ℕ)
    (h : ∀ t : Fin n, Relation.ReflTransGen (ag_rd n C.gates) t.val y → x' t = x t) :
    val C (List.ofFn x') y = val C (List.ofFn x) y := by
  have hl : (List.ofFn x).length = n := List.length_ofFn
  have e := agree_cone (List.ofFn x) (List.ofFn x') C.gates y (by simp) (by
    intro q hq hr
    rw [hl] at hq hr
    rw [ofFn_getD x' q hq, ofFn_getD x q hq]
    exact h ⟨q, hq⟩ hr)
  exact e

theorem agree_except_one (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) (u : Fin n)
    (hxu : ∀ t, t ≠ u → x' t = x t) (y : ℕ)
    (hu : ¬ Relation.ReflTransGen (ag_rd n C.gates) u.val y) :
    val C (List.ofFn x') y = val C (List.ofFn x) y :=
  agree_cone_val n C x x' y (fun t ht => hxu t (fun e => hu (by rw [← e]; exact ht)))

theorem agree_ofFn {m : ℕ} (x y : Fin m → Bool) (k : Fin m)
    (h : ∀ k1 : Fin m, k1 ≠ k → x k1 = y k1) (i : ℕ) (hi : i ≠ k.val) :
    (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  by_cases hlt : i < m
  · rw [ofFn_getD x i hlt, ofFn_getD y i hlt]
    exact h ⟨i, hlt⟩ (fun he => hi (congrArg Fin.val he))
  · rw [ofFn_getD_ge x i (by omega), ofFn_getD_ge y i (by omega)]

theorem ag_rb_core (n : ℕ) (gs G : List Gate) (i m : ℕ) (hlen : G.length = gs.length)
    (hRB : ∀ k < gs.length, ∀ q ∈ (ag_gat gs k).inputs, q < n + k)
    (hsame : ∀ k, k ≠ i → k ≠ m → ag_gat G k = ag_gat gs k)
    (hi : ∀ q ∈ (ag_gat G i).inputs, q < n + i)
    (hm : ∀ q ∈ (ag_gat G m).inputs, q < n + m) :
    ∀ k < G.length, ∀ q ∈ (ag_gat G k).inputs, q < n + k := by
  intro k hk q hq
  by_cases h1 : k = i
  · subst h1; exact hi q hq
  · by_cases h2 : k = m
    · subst h2; exact hm q hq
    · rw [hsame k h1 h2] at hq
      exact hRB k (by omega) q hq


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem dc_dep_k (n : ℕ) (pre : List Gate) (k : ℕ) : (∀ g ∈ pre, g.inputs.length ≤ k + 1) →
    ∀ S : Finset ℕ, ∃ T : Finset ℕ, T.card ≤ k * pre.length + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ S
    exact ⟨S, by simp, fun x y _ _ h w hw => h w hw⟩
  | append_singleton pre g ih =>
    intro h2 S
    have h2p : ∀ g1 ∈ pre, g1.inputs.length ≤ k + 1 := fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg : g.inputs.length ≤ k + 1 := h2 g (by simp)
    have key : ∀ (T : Finset ℕ) (S1 : Finset ℕ), (∀ w ∈ S, w ≠ n + pre.length → w ∈ S1) →
        (n + pre.length ∈ S → ∀ i ∈ g.inputs, i ∈ S1) →
        (∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S1, (W pre x).getD w false = (W pre y).getD w false) →
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S, (W (pre ++ [g]) x).getD w false = (W (pre ++ [g]) y).getD w false := by
      intro T S1 hS1 hin hI x y hx hy hag w hw
      have hI2 := hI x y hx hy hag
      rw [W_snoc, W_snoc]
      have hlx : (W pre x).length = n + pre.length := by rw [W_length, hx]
      have hly : (W pre y).length = n + pre.length := by rw [W_length, hy]
      rcases lt_trichotomy w (n + pre.length) with hlt | heq | hgt
      · rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        exact hI2 w (hS1 w hw (by omega))
      · rw [step_last _ _ _ (by omega), step_last _ _ _ (by omega)]
        have hmap : (g.inputs.map fun i => (W pre x).getD i false)
            = (g.inputs.map fun i => (W pre y).getD i false) :=
          List.map_congr_left (fun i hi => hI2 i (hin (heq ▸ hw) i hi))
        rw [hmap]
      · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by rw [step_len]; omega)]
    by_cases hm : (n + pre.length) ∈ S
    · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ g.inputs.toFinset)
      refine ⟨T, ?_, key T _ ?_ ?_ hTv⟩
      · have h1 := Finset.card_union_le (S.erase (n + pre.length)) g.inputs.toFinset
        have h3 := List.toFinset_card_le g.inputs
        have h4 := Finset.card_erase_of_mem hm
        have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
        rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
        omega
      · intro w hw hne
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
      · intro _ i hi
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
    · obtain ⟨T, hT, hTv⟩ := ih h2p S
      refine ⟨T, ?_, key T S (fun w hw _ => hw) (fun h => absurd h hm) hTv⟩
      rw [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
      omega

theorem dc_dep (n : ℕ) (pre : List Gate) (h2 : ∀ g ∈ pre, g.inputs.length ≤ 2) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ pre.length + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  obtain ⟨T, hT, hv⟩ := dc_dep_k n pre 1 h2 S
  exact ⟨T, by rw [Nat.one_mul] at hT; exact hT, hv⟩

theorem dc_ne_of {a b : Bool} (ha : a = true) (hb : b = false) : a ≠ b := by
  rw [ha, hb]; decide

theorem dc_sens_card {n : ℕ} (C : Circuit) (k : ℕ) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ k + 1)
    (K : Finset (Fin n))
    (hK : ∀ i ∈ K, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    K.card ≤ k * C.size + 1 := by
  obtain ⟨T, hT, hTv⟩ := dc_dep_k n C.gates k hfan {C.output}
  have hall : ∀ i ∈ K, i.val ∈ T := by
    intro i hi
    by_contra hk
    obtain ⟨x, y, hne, hxy⟩ := hK i hi
    have he := hTv (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (fun j hj => agree_ofFn x y i hxy j (fun h => hk (h ▸ hj))) C.output
      (Finset.mem_singleton_self _)
    exact hne he
  have hcard : K.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => hall i hi)
      (fun a _ b _ h => Fin.ext h)
  rw [Finset.card_singleton] at hT
  show K.card ≤ k * C.gates.length + 1
  omega

theorem dc_sens_univ {n : ℕ} (C : Circuit) (k : ℕ) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ k + 1)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ k * C.size + 1 := by
  have h := dc_sens_card C k hfan Finset.univ (fun i _ => hK i)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem dc_sens2 {n : ℕ} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (K : Finset (Fin n))
    (hK : ∀ i ∈ K, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    K.card ≤ C.size + 1 := by
  have h := dc_sens_card C 1 hfan K hK
  rw [Nat.one_mul] at h
  exact h

theorem dc_sens2_univ {n : ℕ} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ C.size + 1 := by
  have h := dc_sens_univ C 1 hfan hK
  rw [Nat.one_mul] at h
  exact h

theorem dc_sens_mono2 {n : ℕ} (C : Circuit) (hC : Monotone2 C)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ C.size + 1 :=
  dc_sens2_univ C (fun _ hg => monotone2_len hC hg) hK

theorem dc_sens_ao2 {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hK : ∀ i : Fin n, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    n ≤ C.size + 1 :=
  dc_sens2_univ C (fun _ hg => le_of_eq (isAO2_len hC hg)) hK

theorem dc_cast_inj {P L : ℕ} {a b : Fin P} (h : Fin.castAdd L a = Fin.castAdd L b) : a = b := by
  have := congrArg Fin.val h
  exact Fin.ext (by simpa using this)

theorem dc_nat_inj {P L : ℕ} {a b : Fin L} (h : Fin.natAdd P a = Fin.natAdd P b) : a = b := by
  have := congrArg Fin.val h
  exact Fin.ext (by simpa using this)

theorem dc_nat_ne_cast {N M : ℕ} (a : Fin M) (b : Fin N) : Fin.natAdd N a ≠ Fin.castAdd M b := by
  intro h
  have h1 : N + a.val = b.val := congrArg Fin.val h
  have h2 := b.isLt
  omega

theorem dc_cast_ne_nat {N M : ℕ} (a : Fin M) (b : Fin N) : Fin.castAdd M b ≠ Fin.natAdd N a :=
  fun h => dc_nat_ne_cast a b h.symm

def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_natAdd]
    omega

theorem rep_pt {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (h : PEqualNP.Represents.Represents A C) (u : Fin n) (v : Fin m) :
    circuitFun (n + m) C (pt n m u.val (n + v.val)) = A u v := by
  rw [← h u v, oneEach_pt]
  rfl

def q (n m b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = b)

def rs (n m : ℕ) (C : Circuit) : Finset (Fin n) := Finset.univ.filter (fun u : Fin n => ∃ v : Fin m,
  circuitFun (n + m) C (pt n m u.val (n + v.val)) ≠ circuitFun (n + m) C (q n m (n + v.val)))

def cs (n m : ℕ) (C : Circuit) : Finset (Fin m) := Finset.univ.filter (fun w : Fin m => ∃ u : Fin n,
  circuitFun (n + m) C (pt n m u.val (n + w.val)) ≠ circuitFun (n + m) C (q n m u.val))

theorem sens_bound (n m : ℕ) (C : Circuit) (hfan2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (rs n m C).card + (cs n m C).card ≤ C.size + 1 := by
  have hdisj : Disjoint ((rs n m C).image (Fin.castAdd m)) ((cs n m C).image (Fin.natAdd n)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨b, _, hb⟩ := Finset.mem_image.1 hx2
    have h2 := congrArg Fin.val hb
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
    have := a.isLt
    omega
  have hK : ∀ i ∈ (rs n m C).image (Fin.castAdd m) ∪ (cs n m C).image (Fin.natAdd n),
      ∃ x y : Fin (n + m) → Bool, circuitFun (n + m) C x ≠ circuitFun (n + m) C y ∧
        ∀ k : Fin (n + m), k ≠ i → x k = y k := by
    intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      simp only [rs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨v, hv⟩ := hu
      refine ⟨_, _, hv, fun k hk => ?_⟩
      have hk' : k.val ≠ u.val := fun e => hk (Fin.ext (by simp [e]))
      simp [pt, q, hk']
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
      simp only [cs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨u, hu⟩ := hw
      refine ⟨_, _, hu, fun k hk => ?_⟩
      have hk' : k.val ≠ n + w.val := fun e => hk (Fin.ext (by simp only [Fin.val_natAdd]; omega))
      simp [pt, q, hk']
  have hc := dc_sens2 C hfan2 _ hK
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => dc_cast_inj h),
    Finset.card_image_of_injective _ (fun a b h => dc_nat_inj h)] at hc
  exact hc


def isNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

theorem isNot_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
  unfold isNot
  cases g.op <;> simp

theorem not_eval_congr (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i ∈ l.take 1, f i = f' i) :
    GateOp.not.eval (l.map f) = GateOp.not.eval (l.map f') := by
  cases l with
  | nil => rfl
  | cons a t =>
    have h1 := h a (by simp)
    simp [GateOp.eval, h1]

theorem dn_dep (n : ℕ) (pre : List Gate) : (∀ g ∈ pre, g.inputs.length ≤ 2) →
    ∀ S : Finset ℕ, ∃ T : Finset ℕ, T.card + pre.countP isNot ≤ pre.length + S.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ w ∈ S, (W pre x).getD w false = (W pre y).getD w false := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ S
    exact ⟨S, by simp, fun x y _ _ h w hw => h w hw⟩
  | append_singleton pre g ih =>
    intro h2 S
    have h2p : ∀ g1 ∈ pre, g1.inputs.length ≤ 2 := fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg : g.inputs.length ≤ 2 := h2 g (by simp)
    have key : ∀ (T : Finset ℕ) (S1 : Finset ℕ) (I : List ℕ),
        (∀ w ∈ S, w ≠ n + pre.length → w ∈ S1) →
        (n + pre.length ∈ S → ∀ i ∈ I, i ∈ S1) →
        (∀ f f' : ℕ → Bool, (∀ i ∈ I, f i = f' i) →
          g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f')) →
        (∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S1, (W pre x).getD w false = (W pre y).getD w false) →
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ T, x.getD i false = y.getD i false) →
          ∀ w ∈ S, (W (pre ++ [g]) x).getD w false = (W (pre ++ [g]) y).getD w false := by
      intro T S1 I hS1 hin hcong hI x y hx hy hag w hw
      have hI2 := hI x y hx hy hag
      rw [W_snoc, W_snoc]
      have hlx : (W pre x).length = n + pre.length := by rw [W_length, hx]
      have hly : (W pre y).length = n + pre.length := by rw [W_length, hy]
      rcases lt_trichotomy w (n + pre.length) with hlt | heq | hgt
      · rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        exact hI2 w (hS1 w hw (by omega))
      · rw [step_last _ _ _ (by omega), step_last _ _ _ (by omega)]
        exact hcong _ _ (fun i hi => hI2 i (hin (heq ▸ hw) i hi))
      · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by rw [step_len]; omega)]
    have hlen : (pre ++ [g]).length = pre.length + 1 := by simp
    have hcnt : (pre ++ [g]).countP isNot
        = pre.countP isNot + (if isNot g = true then 1 else 0) := by
      rw [List.countP_append, List.countP_singleton]
    rw [hlen, hcnt]
    by_cases hm : (n + pre.length) ∈ S
    · have h4 := Finset.card_erase_of_mem hm
      have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
      by_cases hnot : isNot g = true
      · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ (g.inputs.take 1).toFinset)
        refine ⟨T, ?_, key T _ (g.inputs.take 1) ?_ ?_ ?_ hTv⟩
        · have h1 := Finset.card_union_le (S.erase (n + pre.length)) (g.inputs.take 1).toFinset
          have h3 := List.toFinset_card_le (g.inputs.take 1)
          have h6 : (g.inputs.take 1).length ≤ 1 := by rw [List.length_take]; omega
          rw [ifp hnot]
          omega
        · intro w hw hne
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
        · intro _ i hi
          exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
        · intro f f' hff
          rw [(isNot_iff g).1 hnot]
          exact not_eval_congr _ f f' hff
      · obtain ⟨T, hT, hTv⟩ := ih h2p (S.erase (n + pre.length) ∪ g.inputs.toFinset)
        refine ⟨T, ?_, key T _ g.inputs ?_ ?_ ?_ hTv⟩
        · have h1 := Finset.card_union_le (S.erase (n + pre.length)) g.inputs.toFinset
          have h3 := List.toFinset_card_le g.inputs
          rw [ifn hnot]
          omega
        · intro w hw hne
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
        · intro _ i hi
          exact Finset.mem_union_right _ (List.mem_toFinset.mpr hi)
        · intro f f' hff
          rw [List.map_congr_left hff]
    · obtain ⟨T, hT, hTv⟩ := ih h2p S
      refine ⟨T, ?_, key T S g.inputs (fun w hw _ => hw) (fun h => absurd h hm)
        (fun f f' hff => by rw [List.map_congr_left hff]) hTv⟩
      split <;> omega

theorem dn_sens {n : ℕ} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (K : Finset (Fin n))
    (hK : ∀ i ∈ K, ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y ∧
      ∀ j : Fin n, j ≠ i → x j = y j) :
    K.card + C.gates.countP isNot ≤ C.size + 1 := by
  obtain ⟨T, hT, hTv⟩ := dn_dep n C.gates hfan {C.output}
  have hall : ∀ i ∈ K, i.val ∈ T := by
    intro i hi
    by_contra hk
    obtain ⟨x, y, hne, hxy⟩ := hK i hi
    have he := hTv (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (fun j hj => agree_ofFn x y i hxy j (fun h => hk (h ▸ hj))) C.output
      (Finset.mem_singleton_self _)
    exact hne he
  have hcard : K.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => hall i hi)
      (fun a _ b _ h => Fin.ext h)
  rw [Finset.card_singleton] at hT
  show K.card + C.gates.countP isNot ≤ C.gates.length + 1
  omega

theorem sens_bound_n (n m : ℕ) (C : Circuit) (hfan2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (rs n m C).card + (cs n m C).card + C.gates.countP isNot ≤ C.size + 1 := by
  have hdisj : Disjoint ((rs n m C).image (Fin.castAdd m)) ((cs n m C).image (Fin.natAdd n)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨b, _, hb⟩ := Finset.mem_image.1 hx2
    have h2 := congrArg Fin.val hb
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
    have := a.isLt
    omega
  have hK : ∀ i ∈ (rs n m C).image (Fin.castAdd m) ∪ (cs n m C).image (Fin.natAdd n),
      ∃ x y : Fin (n + m) → Bool, circuitFun (n + m) C x ≠ circuitFun (n + m) C y ∧
        ∀ k : Fin (n + m), k ≠ i → x k = y k := by
    intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      simp only [rs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨v, hv⟩ := hu
      refine ⟨_, _, hv, fun k hk => ?_⟩
      have hk' : k.val ≠ u.val := fun e => hk (Fin.ext (by simp [e]))
      simp [pt, q, hk']
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
      simp only [cs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨u, hu⟩ := hw
      refine ⟨_, _, hu, fun k hk => ?_⟩
      have hk' : k.val ≠ n + w.val := fun e => hk (Fin.ext (by simp only [Fin.val_natAdd]; omega))
      simp [pt, q, hk']
  have hc := dn_sens C hfan2 _ hK
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => dc_cast_inj h),
    Finset.card_image_of_injective _ (fun a b h => dc_nat_inj h)] at hc
  exact hc

theorem compl_le {n : ℕ} (S : Finset (Fin n)) (Q : Fin n → Prop) [DecidablePred Q]
    (h : ∀ a, a ∉ S → Q a) : n - (Finset.univ.filter Q).card ≤ S.card := by
  have h1 : Sᶜ ⊆ Finset.univ.filter Q := by
    intro a ha
    rw [Finset.mem_compl] at ha
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ a, h a ha⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_compl, Fintype.card_fin] at h2
  omega

theorem twin_aux (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit)
    (hn : 0 < n) (hm : 0 < m) (hfan : FanInTwo C) (hrep : PEqualNP.Represents.Represents A C) :
    ∃ (u0 : Fin n) (v0 : Fin m),
      (n - (Finset.univ.filter (fun u : Fin n => ∀ v : Fin m, A u v = A u0 v)).card) +
      (m - (Finset.univ.filter (fun v : Fin m => ∀ u : Fin n, A u v = A u v0)).card) +
      C.gates.countP isNot ≤ C.size + 1 := by
  have hfan2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hfan g hg).2
  have hb := sens_bound_n n m C hfan2
  obtain ⟨u0, hu0⟩ : ∃ u0 : Fin n, ∀ a : Fin n, a ∉ rs n m C → ∀ v : Fin m, A a v = A u0 v := by
    by_cases hex : ∃ u0 : Fin n, u0 ∉ rs n m C
    · obtain ⟨u0, h0⟩ := hex
      refine ⟨u0, fun a ha v => ?_⟩
      simp only [rs, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, ne_eq, not_not] at ha h0
      rw [← rep_pt hrep a v, ← rep_pt hrep u0 v, ha v, h0 v]
    · simp only [not_exists, not_not] at hex
      exact ⟨⟨0, hn⟩, fun a ha => absurd (hex a) ha⟩
  obtain ⟨v0, hv0⟩ : ∃ v0 : Fin m, ∀ b : Fin m, b ∉ cs n m C → ∀ u : Fin n, A u b = A u v0 := by
    by_cases hex : ∃ v0 : Fin m, v0 ∉ cs n m C
    · obtain ⟨v0, h0⟩ := hex
      refine ⟨v0, fun b hb' u => ?_⟩
      simp only [cs, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, ne_eq, not_not] at hb' h0
      rw [← rep_pt hrep u b, ← rep_pt hrep u v0, hb' u, h0 u]
    · simp only [not_exists, not_not] at hex
      exact ⟨⟨0, hm⟩, fun b hb' => absurd (hex b) hb'⟩
  refine ⟨u0, v0, ?_⟩
  have h1 := compl_le (rs n m C) (fun u : Fin n => ∀ v : Fin m, A u v = A u0 v) hu0
  have h2 := compl_le (cs n m C) (fun v : Fin m => ∀ u : Fin n, A u v = A u v0) hv0
  omega

theorem mono_sub (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit)
    (hmono : Monotone2 C) (hrep : PEqualNP.Represents.Represents A C) :
    (Finset.univ.filter (fun a : Fin n => ∃ b : Fin n, ∃ v : Fin m,
        A a v = true ∧ A b v = false)) ⊆ rs n m C ∧
    (Finset.univ.filter (fun v : Fin m => ∃ w : Fin m, ∃ a : Fin n,
        A a v = true ∧ A a w = false)) ⊆ cs n m C := by
  have hAO := andOrOnly_of_monotone2 hmono
  constructor
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨b, v, hav, hbv⟩ := ha
    simp only [rs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨v, ?_⟩
    rw [rep_pt hrep a v, hav]
    intro h
    have h3 := circuitFun_mono (n + m) C hAO (q n m (n + v.val)) (pt n m b.val (n + v.val))
      (fun i hi => by
        simp only [q, pt, decide_eq_true_eq, Bool.or_eq_true] at hi ⊢
        exact Or.inr hi) h.symm
    rw [rep_pt hrep b v, hbv] at h3
    cases h3
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨w, a, hav, haw⟩ := hv
    simp only [cs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨a, ?_⟩
    rw [rep_pt hrep a v, hav]
    intro h
    have h3 := circuitFun_mono (n + m) C hAO (q n m a.val) (pt n m a.val (n + w.val))
      (fun i hi => by
        simp only [q, pt, decide_eq_true_eq, Bool.or_eq_true] at hi ⊢
        exact Or.inl hi) h.symm
    rw [rep_pt hrep a w, haw] at h3
    cases h3

theorem mono_aux (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit)
    (hmono : Monotone2 C) (hrep : PEqualNP.Represents.Represents A C) :
    (Finset.univ.filter (fun a : Fin n => ∃ b : Fin n, ∃ v : Fin m,
        A a v = true ∧ A b v = false)).card +
    (Finset.univ.filter (fun v : Fin m => ∃ w : Fin m, ∃ a : Fin n,
        A a v = true ∧ A a w = false)).card ≤ C.size + 1 := by
  have hb := sens_bound n m C (fun g hg => monotone2_len hmono hg)
  obtain ⟨hr, hc⟩ := mono_sub n m A C hmono hrep
  have h1 := Finset.card_le_card hr
  have h2 := Finset.card_le_card hc
  omega

theorem monotone2_of_no_not (C : Circuit) (hfan : FanInTwo C)
    (hex : ¬ ∃ g ∈ C.gates, isNot g = true) : Monotone2 C := by
  intro g hg
  have h1 := hfan g hg
  refine ⟨?_, h1.2⟩
  have h2 : ¬ g.op = GateOp.not := fun e => hex ⟨g, hg, (isNot_iff g).2 e⟩
  have h3 := h1.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3 ⊢
  tauto

def A : Fin 4 → Fin 4 → Bool := fun u v => (311 : ℕ).testBit (4 * u.val + v.val)

theorem facts1 : ∀ u0 v0 : Fin 4,
    6 ≤ (4 - (Finset.univ.filter (fun u : Fin 4 => ∀ v : Fin 4, A u v = A u0 v)).card) +
    (4 - (Finset.univ.filter (fun v : Fin 4 => ∀ u : Fin 4, A u v = A u v0)).card) := by
  decide

theorem facts2 : 6 ≤ (Finset.univ.filter (fun a : Fin 4 => ∃ b : Fin 4, ∃ v : Fin 4,
        A a v = true ∧ A b v = false)).card +
    (Finset.univ.filter (fun v : Fin 4 => ∃ w : Fin 4, ∃ a : Fin 4,
        A a v = true ∧ A a w = false)).card := by
  decide

def ind2 (p q : ℕ) : ℕ → Bool := fun w => decide (w = p) || decide (w = q)

def Dep (S : Finset ℕ) (Ψ : (ℕ → Bool) → Bool) : Prop :=
  ∀ v v' : ℕ → Bool, (∀ w ∈ S, v w = v' w) → Ψ v = Ψ v'

def rel (Ψ : (ℕ → Bool) → Bool) (p q : ℕ) : Prop :=
  Ψ (ind2 p q) = true ∧ Ψ (ind2 p p) = false ∧ Ψ (ind2 q q) = false

def Bi (Ψ : (ℕ → Bool) → Bool) : Prop :=
  ∀ p p' q q', rel Ψ p q → rel Ψ p' q → rel Ψ p q' → rel Ψ p' q'

def BiN (N : ℕ) (Ψ : (ℕ → Bool) → Bool) : Prop :=
  ∀ p p' q q', p < N → p' < N → q < N → q' < N →
    rel Ψ p q → rel Ψ p' q → rel Ψ p q' → rel Ψ p' q'

def phi (a b k z x : ℕ) : ℕ := if x = a ∨ x = b then k else if x = k then z else x

def psi (a b k z x : ℕ) : ℕ := if x = a ∨ x = b ∨ x = k then z else x

def E (a b x y : ℕ) : Prop := (x = a ∧ y = b) ∨ (x = b ∧ y = a)

def orL (k a b : ℕ) (Ψ : (ℕ → Bool) → Bool) : (ℕ → Bool) → Bool :=
  fun val => Ψ (fun w => if w = k then (val a || val b) else val w)

def andL (k a b : ℕ) (Ψ : (ℕ → Bool) → Bool) : (ℕ → Bool) → Bool :=
  fun val => Ψ (fun w => if w = k then (val a && val b) else val w)

def lift (k : ℕ) (g : Gate) (Ψ : (ℕ → Bool) → Bool) : (ℕ → Bool) → Bool :=
  fun val => Ψ (fun w => if w = k then g.op.eval (g.inputs.map val) else val w)

def inF (N : ℕ) (pre : List Gate) (Ψ : (ℕ → Bool) → Bool) : (ℕ → Bool) → Bool :=
  fun val => Ψ (fun w => (W pre (List.ofFn fun i : Fin N => val i.val)).getD w false)

theorem fresh (S : Finset ℕ) (k : ℕ) : ∃ z, z ∉ S ∧ z ≠ k := by
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (insert k S)
  refine ⟨z, fun h => hz (Finset.mem_insert_of_mem h), fun h => hz ?_⟩
  rw [h]
  exact Finset.mem_insert_self k S

theorem bi_pull (Ψ Ψ' : (ℕ → Bool) → Bool) (f : ℕ → ℕ)
    (key : ∀ x y, Ψ' (ind2 x y) = Ψ (ind2 (f x) (f y))) (hBi : Bi Ψ) : Bi Ψ' := by
  have tr : ∀ x y, rel Ψ' x y ↔ rel Ψ (f x) (f y) := by
    intro x y
    unfold rel
    rw [key x y, key x x, key y y]
  intro p p' q q' h1 h2 h3
  rw [tr] at h1 h2 h3 ⊢
  exact hBi _ _ _ _ h1 h2 h3

theorem bi_or (S : Finset ℕ) (Ψ : (ℕ → Bool) → Bool) (hD : Dep S Ψ) (k a b : ℕ)
    (ha : a ∈ S → a = k) (hb : b ∈ S → b = k) (hBi : Bi Ψ) : Bi (orL k a b Ψ) := by
  obtain ⟨z, hzS, hzk⟩ := fresh S k
  refine bi_pull Ψ _ (phi a b k z) (fun x y => ?_) hBi
  refine hD _ _ (fun w hw => ?_)
  show (if w = k then (ind2 x y a || ind2 x y b) else ind2 x y w)
    = ind2 (phi a b k z x) (phi a b k z y) w
  have h1 : w = a → w = k := by
    intro e; rw [e] at hw ⊢; exact ha hw
  have h2 : w = b → w = k := by
    intro e; rw [e] at hw ⊢; exact hb hw
  have h3 : w ≠ z := by
    intro e; rw [e] at hw; exact hzS hw
  rw [Bool.eq_iff_iff]
  simp only [ind2, phi]
  split_ifs <;> simp only [Bool.or_eq_true, decide_eq_true_eq] <;> omega

theorem bi_and (S : Finset ℕ) (Ψ : (ℕ → Bool) → Bool) (hD : Dep S Ψ) (k a b : ℕ) (hab : a ≠ b)
    (ha : a ∈ S → a = k) (hb : b ∈ S → b = k) (hBi : Bi Ψ) : Bi (andL k a b Ψ) := by
  obtain ⟨z, hzS, hzk⟩ := fresh S k
  have dead1 : ∀ t, ¬ rel Ψ z t := by
    intro t ⟨r1, _, r3⟩
    have e : Ψ (ind2 z t) = Ψ (ind2 t t) := hD _ _ (fun w hw => by
      have h3 : w ≠ z := by
        intro e; rw [e] at hw; exact hzS hw
      simp [ind2, h3])
    rw [e, r3] at r1
    cases r1
  have dead2 : ∀ t, ¬ rel Ψ t z := by
    intro t ⟨r1, r2, _⟩
    have e : Ψ (ind2 t z) = Ψ (ind2 t t) := hD _ _ (fun w hw => by
      have h3 : w ≠ z := by
        intro e; rw [e] at hw; exact hzS hw
      simp [ind2, h3])
    rw [e, r2] at r1
    cases r1
  have key2 : ∀ x y, ¬ E a b x y →
      andL k a b Ψ (ind2 x y) = Ψ (ind2 (psi a b k z x) (psi a b k z y)) := by
    intro x y hE
    refine hD _ _ (fun w hw => ?_)
    show (if w = k then (ind2 x y a && ind2 x y b) else ind2 x y w)
      = ind2 (psi a b k z x) (psi a b k z y) w
    have h1 : w = a → w = k := by
      intro e; rw [e] at hw ⊢; exact ha hw
    have h2 : w = b → w = k := by
      intro e; rw [e] at hw ⊢; exact hb hw
    have h3 : w ≠ z := by
      intro e; rw [e] at hw; exact hzS hw
    unfold E at hE
    rw [Bool.eq_iff_iff]
    simp only [ind2, psi]
    split_ifs <;> simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  have key1 : ∀ x y, E a b x y → andL k a b Ψ (ind2 x y) = Ψ (ind2 k k) := by
    intro x y hE
    refine hD _ _ (fun w hw => ?_)
    show (if w = k then (ind2 x y a && ind2 x y b) else ind2 x y w) = ind2 k k w
    have h1 : w = a → w = k := by
      intro e; rw [e] at hw ⊢; exact ha hw
    have h2 : w = b → w = k := by
      intro e; rw [e] at hw ⊢; exact hb hw
    unfold E at hE
    rw [Bool.eq_iff_iff]
    simp only [ind2]
    split_ifs <;> simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  have hpsi : ∀ x, x = a ∨ x = b → psi a b k z x = z := by
    intro x hx
    unfold psi
    exact ifp (by omega)
  have tr2 : ∀ x y, ¬ E a b x y →
      (rel (andL k a b Ψ) x y ↔ rel Ψ (psi a b k z x) (psi a b k z y)) := by
    intro x y hE
    have hx : ¬ E a b x x := by unfold E; omega
    have hy : ¬ E a b y y := by unfold E; omega
    unfold rel
    rw [key2 x y hE, key2 x x hx, key2 y y hy]
  have trE : ∀ x y, E a b x y →
      (rel (andL k a b Ψ) x y ↔ (Ψ (ind2 k k) = true ∧ Ψ (ind2 z z) = false)) := by
    intro x y hE
    have hx : ¬ E a b x x := by unfold E; omega
    have hy : ¬ E a b y y := by unfold E; omega
    have px : psi a b k z x = z := hpsi x (by unfold E at hE; omega)
    have py : psi a b k z y = z := hpsi y (by unfold E at hE; omega)
    unfold rel
    rw [key1 x y hE, key2 x x hx, key2 y y hy, px, py]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.2⟩⟩
  intro p p' q q' h1 h2 h3
  by_cases hE : E a b p q
  · have hE2 : E a b p' q := by
      by_contra hn
      have r := (tr2 p' q hn).1 h2
      rw [hpsi q (by unfold E at hE; omega)] at r
      exact dead2 _ r
    have hE3 : E a b p q' := by
      by_contra hn
      have r := (tr2 p q' hn).1 h3
      rw [hpsi p (by unfold E at hE; omega)] at r
      exact dead1 _ r
    have hE4 : E a b p' q' := by
      unfold E at hE hE2 hE3 ⊢
      omega
    exact (trE p' q' hE4).2 ((trE p q hE).1 h1)
  · have r1 := (tr2 p q hE).1 h1
    have hp : ¬ (p = a ∨ p = b) := by
      intro h; rw [hpsi p h] at r1; exact dead1 _ r1
    have hq : ¬ (q = a ∨ q = b) := by
      intro h; rw [hpsi q h] at r1; exact dead2 _ r1
    have hE2 : ¬ E a b p' q := by unfold E; omega
    have hE3 : ¬ E a b p q' := by unfold E; omega
    have r2 := (tr2 p' q hE2).1 h2
    have r3 := (tr2 p q' hE3).1 h3
    have hp' : ¬ (p' = a ∨ p' = b) := by
      intro h; rw [hpsi p' h] at r2; exact dead1 _ r2
    have hE4 : ¬ E a b p' q' := by unfold E; omega
    exact (tr2 p' q' hE4).2 (hBi _ _ _ _ r1 r2 r3)

theorem lift_W (Ψ : (ℕ → Bool) → Bool) (pre : List Gate) (g : Gate) (x : List Bool) :
    Ψ (fun w => (W (pre ++ [g]) x).getD w false) =
      lift (x.length + pre.length) g Ψ (fun w => (W pre x).getD w false) :=
  congrArg Ψ (funext fun w => W_snoc_getD pre g x w)

theorem inF_snoc (N : ℕ) (pre : List Gate) (g : Gate) (Ψ : (ℕ → Bool) → Bool) :
    inF N (pre ++ [g]) Ψ = inF N pre (lift (N + pre.length) g Ψ) := by
  funext val
  unfold inF
  rw [lift_W Ψ pre g, List.length_ofFn]

theorem dep_lift (S : Finset ℕ) (Ψ : (ℕ → Bool) → Bool) (hD : Dep S Ψ) (k : ℕ) (g : Gate) :
    Dep (S.erase k ∪ g.inputs.toFinset) (lift k g Ψ) := by
  intro v v' h
  refine hD _ _ (fun w hw => ?_)
  show (if w = k then g.op.eval (g.inputs.map v) else v w)
    = (if w = k then g.op.eval (g.inputs.map v') else v' w)
  by_cases hk : w = k
  · rw [ifp hk, ifp hk]
    congr 1
    exact List.map_congr_left
      (fun i hi => h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
  · rw [ifn hk, ifn hk]
    exact h w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hk, hw⟩))

theorem bi_lift (S : Finset ℕ) (Ψ : (ℕ → Bool) → Bool) (hD : Dep S Ψ) (k : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hcard : S.card + 1 ≤ (S.erase k ∪ g.inputs.toFinset).card) (hk : k ∈ S) (hBi : Bi Ψ) :
    Bi (lift k g Ψ) := by
  have h1 := Finset.card_union_le (S.erase k) g.inputs.toFinset
  have h3 := List.toFinset_card_le g.inputs
  have h4 := Finset.card_erase_of_mem hk
  have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hk⟩
  have hl2 : g.inputs.length = 2 := by omega
  have hdisj : Disjoint (S.erase k) g.inputs.toFinset :=
    Finset.card_union_eq_card_add_card.mp (by omega)
  have hc2 : g.inputs.toFinset.card = 2 := by omega
  obtain ⟨op, inputs⟩ := g
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl2
  have hab' : inputs = [a, b] := hab
  subst hab'
  have hne : a ≠ b := by
    intro e
    subst e
    simp at hc2
  have ha : a ∈ S → a = k := by
    intro haS
    by_contra hak
    exact Finset.disjoint_left.mp hdisj (Finset.mem_erase.mpr ⟨hak, haS⟩) (by simp)
  have hb : b ∈ S → b = k := by
    intro hbS
    by_contra hbk
    exact Finset.disjoint_left.mp hdisj (Finset.mem_erase.mpr ⟨hbk, hbS⟩) (by simp)
  have hop' : op = GateOp.and ∨ op = GateOp.or := hop
  rcases hop' with rfl | rfl
  · have e : lift k ⟨GateOp.and, [a, b]⟩ Ψ = andL k a b Ψ := by
      funext val
      unfold lift andL
      simp only [List.map_cons, List.map_nil, eval_and2]
    rw [e]
    exact bi_and S Ψ hD k a b hne ha hb hBi
  · have e : lift k ⟨GateOp.or, [a, b]⟩ Ψ = orL k a b Ψ := by
      funext val
      unfold lift orL
      simp only [List.map_cons, List.map_nil, eval_or2]
    rw [e]
    exact bi_or S Ψ hD k a b ha hb hBi

theorem biN_nil (N : ℕ) (Ψ : (ℕ → Bool) → Bool) (hBi : Bi Ψ) : BiN N (inF N [] Ψ) := by
  have key : ∀ p q, p < N → q < N → inF N [] Ψ (ind2 p q) = Ψ (ind2 p q) := by
    intro p q hp hq
    refine congrArg Ψ (funext fun w => ?_)
    rw [W_nil]
    by_cases hw : w < N
    · rw [ofFn_getD _ w hw]
    · rw [ofFn_getD_ge _ w (by omega)]
      have e1 : w ≠ p := by omega
      have e2 : w ≠ q := by omega
      simp [ind2, e1, e2]
  have tr : ∀ p q, p < N → q < N → (rel (inF N [] Ψ) p q ↔ rel Ψ p q) := by
    intro p q hp hq
    unfold rel
    rw [key p q hp hq, key p p hp hp, key q q hq hq]
  intro p p' q q' hp hp' hq hq' h1 h2 h3
  rw [tr _ _ hp hq] at h1
  rw [tr _ _ hp' hq] at h2
  rw [tr _ _ hp hq'] at h3
  rw [tr _ _ hp' hq']
  exact hBi _ _ _ _ h1 h2 h3

theorem peel (N : ℕ) (pre : List Gate) :
    (∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ (S : Finset ℕ) (Ψ : (ℕ → Bool) → Bool), Dep S Ψ →
    ∃ T : Finset ℕ, T.card ≤ pre.length + S.card ∧
      (∀ x y : List Bool, x.length = N → y.length = N →
        (∀ i ∈ T, x.getD i false = y.getD i false) →
        Ψ (fun w => (W pre x).getD w false) = Ψ (fun w => (W pre y).getD w false)) ∧
      (T.card = pre.length + S.card → Bi Ψ → BiN N (inF N pre Ψ)) := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ S Ψ hD
    exact ⟨S, by simp, fun x y _ _ h => hD _ _ (fun w hw => h w hw),
      fun _ hBi => biN_nil N Ψ hBi⟩
  | append_singleton pre g ih =>
    intro h2 S Ψ hD
    have h2p : ∀ g1 ∈ pre, (g1.op = GateOp.and ∨ g1.op = GateOp.or) ∧ g1.inputs.length ≤ 2 :=
      fun g1 hg1 => h2 g1 (by simp [hg1])
    have hg := h2 g (by simp)
    by_cases hm : (N + pre.length) ∈ S
    · obtain ⟨T, hT, hTv, hTb⟩ := ih h2p (S.erase (N + pre.length) ∪ g.inputs.toFinset)
        (lift (N + pre.length) g Ψ) (dep_lift S Ψ hD _ g)
      have h1 := Finset.card_union_le (S.erase (N + pre.length)) g.inputs.toFinset
      have h3 := List.toFinset_card_le g.inputs
      have h4 := Finset.card_erase_of_mem hm
      have h5 : 0 < S.card := Finset.card_pos.mpr ⟨_, hm⟩
      have hgl := hg.2
      refine ⟨T, ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hag
        rw [lift_W Ψ pre g x, lift_W Ψ pre g y, hx, hy]
        exact hTv x y hx hy hag
      · intro hc hBi
        rw [List.length_append, List.length_singleton] at hc
        rw [inF_snoc]
        exact hTb (by omega) (bi_lift S Ψ hD _ g hg.1 hg.2 (by omega) hm hBi)
    · obtain ⟨T, hT, hTv, _⟩ := ih h2p S Ψ hD
      have e : ∀ x : List Bool, x.length = N →
          Ψ (fun w => (W (pre ++ [g]) x).getD w false) = Ψ (fun w => (W pre x).getD w false) := by
        intro x hx
        refine hD _ _ (fun w hw => ?_)
        show (W (pre ++ [g]) x).getD w false = (W pre x).getD w false
        have hne : ¬ w = x.length + pre.length := by
          intro e
          rw [e, hx] at hw
          exact hm hw
        rw [W_snoc_getD, ifn hne]
      refine ⟨T, ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hag
        rw [e x hx, e y hy]
        exact hTv x y hx hy hag
      · intro hc
        rw [List.length_append, List.length_singleton] at hc
        omega

theorem single_row {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hrep : PEqualNP.Represents.Represents A C)
    (a : Fin n) (c : Fin m) (h : A a c = false) :
    circuitFun (n + m) C (pt n m a.val a.val) = false := by
  cases hc : circuitFun (n + m) C (pt n m a.val a.val)
  · rfl
  · have h3 := circuitFun_mono (n + m) C hAO (pt n m a.val a.val) (pt n m a.val (n + c.val))
      (fun i hi => by
        simp only [pt, decide_eq_true_eq, Bool.or_eq_true] at hi ⊢
        omega) hc
    rw [rep_pt hrep a c, h] at h3
    cases h3

theorem single_col {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hrep : PEqualNP.Represents.Represents A C)
    (r : Fin n) (v : Fin m) (h : A r v = false) :
    circuitFun (n + m) C (pt n m (n + v.val) (n + v.val)) = false := by
  cases hc : circuitFun (n + m) C (pt n m (n + v.val) (n + v.val))
  · rfl
  · have h3 := circuitFun_mono (n + m) C hAO (pt n m (n + v.val) (n + v.val))
      (pt n m r.val (n + v.val))
      (fun i hi => by
        simp only [pt, decide_eq_true_eq, Bool.or_eq_true] at hi ⊢
        omega) hc
    rw [rep_pt hrep r v, h] at h3
    cases h3


theorem K_spec (n m : ℕ) (C : Circuit) : ∃ K : Finset (Fin (n + m)),
    K.card = (rs n m C).card + (cs n m C).card ∧
    ∀ i ∈ K, ∃ x y : Fin (n + m) → Bool, circuitFun (n + m) C x ≠ circuitFun (n + m) C y ∧
      ∀ k : Fin (n + m), k ≠ i → x k = y k := by
  have hdisj : Disjoint ((rs n m C).image (Fin.castAdd m)) ((cs n m C).image (Fin.natAdd n)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨b, _, hb⟩ := Finset.mem_image.1 hx2
    have h2 := congrArg Fin.val hb
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
    have := a.isLt
    omega
  have hK : ∀ i ∈ (rs n m C).image (Fin.castAdd m) ∪ (cs n m C).image (Fin.natAdd n),
      ∃ x y : Fin (n + m) → Bool, circuitFun (n + m) C x ≠ circuitFun (n + m) C y ∧
        ∀ k : Fin (n + m), k ≠ i → x k = y k := by
    intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      simp only [rs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨v, hv⟩ := hu
      refine ⟨_, _, hv, fun k hk => ?_⟩
      have hk' : k.val ≠ u.val := fun e => hk (Fin.ext (by simp [e]))
      simp [pt, q, hk']
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
      simp only [cs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨u, hu⟩ := hw
      refine ⟨_, _, hu, fun k hk => ?_⟩
      have hk' : k.val ≠ n + w.val := fun e => hk (Fin.ext (by simp only [Fin.val_natAdd]; omega))
      simp [pt, q, hk']
  refine ⟨_, ?_, hK⟩
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => dc_cast_inj h),
    Finset.card_image_of_injective _ (fun a b h => dc_nat_inj h)]

theorem gen2 (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (hmono : Monotone2 C)
    (hrep : PEqualNP.Represents.Represents A C)
    (a b : Fin n) (v w : Fin m) (h1 : A a v = true) (h2 : A b v = true) (h3 : A a w = true)
    (h4 : A b w = false) (ha : ∃ c, A a c = false) (hv : ∃ r, A r v = false)
    (hw : ∃ r, A r w = false) : (rs n m C).card + (cs n m C).card ≤ C.size := by
  have hAO := andOrOnly_of_monotone2 hmono
  obtain ⟨K, hKc, hK⟩ := K_spec n m C
  obtain ⟨T, hT, hdep, hbi⟩ := peel (n + m) C.gates
    (fun g hg => ⟨hAO g hg, monotone2_len hmono hg⟩) {C.output} (fun val => val C.output)
    (fun v v' h => h _ (Finset.mem_singleton_self _))
  have hall : ∀ i ∈ K, i.val ∈ T := by
    intro i hi
    by_contra hk
    obtain ⟨x, y, hne, hxy⟩ := hK i hi
    exact hne (hdep (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (fun j hj => agree_ofFn x y i hxy j (fun h => hk (h ▸ hj))))
  have hcard : K.card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => hall i hi)
      (fun a _ b _ h => Fin.ext h)
  rw [Finset.card_singleton] at hT hbi
  by_cases htight : T.card = C.gates.length + 1
  · exfalso
    have hB := hbi htight (by
      intro p p' q q' r1 _ _
      exfalso
      obtain ⟨r1, r2, r3⟩ := r1
      simp only [ind2, Bool.or_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at r1 r2 r3
      omega)
    have rl : ∀ (r : Fin n) (c : Fin m), A r c = true → (∃ c', A r c' = false) →
        (∃ r', A r' c = false) →
        rel (inF (n + m) C.gates (fun val => val C.output)) r.val (n + c.val) := by
      intro r c hrc ⟨c', hc'⟩ ⟨r', hr'⟩
      unfold rel
      exact ⟨(rep_pt hrep r c).trans hrc, single_row hAO hrep r c' hc',
        single_col hAO hrep r' c hr'⟩
    have r4 := hB a.val b.val (n + v.val) (n + w.val) (by omega) (by omega) (by omega)
      (by omega) (rl a v h1 ha hv) (rl b v h2 ⟨w, h4⟩ hv) (rl a w h3 ha hw)
    have r5 : A b w = true := (rep_pt hrep b w).symm.trans r4.1
    rw [h4] at r5
    cases r5
  · show (rs n m C).card + (cs n m C).card ≤ C.gates.length
    omega

theorem final (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 5)
    (hrep : PEqualNP.Represents.Represents A C) : False := by
  by_cases hex : ∃ g ∈ C.gates, isNot g = true
  · have hpos : 0 < C.gates.countP isNot := List.countP_pos_iff.2 hex
    obtain ⟨u0, v0, h⟩ := twin_aux 4 4 A C (by omega) (by omega) hfan hrep
    have h1 := facts1 u0 v0
    omega
  · have hmono := monotone2_of_no_not C hfan hex
    obtain ⟨hr, hc⟩ := mono_sub 4 4 A C hmono hrep
    have h := gen2 4 4 A C hmono hrep 0 1 1 2 (by decide) (by decide) (by decide) (by decide)
      ⟨3, by decide⟩ ⟨3, by decide⟩ ⟨1, by decide⟩
    have h1 := Finset.card_le_card hr
    have h2 := Finset.card_le_card hc
    have h3 := facts2
    omega

end PEqualNP.Outside.L_meta_19450

theorem PEqualNP.Outside.L_meta_19450 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (311 : ℕ).testBit (4 * u.val + v.val)) C := by
  rintro ⟨C, hfan, hsize, hrep⟩
  exact PEqualNP.Outside.L_meta_19450.final C hfan hsize hrep
