import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19452.Cn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

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

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem step_ne (w : List Bool) (g : Gate) (j : ℕ) (hj : j ≠ w.length) :
    (step w g).getD j false = w.getD j false := by
  by_cases h : j < w.length
  · exact step_lt w g j h
  · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by omega)]

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

theorem gD_lt {α : Type} (l l2 : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

theorem gD_len {α : Type} (l : List α) (v d : α) (k : ℕ) (hk : k = l.length) :
    (l ++ [v]).getD k d = v := by
  subst hk; simp [List.getD]

theorem gD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def cn (N : ℕ) (gs : List Gate) : List (List ℕ) := gs.foldl (coneStep N) []

theorem cn_snoc (N : ℕ) (gs : List Gate) (g : Gate) : cn N (gs ++ [g]) = coneStep N (cn N gs) g := by
  simp [cn, List.foldl_append]

def dg : Gate := ⟨GateOp.and, []⟩

theorem inv (N : ℕ) (gs : List Gate) :
    (cn N gs).length = gs.length ∧
    (∀ j, ∀ i ∈ (cn N gs).getD j [], i < j) ∧
    ∀ j, j < gs.length → ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ a, a < N → (a ∈ (gs.getD j dg).inputs ∨ ∃ i ∈ (cn N gs).getD j [], a ∈ (gs.getD i dg).inputs) →
        x.getD a false = y.getD a false) →
      (W gs x).getD (N + j) false = (W gs y).getD (N + j) false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j i hi
      simp [cn] at hi
    · intro j hj
      simp at hj
  | append_singleton pre g ih =>
    obtain ⟨hlen, hlt, hdep⟩ := ih
    have hcn : cn N (pre ++ [g]) = cn N pre ++ [(g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + (cn N pre).length))).flatMap (fun w => (w - N) :: (cn N pre).getD (w - N) [])] := by
      rw [cn_snoc]; rfl
    have hnew : ∀ i, i ∈ (g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + (cn N pre).length))).flatMap (fun w => (w - N) :: (cn N pre).getD (w - N) []) ↔ ∃ w ∈ g.inputs, N ≤ w ∧ w < N + pre.length ∧ (i = w - N ∨ i ∈ (cn N pre).getD (w - N) []) := by
      intro i
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons, hlen]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩; exact ⟨w, hw, h1, h2, h3⟩
      · rintro ⟨w, hw, h1, h2, h3⟩; exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hcn]; simp [hlen]
    · intro j i hi
      rw [hcn] at hi
      rcases lt_trichotomy j pre.length with h | h | h
      · rw [gD_lt _ _ _ _ (by omega)] at hi
        exact hlt j i hi
      · rw [gD_len _ _ _ _ (by omega)] at hi
        obtain ⟨w, _, h1, h2, h3⟩ := (hnew i).1 hi
        rcases h3 with h3 | h3
        · omega
        · have := hlt _ _ h3; omega
      · rw [gD_ge _ _ _ (by simp; omega)] at hi
        simp at hi
    · intro j hj x y hx hy hag
      have hlx : (W pre x).length = N + pre.length := by rw [W_length, hx]
      have hly : (W pre y).length = N + pre.length := by rw [W_length, hy]
      rw [W_snoc, W_snoc]
      have hj' : j < pre.length + 1 := by simpa using hj
      by_cases h : j < pre.length
      · rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega)]
        apply hdep j h x y hx hy
        intro a ha hor
        apply hag a ha
        rcases hor with hor | ⟨i, hi, hia⟩
        · left; rwa [gD_lt _ _ _ _ h]
        · right
          refine ⟨i, ?_, ?_⟩
          · rw [hcn, gD_lt _ _ _ _ (by omega)]; exact hi
          · rwa [gD_lt _ _ _ _ (by have := hlt j i hi; omega)]
      · have hje : j = pre.length := by omega
        rw [step_last _ _ _ (by omega), step_last _ _ _ (by omega)]
        congr 1
        apply List.map_congr_left
        intro w hw
        rcases lt_or_ge w N with hwN | hwN
        · rw [W_prefix _ _ _ (by omega), W_prefix _ _ _ (by omega)]
          apply hag w hwN
          left
          rw [gD_len _ _ _ _ hje]; exact hw
        · by_cases hw2 : w < N + pre.length
          · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
            apply hdep k (by omega) x y hx hy
            intro a ha hor
            apply hag a ha
            right
            rcases hor with hor | ⟨i, hi, hia⟩
            · refine ⟨k, ?_, ?_⟩
              · rw [hcn, gD_len _ _ _ _ (by omega)]
                exact (hnew k).2 ⟨N + k, hw, by omega, hw2, Or.inl (by omega)⟩
              · rwa [gD_lt _ _ _ _ (by omega)]
            · refine ⟨i, ?_, ?_⟩
              · rw [hcn, gD_len _ _ _ _ (by omega)]
                exact (hnew i).2 ⟨N + k, hw, by omega, hw2, Or.inr (by rw [Nat.add_sub_cancel_left]; exact hi)⟩
              · rwa [gD_lt _ _ _ _ (by have := hlt k i hi; omega)]
          · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]

theorem eval_dep (N : ℕ) (C : Circuit) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hout : C.output < N → x.getD C.output false = y.getD C.output false)
    (hc : ∀ j, j < C.gates.length → (C.output = N + j ∨ (N ≤ C.output ∧ InCone N C j (C.output - N))) →
      ∀ a ∈ (C.gates.getD j ⟨GateOp.and, []⟩).inputs, a < N → x.getD a false = y.getD a false) :
    C.eval x = C.eval y := by
  rw [eval_W, eval_W]
  obtain ⟨_, hlt, hdep⟩ := inv N C.gates
  rcases lt_or_ge C.output N with ho | ho
  · rw [W_prefix _ _ _ (by omega), W_prefix _ _ _ (by omega)]
    exact hout ho
  · by_cases ho2 : C.output < N + C.gates.length
    · obtain ⟨k, hk⟩ : ∃ k, C.output = N + k := ⟨C.output - N, by omega⟩
      rw [hk]
      apply hdep k (by omega) x y hx hy
      intro a ha hor
      rcases hor with hor | ⟨i, hi, hia⟩
      · exact hc k (by omega) (Or.inl hk) a hor ha
      · have hik := hlt k i hi
        refine hc i (by omega) (Or.inr ⟨ho, ?_⟩) a hia ha
        have : C.output - N = k := by omega
        rw [this]
        exact hi
    · rw [W_ge _ _ _ (by omega), W_ge _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_19452.Cn

namespace PEqualNP.Outside.L_meta_19452

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


theorem two_silent (N : ℕ) (C : Circuit) (a b : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (ha : C.output ≠ a ∧ ∀ g < C.gates.length, (C.output = N + g ∨ (N ≤ C.output ∧
      PEqualNP.EdgeOwnership.InCone N C g (C.output - N))) →
      a ∉ (C.gates.getD g ⟨GateOp.and, []⟩).inputs)
    (hb : C.output ≠ b ∧ ∀ g < C.gates.length, (C.output = N + g ∨ (N ≤ C.output ∧
      PEqualNP.EdgeOwnership.InCone N C g (C.output - N))) →
      b ∉ (C.gates.getD g ⟨GateOp.and, []⟩).inputs)
    (hxy : ∀ i, i ≠ a → i ≠ b → x.getD i false = y.getD i false) : C.eval x = C.eval y := by
  apply Cn.eval_dep N C x y hx hy
  · intro _
    exact hxy _ ha.1 hb.1
  · intro j hj hc w hw _
    apply hxy
    · intro h
      exact ha.2 j hj hc (h ▸ hw)
    · intro h
      exact hb.2 j hj hc (h ▸ hw)

theorem pt_getD (n m a b i : ℕ) (ha : a < n + m) (hb : b < n + m) :
    (List.ofFn (pt n m a b)).getD i false = (decide (i = a) || decide (i = b)) := by
  by_cases hi : i < n + m
  · rw [ofFn_getD _ i hi]
    rfl
  · rw [ofFn_getD_ge _ i (by omega), decide_eq_false (by omega), decide_eq_false (by omega)]
    rfl

theorem q_getD (n m b i : ℕ) (hb : b < n + m) :
    (List.ofFn (q n m b)).getD i false = decide (i = b) := by
  by_cases hi : i < n + m
  · rw [ofFn_getD _ i hi]
    rfl
  · rw [ofFn_getD_ge _ i (by omega), decide_eq_false (by omega)]

theorem main (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (u u' : Fin n)
    (hrep : PEqualNP.Represents.Represents A C)
    (hu : C.output ≠ u.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧
      PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) →
      u.val ∉ (C.gates.getD g ⟨GateOp.and, []⟩).inputs)
    (hu' : C.output ≠ u'.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧
      PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) →
      u'.val ∉ (C.gates.getD g ⟨GateOp.and, []⟩).inputs)
    (v : Fin m) : A u v = A u' v := by
  have h1 := u.isLt
  have h2 := u'.isLt
  have h3 := v.isLt
  rw [← hrep u v, ← hrep u' v, oneEach_pt, oneEach_pt]
  apply two_silent (n + m) C u.val u'.val _ _ (by simp) (by simp) hu hu'
  intro i hi hi'
  rw [pt_getD n m _ _ i (by omega) (by omega), pt_getD n m _ _ i (by omega) (by omega),
    decide_eq_false hi, decide_eq_false hi']

end PEqualNP.Outside.L_meta_19452

theorem PEqualNP.Outside.L_meta_19452 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (u u' : Fin n), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ u.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → (C.output ≠ u'.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u'.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ v : Fin m, A u v = A u' v := by
  intro n m A C u u' _ hrep hu hu' v
  exact PEqualNP.Outside.L_meta_19452.main n m A C u u' hrep hu hu' v
