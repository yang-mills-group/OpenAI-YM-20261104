import YM.Integration.AnchoredTensorGrowthFacts
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Finite anchored tensor contraction

The selected directed edges form the supplied rooted growth order. A vertex
tensor is charged once, at its incoming selected edge, and the root tensor is
charged by its fixed-port marginal. All other edge labels remain in a separate
pointwise-cost product. The proof uses no division and permits zero costs.
-/

set_option autoImplicit false

open scoped BigOperators

namespace YM.Integration.AnchoredTensorContraction

noncomputable section

section Coordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, Fintype (X v)]

private def freeAssignments (S : Finset V) (base : ∀ v, X v) :
    Finset (∀ v, X v) := by
  classical
  exact Finset.univ.filter (fun x => ∀ v, v ∉ S → x v = base v)

private theorem mem_freeAssignments (S : Finset V) (base x : ∀ v, X v) :
    x ∈ freeAssignments S base ↔ ∀ v, v ∉ S → x v = base v := by
  classical
  simp [freeAssignments]

private theorem freeAssignments_empty (base : ∀ v, X v) :
    freeAssignments ∅ base = {base} := by
  classical
  ext x
  constructor
  · intro hx
    apply Finset.mem_singleton.mpr
    funext v
    exact (mem_freeAssignments ∅ base x).mp hx v (by simp)
  · intro hx
    have hxb : x = base := Finset.mem_singleton.mp hx
    subst x
    exact (mem_freeAssignments ∅ base base).mpr (fun _ _ => rfl)

private theorem freeAssignments_univ (base : ∀ v, X v) :
    freeAssignments Finset.univ base = Finset.univ := by
  classical
  ext x
  simp [freeAssignments]

/-- Freeing a new coordinate is an exact bijection, with no cardinal factor. -/
private theorem sum_freeAssignments_insert (S : Finset V) (base : ∀ v, X v)
    (v : V) (hv : v ∉ S) (F : (∀ v, X v) → ℝ) :
    (∑ y ∈ freeAssignments (insert v S) base, F y) =
      ∑ x ∈ freeAssignments S base, ∑ z : X v, F (Function.update x v z) := by
  classical
  have hb :
      (∑ p ∈ freeAssignments S base ×ˢ (Finset.univ : Finset (X v)),
        F (Function.update p.1 v p.2)) =
      ∑ y ∈ freeAssignments (insert v S) base, F y := by
    apply Finset.sum_bij (fun p _ => Function.update p.1 v p.2)
    · intro p hp
      apply (mem_freeAssignments _ _ _).mpr
      intro w hw
      have hwv : w ≠ v := by
        intro heq
        subst w
        exact hw (Finset.mem_insert_self _ _)
      have hws : w ∉ S := fun hmem => hw (Finset.mem_insert_of_mem hmem)
      rw [Function.update_of_ne hwv]
      exact (mem_freeAssignments _ _ _).mp (Finset.mem_product.mp hp).1 w hws
    · intro p hp q hq hpq
      apply Prod.ext
      · funext w
        by_cases hw : w = v
        · subst w
          exact ((mem_freeAssignments _ _ _).mp
            (Finset.mem_product.mp hp).1 v hv).trans
            ((mem_freeAssignments _ _ _).mp
              (Finset.mem_product.mp hq).1 v hv).symm
        · simpa only [Function.update_of_ne hw] using congrFun hpq w
      · simpa only [Function.update_self] using congrFun hpq v
    · intro y hy
      let x : ∀ w, X w := Function.update y v (base v)
      have hx : x ∈ freeAssignments S base := by
        apply (mem_freeAssignments _ _ _).mpr
        intro w hw
        by_cases hwv : w = v
        · subst w
          simp only [x, Function.update_self]
        · rw [show x w = y w by exact Function.update_of_ne hwv _ _]
          exact (mem_freeAssignments _ _ _).mp hy w (by simp [hwv, hw])
      refine ⟨(x, y v), Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, ?_⟩
      funext w
      by_cases hw : w = v
      · subst w
        simp only [Function.update_self]
      · simp only [x, Function.update_of_ne hw]
    · intro p _hp
      rfl
  rw [Finset.sum_product] at hb
  exact hb.symm

end Coordinates

private theorem list_prod_nonneg {J : Type*} (es : List J) (f : J → ℝ)
    (hf : ∀ e, 0 ≤ f e) : 0 ≤ (es.map f).prod := by
  induction es with
  | nil => simp
  | cons e es ih =>
    exact mul_nonneg (hf e) ih

section Kernels

variable {V J : Type*}
variable {X : V → Type*}
variable {src dst : J → V} {root : V}

private def visited [DecidableEq V] (dst : J → V) (root : V) (es : List J) : Finset V :=
  (root :: es.map dst).toFinset

private def rootedWeight (R : X root → ℝ)
    (K : ∀ e, X (src e) → X (dst e) → ℝ) (es : List J) (x : ∀ v, X v) : ℝ :=
  R (x root) * (es.map (fun e => K e (x (src e)) (x (dst e)))).prod

private theorem rootedWeight_nonneg (R : X root → ℝ)
    (K : ∀ e, X (src e) → X (dst e) → ℝ)
    (hR : ∀ z, 0 ≤ R z) (hK : ∀ e u v, 0 ≤ K e u v)
    (es : List J) (x : ∀ v, X v) : 0 ≤ rootedWeight R K es x :=
  mul_nonneg (hR _) (list_prod_nonneg es _ (fun e => hK e _ _))

private theorem rootedWeight_snoc (R : X root → ℝ)
    (K : ∀ e, X (src e) → X (dst e) → ℝ)
    (es : List J) (e : J) (x : ∀ v, X v) :
    rootedWeight R K (es ++ [e]) x =
      rootedWeight R K es x * K e (x (src e)) (x (dst e)) := by
  simp only [rootedWeight, List.map_append, List.map_singleton,
    List.prod_append, List.prod_singleton, mul_assoc]

private theorem rootedWeight_update [DecidableEq V] (R : X root → ℝ)
    (K : ∀ e, X (src e) → X (dst e) → ℝ)
    {es : List J} (g : Growth src dst root es)
    (v : V) (hv : v ∉ root :: es.map dst) (x : ∀ v, X v) (z : X v) :
    rootedWeight R K es (Function.update x v z) = rootedWeight R K es x := by
  have hr : root ≠ v := by
    intro heq
    subst v
    exact hv List.mem_cons_self
  have hsrc (e : J) (he : e ∈ es) : src e ≠ v := by
    intro heq
    exact hv (heq ▸ g.source_mem e he)
  have hdst (e : J) (he : e ∈ es) : dst e ≠ v := by
    intro heq
    apply hv
    exact heq ▸ List.mem_cons_of_mem root (List.mem_map.mpr ⟨e, he, rfl⟩)
  unfold rootedWeight
  rw [Function.update_of_ne hr]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp only [Function.update_of_ne (hsrc e he), Function.update_of_ne (hdst e he)]

variable [Fintype V] [DecidableEq V] [∀ v, Fintype (X v)]

private theorem partial_kernel_bound (R : X root → ℝ)
    (K : ∀ e, X (src e) → X (dst e) → ℝ)
    (a : ℝ) (b : J → ℝ)
    (hR0 : ∀ z, 0 ≤ R z) (hR : (∑ z, R z) ≤ a)
    (hK0 : ∀ e u v, 0 ≤ K e u v)
    (hK : ∀ e u, (∑ v, K e u v) ≤ b e)
    (base : ∀ v, X v) {es : List J} (g : Growth src dst root es) :
    (∑ x ∈ freeAssignments (visited dst root es) base, rootedWeight R K es x) ≤
      a * (es.map b).prod := by
  induction g with
  | nil =>
    have hv : visited dst root ([] : List J) = insert root ∅ := by
      simp [visited]
    rw [hv, sum_freeAssignments_insert ∅ base root (by simp),
      freeAssignments_empty, Finset.sum_singleton]
    simpa only [rootedWeight, List.map_nil, List.prod_nil, mul_one,
      Function.update_self] using hR
  | @snoc es previous e hsrc hdst ih =>
    have hv : dst e ∉ visited dst root es := by
      simpa only [visited, List.mem_toFinset] using hdst
    have hvis : visited dst root (es ++ [e]) =
        insert (dst e) (visited dst root es) := by
      ext v
      simp [visited, or_left_comm]
    have hsd : src e ≠ dst e := by
      intro heq
      exact hdst (heq ▸ hsrc)
    have hupdate (x : ∀ v, X v) (z : X (dst e)) :
        rootedWeight R K (es ++ [e]) (Function.update x (dst e) z) =
          rootedWeight R K es x * K e (x (src e)) z := by
      rw [rootedWeight_snoc, rootedWeight_update R K previous (dst e) hdst]
      simp only [Function.update_of_ne hsd, Function.update_self]
    have hb : 0 ≤ b e :=
      (Finset.sum_nonneg (fun z _ => hK0 e (base (src e)) z)).trans
        (hK e (base (src e)))
    rw [hvis, sum_freeAssignments_insert _ base (dst e) hv]
    calc
      (∑ x ∈ freeAssignments (visited dst root es) base,
          ∑ z : X (dst e),
            rootedWeight R K (es ++ [e]) (Function.update x (dst e) z)) ≤
          ∑ x ∈ freeAssignments (visited dst root es) base,
            rootedWeight R K es x * b e := by
        apply Finset.sum_le_sum
        intro x _hx
        simp_rw [hupdate]
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hK e (x (src e)))
          (rootedWeight_nonneg R K hR0 hK0 es x)
      _ = (∑ x ∈ freeAssignments (visited dst root es) base,
          rootedWeight R K es x) * b e := by rw [Finset.sum_mul]
      _ ≤ (a * (es.map b).prod) * b e := mul_le_mul_of_nonneg_right ih hb
      _ = a * ((es ++ [e]).map b).prod := by
        simp only [List.map_append, List.map_singleton,
          List.prod_append, List.prod_singleton, mul_assoc]

/-- A finite growth order contracts nonnegative kernels against a priced root.
The root's complete sum is charged explicitly; it is not a free vacuum sum. -/
theorem kernel_growth_bound (R : X root → ℝ)
    (K : ∀ e, X (src e) → X (dst e) → ℝ)
    (a : ℝ) (b : J → ℝ)
    (hR0 : ∀ z, 0 ≤ R z) (hR : (∑ z, R z) ≤ a)
    (hK0 : ∀ e u v, 0 ≤ K e u v)
    (hK : ∀ e u, (∑ v, K e u v) ≤ b e)
    (base : ∀ v, X v) {es : List J} (g : Growth src dst root es)
    (cover : ∀ v, v ∈ root :: es.map dst) :
    (∑ x : (∀ v, X v),
      R (x root) * (es.map (fun e => K e (x (src e)) (x (dst e)))).prod) ≤
      a * (es.map b).prod := by
  have hv : visited dst root es = Finset.univ := by
    ext v
    simp only [visited, List.mem_toFinset, Finset.mem_univ, iff_true]
    exact cover v
  have hp := partial_kernel_bound R K a b hR0 hR hK0 hK base g
  rw [hv, freeAssignments_univ] at hp
  exact hp

end Kernels

/-- A tensor's uniform one-port marginal controls its contraction with one row. -/
theorem one_port_edge_le {P I : Type*} [Fintype P] [DecidableEq P]
    [Fintype I] [DecidableEq I]
    (A : (P → I) → ℂ) (C : I → I → ℂ) (p : P) (i : I) (a b : ℝ)
    (hA : ∀ j, (∑ z : P → I, if z p = j then ‖A z‖ else 0) ≤ a)
    (hC : (∑ j, ‖C i j‖) ≤ b) :
    (∑ z : P → I, ‖A z‖ * ‖C i (z p)‖) ≤ a * b := by
  have ha : 0 ≤ a :=
    (Finset.sum_nonneg
      (f := fun z : P → I => if z p = i then ‖A z‖ else 0) (fun z _ => by
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl)).trans (hA i)
  calc
    (∑ z : P → I, ‖A z‖ * ‖C i (z p)‖) =
        ∑ z : P → I, ∑ j : I,
          (if z p = j then ‖A z‖ else 0) * ‖C i j‖ := by
      apply Finset.sum_congr rfl
      intro z _hz
      simp [ite_mul]
    _ = ∑ j : I, ∑ z : P → I,
        (if z p = j then ‖A z‖ else 0) * ‖C i j‖ := Finset.sum_comm
    _ = ∑ j : I, (∑ z : P → I, if z p = j then ‖A z‖ else 0) * ‖C i j‖ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul]
    _ ≤ ∑ j : I, a * ‖C i j‖ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hA j) (norm_nonneg _))
    _ = a * ∑ j : I, ‖C i j‖ := by rw [Finset.mul_sum]
    _ ≤ a * b := mul_le_mul_of_nonneg_left hC ha

private theorem vertex_product {V J : Type*} [Fintype V] [DecidableEq V]
    {src dst : J → V} {root : V} {es : List J}
    (g : Growth src dst root es) (cover : ∀ v, v ∈ root :: es.map dst) (f : V → ℝ) :
    f root * (es.map (fun e => f (dst e))).prod = ∏ v, f v := by
  have hv : (root :: es.map dst).toFinset = Finset.univ := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact cover v
  have hp := List.prod_toFinset f g.vertices_nodup
  rw [hv] at hp
  simpa only [List.map_cons, List.map_map, List.prod_cons, Function.comp_def] using hp.symm

private theorem product_split {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset J) (f : J → ℝ) :
    (∏ e, f e) = (∏ e ∈ S, f e) * (∏ e ∈ Finset.univ \ S, f e) :=
  (Finset.prod_sdiff (f := f) S.subset_univ).symm.trans (mul_comm _ _)

section Tensors

variable {V J I : Type*}
variable [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable [Fintype I] [DecidableEq I]
variable (P : V → Type*) [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]
variable (src dst : J → V)
variable (left : ∀ e, P (src e)) (right : ∀ e, P (dst e))
variable (A : ∀ v, (P v → I) → ℂ) (C : J → I → I → ℂ)
variable (a : V → ℝ) (b c : J → ℝ)
variable (root : V) (p0 : P root) (i0 : I)
variable {es : List J} (g : Growth src dst root es)
variable (cover : ∀ v, v ∈ root :: es.map dst)
variable (hA : ∀ v p i, (∑ z : P v → I, if z p = i then ‖A v z‖ else 0) ≤ a v)
variable (hrow : ∀ e i, (∑ j : I, ‖C e i j‖) ≤ b e)

include g cover hA hrow

/-- An anchored finite tensor contraction. Selected edges use row-sum costs;
every remaining original edge, including loops and parallel edges, uses its
declared pointwise cost. The supplied growth order is never changed. -/
theorem anchored_tensor_bound
    (hpoint : ∀ e, e ∉ es → ∀ i j, ‖C e i j‖ ≤ c e) :
    (∑ x : (∀ v, P v → I), if x root p0 = i0 then
      (∏ v, ‖A v (x v)‖) *
        (∏ e, ‖C e (x (src e) (left e)) (x (dst e) (right e))‖) else 0) ≤
      (∏ v, a v) * (∏ e ∈ es.toFinset, b e) *
        (∏ e ∈ Finset.univ \ es.toFinset, c e) := by
  let R0 : (P root → I) → ℝ := fun z => if z p0 = i0 then ‖A root z‖ else 0
  let K0 : ∀ e, (P (src e) → I) → (P (dst e) → I) → ℝ :=
    fun e u v => ‖A (dst e) v‖ * ‖C e (u (left e)) (v (right e))‖
  have hR0 : ∀ z, 0 ≤ R0 z := by
    intro z
    dsimp only [R0]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hK0 : ∀ e u v, 0 ≤ K0 e u v := by
    intro e u v
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hK : ∀ e u, (∑ v, K0 e u v) ≤ a (dst e) * b e := by
    intro e u
    exact one_port_edge_le (A (dst e)) (C e) (right e) (u (left e))
      (a (dst e)) (b e) (hA (dst e) (right e)) (hrow e (u (left e)))
  have htree := kernel_growth_bound (X := fun v => P v → I)
    (src := src) (dst := dst) (root := root) R0 K0 (a root) (fun e => a (dst e) * b e)
    hR0 (hA root p0 i0) hK0 hK (fun _ _ => i0) g cover
  have hcost : a root * (es.map (fun e => a (dst e) * b e)).prod =
      (∏ v, a v) * (∏ e ∈ es.toFinset, b e) := by
    rw [List.prod_map_mul, ← mul_assoc, vertex_product g cover a,
      ← List.prod_toFinset b g.edges_nodup]
  change (∑ x : (∀ v, P v → I), rootedWeight R0 K0 es x) ≤
    a root * (es.map (fun e => a (dst e) * b e)).prod at htree
  rw [hcost] at htree
  have hweight (x : ∀ v, P v → I) :
      rootedWeight R0 K0 es x =
        if x root p0 = i0 then
          (∏ v, ‖A v (x v)‖) *
            (∏ e ∈ es.toFinset, ‖C e (x (src e) (left e)) (x (dst e) (right e))‖)
        else 0 := by
    by_cases hx : x root p0 = i0
    · simp only [rootedWeight, R0, K0, if_pos hx, List.prod_map_mul]
      rw [← mul_assoc, vertex_product g cover (fun v => ‖A v (x v)‖),
        ← List.prod_toFinset
          (fun e => ‖C e (x (src e) (left e)) (x (dst e) (right e))‖) g.edges_nodup]
    · simp only [rootedWeight, R0, if_neg hx, zero_mul]
  have hc : ∀ e ∈ Finset.univ \ es.toFinset, 0 ≤ c e := by
    intro e he
    have hne : e ∉ es := fun hm => (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr hm)
    exact (norm_nonneg (C e i0 i0)).trans (hpoint e hne i0 i0)
  have hrest : 0 ≤ ∏ e ∈ Finset.univ \ es.toFinset, c e := Finset.prod_nonneg hc
  calc
    (∑ x : (∀ v, P v → I), if x root p0 = i0 then
        (∏ v, ‖A v (x v)‖) *
          (∏ e, ‖C e (x (src e) (left e)) (x (dst e) (right e))‖) else 0) ≤
        ∑ x : (∀ v, P v → I), rootedWeight R0 K0 es x *
          (∏ e ∈ Finset.univ \ es.toFinset, c e) := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [hweight]
      by_cases hx : x root p0 = i0
      · simp only [if_pos hx]
        have hprod :
            (∏ e ∈ Finset.univ \ es.toFinset,
              ‖C e (x (src e) (left e)) (x (dst e) (right e))‖) ≤
            ∏ e ∈ Finset.univ \ es.toFinset, c e := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro e he
          have hne : e ∉ es :=
            fun hm => (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr hm)
          exact hpoint e hne _ _
        rw [product_split es.toFinset
          (fun e => ‖C e (x (src e) (left e)) (x (dst e) (right e))‖), ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hprod
          (mul_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
            (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
      · simp only [if_neg hx, zero_mul, le_refl]
    _ = (∑ x : (∀ v, P v → I), rootedWeight R0 K0 es x) *
        (∏ e ∈ Finset.univ \ es.toFinset, c e) := by rw [Finset.sum_mul]
    _ ≤ ((∏ v, a v) * (∏ e ∈ es.toFinset, b e)) *
        (∏ e ∈ Finset.univ \ es.toFinset, c e) :=
      mul_le_mul_of_nonneg_right htree hrest

/-- The row bound also dominates every entry, giving one cost per original edge. -/
theorem anchored_tensor_row_bound :
    (∑ x : (∀ v, P v → I), if x root p0 = i0 then
      (∏ v, ‖A v (x v)‖) *
        (∏ e, ‖C e (x (src e) (left e)) (x (dst e) (right e))‖) else 0) ≤
      (∏ v, a v) * (∏ e, b e) := by
  have hpoint : ∀ e, e ∉ es → ∀ i j, ‖C e i j‖ ≤ b e := by
    intro e _he i j
    exact (Finset.single_le_sum (f := fun k => ‖C e i k‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (hrow e i)
  have hb := anchored_tensor_bound P src dst left right A C a b b root p0 i0
    g cover hA hrow hpoint
  rw [mul_assoc, ← product_split es.toFinset b] at hb
  exact hb

/-- Extra consistency restrictions can be retained and then dominated because
every summand is nonnegative. No restriction is silently identified with truth. -/
theorem anchored_tensor_restricted_bound
    (hpoint : ∀ e, e ∉ es → ∀ i j, ‖C e i j‖ ≤ c e)
    (q : (∀ v, P v → I) → Prop) [DecidablePred q] :
    (∑ x : (∀ v, P v → I), if x root p0 = i0 ∧ q x then
      (∏ v, ‖A v (x v)‖) *
        (∏ e, ‖C e (x (src e) (left e)) (x (dst e) (right e))‖) else 0) ≤
      (∏ v, a v) * (∏ e ∈ es.toFinset, b e) *
        (∏ e ∈ Finset.univ \ es.toFinset, c e) := by
  apply le_trans _ (anchored_tensor_bound P src dst left right A C a b c root p0 i0
    g cover hA hrow hpoint)
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hx : x root p0 = i0
  · by_cases hq : q x
    · rw [if_pos ⟨hx, hq⟩, if_pos hx]
    · rw [if_neg (fun hh => hq hh.2), if_pos hx]
      exact mul_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  · rw [if_neg (fun hh => hx hh.1), if_neg hx]

end Tensors

end

end YM.Integration.AnchoredTensorContraction
