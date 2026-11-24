import YM.Integration.AnchoredTensorContractionBound

/-!
# Anchored contraction through vertex observations

Vertex states may have unrelated finite coordinate types. Each edge observes
only an internal value at each endpoint. The root event is priced explicitly;
only selected edges need incoming-fiber and row bounds. Every other original
edge retains its pointwise cost. A baseline is an explicit inhabitance witness.
-/

set_option autoImplicit false

open scoped BigOperators
open YM.Integration.AnchoredTensorContraction

namespace YM.Integration.AnchoredTensorObservation

noncomputable section

/-- An arbitrary finite observation fiber can be contracted against one row. -/
theorem one_fiber_edge_le {X I : Type*} [Fintype X]
    [Fintype I] [DecidableEq I]
    (A : X → ℂ) (C : I → I → ℂ) (observe : X → I) (i : I) (a b : ℝ)
    (hA : ∀ j, (∑ z : X, if observe z = j then ‖A z‖ else 0) ≤ a)
    (hC : (∑ j, ‖C i j‖) ≤ b) :
    (∑ z : X, ‖A z‖ * ‖C i (observe z)‖) ≤ a * b := by
  have ha : 0 ≤ a :=
    (Finset.sum_nonneg
      (f := fun z : X => if observe z = i then ‖A z‖ else 0) (fun z _ => by
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl)).trans (hA i)
  calc
    (∑ z : X, ‖A z‖ * ‖C i (observe z)‖) =
        ∑ z : X, ∑ j : I,
          (if observe z = j then ‖A z‖ else 0) * ‖C i j‖ := by
      apply Finset.sum_congr rfl
      intro z _hz
      simp [ite_mul]
    _ = ∑ j : I, ∑ z : X,
        (if observe z = j then ‖A z‖ else 0) * ‖C i j‖ := Finset.sum_comm
    _ = ∑ j : I, (∑ z : X, if observe z = j then ‖A z‖ else 0) * ‖C i j‖ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul]
    _ ≤ ∑ j : I, a * ‖C i j‖ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hA j) (norm_nonneg _))
    _ = a * ∑ j : I, ‖C i j‖ := by rw [Finset.mul_sum]
    _ ≤ a * b := mul_le_mul_of_nonneg_left hC ha

private theorem vertex_product {V E : Type*} [Fintype V] [DecidableEq V]
    {src dst : E → V} {root : V} {es : List E}
    (g : Growth src dst root es) (cover : ∀ v, v ∈ root :: es.map dst) (f : V → ℝ) :
    f root * (es.map (fun e => f (dst e))).prod = ∏ v, f v := by
  have hv : (root :: es.map dst).toFinset = Finset.univ := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact cover v
  have hp := List.prod_toFinset f g.vertices_nodup
  rw [hv] at hp
  simpa only [List.map_cons, List.map_map, List.prod_cons, Function.comp_def] using hp.symm

private theorem product_split {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (f : E → ℝ) :
    (∏ e, f e) = (∏ e ∈ S, f e) * (∏ e ∈ Finset.univ \ S, f e) :=
  (Finset.prod_sdiff (f := f) S.subset_univ).symm.trans (mul_comm _ _)

section Observations

variable {V E I : Type*}
variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable [Fintype I] [DecidableEq I]
variable (X : V → Type*) [∀ v, Fintype (X v)]
variable (src dst : E → V)
variable (left : ∀ e, X (src e) → I) (right : ∀ e, X (dst e) → I)
variable (A : ∀ v, X v → ℂ) (C : E → I → I → ℂ)
variable (a : V → ℝ) (b c : E → ℝ)
variable (root : V) (q : X root → Prop) [DecidablePred q]
variable (base : ∀ v, X v)
variable {es : List E} (g : Growth src dst root es)
variable (cover : ∀ v, v ∈ root :: es.map dst)
variable (hroot : (∑ z : X root, if q z then ‖A root z‖ else 0) ≤ a root)
variable (hA : ∀ e, e ∈ es → ∀ i,
  (∑ z : X (dst e), if right e z = i then ‖A (dst e) z‖ else 0) ≤ a (dst e))
variable (hrow : ∀ e, e ∈ es → ∀ i, (∑ j : I, ‖C e i j‖) ≤ b e)

include base g cover hroot hA hrow

/-- Heterogeneous vertex states contract through their edge observations.
No identification of internal and exterior alphabets is required. -/
theorem anchored_observation_bound
    (hpoint : ∀ e, e ∉ es → ∀ i j, ‖C e i j‖ ≤ c e) :
    (∑ x : (∀ v, X v), if q (x root) then
      (∏ v, ‖A v (x v)‖) *
        (∏ e, ‖C e (left e (x (src e))) (right e (x (dst e)))‖) else 0) ≤
      (∏ v, a v) * (∏ e ∈ es.toFinset, b e) *
        (∏ e ∈ Finset.univ \ es.toFinset, c e) := by
  let R0 : X root → ℝ := fun z => if q z then ‖A root z‖ else 0
  let K0 : ∀ e, X (src e) → X (dst e) → ℝ :=
    fun e u v => if e ∈ es then
      ‖A (dst e) v‖ * ‖C e (left e u) (right e v)‖ else 0
  let B0 : E → ℝ := fun e => if e ∈ es then a (dst e) * b e else 0
  let W : (∀ v, X v) → ℝ := fun x =>
    R0 (x root) * (es.map (fun e => K0 e (x (src e)) (x (dst e)))).prod
  have hR0 : ∀ z, 0 ≤ R0 z := by
    intro z
    dsimp only [R0]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hK0 : ∀ e u v, 0 ≤ K0 e u v := by
    intro e u v
    dsimp only [K0]
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact le_rfl
  have hK : ∀ e u, (∑ v, K0 e u v) ≤ B0 e := by
    intro e u
    by_cases he : e ∈ es
    · simpa only [K0, B0, if_pos he] using
        one_fiber_edge_le (A (dst e)) (C e) (right e) (left e u)
          (a (dst e)) (b e) (hA e he) (hrow e he (left e u))
    · simp only [K0, B0, if_neg he, Finset.sum_const_zero, le_refl]
  have htree := kernel_growth_bound (X := X)
    (src := src) (dst := dst) (root := root) R0 K0 (a root) B0
    hR0 hroot hK0 hK base g cover
  have hbmap : es.map B0 = es.map (fun e => a (dst e) * b e) := by
    apply List.map_congr_left
    intro e he
    exact if_pos he
  have hcost : a root * (es.map B0).prod =
      (∏ v, a v) * (∏ e ∈ es.toFinset, b e) := by
    rw [hbmap, List.prod_map_mul, ← mul_assoc, vertex_product g cover a,
      ← List.prod_toFinset b g.edges_nodup]
  change (∑ x : (∀ v, X v), W x) ≤ a root * (es.map B0).prod at htree
  rw [hcost] at htree
  have hweight (x : ∀ v, X v) :
      W x = if q (x root) then
        (∏ v, ‖A v (x v)‖) *
          (∏ e ∈ es.toFinset, ‖C e (left e (x (src e))) (right e (x (dst e)))‖)
      else 0 := by
    have hkmap :
        es.map (fun e => K0 e (x (src e)) (x (dst e))) =
          es.map (fun e => ‖A (dst e) (x (dst e))‖ *
            ‖C e (left e (x (src e))) (right e (x (dst e)))‖) := by
      apply List.map_congr_left
      intro e he
      exact if_pos he
    by_cases hx : q (x root)
    · dsimp only [W]
      rw [hkmap]
      simp only [R0, if_pos hx, List.prod_map_mul]
      rw [← mul_assoc, vertex_product g cover (fun v => ‖A v (x v)‖),
        ← List.prod_toFinset
          (fun e => ‖C e (left e (x (src e))) (right e (x (dst e)))‖) g.edges_nodup]
    · simp only [W, R0, if_neg hx, zero_mul]
  have hc : ∀ e ∈ Finset.univ \ es.toFinset, 0 ≤ c e := by
    intro e he
    have hne : e ∉ es :=
      fun hm => (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr hm)
    exact (norm_nonneg
      (C e (left e (base (src e))) (right e (base (dst e))))).trans
      (hpoint e hne _ _)
  have hrest : 0 ≤ ∏ e ∈ Finset.univ \ es.toFinset, c e := Finset.prod_nonneg hc
  calc
    (∑ x : (∀ v, X v), if q (x root) then
        (∏ v, ‖A v (x v)‖) *
          (∏ e, ‖C e (left e (x (src e))) (right e (x (dst e)))‖) else 0) ≤
        ∑ x : (∀ v, X v), W x * (∏ e ∈ Finset.univ \ es.toFinset, c e) := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [hweight]
      by_cases hx : q (x root)
      · simp only [if_pos hx]
        have hprod :
            (∏ e ∈ Finset.univ \ es.toFinset,
              ‖C e (left e (x (src e))) (right e (x (dst e)))‖) ≤
            ∏ e ∈ Finset.univ \ es.toFinset, c e := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro e he
          have hne : e ∉ es :=
            fun hm => (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr hm)
          exact hpoint e hne _ _
        rw [product_split es.toFinset
          (fun e => ‖C e (left e (x (src e))) (right e (x (dst e)))‖), ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hprod
          (mul_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
            (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
      · simp only [if_neg hx, zero_mul, le_refl]
    _ = (∑ x : (∀ v, X v), W x) * (∏ e ∈ Finset.univ \ es.toFinset, c e) := by
      rw [Finset.sum_mul]
    _ ≤ ((∏ v, a v) * (∏ e ∈ es.toFinset, b e)) *
        (∏ e ∈ Finset.univ \ es.toFinset, c e) :=
      mul_le_mul_of_nonneg_right htree hrest

/-- Additional consistency conditions only decrease the nonnegative sum. -/
theorem anchored_observation_restricted_bound
    (hpoint : ∀ e, e ∉ es → ∀ i j, ‖C e i j‖ ≤ c e)
    (r : (∀ v, X v) → Prop) [DecidablePred r] :
    (∑ x : (∀ v, X v), if q (x root) ∧ r x then
      (∏ v, ‖A v (x v)‖) *
        (∏ e, ‖C e (left e (x (src e))) (right e (x (dst e)))‖) else 0) ≤
      (∏ v, a v) * (∏ e ∈ es.toFinset, b e) *
        (∏ e ∈ Finset.univ \ es.toFinset, c e) := by
  apply le_trans _ (anchored_observation_bound X src dst left right A C a b c root q
    base g cover hroot hA hrow hpoint)
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hx : q (x root)
  · by_cases hr : r x
    · rw [if_pos ⟨hx, hr⟩, if_pos hx]
    · rw [if_neg (fun hh => hr hh.2), if_pos hx]
      exact mul_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  · rw [if_neg (fun hh => hx hh.1), if_neg hx]

end Observations

end

end YM.Integration.AnchoredTensorObservation
