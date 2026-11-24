import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Operator estimates for an entire independent field tuple from finitely many
basis evaluations. Cancellation takes place before the norm of each output. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SignedTensor
open Filter Asymptotics
open scoped BigOperators Classical

variable {I K : Type*} [Fintype I] [Fintype K]
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [FiniteDimensional ℂ V] in
/-- Expand each independent slot in the same fixed physical input basis. -/
theorem expand (b : Module.Basis K ℂ V) (T : MultilinearMap ℂ (fun _ : I => V) W)
    (v : I → V) :
    T v = ∑ u : I → K, (∏ j, b.repr (v j) (u j)) • T (fun j => b (u j)) := by
  classical
  have hv : v = fun j => ∑ k : K, b.repr (v j) k • b k :=
    funext fun j => (b.sum_repr (v j)).symm
  conv_lhs => rw [hv, MultilinearMap.map_sum_finset]
  apply Finset.sum_congr (by ext; simp)
  intro u _
  exact MultilinearMap.map_smul_univ _ _ _

/-- A single physical-scale threshold covers every tuple, including inputs of
arbitrary norm. Its engineering amplitude is the product of the original
input norms. Each finite basis tuple may have a separate starting threshold. -/
theorem uniform_of_basis_littleO {A : Type*} {l : Filter A} (b : Module.Basis K ℂ V)
    (T : A → MultilinearMap ℂ (fun _ : I => V) W) (q : A → ℝ)
    (hb : ∀ u : I → K, (fun a => T a (fun j => b (u j))) =o[l] q)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in l, ∀ v : I → V, ‖T a v‖ ≤ ε * ‖q a‖ * ∏ j, ‖v j‖ := by
  classical
  let c (k : K) := LinearMap.toContinuousLinearMap (b.coord k)
  let cost (u : I → K) : ℝ := ∏ j, ‖c (u j)‖
  let total : ℝ := ∑ u : I → K, cost u
  have hc (u : I → K) : 0 ≤ cost u := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have ht : 0 ≤ total := Finset.sum_nonneg fun u _ => hc u
  let δ := ε / (total + 1)
  have hd : 0 < δ := div_pos hε (by linarith)
  have hpay : total * δ ≤ ε := by
    calc
      total * δ ≤ (total + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = ε := by dsimp [δ]; field_simp
  filter_upwards [eventually_all.mpr (fun u : I → K => (hb u).bound hd)] with a ha v
  rw [expand b (T a) v]
  refine (norm_sum_le _ _).trans ?_
  have hcoef (u : I → K) :
      ‖∏ j, b.repr (v j) (u j)‖ ≤ cost u * ∏ j, ‖v j‖ := by
    rw [norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun j _ => (c (u j)).le_opNorm (v j))
  calc
    _ ≤ ∑ u : I → K, (cost u * ∏ j, ‖v j‖) * (δ * ‖q a‖) := by
      apply Finset.sum_le_sum
      intro u _
      rw [norm_smul]
      exact mul_le_mul (hcoef u) (ha u) (norm_nonneg _) (by positivity)
    _ = (total * δ) * ‖q a‖ * ∏ j, ‖v j‖ := by
      dsimp [total]
      simp only [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpay (norm_nonneg _))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- The operator estimate is necessary and sufficient for separate little-o
estimates at the finitely many independently chosen basis inputs. -/
theorem uniform_iff_basis_littleO {A : Type*} {l : Filter A} (b : Module.Basis K ℂ V)
    (T : A → MultilinearMap ℂ (fun _ : I => V) W) (q : A → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∀ v : I → V,
      ‖T a v‖ ≤ ε * ‖q a‖ * ∏ j, ‖v j‖) ↔
    (∀ u : I → K, (fun a => T a (fun j => b (u j))) =o[l] q) := by
  constructor
  · intro h u
    apply IsLittleO.of_bound
    intro ε hε
    let size : ℝ := ∏ j, ‖b (u j)‖
    have hs : 0 ≤ size := Finset.prod_nonneg fun _ _ => norm_nonneg _
    let δ := ε / (size + 1)
    have hd : 0 < δ := div_pos hε (by linarith)
    have hpay : δ * size ≤ ε := by
      calc
        δ * size ≤ δ * (size + 1) := mul_le_mul_of_nonneg_left (by linarith) hd.le
        _ = ε := by dsimp [δ]; field_simp
    filter_upwards [h δ hd] with a ha
    exact (ha (fun j => b (u j))).trans (by
      change δ * ‖q a‖ * size ≤ ε * ‖q a‖
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right hpay (norm_nonneg _))
  · exact fun h _ hε => uniform_of_basis_littleO b T q h hε

open scoped Topology

/-- On the original inner extraction filter a signed estimate may hold on a
cofinal set. Small slack in the outer little-o bound gives the converse. -/
theorem littleO_iff_frequent_regulator {A B Y : Type*} [NormedAddCommGroup Y]
    {l : Filter A} {φ : Filter B} [NeBot φ] (z : A → B → Y) (y : A → Y)
    (q : A → ℝ) (hlim : ∀ᶠ a in l, Tendsto (z a) φ (𝓝 (y a)))
    (hpos : ∀ᶠ a in l, q a ≠ 0) :
    y =o[l] q ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∃ᶠ b in φ, ‖z a b‖ ≤ ε * ‖q a‖ := by
  constructor
  · intro h ε hε
    filter_upwards [h.bound (half_pos hε), hlim, hpos] with a ha hl hq
    have hlt : ‖y a‖ < ε * ‖q a‖ := ha.trans_lt
      (mul_lt_mul_of_pos_right (half_lt_self hε) (norm_pos_iff.mpr hq))
    exact ((hl.norm.eventually (gt_mem_nhds hlt)).mono (fun _ hx => hx.le)).frequently
  · intro h
    apply IsLittleO.of_bound
    intro ε hε
    filter_upwards [h ε hε, hlim] with a ha hl
    exact le_of_tendsto_of_frequently hl.norm ha

end YM.Integration.SignedTensor
