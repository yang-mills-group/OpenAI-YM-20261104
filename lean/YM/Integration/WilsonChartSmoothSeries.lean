/- The termwise derivative induction in derivatives uses the zero- and successor-order
curry maps, as in `iteratedFDeriv_tsum`.
Upstream source: Mathlib/Analysis/Calculus/SmoothSeries.lean
Authors: Sébastien Gouëzel. Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.ActualWilsonPacketGerms
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Summation of the original uniformly priced derivatives on an open
convex Wilson chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonChartSmoothSeries
open Set Function Filter AnalyticBridge.SectorAffine.Offset
open scoped BigOperators Classical Topology ContDiff

variable {E F : Type} {I : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : I → E → F} {n : ℕ} {c : I → ℝ} {U : Set E}
variable (hU : IsOpen U) (convex : Convex ℝ U)
  (rows : ∀ i x, x ∈ U → Through n (f i) x (c i)) (budget : Summable c)
local notation "total" => fun x => ∑' i, f i x
local notation "jet" => iteratedFDeriv ℝ

include hU convex rows budget in
theorem derivatives {j : ℕ} (hj : j ≤ n) (x : E) (hx : x ∈ U) :
    HasSum (fun i => jet j (f i) x) (jet j total x) := by
  induction j generalizing x with
  | zero =>
    have point (i : I) : ‖f i x‖ ≤ c i :=
      (norm_iteratedFDeriv_zero (𝕜:=ℝ)).symm.trans_le ((rows i x hx).pay 0 (Nat.zero_le _))
    have summed := (Summable.of_norm_bounded budget point).hasSum
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum summed
  | succ j ih =>
    let cols (i : I) := jet j (f i)
    let sum := fun x => ∑' i, cols i x
    have hd (i : I) (y : E) (hy : y ∈ U) :
        HasFDerivAt (cols i) (fderiv ℝ (cols i) y) y :=
      ((rows i y hy).smooth.differentiableAt_iteratedFDeriv
        (show (j : WithTop ℕ∞) < (n : WithTop ℕ∞) from Nat.cast_lt.mpr (by omega))).hasFDerivAt
    have bound (i : I) (y : E) (hy : y ∈ U) : ‖fderiv ℝ (cols i) y‖ ≤ c i := by
      have e := (rows i y hy).pay _ hj
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map] at e
      exact e
    have diff := hasFDerivAt_tsum_of_isPreconnected budget hU convex.isPreconnected hd bound hx
      (ih (by omega) x hx).summable hx
    have localEq : sum =ᶠ[𝓝 x] jet j total :=
      (show ∀ᶠ y in 𝓝 x, y∈U from hU.mem_nhds hx).mono fun y hy => (ih (by omega) y hy).tsum_eq
    have equal := (diff.congr_of_eventuallyEq localEq.symm).fderiv
    simp_rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [equal]
    exact (continuousMultilinearCurryLeftEquiv ..).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
      (Summable.of_norm_bounded budget (fun i => bound i x hx)).hasSum

include hU convex rows budget in
theorem summed (x : E) (hx : x ∈ U) : Through n total x (∑' i, c i) := by
  let field := total
  have eqn (j : ℕ) (hj : j ≤ n) (y : E) (hy : y ∈ U) : jet j field y = ∑' i, jet j (f i) y :=
    (derivatives hU convex rows budget hj y hy).tsum_eq.symm
  have smooth : ContDiffOn ℝ n field U := by
    refine (contDiffOn_iff_continuousOn_differentiableOn hU.uniqueDiffOn).mpr ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hj' : j ≤ n := by exact_mod_cast hj
      have uniforms := tendstoUniformlyOn_tsum budget (fun i y hy => (rows i y hy).pay j hj')
      have continuous : ContinuousOn (fun y => ∑' i, jet j (f i) y) U :=
        uniforms.continuousOn (Eventually.frequently (Eventually.of_forall fun S =>
          continuousOn_finsetSum S fun i _ y hy =>
            ((rows i y hy).smooth.continuousAt_iteratedFDeriv (by exact_mod_cast hj')).continuousWithinAt))
      exact (continuous.congr (fun y hy => eqn j hj' y hy)).congr (iteratedFDerivWithin_of_isOpen j hU)
    · apply DifferentiableOn.congr (f:=jet j field) _ (iteratedFDerivWithin_of_isOpen j hU)
      have hj' : j < n := by exact_mod_cast hj
      intro y hy
      let cols (i : I) := jet j (f i)
      have hd (i : I) (z : E) (hz : z ∈ U) :
          HasFDerivAt (cols i) (fderiv ℝ (cols i) z) z :=
        ((rows i z hz).smooth.differentiableAt_iteratedFDeriv
          (show (j : WithTop ℕ∞) < (n : WithTop ℕ∞) from Nat.cast_lt.mpr hj')).hasFDerivAt
      have bound (i : I) (z : E) (hz : z ∈ U) : ‖fderiv ℝ (cols i) z‖ ≤ c i := by
        have e := (rows i z hz).pay (j+1) hj'
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map] at e
        exact e
      have diff := hasFDerivAt_tsum_of_isPreconnected budget hU convex.isPreconnected hd bound hy
        (derivatives hU convex rows budget hj'.le y hy).summable hy
      exact (diff.congr_of_eventuallyEq ((show ∀ᶠ z in 𝓝 y, z∈U from hU.mem_nhds hy).mono fun z hz =>
        eqn j hj'.le z hz)).differentiableAt.differentiableWithinAt
  refine ⟨(smooth x hx).contDiffAt (hU.mem_nhds hx), fun j hj => ?_⟩
  rw [show jet j _ _ = _ from eqn j hj x hx]
  have norms := budget.of_nonneg_of_le (fun i => norm_nonneg (jet j (f i) x))
    (fun i => (rows i x hx).pay j hj)
  exact (norm_tsum_le_tsum_norm norms).trans (norms.tsum_le_tsum (fun i => (rows i x hx).pay j hj) budget)

end YM.Integration.WilsonChartSmoothSeries

