import YM.Integration.WilsonMacroscopicRichWatchLabels

/-! The cutoff effect of the fixed hearing on every bounded raw filed label is uniform in that label. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchBounded
open Set Filter Spec Wilson Next.UVStress WilsonMacroscopicRichWatchLabels
open WilsonMacroscopicRichWatchPlot WilsonMacroscopicRichFixedWatchSale
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

theorem measured (F:Final C f S){a h:ℕ}(W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ]S.Field h)
    (fits:∀z,D (fun i=>(W i).tester S h z)=z)
    (K ε:ℝ)(ep:0<ε):∀ᶠ w:ℕ×ℕ in f.fuse,∀z:C.label h,‖z‖≤K→
    ‖S.project h z-D (heard (calibrated S ∘ W) w (C.O w.1 w.2 z 0))‖≤ε:=by
  let basis:=Module.finBasis ℂ (C.label h)
  let P (w:ℕ×ℕ):=hearing W D w-S.project h
  let c (i:Fin (Module.finrank ℂ (C.label h))):=‖(basis.coord i).toContinuousLinearMap‖*|K|
  have zero (z:C.label h):Tendsto (fun w=>‖P w z‖) f.fuse (𝓝 0):=by
    have point:Tendsto (fun w=>hearing W D w z) f.fuse (𝓝 (S.project h z)):=by
      rw [←fits (S.project h z)]
      apply D.continuous.continuousAt.tendsto.comp
      apply tendsto_pi_nhds.mpr
      intro i
      change Tendsto (fun w:ℕ×ℕ=>row (calibrated S (W i)) h w z) f.fuse (𝓝 ((W i).tester S h (S.project h z)))
      simpa only [invariant] using limits F (calibrated S (W i)) h z
    simpa only [P,LinearMap.sub_apply,sub_self,norm_zero] using (point.sub_const (S.project h z)).norm
  have charge:Tendsto (fun w=>∑i,c i*‖P w (basis i)‖) f.fuse (𝓝 0):=by
    simpa only [mul_zero,Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _=>(zero (basis i)).const_mul (c i))
  filter_upwards [charge.eventually (ge_mem_nhds ep)] with w small z bound
  have coord (i:Fin (Module.finrank ℂ (C.label h))):‖basis.repr z i‖≤c i:=
    ((basis.coord i).toContinuousLinearMap.le_opNorm z).trans (mul_le_mul_of_nonneg_left
      (bound.trans (le_abs_self K)) (ContinuousLinearMap.opNorm_nonneg _))
  rw [←performed W D w z,norm_sub_rev]
  change ‖P w z‖≤ε
  calc
    ‖P w z‖=‖∑i,basis.repr z i • P w (basis i)‖:=by
      conv_lhs=>rw [←basis.sum_repr z]
      simp only [map_sum,map_smul]
    _ ≤ ∑i,‖basis.repr z i • P w (basis i)‖:=norm_sum_le _ _
    _ ≤ ∑i,c i*‖P w (basis i)‖:=Finset.sum_le_sum fun i _=>by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (coord i) (norm_nonneg _)
    _ ≤ ε:=small

end YM.Integration.WilsonMacroscopicRichWatchBounded
