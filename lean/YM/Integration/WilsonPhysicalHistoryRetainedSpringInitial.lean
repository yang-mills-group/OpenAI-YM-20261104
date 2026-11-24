import YM.Integration.WilsonPhysicalHistoryRetainedSpringJet

/-! Below the number of genuine curvature factors, every angular coefficient
of the prescribed finite polynomial is zero at the flat held field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Wilson Finset Precision Exterior Work.F03 Bid
open FundedCurvatureRayTaylor WilsonMeasuredPathTaylor
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ}

theorem flat_atom_polynomial (a : Atom G k) (x : Site n) (z : Dir G n) {q : ℕ} (low : q<k) (t : ℝ) :
    polynomial a x (collect G z) q t=0 := by
  have chart (u : ℝ) : field (collect G z) u=represent (u • z) := by
    funext e
    rw [represent_link]
    rfl
  have smooth : ContDiffAt ℝ ω (fun u : ℝ=>a.unmasked (represent (u • z)) x) 0 := by
    change ContDiffAt ℝ ω (fun u : ℝ=>∑ b,a.coeff b*∏ e,
      (a.leg e).atSite (represent (u • z)) x (b e)) 0
    apply ContDiffAt.sum
    intro b _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro e _
    exact (ContinuousLinearMap.contDiff (PiLp.proj (𝕜:=ℝ) 2 (fun _=>ℝ) (b e))).contDiffAt.comp _
      (CubicMatch.slot_smooth (U:=fun u : ℝ=>represent (u • z)) (CubicMatch.test_ray z) (a.leg e) x)
  rw [atom_ray_polynomial]
  apply Finset.sum_eq_zero
  intro r hr
  have below:= (CubicMatch.slot_first a x z).2 r (lt_of_le_of_lt (Nat.le_of_lt_succ (mem_range.mp hr)) low)
  have cast : CubicMatch.term r (fun u : ℝ=>(a.unmasked (represent (u • z)) x : ℂ)) =
      ((CubicMatch.term r (fun u : ℝ=>a.unmasked (represent (u • z)) x) : ℝ) : ℂ) :=
    CubicMatch.term_linear (k:=r) Complex.ofRealCLM (smooth.of_le le_top)
  simp only [chart,cast,below,Complex.ofReal_zero,smul_zero]

theorem flat_site_polynomial (A : ℕ→Atom G k) (x : Site n) (z : Dir G n) {q : ℕ} (low : q<k) (t : ℝ) :
    siteTaylor A x z q t=0 := by
  simp only [siteTaylor,flat_atom_polynomial _ _ _ low,tsum_zero,Finset.sum_const_zero,mul_zero]

end YM.Integration.OriginalMarkedRunAction
