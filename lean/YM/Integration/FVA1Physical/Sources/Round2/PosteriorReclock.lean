import YM.Integration.FVA1Physical.Wilson.MeasuredFieldReset
import YM.Integration.FVA1Physical.Sources.Round2.TwoPhysicalFields

/-! Insert the independently emitted input at the measured *next* clock in a
true outer posterior. The certified scalar reset error is transported off the
origin on the selected halo; its price involves no outside sites. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Set Filter Finset MeasureTheory Metric Push.Uniform Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Bakery MSbar.Bakery.Portal MSbar.Cacao MSbar.Whisk MSbar.Bout MSbar.Bulk MSbar.Midpoint
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f:Side}

def clockReading {ι:Type} (p:ℕ) (g:ℝ) (T:PowerSeries (Pot ι)) (z:View ι):ℝ :=
  taste p (picture z T) g

theorem clockReading_continuous {ι:Type} (p:ℕ) (g:ℝ) (T:PowerSeries (Pot ι)) :
    Continuous (clockReading p g T) := by
  unfold clockReading taste picture
  simp only [PowerSeries.coeff_map]
  exact continuous_finsetSum _ fun i _=>continuous_const.mul (MvPolynomial.continuous_eval _)

theorem reset_degree {ι:Type} [Fintype ι] [DecidableEq ι] (m p:ℕ) (b:PowerSeries ℝ) (g u:ℝ)
    (T:PowerSeries (Pot ι)) : (scalarResetRow m p b g u T).totalDegree ≤ m := by
  unfold scalarResetRow
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  exact (MvPolynomial.totalDegree_smul_le ..).trans ((MvPolynomial.homogeneousComponent_isHomogeneous ..).totalDegree_le.trans
    (Nat.lt_succ_iff.mp (mem_range.mp hk)))

theorem posterior_reclock (S:StepData c f) (R:Rep G f) (O:Config G c) {σ C δ Λ w:ℝ}
    (law:Admitted O R S σ C δ Λ w) (H:Set (Config G f)) (me:MeasurableSet H)
    (copy:Config G f → Config G f) (mc:Measurable copy) (h g:ℝ) (hp:0 < h) (gp:0 < g)
    (series:PowerSeries ℝ) (T:PowerSeries (Pot (Primary f G))) (p m s:ℕ)
    (degree:∀ i ≤ p, (PowerSeries.coeff i T).totalDegree ≤ m)
    (b:Site f) {α M D:ℝ} (ha:0 ≤ α)
    (bank:Vault (MSbar.Measuring.chart f G) {b} α s m 0 (scalarResetRow m p series h (h/g) T) M)
    (live:∀ U∈H,‖chartLog h (copy U)‖ ≤ D) :
    let E:=expect S R O
    let fresh:=fun U=>clockReading p g T (chartLog g (copy U))
    let inherited:=fun U=>clockReading p h (sourceClock m series T) (chartLog h (copy U))
    |E (H.indicator fresh)-E (H.indicator inherited)| ≤ M*(1+max 0 D)^(m+1) := by
  intro E fresh inherited
  let old:=sourceClock m series T
  let t:=max 0 D
  have t0:0 ≤ t:=le_max_left ..
  let actual:=clockReading p h old
  have ct:Continuous actual:=clockReading_continuous ..
  obtain ⟨B,cap⟩:=(isCompact_closedBall (0:View (Primary f G)) t).exists_bound_of_continuousOn ct.continuousOn
  have inside:Measurable inherited:=ct.measurable.comp ((chartLog_meas h).comp mc)
  have test:Envelope (H.indicator inherited):=by
    refine ⟨inside.indicator me,max 0 B,?_⟩
    intro U
    by_cases hit:U∈H
    · rw [Set.indicator_of_mem hit]
      exact (cap _ (mem_closedBall_zero_iff.mpr ((live U hit).trans (le_max_right ..)))).trans (le_max_right ..)
    rw [Set.indicator_of_notMem hit,norm_zero]
    exact le_max_left ..
  have price0:0 ≤ M*(1+t)^(m+1):=mul_nonneg bank.1 (pow_nonneg (by linarith only [t0]) _)
  apply expect_difference law (((clockReading_continuous p g T).measurable.comp ((chartLog_meas g).comp mc)).indicator me) test
  intro U
  by_cases hit:U∈H
  swap
  · simpa only [Set.indicator_of_notMem hit,sub_self,abs_zero] using price0
  rw [Set.indicator_of_mem hit,Set.indicator_of_mem hit]
  let X:=chartLog h (copy U)
  have rescale:chartLog g (copy U)=(h/g) • X:=by
    dsimp only [X,chartLog]
    rw [smul_smul];congr 1;field_simp
  have hr:h/(h/g)=g:=by field_simp
  have eqn:=scalar_reset_identity m p series h (h/g) T degree X
  rw [hr,←rescale] at eqn
  change |clockReading p g T (chartLog g (copy U))-clockReading p h old X| ≤ _
  rw [show clockReading p g T (chartLog g (copy U))-clockReading p h old X=_ from eqn]
  exact Bout.looks ha (Bout.across X bank ha (by simpa only [sub_zero] using (live U hit).trans (le_max_right (0:ℝ) D))
    (reset_degree ..) 0)

end YM.Integration.FVA1Physical.Round2.Curvature
