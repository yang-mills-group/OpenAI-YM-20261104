import YM.Integration.WilsonReportingAbsoluteInletForecastProduct

/-! Use a separately priced finite kinetic action at the physical running
coupling. The reciprocal is a numerical forecast of the inverse clock.
All actual period and cutoff temperatures remain in the estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastReciprocal
open Filter Finset Real Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReportingAbsoluteInletNativeDates WilsonReportingAbsoluteInletNativeInvoice
open WilsonReportingAbsoluteInletForecastRate WilsonReportingAbsoluteInletForecastProduct
open scoped Classical Topology BigOperators
variable {G:Gauge}

def Forward (R:Run G) (p:ℕ) (a:ℕ→ℕ→ℕ→ℝ) : Prop :=
  ∀ᶠ k:ℕ in atTop,∀N per j,k≤j→j<N→
    let g:=fun t=>regulatorRun R.family N per t
    |g j/g (j+1)-a N per j|≤(R.family.path.levels.clock.hatBeta j)^exponent p

private theorem logarithm {a b:ℝ}(ha:1/4≤a)(hb:1/4≤b):|log a-log b|≤4*|a-b|:=by
  have up {x y:ℝ}(hx:1/4≤x)(hy:1/4≤y):log x-log y≤4*|x-y|:=by
    have x0:0<x:=lt_of_lt_of_le (by norm_num) hx
    have y0:0<y:=lt_of_lt_of_le (by norm_num) hy
    calc
      log x-log y=log (x/y):=(log_div x0.ne' y0.ne').symm
      _≤x/y-1:=log_le_sub_one_of_pos (div_pos x0 y0)
      _=(x-y)/y:=by field_simp
      _≤|x-y|/y:=div_le_div_of_nonneg_right (le_abs_self _) y0.le
      _≤4*|x-y|:=(div_le_iff₀ y0).2 (by nlinarith only [mul_nonneg (abs_nonneg (x-y)) (sub_nonneg.mpr hy)])
  exact abs_le.mpr ⟨by have h:=up hb ha;rw [abs_sub_comm b a] at h;linarith only [h],up ha hb⟩

private theorem lower (R:Run G)(simple:G.Simple){j N per:ℕ}(jn:j<N):
    1/2≤regulatorRun R.family N per j/regulatorRun R.family N per (j+1):=by
  let A:=R.family.path.levels
  let a:=R.family.path.β N per j
  let b:=R.family.path.β N per (j+1)
  have ha:0<A.clock.hatBeta j:=zero_lt_one.trans (A.fits.delayed j)
  have hb:0<A.clock.hatBeta (j+1):=zero_lt_one.trans (A.fits.delayed _)
  have bd:A.clock.hatBeta j≤A.clock.hatBeta (j+1):=(Real.log_le_log_iff ha hb).1
    (logarithm_monotone A simple j.le_succ)
  have ma:=R.makes.wilson.represents N per j jn.le
  have mb:=R.makes.wilson.represents N per (j+1) jn
  have ap:0<a:=(half_pos ha).trans_le ma.band.1
  have bp:0<b:=(half_pos hb).trans_le mb.band.1
  have lo:A.clock.hatBeta (j+1)/2≤b:=mb.band.1
  have hi:a≤2*A.clock.hatBeta j:=ma.band.2
  have scale:a≤4*b:=by linarith only [lo,hi,bd]
  change 1/2≤(sqrt a)⁻¹/(sqrt b)⁻¹
  rw [div_inv_eq_mul,mul_comm,←div_eq_mul_inv]
  apply (le_div_iff₀ (sqrt_pos.2 ap)).2
  apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
  nlinarith only [Real.sq_sqrt ap.le,Real.sq_sqrt bp.le,scale]

theorem inverse (R:Run G) (simple:G.Simple) (p:ℕ) (a:ℕ→ℕ→ℕ→ℝ)
    (income:Forward R (p+2) a):InversePrice R p (fun N per j=>(a N per j)⁻¹):=by
  apply positive R simple p
  refine ⟨4,0,by norm_num,?_⟩
  have down:0 < -exponent (p+2):=by unfold exponent;linarith only [Nat.cast_nonneg (α:=ℝ) (p+2)]
  have limit:= (tendsto_rpow_neg_atTop down).comp (Next.Rank.Station.hat_rate R.family.path.levels simple)
  have paid:∀ᶠ j:ℕ in atTop,(R.family.path.levels.clock.hatBeta j)^exponent (p+2)≤1/4:=by
    have bound:=limit.eventually (gt_mem_nhds (by norm_num:0<(1:ℝ)/4))
    exact bound.mono (fun j z=>by simpa only [Function.comp_apply,neg_neg] using z.le)
  obtain ⟨i,late⟩:=eventually_atTop.mp paid
  filter_upwards [eventually_ge_atTop i,income] with k low cost N per j kj jn
  let g:=fun t=>regulatorRun R.family N per t
  let t:=g j/g (j+1)
  have first:1/2≤t:=lower R simple jn
  have entry:|t-a N per j|≤(R.family.path.levels.clock.hatBeta j)^exponent (p+2):=cost N per j kj jn
  have gap:=entry.trans (late j (low.trans kj))
  have second:(1:ℝ)/4≤a N per j:=by linarith only [(abs_le.mp gap).2,first]
  refine ⟨inv_pos.2 (lt_of_lt_of_le (by norm_num) second),?_⟩
  change |log (g (j+1)/g j)-log (a N per j)⁻¹|≤4*(lag R.family j)^0*_
  rw [←inv_div (g j) (g (j+1)),log_inv,log_inv,neg_sub_neg,abs_sub_comm,pow_zero,mul_one]
  exact (logarithm (by linarith only [first]:1/4≤t) second).trans (mul_le_mul_of_nonneg_left entry (by norm_num))

end YM.Integration.WilsonReportingAbsoluteInletForecastReciprocal
