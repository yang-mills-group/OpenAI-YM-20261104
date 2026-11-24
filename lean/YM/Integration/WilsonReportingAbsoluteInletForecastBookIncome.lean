import YM.Integration.WilsonReportingAbsoluteInletForecastBookStep

/-! Turn the signed one-step error for the actual finite inverse series into
the full uniform close product on the funded physical regulator calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastBookIncome
open Filter Finset Real Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open FormalBulk08.Wine WilsonReportingAbsoluteInletNativeDates WilsonReportingAbsoluteInletNativeInvoice
open WilsonReportingAbsoluteInletForecastRate WilsonReportingAbsoluteInletForecastProduct
open WilsonReportingAbsoluteInletForecastReciprocal WilsonReportingAbsoluteInletForecastBooks
open WilsonReportingAbsoluteInletForecastBookStep
open scoped BigOperators Topology Classical
variable {G:Gauge}

private theorem logarithm {a b:ℝ}(ha:1/6 ≤ a)(hb:1/6 ≤ b):|log a-log b| ≤ 6*|a-b|:=by
  have up {x y:ℝ}(hx:1/6 ≤ x)(hy:1/6 ≤ y):log x-log y ≤ 6*|x-y|:=by
    have x0:0<x:=lt_of_lt_of_le (by norm_num) hx
    have y0:0<y:=lt_of_lt_of_le (by norm_num) hy
    calc
      log x-log y=log (x/y):=(log_div x0.ne' y0.ne').symm
      _ ≤ x/y-1:=log_le_sub_one_of_pos (div_pos x0 y0)
      _=(x-y)/y:=by field_simp
      _ ≤ |x-y|/y:=div_le_div_of_nonneg_right (le_abs_self _) y0.le
      _ ≤ 6*|x-y|:=(div_le_iff₀ y0).2 (by nlinarith only [mul_nonneg (abs_nonneg (x-y)) (sub_nonneg.mpr hy)])
  exact abs_le.mpr ⟨by have h:=up hb ha;rw [abs_sub_comm b a] at h;linarith only [h],up ha hb⟩

private theorem temperature (R:Run G)
    (hats:∀i,R.family.path.levels.clock.hatBeta (i+1) ≤ 2*R.family.path.levels.clock.hatBeta i)
    {j N per:ℕ}(jn:j<N):1/3 ≤ regulatorRun R.family N per (j+1)/regulatorRun R.family N per j:=by
  let A:=R.family.path.levels
  let a:=R.family.path.β N per j
  let b:=R.family.path.β N per (j+1)
  have ja:0<A.clock.hatBeta j:=zero_lt_one.trans (A.fits.delayed _)
  have jb:0<A.clock.hatBeta (j+1):=zero_lt_one.trans (A.fits.delayed _)
  have ma:=R.makes.wilson.represents N per j jn.le
  have mb:=R.makes.wilson.represents N per (j+1) jn
  have ap:0<a:=(half_pos ja).trans_le ma.band.1
  have bp:0<b:=(half_pos jb).trans_le mb.band.1
  have low:A.clock.hatBeta j/2 ≤ a:=ma.band.1
  have high:b ≤ 2*A.clock.hatBeta (j+1):=mb.band.2
  have move:A.clock.hatBeta (j+1) ≤ 2*A.clock.hatBeta j:=hats j
  have paid:b ≤ 9*a:=by linarith only [low,high,move,ap]
  change 1/3 ≤ (sqrt b)⁻¹/(sqrt a)⁻¹
  rw [div_inv_eq_mul,mul_comm,←div_eq_mul_inv]
  apply (le_div_iff₀ (sqrt_pos.2 bp)).2
  apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
  nlinarith only [Real.sq_sqrt ap.le,Real.sq_sqrt bp.le,paid]

theorem logged (R:Run G)(simple:G.Simple)(n:ℕ)(h:ℕ→ℕ→ℕ→ℝ)
    (hats:∀i,R.family.path.levels.clock.hatBeta (i+1) ≤ 2*R.family.path.levels.clock.hatBeta i)
    (receipt:Cash R n h):PositiveStep R n h:=by
  obtain ⟨C,d,C0,numbers⟩:=receipt
  let δ:ℝ:=(6*(1+C))⁻¹
  have dp:0<δ:=by dsimp [δ];positivity
  have decay:0 < -exponent n:=by unfold exponent;linarith only [Nat.cast_nonneg (α:=ℝ) n]
  have tiny:∀ᶠ j:ℕ in atTop,C*(lag R.family j)^d*(R.family.path.levels.clock.hatBeta j)^exponent n ≤ 1/6:=by
    filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually (spend d decay dp)] with j price
    let b:=R.family.path.levels.clock.hatBeta j
    have bp:0<b:=zero_lt_one.trans (R.family.path.levels.fits.delayed j)
    have up:(lag R.family j)^d ≤ δ*b^(-exponent n):=price
    have eq:b^(-exponent n)*b^exponent n=1:=by rw [←Real.rpow_add bp,neg_add_cancel,Real.rpow_zero]
    calc
      _ ≤ C*(δ*b^(-exponent n))*b^exponent n:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left up C0) (Real.rpow_nonneg bp.le _)
      _ = C*δ*(b^(-exponent n)*b^exponent n):=by ring
      _ = C*δ:=by rw [eq,mul_one]
      _ ≤ 1/6:=by dsimp [δ];rw [←div_eq_mul_inv,(div_le_iff₀ (by positivity))];linarith only [C0]
  obtain ⟨v,late⟩:=eventually_atTop.mp tiny
  refine ⟨6*C,d,by positivity,?_⟩
  filter_upwards [numbers,eventually_ge_atTop v] with k income vk N per j kj jn g
  have row:=income N per j kj jn
  have error:=row.trans (late j (vk.trans kj))
  have floor:1/3 ≤ g (j+1)/g j:=temperature R hats jn
  have paid:1/6 ≤ h N per j:=by linarith only [floor,(abs_le.mp error).2]
  refine ⟨lt_of_lt_of_le (by norm_num) paid,?_⟩
  calc
    _ ≤ 6*|g (j+1)/g j-h N per j|:=logarithm (by linarith only [floor]) paid
    _ ≤ 6*(C*(lag R.family j)^d*(R.family.path.levels.clock.hatBeta j)^exponent n):=
      mul_le_mul_of_nonneg_left row (by norm_num)
    _ = _:=by ring

theorem inverse (R:Run G)(simple:G.Simple)(p:ℕ)(D:ℕ→ℕ→ℕ→PowerSeries ℝ)
    (hats:∀i,R.family.path.levels.clock.hatBeta (i+1) ≤ 2*R.family.path.levels.clock.hatBeta i)
    (forward:Forward R (p+2) (fun N per j=>value (p+2) (bookU (D N per j)) (regulatorRun R.family N per j)))
    (cost:Cost R (p+2) D):
    InversePrice R p (fun N per j=>value (p+2) (bookH (D N per j)) (regulatorRun R.family N per j)):=
  positive R simple p _ (logged R simple _ _ hats (numerical R simple _ D forward cost))
end YM.Integration.WilsonReportingAbsoluteInletForecastBookIncome
