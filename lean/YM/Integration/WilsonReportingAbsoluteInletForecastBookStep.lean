import YM.Integration.WilsonReportingAbsoluteInletForecastReciprocal
import YM.Integration.WilsonReportingAbsoluteInletForecastBooks

/-! Numerical error in the literal finite inverse kinetic polynomial on each
physical reporting date, from the forward price on that same original book. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastBookStep
open Filter Finset Real Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open FormalBulk08.Wine WilsonReportingAbsoluteInletNativeDates WilsonReportingAbsoluteInletForecastRate
open WilsonReportingAbsoluteInletForecastReciprocal WilsonReportingAbsoluteInletForecastBooks
open scoped BigOperators Topology Classical
variable {G:Gauge}

def Cost (R:Run G)(n:ℕ)(D:ℕ→ℕ→ℕ→PowerSeries ℝ):Prop:=
  ∃B:ℝ,∃d:ℕ,0 ≤ B ∧ ∀ᶠ k:ℕ in atTop,∀N per j,k ≤ j→j<N→
    mass n (bookU (D N per j))+mass n (bookH (D N per j)) ≤ B*(lag R.family j)^d

def Cash (R:Run G)(n:ℕ)(h:ℕ→ℕ→ℕ→ℝ):Prop:=
  ∃C:ℝ,∃d:ℕ,0 ≤ C ∧ ∀ᶠ k:ℕ in atTop,∀N per j,k ≤ j→j<N→
    let g:=fun i=>regulatorRun R.family N per i
    |g (j+1)/g j-h N per j| ≤ C*(lag R.family j)^d*(R.family.path.levels.clock.hatBeta j)^exponent n

private theorem mass_nonneg (n:ℕ)(T:PowerSeries ℝ):0 ≤ mass n T:=
  Finset.sum_nonneg (fun _ _=>abs_nonneg _)
private theorem value_le {g:ℝ}(g0:0 ≤ g)(g1:g ≤ 1)(n:ℕ)(T:PowerSeries ℝ):
    |value n T g| ≤ mass n T:=by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul,abs_of_nonneg (pow_nonneg g0 i)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ g0 g1)
private theorem heat {b q:ℝ}(hb:1 < b)(band:b/2 ≤ q)(p:ℕ):
    ((sqrt q)⁻¹)^(p+1) ≤ (2:ℝ)^(p+1)*b^exponent p:=by
  have b1:1 < b:=hb
  have b0:0 < b:=zero_lt_one.trans b1
  have q0:0 < q:=(half_pos b0).trans_le band
  have sq:sqrt b ≤ 2*sqrt (q):=calc
    _ ≤ sqrt (4*q):=sqrt_le_sqrt (by linarith)
    _ = _:=by rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  have heat:(sqrt q)⁻¹ ≤ 2*(sqrt b)⁻¹:=by
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (sqrt_pos.2 q0) (sqrt_pos.2 b0),one_mul]
    exact sq
  have shape:(sqrt b)⁻¹=b^(-(1:ℝ)/2):=by rw [sqrt_eq_rpow,neg_div,Real.rpow_neg b0.le]
  rw [shape] at heat
  have raise:=pow_le_pow_left₀ (inv_nonneg.mpr (sqrt_nonneg q)) heat (p+1)
  rw [mul_pow,←rpow_mul_natCast b0.le] at raise
  refine raise.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le b1.le ?_) (by positivity))
  unfold exponent
  push_cast
  linarith


private theorem reciprocal (D:PowerSeries ℝ)(p:ℕ) {g r z a x:ℝ} (g0:0 ≤ g)(g1:g ≤ 1)
    (r0:1/2 ≤ r) (z0:0 ≤ z)(a0:0 ≤ a)(x0:0 ≤ x)
    (power:g^(p+1) ≤ a*z)(paid:mass p (bookU D)+mass p (bookH D) ≤ x)
    (row:|r-value p (bookU D) g| ≤ z):
    |r⁻¹-value p (bookH D) g| ≤ 2*(a*x^2+x)*z:=by
  let h:=value p (bookH D) g; let t:=value p (bookU D) g
  have hb:=mass_nonneg p (bookH D);have tb:=mass_nonneg p (bookU D)
  have hcost:mass p (bookH D) ≤ x:=by linarith only [paid,tb]
  have tcost:mass p (bookU D) ≤ x:=by linarith only [paid,hb]
  have hv:|h| ≤ x:=(value_le g0 g1 _ _).trans hcost
  have ht:mass p (bookH D)*mass p (bookU D) ≤ x*x:=mul_le_mul hcost tcost tb x0
  have cap:|1-h*t| ≤ (a*x^2)*z:=by
    apply (truncation p D g0 g1).trans
    calc _ ≤ (a*z)*(x*x):=mul_le_mul power ht (mul_nonneg hb tb) (mul_nonneg a0 z0)
         _ = (a*x^2)*z:=by ring
  have dev:|h*(t-r)| ≤ x*z:=by
    rw [abs_mul,abs_sub_comm t r];exact mul_le_mul hv row (abs_nonneg _) x0
  have positiveR:0 < r:=by linarith only [r0]
  have equal:(r⁻¹-h)*r=(1-h*t)+h*(t-r):=by rw [sub_mul,inv_mul_cancel₀ positiveR.ne'];ring
  have total:|r⁻¹-h| *r ≤ (a*x^2)*z+x*z:=by
    have bought: |(r⁻¹-h)*r| ≤ (a*x^2)*z+x*z:=by
      rw [equal];exact (abs_add_le _ _).trans (add_le_add cap dev)
    simpa only [abs_mul,abs_of_pos positiveR] using bought
  have low:=mul_le_mul_of_nonneg_left r0 (abs_nonneg (r⁻¹-h))
  change |r⁻¹-h| ≤ _
  linarith only [total,low]

private theorem lower (R:Run G)(simple:G.Simple){j N per:ℕ}(jn:j<N):
    1/2 ≤ regulatorRun R.family N per j/regulatorRun R.family N per (j+1):=by
  let A:=R.family.path.levels
  let a:=R.family.path.β N per j
  let b:=R.family.path.β N per (j+1)
  have ha:0<A.clock.hatBeta j:=zero_lt_one.trans (A.fits.delayed j)
  have hb:0<A.clock.hatBeta (j+1):=zero_lt_one.trans (A.fits.delayed _)
  have bd:A.clock.hatBeta j ≤ A.clock.hatBeta (j+1):=(Real.log_le_log_iff ha hb).1
    (logarithm_monotone A simple j.le_succ)
  have ma:=R.makes.wilson.represents N per j jn.le
  have mb:=R.makes.wilson.represents N per (j+1) jn
  have ap:0<a:=(half_pos ha).trans_le ma.band.1
  have bp:0<b:=(half_pos hb).trans_le mb.band.1
  have lo:A.clock.hatBeta (j+1)/2 ≤ b:=mb.band.1
  have hi:a ≤ 2*A.clock.hatBeta j:=ma.band.2
  have scale:a ≤ 4*b:=by linarith only [lo,hi,bd]
  change 1/2 ≤ (sqrt a)⁻¹/(sqrt b)⁻¹
  rw [div_inv_eq_mul,mul_comm,←div_eq_mul_inv]
  apply (le_div_iff₀ (sqrt_pos.2 ap)).2
  apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
  nlinarith only [Real.sq_sqrt ap.le,Real.sq_sqrt bp.le,scale]


theorem numerical (R:Run G)(simple:G.Simple)(n:ℕ)(D:ℕ→ℕ→ℕ→PowerSeries ℝ)
    (forward:Forward R n (fun N per j=>value n (bookU (D N per j)) (regulatorRun R.family N per j)))
    (cost:Cost R n D):
    Cash R n (fun N per j=>value n (bookH (D N per j)) (regulatorRun R.family N per j)):=by
  obtain ⟨B,d,B0,rows⟩:=cost
  let a:ℝ:=2^(n+1)
  let C:=2*(a*B^2+B)
  have a0:0 ≤ a:=by dsimp [a]; positivity
  refine ⟨C,2*d,by dsimp [C];positivity,?_⟩
  obtain ⟨i,late⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 2)
  filter_upwards [rows,forward,eventually_ge_atTop i] with k paid income ik N per j kj jn g
  let b:=R.family.path.levels.clock.hatBeta j
  let L:=lag R.family j
  have b1:1<b:=R.family.path.levels.fits.delayed j
  have b2:2 ≤ b:=late j (ik.trans kj)
  have l1:1 ≤ L:=by change 1 ≤ 2+log b;linarith only [log_nonneg b1.le]
  have band:b/2 ≤ R.family.path.β N per j:= (R.makes.wilson.represents N per j jn.le).band.1
  have sq1:1 ≤ sqrt (R.family.path.β N per j):=Real.one_le_sqrt.mpr (by linarith only [band,b2])
  have g0:0 ≤ g j:=inv_nonneg.mpr (sqrt_nonneg _)
  have g1:g j ≤ 1:=(inv_le_one₀ (zero_lt_one.trans_le sq1)).2 sq1
  have z0:0 ≤ b^exponent n:=Real.rpow_nonneg (zero_lt_one.trans b1).le _
  let X:=L^d
  have X1:1 ≤ X:=one_le_pow₀ l1
  have ins:=reciprocal (D N per j) n g0 g1 (lower R simple jn) z0 a0
    (mul_nonneg B0 (zero_le_one.trans X1)) (heat b1 band n) (paid N per j kj jn) (income N per j kj jn)
  rw [inv_div] at ins
  have xx:X ≤ X^2:=by nlinarith only [mul_nonneg (sub_nonneg.mpr X1) (zero_le_one.trans X1)]
  have coal:2*(a*(B*X)^2+B*X) ≤ C*X^2:=by dsimp [C];nlinarith only [mul_le_mul_of_nonneg_left xx B0]
  have equiv:X^2=L^(2*d):=by dsimp [X];rw [←pow_mul,Nat.mul_comm]
  exact ins.trans (mul_le_mul_of_nonneg_right (coal.trans_eq (by rw [equiv])) z0)
end YM.Integration.WilsonReportingAbsoluteInletForecastBookStep
