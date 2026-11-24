import YM.Integration.WilsonReportingAbsoluteInletForecastDepth

/-! Original finite-order kinetic fee with its extra quarter order. Any
fixed power of the reported logarithm and the genuine number of intermediate
invoices are absorbed before the regulator and the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastRate
open Filter Finset Real Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReportingAbsoluteInletNativeDates
open scoped Classical Topology BigOperators
variable {G:Gauge}
def exponent (p:ℕ):ℝ := -((p:ℝ)+1/4)/2

theorem spend (d:ℕ) {s ε:ℝ} (hot:0<s) (positive:0<ε):
    ∀ᶠ x:ℝ in atTop, (2+log x)^d≤ε*x^s:=by
  let K:=(2/s)^d
  have kp:0<K:=pow_pos (div_pos (by norm_num) hot) _
  have up:Tendsto (fun x:ℝ=>x^s) atTop atTop:=tendsto_rpow_atTop hot
  filter_upwards [up.eventually ((Real.isLittleO_pow_log_id_atTop (n:=d)).bound (div_pos positive kp)),
    eventually_ge_atTop (exp 2)] with x price xl
  have xp:0<x:=(exp_pos _).trans_le xl
  have lx:2≤log x:=(le_log_iff_exp_le xp).2 xl
  have Ly:0≤log (x^s):=by rw [Real.log_rpow xp];exact mul_nonneg hot.le (by linarith only [lx])
  have y0:0≤x^s:=(rpow_pos_of_pos xp _).le
  have inv:(log (x^s))^d≤(ε/K)*(x^s):=by
    simpa [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg Ly d),abs_of_nonneg Ly,abs_of_nonneg y0] using price
  have fit:2+log x≤(2/s)*log (x^s):=by
    rw [Real.log_rpow xp,←mul_assoc,div_mul_cancel₀ 2 hot.ne']
    linarith only [lx]
  calc
    _ ≤ ((2/s)*log (x^s))^d:=pow_le_pow_left₀ (by linarith only [lx]) fit d
    _ = K*(log (x^s))^d:=mul_pow _ _ _
    _ ≤ K*((ε/K)*x^s):=mul_le_mul_of_nonneg_left inv kp.le
    _ = _:=by field_simp [kp.ne']

private theorem monotone (A:Levels G) (simple:G.Simple):Monotone A.clock.hatBeta:=by
  intro i j ij
  apply (Real.log_le_log_iff (zero_lt_one.trans (A.fits.delayed i)) (zero_lt_one.trans (A.fits.delayed j))).1
  exact logarithm_monotone A simple ij

theorem scale (p:ℕ) {x a:ℝ} (xp:0<x) (ap:0<a) (cap:a≤2*x):
    x^(-(p:ℝ)/2)≤(2:ℝ)^p*((sqrt a)⁻¹)^p:=by
  have ratio:sqrt a≤2*sqrt x:=by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    nlinarith only [Real.sq_sqrt ap.le,Real.sq_sqrt xp.le,cap,xp]
  have xg:(sqrt x)⁻¹≤2*(sqrt a)⁻¹:=by
    rw [←div_eq_mul_inv]
    apply (le_div_iff₀ (sqrt_pos.2 ap)).2
    rw [mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ (sqrt_pos.2 xp)).2 ratio
  have root:x^(-(p:ℝ)/2)=((sqrt x)⁻¹)^p:=by
    rw [←Real.rpow_natCast,Real.sqrt_eq_rpow,←Real.rpow_neg xp.le,
      ←Real.rpow_mul xp.le]
    congr 1
    ring
  rw [root,←mul_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 (sqrt_nonneg _)) xg p

theorem purchase (R:Run G) (simple:G.Simple) (p d:ℕ){C ε:ℝ} (C0:0≤C) (ep:0<ε):
    ∀ᶠ k:ℕ in atTop,∀N per j,k≤j→j≤N→N≤ultraviolet R.family 2 k→
    ((N-k:ℕ):ℝ)*(C*(lag R.family j)^d*(R.family.path.levels.clock.hatBeta j)^exponent p)
      ≤ ε*(regulatorRun R.family N per k)^p:=by
  let A:=R.family.path.levels
  let L:=log (3:ℝ)
  have Lp:0<L:=log_pos (by norm_num)
  let E:=1+1/L
  have Ep:0<E:=by dsimp only [E];positivity
  let c:=ε/((1+C)*E*(2:ℝ)^p)
  have cp:0<c:=by dsimp only [c];positivity
  have rate:=Next.Rank.Station.hat_rate A simple
  obtain ⟨threshold,localCash⟩:=eventually_atTop.mp (rate.eventually (spend d (s:=1/16) (by norm_num) one_pos))
  filter_upwards [eventually_ge_atTop threshold,rate.eventually (spend 2 (s:=1/16) (by norm_num) cp)] with k early logk N per j kj jN cap
  let x:=A.clock.hatBeta k
  let y:=A.clock.hatBeta j
  let a:=R.family.path.β N per k
  have xp:0<x:=zero_lt_one.trans (A.fits.delayed k)
  have yp:0<y:=zero_lt_one.trans (A.fits.delayed j)
  have xy:x≤y:=monotone A simple kj
  have live:=R.makes.wilson.represents N per k (kj.trans jN)
  have ap:0<a:=(half_pos xp).trans_le live.band.1
  have lk:1≤lag R.family k:=by change 1≤2+log x;linarith only [Real.log_pos (A.fits.delayed k)]
  have l2:1≤(lag R.family k)^2:=one_le_pow₀ lk
  have count:=WilsonReportingAbsoluteInletForecastDepth.count R.family (kj.trans jN) cap
  have week:((N-k:ℕ):ℝ)≤E*(c*x^(1/16:ℝ)):=by
    have price:(lag R.family k)^2≤c*x^(1/16:ℝ):=logk
    refine count.trans (le_trans ?_ (mul_le_mul_of_nonneg_left price Ep.le))
    change 1+(lag R.family k)^2/L≤(1+1/L)*(lag R.family k)^2
    rw [add_mul,one_mul,one_div,mul_comm L⁻¹,←div_eq_mul_inv]
    exact add_le_add l2 le_rfl
  let n:=-(p:ℝ)/2-1/16
  have neg:n ≤ 0:=by dsimp only [n];linarith only [Nat.cast_nonneg (α:=ℝ) p]
  have old:C*(lag R.family j)^d*y^exponent p≤C*x^n:=by
    have localPrice:(lag R.family j)^d≤y^(1/16:ℝ):=by
      simpa only [lag,y,A,one_mul] using localCash j (early.trans kj)
    have prod:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left localPrice C0)
      (rpow_pos_of_pos yp (exponent p)).le
    refine prod.trans ?_
    rw [mul_assoc,←Real.rpow_add yp]
    have ex:(1/16:ℝ)+exponent p=n:=by dsimp [exponent,n];ring
    rw [ex]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos xp xy neg) C0
  have factor:C*E*c≤ε/(2:ℝ)^p:=by
    have D:0<(1+C)*E*(2:ℝ)^p:=by positivity
    dsimp only [c]
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ D (by positivity)).2
    nlinarith only [mul_nonneg (mul_nonneg ep.le Ep.le) (pow_nonneg (by norm_num:0≤(2:ℝ)) p)]
  have rpowSum:x^(1/16:ℝ)*x^n=x^(-(p:ℝ)/2):=by
    rw [←Real.rpow_add xp]
    congr 1
    dsimp only [n]
    ring
  calc
    _ ≤ (E*(c*x^(1/16:ℝ)))*(C*x^n):=
      (mul_le_mul_of_nonneg_left old (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right week (mul_nonneg C0 (rpow_pos_of_pos xp n).le))
    _ = C*E*c*x^(-(p:ℝ)/2):=by rw [←rpowSum];ring
    _ ≤ (ε/(2:ℝ)^p)*((2:ℝ)^p*((sqrt a)⁻¹)^p):=
      (mul_le_mul_of_nonneg_right factor (rpow_pos_of_pos xp _).le).trans
       (mul_le_mul_of_nonneg_left (scale p xp ap live.band.2) (by positivity))
    _ = _:=by change (ε/(2:ℝ)^p)*((2:ℝ)^p*((sqrt a)⁻¹)^p)=ε*((sqrt a)⁻¹)^p;field_simp
end YM.Integration.WilsonReportingAbsoluteInletForecastRate
