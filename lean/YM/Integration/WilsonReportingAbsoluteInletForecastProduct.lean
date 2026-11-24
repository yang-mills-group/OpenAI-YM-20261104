import YM.Integration.WilsonReportingAbsoluteInletForecastRate

/-! The actual quarter-order single-date kinetic invoice, before all subsequent
cutoffs and periods, pays the complete product at the original quadratic-log
window on that same measured family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastProduct
open Filter Finset Real Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReportingAbsoluteInletNativeDates WilsonReportingAbsoluteInletNativeInvoice
open WilsonReportingAbsoluteInletForecastRate
open scoped Classical Topology BigOperators
variable {G:Gauge}

def FiledStep (R:Run G) (p:ℕ) (h:ℕ→ℕ→ℕ→ℝ) :Prop:=
  ∃C:ℝ,∃ d:ℕ,0≤C ∧ ∀ᶠ k:ℕ in atTop,∀N per j,k≤j→j<N→
    let g:=fun t=>regulatorRun R.family N per t
    1/2≤h N per j ∧ |log (g (j+1)/g j)-log (h N per j)|≤
      C*(lag R.family j)^d*(R.family.path.levels.clock.hatBeta j)^exponent p

def PositiveStep (R:Run G) (p:ℕ) (h:ℕ→ℕ→ℕ→ℝ) :Prop:=
  ∃C:ℝ,∃ d:ℕ,0≤C ∧ ∀ᶠ k:ℕ in atTop,∀N per j,k≤j→j<N→
    let g:=fun t=>regulatorRun R.family N per t
    0<h N per j ∧ |log (g (j+1)/g j)-log (h N per j)|≤
      C*(lag R.family j)^d*(R.family.path.levels.clock.hatBeta j)^exponent p

private theorem telescope (g:ℕ→ℝ)(k J:ℕ)(kJ:k ≤ J)(pos:∀i,k ≤ i → i ≤ J → 0 < g i):
    (∑t∈range (J-k),log (g (k+t+1)/g (k+t)))=log (g J/g k):=by
  let l:=fun t=>log (g (k+t))
  have cell (t:ℕ)(ht:t∈range (J-k)):log (g (k+t+1)/g (k+t))=l (t+1)-l t:=by
    have free:=mem_range.mp ht
    rw [log_div (pos _ (by omega) (by omega)).ne' (pos _ (by omega) (by omega)).ne',Nat.add_assoc]
  calc _=∑t∈range (J-k),(l (t+1)-l t):=sum_congr rfl cell
       _=l (J-k)-l 0:=sum_range_sub l (J-k)
       _=log (g J/g k):=by dsimp [l];rw [show k+(J-k)=J by omega,log_div (pos _ kJ le_rfl).ne' (pos _ le_rfl kJ).ne']

private theorem number {r y g ε:ℝ}(p:ℕ)(_ep:0 < ε)(r0:0 < r)(rr:r  ≤  3)(y0:0 < y)(g0:0  ≤  g)(g1:g  ≤  1)
    (cash:|log r-log y|  ≤  (min ε 1/6)*g^p):|r-y|  ≤  ε*g^p:=by
  let z:=log y-log r
  have zpay:|z|  ≤  (min ε 1/6)*g^p:=by change |log y-log r|  ≤  _;rw [abs_sub_comm];exact cash
  have zsmall:|z|  ≤  1:=by
    have m:=mul_le_mul_of_nonneg_right (show min ε 1/6  ≤  1/6 by linarith only [min_le_right ε (1:ℝ)]) (pow_nonneg g0 p)
    linarith only [zpay,m,(show g^p  ≤  1 from pow_le_one₀ g0 g1)]
  have eqn:r*(exp z-1)=y-r:=by
    dsimp only [z]
    rw [exp_sub,exp_log y0,exp_log r0]
    field_simp
  rw [abs_sub_comm r y,←eqn,abs_mul,abs_of_pos r0]
  calc
    r*|exp z-1|  ≤  r*(2*|z|):=mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le zsmall) r0.le
    _  ≤  3*(2*|z|):=mul_le_mul_of_nonneg_right rr (by positivity)
    _  ≤  ε*g^p:=by
      have m:=mul_le_mul_of_nonneg_right (min_le_left ε (1:ℝ)) (pow_nonneg g0 p)
      linarith only [zpay,m]

private theorem ratio (R:Run G) (simple:G.Simple) {N k per:ℕ} (live:k≤N):
    regulatorRun R.family N per N/regulatorRun R.family N per k≤3:=by
  let A:=R.family.path.levels
  let a:=R.family.path.β N per k
  let b:=R.family.path.β N per N
  have ma:=R.makes.wilson.represents N per k live
  have mb:=R.makes.wilson.represents N per N le_rfl
  have ha:0<A.clock.hatBeta k:=zero_lt_one.trans (A.fits.delayed k)
  have hb:0<A.clock.hatBeta N:=zero_lt_one.trans (A.fits.delayed N)
  have bd:A.clock.hatBeta k≤A.clock.hatBeta N:=(Real.log_le_log_iff ha hb).1 (logarithm_monotone A simple live)
  have ap:0<a:=(half_pos ha).trans_le ma.band.1
  have bp:0<b:=(half_pos hb).trans_le mb.band.1
  have lo:A.clock.hatBeta N/2≤b:=mb.band.1
  have hi:a≤2*A.clock.hatBeta k:=ma.band.2
  have scale:a≤4*b:=by linarith only [lo,hi,bd]
  have step:sqrt a≤3*sqrt b:=by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    nlinarith only [Real.sq_sqrt ap.le,Real.sq_sqrt bp.le,scale,bp]
  change (sqrt b)⁻¹/(sqrt a)⁻¹≤3
  rw [div_inv_eq_mul,mul_comm,←div_eq_mul_inv]
  exact (div_le_iff₀ (sqrt_pos.2 bp)).2 step

theorem positive (R:Run G) (simple:G.Simple) (p:ℕ) (h:ℕ→ℕ→ℕ→ℝ)
    (fund:PositiveStep R (p+2) h):InversePrice R p h:=by
  obtain ⟨C,d,C0,paid⟩:=fund
  intro ε ep
  let η:=min ε 1/6
  have pos:0<η:=div_pos (lt_min ep zero_lt_one) (by norm_num)
  let A:=R.family.path.levels
  filter_upwards [paid,WilsonReportingAbsoluteInletForecastRate.purchase R simple (p+2) d C0 pos,
    (Next.Rank.Station.hat_rate A simple).eventually_ge_atTop 2] with k individual fees hot N per kN cap
  let g:=fun t=>regulatorRun R.family N per t
  have point:∀i,i≤N→0<g i:=by
    intro i hi
    have x:=R.makes.wilson.represents N per i hi
    have b:0<R.family.path.β N per i:=(half_pos (zero_lt_one.trans (A.fits.delayed i))).trans_le x.band.1
    exact inv_pos.2 (sqrt_pos.2 b)
  have cold:g k≤1:=by
    have lo:A.clock.hatBeta k/2≤R.family.path.β N per k:=(R.makes.wilson.represents N per k kN).band.1
    have ba:1≤R.family.path.β N per k:=by linarith only [hot,lo]
    have root:1 ≤ sqrt (R.family.path.β N per k):=by simpa only [Real.sqrt_one] using sqrt_le_sqrt ba
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one root)).2 root
  have positive:∀j∈range (N-k),0<h N per (k+j):=by
    intro j hj
    have e:=mem_range.mp hj
    exact (individual N per (k+j) (by omega) (by omega)).1
  apply number (p+2) ep (div_pos (point N le_rfl) (point k kN)) (ratio R simple kN)
    (prod_pos positive) (point k kN).le cold
  rw [Real.log_prod (fun j hj=>(positive j hj).ne'),
    ←telescope g k N kN (fun i _ hi=>point i hi),←sum_sub_distrib]
  obtain same|more:=eq_or_lt_of_le kN
  · subst N
    simp only [Nat.sub_self,Finset.range_zero,Finset.sum_empty,abs_zero]
    exact mul_nonneg pos.le (pow_nonneg (point k le_rfl).le _)
  have duration:0<((N-k:ℕ):ℝ):=by exact_mod_cast Nat.sub_pos_of_lt more
  calc
    _ ≤ ∑j∈range (N-k), |log (g (k+j+1)/g (k+j))-log (h N per (k+j))|:=abs_sum_le_sum_abs _ _
    _ ≤ ∑_j∈range (N-k), η*(g k)^(p+2)/((N-k:ℕ):ℝ):=by
      apply sum_le_sum
      intro j hj
      have e:=mem_range.mp hj
      have jN:k+j<N:=by omega
      have paidStep:=individual N per (k+j) (by omega) jN
      have fee:=fees N per (k+j) (by omega) jN.le cap
      apply (le_div_iff₀ duration).2
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left paidStep.2 duration.le).trans fee
    _ = _:=by rw [sum_const,card_range,nsmul_eq_mul];change ((N-k:ℕ):ℝ)*(η*(g k)^(p+2)/((N-k:ℕ):ℝ))=η*(g k)^(p+2);field_simp [duration.ne']

theorem original (R:Run G) (simple:G.Simple) (p:ℕ) (h:ℕ→ℕ→ℕ→ℝ)
    (fund:FiledStep R (p+2) h):InversePrice R p h:=by
  obtain ⟨C,d,C0,step⟩:=fund
  apply positive R simple p h
  refine ⟨C,d,C0,?_⟩
  filter_upwards [step] with k paid N per j kj jN
  have price:=paid N per j kj jN
  exact ⟨lt_of_lt_of_le (by norm_num:0<(1:ℝ)/2) price.1,price.2⟩

end YM.Integration.WilsonReportingAbsoluteInletForecastProduct

