import YM.Integration.WilsonReportingAbsoluteInletNativeInvoice

/-! One genuine power of the measured coupling pays the number of discrete
factors in the original squared-logarithmic forward window, uniformly in
the period. This is used when accumulating a separately filed action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastDepth
open Filter Finset Real Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReportingAbsoluteInletNativeDates
open scoped Classical Topology BigOperators
variable {G:Gauge}

private theorem spans (S:Schedule) (k n:ℕ):
    (n:ℝ)*log 3 ≤ S.scale (k+n)-S.scale k:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    have b:log (3:ℝ)≤log ((S.block (k+n)).val:ℝ):=
      log_le_log (by norm_num) (by exact_mod_cast S.block_large (k+n))
    rw [←Nat.add_assoc,S.scale_succ,Nat.cast_succ,add_mul,one_mul]
    linarith only [b,ih]

theorem count (C:Family G) {k N:ℕ} (kN:k≤N) (bound:N≤ultraviolet C 2 k):
    ((N-k:ℕ):ℝ)≤1+(lag C k)^2/log 3:=by
  have lp:0<log (3:ℝ):=log_pos (by norm_num)
  rcases eq_or_lt_of_le kN with e|live
  · rw [e,Nat.sub_self,Nat.cast_zero];positivity
  let i:=N-1
  have ki:k ≤ i:=by dsimp [i];omega
  have sub:i<N:=by dsimp [i];omega
  have prior:C.S.scale i<C.S.scale k+(lag C k)^2:=by
    by_contra! late
    have chosen:ultraviolet C 2 k ≤ i:=by
      unfold ultraviolet crossing
      apply Nat.find_min'
      simpa only [Real.rpow_two] using late
    omega
  have steps:=spans C.S k (i-k)
  rw [Nat.add_sub_of_le ki] at steps
  have spend:((i-k:ℕ):ℝ)≤(lag C k)^2/log 3:=by
    apply (le_div_iff₀ lp).2
    linarith only [steps,prior]
  have card:N-k=(i-k)+1:=by dsimp [i];omega
  rw [card,Nat.cast_add,Nat.cast_one]
  linarith only [spend]

private theorem log_price : ∀ᶠ x:ℝ in atTop,2*(1+(2+log (x^2))^2/log 3)≤x:=by
  have lp:0<log (3:ℝ):=log_pos (by norm_num)
  have small:0<log (3:ℝ)/64:=by positivity
  filter_upwards [(Real.isLittleO_pow_log_id_atTop (n:=2)).bound small,
    eventually_ge_atTop (max (exp 1) 4)] with x rate lower
  have x4:(4:ℝ)≤x:=(le_max_right _ _).trans lower
  have xp:0<x:=by linarith only [x4]
  have lx:1≤log x:=(Real.le_log_iff_exp_le xp).2 ((le_max_left _ _).trans lower)
  have q:(log x)^2≤(log 3/64)*x:=by
    simpa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (log x)),abs_of_nonneg xp.le] using rate
  have a:2+2*log x≤4*log x:=by linarith only [lx]
  have b:0≤2+2*log x:=by linarith only [lx]
  have sq:=(pow_le_pow_left₀ b a 2)
  have num:(2+log (x^2))^2≤(x/4)*log 3:=by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [q,sq]
  have div:((2+log (x^2))^2/log 3)≤x/4:=(div_le_iff₀ lp).2 num
  linarith only [div,x4]

theorem original (R:Run G) (simple:G.Simple):∀ᶠ k:ℕ in atTop,∀N per,k≤N→N≤ultraviolet R.family 2 k→
    ((N-k:ℕ):ℝ)*regulatorRun R.family N per k≤1:=by
  let A:=R.family.path.levels
  have hot:Tendsto (fun k=>sqrt (A.clock.hatBeta k)) atTop atTop:=
    Real.tendsto_sqrt_atTop.comp (Next.Rank.Station.hat_rate A simple)
  filter_upwards [hot.eventually log_price] with k paid N per kN cap
  let b:=A.clock.hatBeta k
  let α:=R.family.path.β N per k
  have bp:0<b:=zero_lt_one.trans (A.fits.delayed k)
  have component:b/2≤α:=(R.makes.wilson.represents N per k kN).band.1
  have ap:0<α:=by linarith only [bp,component]
  have bq:(sqrt b)^2=b:=Real.sq_sqrt bp.le
  have aq:(sqrt α)^2=α:=Real.sq_sqrt ap.le
  have aroot:0<sqrt α:=Real.sqrt_pos.2 ap
  have half:sqrt b/2 ≤ sqrt α:=by
    apply (sq_le_sq₀ (by positivity) aroot.le).mp
    nlinarith only [bq,aq,component,bp]
  have price:2*(1+(lag R.family k)^2/log 3) ≤ sqrt b:=by
    change 2*(1+(2+log ((sqrt b)^2))^2/log 3) ≤ sqrt b at paid
    simpa only [lag,b,A,bq] using paid
  have n:=count R.family kN cap
  change ((N-k:ℕ):ℝ)*(sqrt α)⁻¹≤1
  rw [←div_eq_mul_inv]
  apply (div_le_one aroot).2
  linarith only [n,price,half]
end YM.Integration.WilsonReportingAbsoluteInletForecastDepth
