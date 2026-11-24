import YM.Integration.WilsonPhysicalPositionBookedBranch
import YM.Integration.WilsonMovingForkStoppedHeat

/-! At fixed appointment exponent, successive genuine Wilson steps separate
rulers by at least a factor two, uniformly on the late original calendar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionFirstWeakClock
open Filter Set Lattice Wilson RG PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Station
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale

private theorem slow {p:ℝ}(hp:0≤p){x y:ℝ}(hot:Real.exp 1≤x)(weight:2*p≤x)(xy:x≤y):
    p*(Real.log (Real.log y))^2-p*(Real.log (Real.log x))^2≤y-x:=by
  let f(u:ℝ):=p*(Real.log (Real.log u))^2
  let slope(u:ℝ):=(2*p/u)*(Real.log (Real.log u)/Real.log u)
  have base {u:ℝ}(eu:Real.exp 1≤u):1≤Real.log u:=by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) eu
  have diff {u:ℝ}(eu:Real.exp 1≤u):HasDerivAt f (slope u) u:=by
    have up:0<u:=(Real.exp_pos _).trans_le eu
    have lp:0<Real.log u:=zero_lt_one.trans_le (base eu)
    have hd:=(((Real.hasDerivAt_log lp.ne').comp u (Real.hasDerivAt_log up.ne')).pow 2).const_mul p
    apply hd.congr_deriv
    simp [slope,div_eq_mul_inv]
    ring
  rcases xy.eq_or_lt with rfl|lt
  · simp
  obtain ⟨u,hu,eq⟩:=exists_hasDerivAt_eq_slope f slope lt
    (fun z hz=>(diff (hot.trans hz.1)).continuousAt.continuousWithinAt)
    (fun z hz=>diff (hot.trans hz.1.le))
  have eu:=hot.trans hu.1.le
  have up:0<u:=(Real.exp_pos _).trans_le eu
  have lp:0<Real.log u:=zero_lt_one.trans_le (base eu)
  have logle:Real.log (Real.log u)≤Real.log u:=(Real.log_le_sub_one_of_pos lp).trans (by linarith)
  have bound:slope u≤1:=calc
    _ ≤ (2*p/u)*1:=mul_le_mul_of_nonneg_left ((div_le_one lp).mpr logle) (by positivity)
    _ ≤ 1:=by rw [mul_one];exact (div_le_one up).mpr (weight.trans hu.1.le)
  rw [eq] at bound
  exact (div_le_one (sub_pos.mpr lt)).mp bound

private theorem log_gap (b:ℝ)(k:ℕ):Real.log (Station.gap A b k)=
    -σ k+b*(Real.log (Real.log (β k)))^2:=by
  rw [Station.gap,Real.log_mul (R.family.S.a_pos _).ne' (Station.mag_pos ..).ne']
  unfold Station.mag
  rw [Real.log_rpow (show 0<(A).clock.monitor k from Real.exp_pos _)]
  change Real.log (R.family.S.a k)+b*Real.log (Real.exp _)=_
  rw [Real.log_exp]
  simp only [Schedule.scale,Real.log_inv,neg_neg]

theorem one (simple:G.Simple)(b:ℝ)(hb:0≤b):
    ∀ᶠk:ℕ in atTop,4*(Real.log (Station.gap A b (k+1))-Real.log (Station.gap A b k))≤-3*Real.log 3:=by
  have cp:=Gauge.slopeConstant_pos simple
  have lim:=Station.hat_rate A simple
  filter_upwards [lim.eventually_ge_atTop (Real.exp 1),lim.eventually_ge_atTop (2*(4*G.slopeConstant*b))]
    with k hot enough
  have big:(3:ℝ)≤(R.family.S.block k).val:=by exact_mod_cast R.family.S.block_large k
  have bound:=Real.log_le_log (by norm_num : 0<(3:ℝ)) big
  have delta:β (k+1)-β k=G.slopeConstant*Real.log (R.family.S.block k).val:=by
    change _+_*σ (k+1)-(_+_*σ k)=_
    rw [Schedule.scale_succ];ring
  have mono:=WilsonStartup.Timing.hat_mono A cp.le (Nat.le_succ k)
  have change:=slow (p:=4*G.slopeConstant*b) (by positivity) hot enough mono
  rw [delta] at change
  have paid:4*b*((Real.log (Real.log (β (k+1))))^2-(Real.log (Real.log (β k)))^2)≤
      Real.log (R.family.S.block k).val:=by
    apply le_of_mul_le_mul_left _ cp
    linarith only [change]
  rw [log_gap R,log_gap R,Schedule.scale_succ]
  linarith only [paid,bound]

theorem halves (simple:G.Simple)(b:ℝ)(hb:0≤b):∀ᶠk:ℕ in atTop,
    2*Station.gap A b (k+1) ≤ Station.gap A b k:=by
  filter_upwards [one R simple b hb] with k step
  have room:4*Real.log (2:ℝ)≤3*Real.log (3:ℝ):=by
    have h:=Real.log_le_log (by norm_num : 0<(2:ℝ)^4) (by norm_num : (2:ℝ)^4≤3^3)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have cap:Real.log (2*(Station.gap A b (k+1)))≤Real.log (Station.gap A b k):=by
    rw [Real.log_mul (by norm_num) (Station.gap_pos ..).ne']
    linarith only [step,room]
  exact (Real.log_le_log_iff (mul_pos (by norm_num) (Station.gap_pos ..)) (Station.gap_pos ..)).mp cap

end YM.Integration.WilsonPhysicalPositionFirstWeakClock
end
