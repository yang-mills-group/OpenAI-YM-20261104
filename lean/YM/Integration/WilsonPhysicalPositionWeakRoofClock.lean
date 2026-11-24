import YM.Integration.WilsonPhysicalPositionWeakRoofRuler

/-! Slow variation of the single all-grade ruler on the actual Wilson clock. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionWeakRoofClock
open Filter Set Lattice Wilson RG PhysicalNext.Repeat.Legato Next.Rank
open WilsonPhysicalPositionWeakRoofRuler
open scoped Classical Topology
variable {G:Gauge}

private theorem square {x:ℝ} (pos:0<x) (hot:0≤Real.log x):
    (Real.log x)^2 ≤ 4*x := by
  let z := Real.log x/2
  have h:0≤z := by dsimp [z]; positivity
  have small:z≤Real.exp z := by linarith only [Real.add_one_le_exp z]
  have prod := mul_self_le_mul_self h small
  have eq:Real.exp z * Real.exp z = x := by
    rw [←Real.exp_add,show z+z=Real.log x by dsimp [z];ring,Real.exp_log pos]
  rw [eq] at prod
  dsimp [z] at prod
  nlinarith only [prod]

private theorem cubic {p:ℝ}(hp:0≤p){x y:ℝ}(hot:Real.exp 1≤x)(weight:12*p≤x)(xy:x≤y):
    p*(Real.log (Real.log y))^3-p*(Real.log (Real.log x))^3≤y-x:=by
  let f(u:ℝ):=p*(Real.log (Real.log u))^3
  let slope(u:ℝ):=(3*p/u)*((Real.log (Real.log u))^2/Real.log u)
  have base {u:ℝ}(eu:Real.exp 1≤u):1≤Real.log u:=by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) eu
  have diff {u:ℝ}(eu:Real.exp 1≤u):HasDerivAt f (slope u) u:=by
    have up:0<u:=(Real.exp_pos _).trans_le eu
    have lp:0<Real.log u:=zero_lt_one.trans_le (base eu)
    have hd:=(((Real.hasDerivAt_log lp.ne').comp u (Real.hasDerivAt_log up.ne')).pow 3).const_mul p
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
  have bound:slope u≤1:=calc
    _ ≤ (3*p/u)*4:=mul_le_mul_of_nonneg_left
      ((div_le_iff₀ lp).mpr (square lp (Real.log_nonneg (base eu)))) (by positivity)
    _ = (12*p)/u:=by ring
    _ ≤ 1:=(div_le_one up).mpr (weight.trans hu.1.le)
  rw [eq] at bound
  exact (div_le_one (sub_pos.mpr lt)).mp bound

private theorem increase {lo hi a e : ℝ} (hl : 0 ≤ lo) (hm : lo ≤ hi)
    (cap : a ≤ lo) (step : e - a ≤ hi - lo) : e * hi^2 - a * lo^2 ≤ hi^3 - lo^3 := by
  have squares:=pow_le_pow_left₀ hl hm 2
  nlinarith only [mul_le_mul_of_nonneg_right cap (sub_nonneg.mpr squares),
    mul_le_mul_of_nonneg_right step (sq_nonneg hi)]

def dial (R:Run G) (b t:ℕ → ℝ) (k:ℕ) : ℝ :=
  height b t (Real.log (Real.log (R.family.path.levels.clock.hatBeta k)))

def ruler (R:Run G) (b t:ℕ → ℝ) (k:ℕ) : ℝ :=
  Station.gap R.family.path.levels (dial R b t k) k

private theorem log_ruler (R:Run G) (b t:ℕ → ℝ) (k:ℕ):
    Real.log (ruler R b t k) = -R.family.S.scale k +
      dial R b t k * (Real.log (Real.log (R.family.path.levels.clock.hatBeta k)))^2 := by
  rw [ruler,Station.gap,Real.log_mul (R.family.S.a_pos _).ne' (Station.mag_pos ..).ne']
  unfold Station.mag
  rw [Real.log_rpow (show 0<R.family.path.levels.clock.monitor k from Real.exp_pos _)]
  change Real.log (R.family.S.a k)+dial R b t k*Real.log (Real.exp _)=_
  rw [Real.log_exp]
  simp only [Schedule.scale,Real.log_inv,neg_neg]

theorem halves (R:Run G) (simple:G.Simple) (b t:ℕ → ℝ) (positive:∀ d,0≤b d)
    (first:b 0≤t 0):∀ᶠ k:ℕ in atTop, 2*ruler R b t (k+1)≤ruler R b t k := by
  let A:=R.family.path.levels
  let β:=A.clock.hatBeta
  let y(k:ℕ):=Real.log (Real.log (β k))
  have cp:=Gauge.slopeConstant_pos simple
  have lim:=Station.hat_rate A simple
  have levels:Tendsto y atTop atTop:=Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp lim)
  filter_upwards [lim.eventually_ge_atTop (Real.exp 1),lim.eventually_ge_atTop (12*(4*G.slopeConstant)),
    levels.eventually_ge_atTop (t 0)] with k hot enough ready
  have big:(3:ℝ)≤(R.family.S.block k).val:=by exact_mod_cast R.family.S.block_large k
  have block:=Real.log_le_log (by norm_num : 0<(3:ℝ)) big
  have delta:β (k+1)-β k=G.slopeConstant*Real.log (R.family.S.block k).val:=by
    change _+_*R.family.S.scale (k+1)-(_+_*R.family.S.scale k)=_
    rw [Schedule.scale_succ];ring
  have mono:=WilsonStartup.Timing.hat_mono A cp.le (Nat.le_succ k)
  have loghot:1≤Real.log (β k):=by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hot
  have yp:0≤y k:=Real.log_nonneg loghot
  have ymono:y k≤y (k+1):=Real.log_le_log (zero_lt_one.trans_le loghot)
    (Real.log_le_log ((Real.exp_pos _).trans_le hot) mono)
  have bound:=cubic (p:=4*G.slopeConstant) (by positivity) hot enough mono
  rw [delta] at bound
  have slope:4*(y (k+1)^3-y k^3)≤Real.log (R.family.S.block k).val:=by
    apply le_of_mul_le_mul_left _ cp
    dsimp [y]
    linarith only [bound]
  have diff:=increase yp ymono (capped b t positive first ready) (rate b t positive ymono).2
  have step:4*(Real.log (ruler R b t (k+1))-Real.log (ruler R b t k))≤-3*Real.log 3:=by
    rw [log_ruler,log_ruler,Schedule.scale_succ]
    change 4*((-(R.family.S.scale k+_)+height b t (y (k+1))*y (k+1)^2)-
      (-R.family.S.scale k+height b t (y k)*y k^2))≤_
    linarith only [diff,slope,block]
  have room:4*Real.log (2:ℝ)≤3*Real.log (3:ℝ):=by
    have h:=Real.log_le_log (by norm_num : 0<(2:ℝ)^4) (by norm_num : (2:ℝ)^4≤3^3)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have cap:Real.log (2*ruler R b t (k+1))≤Real.log (ruler R b t k):=by
    rw [Real.log_mul (by norm_num) (show 0<ruler R b t (k+1) from Station.gap_pos ..).ne']
    linarith only [step,room]
  exact (Real.log_le_log_iff (mul_pos (by norm_num) (Station.gap_pos ..)) (Station.gap_pos ..)).mp cap

end YM.Integration.WilsonPhysicalPositionWeakRoofClock
end
