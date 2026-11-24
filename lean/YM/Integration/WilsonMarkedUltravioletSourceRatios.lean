import YM.RG05Readout.Many.Pick
import YM.Integration.WilsonMarkedUltravioletRadii
import YM.Integration.WilsonWindowReportingPace
import YM.MSbar.Atlas.Apex

/-! Adjacent radii of the original tuned singleton on the same slow physical family. The normalization at the reporting date cancels, even when it varies with the submitted source. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMarkedUltravioletSourceRatios
open Real Function Filter Lattice RG RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Copper
open PhysicalNext.Repeat.Legato WilsonMeasuredAdmission MSbar MSbar.Heath.Stock
open scoped Classical Topology
variable {G:Gauge}

private theorem boundary (A:Levels G)(g:G.Simple): ∀ᶠi:ℕ in atTop,A.clock.hatBeta (i+1) ≤ 2*A.clock.hatBeta i:=by
  filter_upwards [A.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),A.S.divergent.eventually_gt_atTop 0] with i hi he
  have hS:Real.log (A.S.block i).val ≤ A.S.scale i:=by
    have hh:Real.log (A.S.block i).val/A.S.scale i ≤ 1:=hi
    simpa using (div_le_iff₀ he).mp hh
  unfold RG.Calendar.hatBeta
  rw [Schedule.scale_succ]
  nlinarith only [A.clock.bar_pos,mul_le_mul_of_nonneg_left hS (Gauge.slopeConstant_pos g).le]

def radius (C:Family G)(Q:ℝ)(k d m i:ℕ)(β:ℝ):ℝ:=(cue β)^k/Many.total C Q d m i

private theorem logchange (C:Family G) {Q:ℝ}(qp:0 < Q)(k d:ℕ){m i:ℕ}(mi:m ≤ i){x y:ℝ}(xp:0 < x)(yp:0 < y):
    Real.log (radius C Q k d m i x/radius C Q k d m (i+1) y)=
      Real.log (ld C.path.levels i) + (k:ℝ)/2*(Real.log y-Real.log x):=by
  have cx:0 < cue x:=inv_pos.mpr (Real.sqrt_pos.2 xp)
  have cy:0 < cue y:=inv_pos.mpr (Real.sqrt_pos.2 yp)
  have tu:0 < Many.total C Q d m i:=Many.totalpos qp i
  have ell:0 < ld C.path.levels i:=zero_lt_one.trans_le (lamp_nn (C:=C) i)
  have ratio:radius C Q k d m i x/radius C Q k d m (i+1) y=ld C.path.levels i*(cue x/cue y)^k:=by
    unfold radius
    rw [Many.totaltail (C:=C) (Q:=Q) (d:=d) mi,div_pow]
    field_simp [ne_of_gt tu,ne_of_gt cy,ne_of_gt ell]
  rw [ratio,Real.log_mul ell.ne' (pow_ne_zero _ (div_ne_zero cx.ne' cy.ne')),
      Real.log_pow,Real.log_div cx.ne' cy.ne']
  have form {b:ℝ}(bp:0 < b):Real.log (cue b)= -(Real.log b)/2:=by
    rw [cue,Real.log_inv,Real.log_sqrt bp.le]
    ring
  rw [form xp,form yp]
  ring

theorem band (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(k:ℕ){ε:ℝ}(ep:0 < ε):
    ∀ᶠ i:ℕ in atTop,let A:=R.family.path.levels
      ∀m:ℕ,m ≤ i → ∀(d:ℕ)(Q:ℝ),0 < Q → ∀x y:ℝ,
        A.clock.hatBeta i/2 ≤ x → x ≤ 2*A.clock.hatBeta i →
        A.clock.hatBeta (i+1)/2 ≤ y → y ≤ 2*A.clock.hatBeta (i+1) →
        |Real.log (radius R.family Q k d m i x/radius R.family Q k d m (i+1) y)| ≤ ε*(A.budget i).B:=by
  let A:=R.family.path.levels
  let K:ℝ:=8*(k:ℝ)+3
  have kp:0 ≤ (k:ℝ):=by positivity
  have grown:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate A simple)
  have monotone:=WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le
  filter_upwards [boundary A simple,grown.eventually_ge_atTop (max 1 (K/ε))] with i neighbor tall _ m mi d Q qp x y xl xh yl yh
  have up:=monotone (Nat.le_succ i)
  have bp:0 < A.clock.hatBeta i:=zero_lt_one.trans (A.fits.delayed i)
  have xp:0 < x:=(half_pos bp).trans_le xl
  have yp:0 < y:=(half_pos (bp.trans_le up)).trans_le yl
  have fw:y ≤ 8*x:=by linarith only [xl,yh,neighbor]
  have bw:x ≤ 8*y:=by linarith only [yl,xh,up,bp]
  have l₁:=Real.log_le_log yp fw
  have l₂:=Real.log_le_log xp bw
  rw [Real.log_mul (by norm_num: (8:ℝ)≠0) xp.ne'] at l₁
  rw [Real.log_mul (by norm_num: (8:ℝ)≠0) yp.ne'] at l₂
  have l8:Real.log 8 ≤ 8:=by linarith only [Real.log_le_sub_one_of_pos (by norm_num:0 < (8:ℝ))]
  let z:=Real.log (A.clock.hatBeta i)
  have z1:1 ≤ z:=(le_max_left ..).trans tall
  have paid:K ≤ ε*z:=by
    have h:K/ε ≤ z:=(le_max_right ..).trans tall
    linarith only [(div_le_iff₀ ep).mp h]
  have fund:z^2 ≤ ((A.budget i).B:ℝ):=Nat.le_ceil _
  have reserve:mast A i+8*(k:ℝ) ≤ ε*(A.budget i).B:=by
    have k0:0 ≤ K-1:=by dsimp [K];linarith only [kp]
    have cr:=mul_nonneg (sub_nonneg.mpr paid) (zero_le_one.trans z1)
    have mr:=mul_nonneg k0 (sub_nonneg.mpr z1)
    have fc:=mul_le_mul_of_nonneg_left fund ep.le
    change 2+z+8*(k:ℝ) ≤ _
    dsimp [K] at mr cr
    nlinarith only [mr,cr,fc]
  have many:1 ≤ ld A i:=lamp_nn (C:=R.family) i
  have st:(R.family.S.block i).val ≤ Real.log (mast A i):=slow.2 i
  have lm:Real.log (ld A i) ≤ mast A i:=calc
    _ ≤ ld A i:=Real.log_le_self (zero_le_one.trans many)
    _ ≤ _:=Many.lamp_head (C:=R.family) i
    _ ≤ _:=st
    _ ≤ _:=Real.log_le_self (mast_pos A i).le
  have lp:=Real.log_nonneg many
  rw [logchange R.family qp k d mi xp yp]
  apply le_trans _ reserve
  rw [abs_le]
  constructor <;> nlinarith only [lp,lm,kp,mul_nonneg kp (sub_nonneg.mpr (show -8 ≤ Real.log y-Real.log x by linarith only [l₂,l8])),
    mul_nonneg kp (sub_nonneg.mpr (show Real.log y-Real.log x ≤ 8 by linarith only [l₁,l8]))]

theorem original (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(k:ℕ){ε:ℝ}(ep:0 < ε):
    ∀ᶠ i:ℕ in atTop,∀m:ℕ,m ≤ i →∀(d:ℕ)(Q:ℝ),0 < Q →∀N:ℕ,i+1 ≤ N →∀per:ℕ,
      let Y:=R.family.path.rep N per
      |Real.log (radius R.family Q k d m i (Y i).beta/radius R.family Q k d m (i+1) (Y (i+1)).beta)|
        ≤ ε*(R.family.path.levels.budget i).B:=by
  filter_upwards [band R simple slow k ep] with i bought m mi d Q qp N live per Y
  have old:=(R.makes.wilson.represents N per i (Nat.le_trans (Nat.le_succ i) live)).band
  have fresh:=(R.makes.wilson.represents N per (i+1) live).band
  exact bought m mi d Q qp _ _ old.1 old.2 fresh.1 fresh.2

private theorem earned (C:Family G)(Q:ℝ)(d k:ℕ){m i:ℕ}(mi:m ≤ i):
    Many.envelope C m d k Q i = radius C Q (2*k) d m i (C.path.levels.clock.hatBeta i):=by
  have good:0 < C.path.levels.clock.hatBeta i:=zero_lt_one.trans (C.path.levels.fits.delayed i)
  unfold Many.envelope Many.west
  rw [Many.rust_above mi,one_mul]
  change _ / _= (cue (C.path.levels.clock.hatBeta i))^(2*k)/_
  rw [pow_mul,cue,inv_pow,Real.sq_sqrt good.le,inv_pow]

theorem filed (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(k:ℕ){ε:ℝ}(ep:0 < ε):
    ∀ᶠ i:ℕ in atTop,∀m:ℕ,m ≤ i →∀(d:ℕ)(Q:ℝ),0 < Q →
      |Real.log (Many.envelope R.family m d k Q i/Many.envelope R.family m d k Q (i+1))|
        ≤ ε*(R.family.path.levels.budget i).B:=by
  filter_upwards [band R simple slow (2*k) ep] with i price m mi d Q qp
  rw [earned _ _ _ _ mi,earned _ _ _ _ (mi.trans (Nat.le_succ i))]
  have b:=R.family.path.levels.fits.delayed i
  have t:=R.family.path.levels.fits.delayed (i+1)
  exact price m mi d Q qp _ _ (by linarith only [b]) (by linarith only [b]) (by linarith only [t]) (by linarith only [t])

end YM.Integration.WilsonMarkedUltravioletSourceRatios
