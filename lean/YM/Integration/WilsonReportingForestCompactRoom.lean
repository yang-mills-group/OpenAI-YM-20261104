import YM.Integration.WilsonReportingForestMovingCount

/-! For fixed registered footprints the plaquette filling costs a quadratic
polynomial in the true *adjacent block*. Its slow-clock logarithm leaves the
physical angular cutoff strictly inside the smaller rescaled compact room. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestCompactRoom
open Filter Lattice Wilson RG RG16 OPE.Therm PhysicalNext.Repeat.Legato Next.Scheduling
open WilsonPhysicalLocalPlaquetteForest WilsonReportingForestBlocks
open scoped Topology Classical
variable {G:Gauge}

private def fee (H:ℕ):ℝ:=(16*(H:ℝ)+225)*4*((H:ℝ)+14)*Fintype.card PlaqAxes

private theorem quadratic (H D L:ℕ) (hd:D≤H) :
    area (extent D L) L≤fee H*(1+(L:ℝ))^2:=by
  have le:(D:ℝ)≤H:=by exact_mod_cast hd
  have h0:0≤(H:ℝ):=H.cast_nonneg
  have l0:0≤(L:ℝ):=L.cast_nonneg
  have hl:=mul_nonneg h0 l0
  have arm:(lanes (extent D L) L:ℝ)≤(16*(H:ℝ)+225)*(1+(L:ℝ)):=by
    unfold lanes extent;push_cast;nlinarith only [le,hl,l0]
  have span:(radius (extent D L) L:ℝ)≤((H:ℝ)+14)*(1+(L:ℝ)):=by
    unfold radius extent;push_cast;nlinarith only [le,hl,l0]
  unfold area
  calc
    _≤((16*(H:ℝ)+225)*(1+(L:ℝ)))*(4*(((H:ℝ)+14)*(1+(L:ℝ)))*Fintype.card PlaqAxes):=by gcongr
    _=fee H*(1+(L:ℝ))^2:=by dsimp [fee];ring

private theorem grows (C:ℝ) (cp:0≤C) : ∀ᶠ s:ℝ in atTop,
    C*(1+Real.log (2+s))^2≤Real.sqrt s := by
  have h:0<1/(9*(C+1)):=by positivity
  have loan:=(isLittleO_log_rpow_rpow_atTop (2:ℝ) (show 0<(1/2:ℝ) by norm_num)).def h
  filter_upwards [loan,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2:ℝ)] with s rate high big
  have sp:0<s:=by linarith
  have sq:2+s≤ s^2:=by nlinarith only [mul_nonneg (sub_nonneg.mpr big) (show 0≤ s+1 by positivity)]
  have log2:=Real.log_le_log (show 0<2+s by positivity) sq
  rw [Real.log_pow] at log2
  have window:1+Real.log (2+s)≤3*Real.log s:=by norm_num at log2;linarith only [log2,high]
  have l0:0≤Real.log (2+s):=Real.log_nonneg (by linarith)
  have r:(Real.log s)^2≤1/(9*(C+1))*Real.sqrt s:=by
    change ‖(Real.log s)^(2:ℝ)‖≤1/(9*(C+1))*‖s^(1/2:ℝ)‖ at rate
    simpa only [Real.rpow_ofNat,←Real.sqrt_eq_rpow,Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] using rate
  calc
    _≤(C+1)*(3*Real.log s)^2:=by gcongr;linarith
    _=9*(C+1)*(Real.log s)^2:=by ring
    _≤9*(C+1)*(1/(9*(C+1))*Real.sqrt s):=mul_le_mul_of_nonneg_left r (by positivity)
    _=Real.sqrt s:=by field_simp

/-- The coefficient in front of the original hat-g log^(5/4) angular
cut may be the true quadrant-chart price times the full adjacent-block area. -/
theorem original (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤
    Real.log (Lambda R.family.path.levels m)) (H:ℕ) (K:ℝ) (kp:0≤K) :
    ∀ᶠ m:ℕ in atTop, ∀N,m<N→∀per D,D≤H→
    let A:=R.family.path.levels
    let L:=(A.clock.op m per).ratio.count.val
    let b:=A.clock.hatBeta (m+1)
    let s:=Real.log b
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    K*area (extent D L) L*(A.clock.hatCoupling (m+1)*s*Real.sqrt (Real.sqrt s))
      ≤g*(s^2/32) := by
  let A:=R.family.path.levels
  have fp:0≤fee H:=by dsimp [fee];positivity
  have more:=Real.tendsto_log_atTop.comp ((Next.Rank.Station.hat_rate A simple).comp (tendsto_add_atTop_nat 1))
  filter_upwards [more.eventually (grows (64*K*fee H) (by positivity)),more.eventually_ge_atTop (1:ℝ)] with m price large N live per D hd
  dsimp only
  let L:=(A.clock.op m per).ratio.count.val
  let b:=A.clock.hatBeta (m+1)
  let s:=Real.log b
  let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
  let gh:=A.clock.hatCoupling (m+1)
  let t:=Real.sqrt s
  let u:=Real.sqrt t
  have s1:1≤ s:=large
  have u0:0≤u:=Real.sqrt_nonneg _
  have t0:0≤t:=Real.sqrt_nonneg _
  have t1:1≤t:=by simpa [t] using Real.sqrt_le_sqrt s1
  have u1:1≤u:=by simpa [u] using Real.sqrt_le_sqrt t1
  have t2:t^2=s:=Real.sq_sqrt (zero_le_one.trans s1)
  have u2:u^2=t:=Real.sq_sqrt t0
  have ut:u≤t:=by nlinarith only [u2,mul_nonneg u0 (sub_nonneg.mpr u1)]
  have lp:(L:ℝ)≤Real.log (2+s):=
    (slow m).trans (Real.log_le_log (Literal.lambda_pos R.family m)
      ((Literal.lambda_mono R.family simple).monotone (Nat.le_succ m)))
  have work:64*K*area (extent D L) L≤t:=calc
    _≤64*K*(fee H*(1+(L:ℝ))^2):=mul_le_mul_of_nonneg_left (quadratic H D L hd) (by positivity)
    _≤64*K*fee H*(1+Real.log (2+s))^2:=by rw [←mul_assoc];gcongr
    _≤t:=price
  have b0:0<b:=zero_lt_one.trans (A.fits.delayed _)
  have beta:b/2≤R.family.path.β N per (m+1):=(R.makes.wilson.represents N per (m+1) live).band.1
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (by linarith only [b0,beta]))
  have half:gh/2≤g:=(band_gap b _ b0 (trial_in (R.makes.wilson.represents N per (m+1) live).band)).1
  have charge:0≤K*area (extent D L) L:=by unfold area;positivity
  have cost:(64*K*area (extent D L) L)*u≤ s:=calc
    _≤t*t:=mul_le_mul work ut u0 t0
    _=s:=by rw [←sq,t2]
  have bound:gh≤2*g:=by linarith only [half]
  change K*area (extent D L) L*(gh*s*u)≤g*(s^2/32)
  calc
    _≤K*area (extent D L) L*((2*g)*s*u):=by gcongr
    _=(g*s/32)*((64*K*area (extent D L) L)*u):=by ring
    _≤(g*s/32)*s:=mul_le_mul_of_nonneg_left cost (by positivity)
    _=g*(s^2/32):=by ring

end YM.Integration.WilsonReportingForestCompactRoom
