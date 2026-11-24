import YM.Integration.WilsonVacuumPreResetPrecursorReserve
import YM.Integration.WilsonVacuumPreResetLiftedClock
import YM.Integration.WilsonVacuumPreResetRenderCalendar

/-! The actual reset budget has room for both the original kinetic widths
and the covering widths. All purchases precede both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetModelWidths
open RG01Estimate
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Laplace Pressure ConnectedActivityE6 Coat Evoc Push Deck
open Censor Censor.Toft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open FullVolume WilsonLimitConstruction RG01Estimate.Chart
open Comparison.Density Comparison.Density.Render
open WilsonVacuumPreResetRenderReserve WilsonVacuumPreResetCurvatureReserve WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
variable {G:Gauge}

private theorem coefficients (d:ℕ):1≤FundedCloverWidthMoment.coefficient d:=by
  open FundedCloverWidthMoment in
    have squares1:1≤∑' n,FundedCloverWidthMoment.square n:=by
      simpa [FundedCloverWidthMoment.square] using squares.le_tsum 0 (fun n _=>show 0≤ FundedCloverWidthMoment.square n by unfold FundedCloverWidthMoment.square;positivity)
    have fact:(1:ℝ)≤(d+2).factorial:=by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    have power:(1:ℝ)≤(4:ℝ)^(d+2):=one_le_pow₀ (by norm_num)
    unfold coefficient
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) fact) power) squares1

private theorem headroom (T:RG.Stage){x:ℝ}(hx:1≤2*Real.log x):
    Real.exp (81*(T.supportExponent+6))≤WilsonVacuumPreResetRenderReserve.amount G T 0 x:=by
  let A:=T.supportExponent+6
  let d:=Wages.grade 0 T.power T.order
  let L:ℝ:=(1+|Frame.cost (Time.probe T)|)*(1+|factor|)*(1+|Comparison.Density.Render.bloom G (Time.probe T)|)
  let P:ℝ:=(1+|Wages.startup G 0 T.power T.order|)*Real.exp (A*(1+2*(0:ℝ)))*
    FundedCloverWidthMoment.coefficient d*(2*Real.log x)^(d+2)
  have one (z:ℝ):1≤1+|z|:=by linarith [abs_nonneg z]
  have ll:1≤L:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one _) (one _)) (one _)
  have e:0≤A*(1+2*(0:ℝ)):=by have:=T.price_pos;dsimp [A];positivity
  have pp:1≤P:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one _) (Real.one_le_exp e)) (coefficients _)) (one_le_pow₀ hx)
  calc
    _≤L*Real.exp (81*A):=le_mul_of_one_le_left (Real.exp_pos _).le ll
    _≤L*Real.exp (81*A)*P:=le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans ll) (Real.exp_pos _).le) pp
    _=WilsonVacuumPreResetRenderReserve.amount G T 0 x:=by
      dsimp [L,P,A,d,WilsonVacuumPreResetRenderReserve.amount,WilsonVacuumPreResetRenderReserve.base]
      ring

theorem original (R:Run G)(simple:G.Simple)(render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)
    (curves:WilsonVacuumPreResetPrecursorReserve.Issued R.kit):
    let V:=R.family.path.levels
    ∀ᶠm:ℕ in atTop,let B:=V.budget m
      4≤B.B ∧ preExponent B/B.B≤(V.params m).width/4 ∧
      ∀σ:ℝ,0<σ→σ⁻¹≤zz V (m+1)→preExponent B/B.B≤σ/4:=by
  intro V
  have growth:=Real.tendsto_log_atTop.comp (RG01.Physical.hats simple V)
  filter_upwards [WilsonVacuumPreResetRenderCalendar.original R render simple 0 (η:=1) zero_lt_one,
    growth.eventually_ge_atTop 3] with m paid big
  intro B
  let T:=V.params m
  let x:=Real.log (V.clock.hatBeta m)
  let b:=(B.B:ℝ)
  have xp:3≤x:=big
  have bp:0<b:=Nat.cast_pos.mpr B.B_pos
  have block:x^2≤b:=Nat.le_ceil _
  have large:(4:ℝ)≤b:=by nlinarith [sq_nonneg (x-2)]
  have log:81*(T.supportExponent+6)≤x:=by
    apply (Real.le_log_iff_exp_le (zero_lt_one.trans (V.fits.delayed m))).2
    exact (headroom (G:=G) T paid.1).trans (by simpa using paid.2.2 0 le_rfl)
  have e:preExponent B=T.supportExponent+3:=rfl
  have start:8*preExponent B≤x:=by rw [e];nlinarith only [log,T.price_pos]
  have nums:4*|T.supportExponent+9|/T.width≤WilsonVacuumPreResetCurvatureReserve.income G T T:=by
    have a (k:ℕ):0≤anchor T k:=by unfold anchor;positivity
    unfold WilsonVacuumPreResetCurvatureReserve.income
    linarith only [mul_nonneg (a lowCount) (abs_nonneg (head G T T)),mul_nonneg (a (octave 3)) (abs_nonneg (arm G T T 3)),
      mul_nonneg (a (octave 4)) (abs_nonneg (arm G T T 4))]
  have cov:(4*|T.supportExponent+9|)/T.width≤x:=nums.trans (curves m)
  have co:4*preExponent B≤x*T.width:=by have h:=(div_le_iff₀ T.width_pos).1 cov;rw [e];linarith [le_abs_self (T.supportExponent+9)]
  have xb:x≤b:=by nlinarith only [block,xp,sq_nonneg (x-2)]
  change (4:ℝ)≤(B.B:ℝ) at large
  refine ⟨by exact_mod_cast large,?_,?_⟩
  · apply (div_le_div_iff₀ bp (by norm_num : (0:ℝ)<4)).2
    have h:=co.trans (mul_le_mul_of_nonneg_right xb T.width_pos.le)
    change preExponent B*4≤T.width*b
    linarith only [h]
  intro σ hs paidσ
  have z:σ⁻¹≤2*x:=paidσ.trans paid.2.1
  have nn:0≤preExponent B:=by rw [e];linarith [T.price_pos]
  have expense:4*preExponent B*σ⁻¹≤b:=calc
    _≤4*preExponent B*(2*x):=mul_le_mul_of_nonneg_left z (by positivity)
    _≤x^2:=by nlinarith only [mul_le_mul_of_nonneg_right start (show 0≤x by linarith)]
    _≤_:=block
  have mult:=mul_le_mul_of_nonneg_left expense hs.le
  have unit:σ*(4*preExponent B*σ⁻¹)=4*preExponent B:=by field_simp
  apply (div_le_div_iff₀ bp (by norm_num : (0:ℝ)<4)).2
  rw [unit] at mult
  change preExponent B*4≤σ*b
  linarith only [mult]

end YM.Integration.WilsonVacuumPreResetModelWidths
