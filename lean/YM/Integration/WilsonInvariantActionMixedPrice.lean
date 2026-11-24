import YM.Integration.WilsonInvariantActionMixedInterval
import YM.Integration.WilsonRegisteredSoftCovariance

/-! Pay the measured grade-four mixed row through the entire close
interval at the true reporting coupling, before every upper cutoff and
period, with the two independent submitted label norms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonInvariantActionMixedPrice
open Filter Finset Set MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics WilsonLimitConstruction
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonInvariantActionMixedMaterial WilsonInvariantActionMixedInterval Next.UVStress
open private currency from YM.Integration.WilsonDegreeFourFundedTail
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G) (simple:G.Simple)
    {ρ:ℝ} {P:Campaign R} (W:Campaign.Pillars R P) (funded:FundedOriginalProperties.{u} simple ρ W)
local notation "β" => R.family.path.levels.clock.hatBeta

include simple funded in
private theorem purchase {m N per:ℕ} (v:R.family.label 4) (e:ℕ) {M:ℝ} (mp:0≤M)
    (paid:quota R.family 4 m N per v≤R.family.S.a m^4*(β m^e*M)):
    budget v m N per≤β m^(e+1)*M:=by
  have bp:0≤β m:=zero_le_one.trans (R.family.path.levels.fits.delayed m).le
  have ap:0<R.family.S.a m^4:=pow_pos (R.family.S.a_pos m) _
  have scaled:(R.family.S.a m^4)⁻¹*quota R.family 4 m N per v≤β m^e*M:=by
    calc
      _≤(R.family.S.a m^4)⁻¹*(R.family.S.a m^4*(β m^e*M)):=mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr ap.le)
      _=_:=inv_mul_cancel_left₀ ap.ne' _
  have col: (R.family.path.levels.params m).columns≤β m:=funded.2.1.logBudget.money.present m
  calc
    budget v m N per≤(R.family.path.levels.params m).columns*(β m^e*M):=
      mul_le_mul_of_nonneg_left scaled (zero_le_one.trans (R.family.path.levels.params m).columns_ge)
    _≤β m*(β m^e*M):=mul_le_mul_of_nonneg_right col (mul_nonneg (pow_nonneg bp _) mp)
    _=_:=by rw [pow_succ];ring

include simple W funded in
theorem purchased (pace:WilsonWindowReportingPace.Slow R.kit)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (d:I→ℕ) {B:ℕ} (bp:0<B) (ev ew q grade:ℕ)
    (precision:q+2*(ev+ew+2)+7≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠr:ℝ in trail,let b:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
      let j:=WilsonCloseCaptureDate.level R.family.S r
      j≤b ∧ ∀k:ℕ,j≤k→∀live:k≤b,∀N:ℕ,∀cut:b<N,∀per,
      ∀(T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
        (o:∀i,i<b→I→Site (R.family.side (i+1) per)) (_birth:R.family.ref 4≤b)
        (x y:Site (R.family.side b per)) (v w:R.family.label 4) (Mv Mw:ℝ),0≤Mv→0≤Mw→
      quota R.family 4 b N per v ≤ R.family.S.a b^4*(β b^ev*Mv) →
      quota R.family 4 b N per w ≤ R.family.S.a b^4*(β b^ew*Mw) →
      ∀(cohort:Set ℕ)(η χ:ℂ→L[ℝ]ℝ),
      let A:=fun U=>η (primary R.makes cut.le v x U)
      let H:=fun U=>χ (earlier R.makes cut.le w y cohort U)
      let g:=regulatorRun R.family N per b
      |pair (retained R cut grade d T o live) A H-pair (physicalMean R N per b) A H|≤
        ε*g^q*(‖η‖*‖χ‖)*(Mv*Mw):=by
  let f:=ev+ew+2
  let δ:=min 1 (ε/(4*(2:ℝ)^f))
  have dp:0<δ:=lt_min (by norm_num) (div_pos ep (by positivity))
  have small:δ≤1:=min_le_left _ _
  have buy:4*δ*(2:ℝ)^f≤ε:=by
    have ready:δ≤ε/(4*(2:ℝ)^f):=min_le_right _ _
    calc
      _=δ*(4*(2:ℝ)^f):=by ring
      _≤ε:=(le_div_iff₀ (by positivity : 0<4*(2:ℝ)^f)).mp ready
  have grows:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp
    (WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B bp)
  filter_upwards [integrated R simple pace marks fees d bp (q+2*f) grade precision dp,grows.eventually_ge_atTop 2] with r cash warm
  intro b j
  refine ⟨cash.1,?_⟩
  intro k date live N cut per T o birth x y v w Mv Mw vp wp billV billW cohort η χ A H g
  have paid:=cash.2 k date live N cut per T o birth x y v w cohort η χ
  let τ:=δ*g^(q+2*f)
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have second:β b*g^2≤2:=by simpa only [pow_one,pow_zero,mul_one,Nat.zero_add,Nat.mul_one] using currency R cut.le 1 0
  change (2:ℝ)≤β b at warm
  have gs:g^2≤1:=by nlinarith only [mul_le_mul_of_nonneg_right warm (sq_nonneg g),second]
  have gl:g≤1:=by nlinarith only [gs,sq_nonneg (g-1)]
  have tn:0≤τ:=mul_nonneg dp.le (pow_nonneg gp _)
  have tc:τ≤1:=(mul_le_mul_of_nonneg_right small (pow_nonneg gp _)).trans (by simpa only [one_mul] using (pow_le_one₀ gp gl (n:=q+2*f)))
  have approx:3*τ+τ^2≤4*τ:=by nlinarith only [mul_le_mul_of_nonneg_left tc tn]
  have costV:=purchase R simple W funded v ev vp billV
  have costW:=purchase R simple W funded w ew wp billW
  have zeroV:0≤budget v b N per:=(norm_nonneg _).trans ((filed R.makes cut.le birth v x cohort).1.2.2 1)
  have zeroW:0≤budget w b N per:=(norm_nonneg _).trans ((filed R.makes cut.le birth w y cohort).2.2.2 1)
  have price:=currency R (per:=per) cut.le f q
  let norm:=(‖η‖*‖χ‖)*(Mv*Mw)
  have nn:0≤norm:=mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg vp wp)
  calc
    _≤(3*τ+τ^2)*(‖η‖*budget v b N per)*(‖χ‖*budget w b N per):=paid
    _≤(4*τ)*(‖η‖*(β b^(ev+1)*Mv))*(‖χ‖*(β b^(ew+1)*Mw)):=by gcongr
    _=(4*δ)*(β b^f*g^(q+2*f))*norm:=by
      have eq:f=(ev+1)+(ew+1):=by dsimp only [f];omega
      dsimp only [τ,norm];rw [show β b^f=β b^(ev+1)*β b^(ew+1) by rw [eq,pow_add]]
      ring
    _≤(4*δ)*((2:ℝ)^f*g^q)*norm:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left price (by positivity)) nn
    _≤ε*g^q*(‖η‖*‖χ‖)*(Mv*Mw):=by
      simpa only [norm,mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right buy (pow_nonneg gp q)) nn

end YM.Integration.WilsonInvariantActionMixedPrice
