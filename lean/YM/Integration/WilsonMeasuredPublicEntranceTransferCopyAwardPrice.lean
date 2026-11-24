import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyFlockSalary
/-! The exact terminal money of the height-zero copied Wilson field at its fixed receiver. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyAwardPrice
open Function Filter Real Lattice RG Wilson Source Labels MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign

open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "S" => R.family.S
local notation "σ" => G.slopeConstant

open PhysicalNext.Repeat.Legato.Bandage
open WilsonOriginalPublicTrialPhaseRace (wage)
local notation "Wunit" => WilsonOriginalPublicTrialPhaseRay.unit
local notation "beam" => WilsonOriginalPublicTrialPhaseRay.weight

include simple in
theorem original (D:ℝ) (u q:ℕ) :
    ∀ᶠ c:ℕ in atTop, ∀ f:ℕ,c≤f → H f≤2*H c → ∀ B:ℝ,1≤B →
      7*(H (c+1))^2*B≤Real.exp (H c/(10*σ)) →
      let r:=(1+8*(bling R.family.path.levels c+2)*B)/min 1 (renal R.family.path.levels c)
      let w:=beam (S) r c u
      let a:=w*wage (S) r c u
      Real.exp (D+a+a+2)/w≤1/(H f)^q:=by
  let D₀:=Real.exp (D+Wunit⁻¹+Wunit⁻¹+2)
  have late:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [WilsonMeasuredPublicEntranceTransferCopyFlockSalary.original R simple u (q+1),
    late.eventually_ge_atTop D₀] with c terminal onset f cf hot B start incoming
  let g:=(7*(H (c+1))^2*B)⁻¹
  let b:=bling R.family.path.levels c
  let r:=(1+8*(b+2)*B)/min 1 (renal R.family.path.levels c)
  have h1:1≤H (c+1):=(R.family.path.levels.fits.delayed (c+1)).le
  have h0:=zero_lt_one.trans_le h1
  have B0:=zero_lt_one.trans_le start
  have g0:0<g:=by dsimp only [g];positivity
  have gproof:g⁻¹≤Real.exp (H c/(10*σ)):=by simpa only [g,inv_inv] using incoming
  have b1:1≤b:=Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _)
  have rent:renal R.family.path.levels c=(H (c+1)^2)⁻¹:=by
    unfold renal PhysicalNext.Repeat.Mallow.probe
    rw [Real.rpow_neg h0.le];norm_num
  have quad:1≤H (c+1)^2:=one_le_pow₀ h1
  have low:min 1 (renal R.family.path.levels c)=(H (c+1)^2)⁻¹:=by
    rw [rent,min_eq_right ((inv_le_one₀ (by positivity)).mpr quad)]
  have rd:r=(1+8*(b+2)*B)*(H (c+1))^2:=by dsimp only [r];rw [low,div_inv_eq_mul]
  have r0:0<r:=by rw [rd];positivity
  have rcap:r≤4*b*g⁻¹:=by
    rw [rd,show g⁻¹=7*(H (c+1))^2*B by simp [g]]
    have bb:1+8*(b+2)*B≤28*b*B:=by nlinarith only [start,b1,mul_nonneg (sub_nonneg.mpr b1) B0.le]
    have take:=mul_le_mul_of_nonneg_right bb (sq_nonneg (H (c+1)))
    nlinarith only [take]
  have smaller:(beam (S) r c u)⁻¹≤(beam (S) (4*b*g⁻¹) c u)⁻¹:=by
    simp only [WilsonOriginalPublicTrialPhaseRay.weight,inv_inv,WilsonOriginalPublicTrialPhaseRace.wage]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left rcap (Real.rpow_nonneg
      (div_nonneg ((S).a_pos _).le ((S).a_pos _).le) _)) WilsonOriginalPublicTrialPhaseRay.unit_pos.le
  have cash:=smaller.trans (terminal f hot g g0 gproof)
  have fit:0<wage (S) r c u:=mul_pos (Real.rpow_pos_of_pos (div_pos ((S).a_pos _) ((S).a_pos _)) _) r0
  have aid:beam (S) r c u*wage (S) r c u=Wunit⁻¹:=by
    unfold WilsonOriginalPublicTrialPhaseRay.weight
    field_simp [fit.ne',WilsonOriginalPublicTrialPhaseRay.unit_pos.ne']
  have f0:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have bought:D₀≤H f:=onset.trans (WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le cf)
  change Real.exp (D+(beam (S) r c u*wage (S) r c u)+(beam (S) r c u*wage (S) r c u)+2) / _ ≤ _
  rw [aid,div_eq_mul_inv]
  calc
    _≤H f*(1/(H f)^(q+1)):=mul_le_mul bought cash
      (inv_nonneg.mpr (WilsonOriginalPublicTrialPhaseRay.weight_pos _ r0 _ _).le) f0.le
    _=1/(H f)^q:=by rw [pow_succ];field_simp

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyAwardPrice
