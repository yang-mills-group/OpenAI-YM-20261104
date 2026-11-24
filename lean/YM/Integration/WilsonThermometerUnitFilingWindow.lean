import YM.Integration.WilsonThermometerUnitFilingFeed
import YM.Integration.WilsonCloseCaptureDate
import YM.Pert.Asymptotics.RawAxis

/-! The stable unit feed's short interval, chosen on the original slow
calendar before either the cutoff or the period is read. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWindow
open Function Filter Set Lattice RG Wilson Pert.Asymptotics RG12 PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "σ" => R.family.S.scale
local notation "H" => R.family.path.levels.clock.hatBeta

private theorem heights : StrictMono (σ) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [R.family.S.scale_succ]
  have hi := R.family.S.block_large i
  have hn : (1:ℕ)<(R.family.S.block i).val := by omega
  linarith only [Real.log_pos (show (1:ℝ)<((R.family.S.block i).val:ℝ) by exact_mod_cast hn)]

private theorem affine (b i : ℕ) :
    H b-H i=G.slopeConstant*(σ b-σ i) := by
  dsimp [Calendar.hatBeta]
  ring

private theorem subdued (D : ℝ) (pos : 0 ≤ D) : ∀ᶠ x : ℝ in atTop,D*Real.log x ≤ x/2 := by
  have positive : 0<2*(1+D) := by linarith
  have lim := Real.isLittleO_log_id_atTop.bound (inv_pos.mpr positive)
  filter_upwards [lim,eventually_ge_atTop (1:ℝ)] with x he one
  change ‖Real.log x‖ ≤ (2*(1+D))⁻¹*‖x‖ at he
  have hlog := Real.log_nonneg one
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_pos (zero_lt_one.trans_le one),inv_mul_eq_div] at he
  nlinarith only [(le_div_iff₀ positive).mp he,hlog]

include simple in
/-- One earlier date works on every regulated period and every larger cutoff.
The width is stated in the actual measured coupling of that cutoff. -/
theorem original (slow : WilsonWindowReportingPace.Slow R.kit) (u D : ℕ) :
    ∀ᶠ b : ℕ in atTop, ∃ stop : ℕ, u ≤ stop ∧ stop ≤ b ∧ ∀ N p : ℕ, b ≤ N →
      let g:=regulatorRun R.family N p b
      0<g ∧ g ≤ 1 ∧ D * Real.log g⁻¹ ≤ σ b - σ stop ∧ σ b - σ stop ≤ 4*(D+1)*Real.log g⁻¹ := by
  have slope := Gauge.slopeConstant_pos simple
  have grow := Next.Rank.Station.hat_rate R.family.path.levels simple
  have pref : 0 ≤ G.slopeConstant*(D:ℝ) := mul_nonneg slope.le (Nat.cast_nonneg _)
  filter_upwards [grow.eventually_ge_atTop 4,grow.eventually_ge_atTop (2*H u),
    grow.eventually (subdued _ pref)] with b four room toll
  have high : 0 < H b := by linarith only [four]
  have hl : 0 ≤ Real.log (H b) := Real.log_nonneg (by linarith only [four])
  have nonnegspan := mul_nonneg (Nat.cast_nonneg D) hl
  let x := σ b-D*Real.log (H b)
  have ux : σ u ≤ x := by
    dsimp [x]
    apply (mul_le_mul_iff_right₀ slope).mp
    nlinarith only [affine R b u,toll,room]
  have sx : 0 ≤ x := by
    have hu := (heights R).monotone (Nat.zero_le u)
    rw [R.family.S.scale_zero] at hu
    exact hu.trans ux
  have nonempty : ∃ n, x < σ n := (R.family.S.divergent.eventually_gt_atTop x).exists
  let n := Nat.find nonempty
  have later : x<σ n := Nat.find_spec nonempty
  have nz : n≠0 := by
    intro such
    rw [such,R.family.S.scale_zero] at later
    linarith
  let i := n-1
  have near : i+1=n := by omega
  have earlier : σ i ≤ x := not_lt.mp (Nat.find_min nonempty (show i<n by omega))
  have ui : u ≤ i := by
    by_contra! h
    have ineq := (heights R).monotone (show n ≤ u by omega)
    linarith
  have ib : i ≤ b := by
    by_contra! h
    have ineq := heights R h
    dsimp [x] at earlier
    linarith
  have hm : H i ≤ H b := by
    nlinarith only [affine R b i,mul_nonneg slope.le (sub_nonneg.mpr ((heights R).monotone ib))]
  have priced := WilsonFundedMeasuredWindow.paced R slow i
  change ((R.family.S.block i).val:ℝ) ≤ Real.log (H i) at priced
  have hi : 0 < H i := zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have block : ((R.family.S.block i).val:ℝ) ≤ H b :=
    priced.trans ((Real.log_le_sub_one_of_pos hi).trans (by linarith only [hm]))
  have logblock := Real.log_le_log (show (0:ℝ)<((R.family.S.block i).val:ℝ) by exact_mod_cast (R.family.S.block i).property) block
  rw [←near,R.family.S.scale_succ] at later
  have below : D*Real.log (H b) ≤ σ b-σ i := by linarith only [earlier]
  have above : σ b-σ i ≤ (D+1)*Real.log (H b) := by dsimp [x] at later; nlinarith only [later,logblock]
  refine ⟨i,ui,ib,?_⟩
  intro N p cutoff g
  let beta := R.family.path.β N p b
  have band := (R.makes.wilson.represents N p b cutoff).band
  change H b/2 ≤ beta ∧ beta ≤ 2*H b at band
  have betaOne : 1 ≤ beta := by linarith only [four,band.1]
  have bp := zero_lt_one.trans_le betaOne
  have sqrtp := Real.sqrt_pos.mpr bp
  have lbg : Real.log g⁻¹=Real.log beta/2 := by
    change Real.log ((Real.sqrt beta)⁻¹)⁻¹=_
    rw [inv_inv,Real.log_sqrt bp.le]
  have lower : Real.log beta/2 ≤ Real.log (H b) := by
    have h := Real.log_le_log bp (show beta ≤ (H b)^2 by nlinarith only [four,band.2])
    rw [Real.log_pow] at h
    norm_num1 at h
    linarith only [h]
  have upper : Real.log (H b) ≤ 2*Real.log beta := by
    have h := Real.log_le_log high (show H b ≤ beta^2 by nlinarith only [four,band.1,sq_nonneg (beta-2)])
    rw [Real.log_pow] at h
    norm_num1 at h
    linarith only [h]
  have gp : 0<g := inv_pos.mpr sqrtp
  have gs : g ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr betaOne)
  refine ⟨gp,gs,?_,?_⟩
  · rw [lbg]
    exact (mul_le_mul_of_nonneg_left lower (Nat.cast_nonneg D)).trans below
  · rw [lbg]
    exact above.trans (by nlinarith only [mul_le_mul_of_nonneg_left upper (show (0:ℝ) ≤ D+1 by positivity)])
end YM.Integration.WilsonThermometerUnitFilingWindow
