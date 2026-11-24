import YM.Integration.WilsonMacroscopicRichReportingRate
import YM.Integration.WilsonReportHarvestPlatedLayout

/-! The original rich reporting port and its actual finite-temperature interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactRichPortClock
open Filter Set Finset Lattice RG Wilson RG16 RG16.Literal Precision Pert.Asymptotics PhysicalNext.Repeat.Legato RG05Readout
open OPE OPE.Log Trace.Pilot Real
open private square from YM.Integration.WilsonLocalCompactClock
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)(simple:G.Simple)
include simple
local notation "S" => R.family.S
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem dates (L B:ℝ)(lp:0<L)(bp:0<B)
    (pace:∀m,(((S).block m).val:ℝ)≤log (RG16.Lambda A m)):
    ∀ᶠ m:ℕ in atTop,let b:=port R.family L B lp m+1
    (b < m) ∧ WilsonCloseCaptureDate.level S (Upper R.family L B m*(S).a m)=b ∧
    ((m-b:ℕ):ℝ)≤G.slopeConstant⁻¹*β m ∧ 4≤β m ∧
      ∀ i : ℕ, b ≤ i → i ≤ m → β m / 2 ≤ β i:=by
  let a:=port R.family L B lp
  have half:=(port_height R.family simple L B lp bp pace).2.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  have grows:=port_grows R.family simple L B lp
  have cp:=G.slopeConstant_pos simple
  have next:=port_small R.family simple L B lp bp
  filter_upwards [half,next,inner_bound R.family simple L B lp,(S).divergent.eventually_gt_atTop 0,
    ((S).divergent.comp grows).eventually_ge_atTop 0,(Next.Rank.Station.hat_rate A simple).eventually_ge_atTop 4]
    with m response earlier inner positive prior high
  intro b
  have hit:=WilsonCloseCaptureDate.identifies (S) (step_bound R.family L B lp m) inner
  change 0≤(S).scale (a m) at prior
  have grow:=Many.tall (C:=R.family) (a m) b (Nat.le_succ (a m))
  have h:0≤(S).scale b:=by linarith only [prior,grow,show (0:ℝ)≤((b-a m:ℕ):ℝ) by positivity]
  have tall:=Many.tall (C:=R.family) b m earlier.le
  have walk:(m-b:ℕ)≤(S).scale m:=by linarith only [tall,h]
  have money:(S).scale m≤G.slopeConstant⁻¹*β m:=by
    rw [←div_eq_inv_mul];apply (le_div_iff₀ cp).2
    change (S).scale m*G.slopeConstant≤(A).clock.bar+G.slopeConstant*(S).scale m
    linarith only [(A).clock.bar_pos]
  refine ⟨earlier,hit,walk.trans money,high,?_⟩
  intro i bi _
  have first:(1/2:ℝ)*(S).scale m≤(S).scale (a m):=(le_div_iff₀ positive).mp response.le
  have low:β m/2≤β (a m):=by
    dsimp only [Calendar.hatBeta]
    nlinarith only [mul_le_mul_of_nonneg_left first cp.le,(A).clock.bar_pos]
  exact low.trans (WilsonStartup.Timing.hat_mono A cp.le ((Nat.le_succ (a m)).trans bi))

theorem prices (L B:ℝ)(lp:0<L)(bp:0<B)
    (pace:∀m,(((S).block m).val:ℝ)≤log (RG16.Lambda A m)):
    ∀ᶠ j:ℕ in atTop,let b:=port R.family L B lp j+1
    b≤j ∧ ∀N,j≤N→∀per,let g:=regulatorRun R.family N per
      ((j-b:ℕ):ℝ)≤G.slopeConstant⁻¹*β j ∧ β j*g j^2≤2 ∧
      ∀ i : ℕ, b ≤ i → i ≤ j → g i ≤ 1 ∧ g i ≤ 3*g j:=by
  filter_upwards [dates R simple L B lp bp pace] with j row b
  refine ⟨row.1.le,?_⟩
  have clock:=row.2.2
  intro N top per g
  let base:=R.family.path.β N per j
  have bpair:=(R.makes.wilson.represents N per j top).band
  change β j/2≤base ∧ base≤2*β j at bpair
  have high:=clock.2.1
  have b0:0<base:=by linarith only [bpair.1,high]
  have conv:g j^2=1/base:=square R top
  refine ⟨clock.1,?_,fun i bi ij=>?_⟩
  · rw [conv,one_div,←div_eq_mul_inv];exact (div_le_iff₀ b0).2 (by linarith only [bpair.1])
  · let a:=R.family.path.β N per i
    have pair:=(R.makes.wilson.represents N per i (ij.trans top)).band
    change β i/2≤a ∧ a≤2*β i at pair
    have gap:=clock.2.2 i bi ij
    have one:1≤a:=by linarith only [pair.1,gap,high]
    have ap:0<a:=zero_lt_one.trans_le one
    have comp:base≤9*a:=by linarith only [gap,pair.1,bpair.2,high]
    have g0 k:0≤g k:=inv_nonneg.mpr (Real.sqrt_nonneg _)
    have shift:g i^2=1/a:=square R (ij.trans top)
    refine ⟨(sq_le_sq₀ (g0 i) zero_le_one).1 ?_,(sq_le_sq₀ (g0 i) (mul_nonneg (by norm_num) (g0 j))).1 ?_⟩
    · rw [shift,one_pow];exact (div_le_one ap).2 one
    · rw [mul_pow,shift,conv,show (3:ℝ)^2*(1/base)=9/base by ring]
      exact (div_le_div_iff₀ ap b0).2 (by simpa only [one_mul] using comp)

end YM.Integration.WilsonLocalCompactRichPortClock
