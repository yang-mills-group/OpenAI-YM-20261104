import YM.Integration.WilsonMovingForkStoppedHeat
import YM.Integration.WilsonAddressedCollarWindow

/-! Scale and optical-width prices from the true fired stop through the
true first fine reporting cut on the shared original Wilson run. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonMovingForkOpticalStops
open Function Filter Set Lattice RG Wilson Org PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open MS MS.Land Trace.Pilot Next.Rank Next.Rank.Station MergeProof.East
open Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale
local notation "a" => R.family.S.a

open private short from YM.Integration.WilsonMovingForkStoppedHeat
open WilsonInvariantActionPosition (berth)

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(t window depth:ℕ):
    ∃width:ℕ,∀ᶠj:ℕ in atTop,let K:=berth R t j
      ∀c v N per:ℕ,c≤j→v≤c→c≤N→a c/a j≤(H j)^window→
        σ c-σ v≤4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹→
        a v/a K≤(H v)^width ∧ σ K-σ v≤(width:ℝ)*(1+Real.log (H (v+1))):=by
  let U:ℕ:=window+4*(2*depth+1)
  let W:ℕ:=2*(t+1)+3*U
  refine ⟨W,?_⟩
  have sp:=Gauge.slopeConstant_pos simple
  have rate:=hat_rate L simple
  have windowCut:=WilsonAddressedCollarWindow.original R simple slow t (show (0:ℝ)<1 by norm_num)
  filter_upwards [windowCut,short R simple (U:ℝ) (Nat.cast_nonneg _),rate.eventually_ge_atTop 4]
    with j fine wk hot
  intro K c v N per cj vc live wide span
  have jp:0<H j:=by linarith
  have shift:σ j-σ c≤(window:ℝ)*Real.log (H j):=by
    have priced:=Real.log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) wide
    rwa [WilsonReflectedRelativeDate.ratio R,Real.log_pow] at priced
  have hatOrder:H c≤H j:=WilsonStartup.Timing.hat_mono L sp.le cj
  have βc:R.family.path.β N per c≤2*H j:=(R.makes.wilson.represents N per c live).band.2.trans
    (mul_le_mul_of_nonneg_left hatOrder (by norm_num))
  have βcp:0<R.family.path.β N per c:=by
    exact lt_of_lt_of_le (half_pos (zero_lt_one.trans ((L).fits.delayed c))) (R.makes.wilson.represents N per c live).band.1
  have mask:Real.sqrt (R.family.path.β N per c)≤2*H j:=(Real.sqrt_le_iff).2
    ⟨by linarith,βc.trans (by nlinarith only [wk.1,mul_nonneg (sub_nonneg.mpr wk.1) jp.le])⟩
  have cCost:Real.log (regulatorRun R.family N per c)⁻¹≤Real.log (2*H j):=by
    simpa only [regulatorRun,inv_inv] using Real.log_le_log (Real.sqrt_pos.2 βcp) mask
  have halfSpan:σ j-σ v≤(U:ℝ)*Real.log (2*H j):=by
    have high:=Real.log_le_log jp (show H j≤2*H j by linarith)
    have a₁:=mul_le_mul_of_nonneg_left high (Nat.cast_nonneg window)
    have a₂:=mul_le_mul_of_nonneg_left cCost (show 0≤4*(2*(depth:ℝ)+1) by positivity)
    dsimp only [U];push_cast
    linarith only [shift,span,a₁,a₂]
  have anchor:H j≤2*H v:=wk.2 v halfSpan
  have vp:2≤H v:=by linarith only [hot,anchor]
  have vp':0<H v:=by linarith
  have log₁:Real.log (H j)≤2*Real.log (H v):=by
    have bound:H j≤(H v)^2:=anchor.trans (by nlinarith only [vp,sq_nonneg (H v-2)])
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log jp bound
  have log₂:Real.log (2*H j)≤3*Real.log (H v):=by
    have two:Real.log 2≤Real.log (H v):=Real.log_le_log (by norm_num) vp
    rw [Real.log_mul (by norm_num) jp.ne']
    linarith
  have optical:a j/a K≤(H j)^(t+1):=by
    simpa only [pow_succ,Real.rpow_one] using fine.2.2
  have fineSpan:σ K-σ j≤((t+1:ℕ):ℝ)*Real.log (H j):=by
    simpa only [WilsonReflectedRelativeDate.ratio R,Real.log_pow] using
      Real.log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) optical
  have duration:σ K-σ v≤(W:ℝ)*Real.log (H v):=by
    have t₁:=mul_le_mul_of_nonneg_left log₁ (Nat.cast_nonneg (t+1))
    have t₂:=mul_le_mul_of_nonneg_left log₂ (Nat.cast_nonneg U)
    dsimp only [W];push_cast at *
    linarith only [fineSpan,halfSpan,t₁,t₂]
  constructor
  · apply (Real.log_le_log_iff (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) (pow_pos vp' _)).mp
    rwa [WilsonReflectedRelativeDate.ratio R,Real.log_pow]
  · have growing:=Real.log_le_log vp' (WilsonStartup.Timing.hat_mono L sp.le (Nat.le_succ v))
    exact duration.trans (mul_le_mul_of_nonneg_left (by linarith : Real.log (H v)≤1+Real.log (H (v+1))) (Nat.cast_nonneg _))

end YM.Integration.WilsonMovingForkOpticalStops
end
