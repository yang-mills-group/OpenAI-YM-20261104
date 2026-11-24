import YM.Integration.WilsonThermometerWeakFundedRoster
import YM.Integration.WilsonThermometerWeakIssuedDetector

/-! Prices at the initial radius of a calibrated Wilson reflection course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSourceRadius
open Function Filter Set MeasureTheory RG RG12 Extra.Histories Lattice Wilson Source Labels
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open Next.Rank.Tapes Vac.Numbers
open WilsonThermometerOwnOffsetRadii
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels

theorem enrolled (simple:G.Simple) {H:ℕ} (plan:Panel H):
    ∀ᶠ k:ℕ in atTop,bill ((plan.bag ((A).clock.J k)).credit-1) (clim (A) k)≤(A).clock.hatBeta k:=by
  let b:ℝ:= -9-plan.currency
  filter_upwards [(hat_rate (A) simple).eventually (Paint.monitors b 1 zero_lt_one)] with k cost
  let n:=(A).clock.J k
  have eq:=plan.vital n
  have h:= (plan.bag n).fits
  have le:(plan.bag n).credit-1≤b:=by dsimp only [b];linarith only [eq,h]
  refine (Glimmer.billed _ le).trans ?_
  calc
    _ ≤ Real.exp (Real.log ((A).clock.hatBeta k)):=by
      unfold Perch.bill;apply Real.exp_le_exp.mpr
      simpa only [one_mul,mul_comm] using cost
    _ = _:=Real.exp_log (WardBin.hot (A) k)

theorem native (t k:ℕ):
    radius R t k k=Hat (clim (A) k)^(2*(t:ℝ)):=by
  rw [radius_start, show (2:ℝ)*t=↑(2*t) by push_cast;rfl,Real.rpow_natCast,pow_mul]
  change (((A).clock.hatBeta k)^t)⁻¹=(((Real.sqrt ((A).clock.hatBeta k))⁻¹)^2)^t
  simp only [inv_pow,Real.sq_sqrt (WardBin.hot (A) k).le]

end YM.Integration.WilsonThermometerWeakSourceRadius
end
