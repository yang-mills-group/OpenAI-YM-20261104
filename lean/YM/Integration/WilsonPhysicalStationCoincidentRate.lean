import YM.Integration.WilsonPhysicalStationCoincidentEntry
import YM.Integration.WilsonPhysicalStationAdjacentRate
import YM.Integration.WilsonPhysicalStationAdjacentBank
import YM.Integration.WilsonIndependentRegisteredThermalRatios
import YM.Planned.CALIBRATED_MIXED_HISTORY.Bridge

/-! The genuine common-date error tends to zero on the original measured course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationCoincidentRate
open Function Filter Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Work.G08 Next.Foundations Bid
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling ceiling_nonneg)
open WilsonPhysicalStationAdjacentFare (fare)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationAdjacentBank (stock)
open WilsonPhysicalStationRawReading (err)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels


open WilsonPhysicalStationCoincidentEntry (rent)
def tariff (m:ℕ):ℝ:=10*((A).clock.monitor m)^(-(7:ℝ)/16)
theorem paid (m:ℕ) (early:0 < m)(home:((C).S.block m).val ≤ (A).clock.monitor m):
    rent R m ≤ tariff R m:=by
  let c:=((A).params m).columns
  let x:=err R m
  let w:=stock R m
  have cw:1+c ≤ w:=(WilsonPhysicalStationAdjacentBank.both R m early).1
  have one:1 ≤ c:=((A).params m).columns_ge
  have xp:0 ≤ x:=(Real.exp_pos _).le
  have xmax:x ≤ 1:=by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by norm_num)
  have raw:2*c*(1+x) ≤ 2*c*2:=mul_le_mul_of_nonneg_left (by linarith only [xmax]) (by linarith only [one])
  have cap:1+2*c*(1+x) ≤ 5*w:=by linarith only [raw,cw,one]
  have heat: w*x ≤ ((A).clock.monitor m)^(-(7:ℝ)/16):=(WilsonPhysicalStationAdjacentBank.heat R m m home).1
  calc
    rent R m ≤ (5*w)*(2*x):=mul_le_mul_of_nonneg_right cap (by linarith only [xp])
    _=10*(w*x):=by ring
    _≤tariff R m:=mul_le_mul_of_nonneg_left heat (by norm_num)
theorem tends (hg:G.Simple):Tendsto (tariff R) atTop (𝓝 0):=by
  have heat:Tendsto (A).clock.monitor atTop atTop :=
    (Station.mag_rate (A) hg (show (0:ℝ) < 1 from zero_lt_one)).congr (fun i=>Real.rpow_one _)
  have a:Tendsto (fun m=>((A).clock.monitor m)^(-(7:ℝ)/16)) atTop (𝓝 0):=by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 7/16)).comp heat using 1
    ext i;simp [neg_div]
  change Tendsto (fun m=>10*((A).clock.monitor m)^(-(7:ℝ)/16)) atTop (𝓝 0)
  simpa only [mul_zero] using a.const_mul (10:ℝ)
theorem original (hg:G.Simple){ε:ℝ}(goal:0 < ε):
    ∀ᶠ m:ℕ in atTop,((C).S.block m).val ≤ (A).clock.monitor m → rent R m < ε:=by
  filter_upwards [eventually_ge_atTop 1,(tends R hg).eventually_lt_const goal] with m earlier small shelter
  exact (paid R m earlier shelter).trans_lt small
end YM.Integration.WilsonPhysicalStationCoincidentRate
end
