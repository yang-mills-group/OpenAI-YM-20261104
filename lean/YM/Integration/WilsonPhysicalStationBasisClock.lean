import YM.Integration.WilsonPhysicalStationDatedWidth
import YM.Integration.WilsonPhysicalStationBasisImpact
import YM.Integration.WilsonMovingForkReporterRankSurvey
import YM.Integration.WilsonIndependentRegisteredActuators
/-! Actual column thresholds on the original common two-post seller. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisClock
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

open WilsonPhysicalStationAdjacentRate (grade tab)
open MergeProof.East (topL)
open WilsonPhysicalStationBasisRoof (rent)
structure Live (m:ℕ) : Prop where
  large : 4 ≤ (A).clock.monitor m
  old : ((A).params m).columns*err R m ≤ 1/2
  fine : ((A).params (m+1)).columns*err R (m+1) ≤ 1/2
  thermal : ratio R m ≤ 2
  slope (N p:ℕ) : m < N → shrink (C) m N p ≤ 6*shrink (C) (m+1) N p
  adjacent (h:ℕ) : rate R m (m+1) h ≤ rent R m h
  coincident (h:ℕ) : WilsonPhysicalStationCoincidentEntry.rent R m ≤ rent R m h
theorem original (hg:G.Simple)(house:∀ᶠk:ℕ in atTop,topL (A) k ≤ (A).clock.monitor k):
    ∀ᶠm in atTop,Live R m:=by
  have heat:Tendsto (A).clock.monitor atTop atTop:=
    (Station.mag_rate (A) hg (show (0:ℝ) < 1 from zero_lt_one)).congr (fun i=>Real.rpow_one _)
  have cold:Tendsto (fun m=>((A).clock.monitor m)^(-(7:ℝ)/16)) atTop (𝓝 0):=by
    convert (tendsto_rpow_neg_atTop (by norm_num:(0:ℝ) < 7/16)).comp heat using 1
    ext i; simp [neg_div]
  have gates:∀ᶠm in atTop,((A).params m).columns*err R m ≤ 1/2:=by
    filter_upwards [eventually_ge_atTop 1, house,cold.eventually_lt_const (by norm_num:(0:ℝ) < 1/2)] with m early roof small
    have old:=WilsonPhysicalStationDatedWidth.earlier R m early
    have salary:((A).params m).columns ≤ stock R (m-1):=by linarith only [old]
    exact (mul_le_mul_of_nonneg_right salary (Real.exp_pos _).le).trans
      ((WilsonPhysicalStationAdjacentBank.heat R (m-1) m (WilsonPhysicalStationDatedWidth.sheltered R m early roof)).1.trans small.le)
  filter_upwards [eventually_ge_atTop 1,heat.eventually_ge_atTop 4,gates,(tendsto_add_atTop_nat 1).eventually gates,
    house,(tendsto_add_atTop_nat 1).eventually house,WilsonIndependentRegisteredActuators.original R hg] with m early hot e₀ e₁ roof next clock
  refine ⟨hot,e₀,e₁,clock.1,fun N p live=>(clock.2.2 N p live).1,?_,?_⟩
  · intro h
    exact (WilsonPhysicalStationDatedWidth.advance R m h early next roof ((div_le_iff₀ ((A).budget _).threshold_pos).mp clock.1)).trans
      ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
  · intro h
    exact (WilsonPhysicalStationDatedWidth.coincident R m early roof).trans
      ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))

open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward MergeProof MergeProof.Accent
open WilsonMovingForkReporterFixedRanks (Axes)
theorem issued (B:Binding (C))(O:HaarBudget G)(J:ChartRatio G){f:Extraction.Order}
    (H:(Cells.standard (C)).Hierarchy)(b:ℕ→Fin 3→ℝ)(z c:ℕ→ℝ)(P:∀d,ℝ→Fin 3→Tapes.Panel d)
    (grade:ℕ→ℕ){start:ℕ}{radius:ℝ}(station:Set.Ioc (0:ℝ) radius→{k:ℕ // start < k})
    (offset:Set.Ioc (0:ℝ) radius→ℝ)(count:ℕ→ℕ)(tests:∀d,Fin (count d)→Axes (C))
    (books:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O J H b z c P grade start radius station offset count tests)
    (outer inner:ℕ→Set.Ioc (0:ℝ) radius)(grown:∀i,1 ≤ grade (station (inner i)))(hg:G.Simple):
    ∀ᶠm in atTop,Live R m:=by
  obtain ⟨_,sold,_⟩:=books outer inner grown
  apply original R hg
  filter_upwards [eventually_gt_atTop start] with k hk
  exact (sold 0 ⟨k,hk⟩).limit
end YM.Integration.WilsonPhysicalStationBasisClock
end
