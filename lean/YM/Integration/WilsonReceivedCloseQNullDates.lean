import YM.Integration.WilsonReceivedCloseGeometricHardCourse
import YM.Integration.WilsonOriginalNullFiledStep

/-! The return of a compensated rank-zero source uses the same original income as the compact hard account. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseQNullDates
open Filter Lattice Wilson RG
open PhysicalNext Repeat Legato
open OPE.Therm WilsonLimitConstruction WilsonMeasuredOwnerAppointments
open scoped Topology Classical

variable {G:Gauge} (R:Run G) {k:ℕ} (order shelf:ℕ) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
  (lamp:WilsonReportLampForecast.Ready R.family.path.levels) (deep:2*(5+4+1)+8 ≤ order) (aged:5+4+4 ≤ 3*k+2)

def Booked (ε:ℝ) (m:ℕ):Prop :=
  ∃ M:WilsonMeasuredRankedMenu.Menu R 0, ∀i, m ≤ i →
    Ready R simple 0 5 k order shelf M slow.2 lamp (by decide) deep aged i ∧
    WilsonOriginalNullBooked.Date R 0 simple M 5 ε i

theorem original {σ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple σ W) (ε:ℝ) (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop, Booked R order shelf simple slow lamp deep aged ε m := by
  obtain ⟨M⟩:=WilsonMeasuredRankedMenu.original R 0 simple W funded slow lamp
  have dates:∀ᶠ i:ℕ in atTop,Ready R simple 0 5 k order shelf M slow.2 lamp (by decide) deep aged i ∧
      WilsonOriginalNullBooked.Date R 0 simple M 5 ε i :=
    (WilsonMeasuredOwnerAppointments.original R simple 0 5 k order shelf M slow.2 lamp (by decide) deep aged).and
      (WilsonOriginalNullBooked.original R 0 simple M 5 ep (by decide) slow lamp funded.2.2.2.1)
  obtain ⟨b,after⟩:=eventually_atTop.mp dates
  filter_upwards [eventually_ge_atTop b] with m cutoff
  exact ⟨M,fun i mi=>after i (cutoff.trans mi)⟩

end YM.Integration.WilsonReceivedCloseQNullDates
