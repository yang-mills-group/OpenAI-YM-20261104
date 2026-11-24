import YM.Integration.WilsonOriginalNullStrongGate
import YM.Integration.WilsonOriginalNullLanding

/-! One original calendar for the measured feed, the regular reserve and
the compulsory reserve, all before choosing either regulator or origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBooked
open Function Filter Lattice Wilson RG Source Labels Trace.Physical
open ConnectedActivityE6 PhysicalNext Repeat Legato Graces Roost Org Push.Local Next.Foundations
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "scaleCost" => WilsonMeasuredRankedResidual.sourceCost R d
local notation "wrap₀" => WilsonMeasuredRankedPrimaryBudget.wrap F₀ R.family.params

structure Date (simple:G.Simple) (M:WilsonMeasuredRankedMenu.Menu R d) (q:ℕ) (ε:ℝ) (i:ℕ) : Prop where
  reserve : WilsonOriginalNullGain.Appointment R d (min ε 1) i
  landing : (eventually_atTop.mp (WilsonOriginalNullLanding.local_section R d simple)).choose ≤ i
  compulsory : ∀ N per, i<N →
    let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
    let L:ℝ:=(R.family.S.block i).val
    (2+4*(R.family.path.levels.params i).columns)*
      (2*L^d*((WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap₀ q)*g^q)) ≤ (min ε 1)*L^(-(1/8:ℝ))

theorem original (simple:G.Simple) (M:WilsonMeasuredRankedMenu.Menu R d) (q:ℕ) {ε:ℝ} (ep:0<ε)
    (accuracy:2*d+5≤q) (slow:WilsonWindowReportingPace.Slow R.kit)
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (roster:∀ j,j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power) :
    ∀ᶠ i:ℕ in atTop,Date R d simple M q ε i := by
  have pos:0 < min ε 1:=lt_min ep zero_lt_one
  filter_upwards [WilsonOriginalNullGain.original R d simple M pos slow roster,
    eventually_ge_atTop (eventually_atTop.mp (WilsonOriginalNullLanding.local_section R d simple)).choose,
    WilsonMeasuredOwnerPlacedGain.small R d simple q (WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap₀ q)
      (min ε 1) pos accuracy slow.2 prepared] with i reserve stop forced
  exact ⟨reserve,stop,forced⟩

end YM.Integration.WilsonOriginalNullBooked
