import YM.Integration.WilsonOriginalOneArmOpticalDates
import YM.Integration.WilsonOriginalOneArmClearCash
import YM.Integration.WilsonOriginalSparseDatedHeat
import YM.Integration.WilsonOriginalPhysicalCorridorLength

/-! A finite roster's thermal and original occupied-gallery costs on one optical
collar. The opening precedes the physical cutoff, period, and held board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmOpticalReprice
open Filter Finset Lattice Wilson RG Marker MeasureTheory
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open WilsonOriginalFullRosterCouplingClock
open WilsonRootedKioskOccupiedSlip WilsonCapturedPrimarySoftPartition
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(simple:G.Simple){V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "g" N:max per:max i:max => Pert.Asymptotics.regulatorRun R.family N per i
local notation "spanCost" c:max => (c:ℝ)/Real.log 3

open WilsonOriginalOneArmOpticalDates (At)

theorem original {s:(marks).Mode}{n cost P f d debt level request:ℕ}{C η:ℝ}
    {budget:2≤C}{np:0<n}{load:∀t:(marks).Mode,t.val.card≤n}{ep:0<η}{b i N per:ℕ}
    (old:At R simple s n cost P f d debt request C η budget np load ep b i N per)
    (actual:((H i)^level)⁻¹ ≤ C*(g N per (i+1))^(work n P f d+2)):
    At R simple s n cost P f d debt level C η budget np load ep b i N per:=
  ⟨old.begin_at,old.fixed,old.mature,old.failed_age,old.failed,old.clock,actual,old.tilt,
    old.positive,old.wide,old.neighbor,old.optical⟩

end YM.Integration.WilsonOriginalOneArmOpticalReprice
end
