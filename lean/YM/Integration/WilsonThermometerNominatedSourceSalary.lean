import YM.Integration.WilsonThermometerMarchReference
import YM.Integration.WilsonThermometerOwnOffsetField
import YM.Integration.WilsonThermometerOffsetTrajectory

/-! Numeric source receipt common to the weak reflected panel and the original
close Wilson school. It is a receipt for the entire nominated bare label. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerNominatedSourceSalary
open Lattice Wilson RG Source Table Extraction Marker PhysMS Trace Trace.Pilot RG05Readout
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout.Address XSpace XSpace.Normalize XSpace.Rose Cells WilsonPositionThermometerReading
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource
open scoped Classical BigOperators
variable {G:Gauge} {R:Run G}
local notation "C" => R.family

def owns (Z:Group (C) 6) (k N p:ℕ) (hk:k≤N) (s:Badge)
    (r:∀i:Fin 3,Emblems (C) (grade i)) (E:ℝ):Prop:=
  ∃y:∀i:Fin 3,Palette (C) (grade i),∀i:Fin 3,
    (((C).S.a k:ℂ)^(grade i).val) • ((C).factory (grade i) N p).terminal
      (finer (r i) hk (y i) (primaryLetter (grade i)))=
        Z.station.wheel.atCut (N,p) (index Z (grade i)) (vector Z s i) ∧
    size (y i)≤ E*WilsonThermometerMarchReference.fee (C) s i

end YM.Integration.WilsonThermometerNominatedSourceSalary
