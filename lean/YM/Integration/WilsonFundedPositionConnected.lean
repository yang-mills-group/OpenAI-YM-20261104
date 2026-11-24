import YM.FVA2.Main
import YM.XSpace.Panorama
import YM.Integration.WilsonReportingMeasuredAdmission
import YM.Pier.Lair.Stream

noncomputable section
namespace YM.Integration.WilsonPositionThermometerConnected
open Finset XSpace.Rose
open scoped Classical
def value (A : Badge → ℂ) : ℂ :=
  A univ - (A {0,1}*A {2} + A {0,2}*A {1} + A {1,2}*A {0}) +
    2*(A {0}*A {1}*A {2})

theorem continuous_value : Continuous value := by unfold value; fun_prop


end YM.Integration.WilsonPositionThermometerConnected
end
