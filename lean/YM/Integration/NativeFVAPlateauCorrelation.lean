import YM.Integration.NativeFVAPlateau
import YM.FVAAlt2.Moving.Supplier

/-! The moving formal FVA comparison on the Run that purchased the regulator windows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFVAPlateau

open Lattice Precision RG RegulatorIR
open YM.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open PhysicalNext.Repeat.Legato MS MS.Land

/-- The kernel, branches, physical Run and plan are common to the regulator contract
and the formal moving correlation match. -/
def Correlations {G : Gauge} (R : Run G) : Prop :=
  let K := R.family.path.levels.clock.kernel
  let Y := Oracle.books K
  ∃ (Z : ∀ P : Patch, P.Branches K G)
    (C : RegulatorIR.FVAAlt2.Lodge.Contract R Y Z)
    (A : Booked (Home.seats (Study.Plan R).liftOff (Study.Plan R).certified))
    (H : MS_Data G A)
    (T : Prescription (Home.seats (Study.Plan R).liftOff (Study.Plan R).certified)),
    RegulatorIR.FVAAlt2.Moving.Supplier.CorrelationMatch Y Z R C H T

theorem correlations {G : Gauge} (hG : G.Simple) (R : Run G)
    (h : Funded R.family.path.levels) : Correlations R := by
  obtain ⟨Z, C⟩ := contract R h
  obtain ⟨A, H, T, hT⟩ :=
    RegulatorIR.FVAAlt2.Moving.Supplier.supply_H
      (Oracle.books R.family.path.levels.clock.kernel) Z R C hG
  exact ⟨Z, C, A, H, T, hT⟩

end YM.Integration.NativeFVAPlateau
end
