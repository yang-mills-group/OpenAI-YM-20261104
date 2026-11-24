import YM.OPE.Compatible.Maestro.Lanes
import YM.OPE.Compatible.Eyrie.Return
import YM.OPE.Exchange.Arrangement

/-! Price both physical lanes for the particular final and authentic bin
that the original extraction supplies. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketFuelPrice
open OPE Next.Extract Dash
variable {G : Gauge}

def FromStrongBin (C:Family G):Prop :=
  ∀ (f:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (B:Bin A)
    (Z : ∀ d, ℕ → CoordMap C d) (tr:Presentation C) (T:Table C.book) (E:DiffPlan T)
    (physical:Spec.Final C f T), Projected tr f B Z → Next.Extract.Base C f A L B T E →
    (∀ d, OPE.RigE.StrongBin C B f d) → Services C f T →
    OPE.Lanes (F:=f) physical.sector.derivatives

end YM.Integration.WilsonMatrixTicketFuelPrice

