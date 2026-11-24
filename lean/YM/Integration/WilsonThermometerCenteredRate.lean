import YM.Integration.WilsonThermometerCenteredCredit
import YM.Integration.WilsonThermometerCenteredBound

/-! Quantitative extraction of the signed connected thermometer after the
single common Wilson normalization. Only its proper residuals enter nonlinearly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredRate
open Filter Finset Marker QuadraticLocal Extra.Trajectories WilsonThermometerCenteredAlgebra
open FVA1 RG Wilson Table Extraction Climb Trace.Pilot Next.Rank Next.UVStress
open RG12 RG17 PhysicalNext.Repeat.Legato OriginalForcedAddresses WilsonPositionThermometerCapStation
open WilsonThermometerCenteredCredit WilsonThermometerCenteredBound
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)

/-- Each measured proper face has already been integrated over the old
vacuum. The complete credit is the only first-order scalar purchase. -/
theorem original {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1)
      (o : Positions (Fin 3) (R.family.side z.1 z.2)) (Q : Poly J) (_qu : Q.part (J).quiet=1)
      (w : Fin 3 → ℝ) (_hw : ∀ i,0<w i) (e : ℝ),
      (∑ s : (J).Mode, if s≠(J).quiet ∧ s≠full then
        Poly.toll w s*‖(total (table R A z o) Q).part s‖ else 0) ≤ e →
      Poly.toll w full * ‖(Extra.Trajectories.connected (table R A z o)).part full -
        (Extra.Trajectories.connected Q).part full - normalized R A z upper o Q‖ ≤ e^2/2+e^3/3 := by
  filter_upwards [unit_table R A checked unit,heard R A simple checked unit] with z mass fee k upper o Q qu w hw e b
  rw [fee k upper o Q]
  apply charged _ Q (mass o) qu w hw
  rw [proper_bill _ (normed _ _ (mass o) qu) w]
  exact b

end YM.Integration.WilsonThermometerCenteredRate
