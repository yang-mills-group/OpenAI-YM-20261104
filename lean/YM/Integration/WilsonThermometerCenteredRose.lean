import YM.Integration.WilsonThermometerCenteredRate
import YM.Integration.WilsonThermometerCenteredScalar

/-! The seven ordinary face readings of the physical position test, using
one compensated scalar credit at every earlier Wilson date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredRose
open Filter Finset Marker RG Wilson Table Extraction Climb Trace.Pilot Next.Rank Next.UVStress
open FVA1 RG12 RG17 PhysicalNext.Repeat.Legato OriginalForcedAddresses WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredCredit WilsonThermometerCenteredScalar
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)

theorem named (F : Poly J) (fu : F.part (J).quiet=1) :
    (Extra.Trajectories.connected F).part full =
      WilsonPositionThermometerConnected.value (WilsonThermometerCenteredScalar.read F) :=
  WilsonThermometerCenteredScalar.three F fu

theorem original {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1)
      (o : Positions (Fin 3) (R.family.side z.1 z.2)) (Q : Poly J) (_qu : Q.part (J).quiet=1)
      (w : Fin 3 → ℝ) (_hw : ∀ i,0<w i) (e : ℝ),
      (∑ s : (J).Mode, if s≠(J).quiet ∧ s≠full then
        Poly.toll w s*‖(total (table R A z o) Q).part s‖ else 0) ≤ e →
      Poly.toll w full * ‖WilsonPositionThermometerConnected.value (WilsonPositionThermometerGradedReading.row A z o.origin) -
        WilsonPositionThermometerConnected.value (WilsonThermometerCenteredScalar.read Q) -
        normalized R A z upper o Q‖ ≤ e^2/2+e^3/3 := by
  filter_upwards [unit_table R A checked unit,WilsonThermometerCenteredRate.original R A simple checked unit]
    with z mass rate k upper o Q qu w hw e cover
  have earned := rate k upper o Q qu w hw e cover
  rw [named _ (mass o),named Q qu] at earned
  exact earned

end YM.Integration.WilsonThermometerCenteredRose
