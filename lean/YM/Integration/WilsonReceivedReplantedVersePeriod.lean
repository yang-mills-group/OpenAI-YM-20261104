import YM.Integration.WilsonReceivedReplantedVerseCourse

/-! The signed finite minus reprinted period fee for the same complete incoming independent table. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedReplantedVersePeriod
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint (Issued printed)
open WilsonMarkedIndependentEnrolledPeriod (registered)

open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedMicroscopicVerseWallet (gross)

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h k:I → ℕ}{e:ℕ}

def Charge (Y:Outerm G h)(k:I → ℕ)(e:ℕ)(n:Side)(σ A:ℝ):Prop:=
  ∀(J:Finset I)(c:I),c∈J → ∀(z:I → Site n)(a:ℕ),a ≤ e → ∀(r:ℕ)(x:Fin r → Woods G n),
    let y:=PeriodicMarkedWinding.roots n z c
    ‖(Y y J).1 n a r x-((submit Y k e) y J).1 n a r x‖ ≤
      (((priceM (Hooks G) r σ+tiePay (Hooks G) r (σ/4)+1)*A^J.card+A^J.card)*
        catchW (σ/32/16) n)*Real.exp (-(σ/32/2)*Syn (tor n) z J x)

omit [DecidableEq I] in
theorem original {Y:Outerm G h}(well:Wellness k Y){n:Side}{σ A:ℝ}(hs:0<σ)(hA:1 ≤ A)
    (paid:PairedAt e Y n σ A):Charge Y k e n σ A:=by
  have cover:CoverBill Y e σ A:=fun y J a ha r=>(paid y J a ha r).access
  have files:=(WilsonReceivedCompactVerseEntrance.original Y well hs hA cover).2.2.1
  intro J c root z a ha r x y
  rw [(files y J a ha).2 n r]
  exact (norm_sub_rev _ _).le.trans ((PeriodicMarkedWinding.periodized z c root hs
    (paid y J a ha r)).2 x)

end YM.Integration.WilsonReceivedReplantedVersePeriod
