import YM.Integration.WilsonVacuumPreResetMeasuredCoin
import YM.QuadraticLocal.Rebirth.Life
import YM.Integration.WilsonMarkedScalarUniqueness

/-! Every grade of the actual outgoing caliber reads the one independently projected vacuum on the same course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMeasuredCaliber
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Tree
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.alloy.B.a



open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi

open WilsonVacuumPreResetDatedCourse (coin)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)



theorem measured {N m e i:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (identified:Agrees R N m e Z π Γ)(lo:m ≤ i)(hi:i<N)(starts:Γ i 0=0){l:ℕ}(hl:l≤e+2):
    (Rebirth.caliber (Γ i) starts).measure l=PowerSeries.coeff l (pitch (levels R) (ratio R) N i):=by
  have at_l:Γ i l=PowerSeries.coeff l (pitch (levels R) (ratio R) N i-1):=identified.rates i lo hi l hl
  by_cases zero:l=0
  · subst l
    rw [starts,map_sub,PowerSeries.coeff_zero_one] at at_l
    exact (Rebirth.caliber (Γ i) starts).starts.trans (by linarith only [at_l])
  · rw [Rebirth.Chart.elsewhere (Γ i) starts (Nat.pos_of_ne_zero zero),at_l,map_sub,
        PowerSeries.coeff_one,if_neg zero,sub_zero]

open FormalBulk08 FormalBulk08.Series FormalBulk08.Flat FormalBulk08.Reef
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm

theorem settled {N m e i:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (identified:Agrees R N m e Z π Γ)(lo:m ≤ i)(hi:i<N)(starts:Γ i 0=0):
    let C:=Rebirth.caliber (Γ i) starts
    let H:=pitch (levels R) (ratio R) N i
    let cap:=e+2
    (∀ l≤cap,C.measure l=PowerSeries.coeff l H) ∧
    FormalBulk08.Series.Through cap (rate (C.back cap)) (PowerSeries.map Complex.ofRealHom (Wine.bookH H)) ∧
    FormalBulk08.Series.Through cap (reciprocal (C.back cap)) (PowerSeries.map Complex.ofRealHom (Wine.bookU H)) ∧
    ∀l≤cap,∀birth angular,physicalWeight C cap l birth angular=formalWeight H l birth angular:=by
  intro C H cap
  have fees:∀l≤cap,C.measure l=PowerSeries.coeff l H:=fun _ h=>measured R identified lo hi starts h
  have fresh:Wine.Fresh H:=(fees 0 (Nat.zero_le _)).symm.trans C.starts
  have primitive:=WilsonMarkedScalarUniqueness.primitive C cap cap le_rfl H fresh fees
  let K:=C.back cap
  let forward:=PowerSeries.map Complex.ofRealHom (Wine.bookH H)
  let U:=PowerSeries.map Complex.ofRealHom (Wine.bookU H)
  have product:forward*U=1:=by dsimp [forward,U];rw [←map_mul,Wine.book_equal,map_one]
  have opposite:FormalBulk08.Series.Through cap (reciprocal K*rate K*U) (reciprocal K*forward*U):=
    ((FormalBulk08.Series.Through.exact_eq (reciprocal K) cap).mul primitive).mul (FormalBulk08.Series.Through.exact_eq U cap)
  rw [mul_comm (reciprocal K) (rate K),unit,one_mul,mul_assoc,product,mul_one] at opposite
  exact ⟨fees,primitive,opposite.symm,fun _ hl birth angular=>
    WilsonMarkedScalarUniqueness.weight C cap cap le_rfl H fresh fees hl birth angular⟩

end YM.Integration.WilsonVacuumPreResetMeasuredCaliber
