import YM.Integration.WilsonOlderFreshConnectedReceiver
import YM.Integration.WilsonOlderFreshUnaryCourse
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedBirth
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
variable {G:Gauge}{n e j:ℕ}{k D:Fin n → ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
variable (R:Run G)(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor ≤ j)(enrolled:Paid R Y lo D k δ σ)
variable (N:ℕ) (c:Fin n)(X:Input Y lo S k D A)(included:J⊆S)(pin:c∈J)(positive:0 ≤ A)
variable (older:j<N)(deep:0 < mass k J)(sw:0 ≤ σ)(o:Cover)(t:Case D)(u:Frill J c)
local notation "M₀" => R.family.path.levels.clock.hatBeta j^δ*A^J.card

def issued:Copy G (mass k J) e σ:=
  book Y lo X J c (mass k J) N o t u σ M₀ deep sw
    (fun a ha r=>WilsonOlderFreshConnectedEarning.payroll Y lo X
      ((enrolled N S J c A X included pin positive older).2 o a ha r) (by linarith))

local notation "T" => issued R Y lo enrolled N c X included pin positive older deep sw o t u

theorem account:
    ∑h:Fin (e+1),(T).fare h ≤ (e+1:ℕ)*((mass k J+e+1:ℕ)*((∏v∈J,‖t v‖)*M₀)):=by
  apply WilsonOlderFreshConnectedPin.income

theorem heard {n':Side}(a:ℕ)(ha:a ≤ e)(r:Fin (mass k J+a+1))(z:RadP G r.val)
    (U:Config G n')(place:Site n'):
    ∑b, (((T).roll ⟨a,by omega⟩).leg ⟨⟨r,(u,z),b⟩,rfl⟩).atom.unmasked U place =
      (Rolls.dip (packet Y lo X J c (mass k J) N o a r (u,z)) (touch t J)).unmasked U place:=
  WilsonOlderFreshConnectedPin.heard Y lo X J c (mass k J) N o t u a r z
    ((enrolled N S J c A X included pin positive older).2 o a ha r) U place

end YM.Integration.WilsonOlderFreshConnectedBirth
end
