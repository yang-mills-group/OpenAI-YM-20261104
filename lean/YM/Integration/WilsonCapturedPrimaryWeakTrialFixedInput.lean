import YM.Integration.WilsonCapturedPrimaryWeakTrialConnectedScalar
import YM.Integration.WilsonReceivedCanonicalVerseRegister

/-! Purchased fixed fine residues for each signed socket of the authentic upper field. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialFixedInput
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
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds WilsonCoeffUV.Winding
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCompactVerseEntrance (CoverBill)
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Carp XSpace
variable {G:Gauge}{n e j:ℕ}{d h:Fin n→ℕ}(R:Run G)
variable (κ:(v:Fin n)→Knob (h v))(pt:Fin n→Chamber)

def places (Y:Realm G (e+1) Credit.leanC)
    (digits:(Fin n→ Cover)→Fin n→Site (ll Y.draws j).L)(y:Fin n→ Cover)(v:Fin n):Cover:=
  (ll Y.draws j).L.val • y v + lift (digits y v)

def input (Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor≤j)(S:Finset (Fin n))
    (choice:(v:Fin n)→Choice R d v)(digits:(Fin n→ Cover)→Fin n→Site (ll Y.draws j).L)
    {A:ℝ}(sound:Wellness d (start R d κ pt choice))
    (paid:CoverBill (start R d κ pt choice) e (Y.mint (j+1) (by omega)).σ A) :
    FundedMarkedPathSelection.Input Y lo S d h A where
  familyAt y:=start R d κ pt choice (places Y digits y)
  offsets:=digits
  empty y:=sound.quiet' (places Y digits y)
  degree y:=sound.level' (places Y digits y)
  price y T _ a ha r:=paid (places Y digits y) T a ha r

theorem uniform (e:ℕ):∃A:ℝ,1≤A ∧ ∀(j:ℕ)(Y:Realm G (e+1) Credit.leanC)
    (lo:Y.anchor≤j), (Y.mint (j+1) (by omega)).σ≤1 →
    ∀(S:Finset (Fin n))(q:(v:Fin n)→Choice R d v)
    (digits:(Fin n→ Cover)→Fin n→Site (ll Y.draws j).L),
    ∃X:FundedMarkedPathSelection.Input Y lo S d h A,
      X.familyAt=(fun y=>start R d κ pt q (places Y digits y)) ∧ X.offsets=digits ∧
      ∀N T y, FundedMarkedPathSelection.output X T N y =
        logO Y.draws Y.paid j N (start R d κ pt q (places Y digits y)) d T := by
  obtain ⟨A,one,sold⟩:=WilsonReceivedCanonicalVerseRegister.original R d κ pt e (s:=1) zero_lt_one
  refine ⟨A,one,?_⟩
  intro j Y lo width S q digits
  obtain ⟨sound,bill,_⟩:=sold q
  let X:=input R κ pt Y lo S q digits sound (fun y T a ha r=>(bill y T a ha r).shave width)
  exact ⟨X,rfl,rfl,fun _ _ _=>rfl⟩

end YM.Integration.WilsonCapturedPrimaryWeakTrialFixedInput
