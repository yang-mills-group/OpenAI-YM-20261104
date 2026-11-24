import YM.Integration.WilsonAddressedPublicFirstOrigin
import YM.Integration.WilsonAddressedPublicSubmittedDates

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstActivation
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators
open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics
open WilsonVacuumPreResetStationaryChange (step coarse levels)
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.TwoReset WilsonCoeffUV.Winding Further.PhysicalPeriodLimitF933 Macrame
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider.Canvas FreeResolvent
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Pressure Precision Tree Exterior PertExtension PertExtension.Series WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open scoped Topology ContDiff Matrix.Norms.Frobenius
open Source Labels
open WilsonOriginalFullRosterCouplingClock (work)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalCensusPhysicalAttendance (roots tab Room)
open WilsonReceivedChronologicalPanelClock (debitDepth fare)
open WilsonOriginalOccupiedWindow WilsonOriginalOccupiedCorridor WilsonOriginalJointTrialHearing
open WilsonOriginalCensusPhysicalAttendance (Room roots tab)
open WilsonOriginalCensusFundedAttendance (Demand)
open WilsonReceivedChronologicalFixedLedger (Registered)
open WilsonReceivedChronologicalFixedEarner (programme)
open WilsonReceivedChronologicalFixedReserve (terms)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonOriginalCensusAttendanceStation
open AllOrder AllOrder.Floe
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonReceivedFixedDigitHistory (Digits)
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open WilsonOriginalCollarElection WilsonOriginalCollarTeacher QuadraticLocal.Advent.Oak QuadraticLocal.Affinity
open LocalComparison
open scoped Classical BigOperators Topology
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
open WilsonOriginalCensusPublicationClock (Open)
open WilsonOriginalCensusCanonicalFirstEdgePayer (Source)
open WilsonReceivedChronologicalSocket (lit)
open WilsonReceivedFixedDigitHistory (Digits)
open Finset Wilson RG QuadraticLocal Org Work.F08
open WilsonOriginalFullRosterCouplingClock (work wallet)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonReceivedChronologicalFixedReserve (terms charges)
open WilsonAddressedPublicSubmittedDates (grades)
open WilsonOriginalStarSceneWords (rank maximum)
open WilsonThermometerDeclaredSeeds (Choice entry)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)

theorem before {n:ℕ}(d:Fin n→ℕ) : WilsonAddressedPublicFirstOrigin.ceiling R d≤ maximum R d:=by
  classical
  unfold WilsonAddressedPublicFirstOrigin.ceiling
  apply Finset.sup_le
  intro i _
  apply Finset.sup_le
  intro v _
  exact Finset.le_sup (f:=rank R d) (Finset.mem_univ (entry R d i v))

theorem rank_budget {n:ℕ}(d:Fin n→ℕ)(P:ℕ) : P≤(terms d (fun _=>0) P).order:=by
  let S:=terms d (fun _=>0) P
  have cash:=S.cash
  have deep:=S.deep
  simp only [work] at cash
  change P ≤ S.order
  omega

/-- A single order pays the primitive ceiling on every nominated and reflected
subroster of the three columns. It is chosen before mesh, period and sites. -/
theorem original (requested:ℕ):
    ∃P:ℕ,requested≤P ∧ ∀role:Fin 3→Fin 3, WilsonAddressedPublicFirstOrigin.ceiling R (grades role)≤
      (terms (grades role) (fun _=>0) P).order:=by
  classical
  let largest:=Finset.univ.sup fun role:Fin 3→Fin 3=>maximum R (grades role)
  refine ⟨max requested largest,le_max_left ..,?_⟩
  intro role
  have h:maximum R (grades role)≤largest:=Finset.le_sup (f:=fun v:Fin 3→Fin 3=>maximum R (grades v))
    (Finset.mem_univ role)
  exact (before R (grades role)).trans ((h.trans (le_max_right ..)).trans (rank_budget ..))

end YM.Integration.WilsonAddressedPublicFirstActivation
end
