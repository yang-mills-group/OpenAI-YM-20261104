import YM.Integration.WilsonOriginalCensusCanonicalFirstEdgePayer
import YM.Integration.WilsonAddressedPublicFirstLive
import YM.Integration.WilsonAddressedPublicFirstClock
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstOrigin
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
attribute [local instance] Gauge.frobInner
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

variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}(d:Fin n→ℕ)

/-- The primitive ceiling is fixed by the finite original source list. -/
def ceiling : ℕ := Finset.univ.sup fun i:Fin n=>
  Finset.univ.sup fun v:Choice R d i=>rank R d (entry R d i v)

theorem fits (a:∀i,Choice R d i)(i:Fin n) : rank R d (entry R d i (a i))≤ceiling R d:=by
  classical
  exact (Finset.le_sup (f:=fun v:Choice R d i=>rank R d (entry R d i v)) (Finset.mem_univ (a i))).trans
    (Finset.le_sup (f:=fun i:Fin n=>Finset.univ.sup fun v:Choice R d i=>rank R d (entry R d i v))
      (Finset.mem_univ i))

variable {semester:WilsonOriginalAllOrderCourse.Schedule G}(school:Room semester R simple)
  {qmin p:ℕ}(ask:Demand qmin p d){m j N per:ℕ}(day:Day semester R simple ask.school m N)
local notation "clock" => R.alloy.B.a.clock

/-- The counted first source on this same day can be posted on each submitted
primitive and at any previously set positive rent, before choosing a lower row. -/
theorem original (early:m≤j)(live:j+1+1≤N)
    (seller:ℕ→Gear G→ℝ)(fund:FundedMarkedCoverRows.prices seller R.kit)
    (history:FundedOriginalVacuumPaths.prices R.kit)
    (paid:WilsonOriginalCensusCanonicalAppointedClock.opening R simple seller fund history (Burn.horizon ask.vac) ≤ m)
    (pre:ceiling R d≤qmin)(ord:ask.order≤(clock).J (j+1))
    (stock:Open R simple d ask.school.pieces (ask.school.order+1) ask.load (j+1))
    (tags:∀t:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per),(step R (j+1) t.val).Choices):
    ∃op:Mentor.Opportunity ((clock).J (j+1+1)) ((clock).J (j+1)),
      op.count=ask.school.pieces ∧ op.stage=ask.school.order+1 ∧
      ∀(hd:∀i,0<d i)(y:Fin n→Lattice.Cover)(cells:Digits R.family.path.levels (Fin n))
        (a:∀i,Choice R d i)(tol:ℝ),0<tol→
      Nonempty (Source R day.hk (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per)
        school.books early op (day.lessons (j+1) (Nat.le_succ_of_le early) live)
        school.ahead d a hd y cells ask.order ask.shelf tol):=by
  classical
  obtain ⟨_,⟨cal⟩,_,op,_,_,count,stage⟩:=(day.seen per).2.2.2 j early (by omega)
  refine ⟨op,count,stage,?_⟩
  intro hd y cells a tol tp
  have slots:Fintype.card (Fin n)≤op.count:=by simpa only [Fintype.card_fin,count] using ask.load.slots
  have hard:6*op.count≤(clock).J (j+1):=by simpa only [count] using stock.hard
  have opened:WilsonFirstReceivedEarnedFee.opening R simple op.count p ask.order ask.vac ask.load.deep
      ask.load.aged (by norm_num:0<(1:ℝ)) ≤ (j+1):=by simpa only [count] using stock.opened
  have more:WilsonMeasuredSemesterSubpower.onset R op.count (by norm_num:0<(1:ℝ))≤j+1:=by
    simpa only [count] using stock.more
  exact ⟨WilsonOriginalCensusCanonicalFirstEdgePayer.original R simple day.hk
    (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per) (day.seen per).1
    (WilsonPhysicalHistoryPriorAperture.law G MintClock.splits) school.books early (by omega) op (day.lessons (j+1) (Nat.le_succ_of_le early) live)
    cal school.ahead school.chamber school.hospital d a hd y cells ask.order ask.shelf
    seller fund history paid school.ticket day.path (fun i=>(fits R d a i).trans (pre.trans ask.load.qfit))
    slots ask.load.fit stock.level ord (stage.symm ▸ ask.load.stage) (count.symm ▸ ask.load.count)
    ask.load.expense tp (lit (V:=Fin n)) (day.seen per).2.1 school.warm school.pass stock.halo stock.onset
    p school.way hard ask.load.deep ask.load.aged opened more stock.cooled stock.fresh school.month tags⟩

end YM.Integration.WilsonAddressedPublicFirstOrigin
end
