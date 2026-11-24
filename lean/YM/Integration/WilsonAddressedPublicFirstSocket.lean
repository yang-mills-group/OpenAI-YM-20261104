import YM.Integration.WilsonAddressedPublicFirstLedger
import YM.Integration.WilsonAddressedPublicFirstReceived
import YM.Integration.WilsonAddressedPublicSubmittedFiling
import YM.Integration.WilsonAddressedPublicFirstLower
import YM.Integration.WilsonAddressedPublicFirstCalendar
import YM.Integration.WilsonAddressedPublicFirstDay
import YM.Integration.WilsonOriginalOneArmCanonicalCalendar
import YM.Integration.WilsonOriginalCensusCanonicalTranslatedPayer
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstSocket
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
open WilsonOriginalCensusAttendanceStation (Day)
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
variable {G:Gauge}(R:Run G)(simple:G.Simple){n m j N per:ℕ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
  (d:Fin n→ℕ)(P:ℕ)
local notation "zeroFee" => (fun _ : Fin n=>(0:ℕ))
local notation "semester" => (WilsonOriginalOpticalSchedule.prepared schedule)
local notation "ask" => (programme d (zeroFee) P)
local notation "length" => ((terms d (zeroFee) P).order)
variable (school:Room (WilsonOriginalOpticalSchedule.prepared schedule) R simple)
  (day:Day (WilsonOriginalOpticalSchedule.prepared schedule) R simple (programme d (fun _:Fin n=>0) P).school m N)
  (base:m≤j)(cut:j+1<N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (j+1+1)) (R.alloy.B.a.clock.J (j+1)))
  (q:(v:Fin n)→Choice R d v)(hd:∀v,0<d v)(y:Fin n→Lattice.Cover)
  {V:Realm G ((terms d (fun _:Fin n=>0) P).order+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
  {rate allowance:ℝ}(tape:Digits V.draws (Fin n))(lens:Fin n→ℕ)(pt:Fin n→Chamber)
  (x:Wallet (room (Fin n)))(bills:Fin n→ℝ)
  (past:∀i:ℕ,Config G (R.family.side i per)→Marker.Poly (Stock.census (Fin n)))
  (reg:Registered (K:=j+1+1) (per:=per) (draw:=draw) (rate:=rate) (allowance:=allowance)
    (fun _:Fin n=>0) P school day tape (WilsonReceivedCanonicalSocketSeed.present lens)
    (fun i=>WilsonReceivedCanonicalSocketSeed.contact (lens i)) pt q x j base ((Nat.lt_succ_self j).trans cut)
    y bills (past (j+1)))
local notation "cells" => (onLevels draw tape)
local notation "Mₗ" => reg.matter
local notation "lowOrder" => (ask).order
local notation "lowShelf" => (ask).shelf
local notation "rawHigh" => (past (j+1+1))
local notation "o" => WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per y cells

local notation "H" => (day.Ψ per) ((j+1)+1)
local notation "scale" => Poetry.Agenda.seed (roots semester R simple) MintClock.splits (Burn.horizon (ask).vac) (R.alloy.B.a.clock.J ((j+1)+1))
local notation "M" => row R d q hd o scale
local notation "A" => room (Fin n)
local notation "K₀" => (fun _:(Fin n)=>(⊥:Submodule ℝ ℂ))
local notation "marks" => Stock.census (Fin n)
local notation "w₀" => (fun _:(Fin n)=>(1:ℝ))
local notation "C₀" => charge R d q scale w₀
local notation "g" => Coat.gStep (H).beta
local notation "D₀" => (∑v:(Fin n),d v)+1
local notation "χ" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "S₀" => (fun _:(Fin n)=>max 1 (C₀))
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonOriginalCensusCanonicalAngularMenu (repeated plottedLow)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonNeutralTwoPrintPathBoxHome (breadth)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonOriginalCensusFaceSites (binder port)
open WilsonOriginalCensusFaceSheet (Addressed)
open FundedMarkedPathSelection (output)
open WilsonReceivedFixedDigitCanonical (fixed)

open Comparison.Density.Transport
open WilsonOriginalCensusCanonicalFirstEdgePayer (Source)
local notation "source" t:max => Source R day.hk (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per) school.books base op (day.lessons (j+1) (Nat.le_succ_of_le base) cut) school.ahead d q hd y cells (ask).order (ask).shelf t



local notation "clock" => R.alloy.B.a.clock
local notation "Hhat" => (clock).hatBeta (j+1)
local notation "σₗ" => Poetry.Agenda.seed (roots semester R simple) MintClock.splits (Burn.horizon (ask).vac) ((clock).J (j+1))
local notation "sideₗ" => coarse R (j+1) per
local notation "geom" => binder (sideₗ) y
variable {rentLimit tol:ℝ}
    (origin : WilsonOriginalCensusCanonicalFirstEdgePayer.Source R day.hk (roots (WilsonOriginalOpticalSchedule.prepared schedule) R simple)
      (tab (WilsonOriginalOpticalSchedule.prepared schedule) R simple) day.π day.Γ (day.Ψ per) school.books base op (day.lessons (j+1)
      (Nat.le_succ_of_le base) cut) school.ahead d q hd y (onLevels draw tape) (programme d (fun _ : Fin n=>0) P).order (programme d (fun _ : Fin n=>0) P).shelf rentLimit)
  (same : ∀U, ((((day.Ψ per) (j+1+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (row R d q hd (WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per y (onLevels draw tape)) (Poetry.Agenda.seed (roots (WilsonOriginalOpticalSchedule.prepared schedule) R simple) MintClock.splits (Burn.horizon (programme d (fun _ : Fin n=>0) P).vac) (R.alloy.B.a.clock.J ((j+1)+1)))) (Coat.gStep ((day.Ψ per) (j+1+1)).beta) x U))=(past (j+1+1)) U)

local notation "high" => WilsonOriginalCensusCanonicalTranslatedPayer.named R day.hk (roots semester R simple) (tab semester R simple) day.π day.Γ (day.Ψ per) school.books base
  op (day.lessons (j+1) (Nat.le_succ_of_le base) cut) school.ahead d q hd y cells (ask).order (ask).shelf origin x rawHigh same
local notation "bill" => WilsonIndependentCollarMaterialWallet.bill Mₗ bills
local notation "lowCash" => fun v=>bills v*max 1 (WilsonOriginalMixedBlockBudget.roots
  (geom) (bill))
local notation "loRaw" => WilsonAddressedPublicFirstLower.value R (N:=N) (j:=j+1) (per:=per) d y ((day.Ψ per) (j+1)) Mₗ x
local notation "power₀" => ((∑v:Fin n,d v)+1+5)*Fintype.card (Fin n)
local notation "peak" c:max => 3*WilsonOriginalFullRosterBookedHearing.roof d d (fun _ : Fin n=>4) c
local notation "bound" => max ((2:ℝ)^((ask).order+(ask).shelf+1)) ((2:ℝ)^(lowOrder+lowShelf+1))

local notation "charges" => fun _ : Fin n=>4
local notation "rk" => (∑v:Fin n,d v)+1
local notation "home" => ((Passport.point (o)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "gAt" b:max => Pert.Asymptotics.regulatorRun R.family N per b
include origin same in
theorem original     (tags : ∀b:Covers R.family.path.levels.S (j+1) (sideₗ),(step R (j+1) b.val).Choices)
    (rentOrder precision target breadthCap : ℕ)
    (fit : (ask).order ≤ Burn.horizon (ask).vac+1)(shelved : (ask).shelf ≤ (clock).J (j+1))
    (count : op.count ≤ Burn.horizon (ask).vac+2)(depth : 2*rentOrder+8 ≤ (ask).order)(age : rentOrder+3 ≤ 3*(ask).vac+2)
    (ready : WilsonReceivedMeasuredStampPrice.opening R simple rentOrder (ask).order (ask).vac depth age
      (by norm_num:0<(1:ℝ)) ≤ j+1)
    (loDepth : lowOrder ≤ (clock).J (j+1))(loShelf : lowShelf ≤ (clock).J j)
    (loSeats : (ask).school.pieces ≤ Burn.horizon (ask).vac+2)
    (halo : (eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    (income : (eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1)
    (upperWidth : scale ≤ 1)
    (sold : (eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop
      (max 1 (WilsonOriginalCensusCanonicalRows.ceiling R d 1)))).choose ≤ j+1)
    (rent : rentLimit ≤ (Pert.Asymptotics.regulatorRun R.family N per (j+1+1))^rentOrder)
    (tube : LinkTube G)(front : (t:Multi.Hot (marks)) → t.val.val)
    (teacher : 0<σₗ ∧ Real.exp ((σₗ)⁻¹^2)≤(Hhat) ∧
      (((day.Ψ per) (j+1)).p.supportExponent+2)*((((day.Ψ per) (j+1)).p.B:ℝ)⁻¹)≤(σₗ)/2 ∧
      (Real.sqrt ((day.Ψ per) (j+1)).beta)⁻¹≤1/2 ∧ ((day.Ψ per) (j+1)).p.B=Nat.ceil ((Real.log (Hhat))^2) ∧
      ((day.Ψ per) (j+1)).p.supportExponent+2≤102)
    (accuracy : 2*(precision+1) ≤ target) (highCap : peak target ≤ (ask).order)(lowCap : peak target ≤ length)
    (menu : WilsonOriginalCensusCanonicalRelativePeriodSchedule.Appointment R simple d lens pt
      (fun _ : Fin n=>4) tube (ask).order lowOrder target precision accuracy)
    (go : menu.first ≤ j+1)(board : menu.period (j+1) breadthCap ≤ per)
    (near : ∀t : Multi.Hot (marks), breadth t.val.val (front t).val 0
      (relative t.val.val (front t).val y) ≤ breadthCap)
    (pieces:op.count=(ask).school.pieces)
    (s:(marks).Mode){u b geomCost p roomSize:ℕ}{η:ℝ}(ep:0<η)(tp:0<tol)
    (two:2≤(bound))
    (late:(eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask (charges) P
      geomCost p target (bound) tol η two tp ep)).choose ≤ b)
    (floorOld:WilsonSingleHardRadius.first R simple ≤ m)(oldEar:m ≤ u)(ub:u≤b)(bj:b≤j)
    (geo:R.family.S.a b/R.family.S.a (j+1+1)≤(R.family.path.levels.clock.hatBeta b)^geomCost)
    (np:0<n)
    (cash:work n P (fare d (charges)) (rk)+1+(WilsonOriginalFullRosterCouplingClock.wallet (fare d (charges))).pole+1 ≤ rentOrder)
    (jet:work n P (fare d (charges)) (rk)+1+1≤precision)
    (regular:work n P (fare d (charges)) (rk)+2≤p)
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(held:center∈Z)
    (homes:∀i∈s.val,sites R (home) (Nat.le_succ_of_le bj) i∈Z)
    (roof:coverNumber ((day.Ψ per) b).p.B Z ≤ roomSize) :
  (∃hi : WilsonOriginalDatedCensusInput.Filed (N:=N) R day.hk (roots semester R simple)
      (tab semester R simple) day.π day.Γ (day.Ψ per) school.books (Nat.le_succ_of_le base)
      school.ahead (S₀) (power₀) (past (j+1+1)),
    ∃lo : WilsonOriginalDatedCensusInput.Filed (N:=N) R day.hk (roots semester R simple)
      (tab semester R simple) day.π day.Γ (day.Ψ per) school.books base
      school.ahead (lowCash) (power₀) (past (j+1)),
    WilsonReceivedChronologicalTwoFlatSale.Sale R simple day.hk (roots semester R simple) (tab semester R simple)
      day.π day.Γ (day.Ψ per) school.books base school.ahead past hi lo u b s P roomSize η) ∧
  ∀e, u≤e → (eb:e≤b) →
      ‖WilsonOriginalJointTrialHearing.read R N per (1:Config G (R.family.side e per))
          ((eb.trans bj).trans (Nat.le_add_right j 2)) rawHigh s-
        WilsonOriginalJointTrialHearing.read R N per (1:Config G (R.family.side e per))
          (Nat.le_succ_of_le (eb.trans bj)) (past (j+1)) s‖≤
        WilsonReceivedChronologicalLastFlat.wage s P roomSize η*(gAt b)^P := by
  classical
  obtain ⟨test,lives,fixed,rowAt,positive,wages,opL,counted,_stages,file⟩:=WilsonAddressedPublicFirstLedger.original
    (fun _:Fin n=>0) P school day tape pt q x base ((Nat.lt_succ_self j).trans cut) y bills (past (j+1)) reg
  have funded:=WilsonAddressedPublicFirstReceived.original R simple d (ask) school day base cut op q hd y (cells)
    origin x (rawHigh) same opL (length) (lowOrder) (lowShelf) bills (Mₗ) past (file tol tp) wages pt lens test
    lives fixed tags rentOrder precision target breadthCap fit shelved count depth age ready loDepth loShelf
    (counted.le.trans loSeats) halo income upperWidth sold rent tube front teacher accuracy highCap lowCap
    menu go board near (fun v=>(positive v).le) pieces s ep tp two late floorOld oldEar ub bj geo np cash jet
    regular support section_ group Z center held homes roof
  have stored (i:ℕ):Function.update past i (past i)=past:=by
    funext k
    by_cases h:k=i
    · subst k
      exact Function.update_self i (past i) past
    · exact Function.update_of_ne h (past i) past
  let posted (history:∀i:ℕ,Config G (R.family.side i per)→Marker.Poly (Stock.census (Fin n))):Prop:=
    (∃hi : WilsonOriginalDatedCensusInput.Filed (N:=N) R day.hk (roots semester R simple)
      (tab semester R simple) day.π day.Γ (day.Ψ per) school.books (Nat.le_succ_of_le base)
      school.ahead (S₀) (power₀) (history (j+1+1)),
    ∃lo : WilsonOriginalDatedCensusInput.Filed (N:=N) R day.hk (roots semester R simple)
      (tab semester R simple) day.π day.Γ (day.Ψ per) school.books base
      school.ahead (lowCash) (power₀) (history (j+1)),
    WilsonReceivedChronologicalTwoFlatSale.Sale R simple day.hk (roots semester R simple) (tab semester R simple)
      day.π day.Γ (day.Ψ per) school.books base school.ahead history hi lo u b s P roomSize η)
  let patched:=Function.update (Function.update past (j+1) (loRaw)) (j+1+1) (past (j+1+1))
  have issued:posted patched:=funded.1
  have joined:patched=past:=by
    dsimp only [patched]
    rw [←rowAt,stored (j+1),stored (j+1+1)]
  refine ⟨(congrArg posted joined).mp issued,?_⟩
  intro e ue eb
  have received:=funded.2 e ue eb
  rw [rowAt]
  exact received

end YM.Integration.WilsonAddressedPublicFirstSocket
end
