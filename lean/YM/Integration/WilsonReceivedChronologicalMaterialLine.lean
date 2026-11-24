import YM.Integration.WilsonOriginalCensusAttendancePair
import YM.Integration.WilsonReceivedChronologicalMaterialRoster

/-! From the recorded dated grant, elect each real mixed input once for the entire interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialLine
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
open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding
open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series
open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead
open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)
open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram
open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonIndependentCollarAddressedSource (Submitted)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedCoverGrade (Same)
open WilsonOriginalCensusDatedMaterial (words)
open WilsonVacuumPreResetStationaryChange (fine coarse)

open WilsonIndependentCollarMaterialHearing (Mounted)
open WilsonOriginalCensusFaceSchools (Account)
open WilsonOriginalMixedBlockRows (room)
open WilsonReceivedDepositedOrbitalLedger (book)

open WilsonOriginalCensusPublicationClock WilsonOriginalCensusMaterialPosting
open MintClock VowsR


open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
variable {G:Gauge}{s:WilsonOriginalAllOrderCourse.Schedule G}{R:Run G}{simple:G.Simple}
variable {n q p N per m K j:ℕ}{k D:Fin n → ℕ}
variable (room:WilsonOriginalCensusPhysicalAttendance.Room s R simple)
  (ask:Demand q p k)
variable (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)
  (hk:Burn.horizon ask.vac+2 ≤ (R.alloy.B.a.clock).J m)
  (lessons:∀i,∀(hi:m ≤ i),i < N → Lesson (N:=N) R hk (WilsonOriginalCensusPhysicalAttendance.roots s R simple) (WilsonOriginalCensusPhysicalAttendance.tab s R simple) π Γ hi)
  (Ψ:(i:ℕ) → RG.Rep G (R.family.side i per))
  (record:Receives s R simple ask.school π Γ hk lessons Ψ)
  (young:m ≤ j)(live:j+1 < N)
variable {V:Realm G (q+1) Credit.leanC}{draw:V.draws=R.family.path.levels}{rate δ:ℝ}


local notation "teacher" => WilsonOriginalCensusPhysicalAttendance.roots s R simple
local notation "width" i:max => Poetry.Agenda.seed (teacher) MintClock.splits (Burn.horizon ask.vac) (R.alloy.B.a.clock.J ((i:ℕ)+1))
local notation "gate" i:max => Open R simple k ask.school.pieces (ask.school.order+1) ask.load i

def Sales (K:ℕ)(rate δ:ℝ):Prop:=
  ∀j:ℕ,∀(hj:m ≤ j),∀(_reach:j+3 ≤ K),∃(live:j+1<N),∃gates:((gate j)∧(gate (j+1))),
    WilsonOriginalCensusAttendancePair.Sold (K:=K) (D:=D) (V:=V) (draw:=draw) (rate:=rate) (δ:=δ)
      room ask π Γ hk lessons Ψ hj live gates

theorem current (wide:m+3≤K)
    (sales:Sales (D:=D) (V:=V) (draw:=draw) room ask π Γ hk lessons Ψ K rate δ):
    ∀j:ℕ,m≤j→j+2≤K→(gate j)∧Submitted R V draw D k N K j rate δ (width j):=by
  intro j hj reach
  by_cases before:j+3≤K
  · obtain ⟨live,gates,pair⟩:=sales j hj before
    obtain ⟨_,_,_,_,_,_,_,_,_,lower,_⟩:=pair
    exact ⟨gates.1,lower⟩
  · cases j with
    | zero=>omega
    | succ j=>
      obtain ⟨live,gates,pair⟩:=sales j (by omega) (by omega)
      obtain ⟨_,_,_,_,_,_,_,_,upper,_,_⟩:=pair
      exact ⟨gates.2,upper⟩

/-- A shared starting lift and the independently fixed child digit retain all occupied names at every position. -/
def homes (cells:Digits V.draws (Fin n))(ground:Fin n→ Cover)(m:ℕ):ℕ→Fin n→ Cover
  | 0 => ground
  | a+1 => chartIn (loose V.draws (m+a+1)) (homes cells ground m a) (cells (m+a+1))

include record in
theorem original (wide:m+3≤K)(active:K≤N)
    (sales:Sales (D:=D) (V:=V) (draw:=draw) room ask π Γ hk lessons Ψ K rate δ)
    (cells:Digits V.draws (Fin n))(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(seed:(v:Fin n)→Choice R k v)
    (ground:Fin n→ Cover)(t:Case D)(deep:∀s:Hot (Stock.census (Fin n)),0 < mass k s.val.val):
    let z:=fun j:ℕ=>homes cells ground m (j-m)
    ∃H:(a:↥(Ico m (K-1)))→Material R N (a.val+1) q k (width a.val)
       (binder (R.family.side (a.val+1) per) (z a.val)),
      ∀a:↥(Ico m (K-1)),
        WilsonReceivedChronologicalMaterialRoster.Filed (K:=K) (draw:=draw) (rate:=rate) (δ:=δ) cells κ pt seed _ (z a.val) t (H a) ∧
        ∃(op:Mentor.Opportunity (R.alloy.B.a.clock.J (a.val+1)) (R.alloy.B.a.clock.J a.val)),
          ∀(w:Fin n→ℝ), (∀v,0<w v)→∀tol:ℝ,0<tol→
          WilsonOriginalCensusMaterialPosting.Posted R hk (teacher) (WilsonOriginalCensusPhysicalAttendance.tab s R simple)
            π Γ Ψ room.books (mem_Ico.mp a.property).1 op (lessons a.val (mem_Ico.mp a.property).1 (by have h:=(mem_Ico.mp a.property).2;omega)) room.ahead
            (port (R.family.side (a.val+1) per) (z a.val)) (binder _ (z a.val)) k ask.order ask.shelf q w (H a) tol:=by
  intro z
  have stages:=current room ask π Γ hk lessons Ψ wide sales
  obtain ⟨H,declared⟩:=WilsonReceivedChronologicalMaterialRoster.original (rate:=rate) (δ:=δ) cells κ pt seed t per
    (fun j=>width j) z deep (fun j h h'=> (stages j h h').2)
  refine ⟨H,?_⟩
  intro a
  have young:=(mem_Ico.mp a.property).1
  have past:=(mem_Ico.mp a.property).2
  have alive:a.val+1<N:=by omega
  have gates:=(stages a.val young (by omega)).1
  obtain ⟨⟨cal⟩,_,op,_,seats,stage,_,_⟩:=record.2.2.2 a.val young alive
  refine ⟨declared a,op,?_⟩
  intro w wp tol tp
  exact WilsonOriginalCensusPublicationLesson.original R simple hk (teacher) (WilsonOriginalCensusPhysicalAttendance.tab s R simple)
    π Γ Ψ record.1 (WilsonPhysicalHistoryPriorAperture.law G MintClock.splits) room.books young (by omega)
    op (lessons a.val young (by omega)) cal room.ahead room.chamber room.hospital
    (port (R.family.side (a.val+1) per) (z a.val)) (binder _ (z a.val)) k ask.order ask.shelf q w (H a)
    ask.school.pieces (ask.school.order+1) p ask.load gates seats stage wp tp room.warm record.2.1 room.pass room.way

end YM.Integration.WilsonReceivedChronologicalMaterialLine
end
