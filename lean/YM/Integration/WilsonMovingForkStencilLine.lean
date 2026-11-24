import YM.Integration.WilsonMovingForkStencilPurchase
import YM.Integration.WilsonMovingForkRegisteredMaterial
import YM.Integration.WilsonReceivedChronologicalSocket

/-! Complete selected chronological stencils on the actual planted physical sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMovingForkStencilLine
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonThermometerDeclaredSeeds
open Comparison.Density.Transport
open ComparisonDensity.Address
open WilsonReceivedChronologicalFixedLedger (Registered before)
open WilsonReceivedChronologicalSocket (extend lit input)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonMovingForkStencilPurchase (Purchased)
open WilsonMovingForkStencilHousing (cells)
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkDepositedPrint (Sheet board polynomial)
open WilsonOriginalTwoFlatIRMounted (value)
open MeasureTheory Pert.Asymptotics
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Comparison.Density.Transport
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonCoeffUV.Bank.Ticket
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonOriginalCensusPhysicalAttendance (Room)
open WilsonOriginalCensusFundedAttendance (Demand)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonOriginalOpticalSchedule (prepared)
open WilsonOriginalCensusFundedAttendance (quote)
open WilsonReceivedChronologicalFixedEarner (programme start)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedChronologicalFixedReserve (terms charges)
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open WilsonReceivedChronologicalFixedEnrollment (Cohort)
open WilsonReceivedChronologicalFixedProgram (printed)
open WilsonReceivedChronologicalFixedPorts (Period)
open WilsonReceivedChronologicalFixedCohortFee (Earned)
open OriginalIssuedMarkedRows
open WilsonOriginalMixedBlockRows (room)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonThermometerDeclaredSeeds
open Comparison.Density.Transport
open ComparisonDensity.Address
open WilsonReceivedChronologicalFixedLedger (Registered before)
open WilsonReceivedChronologicalSocket (extend lit input)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonMovingForkStencilPurchase (Purchased)
open WilsonMovingForkStencilHousing (cells)
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkDepositedPrint (Sheet board polynomial)
open WilsonOriginalTwoFlatIRMounted (value)
open MeasureTheory Pert.Asymptotics
open scoped Classical
variable {G:Gauge}{R:Run G}{simple:G.Simple}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
  {n m N per:ℕ}{grades:Fin n → ℕ}(power:Fin n → ℕ)(P:ℕ)(house:Room (prepared schedule) R simple)
  (day:Day (prepared schedule) R simple (programme grades power P).school m N)
  {dims:Fin n → ℕ}{V:Realm G ((terms grades power P).order+1) Credit.leanC}
  {draw:V.draws=R.family.path.levels}{rate allowance:ℝ}(κ:(v:Fin n) → Knob (dims v))
  (pt:Fin n → Chamber)(top first:ℕ)(valid:top ≤ N)(toll:ℕ → Fin n → ℝ)(old:m ≤ first)

local notation "bill₀" => terms grades power P
local notation "ask₀" => programme grades power P

variable {caps:Fin n → ℝ}{A target:ℕ}{η:ℝ}
  (classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
    power P house day κ pt top first valid toll old caps A target η)
  (ξ:Fin n → Site (R.family.side top per))(s:(Stock.census (Fin n)).Mode)(q:Selection R grades s.val)
  (test:Case dims)(paid:∀v,‖test v‖ ≤ caps v)(hd:∀v,0 < grades v)
  (prior:(i:ℕ) → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))(σ:ℝ)

local notation "tape" => cells draw ξ
local notation "seed" => extend R grades s.val q
local notation "ν" => R.family.path.rep N per top
local notation "gK" => regulatorRun R.family N per top
local notation "grant" => (classroom ξ seed test paid).choose
local notation "other" => Function.update prior top (WilsonReceivedChronologicalSocket.input R grades s q hd ξ σ ν gK)
local notation "x₀" => (lit (V:=Fin n))
local notation "rows₀" => printed power P house day tape test κ pt seed x₀ 0 toll old valid grant other

theorem atCut (U:Config G (R.family.side top per)):
    (rows₀ top U).part s=((ν).eval U:ℂ)*word R grades κ pt gK ξ s.val q U:=by
  rw [WilsonReceivedChronologicalFixedProgram.cutoff,Function.update_self]
  exact WilsonReceivedChronologicalSocket.ordinary R grades s q hd ξ σ ν gK κ pt U

theorem earned (active:first+1 ≤ top)(located:∀i,parent R active per ξ i=0)
    (forests:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),Forest (step R (j+1) u.val).ratio)
    (chosen:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),(step R (j+1) u.val).Choices)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G):
    Earned (power:=power) (P:=P) (house:=house) (day:=day) (top:=top) (rows:=rows₀) m (first+1) target (2*A) η:=
  (classroom ξ seed test paid).choose_spec active located x₀ other forests chosen section_ group

theorem pinned (active:first+1 ≤ top)(located:∀i,parent R active per ξ i=0)
    (a:↥(Finset.Ico first (top-1))):
    (WilsonOriginalCensusFaceSites.port (R.family.side (a.val+1) per)
      (WilsonReceivedChronologicalMaterialLine.homes tape 0 first (a.val-first))).origin=
    parent R (by have t:=Finset.mem_Ico.mp a.property;omega:a.val+1 ≤ top) per ξ:=by
  have zero:WilsonReceivedChronologicalMaterialSites.footprint R ξ active=0:=by
    funext i
    change lift (parent R active per ξ i)=0
    rw [located]
    funext k
    simp [lift]
  obtain ⟨i,member⟩:=a
  have range:=Finset.mem_Ico.mp member
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le range.1
  change (WilsonOriginalCensusFaceSites.port _ (WilsonReceivedChronologicalMaterialLine.homes tape 0 first (first+k-first))).origin=_
  rw [show first+k-first=k by omega]
  have val:=WilsonReceivedChronologicalMaterialSites.origin R draw ξ active k (show first+k+1 ≤ top by omega)
  rw [zero] at val
  exact val

def Received {G:Gauge}{R:Run G}{n N per i:ℕ}{z:Fin n → Site (R.family.side i per)}
    (H:Sheet R N i z)(raw:Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n))):Prop:=
  let g:=regulatorRun R.family N per i
  let b:=board H
  Integrable raw (Wilson.prior G _) ∧
  (∀U,raw U=(((R.family.path.rep N per i).eval U:ℝ):ℂ) • value b.binder b.load b.copies g b.wallet U) ∧
  ∀e,WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>(raw U).part e) i le_rfl=(polynomial H g).part e

private theorem transfer {G:Gauge}{R:Run G}{n N per i:ℕ}{z w:Fin n → Site (R.family.side i per)}
    (same:z=w)(H:Sheet R N i z){raw:Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n))}
    (licensed:Received H raw):∃B:Sheet R N i w,Received B raw:=by
  subst w
  exact ⟨H,licensed⟩

theorem filed (active:first+1 ≤ top)(located:∀i,parent R active per ξ i=0)
    (a:↥(Finset.Ico first (top-1))):
    let age:=a.val+1
    let pins:=parent R (by have t:=Finset.mem_Ico.mp a.property;omega:age ≤ top) per ξ
    ∃H:Sheet R N age pins,Received H (rows₀ age):=by
  intro age pins
  obtain ⟨entry,_⟩:=WilsonReceivedChronologicalFixedProgram.registered power P house day tape test κ pt seed
    x₀ 0 toll old valid grant other a
  have registered:=WilsonMovingForkRegisteredMaterial.original power P house day tape test κ pt seed x₀
    a.val (old.trans (Finset.mem_Ico.mp a.property).1) (before valid a) _ _ _ entry
  let H:=WilsonMovingForkPostedMaterial.file entry.matter x₀
  have p:=pinned (m:=m) (N:=N) (power:=power) (P:=P) (first:=first) (top:=top) (draw:=draw) (R:=R) (ξ:=ξ) active located a
  exact transfer p H registered

end YM.Integration.WilsonMovingForkStencilLine
end
