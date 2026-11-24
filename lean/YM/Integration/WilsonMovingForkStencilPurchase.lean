import YM.Integration.WilsonMovingForkStencilHousing
import YM.Integration.WilsonReceivedChronologicalFixedPlaced

/-! The actual original chronology on all occupied stencils at a purchased moving fork. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMovingForkStencilPurchase
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
open scoped Classical
variable {G:Gauge}{R:Run G}{simple:G.Simple}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
  {n m N per:ℕ}{grades:Fin n → ℕ}(power:Fin n → ℕ)(P:ℕ)(house:Room (prepared schedule) R simple)
  (day:Day (prepared schedule) R simple (programme grades power P).school m N)
  {dims:Fin n → ℕ}{V:Realm G ((terms grades power P).order+1) Credit.leanC}
  {draw:V.draws=R.family.path.levels}{rate allowance:ℝ}(κ:(v:Fin n) → Knob (dims v))
  (pt:Fin n → Chamber)(top first:ℕ)(valid:top ≤ N)(toll:ℕ → Fin n → ℝ)(old:m ≤ first)

local notation "bill₀" => terms grades power P
local notation "ask₀" => programme grades power P

def Purchased (caps:Fin n → ℝ)(A target:ℕ)(η:ℝ):Prop:=
  ∀(ξ:Fin n → Site (R.family.side top per))(seed:(v:Fin n) → Choice R grades v)
    (test:Case dims), (∀v,‖test v‖ ≤ caps v) →
  let tape:=WilsonMovingForkStencilHousing.cells draw ξ
  ∃granted:Cohort (K:=top) (per:=per) (draw:=draw) (rate:=rate) (allowance:=allowance) power P house day
      tape test κ pt seed 0 toll old valid,
    ∀(active:first+1 ≤ top), (∀i,WilsonReceivedChronologicalMaterialSites.physical R ξ active i=0) →
    ∀(wallet:Wallet (room (Fin n)))(other:(i:ℕ) → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))
      (_forests:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),Forest (step R (j+1) u.val).ratio)
      (_chosen:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),(step R (j+1) u.val).Choices)
      {df:ℕ}{frame:Frame G df}, SectionData frame → Hol G →
    let rows:=printed power P house day tape test κ pt seed wallet 0 toll old valid granted other
    Earned (power:=power) (P:=P) (house:=house) (day:=day) (top:=top) (rows:=rows) m (first+1) target (2*A) η

theorem original(caps:Fin n → ℝ)(nonneg:∀v,0 ≤ caps v)(wide:first+3 ≤ top)
    (classroom:∀(cells:Digits V.draws (Fin n))(seed:(v:Fin n) → Choice R grades v)(test:Case dims),
      (∀j∈Finset.Ico first (top-1),∀v,‖test v‖ ≤ caps v*(R.family.path.levels.clock.hatBeta (j+1))^(power v)) →
      Cohort (K:=top) (per:=per) (draw:=draw) (rate:=rate) (allowance:=allowance) power P house day
        cells test κ pt seed 0 toll old valid)
    {Z₀:ℕ → SeriesA G}{price:Credit}(quiet:QuietAt day price Z₀)
    {Types:Type}[Fintype Types]{purchased pieces physical:ℕ}{pole:Bool → ℕ}{span:Types → ℕ}{lag:Types → Bool → ℕ}
    (tube:LinkTube G)
    (faculty:∀j≥first,WilsonIndependentCollarDatedTeachers.At schedule R simple V dims grades (Burn.horizon (ask₀).vac)
      purchased allowance tube pieces physical pole span lag j)(anchor:V.anchor ≤ first)
    (sparse:WilsonOriginalCensusSparseRosterOpening.first R simple tube grades grades (charges power)
      (bill₀).order (bill₀).order (bill₀).target (bill₀).precision (bill₀).enough ≤ first)
    (admitted:Period (R:=R) (per:=per) (V:=V) (grades:=grades) power P κ pt top first caps)
    (fixed:WilsonSingleHardRadius.first R simple ≤ m)(np:0 < n)(A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)
    (bought:start grades power P R simple (2*A) tol η tp ep ≤ first)
    (mesh:(eventually_atTop.mp (WilsonReceivedChronologicalFixedAperture.original R simple A)).choose ≤ first)
    (spanFit:R.family.S.scale top-R.family.S.scale first ≤ (A:ℝ)*(1+Real.log (R.family.path.levels.clock.hatBeta (first+1))))
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    (clocked:(WilsonReceivedChronologicalDates.stages R simple (2*A)).choose ≤ first)(target:ℕ)(extra:P=target+1):
    Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance) power P house day κ pt top first
      valid toll old caps A target η:=by
  intro ξ seed test paid tape
  have funded (j:ℕ)(_h:j∈Finset.Ico first (top-1))(v:Fin n):‖test v‖ ≤ caps v*(R.family.path.levels.clock.hatBeta (j+1))^(power v):=by
    apply (paid v).trans
    exact le_mul_of_one_le_right (nonneg v) (one_le_pow₀ (R.family.path.levels.fits.delayed _).le)
  let granted:=classroom tape seed test funded
  refine ⟨granted,?_⟩
  intro active located wallet other forests chosen df frame section_ group
  have aperture:=(eventually_atTop.mp (WilsonReceivedChronologicalFixedAperture.original R simple A)).choose_spec first mesh top spanFit
  apply WilsonReceivedChronologicalFixedCohortFee.original (j:=first) (R:=R) (simple:=simple) (schedule:=schedule)
    (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=day)
    (first:=first) (digits:=tape) (test:=test) (κ:=κ) (pt:=pt) (top:=top) (seed:=seed) (wallet:=wallet)
    (valid:=valid) (toll:=toll) (old:=old) (granted:=granted) (other:=other) quiet tube
    (fun s=>s.property.choose) (fun s=>s.property.choose_spec) faculty anchor sparse (Nat.le_succ _) active
    le_rfl (old.trans (Nat.le_succ _)) caps paid ?_ forests chosen section_ group fixed np (2*A) tol η tp ep
    (by omega) aperture support (WilsonMovingForkStencilHousing.original draw ξ active located) (by omega) target extra
  intro j hj
  have h:=Finset.mem_Ico.mp hj
  exact WilsonReceivedChronologicalFixedPorts.entered (digits:=tape) (V:=V) (power:=power) (P:=P)
    (R:=R) (per:=per) (κ:=κ) (pt:=pt) (top:=top) (first:=first) caps admitted ⟨j,Finset.mem_Ico.mpr ⟨by omega,by omega⟩⟩

end YM.Integration.WilsonMovingForkStencilPurchase
end
