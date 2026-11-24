import YM.Integration.WilsonOriginalObservedRoseHaarProbe
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelBadge
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelMesh
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelHearing
import YM.Integration.WilsonOriginalObservedRoseProbeShelf
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelCell
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelWindow
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelAmplitude
import YM.Integration.WilsonOriginalObservedRoseProbeRead
import YM.Integration.WilsonMeasuredPublicEntranceCellWords
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelPower
import YM.Integration.WilsonOlderFreshSoftRoseMarket

/-! A single original reporting date buys every proper or complete deposited face before both numerical regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPortfolio
open Function Filter Finset Lattice Laurent Bloch Precision Wilson RG Source Labels Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension NativeCurvatureTensor
open OriginalMarkedSourceComet WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftTrialCharge (power bill wages)
open WilsonOriginalPublicTrialInput (vector)
open scoped Classical BigOperators Topology
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor
open WilsonIndependentCollarRootedWidth
open scoped Classical BigOperators Topology
universe u

open WilsonOlderFreshSoftRoseMarket (row Probe)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open WilsonOlderFreshSoftCoveredRead (cost)
open WilsonOlderFreshSoftFigureReading (reading)
open WilsonOlderFreshSoftSocketStationPanelCapital (roster)
open WilsonPositionProgramReportedField (entire)
open WilsonReceivedChronologicalHeldEntrance (coords)
open WilsonOriginalPublicFigureIncome (height)
open WilsonMeasuredPublicEntrancePanel (Panel)
open ActualRunPhysicalPages
open WilsonOlderFreshSoftSocketStationPanelStops (printed)
open WilsonOlderFreshSoftSocketStationPanelPower (loss debt)
open WilsonOlderFreshSoftSocketStationCalendar (date)
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels
local notation "H" k:max => R.family.path.levels.clock.hatBeta k
local notation "Faces" => {t:Finset (Fin 3)//t.Nonempty}

open RG16 RG16.Literal Extra.Histories Extra.Trajectories Extra.Multi Source
open WilsonMeasuredPublicEntranceCellWords (physical)
open WilsonMovingForkHeterogeneousCut (Filed)
open ActualRunPhysicalPages Pert.Asymptotics Extraction Labels
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonOriginalObservedRoseProbeRead (quota)
open WilsonReceivedChronologicalHeldEntrance (coords)
open WilsonPositionProgramReportedField (entire)
open WilsonOlderFreshSoftSocketTotal (figure)
open WilsonOlderFreshSoftRoseMarket (scaled)

open WilsonOlderFreshSoftSocketStationPanelCell (observed terminal)
open WilsonOlderFreshSoftSocketStationPanelMesh (mode Entry high low price)
open WilsonOlderFreshSoftSocketStationScan (Support)
open WilsonMaxwellThermometerNominatedSecant (bill faceKey)
local notation "Face" => Finset (Fin 3)
private theorem inactive (a b:Face→ℂ):bill a b ∅=0:=by
  unfold WilsonMaxwellThermometerNominatedSecant.bill
  apply Finset.sum_eq_zero
  intro i _
  have used:(faceKey i).Nonempty:=by fin_cases i <;> decide
  exact if_neg used.ne_empty.symm


private theorem heat (simple:G.Simple):∀ᶠv:ℕ in atTop,∀N≥v,∀per:ℕ,|regulatorRun R.family N per v|≤1:=by
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 8] with v warm N live per
  change |(Real.sqrt (R.family.path.β N per v))⁻¹|≤1
  rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  apply inv_le_one_of_one_le₀
  apply Real.one_le_sqrt.mpr
  have band:=(R.makes.wilson.represents N per v live).band.1
  change (H v)/2≤R.family.path.β N per v at band
  linarith

open WilsonOriginalObservedRoseHaarProbe (priced)
open WilsonPositionProgramReportedField (entire)
open WilsonReceivedChronologicalHeldEntrance (coords)

def wallet {Y:Type}[Fintype Y](μ:Y→ℂ)(m:Y→Face→ℂ)(z:ℂ)(a b:Y→Face→ℂ)(C:ℝ):ℝ:=
  ∑y:Y,‖μ y‖*‖z‖*(∑s:Face,‖bill (a y) (b y) s‖*‖m y s‖*C)

def reading {Y:Type}[Fintype Y](μ:Y→ℂ)(z:ℂ)(a:Y→Face→ℂ):ℂ:=
  ∑y:Y,μ y*(z*WilsonPositionThermometerConnected.value (a y))

private theorem signed {Y:Type}[Fintype Y](μ:Y→ℂ)(m:Y→Face→ℂ)(z:ℂ)(a b:Y→Face→ℂ)(C:ℝ)
    (cash:∀y s,s.Nonempty →‖a y s-b y s‖≤‖m y s‖*C):
    ‖reading μ z a-reading μ z b‖≤wallet μ m z a b C:=by
  classical
  unfold reading wallet
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro y _
  rw [←mul_sub,←mul_sub,norm_mul,norm_mul,←mul_assoc,
      WilsonMaxwellThermometerNominatedSecant.signed]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro s _
  rw [norm_mul,mul_assoc]
  by_cases occupied:s.Nonempty
  · exact mul_le_mul_of_nonneg_left (cash y s occupied) (norm_nonneg _)
  · have empty:s=∅:=Finset.not_nonempty_iff_eq_empty.mp occupied
    rw [empty,inactive,norm_zero,zero_mul,zero_mul]

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D:Fin 3→ℕ)(e width pow target:ℕ)(A:ℝ)(ap:0≤A):
    let w:=date R width (loss R pow target)
    Tendsto w atTop atTop ∧ ∃gate:ℕ,∀c≥gate,w c≤c ∧ ∀v≥gate,v≤w c →
      ∀(start:ℕ)(opt tol:ℝ)(office:WilsonOriginalObservedRoseProbeShelf.Badge R D e v start opt tol),
      ∀(N per b K:ℕ)(bk:b≤K)(kn:K≤N),c≤K →v+1≤K →R.family.S.a c/R.family.S.a K≤(H c)^width →
      R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (H (v+1))) →
      ∀(req step:ℕ)(B:ℝ)(Y:Type)[Fintype Y]
        (panel:Y→Panel R grade N per b K bk kn req pow step B)(file:Filed R grade K),
      (∀y,(panel y).slot=file.station) →(∀y,(panel y).axis=file.A N per) →
      ∀(port:(y:Y)→(s:Face)→Probe D office.field s)(μ:Y→ℂ)(z:ℂ)(m:Y→Face→ℂ)(q:ℕ),q≤e →
      let θ:=regulatorRun R.family N per v
      let g:=regulatorRun R.family N per K
      let x y:=fun i=>entire R (grade i) K (N,per) (votes R grade (N:=N) (per:=per) file (panel y).names (panel y).turn i)
      let old (y:Y)(s:Face):=m y s*priced R D office.field s N K c v (port y s) g (x y) q θ
      let stopped (y:Y)(s:Face):=m y s*row (R:=R) D office.field s N K c (w c) v (port y s) g (x y) q θ true
      let income:ℝ:=(max 1 B)^3*(2:ℝ)^debt R pow*g^target
      ‖reading μ z old-reading μ z stopped‖≤wallet μ m z old stopped income:=by
  classical
  obtain ⟨cofinal,gate,book⟩:=WilsonOlderFreshSoftSocketStationPanelWindow.original R simple slow D e width pow target A ap
  obtain ⟨cutoff,hot⟩:=eventually_atTop.mp (heat R simple)
  refine ⟨cofinal,max gate cutoff,?_⟩
  intro c late
  obtain ⟨capped,roll⟩:=book c ((le_max_left ..).trans late)
  refine ⟨capped,?_⟩
  intro v warm vw stage opt tol office N per b K bk kn ck vk gear span req step B Y _ panel file station axes port μ z m q kept
    θ g x old stopped income
  apply signed
  intro y s active
  dsimp only [old,stopped]
  rw [←mul_sub,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [←WilsonOriginalObservedRoseHaarProbe.original R D office.field s N K c v (port y s) g (x y) q θ office.paid (date R width (loss R pow target) c)]
  have temp:=hot v ((le_max_right ..).trans warm) N ((vk.trans kn).trans' (Nat.le_succ v)) per
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le bk
  have own:(x y)=printed R kn (panel y):=by
    funext i
    dsimp only [x]
    unfold printed WilsonOriginalObservedRoseCorrectedWords.votes coords
    rw [←station y,←axes y]
    rfl
  rw [own]
  exact roll v ((le_max_left ..).trans warm) vw office.field office.date.le office.draw office.paid office.quiet
    (fun s=>office.proper s.val) N per b n kn ck vk gear span req step B (panel y) s active (port y s) q kept θ temp

end YM.Integration.WilsonOlderFreshSoftSocketStationPortfolio
end
