import YM.Integration.WilsonOriginalThermometerTopDensity
import YM.Integration.WilsonPositionThermometerDepositedFaces
import YM.Integration.WilsonOriginalAlternativeHearing

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeBarePorts
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof MergeProof.East MergeProof.Accent Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonThermometerCourseIntake
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G)
local notation "J" => Stock.census (Fin 3)


open Extra.Trajectories MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums RG05Readout.Records
open YM.FVA1 MeasureTheory
open WilsonOriginalAlternativeHearing
variable (d:Fin 3→ℕ) (positive:∀j,0<d j) (N p:ℕ)
    (y:∀j,R.family.book.Ref (d j)) (o:Fin 3→Site (R.family.side N p))

def words (σ:ℝ):=
  let g:=Pert.Asymptotics.regulatorRun R.family N p N
  let a:=R.family.path.rep N p N
  WilsonOriginalStarGradedScene.words R d o σ g a.p.threshold
    (fun j=>Price.awake R.family (d j) N N p (y j)) probe positive

def offer (x:Wallet WilsonThermometerCourseHearing.disks) :=
  birth (J) (R.family.path.rep N p N) (fun j U=>probe j x * R.family.O N p (y j) (o j) U)

theorem entered (ref:∀j,R.family.ref (d j)≤N) (σ:ℝ)
    (x:Wallet WilsonThermometerCourseHearing.disks) (U:Config G (R.family.side N p)) :
    let g:=Pert.Asymptotics.regulatorRun R.family N p N
    ((R.family.path.rep N p N).eval U:ℂ) • Poly.pass
      (Spill.Foundry.uncut (words R d positive N p y o σ) g x U)=offer R d N p y o x U := by
  intro g
  apply congrArg (fun z:Poly (J)=>((R.family.path.rep N p N).eval U:ℂ) • Poly.pass z)
  let L:=rendered (words R d positive N p y o σ) (R.family.path.rep N p N).p g
  change WilsonRootedKioskOccupiedSlip.bare L x U=_
  rw [WilsonOriginalBareMarkedSheet.restore]
  exact WilsonOriginalBarePhysicalLog.birth R d N p o σ y probe positive ref x U

theorem paid (x:Wallet WilsonThermometerCourseHearing.disks){k:ℕ}(high:k≤N):
    Integrable (gust R.family.path N p N (offer R d N p y o x) k high) (prior G _):=by
  apply gust_live _ _ _ _ _ _ high
  have price:Continuous (R.family.path.rep N p N).eval:= by
    rw [show (R.family.path.rep N p N).eval=_ from (R.makes.wilson.starts N p).2]
    exact bare_cont _
  have earned:=hatCont R.family N p
    (fun j U=>probe j x*R.family.O N p (y j) (o j) U)
    (fun j=>continuous_const.mul (R.family.continuousO N p (d j) _ _)) price (J)
  exact earned.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem actual (x:Wallet WilsonThermometerCourseHearing.disks) {f k:ℕ}(high:k≤N)(lower:f≤k)(s:(J).Mode):
    held R.family N p (fun U=>(gust R.family.path N p N (offer R d N p y o x) k high U).part s) lower =
      actualTransport R.family (N:=N)
        (fun U=>∏j∈s.val,probe j x*R.family.O N p (y j) (o j) U) (lower.trans high):=by
  let g:=fun U=>∏j∈s.val,probe j x*R.family.O N p (y j) (o j) U
  have bill:=paid R d N p y o x (Nat.le_refl N)
  rw [gust_base] at bill
  have parts:=pushpart high (offer R d N p y o x) s bill
  have base(U):((offer R d N p y o x) U).part s=(R.family.path.rep N p N).eval U • g U:=by
    unfold offer birth Mach
    rw [Poly.part_smul,pass_fire,Complex.real_smul]
  have face(U): (gust R.family.path N p N (offer R d N p y o x) k high U).part s=
      (R.family.path.rep N p k).eval U • actualTransport R.family (N:=N) g high U :=by
    rw [congrFun parts U,actualTransport_unnormalize R.family R.makes (le_refl N)]
    simp_rw [base]
  have cancel:(fun U:Config G (R.family.side k p)=>((R.family.path.rep N p k).eval U)⁻¹ •
      (gust R.family.path N p N (offer R d N p y o x) k high U).part s)=
      actualTransport R.family (N:=N) g high:=by
    funext U
    have pos:0<(R.family.path.rep N p k).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson high U
    rw [face U,smul_smul,inv_mul_cancel₀ pos.ne',one_smul]
  rw [normalized R.family N p R.makes high,cancel]
  exact actualTransport_tower R.family R.makes (Nat.le_refl N) g high lower

end YM.Integration.WilsonOriginalAlternativeBarePorts
