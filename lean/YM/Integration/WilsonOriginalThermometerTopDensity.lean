import YM.Integration.WilsonOriginalBarePhysicalLog
import YM.Integration.WilsonOriginalThermometerGradedPalette
import YM.Integration.WilsonThermometerCourseHearing
import YM.QuadraticLocal.Class.Foundry

/-! The native bare registration at the common cutoff of all three physical fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerTopDensity
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof MergeProof.East MergeProof.Accent Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonThermometerCourseIntake
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G)
local notation "J" => Stock.census (Fin 3)

def primitive (A:Group R.family 6) (N p:ℕ) (o:Fin 3→Site (R.family.side N p)) (σ:ℝ) :=
  let g:=Pert.Asymptotics.regulatorRun R.family N p N
  let a:=R.family.path.rep N p N
  WilsonOriginalStarGradedScene.words R levels o σ g a.p.threshold (coordinates R A N N p) probe
    WilsonOriginalThermometerGradedPalette.positive

theorem raw (A:Group R.family 6) (i p:ℕ) (o:Positions (Fin 3) (R.family.side (i+1) p))
    (refs:∀j,R.family.ref (levels j) ≤ (i + 1)) (σ:ℝ) (x:Wallet disks) (U:Config G (R.family.side (i+1) p)) :
    let N:=i+1
    let g:=Pert.Asymptotics.regulatorRun R.family N p N
    Spill.Foundry.uncut (primitive R A N p o.origin σ) g x U=
      ∑j:Fin 3, Poly.send ((J).fire j) (probe j x * R.family.O N p
        (A.station.wheel.atCut (N,p) (index A (grade j)) (vector A univ j)) (o.origin j) U) := by
  intro N g
  let a:=R.family.path.rep N p N
  let L:=rendered (primitive R A N p o.origin σ) a.p g
  change WilsonRootedKioskOccupiedSlip.bare L x U=_
  rw [WilsonOriginalBareMarkedSheet.restore]
  exact WilsonOriginalBarePhysicalLog.birth R levels N p o.origin σ
    (fun j=>A.station.wheel.atCut (N,p) (index A (grade j)) (vector A univ j)) probe
    WilsonOriginalThermometerGradedPalette.positive refs x U

theorem offered (A:Group R.family 6) (simple:G.Simple) (i p:ℕ) (o:Positions (Fin 3) (R.family.side (i+1) p))
    (refs:∀j,R.family.ref (levels j) ≤ (i + 1)) (σ:ℝ) (x:Wallet disks) (U:Config G (R.family.side (i+1) p)) :
    let N:=i+1
    let g:=Pert.Asymptotics.regulatorRun R.family N p N
    ((R.family.path.rep N p N).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (primitive R A N p o.origin σ) g x U)=
      WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self i) o x U := by
  intro N g
  rw [raw R A i p o refs σ x U]
  change _=Poly.inject (fun s=>(∏j∈s.val,(x j).val)*(incoming R A simple (show N≤N from le_rfl) o U).part s)
  unfold incoming
  rw [gust_base, WilsonPositionThermometerDepositedFaces.entered R simple N p A.station
    (fun j=>index A (grade j)) (vector A univ) o refs]
  ext s
  have get (f:(J).Mode→ℂ) : (Poly.inject f).part s=f s:=rfl
  simp only [get,N,MergeProof.Accent.birth,Poly.part_smul,Mach,Extra.Trajectories.pass_fire,
    Finset.prod_mul_distrib,probe,WilsonPositionThermometerDepositedFaces.leg]
  ac_rfl

end YM.Integration.WilsonOriginalThermometerTopDensity
