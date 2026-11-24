import YM.Integration.WilsonOriginalThermometerTopGrading
import YM.Integration.WilsonThermometerWardCutoffIncome

/-! The chosen microscopic fields with their own measured bare coordinates, on one three-source scene. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardBareScene
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof MergeProof.East MergeProof.Accent Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonOriginalThermometerPalette
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (dim:Fin 3→ℕ) (N p:ℕ) (o:Fin 3→Site (R.family.side N p))
  (v:(j:Fin 3)→R.family.label (dim j))
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "g" => Pert.Asymptotics.regulatorRun (C) N p N
local notation "rep" => (C).path.rep N p N
local notation "coins" => (fun j=>awake (C) (dim j) N N p (v j))

def models (σ:ℝ) (pos:∀j,0<dim j) := WilsonOriginalStarGradedScene.words R dim o σ g (rep).p.threshold
  coins probe pos

def physical (x:Wallet disks) (U:Config G ((C).side N p)) : Poly J :=
  ((rep).eval U:ℂ) • Poly.pass (∑j:Fin 3,Poly.send ((J).fire j) (probe j x*(C).O N p (v j) (o j) U))

theorem offered (σ:ℝ) (pos:∀j,0<dim j) (refs:∀j,(C).ref (dim j)≤N) (x:Wallet disks)
    (U:Config G ((C).side N p)):
    ((rep).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (models R dim N p o v σ pos) g x U)=
      physical R dim N p o v x U :=by
  apply congrArg (fun y:Poly J=>((rep).eval U:ℂ) • Poly.pass y)
  change WilsonRootedKioskOccupiedSlip.bare (rendered (models R dim N p o v σ pos) (rep).p g) x U=_
  rw [WilsonOriginalBareMarkedSheet.restore]
  exact WilsonOriginalBarePhysicalLog.birth R dim N p o σ v probe pos refs x U

theorem filled : physical R dim N p o v WilsonThermometerCourseHearing.fired =
    WilsonCapturedPrimaryWardAppointment.input R dim o v (J) :=by
  funext U
  simp [physical,WilsonCapturedPrimaryWardAppointment.input,Accent.birth,Accent.Mach,probe,WilsonThermometerCourseHearing.fired]

theorem purchased (pos:∀j,0<dim j) (σ K Ω:ℝ) (fund:∀j,((C).labels.level (dim j)).coeffSize (coins j)≤K)
    (one:1≤Ω) (order count shelf stage vac coarse:ℕ) (slots:3≤count) (space:∑j,dim j ≤ shelf)
    (fit:maximum R dim≤order) (room:order+1 ≤ stage) (future:order≤coarse) (stamp:∀j,dim j≤coarse)
    (cover:order+shelf≤AllOrder.Burn.horizon vac+2) :
    let E:=max 1 ((1+K)*wallet R dim σ)
    let w:=fun _:Fin 3=>(E*Ω)⁻¹
    let M:=models R dim N p o v σ pos
    Scene.Armada M w dim σ Ω⁻¹ order count shelf ∧ Mentor.Cruise.Voter M σ order count stage vac coarse ∧
      Tableau WilsonThermometerCourseHearing.sectors disks M ∧
      ∀s:(J).Mode,Poly.toll w s*(E*Ω)^s.val.card=1 :=by
  intro E w M
  have k0:0≤K:=(Finset.sum_nonneg (fun _ _=>norm_nonneg _)).trans (fund (0:Fin 3))
  have setup:(rep).p=(C).path.levels.budget N:=(R.makes.wilson.represents N p N le_rfl).vac
  have band:g≤2*(rep).p.threshold:=by
    rw [setup]
    exact (RG04B.thresholdHat R.makes (p:=p) (le_rfl (a:=N))).2
  obtain ⟨crew,vote,toll⟩:=WilsonOriginalStarGradedScene.appointed R dim o σ g (rep).p.threshold coins probe
    pos k0 fund (ActualRunKernelPackets.regulator_pos R N p N le_rfl).le (rep).p.threshold_pos band one
    (fun j x=>(x j).property) order count shelf stage vac coarse (by simpa using slots) space fit room future stamp cover
  exact ⟨crew,vote,⟨fun i=>(WilsonOriginalStarSceneMasked.tests R dim o σ g (rep).p.threshold coins _ _ probe
    WilsonOriginalThermometerRealPalette.attentive).bill i⟩,toll⟩

end YM.Integration.WilsonThermometerWardBareScene
