import YM.Integration.WilsonOriginalAlternativeFiniteSource
import YM.Integration.WilsonOriginalThermometerTopGrading

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalAlternativeFiniteWallet
open Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 WilsonLimitConstruction PhysicalNext.Repeat Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot
open Next.UVStress Next.Rank Next.Rank.East MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators


variable {V:Type} [Fintype V] [DecidableEq V]
variable {G:Gauge} (R:Run G) (d:V→ℕ) (positive:∀j,0<d j) (N p:ℕ)
    (y:∀j,R.family.book.Ref (d j)) (o:V→Site (R.family.side N p))

/-- The actual independently priced cutoff coordinates may be chosen on distinct
stations. The native common radius retains their pre-reported bound below. -/
theorem original {cost:ℝ} (non:0 ≤ cost) (cap:∀j,(R.family.labels.level (d j)).coeffSize
    (Next.Rank.Price.awake R.family (d j) N N p (y j)) ≤ cost) (σ Ω:ℝ) (one:1 ≤ Ω) :
    let E:=max 1 ((1+cost)*wallet R d σ)
    let w:=fun _:V=>(E*Ω)⁻¹
    let X:=WilsonOriginalAlternativeFiniteSource.words R d positive N p y o σ
    ∀order count shelf stage vac coarse:ℕ, Fintype.card V ≤ count → (∑j,d j) ≤ shelf → maximum R d ≤ order →
      order+1 ≤ stage → order ≤ coarse → (∀j,d j ≤ coarse) → order+shelf ≤ AllOrder.Burn.horizon vac+2 →
      Scene.Armada X w d σ Ω⁻¹ order count shelf ∧ Mentor.Cruise.Voter X σ order count stage vac coarse ∧
      Tableau WilsonOriginalAlternativeFiniteSource.sectors WilsonOriginalAlternativeFiniteSource.disks X ∧ ∀s:(Stock.census (V)).Mode,
        Poly.toll w s*(E*Ω)^s.val.card=1:=by
  intro E w X order count shelf stage vac coarse slots space fit room future stamp cover
  let a:=R.family.path.rep N p N
  let g:=Pert.Asymptotics.regulatorRun R.family N p N
  let v:=fun j=>Next.Rank.Price.awake R.family (d j) N N p (y j)
  have band:g ≤ 2*a.p.threshold:=by
    have point:a.p=R.family.path.levels.budget N:=(R.makes.wilson.represents N p N le_rfl).vac
    rw [point]
    exact (RG04B.thresholdHat R.makes (p:=p) (show N ≤ N from le_rfl)).2
  obtain ⟨crew,vote,restored⟩:=WilsonOriginalStarGradedScene.appointed R d o σ g a.p.threshold v WilsonOriginalAlternativeFiniteSource.probe
    positive non cap (ActualRunKernelPackets.regulator_pos R N p N le_rfl).le a.p.threshold_pos band one
    (fun j x=>(x j).property) order count shelf stage vac coarse slots
    space fit room future stamp cover
  exact ⟨crew,vote,⟨fun i=>(WilsonOriginalStarSceneMasked.tests R d o σ g a.p.threshold v _ _ WilsonOriginalAlternativeFiniteSource.probe
    WilsonOriginalAlternativeFiniteSource.attentive).bill i⟩,restored⟩

end YM.Integration.WilsonOriginalAlternativeFiniteWallet
