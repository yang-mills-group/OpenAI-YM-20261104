import YM.Integration.WilsonOriginalStarGradedScene
import YM.Integration.WilsonOriginalThermometerRealPalette

/-! The real three-field calibration at its physical grades uses the shelf of
fourteen on one elected station. All amplitudes and source radii are those of
the original inverse-fitted fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerGradedPalette
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonOriginalStarGradedScene
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}

theorem positive (j:Fin 3) : 0<levels j := by fin_cases j <;> decide

theorem total : ∑ j:Fin 3, levels j = 14 := by decide

theorem ceiling (j:Fin 3) : levels j ≤ 6 := by fin_cases j <;> decide

theorem original (simple : G.Simple) (ε : ℝ) (eps : 0<ε) :
    ∀ᶠ k in atTop,∀ (A:Group R.family 6), A.station.k=k → A.station.checked f H A.horizon →
    ∀ σ Ω : ℝ,1 ≤ Ω →
    let K:=(R.family.path.levels.clock.hatBeta k)^ε * salary R A
    let E:=max 1 ((1+K)*wallet R levels σ)
    let w:=fun _ : Fin 3=>(E*Ω)⁻¹
    ∀ (N p:ℕ), k<N → ∀ o:Fin 3→Site (R.family.side k p),
    let g:=Pert.Asymptotics.regulatorRun R.family N p k
    let P:= R.family.path.rep N p k
    let X:=words R levels o σ g P.p.threshold (coordinates R A k N p) probe positive
    ∀ order count shelf stage vac coarse : ℕ, 3≤count → 14 ≤ shelf → maximum R levels ≤ order →
      order+1 ≤ stage → order ≤ coarse → 6≤coarse →
      order+shelf ≤ AllOrder.Burn.horizon vac+2 →
      Scene.Armada X w levels σ Ω⁻¹ order count shelf ∧
      Mentor.Cruise.Voter X σ order count stage vac coarse ∧
      Tableau (fun _ : Fin 3=> (⊥:Submodule ℝ ℂ)) disks X ∧
      (∀s:(Stock.census (Fin 3)).Mode, Poly.toll w s*(E*Ω)^s.val.card=1) ∧
      WilsonOriginalStarFlagPrice.extent R levels ≤ P.p.B := by
  filter_upwards [station R (f:=f) (H:=H) simple ε eps,WilsonOriginalStarFlagPrice.fit R levels simple,
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 0] with k paid fit pos A date checked σ Ω one K E w N p top o g P X order count shelf stage vac coarse load shelfSpace available room future stamp cover
  have kpos : 0 ≤ K:=mul_nonneg (Real.rpow_nonneg pos _)
    (sum_nonneg fun i _=>mul_nonneg (by unfold WilsonPositionThermometerStationNorm.cost;positivity) (norm_nonneg _))
  have band:g ≤ 2*P.p.threshold:=by
    have point:P.p=R.family.path.levels.budget k:=(R.makes.wilson.represents N p k top.le).vac
    rw [point]
    exact (RG04B.thresholdHat R.makes (p:=p) top.le).2
  obtain ⟨crew,votes,restored⟩:=WilsonOriginalStarGradedScene.appointed R levels o σ g P.p.threshold
    (coordinates R A k N p) probe positive kpos (paid A date checked N p top)
    (ActualRunKernelPackets.regulator_pos R N p k top.le).le P.p.threshold_pos band one
    (fun i x=>(x i).property) order count shelf stage vac coarse (by simpa using load)
    (total.le.trans shelfSpace) available room future (fun j=>(ceiling j).trans stamp) cover
  exact ⟨crew,votes,⟨fun i=>(WilsonOriginalStarSceneMasked.tests R levels o σ g P.p.threshold (coordinates R A k N p) _ _ probe
    WilsonOriginalThermometerRealPalette.attentive).bill i⟩,restored,fit N p top.le⟩

end YM.Integration.WilsonOriginalThermometerGradedPalette
