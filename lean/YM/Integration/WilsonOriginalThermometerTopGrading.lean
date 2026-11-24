import YM.Integration.WilsonOriginalThermometerTopDensity
import YM.Integration.WilsonOriginalThermometerMicroscopic

/-! A single adjoint transfer pays the authentic common bare source before the period. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalThermometerTopGrading
open Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 WilsonLimitConstruction PhysicalNext.Repeat Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot
open Next.UVStress Next.Rank Next.Rank.East MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "B" n:max => R.family.path.levels.clock.hatBeta n
local notation "J" => Stock.census (Fin 3)

def cap (k:ℕ) (ε:ℝ) := (B (k+1))^7 * ((B k)^ε*mass R)

private theorem salary_cap (A:Group C 6) (close₀:close R A) : salary R A ≤ mass R := by
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (by unfold WilsonPositionThermometerStationNorm.cost; positivity)
  calc
    ‖vector A univ j‖ = ‖(vector A univ j-source C univ j)+source C univ j‖ := by rw [sub_add_cancel]
    _ ≤ ‖vector A univ j-source C univ j‖+‖source C univ j‖:=norm_add_le _ _
    _  ≤  _:=add_le_add (close₀ j) (le_refl _)

theorem coordinates (simple:G.Simple) {δ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)
    (ε:ℝ) (eps:0 < ε) :
    ∀ᶠ k:ℕ in atTop,∀ A:Group C 6,A.station.k=k → A.station.checked f H A.horizon → close R A →
    ∀ p:ℕ,∀j:Fin 3,(R.family.labels.level (levels j)).coeffSize
      (WilsonOriginalThermometerPalette.coordinates R A (k+1) (k+1) p j)  ≤  cap R k ε := by
  filter_upwards [station R (f:=f) (H:=H) simple ε eps,
    eventually_all.mpr (fun j:Fin 3=>eventually_ge_atTop (R.family.ref (levels j)))]
    with k funded refs A date checked close₀ p j
  let F:=R.family.labels.level (levels j)
  let v:=A.station.wheel.atCut (k+1,p) (index A (grade j)) (vector A univ j)
  let s:=F.coeffSize (awake R.family (levels j) k (k+1) p v)
  have seen:0 ≤ s:=sum_nonneg fun _ _=>norm_nonneg _
  have one:1  ≤  B (k+1) := (R.family.path.levels.fits.delayed (k+1)).le
  have non:0  ≤  B (k+1) := zero_le_one.trans one
  have lower:s ≤ (B k)^ε*mass R :=
    (funded A date checked (k+1) p k.lt_succ_self j).trans
      (mul_le_mul_of_nonneg_left (salary_cap R A close₀) (Real.rpow_nonneg
        (zero_le_one.trans (R.family.path.levels.fits.delayed k).le) _))
  have gate : ((R.family.S.block k).val:ℝ)^(levels j)*(R.family.path.levels.params (k+1)).columns  ≤ 
      (B (k+1))^7 := by
    calc
      _  ≤  (B (k+1))^(levels j)*(B (k+1)):=mul_le_mul
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (WilsonOriginalAdjacentMicroscopicPrice.block R slow k) _)
        (fund.2.1.logBudget.money.present (k+1))
        (zero_le_one.trans (R.family.path.levels.params (k+1)).columns_ge) (pow_nonneg non _)
      _ = (B (k+1))^(levels j+1):=(pow_succ ..).symm
      _  ≤  _:=pow_le_pow_right₀ one (Nat.succ_le_succ (WilsonOriginalThermometerGradedPalette.ceiling j))
  exact (WilsonOriginalAdjacentMicroscopicPrice.backward R (levels j) k (k+1) p k.lt_succ_self (refs j) v).trans
    (mul_le_mul gate lower seen (pow_nonneg non _))

theorem original (simple:G.Simple) {δ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)
    (ε:ℝ) (eps:0 < ε) :
    ∀ᶠ k:ℕ in atTop,∀ A:Group C 6, A.station.k=k → A.station.checked f H A.horizon → close R A →
    ∀ σ Ω:ℝ,1 ≤ Ω →
    let E:=max 1 ((1+cap R k ε)*wallet R levels σ)
    let w:=fun _:Fin 3=>(E*Ω)⁻¹
    ∀ (p:ℕ) (o:Fin 3→Site (R.family.side (k+1) p)),
    let X:=primitive R A (k+1) p o σ
    ∀ order count shelf stage vac coarse:ℕ, 3 ≤ count → 14 ≤ shelf → maximum R levels  ≤  order →
      order+1 ≤ stage → order ≤ coarse → 6 ≤ coarse → order+shelf ≤ AllOrder.Burn.horizon vac+2 →
      Scene.Armada X w levels σ Ω⁻¹ order count shelf ∧ Mentor.Cruise.Voter X σ order count stage vac coarse ∧
      Tableau WilsonThermometerCourseHearing.sectors disks X ∧ ∀s:(J).Mode,Poly.toll w s*(E*Ω)^s.val.card=1 := by
  filter_upwards [coordinates R (f:=f) (H:=H) simple fund slow ε eps] with k paid A date checked close₀ σ Ω one E w p o X order count shelf stage vac coarse load space available room future stamp cover
  let a:=R.family.path.rep (k+1) p (k+1)
  let g:=Pert.Asymptotics.regulatorRun R.family (k+1) p (k+1)
  let v:=WilsonOriginalThermometerPalette.coordinates R A (k+1) (k+1) p
  have non:0 ≤ cap R k ε:=(sum_nonneg fun _ _=>norm_nonneg _).trans (paid A date checked close₀ p 0)
  have band:g ≤ 2*a.p.threshold:=by
    have point:a.p=R.family.path.levels.budget (k+1):=(R.makes.wilson.represents (k+1) p (k+1) le_rfl).vac
    rw [point]
    exact (RG04B.thresholdHat R.makes (p:=p) (show k+1 ≤ k+1 from le_rfl)).2
  obtain ⟨crew,vote,restored⟩:=WilsonOriginalStarGradedScene.appointed R levels o σ g a.p.threshold v probe
    WilsonOriginalThermometerGradedPalette.positive non (paid A date checked close₀ p)
    (ActualRunKernelPackets.regulator_pos R (k+1) p (k+1) le_rfl).le a.p.threshold_pos band one
    (fun j x=>(x j).property) order count shelf stage vac coarse (by simpa using load)
    (WilsonOriginalThermometerGradedPalette.total.le.trans space) available room future
    (fun j=>(WilsonOriginalThermometerGradedPalette.ceiling j).trans stamp) cover
  exact ⟨crew,vote,⟨fun i=>(WilsonOriginalStarSceneMasked.tests R levels o σ g a.p.threshold v _ _ probe
    WilsonOriginalThermometerRealPalette.attentive).bill i⟩,restored⟩

end YM.Integration.WilsonOriginalThermometerTopGrading
