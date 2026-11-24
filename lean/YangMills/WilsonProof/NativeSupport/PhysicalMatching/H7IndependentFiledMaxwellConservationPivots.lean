import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellProfileGradients
import YM.Integration.WilsonGraphUnorderedMaxwellTrace
import YM.Push.STRESS_FLUX.Pairing

set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7IndependentFiledMaxwellConservationPivots
open YM YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick YangMills MeasureTheory Set
open H7IndependentFiledMaxwellProfileGradients H7IndependentIntegratedMaxwellWardPupils
open H7IndependentGroundComponentProfiles H7StandaloneAppointedPublicWardRows
open H7StandaloneFourSmearedWardReadings
open YM.XSpace.Normalize (Index left right)
open YM.UVNext.FreeStress.PublicPanels (planeLabel)
open scoped Topology ContDiff BigOperators

def selectedRead (g : GaugeGroup) (j k : Fin 2) (x : YM.Points 2) : ℂ :=
  if k=0 then (if j=0 then panelRead g x 2 3 else panelRead g x 0 1)
  else (if j=0 then traceRead g x 2 3 else traceRead g x 0 1)

theorem panelHead (g : GaugeGroup) (x : YM.Points 2) (a b : YM.Axis) :
    panelRead g x a b = moment g.core x ![sheetEnergy (G:=g.core) 0 0,phi a a b b] := by
  change (∑ i : YM.Axis, moment g.core x ![phi 0 0 i i,phi a a b b]) = _
  simp_rw [← YM.StressFlux.head_at]
  rw [sheetEnergy, map_sum]

theorem traceHead (g : GaugeGroup) (H : g.core.Simple) (x : YM.Points 2) (r : Index) :
    traceRead g x (left r) (right r) =
      moment g.core x ![(∑ t : Index, square H t).val,(square H r).val] := by
  change (∑ t : Index, moment g.core x
    ![phi (left t) (left t) (right t) (right t),phi (left r) (left r) (right r) (right r)]) = _
  simp_rw [← YM.StressFlux.head_at, planeLabel]
  change (∑ t : Index, YM.StressFlux.head x (square H r).val (square H t).val) =
    YM.StressFlux.head x (square H r).val (∑ t : Index, square H t).val
  rw [Submodule.coe_sum]
  exact (map_sum (YM.StressFlux.head x ((square H r).val : WickPol g.core))
    (fun i : Index => ((square H i).val : WickPol g.core)) Finset.univ).symm

theorem actualColumns (g : GaugeGroup) (H : g.core.Simple) (j k : Fin 2) (x : YM.Points 2) :
    selectedRead g j k x = moment g.core x
      ![(columns H 0 0 ((![1,2] : Fin 2 → Fin 4) k)).val,(probes H j).val] := by
  have h5 : phi (G:=g.core) 2 2 3 3=(square H 5).val := planeLabel 5
  have h0 : phi (G:=g.core) 0 0 1 1=(square H 0).val := planeLabel 0
  fin_cases j <;> fin_cases k
  · change panelRead g x 2 3=moment g.core x ![sheetEnergy 0 0,(square H 5).val]
    rw [panelHead,h5]
  · exact traceHead g H x 5
  · change panelRead g x 0 1=moment g.core x ![sheetEnergy 0 0,(square H 0).val]
    rw [panelHead,h0]
  · exact traceHead g H x 0

theorem selectedSmooth (g : GaugeGroup) (H : g.core.Simple) (j k : Fin 2)
    {x : YM.Points 2} (hx : x ∈ conf 2) :
    ContDiffAt ℝ ∞ (selectedRead g j k) x := by
  have h : selectedRead g j k = fun z => moment g.core z
      ![(columns H 0 0 ((![1,2] : Fin 2 → Fin 4) k)).val,(probes H j).val] :=
    funext (actualColumns g H j k)
  rw [h]
  exact moment_smooth _ hx

theorem selectedGradient (g : GaugeGroup) {x : YM.Points 2} (hx : x ∈ tsupport mass)
    (j k : Fin 2) : YM.Points.gradient 0 0 (selectedRead g j k) x =
      (gradBlock (H7IndependentFiledMaxwellProfiles.price g.core) x j k : ℂ) := by
  fin_cases j <;> fin_cases k
  · exact panel23Gradient g hx
  · exact traceGradient g hx 0 2 3 (by decide)
  · exact panel01Gradient g hx
  · exact traceGradient g hx 1 0 1 (by decide)

private theorem compactCost (f : YM.Points 2 → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) {v : YM.Points 2 → ℂ}
    (hv : ∀ x ∈ tsupport f, ContinuousAt v x) : Integrable (fun x => f x * v x) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hc.mul_right
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.continuousAt.mul (hv x hx)
  apply continuousAt_const.congr (show (fun _ : YM.Points 2 => (0 : ℂ)) =ᶠ[𝓝 x]
      (fun z => f z * v z) from ?_)
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
  have hz0 : f z = (0 : ℂ) := hz
  simp only [hz0, zero_mul]

theorem testedByParts (m : YM.Points 2 → ℂ)
    (smooth : ∀ x ∈ conf 2, ContDiffAt ℝ ∞ m x) (φ : SeparatedTest 2) (e : YM.Points 2) :
    Integrable (fun x => φ x * fderiv ℝ m x e) ∧
    (∫ x : YM.Points 2, φ x * fderiv ℝ m x e) =
      -(∫ x : YM.Points 2, fderiv ℝ (fun z => φ z) x e * m x) := by
  let f : YM.Points 2 → ℂ := fun x => φ x
  have hs : ContDiff ℝ ∞ f := φ.contDiff'
  have hc : HasCompactSupport f := φ.hasCompactSupport'
  have hm (x : YM.Points 2) (hx : x ∈ tsupport f) : ContDiffAt ℝ ∞ m x :=
    smooth x (φ.tsupport_subset' hx)
  have sub : tsupport (fun z => fderiv ℝ f z e) ⊆ tsupport (fderiv ℝ f) :=
    tsupport_comp_subset (g := ContinuousLinearMap.apply ℝ ℂ e) (map_zero _) _
  have h1 : Integrable (fun x => fderiv ℝ f x e * m x) :=
    compactCost _ ((hs.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ e) fun x hx => (hm x (tsupport_fderiv_subset ℝ (sub hx))).continuousAt
  have h2 : Integrable (fun x => f x * fderiv ℝ m x e) :=
    compactCost _ hs.continuous hc fun x hx =>
      (ContDiffAt.continuousAt_fderiv (hm x hx) (by simp)).clm_apply continuousAt_const
  have h3 : Integrable (fun x => f x * m x) :=
    compactCost _ hs.continuous hc fun x hx => (hm x hx).continuousAt
  refine ⟨h2, ?_⟩
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3
    (fun x _ => hs.differentiable (by simp) x) (fun x hx => (hm x hx).differentiableAt (by simp))

theorem signedConservation (g : GaugeGroup) (H : g.core.Simple)
    (hK : 0 < H7IndependentFiledMaxwellProfiles.price g.core) (i k : Fin 2) :
    (∑ j : Fin 2, ∫ x : YM.Points 2, YM.Points.gradient 0 0
      (fun z => (pupils (H7IndependentFiledMaxwellProfiles.price g.core) hK).conservation i j z) x *
      moment g.core x ![(columns H 0 0 ((![1,2] : Fin 2 → Fin 4) k)).val,(probes H j).val]) =
      if i=k then -1 else 0 := by
  let K := H7IndependentFiledMaxwellProfiles.price g.core
  let φ (j : Fin 2) := (pupils K hK).conservation i j
  have h (j : Fin 2) := testedByParts (selectedRead g j k)
    (fun _ hx => selectedSmooth g H j k hx) (φ j) (YM.Points.direction 0 0)
  have back (j : Fin 2) : (∫ x : YM.Points 2, YM.Points.gradient 0 0 (fun z => φ j z) x *
      moment g.core x ![(columns H 0 0 ((![1,2] : Fin 2 → Fin 4) k)).val,(probes H j).val]) =
        -(∫ x : YM.Points 2, φ j x * YM.Points.gradient 0 0 (selectedRead g j k) x) := by
    simp_rw [← actualColumns g H j k]
    exact ((congrArg Neg.neg (h j).2).trans (neg_neg _)).symm
  change (∑ j : Fin 2, ∫ x : YM.Points 2, YM.Points.gradient 0 0 (fun z => φ j z) x *
    moment g.core x ![(columns H 0 0 ((![1,2] : Fin 2 → Fin 4) k)).val,(probes H j).val]) = _
  simp_rw [back]
  rw [Finset.sum_neg_distrib]
  have summed : (∑ j : Fin 2, ∫ x : YM.Points 2, φ j x * YM.Points.gradient 0 0 (selectedRead g j k) x) =
      (∫ x : YM.Points 2, ∑ j : Fin 2, φ j x * YM.Points.gradient 0 0 (selectedRead g j k) x) :=
    (integral_finset_sum Finset.univ (fun j _ => (h j).1)).symm
  rw [summed]
  have collapse : (∫ x : YM.Points 2, ∑ j : Fin 2, φ j x * YM.Points.gradient 0 0 (selectedRead g j k) x) =
      (∫ x : YM.Points 2, ((mass x * ∑ j : Fin 2, cweight K i j x * gradBlock K x j k : ℝ) : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [] with x
    change (∑ j : Fin 2, ((mass x * cweight K i j x : ℝ) : ℂ) * YM.Points.gradient 0 0
      (selectedRead g j k) x) = _
    by_cases hz : mass x=0
    · simp [hz]
    · have hx := subset_tsupport mass hz
      simp_rw [selectedGradient g hx]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [collapse, integral_complex_ofReal, integratedConservation hK i k]
  split_ifs <;> norm_num

end PhysicalMatching.H7IndependentFiledMaxwellConservationPivots
