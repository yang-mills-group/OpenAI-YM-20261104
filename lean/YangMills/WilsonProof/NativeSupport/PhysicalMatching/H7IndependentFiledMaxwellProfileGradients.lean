import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentGroundComponentProfiles
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentIntegratedMaxwellWardPupils
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellIntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
namespace PhysicalMatching.H7IndependentFiledMaxwellProfileGradients
open YM YM.Maxwell YM.Maxwell.Wick YangMills MeasureTheory Set Filter
open H7IndependentIntegratedMaxwellWardPupils H7IndependentFiledMaxwellIntegrationByParts
open H7IndependentGroundComponentProfiles H7IndependentMaxwellPupilKinematics
open scoped Topology ContDiff BigOperators

def along (x : YM.Points 2) (s : ℝ) : YM.Points 2 := x + s • YM.Points.direction 0 0

@[simp] theorem alongZero (x : YM.Points 2) : along x 0 = x := by simp [along]

theorem alongDisplacement (x : YM.Points 2) (s : ℝ) (i : YM.Axis) :
    displacement i (along x s) = displacement i x + if i = 0 then s else 0 := by
  fin_cases i <;> simp [along, displacement, YM.Points.direction, PiLp.add_apply,
    PiLp.smul_apply, PiLp.single_apply, basis_eq] <;> ring

theorem alongRadius (x : YM.Points 2) (s : ℝ) :
    radial (along x s) = radius (radial x) (displacement 0 x) s := by
  simp [radial, radius, alongDisplacement]
  <;> ring

theorem alongTransverse (x : YM.Points 2) (s : ℝ) :
    transverse (along x s) = transverse x := by
  simp [transverse, alongDisplacement]

private theorem pointRadius (x : YM.Points 2) : ‖x 0-x 1‖^2 = radial x := by
  rw [H7IndependentFiledMaxwellProfiles.normFour]
  rfl

private theorem pointTransverse (x : YM.Points 2) :
    H7IndependentFiledMaxwellProfiles.transverse (x 0-x 1) = transverse x := rfl

private theorem alongFirst (x : YM.Points 2) (s : ℝ) :
    ((along x s) 0-(along x s) 1) 0 = displacement 0 x+s := by
  change displacement 0 (along x s) = _
  simp [alongDisplacement]

private theorem different {x : YM.Points 2} (hx : x ∈ tsupport mass) : x 0 ≠ x 1 := by
  intro h
  exact (safe hx).1.ne' (by simp [radial, displacement, h])

private theorem separated {x : YM.Points 2} (h : x 0 ≠ x 1) : x ∈ conf 2 := by
  change Function.Injective x.ofLp
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact (h hij).elim | exact (h hij.symm).elim

private theorem nearby (x : YM.Points 2) (hx : x 0 ≠ x 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ), (along x s) 0 ≠ (along x s) 1 := by
  have hc : Continuous (along x) := continuous_const.add (continuous_id.smul continuous_const)
  exact (isOpen_ne_fun ((PiLp.continuous_apply 2 (fun _ : Fin 2 => E4) (0 : Fin 2)).comp hc)
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 => E4) (1 : Fin 2)).comp hc)).mem_nhds (by simpa using hx)

private theorem onDirection (f : YM.Points 2 → ℂ) (x : YM.Points 2)
    (hf : DifferentiableAt ℝ f x) (u : ℝ → ℝ) (a : ℝ) (hu : HasDerivAt u a 0)
    (hline : (fun s => f (along x s)) =ᶠ[𝓝 (0 : ℝ)] fun s => (u s : ℂ)) :
    YM.Points.gradient 0 0 f x = (a : ℂ) := by
  let v : YM.Points 2 := YM.Points.direction (n := 2) 0 0
  have hconst := hasDerivAt_const (0 : ℝ) x
  have hlinear := (hasDerivAt_id (0 : ℝ)).smul_const v
  have hc := hconst.add hlinear
  have hf' : HasFDerivAt f (fderiv ℝ f x) (along x 0) := by simpa using hf.hasFDerivAt
  have h1 := hf'.comp_hasDerivAt (0 : ℝ) hc
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  have h := h1.unique (h2.congr_of_eventuallyEq hline)
  change fderiv ℝ f x v = (a : ℂ)
  calc
    (fderiv ℝ f x) v = Complex.ofRealCLM a := by
      simpa only [zero_add, one_smul] using h
    _ = (a : ℂ) := by
      first
      | exact Complex.ofRealCLM_apply a
      | rfl
      | simp [Complex.ofRealCLM]
      | ext <;> simp [Complex.ofRealCLM]

private theorem panelSmooth (g : GaugeGroup) (x : YM.Points 2) (hx : x ∈ conf 2)
    (k l : YM.Axis) : DifferentiableAt ℝ (fun z => panelRead g z k l) x := by
  have h : ContDiffAt ℝ ∞ (fun z => panelRead g z k l) x :=
    ContDiffAt.sum fun _ _ => moment_smooth _ hx
  exact h.differentiableAt (by simp)

private theorem traceSmooth (g : GaugeGroup) (x : YM.Points 2) (hx : x ∈ conf 2)
    (k l : YM.Axis) : DifferentiableAt ℝ (fun z => traceRead g z k l) x := by
  have h : ContDiffAt ℝ ∞ (fun z => traceRead g z k l) x :=
    ContDiffAt.sum fun _ _ => moment_smooth _ hx
  exact h.differentiableAt (by simp)

theorem panel23Gradient (g : GaugeGroup) {x : YM.Points 2} (hx : x ∈ tsupport mass) :
    YM.Points.gradient 0 0 (fun z => panelRead g z 2 3) x =
      (gradBlock (H7IndependentFiledMaxwellProfiles.price g.core) x 0 0 : ℂ) := by
  let K := H7IndependentFiledMaxwellProfiles.price g.core
  have hn := different hx
  have hr := (safe hx).1.ne'
  have hd := component23Derivative K (radial x) (displacement 0 x) (transverse x) hr
  have he := onDirection (fun z => panelRead g z 2 3) x
    (panelSmooth g x (separated hn) 2 3) _ _ hd (by
      filter_upwards [nearby x hn] with s hs
      rw [panelE23 g _ hs, alongFirst, pointTransverse, alongTransverse, pointRadius, alongRadius]
      rfl)
  rw [he]
  apply congrArg (fun t : ℝ => (t : ℂ))
  simp [gradBlock, numerator, K]
  <;> field_simp [hr] <;> ring

theorem panel01Gradient (g : GaugeGroup) {x : YM.Points 2} (hx : x ∈ tsupport mass) :
    YM.Points.gradient 0 0 (fun z => panelRead g z 0 1) x =
      (gradBlock (H7IndependentFiledMaxwellProfiles.price g.core) x 1 0 : ℂ) := by
  let K := H7IndependentFiledMaxwellProfiles.price g.core
  have hn := different hx
  have hr := (safe hx).1.ne'
  have hd := component01Derivative K (radial x) (displacement 0 x) (transverse x) hr
  have he := onDirection (fun z => panelRead g z 0 1) x
    (panelSmooth g x (separated hn) 0 1) _ _ hd (by
      filter_upwards [nearby x hn] with s hs
      rw [panelE01 g _ hs, alongFirst, pointTransverse, alongTransverse, pointRadius, alongRadius]
      rfl)
  rw [he]
  apply congrArg (fun t : ℝ => (t : ℂ))
  simp [gradBlock, numerator, K]
  <;> field_simp [hr] <;> ring

theorem traceGradient (g : GaugeGroup) {x : YM.Points 2} (hx : x ∈ tsupport mass)
    (j : Fin 2) (k l : YM.Axis) (hkl : k ≠ l) :
    YM.Points.gradient 0 0 (fun z => traceRead g z k l) x =
      (gradBlock (H7IndependentFiledMaxwellProfiles.price g.core) x j 1 : ℂ) := by
  let K := H7IndependentFiledMaxwellProfiles.price g.core
  have hn := different hx
  have hd := traceDerivative K (radial x) (displacement 0 x) (safe hx).1.ne'
  have he := onDirection (fun z => traceRead g z k l) x
    (traceSmooth g x (separated hn) k l) _ _ hd (by
      filter_upwards [nearby x hn] with s hs
      rw [tracePlane g _ hs k l hkl, pointRadius, alongRadius]
      rfl)
  rw [he]
  fin_cases j <;> simp [gradBlock, K]

theorem occupiedGradient (g : GaugeGroup) (H : g.core.Simple) {x : YM.Points 2}
    (hx : x ∈ tsupport mass) :
    YM.Points.gradient 0 0 (fun z => moment g.core z (actualProbes H)) x =
      (translationDerivative (H7IndependentFiledMaxwellProfiles.price g.core) x : ℂ) := by
  let K := H7IndependentFiledMaxwellProfiles.price g.core
  have hn := different hx
  have hw : actualProbes H = ![(H7StandaloneFourSmearedWardReadings.probes H 0).val,
      (H7StandaloneFourSmearedWardReadings.probes H 0).val] := by
    funext i
    fin_cases i <;> rfl
  have hd := e23Derivative K (radial x) (displacement 0 x) (transverse x) (safe hx).1.ne'
  exact onDirection _ x ((moment_smooth (actualProbes H) (separated hn)).differentiableAt
    (by simp)) _ _ hd (by
      filter_upwards [nearby x hn] with s hs
      change (maxwellReference g).moment (along x s) (actualProbes H) = _
      rw [hw, H7IndependentFiledMaxwellProfiles.filedE23Pair g H _ hs,
        pointTransverse, alongTransverse, pointRadius, alongRadius]
      rfl)

theorem normalizedRhs (g : GaugeGroup) (H : g.core.Simple)
    (hK : 0 < H7IndependentFiledMaxwellProfiles.price g.core) :
    -(∫ x : YM.Points 2, YM.Points.gradient 0 0 (fun z =>
        (pupils (H7IndependentFiledMaxwellProfiles.price g.core) hK).translation z) x *
        moment g.core x (actualProbes H)) = 1 := by
  let K := H7IndependentFiledMaxwellProfiles.price g.core
  let P := pupils K hK
  change -(∫ x : YM.Points 2, fderiv ℝ (fun z => P.translation z) x
    (YM.Points.direction 0 0) * moment g.core x (actualProbes H)) = 1
  rw [← separatedByParts (actualProbes H) P.translation (YM.Points.direction 0 0)]
  calc
    _ = ∫ x : YM.Points 2, (mass x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change ((mass x * tweight K x : ℝ) : ℂ) *
        YM.Points.gradient 0 0 (fun z => moment g.core z (actualProbes H)) x = (mass x : ℂ)
      by_cases hz : mass x = 0
      · simp [hz]
      · have hx := subset_tsupport mass hz
        rw [occupiedGradient g H hx]
        change ((mass x * tweight K x : ℝ) : ℂ) * (translationDerivative K x : ℂ) = _
        rw [← Complex.ofReal_mul, mul_assoc, exactTranslation hK hx, mul_one]
    _ = 1 := by
      first
      | rw [integral_complex_ofReal, normalized.1]; norm_num
      | rw [Complex.integral_ofReal, normalized.1]; norm_num
      | rw [← Complex.ofReal_integral, normalized.1]; norm_num

end PhysicalMatching.H7IndependentFiledMaxwellProfileGradients
