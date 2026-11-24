import YM.Next.MAXWELL.Taxes
import YangMills.StressTensor
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy
import YangMills.WilsonProof.NativeSupport.HierarchySpec

set_option autoImplicit false
noncomputable section

namespace PhysicalMatching.H7IndependentGroupMaxwellIntegrability

open YM YM.Spec YM.Analysis YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick
open MeasureTheory Function Set
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n : ℕ}

theorem compactProduct (w : Points n → ℂ) (hw : Continuous w)
    (hc : HasCompactSupport w) (m : Points n → ℂ)
    (hm : ∀ x ∈ tsupport w, ContinuousAt m x) :
    Integrable (fun x => w x * m x) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hc.mul_right
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport w
  · exact hw.continuousAt.mul (hm x hx)
  apply continuousAt_const.congr (show (fun _ : Points n => (0 : ℂ)) =ᶠ[𝓝 x]
      (fun z => w z * m z) from ?_)
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
  change w z = 0 at hz
  simp [hz]

theorem filedWeightMomentIntegrable (p : Fin n → WickPol G) (w : Points n → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (hs : tsupport w ⊆ conf n) :
    Integrable (fun x => w x * moment G x p) :=
  compactProduct w hw hc _ fun _ hx => (moment_smooth p (hs hx)).continuousAt

theorem testedMomentIntegrable (p : Fin n → WickPol G) (φ : YangMills.SeparatedTest n) :
    Integrable (fun x => φ x * moment G x p) :=
  filedWeightMomentIntegrable p (fun x => φ x) φ.contDiff'.continuous
    φ.hasCompactSupport' φ.tsupport_subset'

theorem testedDerivativeMomentIntegrable (p : Fin n → WickPol G)
    (φ : YangMills.SeparatedTest n) (e : Points n) :
    Integrable (fun x => fderiv ℝ (fun z => φ z) x e * moment G x p) := by
  let w : Points n → ℂ := fun x => φ x
  have hw : ContDiff ℝ ∞ w := φ.contDiff'
  have hc : HasCompactSupport w := φ.hasCompactSupport'
  have sub : tsupport (fun z => fderiv ℝ w z e) ⊆ tsupport (fderiv ℝ w) :=
    tsupport_comp_subset (g := ContinuousLinearMap.apply ℝ ℂ e) (map_zero _) _
  apply filedWeightMomentIntegrable p _ ((hw.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ e)
  intro x hx
  exact φ.tsupport_subset' (tsupport_fderiv_subset ℝ (sub hx))

theorem prependContinuous :
    Continuous (fun z : YangMills.Spacetime × Points 2 => YangMills.Ward.prepend z.1 z.2) := by
  unfold YangMills.Ward.prepend
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => YangMills.Spacetime)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => YangMills.Spacetime) j).comp continuous_snd

theorem signedShellMomentIntegrable (p : Fin 3 → WickPol G)
    (w : YangMills.Spacetime × Points 2 → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (hs : ∀ z ∈ tsupport w, YangMills.Ward.prepend z.1 z.2 ∈ conf 3) :
    Integrable (fun z : YangMills.Spacetime × Points 2 =>
      w z * moment G (YangMills.Ward.prepend z.1 z.2) p) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hc.mul_right
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ tsupport w
  · apply hw.continuousAt.mul
    exact (moment_smooth p (hs z hz)).continuousAt.tendsto.comp
      prependContinuous.continuousAt.tendsto
  apply continuousAt_const.congr (show (fun _ : YangMills.Spacetime × Points 2 => (0 : ℂ))
      =ᶠ[𝓝 z] (fun x => w x * moment G (YangMills.Ward.prepend x.1 x.2) p) from ?_)
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with x hx
  change w x = 0 at hx
  simp [hx]

end PhysicalMatching.H7IndependentGroupMaxwellIntegrability

