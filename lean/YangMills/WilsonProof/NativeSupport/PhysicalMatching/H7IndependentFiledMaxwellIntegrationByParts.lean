import YM.Next.MAXWELL.Taxes
import YM.Next.MAXWELL.Mark
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings

set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7IndependentFiledMaxwellIntegrationByParts
open YM YM.Spec YM.Analysis YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick
open MeasureTheory Function Set
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : ℕ}

theorem signedOccupied (p : Fin (n+1) → WickPol G) {x : Points (n+1)}
    (hx : x ∈ conf _) {χ : E4 → ℝ} (w : Table.Window x χ) (b : Axis) :
    -exportFlux (stressRead x (drift b) p) χ =
      Points.gradient 0 b (fun z => moment G z p) x := by
  rw [moment_force hx w (straight_motion (G:=G) w.1 w.2.1 w.2.2.1 b) p,
    neg_neg, positionD p hx 0 b]

theorem filedMinusStress (p : Fin (n+1) → WickPol G) {x : Points (n+1)}
    (hx : x ∈ conf _) {χ : E4 → ℝ} (w : Table.Window x χ) (b : Axis) :
    exportFlux (fun a y => bookend x y p (-polStress G a b)) χ =
      Points.gradient 0 b (fun z => moment G z p) x := by
  have h (a : Axis) (y : E4) :
      bookend x y p (-polStress G a b) = -stressRead x (drift b) p a y := by
    rw [map_neg]
    congr 1
    simp [stressRead, drift, kr_eq, ite_smul]
  calc
    _ = -exportFlux (stressRead x (drift b) p) χ := by
      simp only [exportFlux, h, smul_neg, integral_neg, Finset.sum_neg_distrib, neg_neg]
    _ = _ := signedOccupied p hx w b

variable {g : YangMills.GaugeGroup}
def actualProbes (hg : g.core.Simple) : Fin 2 → WickPol g.core :=
  fun _ => (H7StandaloneFourSmearedWardReadings.probes hg 0).val

theorem bothAreE23 (hg : g.core.Simple) (j : Fin 2) :
    actualProbes hg j = YM.XSpace.Normalize.label g.core 5 5 := rfl

theorem twoFiledE23 (hg : g.core.Simple) {x : Points 2} (hx : x ∈ conf _)
    {χ : E4 → ℝ} (w : Table.Window x χ) :
    exportFlux (fun a y => bookend x y (actualProbes hg) (-polStress g.core a 0)) χ =
      Points.gradient 0 0 (fun z => moment g.core z (actualProbes hg)) x :=
  filedMinusStress (actualProbes hg) hx w 0

open scoped ContDiff
private theorem compactCost (f : Points 2 → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) {v : Points 2 → ℂ}
    (hv : ∀ x ∈ tsupport f, ContinuousAt v x) : Integrable (fun x => f x * v x) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ hc.mul_right
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.continuousAt.mul (hv x hx)
  apply continuousAt_const.congr (show (fun _ : Points 2 => (0 : ℂ)) =ᶠ[𝓝 x]
      (fun z => f z * v z) from ?_)
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
  change f z = 0 at hz
  simp [hz]

theorem separatedByParts (p : Fin 2 → WickPol G) (φ : YangMills.SeparatedTest 2)
    (e : Points 2) :
    (∫ x : Points 2, φ x * (fderiv ℝ (fun z => moment G z p) x e)) =
      -(∫ x : Points 2, (fderiv ℝ (fun z => φ z) x e) * moment G x p) := by
  let f : Points 2 → ℂ := fun x => φ x
  let m : Points 2 → ℂ := fun x => moment G x p
  have hs : ContDiff ℝ ∞ f := φ.contDiff'
  have hc : HasCompactSupport f := φ.hasCompactSupport'
  have hm (x : Points 2) (hx : x ∈ tsupport f) : ContDiffAt ℝ ∞ m x :=
    moment_smooth p (φ.tsupport_subset' hx)
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
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3
    (fun x _ => hs.differentiable (by simp) x) (fun x hx => (hm x hx).differentiableAt (by simp))

theorem testedFiledShell (hg : g.core.Simple) (φ : YangMills.SeparatedTest 2) (χ : E4 → ℝ)
    (window : ∀ x ∈ tsupport (fun z => φ z), Table.Window x χ) :
    (∫ x : Points 2, φ x * exportFlux
      (fun a y => bookend x y (actualProbes hg) (-polStress g.core a 0)) χ) =
      -(∫ x : Points 2, (Points.gradient 0 0 (fun z => φ z) x) *
        moment g.core x (actualProbes hg)) := by
  calc
    _ = ∫ x : Points 2, φ x * Points.gradient 0 0
          (fun z => moment g.core z (actualProbes hg)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport (fun z => φ z)
      · rw [twoFiledE23 hg (φ.tsupport_subset' hx) (window x hx)]
      · have zero : φ x = 0 := by
          by_contra h
          exact hx (subset_tsupport (fun z => φ z) h)
        simp [zero]
    _ = _ := separatedByParts (actualProbes hg) φ (Points.direction 0 0)

theorem originalPupil (hg : g.core.Simple) (P : H7StandaloneFourSmearedWardReadings.Pupils) :
    (∫ x : Points 2, P.translation x * exportFlux
      (fun a y => bookend x y (actualProbes hg) (-polStress g.core a 0)) P.cutoff) =
      -(∫ x : Points 2, (Points.gradient 0 0 (fun z => P.translation z) x) *
        moment g.core x (actualProbes hg)) := by
  apply testedFiledShell
  intro x hx
  rcases P.window x hx with ⟨smooth, compact, first, others⟩
  exact ⟨smooth, compact, first, others⟩

end PhysicalMatching.H7IndependentFiledMaxwellIntegrationByParts
