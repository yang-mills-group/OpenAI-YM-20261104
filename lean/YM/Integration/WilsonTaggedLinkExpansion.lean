import YM.Integration.WilsonSmoothCylinder
import YM.Integration.WilsonLinkAmplitudeLeading
import YM.Integration.WilsonPhysicalKernelClock

/-! Smooth observables of the relative retained links, with their genuine sign choice and physical clock. -/
noncomputable section
namespace YM.Integration.WilsonTaggedLinkExpansion
open YM RG RG02 RG02.Asym Lattice Wilson Filter MeasureTheory Precision PowerSeries
open PertExtension PertExtension.Series PertExtension.Series.Tested
open WilsonKernelCoupling WilsonLinkMatrixAmplitude WilsonLinkAmplitudeExpansion
open PhysicalNext.Repeat.Legato Pert.Asymptotics FullQLocal.RenderedStep MatchingLedger.Compass.Income
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) {ι : Type*} [Fintype ι]

def linkMean (b : ℝ) (F : G.El → ℝ) : ℝ := ∫ g, link S b 1 g * F g ∂G.probHaar

theorem translate (b : ℝ) (q : G.El) (F : G.El → ℝ) :
    (∫ v, link S b q v * F (v*q⁻¹) ∂G.probHaar) = linkMean S b F := by
  have H := (measurePreserving_mul_right G.probHaar q⁻¹).integral_comp
    ((Homeomorph.mulRight q⁻¹).measurableEmbedding) (fun g => link S b 1 g * F g)
  simpa only [linkMean,link,inv_one,mul_one] using H

def measured (A : Finset (Edge (Site c))) (e : ι ≃ A) (b : ℝ) (U : Config G f)
    (F : ι → G.El → ℝ) : ℝ :=
  ∑ z, S.likelihood U z * ∫ V, S.noise b (S.prediction U z) V *
    ∏ i : A, F (e.symm i) (V i.val*(S.prediction U z i.val)⁻¹) ∂prior G c

theorem factor (h : S.patch.Branches S.kernel G) (A : Finset (Edge (Site c)))
    (e : ι ≃ A) (b : ℝ) (U : Config G f) (F : ι → G.El → ℝ) :
    measured S A e b U F = ∏ j : ι, linkMean S b (F j) := by
  have H z : (∫ V, S.noise b (S.prediction U z) V *
      ∏ i : A, F (e.symm i) (V i.val*(S.prediction U z i.val)⁻¹) ∂prior G c) =
        ∏ j : ι, linkMean S b (F j) := by
    rw [WilsonSmoothCylinder.expectation S A b (S.prediction U z)
      (fun i v => F (e.symm i) (v*(S.prediction U z i.val)⁻¹))]
    simp_rw [translate S b]
    exact Equiv.prod_comp e.symm (fun j => linkMean S b (F j))
  unfold measured
  simp_rw [H]
  rw [← Finset.sum_mul,S.chosen h,one_mul]

def series (F : ι → G.Mat → ℝ) : PowerSeries ℂ :=
  ∏ j : ι, normalizedSeries S (XSpace.Bare.chart G) (atPrediction 1 (fun v => F j (G.mat v)))

theorem expansion (F : ι → G.Mat → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j)) :
    Near (fun t => ∏ j : ι, Complex.ofReal (linkMean S (t^2)⁻¹ (fun v => F j (G.mat v))))
      (series S F) := by
  have H (B : Finset ι) : Near
      (fun t => ∏ j ∈ B, Complex.ofReal (linkMean S (t^2)⁻¹ (fun v => F j (G.mat v))))
      (∏ j ∈ B, normalizedSeries S (XSpace.Bare.chart G) (atPrediction 1 (fun v => F j (G.mat v)))) := by
    induction B using Finset.induction_on with
    | empty => simpa using (Near.fixed (1:ℂ))
    | @insert j B hj ih =>
      simp only [Finset.prod_insert hj]
      exact Near.mult (matrix S (XSpace.Bare.chart G) (XSpace.Bare.chart_ratio G) 1 (F j) (hF j)) ih
  exact H Finset.univ

theorem calendar (D : Calendar G) (F : ι → G.Mat → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in Tested.germ, ∀ m p : ℕ,
      (D.op m p).patch.Branches (D.op m p).kernel G →
      ∀ (A : Finset (Edge (Site (D.schedule.side m p)))) (e : ι ≃ A) (U : Config G (D.schedule.side (m+1) p)),
        ‖Complex.ofReal (measured (D.op m p) A e (t^2)⁻¹ U (fun j v => F j (G.mat v))) -
          peval (fun i => coeff i (series (D.op 0 0) F)) n t‖ ≤ C*t^(n+1) := by
  obtain ⟨C,hC,H⟩ := expansion (D.op 0 0) F hF n
  refine ⟨C,hC,H.mono ?_⟩
  intro t ht m p hb A e U
  rw [factor (D.op m p) hb A e (t^2)⁻¹ U]
  push_cast
  exact ht

end YM.Integration.WilsonTaggedLinkExpansion
