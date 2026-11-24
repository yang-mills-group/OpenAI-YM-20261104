import YM.Integration.WilsonLinkMatrixAmplitude
import YM.Integration.WilsonLocalKernelPairing

/-! Tensor observables on genuine retained Wilson links in a fixed conditional branch. -/
noncomputable section
namespace YM.Integration.WilsonSmoothCylinder
open YM RG RG02 RG02.Asym Lattice Wilson Filter MeasureTheory Precision PowerSeries
open PertExtension PertExtension.Series.Tested WilsonKernelCoupling
open WilsonLinkAmplitudeExpansion WilsonLinkMatrixAmplitude
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

theorem expectation (A : Finset (Edge (Site c))) (b : ℝ) (Q : Config G c)
    (F : A → G.El → ℝ) :
    (∫ V, S.noise b Q V * ∏ i : A, F i (V i.val) ∂prior G c) =
      ∏ i : A, ∫ v, link S b (Q i.val) v * F i v ∂G.probHaar := by
  classical
  let L (i : A) (v : G.El) := link S b (Q i.val) v * F i v
  calc _ = ∫ x, branch S A b Q x * ∏ i : A, F i (x i)
        ∂(Measure.pi fun _ : A => G.probHaar) := by
          simpa only [smul_eq_mul,readLinks] using
            noise_pairing S A b Q (fun x => ∏ i : A, F i (x i))
       _ = ∫ x, ∏ i : A, L i (x i) ∂(Measure.pi fun _ : A => G.probHaar) := by
          apply integral_congr_ae
          filter_upwards with x
          exact Finset.prod_mul_distrib.symm
       _ = _ := integral_fintype_prod_eq_prod L

def series (P : ChartRatio G) (A : Finset (Edge (Site c))) (Q : Config G c)
    (F : A → G.Mat → ℝ) : PowerSeries ℂ :=
  ∏ i : A, normalizedSeries S P (atPrediction (Q i.val) (fun v => F i (G.mat v)))

theorem expansion (P : ChartRatio G) (hP : LocalRatio P) (A : Finset (Edge (Site c)))
    (Q : Config G c) (F : A → G.Mat → ℝ) (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    Near (fun t => Complex.ofReal (∫ V, S.noise (t^2)⁻¹ Q V *
      ∏ i : A, F i (G.mat (V i.val)) ∂prior G c)) (series S P A Q F) := by
  classical
  have H (B : Finset A) : Near
      (fun t => ∏ i ∈ B, Complex.ofReal (∫ v, link S (t^2)⁻¹ (Q i.val) v * F i (G.mat v) ∂G.probHaar))
      (∏ i ∈ B, normalizedSeries S P (atPrediction (Q i.val) (fun v => F i (G.mat v)))) := by
    induction B using Finset.induction_on with
    | empty => simpa using (Near.fixed (1:ℂ))
    | @insert i B hi ih =>
      simp only [Finset.prod_insert hi]
      exact Near.mult (matrix S P hP (Q i.val) (F i) (hF i)) ih
  apply Near.same (H Finset.univ)
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [expectation S A (t^2)⁻¹ Q (fun i v => F i (G.mat v))]
  push_cast
  rfl


theorem measured (P : ChartRatio G) (hP : LocalRatio P) (A : Finset (Edge (Site c)))
    (U : Config G f) (F : A → G.Mat → ℝ) (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    Near (fun t => Complex.ofReal (∫ V, S.density (t^2)⁻¹ U V *
      ∏ i : A, F i (G.mat (V i.val)) ∂prior G c))
      (∑ z, C (Complex.ofReal (S.likelihood U z)) * series S P A (S.prediction U z) F) := by
  classical
  letI : IsFiniteMeasureOnCompacts (prior G c) := inferInstanceAs
    (IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Edge (Site c) => G.probHaar)))
  let probe (V : Config G c) := ∏ i : A, F i (G.mat (V i.val))
  have hc : Continuous probe := by
    apply continuous_finsetProd
    intro i _
    exact (hF i).continuous.comp (G.continuous_mat.comp (continuous_apply i.val))
  have split (b : ℝ) : (∫ V, S.density b U V * probe V ∂prior G c) =
      ∑ z, S.likelihood U z * ∫ V, S.noise b (S.prediction U z) V * probe V ∂prior G c := by
    have hi z : Integrable (fun V : Config G c => S.likelihood U z *
        (S.noise b (S.prediction U z) V * probe V)) (prior G c) := by
      have hn : Continuous (S.noise b (S.prediction U z)) := by
        unfold StepData.noise StepData.penaltyWeight
        fun_prop
      exact (continuous_const.mul (hn.mul hc)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    unfold StepData.density
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [integral_finsetSum _ (fun z _ => hi z)]
    simp_rw [integral_const_mul]
  have H z := Near.mult (Near.fixed (Complex.ofReal (S.likelihood U z)))
    (expansion S P hP A (S.prediction U z) F hF)
  apply Near.same (Near.terms_at Finset.univ (fun z _ => H z))
  apply Filter.Eventually.of_forall
  intro t
  change (∑ z, Complex.ofReal (S.likelihood U z) *
    Complex.ofReal (∫ V, S.noise (t^2)⁻¹ (S.prediction U z) V * probe V ∂prior G c)) =
      Complex.ofReal (∫ V, S.density (t^2)⁻¹ U V * probe V ∂prior G c)
  rw [split]
  push_cast
  rfl

end YM.Integration.WilsonSmoothCylinder
