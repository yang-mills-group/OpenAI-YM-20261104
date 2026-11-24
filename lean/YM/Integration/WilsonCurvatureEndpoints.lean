import YM.Integration.LocalComparisonUniformModelPrice
import YM.OPE.Therm.Rite

/-! The original transported curvature slots charge only their plaquette endpoints for a magnitude estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCurvatureEndpoints
open MeasureTheory Filter Set Finset Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {V : Type} {D : V → ComparisonDensity.Address.Orbit}

def face (s : Slot) (x : Site n) : Face (Per n) := (wrap n s.offset+x,s.plaq)

theorem coordinate (s : Slot) (x : Site n) (U : Config G n) (j : G.ColorIndex) :
    |s.atSite U x j| ≤ G.chord (faceValue U (face s x)) := by
  calc
    _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j) (s.atSite U x)| := by
      simp only [EuclideanSpace.basisFun_inner]
    _ ≤ ‖s.atSite U x‖ := (abs_real_inner_le_norm _ _).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
    _ = ‖G.curvature (faceValue U (face s x))‖ := by
      unfold Slot.atSite Slot.eval
      rw [G.norm_adjoint]
      unfold faceValue
      rw [travel_at]
      rfl
    _ ≤ _ := G.curvature_norm _

variable {k : ℕ} (T : Token G n (fun v => (D v).Mood) k)
variable (x : TestSpace D) (hc : (∑ j, ‖T.gem j x‖) ≤ T.coin)

include hc in
theorem cold (t : ℝ) (ht : 0 ≤ t) (U : Config G n)
    (h : ∀ i, G.chord (faceValue U (face (T.path i) T.root)) ≤ t) :
    ‖T.read x U‖ ≤ T.coin*t^k := by
  have hcoord (i : Fin k) (j : G.ColorIndex) : |(T.path i).atSite U T.root j| ≤ t :=
    (coordinate _ _ _ _).trans (h i)
  unfold Token.read Token.touch
  calc
    _ ≤ ∑ b, ‖(↑(∏ i, (T.path i).atSite U T.root (b i)) : ℂ) * T.gem b x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b, ‖T.gem b x‖ * t^k := by
      apply Finset.sum_le_sum
      intro b _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
      have hp : (∏ i : Fin k, |(T.path i).atSite U T.root (b i)|) ≤ t^k := by
        calc
          _ ≤ ∏ _i : Fin k, t :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hcoord i (b i))
          _ = _ := by simp
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = (∑ b, ‖T.gem b x‖) * t^k := (Finset.sum_mul _ _ _).symm
    _ ≤ T.coin * t^k := mul_le_mul_of_nonneg_right hc (by positivity)


def hit (p : Face (Per n)) (t : ℝ) : Config G n → ℝ := (trigger p t).indicator (fun _ => 1)

include hc in
theorem split (t : ℝ) (ht : 0 ≤ t) (U : Config G n) :
    ‖T.read x U‖ ≤ T.coin * (t^k + 2^k * ∑ i, hit (face (T.path i) T.root) t U) := by
  have hcoin : 0 ≤ T.coin := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hc
  have hh (i : Fin k) : 0 ≤ hit (face (T.path i) T.root) t U := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases good : ∀ i, G.chord (faceValue U (face (T.path i) T.root)) ≤ t
  · exact (cold T x hc t ht U good).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hh i))) hcoin)
  · push Not at good
    obtain ⟨i,hi⟩ := good
    have him : U ∈ trigger (face (T.path i) T.root) t := hi
    have he : hit (face (T.path i) T.root) t U = 1 := Set.indicator_of_mem him _
    have hone : 1 ≤ ∑ j, hit (face (T.path j) T.root) t U := he.symm.le.trans
      (Finset.single_le_sum (fun j _ => hh j) (Finset.mem_univ i))
    have htwo := cold T x hc 2 (by norm_num) U (fun j => G.chord_le_two _)
    apply htwo.trans (mul_le_mul_of_nonneg_left _ hcoin)
    calc
      (2 : ℝ)^k ≤ 2^k * ∑ j, hit (face (T.path j) T.root) t U := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (show 0 ≤ (2:ℝ)^k by positivity)
      _ ≤ _ := le_add_of_nonneg_left (pow_nonneg ht k)

include hc in
theorem measured (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (t δ : ℝ) (ht : 0 ≤ t)
    (hδ : ∀ p : Face (Per n), μ.real (trigger p t) ≤ δ) :
    (∫ U, ‖T.read x U‖ ∂μ) ≤ T.coin * (t^k + 2^k * ((k:ℝ)*δ)) := by
  have hcoin : 0 ≤ T.coin := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hc
  let event (i : Fin k) := hit (G := G) (face (T.path i) T.root) t
  have hi (i : Fin k) : Integrable (event i) μ := (integrable_const _).indicator (fire_meas _ _)
  have hej := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hI : (∫ U, ∑ i, event i U ∂μ) ≤ (k:ℝ)*δ := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    calc
      _ ≤ ∑ _i : Fin k, δ := by
        apply Finset.sum_le_sum
        intro i _
        change (∫ U, (trigger _ t).indicator (fun _ : Config G n => (1:ℝ)) U ∂μ) ≤ δ
        rw [integral_indicator (fire_meas _ _),setIntegral_const,smul_eq_mul,mul_one]
        exact hδ _
      _ = _ := by simp
  calc
    _ ≤ ∫ U, T.coin * (t^k + 2^k * ∑ i, event i U) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (((integrable_const _).add (hej.const_mul _)).const_mul _)
        (ae_of_all _ fun U => split T x hc t ht U)
    _ = T.coin * (t^k + 2^k * ∫ U, ∑ i, event i U ∂μ) := by
      rw [integral_const_mul,integral_add (integrable_const _) (hej.const_mul _),integral_const,probReal_univ,one_smul,integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left hI (by positivity)) _) hcoin

theorem original {H : History G} (Y : H.Selected) (P : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m ≤ N → ∀ (p : ℕ) (k : ℕ), ∀
      (T : Token G (H.S.side m p) (fun v => (D v).Mood) k) (x : TestSpace D), (∑ j, ‖T.gem j x‖) ≤ T.coin →
      (∫ U, ‖T.read x U‖ ∂scene H N p m) ≤
        T.coin * ((cool H.levels m)^k + 2^k*((k:ℝ)*vanishP H.levels m)) := by
  filter_upwards [rare P hG Y] with m h
  intro N hm p k T x hc
  letI := probability (H:=H) (p:=p) Y hm
  apply measured T x hc _ _ _ _ (h N hm p)
  unfold cool Calendar.hatCoupling
  positivity

end YM.Integration.WilsonCurvatureEndpoints
end
