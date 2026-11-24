import YM.FVA2.Laplace

/-! transport real stationarity moments to equivalent tangent space. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GermLaplace
open Filter Function Set Metric PertExtension FormalOPE.RG10 PertExtension.Series.Radial PertExtension.Series.Tested
open FormalOPE.RG10.Inherit MeasureTheory Finset PertExtension.Series
open scoped Topology ContDiff BigOperators Classical

variable {E F : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
   [NormedAddCommGroup F][NormedSpace ℝ F]

lemma jet_pull (m:F→L[ℝ] E) (g:E→ℝ)(h:ContDiffAt ℝ ∞ g 0)(x:F)(j:ℕ): jet (g ∘ m) j x=jet g j (m x):= by
     have hv : ContDiffAt ℝ ∞ (g ∘ m) 0 := ContDiffAt.comp (f:=m) 0 (by rw [map_zero]; exact h) m.contDiff.contDiffAt
     rw [homogeneous_derivative _ x j (hv.of_le (WithTop.coe_le_coe.mpr le_top)),homogeneous_derivative g _ j (h.of_le (WithTop.coe_le_coe.mpr le_top))]; simp_rw [Function.comp_apply, map_smul]
lemma jet_scale (c:ℝ) {g:E→ℝ} (h:ContDiffAt ℝ ∞ g 0) (j:ℕ) : jet (c • g) j=c • jet g j:= by
     ext x; rw [homogeneous_derivative _ x j ((show ContDiffAt ℝ ∞ (c • g) 0 from h.const_smul c).of_le (WithTop.coe_le_coe.mpr le_top)), Pi.smul_apply, homogeneous_derivative g x j (h.of_le (WithTop.coe_le_coe.mpr le_top))]; simp_rw [Pi.smul_apply, smul_eq_mul,iteratedDeriv_const_mul_field]; ring

lemma term_pull (m:F→L[ℝ] E) {g K:E→ℝ} (h:ContDiffAt ℝ ∞ g 0)(hk:ContDiffAt ℝ ∞ K 0) (j:ℕ)(x:F): normTerm (K∘m) (g∘m) j x=normTerm K g j (m x) := by
   have he (k:ℕ) : layers (g ∘ m) k x=layers g k (m x):= by unfold layers; rw [jet_pull _ _ h,jet_pull _ _ h]
   have hv (p r:ℕ): Zone.TaylorPow (layers (g∘ m)) p r x= Zone.TaylorPow (layers g) p r (m x):= by induction p generalizing r with| zero=> unfold Zone.TaylorPow; split<;>rfl| succ p ih=> simp only [Zone.TaylorPow, Zone.mul]; exact sum_congr rfl fun i _=> congr_arg₂ (·*·) (ih i.1) (he i.2)
   unfold normTerm integrandSeries kernel Zone.mul expsum; simp_rw [jet_pull _ _ h, jet_pull _ _ hk, hv]
variable [MeasurableSpace E](μ:Measure E)
lemma moment_scale (c:ℝ)(g:E→ℝ){K:E→ℝ} (h:ContDiffAt ℝ ∞ K 0): moment μ (c • K) g=c • moment μ K g:= by
   ext i; unfold moment normTerm integrandSeries Zone.mul; simp_rw [jet_scale c h, Pi.smul_apply,smul_eq_mul,mul_assoc, ← Finset.mul_sum, mul_assoc c, integral_const_mul]
lemma moment_reindex (m:F≃L[ℝ] E) [MeasurableSpace F][BorelSpace E][BorelSpace F]
    (ν:Measure F)(hp:MeasurePreserving m ν μ){K g:E→ℝ}(hk:ContDiffAt ℝ ∞ K 0)(h:ContDiffAt ℝ ∞ g 0): moment μ K g=moment ν (K ∘ m) (g ∘ m):= by
    ext i; have he (x:F): normTerm (K∘ m) (g∘ m) i x= _:= term_pull m.toContinuousLinearMap h hk i x
    unfold moment; simp_rw [he]; exact (hp.integral_comp m.toHomeomorph.measurableEmbedding _).symm
end YM.FVA2.GermLaplace
