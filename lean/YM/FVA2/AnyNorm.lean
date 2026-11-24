import YM.FVA2.OrbitConnection
import YM.PertExtension.GaussianScore
import YM.FormalOPE.RG10.MultiGauge.Engine
/-!
# Same finite-regulator Laplace using any linear bases or volume constants

Here `M` does not track factors of `g_N` from scaling all variables; it *does* include the
volume at the chosen normalization (`ν` etc.). Denominators are the `M` unmarked vacuum-series.
Use the identical base/dimension for the source and vacuum. Additional fact used for smeared
linear gauges: adding an independent (all-order free) gaussian multiplies all rows by the same
constant. Direct proof from Radial.moment. No claims of removing other saddles here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GermLaplace.Rates
open MeasureTheory Function Filter FormalOPE.RG10 PertExtension PertExtension.Series PertExtension.Series.Radial MultiGauge PowerSeries
open GaussianScore MeasureTheory.Measure
open scoped Topology ContDiff Classical BigOperators NNReal
variable {E F : Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F][FiniteDimensional ℝ E][FiniteDimensional ℝ F]
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (μ : Measure E)[IsAddHaarMeasure μ](ν : Measure F)[IsAddHaarMeasure ν]

def V (g:E≃L[ℝ] F): ℝ≥0:= addHaarScalarFactor (μ.map g) ν
omit [FiniteDimensional ℝ E] in
lemma V_funded (g:E≃L[ℝ] F): μ.map g= V μ ν g • ν:= isAddLeftInvariant_eq_smul _ _
omit [FiniteDimensional ℝ E][FiniteDimensional ℝ F] in
lemma V_pos (g:E≃L[ℝ] F): 0 < (V μ ν g:ℝ):= by unfold V; exact_mod_cast addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map g) ν

def M (J f:E→ℝ) : PowerSeries ℝ:= PowerSeries.mk (Radial.moment μ J f)
def ratioM (K J f:E→ℝ): PowerSeries ℝ:= M μ J f * (M μ K f)⁻¹
omit [FiniteDimensional ℝ E] in
lemma pulled_V (g:E≃L[ℝ] F){f J:F→ℝ}(hf:ContDiffAt ℝ ∞ f 0)(hi: ContDiffAt ℝ ∞ J 0): M μ (J ∘ g) (f ∘ g) = PowerSeries.C (V μ ν g:ℝ) * M ν J f := by
     unfold M; have hx : MeasurePreserving g μ (μ.map g):= ⟨by fun_prop,rfl⟩; rw [← moment_reindex (μ.map g) g μ hx hi hf, V_funded μ ν g]; apply PowerSeries.ext; intro i; rw [ coeff_C_mul, coeff_mk, coeff_mk, Radial.moment,integral_smul_nnreal_measure ]; rfl
lemma agree {K f x : PowerSeries ℝ}{c d : PowerSeries ℝ}(h: constantCoeff K≠0)(hy:constantCoeff d ≠0)(hf: c=f*x)(hz:d=f*K): c*d⁻¹=x*K⁻¹:= by
      symm; apply (eq_mul_inv_iff_mul_eq hy).mpr; rw [hf,hz, show x*K⁻¹*(f*K)= f*x*(K*K⁻¹) by ring,PowerSeries.mul_inv_cancel K h,mul_one]
omit [FiniteDimensional ℝ E] [BorelSpace E] [IsAddHaarMeasure μ] in
lemma starts (J f:E→ℝ) : constantCoeff (M μ J f) = J 0 * ∫ x:E,kernel f x ∂μ:= by
     unfold M; rw [constantCoeff_mk]; unfold Radial.moment normTerm; simp_rw [integrandSeries,Zone.mul]; simp [expsum,Zone.TaylorPow, integral_const_mul]
variable {f J K:E→ℝ}
lemma market (h:Gap f)(hh:Radial.Stationary f)(hJ: ContDiffAt ℝ ∞ J 0)(hf:0<J 0): 0< constantCoeff (M μ J f):= by
     unfold M; rw [constantCoeff_mk]; let g:=normTerm J f 0; have hg (x:E):0<g x:= by
          unfold g normTerm; simp [integrandSeries,Zone.mul,expsum,Zone.TaylorPow]; exact mul_pos hf kernel_pos
     exact integral_pos_of_integrable_nonneg_nonzero (Smooth.continuousTerms J f 0) (hh.integrableTerm μ hJ h) (fun x=> (hg x).le) (x:=0) (hg 0).ne'

omit [FiniteDimensional ℝ E] in
lemma other_basis (g:E≃L[ℝ] F){f J K:F→ℝ}(hf:ContDiffAt ℝ ∞ f 0)(hi:ContDiffAt ℝ ∞ J 0)(hK:ContDiffAt ℝ ∞ K 0)(hz:constantCoeff (M ν K f)≠0): ratioM μ (K ∘ g) (J ∘ g) (f ∘ g)=ratioM ν K J f:=
   agree hz (by rw [pulled_V μ ν g hf hK,map_mul]; exact mul_ne_zero ((PowerSeries.constantCoeff_C (V μ ν g:ℝ)) ▸ (V_pos μ ν g).ne') hz ) (pulled_V μ ν g hf hi) (pulled_V μ ν g hf hK)

omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F][BorelSpace F] in
lemma rebase_gap (g:E≃L[ℝ] F){f:F→ℝ}(hf:ContDiffAt ℝ ∞ f 0)(h:Gap f): Gap (f ∘ g):= by
     apply Radial.quadratic_min _; intro x hx; obtain ⟨c,hc,H⟩:=h; rw [show ⇑g= g.toContinuousLinearMap from rfl, jet_pull (m:=g.toContinuousLinearMap) f hf]; exact (mul_pos hc (pow_pos (norm_pos_iff.mpr (fun e=> hx (g.injective (e.trans (map_zero _).symm)))) _)).trans_le (H _)
omit [FiniteDimensional ℝ E][FiniteDimensional ℝ F] [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F] in
lemma rebase_stat (g:E≃L[ℝ] F){f:F→ℝ}(h: Radial.Stationary f): Radial.Stationary (f ∘ g) where
    smooth := ContDiffAt.comp (g:=f) 0 (by rw [map_zero]; exact h.smooth) g.contDiff.contDiffAt
    base0 := by rw [Function.comp_apply,map_zero,h.base0]
    base1 x := by rw [show ⇑g= g.toContinuousLinearMap from rfl, jet_pull (m:=g.toContinuousLinearMap) _ h.smooth, h.base1]

-- independent centered Gaussian; in particular compare Gaussian ratios for all linear slices
variable (Γ:Law F)
def value (x:F):= Γ.P x x /2
lemma value_hot {i : WithTop ℕ∞}: ContDiff ℝ i (value Γ):= ((( LinearMap.toContinuousLinearMap (E:=F) (F':=ℝ)).toLinearMap.comp Γ.P).toContinuousLinearMap.contDiff.clm_apply contDiff_id).div_const _
lemma value_jet (v:F)(i:ℕ): jet (value Γ) i v= if i=2 then value Γ v else 0:= by
     have h(x:F)(t:ℝ): value Γ (t• x)=t^2* value Γ x:= by unfold value; rw [map_smul,map_smul,LinearMap.smul_apply]; simp [smul_eq_mul]; ring -- simplify
     rw [homogeneous_derivative (value Γ) v i (value_hot Γ|>.contDiffAt)]; simp_rw [h,iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]; split_ifs with hi <;> simp_all
lemma value_stat : Radial.Stationary (value Γ) where
     smooth := value_hot Γ|>.contDiffAt
     base0 := by simp [value]
     base1 x := by rw [value_jet,if_neg]; decide
lemma value_gap : Gap (value Γ) := by unfold Gap; simp_rw [value_jet,if_true]; exact Γ.slope
lemma value_kernel : Radial.kernel (value Γ)=Γ.kern:= by unfold Law.kern kernel; simp_rw [value_jet,if_true,value,neg_div]

def addFree (f:E→ℝ) : F × E→ℝ := (value Γ ∘ Prod.fst)+(f ∘ Prod.snd)
lemma combined_hot {i:WithTop ℕ∞} (hf:ContDiffAt ℝ i f 0) : ContDiffAt ℝ i (addFree Γ f) 0:= ((value_hot Γ).contDiffAt.comp _ contDiffAt_fst).add (hf.comp (f:=Prod.snd) (0:F × E) contDiffAt_snd)
lemma combined_jet {k:ℕ}(hf:ContDiffAt ℝ ∞ f 0)(x:F×E): jet (addFree Γ f) k x= jet f k x.2+jet (value Γ) k x.1:= by
     let p₁:=ContinuousLinearMap.fst ℝ F E; let p₂:=ContinuousLinearMap.snd ℝ F E
     change jet ((value Γ ∘ p₁)+(f ∘ p₂)) k x=_; rw [jet,iteratedFDeriv_add_apply (((value_hot Γ).comp p₁.contDiff).contDiffAt) ((hf.comp (f:=p₂) 0 contDiffAt_snd).of_le (WithTop.coe_le_coe.mpr le_top)),ContinuousMultilinearMap.add_apply,mul_add]; exact (congr_arg₂ (·+·) (jet_pull (m:=p₁) (value Γ) (value_hot Γ|>.contDiffAt) x k) (jet_pull (m:=p₂) f hf x k))|>.trans (add_comm ..)
lemma combined_stat (h:Radial.Stationary f): Radial.Stationary (addFree Γ f) where
     smooth := combined_hot Γ h.smooth
     base0 := by unfold addFree; simp [value,h.base0]
     base1 x := by rw [combined_jet Γ h.smooth, h.base1, (value_stat Γ).base1 x.1,add_zero]
lemma combined_gap (h:ContDiffAt ℝ ∞ f 0)(hh:Gap f): Gap (addFree Γ f) := by
    obtain ⟨c,hc,hC⟩:= hh; obtain ⟨d,hd,hD⟩:= value_gap Γ; refine ⟨min c d,lt_min hc hd, fun x=> ?_⟩; rw [combined_jet Γ h, Prod.norm_def]
    have hxs:=mul_nonneg hc.le (sq_nonneg ‖x.2‖); have hxf:= mul_nonneg hd.le (sq_nonneg ‖x.1‖); apply le_trans _ (add_le_add (hC x.2) (hD x.1)); rcases le_total ‖x.1‖ ‖x.2‖ with h|h
    · rw [max_eq_right h]; apply (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _)).trans (le_add_of_nonneg_right hxf)
    rw [max_eq_left h]; exact (mul_le_mul_of_nonneg_right (min_le_right ..) (sq_nonneg _)).trans (le_add_of_nonneg_left hxs)
lemma layers_combined (hf:ContDiffAt ℝ ∞ f 0)(i:ℕ)(x:F × E): layers (addFree Γ f) i x= layers f i x.2 := by unfold layers; simp_rw [combined_jet Γ hf, value_jet]; split_ifs <;> (simp_all) -- syntax
lemma norm_sync (v:F × E) (hf:ContDiffAt ℝ ∞ f 0)(hK:ContDiffAt ℝ ∞ K 0)(i:ℕ): normTerm (K ∘ Prod.snd) (addFree Γ f) i v= Γ.kern v.1 * normTerm K f i v.2:= by
    let L:=ContinuousLinearMap.snd ℝ F E
    have he (q r:ℕ):Zone.TaylorPow (layers (addFree Γ f)) q r v=Zone.TaylorPow (layers f) q r v.2 := by induction q generalizing r with| zero=> unfold Zone.TaylorPow; split<;> rfl| succ q ih=> simp only [Zone.TaylorPow,Zone.mul]; apply Finset.sum_congr rfl; intro p _; rw [ih, layers_combined Γ hf]
    have hx (v:F × E) : kernel (addFree Γ f) v=Γ.kern v.1 * kernel f v.2:= by unfold kernel; rw [combined_jet Γ hf,← value_kernel]; simp_rw [kernel, ← Real.exp_add]; congr 1; abel
    unfold normTerm integrandSeries expsum Zone.mul; simp_rw [hx,he,show (Prod.snd:F × E→E)= L from rfl,jet_pull (m:=L) _ hK]; rw [show L v=v.2 from rfl]; ring -- simp may loop
lemma add_free_const (h:ContDiffAt ℝ ∞ f 0)(hh:ContDiffAt ℝ ∞ K 0): M (ν.prod μ) (K ∘ Prod.snd) (addFree Γ f) = C (∫ x,Γ.kern x ∂ν)* M μ K f:= by apply PowerSeries.ext; intro i; rw [coeff_C_mul]; unfold M; rw [coeff_mk,coeff_mk]; unfold Radial.moment; simp_rw [norm_sync Γ _ h hh]; exact integral_prod_mul ..

end YM.FVA2.GermLaplace.Rates
