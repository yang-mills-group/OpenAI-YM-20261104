import YM.Comparison.RG02.Normal.Bound
/-!
# Fine measure at fixed pinned V and fixed choice t

Includes one-tag, posterior (under actual `π(V)` & unmarked W). All orientations
 already in S. Sum pointwise exact; prove **no zero** denominator even for
 pinned tag normalization (positive on a neighborhood of flat for every V in finite-volume).
 `S.total` does not enter this reasoning. The normalized *Markov* transport of
 source products uses full posterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Normal
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Integral Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ) (J : Config G c) (t : S.Choices) (W : Config G f→ℝ)

def view := fun U=> taggedKernel S β t U J * W U
def mass := ∫ x,view S β J t W x ∂prior G f
def total := S.push β W J

def sale := mass S β J t W / total S β J W

variable (H : Strong f W) (ok : S.patch.Branches S.kernel G)
include H ok
lemma view_bound : Envelope (view S β J t W) := (env_tagged β t ok measurable_id measurable_const).mul H.safe
omit ok in
lemma view_positive (x : Config G f) : 0 ≤ view S β J t W x:= mul_nonneg (kernel_nonneg ..) (H.positive x).le
lemma mass_pos : 0 < mass S β J t W := by
   apply (integral_pos_iff_support_of_nonneg (view_positive S β J t W H) ((view_bound S β J t W H ok).integrable _)).2
   haveI : (prior G f).IsOpenPosMeasure := by unfold prior; infer_instance
   apply Measure.measure_pos_of_mem_nhds (prior G f) (x:=(1:Config G f))
   filter_upwards [Integral.min_group ok] with x hx; apply (show 0 < view S β J t W x from ?_).ne'
   unfold view taggedKernel; rw [uncharged x hx ok]; exact mul_pos (mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Integral.count_pos)) (YM.Push.SectorMeasure.noise_pos β _ _)) (H.positive x)
lemma mass_total : ∑ v : S.Choices,mass S β J v W=total S β J W := by
   simp_rw [mass]; rw [← integral_finsetSum _ (fun i _=>(view_bound S β J i W H ok).integrable _)]
   simp only [total, StepData.push, StepData.density,view,taggedKernel,←Finset.sum_mul, smul_eq_mul]
lemma total_pos : 0<total S β J W:=coefficient_margin S J ok H (le_refl _)
lemma sale_lit : ∑ v:S.Choices,sale S β J v W=1 := by unfold sale; rw [← sum_div, mass_total S β J W H ok,div_self (total_pos S β J W H ok).ne']
lemma sale_pos : 0<sale S β J t W := div_pos (mass_pos S β J t W H ok) (total_pos S β J W H ok)

-- posterior tag measure on U = conditioned kernel at fixed tag. Restrict to Borel.
local notation "M"=> mass S β J t W
def index := (prior G f).withDensity (fun x=> ENNReal.ofReal (view S β J t W x / M))
lemma probability : IsProbabilityMeasure (index S β J t W) := by
   constructor; unfold index; rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,← ofReal_integral_eq_lintegral_ofReal
     (((view_bound S β J t W H ok).integrable _).div_const M)]; swap; exact Eventually.of_forall fun x=> div_nonneg (view_positive S β J t W H x) (mass_pos S β J t W H ok).le
   rw [integral_div, ← mass,div_self (mass_pos S β J t W H ok).ne', ENNReal.ofReal_one]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
-- generalized measure statement independent of eventual bounds; condition integrability explicitly
lemma intensity (F : Config G f→E) :
   Integrable F (index S β J t W) ↔ Integrable (fun x => (view S β J t W x) • F x) (prior G f) := by
   let v := view S β J t W
   have hi : ∀ᵐ x ∂prior G f, ENNReal.ofReal (v x/M) < ⊤ := Eventually.of_forall (fun x=>ENNReal.ofReal_lt_top)
   unfold index; rw [integrable_withDensity_iff_integrable_smul' (((view_bound S β J t W H ok).meas.div_const _).ennreal_ofReal) hi]
   have ht (x) : (ENNReal.ofReal (view S β J t W x / M)).toReal • F x=M⁻¹ • (view S β J t W x • F x) := by rw [ENNReal.toReal_ofReal (div_nonneg (view_positive S β J t W H x) (mass_pos S β J t W H ok).le), smul_smul,div_eq_mul_inv,mul_comm]
   simp_rw [ht]; exact (integrable_smul_iff (inv_ne_zero (mass_pos S β J t W H ok).ne') _)

lemma at_mass (F : Config G f→E) (_hF : Integrable F (index S β J t W)) : M • (∫ x, F x ∂index S β J t W)=∫ x,view S β J t W x • F x ∂prior G f := by
   unfold index
   rw [integral_withDensity_eq_integral_toReal_smul (((view_bound S β J t W H ok).meas.div_const _).ennreal_ofReal),← integral_smul]; swap; exact Eventually.of_forall (fun x=>ENNReal.ofReal_lt_top)
   apply integral_congr_ae; filter_upwards with x
   rw [ENNReal.toReal_ofReal,smul_smul,mul_div_cancel₀ ..]; exacts [(mass_pos S β J t W H ok).ne', div_nonneg (view_positive S β J t W H x) (mass_pos S β J t W H ok).le]

def assign (p : S.Choices→ Config G f→E) : E := ∑ v : S.Choices, sale S β J v W • ∫ x, p v x ∂index S β J v W
lemma expected (p : S.Choices→ Config G f → E) (h : ∀ v, Integrable (p v) (index S β J v W)) :
    total S β J W • assign S β J W p=∑ v:S.Choices, ∫ x, view S β J v W x • p v x ∂prior G f := by
   unfold assign; rw [smul_sum]; refine sum_congr rfl fun v _=>?_; rw [smul_smul,sale,mul_div_cancel₀ .., at_mass S β J v W H ok _ (h v)]; exact (total_pos S β J W H ok).ne'
end YM.Comparison.RG02.Normal
