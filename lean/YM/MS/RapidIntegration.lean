import YM.MS.Differentiation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Line integration at the correct measure cost, with all external derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real Filter MeasureTheory Module ContinuousLinearMap
open scoped Topology ContDiff
variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Scale ι} {D : ι → Set E}
lemma norm_extDer {f : E×F→G} (h : ContDiff ℝ ∞ f) (i:E) (x:F) (j:ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : F => f (i,q)) x‖ ≤ ‖iteratedFDeriv ℝ j f (i,x)‖ := by
   rw [extDer h];
   apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
   rw [Finset.prod_const,Finset.card_univ]
   exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ..))

def Scale.dust (S : Scale ι) (d : ℕ) (i:ι) (p : E) : ℝ := (S.weight i p ^ d)⁻¹
omit [NormedSpace ℝ E] in
lemma Scale.dust_pos (d : ℕ) i (p : E) : 0 < S.dust d i p := inv_pos.mpr (pow_pos (S.weight_pos _ _) _)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Different measures will use this same test. h-smoothing volume factors not embedded in mass. -/
structure Reserve (S : Scale ι) (D : ι → Set E) (μ : ι → Measure E) (d : ℕ) : Prop where
   dom i : ∀ᵐ p ∂μ i, p ∈ D i
   integrable (i : ι) : Integrable (S.dust d i) (μ i)

namespace Rapid
variable {μ : ι → Measure E} {d : ℕ} {f : ι → E×F→G} {w : ι → ℝ}
variable (V : Reserve S D μ d) (h : Rapid S D f w)
include h
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma dominates (j b : ℕ) : ∃ C : ℝ, 0<C ∧ ∃ k : ℕ, ∀ i p q, p ∈ D i →
    ‖iteratedFDeriv ℝ j (fun x : F=> f i (p,x)) q‖ ≤ C * S.full.cheap i q ^ k * (w i*S.length i^j) * S.dust b i p := by
   obtain ⟨C,hC,k,hK⟩:= (h b).quoted j; refine ⟨C,hC,k, fun i p q hp=>?_⟩
   apply (norm_extDer (h.smooth i) ..).trans ((hK i (p,q) hp).trans ?_)
   change C* S.full.cheap i q^k*(w i / _ * _) ≤ _
   apply le_of_eq; unfold Scale.dust; simp only [div_eq_mul_inv]; ring
include V
lemma major (i : ι) : Majorant (μ i) fun p (x : F) => f i (p,x) where
  smooth := Filter.Eventually.of_forall fun p => (h.smooth i).comp (by fun_prop : ContDiff ℝ ∞ fun x : F => (p,x))
  borel j x := by
    have e (p) := extDer (h.smooth i) x p j
    simp_rw [e]
    let L := ContinuousMultilinearMap.compContinuousLinearMapL (F := G) (fun _ : Fin j => ContinuousLinearMap.inr ℝ E F)
    have he : Continuous fun p=> L (iteratedFDeriv ℝ j (f i) (p,x)) := L.continuous.comp (((h.smooth i).continuous_iteratedFDeriv (m:=j) (by exact_mod_cast le_top)).comp (by fun_prop : Continuous fun p : E => (p,x)))
    exact he.aestronglyMeasurable
  major j p := by
    obtain ⟨C,hC,k,hk⟩:= h.dominates j d
    let L (i) (R:ℝ):= S.basic i*(1+S.length i*R)
    let K i := C*L i (‖p‖+1)^k*(w i*S.length i^j)
    refine ⟨Metric.ball 0 (‖p‖+1), Metric.isOpen_ball.mem_nhds (by simp), _, (V.integrable i).const_mul (K i), ?_⟩
    refine (V.dom i).mono fun a ha q hq=> (hk i a q ha).trans ?_
    have hw := h.nn i (a,q) ha; dsimp only at hw; have hr:= S.pos i; have hb:= S.full.one_le i q (mem_univ _); have hU:= Scale.dust_pos (S:=S) d i a
    have he : S.full.cheap i q ≤ L i (‖p‖+1) := by
       apply mul_le_mul_of_nonneg_left (α:=ℝ) _ (S.basic_pos i).le; unfold Scale.weight; gcongr; exact le_of_lt (by simpa using hq)
    unfold K; gcongr

lemma integrates (i : ι) (p : F) : Integrable (fun q=> f i (q,p)) (μ i) := (h.major V i).values p
lemma consumes [CompleteSpace G] {a : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (H : S.full.Le (fun i (_:F) => ∫ q, S.dust d i q ∂(μ i)) (fun i _=> a i)) :
    Bound S (fun i p => ∫ q, f i (q,p) ∂μ i) (fun i=> w i*a i) := by
    refine ⟨fun i=> (h.major V i).contDiff,fun j=>?_⟩
    obtain ⟨C,hC,k,hk⟩:=h.dominates j d; obtain ⟨J,hJ,e,H⟩:= H
    refine ⟨C*J,by positivity,k+e,fun i p _=>?_⟩
    specialize hw i; have hs:=S.full.cheap_pos (i:=i) (p:=p) (mem_univ _); have hp:= S.pos i
    let K:= C * S.full.cheap i p^k*(w i * S.length i^j)
    dsimp only; rw [(h.major V i).identity]
    apply le_trans (norm_integral_le_of_norm_le ((V.integrable i).const_mul K) ((V.dom i).mono fun q hq=> hk i q p hq))
    rw [integral_const_mul];
    apply (mul_le_mul_of_nonneg_left (H i p trivial) (show 0 ≤ K by unfold K; positivity)).trans
    apply le_of_eq; dsimp only [K]; rw [pow_add]; ring
end Rapid
namespace Reserve
variable {μ : Measure E} [Measure.IsAddHaarMeasure μ]
include S
lemma dustInteg (i) (b : ℕ) (h : finrank ℝ E < b) : Integrable (S.dust b i) μ := by
    have H : Integrable (fun p : E=> (1+‖p‖)^(-(b:ℝ))) μ:= integrable_one_add_norm (by exact_mod_cast h)
    convert! H.comp_smul (S.pos i).ne' using 1
    funext; rw [Real.rpow_neg (by positivity),Real.rpow_natCast, norm_smul_of_nonneg (S.pos i).le]; rfl
lemma cutHaar (hv : ∀ i, MeasurableSet (D i)) (d : ℕ) (h : finrank ℝ E < d) :
    Reserve S D (fun i=> μ.restrict (D i)) d :=
    ⟨fun i=> ae_restrict_mem (hv i), fun i=> (dustInteg (S:=S) i d h).restrict⟩
lemma cover (d : ℕ) (h : finrank ℝ E < d) : Reserve S (fun _=> univ) (fun _=> μ) d := by
    simpa using cutHaar (S:=S) (μ:=μ) (fun _=> MeasurableSet.univ) d h
omit [NormedSpace ℝ F] in
lemma cutoff_mass (b : ℕ) (h : finrank ℝ E < b) : S.full.Le (fun i (_:F) => ∫ q in D i, S.dust b i q ∂μ) fun i _ => (S.length i ^ finrank ℝ E)⁻¹ := by
  let K : E→ℝ := fun x => ((1+ ‖x‖)^b)⁻¹
  let a := ∫ p, K p ∂μ
  refine ⟨max a 1, lt_max_of_lt_right zero_lt_one, 0, fun i p _=>?_⟩
  simp only [pow_zero, mul_one]
  have hp:= S.pos i
  calc
    _ ≤ ∫ q, S.dust b i q ∂μ := setIntegral_le_integral (dustInteg _ b h) (.of_forall fun p=>(Scale.dust_pos ..).le)
    _ = a*(S.length i ^ finrank ℝ E)⁻¹ := by
       rw [show S.dust b i = _ from funext (show ∀ x : E, S.dust b i x = K (S.length i • x) from fun x=>by simp only [K,norm_smul_of_nonneg hp.le]; rfl), Measure.integral_comp_smul_of_nonneg _ _ _ (hR:=hp.le), smul_eq_mul, mul_comm]
    _ ≤ _ := by gcongr; exact le_max_left ..
end Reserve
end YM.MS
