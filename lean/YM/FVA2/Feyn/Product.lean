import YM.FVA2.Laplace.Receipt
import YM.PertExtension.PTBills
/-!
# Independent Gaussian factor in the (complete, all perturbative orders) diagram expansion
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Feyn
open Function Set Filter Finset MeasureTheory PertExtension PertExtension.Series
open Laplace Tested Radial GaussianScore FormalOPE.RG10.MultiGauge Splice Stack
open scoped Topology ContDiff BigOperators Classical
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable (f K O:F→ℝ) (L:Law E)
/-- gauge Gaussian cost -/
def warmth (x:E):ℝ := L.P x x / 2
omit [FiniteDimensional ℝ E] in
@[simp] lemma heat_zero : warmth L 0=0:= by simp [warmth]
lemma heater : ContDiff ℝ ω (warmth L):= by
 let P : E→ₗ[ℝ] E→L[ℝ]ℝ:={toFun:=fun x=> LinearMap.toContinuousLinearMap (L.P x),map_add':=by intros; apply ContinuousLinearMap.ext; intro x; simp, map_smul':=by intros; apply ContinuousLinearMap.ext; intro x; simp}
 exact (P.toContinuousLinearMap.contDiff.clm_apply contDiff_id).div_const _
omit [FiniteDimensional ℝ E] in
lemma funds (x:E)(t:ℝ): warmth L (t • x)=t^2 • warmth L x:= by unfold warmth; simp [map_smul,pow_two]; ring

def outer (p:E×F) := warmth L p.1 + f p.2
local notation "χ" => outer f L
lemma lever (K:F→ℝ)(hK:ContDiffAt ℝ ∞ K 0)(t: F)(x:E) (n:ℕ): jet (fun p:E×F=> K p.2) n (x,t)=jet K n t:= by
 have hh := directions ( hK.comp (x:=0) (f:=Prod.snd) (by fun_prop) : ContDiffAt ℝ ∞ (K ∘ (@Prod.snd E F)) 0 ) (x,t)
 exact congr_fun (hh.unique ( directions hK t )) n
lemma power (h: ContDiffAt ℝ ∞ f 0) (x:E)(t:F)(n:ℕ): jet (outer f L) n (x,t)=(if n=2 then warmth L x else 0)+jet f n t:= by
 have h₁(e:ℝ): χ (e • (x,t)) = e^2 • warmth L x + f (e • t) := congr_arg (· + _) (funds L x e)
 have hh : ContDiffAt ℝ ∞ ( χ ) 0:= ((heater L|>.contDiffAt.of_le le_top).comp (x:=0) (f:=Prod.fst) (by fun_prop)).add (h.comp (x:=0) (f:=Prod.snd) (by fun_prop))
 have hs := directions hh (x,t); simp_rw [h₁] at hs; exact congr_fun (hs.unique ((Aspiration.single _ 2).add (directions h t))) n
lemma feasible (h:Laplace.Steep f): Laplace.Steep (χ):= by
 have hh := h.smooth; refine ⟨⟨ ((heater L|>.contDiffAt.of_le le_top).comp (x:=0) (f:=Prod.fst) (by fun_prop)).add (hh.comp (x:=0) (f:=Prod.snd) (by fun_prop)), by simp [outer,h.base0], fun ⟨x,t⟩=> by rw [power f L hh, if_neg (by decide), h.base1 t, zero_add]⟩,?_⟩
 obtain ⟨c,hc,H⟩:= L.slope; obtain ⟨d,hd,K⟩:= h.gap; refine ⟨ min c d,lt_min hc hd,fun ⟨x,t⟩=> ?_⟩
 rw [power f L hh, if_pos rfl, Prod.norm_def]; rcases le_total ‖x‖ ‖t‖ with hl|hl
 · rw [max_eq_right hl]; exact (mul_le_mul_of_nonneg_right (min_le_right ..) (sq_nonneg _)).trans ( (K _).trans (le_add_of_nonneg_left ((mul_nonneg hc.le (sq_nonneg _)).trans (H x))) )
 rw [max_eq_left hl]; exact (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _)).trans ( le_trans (b:=warmth L x) ( H _ ) (le_add_of_nonneg_right ((mul_nonneg hd.le (sq_nonneg _)).trans (K t))) )

open PowerSeries
variable (h:Steep f)(hK: ContDiffAt ℝ ∞ K 0)
include h
lemma revenue (x:E)(t:F) : Stack.read (x,t) (advancing (χ))= Stack.read t (advancing f):= by
 apply PowerSeries.ext; intro i; rw [levels,levels,Radial.layers,Radial.layers,power f L h.smooth,power f L h.smooth]; cases i with | zero=> simp | succ i=> simp
lemma after (x:E)(t:F) : Stack.read (x,t) (exponential (advancing (χ)))= Stack.read t (exponential (advancing f)):= by
 apply PowerSeries.ext; intro i; simp_rw [reading_term, exponential,coeff_mk,←reading_term, _root_.map_sum, _root_.map_mul, _root_.map_pow, rollThrough, revenue f L h]
lemma kernel_fee (x:E)(t:F): Radial.kernel (χ) (x,t)=L.kern x*Radial.kernel f t:= by rw [Radial.kernel,power f L h.smooth,if_pos rfl,neg_add, Real.exp_add]; unfold Law.kern warmth; rw [neg_div]; rfl

include hK
lemma petals (x:E)(t:F)(n:ℕ) : normTerm (K ∘ Prod.snd) (χ) n (x,t)=L.kern x * normTerm K f n t:= by
 unfold normTerm; rw [kernel_fee f L h, ←Laplace.deck (χ), ←Laplace.deck f,←reading_term,←reading_term, show Stack.read (x,t) (sink (K ∘ Prod.snd) (χ)) = Stack.read t (sink K f) from ?_]; ring
 unfold sink; simp_rw [_root_.map_mul, after f L h]; congr 1; exact PowerSeries.ext fun i=> by rw [read_rise,read_rise]; exact lever _ hK t x i
-- avoid local notation for implicits from user.Measures
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (μ:Measure E)[μ.IsAddHaarMeasure](ν:Measure F)[ν.IsAddHaarMeasure]
omit [BorelSpace E] [BorelSpace F] in
theorem prism : rows (μ.prod ν) (K ∘ Prod.snd) (χ) = C (amount μ L) * rows ν K f := by
 apply PowerSeries.ext; intro i; rw [coeff_C_mul,rows,rows,coeff_mk,coeff_mk]; unfold moment amount;
 rw [show (fun u:E×F=>normTerm (K ∘ Prod.snd) (χ) i u) =(fun u:E×F=> L.kern u.1*normTerm K f i u.2) from funext (fun ⟨x,t⟩=> petals f K L h hK x t i) ]; exact integral_prod_mul ..
lemma settled (hk:K 0=1)(ho:ContDiffAt ℝ ∞ O 0) : Laplace.pricetag (μ.prod ν) (K ∘ Prod.snd) (χ) (O ∘ Prod.snd) = Laplace.pricetag ν K f O:= by
 unfold Laplace.pricetag; rw [← show ((O*K) ∘ @Prod.snd E F)= (O ∘ Prod.snd)*(K ∘ Prod.snd) from rfl, prism f K L h hK μ ν, prism f (O*K) L h (ho.mul hK) μ ν ]; exact shed _ _ _ (ready ν h hk) (amount_pos μ L)
end YM.FVA2.Feyn
