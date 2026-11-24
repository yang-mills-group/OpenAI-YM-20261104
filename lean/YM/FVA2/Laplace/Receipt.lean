import YM.FVA2.Laplace.Diffeo
import YM.FormalOPE.RG10.MultiGauge.Membership
/-!
# Normalized moments = Gaussian coefficient ratio with RG10 Ticket

Use any `GaussianScore.Law` realizing the stationary kernel and report the exact nonzero vacuum
normalization. Our coefficients are independent of the mass determinant factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Laplace
open Function Set Filter Metric MeasureTheory PertExtension Series Radial Series.Tested GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge MultiGauge.Splice
open PowerSeries
open scoped ContDiff Topology Classical BigOperators
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasurableSpace E][BorelSpace E]
variable (μ:Measure E) [Measure.IsAddHaarMeasure μ]
variable (f K O:E→ℝ)
local notation "FP" => PowerSeries ℝ
def sink (K f : E→ℝ) : Ticket E:= Stack.exponential (Stack.advancing f)* Stack.rise K
omit [MeasurableSpace E] [BorelSpace E] in
lemma dreaming {q:E→ℝ}(h:K=ᶠ[𝓝 0] q) : Stack.rise K=Stack.rise q:= by
 apply PowerSeries.ext; intro n; rw [Stack.rise,Stack.rise,coeff_mk,coeff_mk]; exact Subtype.ext (congr_fun (jet_germ h) n)
omit [MeasurableSpace E] [BorelSpace E] in
lemma deck (n:ℕ)(u:E): (coeff n (sink K f)).val u= integrandSeries f K n u:=by
 rw [←Stack.reading_term,sink,mul_comm,_root_.map_mul,coeff_mul]; unfold integrandSeries Zone.mul; exact Finset.sum_congr rfl fun j _=> by rw [Stack.read_rise,Stack.business]
def rows (K f : E→ℝ) := PowerSeries.mk (moment μ K f)
/-- The normalized Taylor/Wick prescription. -/
def pricetag (K f O : E→ℝ) : FP:= rows μ (O*K) f * (rows μ K f)⁻¹
variable (Λ:Law E)
def amount (Λ:Law E) : ℝ:= ∫ x, Λ.kern x ∂μ
local notation "I" => input Λ μ
lemma amount_pos : 0<amount μ Λ:= Splice.positive ..
theorem cuts (hk:Λ.kern= Radial.kernel f): rows μ K f= C (amount μ Λ) * I (sink K f):= by
 apply PowerSeries.ext; intro i
 rw [rows,coeff_mk, coeff_C_mul]; unfold moment; let Z:=amount μ Λ; have hz:0<Z:=amount_pos μ Λ; unfold input throughPrice; simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk,coeff_mk]; change (∫ x,normTerm K f i x ∂μ)= Z * ((∫ x,(coeff i (sink K f)).val x * Λ.kern x ∂μ)/Z)
 simp_rw [normTerm,← deck f K,hk.symm]; field_simp
omit [MeasurableSpace E] [BorelSpace E] in
lemma stamp (h:K 0=1): incline (sink K f):= by
 unfold sink incline; rw [_root_.map_mul,Stack.initial,one_mul,←coeff_zero_eq_constantCoeff_apply]; exact Subtype.ext (funext (fun i => ((Stack.reading_term ..).symm.trans (Stack.read_rise i K 0)).trans ((jet_zero K i).trans h)))
variable {f K O}
include Λ
lemma sink_head (hk:Λ.kern= Radial.kernel f)(h:K 0=1): 0 < constantCoeff (rows μ K f):= by
 rw [cuts μ f K Λ hk,map_mul, underBudget Λ μ (stamp f K h), constantCoeff_C,mul_one]; exact amount_pos μ Λ
omit Λ
lemma shed (c:ℝ) (Y Z:PowerSeries ℝ)(h:0<constantCoeff Z)(h':0<c): C c * Y * (C c * Z)⁻¹=Y * Z⁻¹:= by
 let k:=C (R:=ℝ) c; have hk: 0<constantCoeff (k*Z):= by rw [map_mul, show constantCoeff k=c from constantCoeff_C ..]; positivity
 calc
    _ = (C c * Y) * (C c * Z)⁻¹ * 1:= by rw [mul_one]
    _ = (Y*Z⁻¹)*(k*Z)*(k*Z)⁻¹:= by rw [← PowerSeries.inv_mul_cancel Z h.ne']; dsimp [k]; ring
    _ = _:= by rw [mul_assoc, PowerSeries.mul_inv_cancel _ hk.ne',mul_one]
lemma shed2 {X Y P Q:FP}(c:ℝ)(hx:X=C c * P)(hy:Y=C c * Q)(hY:0<constantCoeff Q)(hc:0<c): X*Y⁻¹=P*Q⁻¹:= by rw [hx,hy]; exact shed c P Q hY hc
include Λ in
theorem receipt (hk:Λ.kern= Radial.kernel f)(hq:K 0=1)(hw:ContDiffAt ℝ ∞ K 0)(h:ContDiffAt ℝ ∞ O 0): pricetag μ K f O=enjoy Λ μ (Stack.rise O) (sink K f):= by
 unfold pricetag enjoy; rw [cuts μ f (O*K) Λ hk,cuts μ f K Λ hk]
 have hf : sink (O*K) f=sink K f * Stack.rise O:= by unfold sink; rw [Stack.rise_mul h hw]; ring
 rw [hf]; refine shed _ _ _ ?_ (amount_pos μ Λ); rw [underBudget Λ μ (stamp f K hq)]; exact zero_lt_one

lemma up (a:ℕ→ℝ)(C:ℝ) : PowerSeries.mk (C • a)= PowerSeries.C C * PowerSeries.mk a:= by ext1 n; rw [coeff_C_mul, coeff_mk, coeff_mk]; rfl
-- existence of the law with Lie-group tangent normalization

def Steep.law {f:E→ℝ}(p:Steep f): Law E where
 P:= polar f
 turns x y:= by rw [side_p,side_p,add_comm]
 slope:= by simp_rw [origin_p]; exact p.gap
 smooth:= by
    rw [show (fun x=>polar f x x)= fun x=> 2*jet f 2 x from funext (fun x=>by rw [←origin_p];ring)]; exact continuous_const.mul (Smooth.continuousJet f 2)
omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma Steep.law_eq (p:Steep f): p.law.kern=Radial.kernel f:= by funext x; unfold Radial.kernel Law.kern; rw [neg_div, show p.law.P x x/2= _ from origin_p ..]
lemma ready (p:Steep f)(h:K 0=1) : 0<constantCoeff (rows μ K f):= sink_head μ p.law p.law_eq h
end YM.FVA2.Laplace
