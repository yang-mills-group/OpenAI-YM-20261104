import YM.FVA2.Facade.Rise
import YM.FVA2.Laplace.Receipt
/-!
 # Cash the ray moments BEFORE division by either denominator

 Uses real tangential additive Haar (choice immaterial as normalized averages). For
 actual Fk symbol `μ` will be `tangent`, `K` the actual product orbit-local Haar
 function, not the inverse determinant or Haar on any additional coordinates. Gives
 the exact bare powerseries restriction, sufficient for identifying Rail
 moments in the same notation as the included engine.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic RGComparison.Core16
open PertExtension.Series Tested Radial
open scoped Classical Topology BigOperators ContDiff ENNReal

section
variable {M:Type}[NormedAddCommGroup M][NormedSpace ℝ M][FiniteDimensional ℝ M]
variable {R:Type} [CommRing R] {N:ℕ} {x y:PowerSeries R}
lemma back_pay (h:Through N x y) : Through N (-x) (-y):= by intro i hi; rw [map_neg,map_neg,h i hi]
lemma sumThrough {ι:Type} (s:Finset ι)(f g:ι→PowerSeries R) (h:∀x∈s,Through N (f x) (g x)): Through N (∑i∈s,f i) (∑i∈s,g i):= by intro i hi; rw [map_sum,map_sum]; exact Finset.sum_congr rfl fun j hj=> h j hj i hi
lemma costThrough {p q:PowerSeries ℝ}(h:Through N p q){f:M→ℝ}(hg:Stationary f)(x): Through N (Stack.read x (pay p f)) (Stack.read x (pay q f)):= by rw [rayPrice f hg, rayPrice f hg]; apply Through.add (back_pay (h.mul (Through.refl _))); have hh : term p 0=term q 0:= h 0 (by omega); rw [hh]; exact Through.refl _
lemma enough_c (Y:ℝ→+* R)(h:Through N x y): Through N (Formal.expander Y x) (Formal.expander Y y):= by intro i hi; rw [Formal.expander,Formal.expander,coeff_mk,coeff_mk]; exact sumThrough _ _ _ (fun k _=> Through.mul (Through.refl _) (Through.pow h k)) i hi
end
section
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] [NormedAddCommGroup F][NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {ι:Type}[Fintype ι] (g:ι→E×F→ℝ)(w:ι→ℝ→ℝ)(y:F)
variable (hp:∀ i,Stationary (g i)) (hg:∀ i,ContDiffAt ℝ ω (g i) 0) (hw:∀ i,ContDiffAt ℝ ω (w i) 0)
variable (p:ι→PowerSeries ℝ)(N:ℕ)(h:∀i, Through N (amount (w i)) (p i))
 def coat (K:E→ℝ) (V:E×F→ ℝ): ℝ×E→ ℝ:= (K ∘ (LinearMap.snd ℝ ℝ E))* (V ∘ flank y)
 def layerFee (K:E→ℝ) : Ticket (E × F):= (∏ i,chip (p i) (g i)) * boost (LinearMap.fst ℝ E F) (Stack.rise K)

include hp hg hw h
variable (K:E→ℝ) (hk:ContDiffAt ℝ ∞ K 0)
variable (V:E× F→ℝ)(hv:ContDiffAt ℝ ∞ V 0)
include hk hv
local notation "L"=> ((layerFee g p K)* Stack.rise V)
local notation "f"=> Facade.raise g w y
local notation "T"=> Laplace.sink (coat y K V) f
omit [MeasurableSpace E] [BorelSpace E] in
lemma tracing (d:E) : Through N (Stack.read ((1:ℝ),d) T) (Stack.read (d,y) L):= by
 let a:= LinearMap.snd ℝ ℝ E; let b := flank (E:=E) y
 have hi:Stack.read ((1:ℝ),d) (Stack.rise (coat y K V))= Stack.read (d,y) ((boost (LinearMap.fst ..) (Stack.rise K))*Stack.rise V):= by
       unfold coat; rw [rise_mul _ _,map_mul,map_mul,←Vault.climbing (a) hk,←Vault.climbing (b) hv]; rotate_left;
       · exact (show ContDiffAt ℝ ∞ K (a 0) from by rw [map_zero]; exact hk).comp _ (LinearMap.toContinuousLinearMap a).contDiff.contDiffAt
       · exact (show ContDiffAt ℝ ∞ V (b 0) from by rw [map_zero]; exact hv).comp _ (LinearMap.toContinuousLinearMap b).contDiff.contDiffAt
       simp_rw [caught]; unfold b; rw [flank_one]; rfl
 unfold Laplace.sink layerFee; rw [mul_assoc (∏ i,chip (p i) (g i)), map_mul (Stack.read ((1:ℝ), d)), _root_.map_mul (Stack.read (d,y)), hi]
 apply Through.mul _ (Through.refl _); simp_rw [OpenSlots.chip]; rw [← compose_many _ (fun i=> pay (p i) (g i)) (fun i=>stipend (p i) (g i) (hp i)), Warp.exponent, Warp.exponent, concentrated g w y d hp hg hw]; apply enough_c; rw [map_sum,map_sum]; exact sumThrough _ _ _ fun i _=> costThrough (h i) (hp i) _

variable (a:Quadratic (E × F)) (q:(core a).RespectsPrice) (ha: a.P=(totalPrice (fun i=> Quadratic.genesis (p i) (g i))).P)
variable (μ:Measure E)[μ.IsAddHaarMeasure]
 def craving := Real.exp (-(1+(reduced a q).flourish y /2)) * ∫ x:E,q.inner.kern x ∂μ
omit hk hv hp hg hw h [FiniteDimensional ℝ F] in
lemma craving_pos : 0<craving y a q μ:= mul_pos (Real.exp_pos _) (Splice.positive ..)
include ha
lemma reading_stamp : Through N
    (PowerSeries.mk (Therm.stamp μ (coat y K V) f 1))
    (PowerSeries.C (craving y a q μ) * Stack.read y (uptake a μ q L)):= by
 intro i hi; rw [coeff_mk,Therm.stamp_moment, coeff_C_mul,uptime];
 let k:= coat y K V; let Q:= q.inner; let z(u):= coeff i (Stack.read (u+skew a q y,y) L); let v:= Real.exp (-(1+(reduced a q).flourish y/2)); let D:= normTerm k f i; let W:= ∫ x:E, Q.kern x ∂μ
 have hx x: D (1,x+skew a q y)= z x * Q.kern x * v:= by
       let d:= x+skew a q y; change integrandSeries f k i (1,d)* Real.exp (-(jet f 2 (1,d)))=_
       rw [←Laplace.deck, ←reading_term, tracing g w y hp hg hw p N h K hk V hv d i hi, initialQ g w y d hp hg hw p N h, flank_one]
       let P:= totalPrice (fun i=> Quadratic.genesis (p i) (g i)); rw [show P.flourish (d,y)= Q.P x x+ (reduced a q).flourish y from (congr_arg (fun (u:(E×F)→ₗ[ℝ] Module.Dual ℝ (E×F))=> u (d,y) (d,y)) ha.symm).trans ((ordinary_square a q x y).trans (by unfold Q; rw [decided]; rfl)), mul_assoc (z x)]; unfold v Law.kern; rw [←Real.exp_add]; congr 2 ; ring
 have hP:0<W:= positive _ _
 rw [← integral_add_right_eq_self (μ:=μ) (fun x:E=>D (1,x)) (skew a q y)]
 change (∫ x:E,D (1,x+_) ∂μ)= (v*W)* Q.average μ z; simp_rw [hx,integral_mul_const]; unfold Law.average; change _=(v*W)* (_/W); field_simp; simp only [Pi.mul_apply]; ring
end
end YM.FVA2.Facade
