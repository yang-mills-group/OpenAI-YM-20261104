import YM.RegulatorIR.Laplace.Compact
import YM.PertExtension.Normalized

/-! Compact-group marginals with gauge pins. Sard: measure local formula
with exponent containing possible arbitrary analytic t variations. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Laplace
open Lattice PertExtension Series Series.Radial MeasureTheory Filter Function Set Metric Geometry
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical
variable {G : Gauge} (E I:Type)[Fintype E][Fintype I]

abbrev RoomK (G: Gauge) (X : Type) := X→ G.El
abbrev Meadow (G : Gauge)(X : Type) := X→ G.Color
abbrev Hook (G: Gauge)(E I:Type):= ℝ → RoomK G I → RoomK G E → ℝ

variable {E I}
-- StationaryInputs deliberately separate graph/gauge premise from finite supp.

def priceMap (F:Hook G E I): (Meadow G E) × ℝ × Meadow G I → ℝ:=fun z=>F z.2.1 (Chart.expLinks G _ z.2.2) (Chart.expLinks G _ z.1)
def aura (A:Hook G E I): (Meadow G E) × ℝ × Meadow G I → ℝ:= fun z=> priceMap A z*Chart.jacobian (Orb.tray G) z.1
lemma expMeadow (E:Type)[Fintype E]: Continuous (Chart.expLinks G E) := continuous_pi (fun i=> G.lieExp_cont.comp (continuous_apply i))
lemma expOrigin (E:Type)[Fintype E]:Chart.expLinks G E 0=1:=funext (fun _=> G.mat_lieExp_zero)

-- evaluate without Haar prefactor. Need readability later as patch fees.
structure Bundle (F A:Hook G E I) : Prop where
 burden : Measurable (fun p:ℝ × RoomK G I × RoomK G E=> F p.1 p.2.1 p.2.2)
 nonneg : ∀ t u v, 0 ≤ F t u v
 cased : Continuous (fun p:ℝ × RoomK G I × RoomK G E=> A p.1 p.2.1 p.2.2)
 entry : Readies (priceMap F) (aura A)
 -- for parameter evaluation localization enough: last T-flat if chained
 isolated : ∀ x: ℕ→ℝ,∀ y:ℕ→RoomK G I, ∀ z:ℕ→RoomK G E, ∀ v, Tendsto x atTop (𝓝 0) → Tendsto y atTop (𝓝 1) → Tendsto z atTop (𝓝 v)→ Tendsto (fun i=>F (x i) (y i) (z i)) atTop (𝓝 0)→ v=1

def dim (G:Gauge) (E:Type)[Fintype E] := Module.finrank ℝ (Meadow G E)
def tilt (F A:Hook G E I) (t:ℝ)(u:RoomK G I)(v:RoomK G E): ℝ:= A t u v*Real.exp (-F t u v/t^2)
def scan (F A:Hook G E I) : ℝ → RoomK G I → ℝ:=fun t u=> ∫ v,tilt F A t u v ∂Chart.physical G E
-- coefficients not yet normalized

def normalized (F A : Hook G E I) (t:ℝ)(x:Meadow G I):ℝ:= (t^dim G E)⁻¹*scan F A t (Chart.expLinks G _ (t • x))
def tomorrow (F A:Hook G E I)(x:Meadow G I) (e:ℕ):ℝ:= rates (Chart.tangent G E) (aura A) (priceMap F) e (1,x)
def Rated (G:Gauge)(I : Type)[Fintype I] (f:ℝ→Meadow G I→ℝ) (w:Meadow G I→ℕ→ℝ) : Prop:= ∀ D:ℝ,0 ≤ D → ∀ n : ℕ,∃ C:ℝ,0 ≤ C ∧ ∀ᶠ t in 𝓝[>] 0,∀ x, ‖x‖≤D → ‖f t x-Tested.peval (w x) n t‖≤ C*t^(n+1)

namespace Bundle
variable {F A:Hook G E I} (H: Bundle F A)
include H
omit H in
lemma m_F (H₀:Hook G E I) (h:Measurable (fun p:ℝ × RoomK G I × RoomK G E=> H₀ p.1 p.2.1 p.2.2)): Measurable (priceMap H₀):= by
 let f:= fun p:ℝ × RoomK G I × RoomK G E=> H₀ p.1 p.2.1 p.2.2
 -- define p^{-1} chart
 let h' (x:Meadow G E × ℝ × Meadow G I):ℝ × RoomK G I × RoomK G E := (x.2.1,Chart.expLinks G _ x.2.2,Chart.expLinks G _ x.1)
 have he : Measurable h':= Measurable.prodMk (measurable_fst.comp measurable_snd) (Measurable.prodMk ((Chart.expLinks_meas).comp (measurable_snd.comp measurable_snd)) ((Chart.expLinks_meas).comp measurable_fst))
 exact (h.comp he)
lemma m_K : Measurable (aura A) := ((m_F A H.cased.measurable).mul ((Chart.Ratio.jacobian_meas (Orb.traySpec G)).comp measurable_fst))
lemma m_tilt (t:ℝ)(u) : Measurable (tilt F A t u):=by
 let g (v:RoomK G E):=(t,u,v)
 have h : Measurable g:= measurable_const.prodMk (measurable_const.prodMk measurable_id)
 exact Measurable.mul (H.cased.measurable.comp h) (Real.measurable_exp.comp ((((H.burden.comp h).neg).div_const _)))
lemma major (t:ℝ) : ∃ C : ℝ,∀ u v, ‖tilt F A t u v‖ ≤ C:=by
 have hx:Continuous (fun u:RoomK G I × RoomK G E=> A t u.1 u.2):= H.cased.comp (continuous_const.prodMk continuous_id)
 obtain ⟨C,hU⟩:= isCompact_univ.exists_bound_of_continuousOn hx.continuousOn
 refine ⟨C,fun u v=>?_⟩
 have hp:Real.exp (-F t u v/t^2)≤1:=Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (H.nonneg ..)) (sq_nonneg _))
 unfold tilt; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) hp); exact hU (u,v) (mem_univ _)
lemma reading (t:ℝ)(u:RoomK G I): Integrable (tilt F A t u) (Chart.physical G E):=by obtain ⟨c,hc⟩:= H.major t; exact Integrable.of_bound (H.m_tilt t u).aestronglyMeasurable c (Eventually.of_forall fun x=> hc u x)

lemma transforms (t:ℝ)(ht:0<t)(x:Meadow G I){r:ℝ}(hr:0<r)(hx:r < Chart.small G (Orb.tray G)) : let u:=Chart.expLinks G I (t • x); (t^dim G E)⁻¹ * (∫ y in Chart.chamber G E r, tilt F A t u y ∂Chart.physical G E)= segment (Chart.tangent G E) (aura A) (priceMap F) t r (1,x):=by
 intro u; let g:= fun y:Meadow G E=> Chart.jacobian (Orb.tray G) y * tilt F A t u (Chart.expLinks G E y)
 let P:=ball (0:Meadow G E) r; let N:= Chart.tangent G E
 let R:=disc (E:= Meadow G E) t r; let f:= fun y:Meadow G E=>projection (aura A) (priceMap F) t (y,1,x)
 have hf y : f y= g (t • y):=by
    unfold f; rw [projection_eq]; unfold g aura tilt; change _* (Real.exp (-F (t*1) _ _/t^2))= _; simp only [priceMap,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_one];dsimp only [u]; ring
 have hg x: P.indicator g (t • x)= R.indicator f x:=by
   by_cases h:x∈ R
   · rw [indicator_of_mem (s:=R) h, indicator_of_mem (s:=P) (show _∈P from h),hf]
   rw [indicator_of_notMem (s:=R) h,indicator_of_notMem (s:=P) (show t • x ∉ P from h)]
 rw [Chart.Ratio.chamber_integral (Orb.traySpec G) _ (H.m_tilt t u) hx hr];change _ * (∫ y in P,g y ∂N) = ∫ y in R, f y ∂N
 have ht':=Measure.integral_comp_smul_of_nonneg (Chart.tangent G E) (P.indicator g) t (hR:=ht.le)
 simp_rw [hg] at ht'; rw [integral_indicator (show MeasurableSet R from disc_meas ..),integral_indicator (show MeasurableSet P from isOpen_ball.measurableSet)] at ht'; exact ht'.symm
end Bundle
end YM.RegulatorIR.Laplace
