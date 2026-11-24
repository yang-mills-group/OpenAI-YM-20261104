import YM.QuadraticLocal.Aperture.Lap
import YM.AllOrder.Catch.Tune
/-!
 Quantitative perturb λ vs Taylor receipt. Measure x pushes selected moments *whole* including
 exact conditioned denominator/context. Uniform over every y tested only after orientation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture.Sage
open Function MeasureTheory Filter Finset Lattice Wilson RG Marker
open scoped Topology ENNReal ContDiff BigOperators Classical
open AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP Response PertExtension PertExtension.Series Radial
open Sunrise Focus Comparison.Cumulants Extra.Trajectories Toggle Drawer
open Multi Comparison.RG02 Comparison.RG02.Order Primitives.GCC PositionX.Gauss
open AllOrder.Catch AllOrder.Catch.Clock ConnectedActivityE6 Blaze Brush PositionX.Jet
variable {X V:Type} [Fintype V][DecidableEq V]
variable [MeasurableSpace X] (W:X→ℝ) (μ:Measure X) [IsFiniteMeasure μ] (ρ:V→X→ℝ)
variable (hW:RG.Envelope W) (hM:0≤W) (hZ:0<∫ i,W i ∂μ)(hρ:∀ i,RG.Envelope (ρ i))
local notation "Z"=> Sage.moment W μ
local notation "P"=> (Knife V × X)
variable {k n:ℕ}
local notation "Region"=> entry_d X
local notation "φ"=> ratioN W μ ρ
local notation "ℱ"=> member ρ
local notation "Fr"=> Sunrise.Focus.census V
-- single t.N.Bit.
section coupon
variable (v:V→ℝ) (b a C:ℝ) (j:ℕ)
include hW
lemma space_sum {I:Type} (s:Finset I) (f:I→X→ℝ)(h:∀ i,Envelope (f i)): Z (fun y=>∑ i∈s,f i y)= ∑ i∈s,Z (f i):= by
 induction s using Finset.induction_on with
 | empty=> simp [Sage.moment]
 | insert i s hi ih=>
    let L(y:X):= ∑ i∈s,f i y; have hx:L=∑ i∈s,f i:=funext fun y=> (Finset.sum_apply y s f).symm
    simp_rw [Finset.sum_insert hi]; let x(j)(hj:j∈s):= h j; have ht :Envelope L:= Envelope.sum s f h -- fix using induction hs or h
    exact (price_sum W μ hW (h i) ht).trans (congr_arg (_ + ·) ih)
omit hW in
lemma actual_T (n:ℕ) : ∃ C>0, ∀ x r:ℝ, 0<r → r≤1 →  ‖x‖ ≤ r →  ‖Real.exp x-∑ i∈ Finset.range (n+1), x^i*(i.factorial:ℝ)⁻¹‖ ≤ C*r^(n+1):= by
 obtain ⟨c,h,hc⟩:= Brush.compact (k:=n+1) (s:=Metric.closedBall (0:ℝ) 1) (isCompact_closedBall ..) fun x _=> Real.contDiff_exp.contDiffAt
 refine ⟨c,h,fun x r hr he hx=>?_⟩; have hh:= AllOrder.Local.Taylor.forecast hr he (Nat.le_refl (n+1)) (fun y hy=> hc y (mem_closedBall_zero_iff.mpr (hy.trans he))) hx
 have hv(i:ℕ):iteratedDeriv i Real.exp 0=1:=by simpa using congr_fun (iteratedDeriv_exp_const_mul i (1:ℝ)) (0:ℝ)
 change ‖_ - _‖ ≤ _; have ht:= hh.bound; change ‖Real.exp x-Work.G05.blockTaylor n Real.exp x‖ ≤_ at ht; rw [← Catch.owns] at ht; simp only [delay,someJ,smul_eq_mul,hv,mul_one] at ht; exact ht
variable (h : ∀ (i:X), W i≠0 → ‖Sage.member ρ (v,i)‖≤ a)
abbrev nap (v:V→ℝ)(t:ℝ):ℝ:=Sage.moment W μ (fun y=> Real.exp (t * Sage.member ρ (v,y)))
local notation "Y"=> Sage.nap W μ ρ
local notation "H"=> Fintype.card V
include h hM hZ
lemma sunny_guess (ha:0 ≤ a): |ratioN W μ ρ j v|≤ a^j:=by
 unfold ratioN; refine banking W μ hW hM hZ _ _ fun i hi=>?_ ; rw [norm_mul,norm_pow, norm_inv,Real.norm_of_nonneg (by positivity : 0≤(j.factorial:ℝ))]; exact (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) ((inv_le_one₀ (by positivity)).2 (mod_cast Nat.factorial_pos j))).trans (pow_le_pow_left₀ (norm_nonneg _) (h i hi) _)
local notation "Tt"=> Sage.member ρ
include hρ
lemma evening (hb:0<b)(ha:0<a)(he:b*a≤1)(hC: ∀ x r:ℝ,0<r → r≤1 →  ‖x‖ ≤ r →  ‖Real.exp x-∑ i∈range (j+1), x^i*(i.factorial:ℝ)⁻¹‖ ≤ C*r^(j+1)):
   |Y v b - delay (fun i=> φ i v) j b| ≤ C*(b*a)^(j+1) := by
 let s:= range (j+1); let f i x:=(b*Tt (v,x))^i*(i.factorial:ℝ)⁻¹; let g(y:X):=∑ i∈s,f i y; let R x:=Real.exp (b*Tt (v,x)); let t(i:ℕ):=(desk_mark ρ i); have hp i:Envelope (f i):=by
    have he:= School.knows (school_ratio ρ hρ i) v; rw [show f i=b^i • (fun x=> t i (v,x)) from ?_]; · exact (Region).scales he (b^i)
    funext x; change _=(b^i*((i.factorial:ℝ)⁻¹*member ρ (v,x)^i)); unfold f; rw [mul_pow]; ring
 have hG:Envelope g:= Envelope.sum s f hp; have hx:Envelope R:= ((Region).scales (School.knows (school_point ρ hρ) v) b|>.exp) -- edit
 let E:= Z; have hr : Z g=delay (fun i=> φ i v) j b:= by
   unfold g delay; rw [space_sum W μ hW s f hp]; apply sum_congr rfl; intro i _; unfold ratioN; rw [show f i=b^i • (fun x=> t i (v,x)) from ?_,Sage.price_scale]; · rfl
   funext y; change _=(b^i*((i.factorial:ℝ)⁻¹*member ρ (v,y)^i)); unfold f; rw [mul_pow]; ring
 have he' : Z (R-g)= Y v b -delay (fun i=>φ i v) j b:=by rw [show R-g= R + (-1:ℝ) • g by rw [neg_one_smul, sub_eq_add_neg],Sage.price_sum W μ hW hx (show Envelope ((-1:ℝ) • g) from (entry_d X).scales hG _), price_scale,hr]; change (Y v b) + _= _; ring
 rw [← he']; refine banking W μ hW hM hZ _ _ (fun i hi=> hC (b*Sage.member ρ (v,i)) _ (mul_pos hb ha) he ?_); rw [norm_mul,Real.norm_of_nonneg hb.le]; exact mul_le_mul_of_nonneg_left (h _ hi) hb.le
end coupon
end YM.QuadraticLocal.Aperture.Sage
