import YM.FVA2.Gen.Pack
import YM.Source.ODE
/-!
 # Path response: short, and smooth dependence in all REAL parameters

 Uses the Volterra resolvent as `Work.G02`. Exponents as before.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Filter Set Finset MeasureTheory Metric Asymptotics
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {E F Y :Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup Y][NormedSpace ℝ Y] {G:Gauge}
-- reuse verbatim proof of primitive from `Work.G02`, local.
/-- Bounded integration operator with base point zero. `projIcc` extends the
integrand for notation; only values in the unit interval are used. -/
private def primitive [CompleteSpace Y] : C(unitInterval, Y) →L[ℝ] C(unitInterval, Y) := by
  let π := projIcc (0 : ℝ) 1 zero_le_one
  have hint (U : C(unitInterval, Y)) (a b : ℝ) :
      IntervalIntegrable (fun s => U (π s)) volume a b :=
    (U.continuous.comp continuous_projIcc).intervalIntegrable a b
  let L : C(unitInterval, Y) →ₗ[ℝ] C(unitInterval, Y) := {
    toFun U := ⟨fun t => ∫ s in 0..(t : ℝ), U (π s),
      (intervalIntegral.continuous_primitive (hint U) 0).comp continuous_subtype_val⟩
    map_add' U W := ContinuousMap.ext fun t => intervalIntegral.integral_add
      (hint U 0 (t : ℝ)) (hint W 0 (t : ℝ))
    map_smul' r U := ContinuousMap.ext fun t => by
      change (∫ s in 0..(t : ℝ), r • U (π s)) = r • ∫ s in 0..(t : ℝ), U (π s)
      rw [intervalIntegral.integral_smul] }
  refine L.mkContinuous 1 fun U => ?_
  rw [one_mul]
  refine (ContinuousMap.norm_le (L U) (norm_nonneg U)).2 fun t => ?_
  change ‖∫ s in 0..(t : ℝ), U (π s)‖ ≤ ‖U‖
  calc
    _ ≤ ‖U‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => U.norm_coe_le_norm (π s)
    _ ≤ ‖U‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg U) t.property.2


local notation "□"=>unitInterval
variable {R:Type} [NormedRing R][NormedAlgebra ℝ R][CompleteSpace R]
local notation "P"=> C(unitInterval,R)
local notation "M"=>R
local notation "π"=> projIcc (0:ℝ) 1 zero_le_one
-- Note ***Matrix norm Frobenius***.
def skyway (R:Type)[NormedRing R][NormedAlgebra ℝ R][CompleteSpace R]: C(unitInterval,R) →L[ℝ] C(unitInterval,R) →L[ℝ] C(unitInterval,R):= ((ContinuousLinearMap.compL ℝ C(unitInterval,R) _ _) (primitive (Y:=R))).comp ( (ContinuousLinearMap.mul ℝ C(unitInterval,R)).flip )
def prong (R:Type)[NormedRing R][NormedAlgebra ℝ R][CompleteSpace R](x:C(unitInterval,R)) : C(unitInterval,R) := Ring.inverse (1 - skyway R x) (1:C(unitInterval,R))
abbrev endpoint (R:Type)[NormedRing R][NormedAlgebra ℝ R][CompleteSpace R](x:C(unitInterval,R)) := prong R x (1:unitInterval)
variable (R)
lemma staff: AnalyticAt ℝ (prong R) 0:= by
 let X:= skyway R; change AnalyticAt ℝ (fun x:P=> _) _; let t (B:P→L[ℝ] P):= Ring.inverse (1-B); have he:AnalyticAt ℝ t (X 0):= by rw [map_zero]; exact analyticAt_inverse_one_sub ℝ (P→L[ℝ] P)
 let Q:P→(P→L[ℝ] P):=fun x=>t (X x); refine (ContinuousLinearMap.analyticAt (𝕜:=ℝ) (E:=P→L[ℝ] P) (f:=ContinuousLinearMap.apply ℝ P (1:P)) (Q 0)).comp (f:=Q) ?_; exact he.comp (f:=⇑X) (ContinuousLinearMap.analyticAt (𝕜:=ℝ) (E:=P) (F:=P→L[ℝ] P) (f:=X) (0:P))
omit [NormedSpace ℝ E] in private lemma nice : ∀ᶠ t:E in 𝓝 0, ‖t‖<1:= by simpa [mem_ball_zero_iff] using (show ∀ᶠ t in 𝓝 (0:E), t∈ball 0 1 from ball_mem_nhds 0 zero_lt_one)
lemma paysG: ∀ᶠ x:P in 𝓝 0, prong R x=1+skyway R x (prong R x):= by
 let f:=skyway R; have h:Tendsto f (𝓝 0) (𝓝 0):= by simpa using f.continuous.tendsto 0
 filter_upwards [h.eventually (nice (E:=P→L[ℝ] P))] with x hx
 have ht:= isUnit_one_sub_of_norm_lt_one (R:=P→L[ℝ] P) (show ‖f x‖<1 by simpa using hx); let u:=prong R x
 change u = _; rw [ ← sub_eq_iff_eq_add, show u-f x u=(1-f x) u from rfl ]; unfold u; rw [ show (1-f x) (prong R x)=( (1-f x)*Ring.inverse (1-f x) ) (1:P) from rfl, Ring.mul_inverse_cancel (1-f x) ht ]; rfl -- sub_eq_iff_add via rw L syntax
lemma engine0: prong R 0=1:= by rw [paysG R|>.self_of_nhds,map_zero,zero_apply,add_zero]
private def adore: P→L[ℝ] P := (skyway R).flip (1:P)
theorem prong_s: HasFDerivAt (prong R) (adore R) 0:= by
    let T:= skyway R; let F:= prong R; obtain ht: AnalyticAt ℝ F 0:= staff R; -- use implicit FTC
    have hD := (hasFDerivAt_const (1:P) (0 : P)).add (T.hasFDerivAt.clm_apply ht.differentiableAt.hasFDerivAt)
    -- show differential. Adapt R02
    convert! hD.congr_of_eventuallyEq (paysG R) using 1
    unfold adore F T; rw [ engine0, map_zero ]; simp
lemma touchEnd: ContDiffAt ℝ ∞ (endpoint R) 0:= by
    let f:P→L[ℝ] M:= ContinuousMap.evalCLM ℝ (1:unitInterval); exact f.contDiff.contDiffAt.comp (0:P) ((staff R).contDiffAt.of_le le_top)
-- identify from actual parallel flow for parameter x with smooth linear-plane family. x= anchor path budget, need x→cont-map witness.
variable {R}
variable {X:Type}[TopologicalSpace X]{f:X→C(unitInterval,R)}{u:X→ C(unitInterval,R)}{Y:X→ℝ→R}{a:X}
variable (hu: ContinuousAt f a)(hx:f a=0) (h:X→ℝ→R)
-- These will be used on genuine smooth connections.
include hu
lemma at_actual {H:X×ℝ→R}(h_:Continuous H)(h0: ∀ x:X,h x 0=1)(he:∀ x:X,∀ t:ℝ,HasDerivAt (h x) (h x t*H (x,t)) t)(hh:∀ x:X,∀ i:unitInterval,f x i=H (x,i.val))(hz: f a=0): (fun x:X=> endpoint R (f x))=ᶠ[𝓝 a]fun x=> h x 1:= by
    let B x:= skyway R (f x); have hB:Tendsto B (𝓝 a) (𝓝 0):= by unfold B; have he:= ( (skyway R).continuous.continuousAt (x:= f a) ).tendsto.comp hu.tendsto; rw [hz,map_zero] at he; exact he -- using he
    let V(x:X): C(unitInterval,R):= ⟨fun t=> h x t, ( (show Differentiable ℝ (h x) from fun t=> (he x t).differentiableAt ).continuous.comp continuous_subtype_val )⟩
    have hp x: V x=1+B x (V x):= by
       ext1 t; change h x (t:ℝ)=1+ ∫ s in 0..(t:ℝ), h x (π s) * (f x) (π s)
       have ht(s:ℝ)(hs:s∈ Set.uIcc 0 (t.val)): (π s).val=s:= by rw [ Set.uIcc_of_le t.property.1 ] at hs; rw [projIcc_of_mem _ (show s∈ unitInterval from ⟨hs.1,hs.2.trans t.property.2⟩)]
       have hi : Continuous (h x):=(show Differentiable ℝ (h x) from fun t=> (he x t).differentiableAt ).continuous
       rw [intervalIntegral.integral_congr ( show Set.EqOn (fun s:ℝ=> h x (π s) * (f x) (π s)) (fun s:ℝ=> h x s* H (x,s)) _ from fun s hs=> by dsimp only; rw [hh, ht s hs]), intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=> he x s) ( Continuous.intervalIntegrable ( hi.mul ( h_.comp (continuous_const.prodMk continuous_id) ) ) ..), h0 x]; abel
    filter_upwards [hB.eventually (nice (E:=P→L[ℝ] P))] with x hx'; have hh:= isUnit_one_sub_of_norm_lt_one (R:=P→L[ℝ] P) (show ‖B x‖<1 by simpa using hx'); change prong R (f x) (1:unitInterval)=_; rw [show prong R (f x)=V x from ?_ ]; rfl
    unfold prong; let A:=1-B x; change Ring.inverse A (1:P)=_; rw [ show (1:P)=A (V x) from ?_, ← mul_apply_eq_comp, Ring.inverse_mul_cancel A hh ]; rfl
    change 1=V x-B x (V x); exact Eq.symm (sub_eq_iff_eq_add.mpr (hp x))
omit hu
variable (R) in
theorem engine_deriv (v:C(unitInterval,R)): fderiv ℝ (endpoint R) 0 v=∫ t in (0:ℝ)..1,v (π t):= by
    let F:P→L[ℝ] R:= ContinuousMap.evalCLM ℝ (1:unitInterval); change fderiv ℝ ( F ∘ prong R ) _ _=_; rw [ ( F.hasFDerivAt.comp _ ( prong_s R ) ).fderiv ]; change (∫ t in (0:ℝ)..1,(1:M)*v (π t))=_; simp
end YM.FVA2.Gen
