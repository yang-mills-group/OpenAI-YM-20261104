import YM.OPE.Compatible.Straws.Gown
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass
section pol
variable (μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
lemma levelProp (f g:E→ℝ)(h:Bond f)(hp:Bond g)(hz:∀ q:E→ℝ,Bond q→ L.average μ (f*q)=L.average μ (g*q)): f=g:=by
     apply sub_eq_zero.mp; let v:=f-g; have ht:Bond v:=h.sub hp; have hx:L.average μ (v*v)=0:=by rw [show v*v=f*v-g*v by unfold v; ring, curb _ _ _ _ (h.mul ht) (hp.mul ht),hz v ht]; simp
     let w:=v*v*L.kern; have hh: ∫ x,w x ∂μ=0:=by
          have hi := L.empty μ; unfold Law.average at hi hx; apply Or.resolve_right (show _ from div_eq_zero_iff.mp hx); intro he; rw [he,div_zero] at hi; norm_num at hi
     have he: w=0 := Measure.eq_of_ae_eq ((integral_eq_zero_iff_of_nonneg (f:=w) (μ:=μ) (fun i=> mul_nonneg (mul_self_nonneg (v i)) (Real.exp_pos _).le) (lumpZ μ L _ (ht.mul ht))).mp hh) ((ht.mul ht).smooth.continuous.mul L.continuous_kern) continuous_zero
     funext i; have hs:=congr_fun he i; change v i*v i*L.kern i=0 at hs; rw [mul_eq_zero] at hs; exact or_self_iff.mp (mul_eq_zero.mp (hs.resolve_right (Real.exp_pos ..).ne'))
lemma levelJet (p q:E→Token)(hp:ScriptJ.B p)(hq:ScriptJ.B q)(hz:∀ r:E→ℝ,Bond r→ draw (low r*p) L μ=draw (low r*q) L μ): p=q:=by
     obtain ⟨h1,h2,h3⟩:= bondX hp;obtain ⟨h4,h5,h6⟩:= bondX hq; funext i; apply JetS.eta
     · apply congr_fun (levelProp μ L _ _ h1 h4 fun s hs=>?_) i; rw [mul_comm _ s,mul_comm _ s]; exact congr_arg JetS.s (hz s hs)
     · apply congr_fun (levelProp μ L _ _ h2 h5 fun s hs=>?_) i; rw [mul_comm _ s,mul_comm _ s]; have hv:= congr_arg JetS.l (hz s hs); simpa only [draw,Pi.mul_apply,ml_l,low,zero_mul,add_zero] using! hv
     apply congr_fun (levelProp μ L _ _ h3 h6 fun s hs=>?_) i; rw [mul_comm _ s,mul_comm _ s]; have hv:=congr_arg JetS.h (hz s hs); simpa only [draw,Pi.mul_apply,ml_h,low,zero_mul,add_zero] using! hv
end pol
variable {F:Fiber E G I}{X:Path E G D}{p:Keys G D→ℝ}(Z:F.SeriesUp X p) {P:ChartRatio G}(R:LocalRatio P)
namespace SeriesUp
local notation "ν0"=> camp F X
local notation "μ0"=> cloth F P
local notation "VΩ"=> Chart.tangent G D
local notation "ωμ"=> Chart.tangent G I
local notation "JΘ" => crossT ωμ F.Q
local notation "mΘ"=> (Z.C.hat P)
omit [BorelSpace E] in
lemma roast (u: ScriptJ K!)(hp:u.B): draw u (penon Z.C) (Chart.tangent G (D⊕I))=draw (JΘ (u ∘ ν0)) Z.Z VΩ:=by
       let μ:=VΩ; let Q:=F.Q; let v:=camp F X; let w:=u ∘ v; have ht(x:U!×Y!): (penon Z.C).P (v x) (v x)= (united Z.Z Q).P x x:=by have hz:= Z.hX x.1 x.2; rw [show (x.1,x.2)=x from Prod.eta x,penon_shape] at hz;rw [united_shape]; change (penon Z.C).P (ν0 x) (ν0 x)= _; linarith only [hz]
       haveI:(μ.prod ωμ).IsAddHaarMeasure:= twoHaar (E:=U!) (F:=Y!) _ _
       have hh:ScriptJ.B w:= fun i=>(hp i).compLinear v.toLinearMap; rw [ease u hp v.symm.toLinearEquiv _ (united Z.Z Q) (fun x=> by convert ht (v.symm x) using 1 <;> simp) _ (μ.prod ωμ)]; exact guest ωμ Q μ Z.Z w hh
-- test Pay ν probes
include R
abbrev dessert (Z': F.SeriesUp X p)(P:ChartRatio G)(q:ScriptJ K!): ScriptJ (Keys G D):= crossT (Chart.tangent G I) F.Q ((q* Z'.C.hat P) ∘ camp F X)
omit [BorelSpace E] in
lemma mintExt (q:ScriptJ K!)(hp:q.B): ScriptJ.B (Z.dessert P q):= crossB _ _ _ fun i=>(ScriptJ.height hp (Z.C.hat_toll R) i).compLinear (camp F X).toLinearMap
abbrev seedOne (Z:F.SeriesUp X p)(P:ChartRatio G) :Token:= draw (dessert Z P 1) Z.Z (Chart.tangent G D)
omit [BorelSpace E] in
lemma seedBase :(seedOne Z P).s=1:= by unfold seedOne dessert;rw [one_mul]; exact headD VΩ Z.Z _ fun i=> headD ωμ F.Q _ fun y=> Z.C.hat_full R _
abbrev netJet (Z:F.SeriesUp X p)(P:ChartRatio G)(q:ScriptJ K!):U!→Token:= fun i=>(seedOne Z P)⁻¹ * (dessert Z P q i)
omit [BorelSpace E] in
lemma nett (q:ScriptJ K!)(hp:q.B): ScriptJ.B (Z.netJet P q):= ScriptJ.height (p:=fun _=> (seedOne Z P)⁻¹) (s:=_) (Bfray _) (mintExt Z R q hp)
omit [BorelSpace E] in
lemma rateN (q:ScriptJ K!)(hq:q.B)(g: ScriptJ U!)(hg:g.B):
     Z.C.pay P ((g ∘ BL)*q)= draw (g*Z.netJet P q) Z.Z VΩ:=by
           let S:= (g ∘ BL); let T:= Z.dessert P q; let U:= seedOne Z P; have hs: ScriptJ.B S:=fun i=> (hg i).compLinear (BL).toLinearMap; have hp:= height hq (Z.C.hat_toll R)
           rw [Z.C.cutOut R (penon _) _ (penon_shape _),mul_assoc S q mΘ,roast Z _ (height hs hp),roast Z mΘ (Z.C.hat_toll R)] -- S defeq rw
           have hy: JΘ ((S*(q* mΘ)) ∘ ν0)=g*T:=by
                funext i; let p':=(q* mΘ) ∘ ν0; let sw (j:Y!):=p' (i,j); have hv: ScriptJ.B sw:=fun k=> Shift.leanB _ ((hp k).compLinear (camp F X).toLinearMap) _; change draw (fun y=> (S*_) _) _ _=_
                rw [show (fun y:Y!=> (S*(q* mΘ)) ((ν0) (i,y)))= fun y=> g i*sw y from funext fun j=> by change g (BL _) *_=_;rw [ (rig F X (i,j)).1];rfl]; exact drips ωμ F.Q sw _ hv
           rw [hy,show draw (JΘ (mΘ ∘ ν0)) Z.Z VΩ=U from (by unfold U seedOne dessert;rw [one_mul]),dv,mul_comm]; rw [← drips VΩ Z.Z _ _ (ScriptJ.height hg (mintExt Z R q hq))]; exact congr_arg (fun p=> draw p Z.Z _) (funext fun i=>mul_left_comm ..)
end SeriesUp
end Fiber
end YM.OPE.Libra
