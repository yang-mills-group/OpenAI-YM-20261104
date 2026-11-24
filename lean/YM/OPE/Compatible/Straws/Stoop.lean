import YM.OPE.Compatible.Straws.Tabu
/-!
# Jet calculus along small paths of coarse parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
open Radial ScriptJ JetS
namespace Stranded
open Flock
variable [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
private lemma remit (a:E)(f:E→ℝ)(hp:Bond f): L.average μ (⇑(L.P a)*f)= L.average μ (pointD a f):=by
      apply bask μ L a f _ hp (hp.amount a); intro x y; let t(z:ℝ):= x+z • a; have hx:HasDerivAt t a y:=by simpa only [one_smul] using! HasDerivAt.const_add x ( (hasDerivAt_id' y).smul_const a)
      exact (hp.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt y hx
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in
private lemma debit (f:E→ℝ): L.average μ (-f)= - L.average μ f:=by simp only [show -f=(-1:ℝ) • f from (neg_one_smul ℝ f).symm,scooted μ L,neg_mul,one_mul]
lemma curb (x y:E→ℝ)(hx:Bond x)(hy:Bond y): L.average μ (x-y)=L.average μ x-L.average μ y:=by rw [sub_eq_add_neg, sun μ L hx hy.neg, debit]; ring
lemma Recuperate (a b:E)(x:E→ℝ)(hp:Bond x):
      draw (Warp L a b * nestE a b x) L μ= plainJ (L.average μ x):=by
      let V:= Warp L a b; let s:=V*nestE a b x; let I:= L.average μ; let D(w:E):=pointD w x; let f(w:E):E→ℝ:=L.P w; let c:= L.P a a; let v:=pointD a (D a); have hv:Bond v:=(hp.amount a).amount a; have hF(w:E):Bond (f w):= Bond.glyph _; have hx(w):Bond (D w):= hp.amount w; have hx'(w i):L.P i w=f w i:= L.turns ..; have h(w:E):I (f w*x)=I (D w):=remit μ L w x hp
      apply JetS.eta
      · simp only [draw,Pi.mul_apply,ml_s,plain_s];simp [nestE]
      · change I (fun i=>(s i).l)=0; rw [show (fun i:E=> _)= f a*x-D a from funext (fun i=>by unfold s; simp only [Pi.mul_apply,ml_l,V,Warp,nestE,Reads.pluck,hx',Pi.sub_apply,D]; ring),show I _= _ from curb μ L _ _ ((hF a).mul hp) (hx a)]; exact sub_eq_zero.mpr (h a)
      change I (fun i=>(s i).h)=0
      let Q:=f b*x-D b; let P':= f a*x
      let T':= (f a*P')-c • x+v; rw [show (fun i:E=>_)= Q+(2:ℝ)⁻¹ • T'-f a*D a from funext (fun i=>by unfold s; simp only [Pi.mul_apply,ml_h,V,Warp,Reads.pluck,nestE,c,Q,P',T',Pi.sub_apply,Pi.add_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,v,D,hx']; ring)] -- hx' repeated loops?
      have ht:Bond Q:= ((hF b).mul hp).sub (hx b); have hq:Bond (f a*P'):= (hF a).mul ((hF a).mul hp); have hh:Bond T':= (hq.sub (Bond.scale _ hp)).add hv; have hi:I Q=0:=by unfold I Q; rw [curb μ L _ _ ((hF b).mul hp) (hx b)]; exact sub_eq_zero.mpr (h b)
      have hr : I (f a*D a)= I v:= remit μ L a _ (hx a)
      have hs: I (f a*P')= I (f a *D a)+c*I x:=by
          rw [show I (f a*P')= _ from remit μ L a _ ((hF a).mul hp)];unfold P'; rw [pointM _ _ _ (hF a) hp,show pointD a (f a)=_ from pointC a (L.P a),show x * (fun _=>L.P a a)= c • x from funext fun i=> mul_comm ..,show L.average μ _=_ from sun μ L ((hF a).mul (hx a)) (Bond.scale c hp),scooted]
      have he:I T'=2* I v:=by unfold I T'; rw [sun μ L (hq.sub (hp.scale _)) hv, curb μ L _ _ hq (hp.scale _),scooted]; change I _- c*I x+I v=2*I v; rw [hs,hr];ring
      unfold I; rw [curb μ L _ _ (ht.add (hh.scale _)) ((hF a).mul (hx a)),sun μ L ht (hh.scale _),scooted]; change I Q+ _*I T'-I _=_; rw [hi,he,hr];ring
end Stranded
end YM.OPE.Libra
