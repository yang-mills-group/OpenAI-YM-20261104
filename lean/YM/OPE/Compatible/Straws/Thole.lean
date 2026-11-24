import YM.OPE.Compatible.Straws.Rift
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
variable [FiniteDimensional ℝ E]
def pointD (a:E)(p:E→ℝ)(x:E):=fderiv ℝ p x a
lemma pointS (a:E)(p q:E→ℝ)(h:Bond p)(hp:Bond q): pointD a (p+q)=pointD a p+pointD a q:=by funext i; rw [pointD,fderiv_add (h.smooth.differentiable (by simp)|>.differentiableAt) (hp.smooth.differentiable (by simp)|>.differentiableAt)]; rfl
lemma pointM (a:E)(p q:E→ℝ)(h:Bond p)(hp:Bond q): pointD a (p*q)= p*pointD a q+ q*pointD a p:=by funext i; rw [pointD,fderiv_mul (h.smooth.differentiable (by simp)|>.differentiableAt) (hp.smooth.differentiable (by simp)|>.differentiableAt)]; rfl
lemma pointC (a:E)(c: Dual ℝ E): pointD a c= fun _=>c a:=by let U:= toContinuousLinearMap c; change pointD a U=_; unfold pointD; funext i; rw [U.fderiv];rfl
omit [FiniteDimensional ℝ E] in
lemma pointT (a:E)(c:ℝ): pointD a (fun _=>c)=0:=by unfold pointD; funext i;simp
def nestE (a b:E)(f:E→ℝ)(x:E):Token:=⟨f x,-pointD a f x,-pointD b f x+pointD a (pointD a f) x/2⟩
lemma nestE_B (a b:E)(p:E→ℝ)(hp:Bond p): ScriptJ.B (nestE a b p):=by
     let s:=fun x:E=> pointD a (pointD a p) x/2; have hh: Bond s:=by rw [show s=(2:ℝ)⁻¹ • pointD a (pointD a p) from funext fun i=>by dsimp only [s]; simp only [Pi.smul_apply,smul_eq_mul];ring]; exact Bond.scale _ ((hp.amount a).amount a)
     exact Xbond hp (hp.amount a).neg ((hp.amount b).neg.add hh)
lemma nestHop (x a b:E)(f:E→ℝ)(hp:Bond f)(δ:ℝ→ E)(hx:Reads δ ⟨0,a,b⟩): Reads (fun t=> f (x-δ t)) (nestE a b f x):=by
     induction hp with
     | keep c=> rw [show nestE a b (fun _=>c) x= ⟨c,0,0⟩ from by simp only [nestE,pointT a,pointT b,Pi.zero_apply]; simp [pointD]]; exact Reads.constants _
     | glyph c=>
         simp only [nestE,pointC,pointT,Pi.zero_apply]; have hp:= ((Reads.constants x).minus hx).tours (LinearMap.toContinuousLinearMap c); convert hp using 1; rfl; apply JetS.eta; · change c _=c (x+- (0:E)); simp
         · change _=c (0+ -a); simp
         change _=c (0+ -b);simp
     | @add p q h1 h2 v u=>
        convert v.sum u using 1; rfl; apply JetS.eta <;>simp only [nestE,pointS _ p q h1 h2,pointS a (pointD a p) (pointD a q) (h1.amount a) (h2.amount a),Pi.add_apply,pl_s,pl_l,pl_h] <;> ring
     | @mul p q h1 h2 v u=>
        have hb:Bond (pointD a p):= h1.amount a; have he:Bond (pointD a q):= h2.amount a; convert v.pile u using 1; rfl; apply JetS.eta <;>simp only [nestE,pointM _ p q h1 h2,pointS a (p * pointD a q) (q * pointD a p) (h1.mul he) (h2.mul hb),pointM a p (pointD a q) h1 he,pointM a q (pointD a p) h2 hb, Pi.add_apply,Pi.mul_apply,ml_s,ml_l,ml_h] <;> ring
end Stranded
end YM.OPE.Libra
