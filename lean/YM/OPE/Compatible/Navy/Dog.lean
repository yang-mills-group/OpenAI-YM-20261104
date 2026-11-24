import YM.OPE.Compatible.Navy.Deep
/-!
# leading τ factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Pilot
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{I J U K:Type}[Fintype I][Fintype J][Fintype U]
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable (p: U ≃ I ⊕ J)
local notation "L" => prL p G
local notation "R" => prR p G
section av
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (μ:Measure E)[μ.IsAddHaarMeasure] (ν:Measure F)[ν.IsAddHaarMeasure](P:Law E)(Q:Law F)
theorem twoHaar : (μ.prod ν).IsAddHaarMeasure:=inferInstance -- incl
open ScriptJ JetS
lemma drips (s:ScriptJ E)(f:Token)(h:s.B): draw (fun x=> f*s x) P μ=f*draw s P μ:=by
     obtain ⟨h1,h2,h3⟩:= bondX h; apply eta
     · simp_rw [ml_s,draw]; exact scooted μ P f.s _
     · simp_rw [draw,ml_l]; rw [show P.average μ (fun x=>f.s* (s x).l+ f.l*(s x).s) = _ from sun μ P (Bond.scale f.s h2) (Bond.scale f.l h1)]; exact congr_arg₂ HAdd.hAdd (scooted μ P f.s _) (scooted μ P f.l _)
     simp_rw [draw, ml_h]; rw [show P.average μ (fun x=> f.s*(s x).h+ f.l*(s x).l+f.h*(s x).s)=_ from sun μ P ((Bond.scale f.s h3).add (Bond.scale f.l h2)) (Bond.scale f.h h1)]; change P.average μ ((f.s • fun i=> (s i).h)+(f.l • fun i=>(s i).l)) + P.average μ (f.h • fun i=>(s i).s)=_; rw [sun μ P (Bond.scale f.s h3) (Bond.scale f.l h2),scooted,scooted,scooted]
lemma drawProd (s: ScriptJ E)(p: ScriptJ F)(h:s.B)(hh:p.B): draw (fun x:E×F=> s x.1*p x.2) (united P Q) (μ.prod ν)= draw s P μ*draw p Q ν:=by
     let Sg(x:E×F):=s x.1*p x.2; let Y(x:E):=draw (fun y:F=> Sg (x,y)) Q ν; have hC:ScriptJ.B Sg:= height (p:=fun x:E×F=>s x.1) (s:=fun x:E×F=>p x.2) (fun i=>(h i).compLinear (LinearMap.fst ℝ E F)) (fun i=>(hh i).compLinear (LinearMap.snd ℝ E F))
     have ht : draw Sg (united P Q) (μ.prod ν)=draw Y P μ:=by apply eta; exact harvested μ ν P Q _ (hC 0); exact harvested μ ν P Q _ (hC 1); exact harvested μ ν P Q _ (hC 2)
     have he(x): Y x= s x * draw p Q ν:= drips ν Q p (s x) hh
     rw [show (fun x:E×F=> s x.1*p x.2)=Sg from rfl, ht,show Y= (fun x=> draw p Q ν*s x) from funext fun x=> (he x).trans (mul_comm ..), drips μ P s _ h,mul_comm]
end av
variable (A:Lid G I) (B:Lid G J)
open ScriptJ JetS
lemma flurry (f:ScriptJ (Keys G I))(g:ScriptJ (Keys G J))(h:f.B)(he:g.B): draw (fun v=> f (L v)*g (R v)) (penon <| cradle p A B) (Chart.tangent G U) = draw f (penon A) (Chart.tangent G I)*draw g (penon B) (Chart.tangent G J):=by
     let M:= (Pilot.drinks p G).toLinearEquiv; let W:= cradle p A B; let P:=penon A; let Q:=penon B; let T:=penon W; have hx(x): T.P x x= (united P Q).P (M x) (M x):=by
        have hp(x): jet W.f 2 x= P.P (prL p G x) _ /2+ Q.P (prR p G x) _ /2:= (jet_purse p A B 2 x).trans (congr_arg₂ _ (penon_shape A _) (penon_shape B _)); have he:= hp x; rw [penon_shape] at he; change T.P x x /2= _ at he; rw [united_shape]; change T.P x x=P.P (prL p G x) (prL p G x)+Q.P (prR p G x) (prR p G x); linarith only [he]
     let μ:= Chart.tangent G I; let ν:= Chart.tangent G J; let u(v:Keys G U):= f (prL p G v)*g (prR p G v); have hu : ScriptJ.B u:= ScriptJ.height (p:=f ∘ prL p G) (s:=g ∘ prR p G) (fun i=>(h i).compLinear (prL p G).toLinearMap) (fun i=>(he i).compLinear (prR p G).toLinearMap) -- notation error
     haveI: (μ.prod ν).IsAddHaarMeasure:= twoHaar (E:=Keys G I) (F:=Keys G J) _ _ -- instance grows let
     rw [show draw (fun v=> f (prL p G v)*g (prR p G v)) _ _=_ from ease u hu M T _ hx _ (μ.prod ν),show (fun v=> u (M.symm v))=(fun x: Keys G I×Keys G J=>f x.1*g x.2) from ?_]; exact drawProd μ ν P Q f g h he
     ext1 x; exact congr_arg (fun x: Keys G I× Keys G J=> f x.1*g x.2) (M.apply_symm_apply x)
end YM.OPE.Cascade.Pilot
