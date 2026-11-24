import YM.OPE.Compatible.Straws.Welt
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
open Arc Flock Pilot Coin
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F]
-- tensors span
abbrev fuseX (p:E→ℝ)(q:F→ℝ)(x:E×F):= p x.1*q x.2
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma fuseB (p:E→ℝ)(q:F→ℝ)(h:Bond p)(hx:Bond q): Bond (fuseX p q):= ((h.compLinear (LinearMap.fst ℝ E F))).mul (hx.compLinear (LinearMap.snd ℝ E F))
lemma sewn (P: (E×F→ℝ)→Prop)(hs:∀ f:E→ℝ,∀ g:F→ℝ,Bond f→Bond g→P (fuseX f g))(hy:∀ f,Bond f→ P f→∀ c:ℝ,P (c • f))(hv:∀ f g,Bond f→Bond g→P f→P g→P (f+g)):∀ f,Bond f→P f:=by
     apply Quilting.everything; refine ⟨?_,hy,hv⟩; intro s
     suffices H:∀ (p:E→ℝ)(q:F→ℝ),Bond p→Bond q→P (fuseX p q*dotV s) by simpa only [show fuseX (1:E→ℝ) (1:F→ℝ)= 1 from funext fun i=>one_mul _,one_mul] using! H _ _ Bond.one Bond.one
     induction s with
     | nil=> intro p q hp hq; rw [show dotV ([]:List (Dual' (E×F)))=1 from rfl, mul_one]; exact hs p q hp hq
     | cons a s ih=>
       intro p q hp hq; let A:=a.comp (LinearMap.inl ℝ E F); let B:=a.comp (LinearMap.inr ℝ E F); let u:=p*⇑A; let v:=q*⇑B; have hh:Bond u:= hp.mul (Bond.glyph A); have he:Bond v:= hq.mul (Bond.glyph B); rw [dot_cons,show fuseX p q*(_ * _) = fuseX u q*dotV s+fuseX p v*dotV s from ?_]; exact hv _ _ ((fuseB _ _ hh hq).mul (bonded s)) ((fuseB _ _ hp he).mul (bonded s)) (ih u q hh hq) (ih p v hp he)
       funext x; have ht : a x=A x.1+B x.2:=by nth_rw 1 [show x=(x.1,0)+(0,x.2) by simp]; rw [map_add];rfl
       simp only [Pi.mul_apply,ht,u,v,Pi.add_apply,fuseX];ring
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
lemma duoS (p q:E→Token)(h:ScriptJ.B p)(hp:ScriptJ.B q):draw (p+q) L μ=draw p L μ+draw q L μ:=by
     obtain ⟨h1,h2,h3⟩:= bondX h; obtain ⟨h4,h5,h6⟩:= bondX hp; apply JetS.eta; exact sun μ L h1 h4; exact sun μ L h2 h5; exact sun μ L h3 h6
abbrev streak (δ:ℝ→E)(x:ℝ→F)(p:F×E→ℝ)(j:E):= trill fun t=> p (x t,j-δ t)
variable {δ:ℝ→E}{a b:E}(h:Reads δ ⟨0,a,b⟩){x:ℝ→F}(hp:Gael x)
include h hp
omit [MeasurableSpace E][BorelSpace E] in
lemma Stalk (p:F×E→ℝ)(hy:Bond p)(j:E): Reads (fun t=> p (x t,j-δ t)) (streak δ x p j):= Gael.oath (show Gael (p∘fun t=>(x t,j-δ t)) from Gael.climb _ hy (Gael.union hp (Exists.intro _ ((Reads.constants _).minus h))))
local notation "W"=> Warp L a b
local notation "ΣXt" p => streak δ x p
lemma vintage (p:F×E→ℝ)(hy:Bond p): ScriptJ.B (streak δ x p) ∧ Reads (fun t=> L.average μ (fun y=> p (x t,y))) (draw (W*streak δ x p) L μ):=by
      apply sewn _ ?_ ?_ ?_ p hy
      · -- rect
        intro f g hf hg; let s:=f ∘ x; have hv := Gael.oath (Gael.climb f hf hp); let t:=trill (f ∘ x); have hx(q): Reads (fun i=> (fuseX f g) (x i,q-δ i)) (t * nestE a b g q):= hv.pile (nestHop q a b g hg _ h)
        let k:E→Token:=fun _=>t; have hb:ScriptJ.B k:=Xbond (Bond.keep t.s) (Bond.keep t.l) (Bond.keep t.h); let P':= fuseX f g; change ScriptJ.B (streak δ x P')∧ _; rw [show streak δ x P'=k*nestE a b g from funext fun i=> Gael.chooses (hx i)]; constructor
        · exact ScriptJ.height hb (nestE_B _ _ _ hg)
        rw [mul_left_comm, show draw _ _ _=_ from (show draw (k*(W*nestE a b g)) L μ = _ from drips μ L _ t (ScriptJ.height (warpB L a b) (nestE_B _ _ _ hg))),Recuperate _ _ _ _ _ hg]; apply (hv.pile (Reads.constants (L.average μ g))).cong; filter_upwards with i; exact scooted μ L (f (x i)) g
      · rintro f hF ⟨hp',ht⟩ c; let k:E→Token:=fun _=>plainJ c; have hb:ScriptJ.B k:= Xbond (Bond.keep _) (Bond.keep _) (Bond.keep _)
        rw [show streak δ x (c • f)=k*streak δ x f from funext fun i=>Gael.chooses ((Reads.constants _).pile (Stalk h hp _ hF i))]; refine ⟨ScriptJ.height hb hp',?_⟩; rw [mul_left_comm,show draw (k*_) L μ= _ from drips μ L _ (plainJ c) (ScriptJ.height (warpB L a b) hp')]; exact ((Reads.constants c).pile ht).cong (Filter.Eventually.of_forall fun t=> scooted μ L _ _)
      rintro f g hf hg ⟨hp',ht⟩ ⟨he,hs⟩; rw [show streak δ x (f+g)= (streak δ x f+streak δ x g) from funext fun i=> Gael.chooses ((Stalk h hp f hf i).sum (Stalk h hp g hg i)),mul_add,duoS μ L _ _ (ScriptJ.height (warpB L a b) hp') (ScriptJ.height (warpB L a b) he)]; exact ⟨ ScriptJ.key hp' he,(ht.sum hs).cong (Filter.Eventually.of_forall fun i=>sun μ L (Shift.leanB f hf (x i)) (Shift.leanB g hg (x i)))⟩
end Stranded
end YM.OPE.Libra
