import YM.OPE.Compatible.Navy.Gem
/-!
# price hop with arbitrary triangular germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Pilot
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{I J U K:Type}[Fintype I][Fintype J][Fintype U]
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable (p: U ≃ I ⊕ J)
local notation "Y" => Keys G U
namespace Hark
variable {v:Tile G I→Tile G J}(F:Hark v)
abbrev crown := (F.suite p).gradient
lemma ballRun : ∀ᶠ x:Keys G U in 𝓝 0, put (crown p F x)=F.run p (put x):=by
     let L:= F.suite p; have he:Tendsto (fun i:Y=> F.run p (put i)) (𝓝 0) (𝓝 1):=by simpa only [Function.comp_apply,put_zero,F.run0 p] using! ((F.run p).continuous.comp putC).tendsto 0
     filter_upwards [L.lead_grad,he.eventually Stand.sphere] with i hi hk; change L.gradient i = _ at hi; rw [show crown p F i= _ from hi]; exact hk
lemma outlookZ : ∀ᶠ x:Keys G U in 𝓝 0, prL p G (crown p F x)=prL p G x ∧ put (prR p G (crown p F x))= put (prR p G x)* v (put (prL p G x)):=by
     let X:=F.suite p; let L:= prL p G; let T:=prR p G
     have ht:Tendsto L (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! L.continuous.tendsto 0
     have he:Tendsto (X.gradient) (𝓝 0) (𝓝 0):= by simpa only [X.grad0] using! X.gradC.continuousAt.tendsto
     filter_upwards [F.ballRun p, ht.eventually local_zone,(ht.comp he).eventually local_zone] with x h hh hp; let y:=crown p F x; constructor
     · have hu: put (L y)=put (L x):=by rw [show put (L y)= _ from (runfront p y).symm,h,F.runleft,runfront]
       exact Eq.trans hp.symm ((congr_arg unput hu).trans hh)
     rw [show put _= _ from (runlift p y).symm,h,runright,runlift,runfront]
lemma alone (A:Lid G I)(X:Lid G J)(T:Lid G U) (h:T.f ∘ crown p F =ᶠ[𝓝 0] roomP p A X) (hv:T.w∘ crown p F=ᶠ[𝓝 0] weightP p A X){P:ChartRatio G}(R:LocalRatio P)(f:ScriptJ (Keys G I))(hx:f.B): T.pay P (f ∘ prL p G)= A.pay P f:=by
       rw [← simply p A X R f hx]; let L:=F.suite p; let K:= cradle p A X; let w:= f ∘ prL p G; have ht :T.f ∘ L.gradient=ᶠ[𝓝 0] K.f:= h
       have hr : Cel (T.f ∘ L.gradient):=by obtain ⟨z,he,hq⟩:=K.bright; exact ⟨z,he,fun x=> (hq x).trans_eq (by unfold jet; rw [(ht.iteratedFDeriv ℝ 2).eq_of_nhds])⟩
       apply Eq.symm; apply L.congr_charge _ (q:=w) _ _ R
       · refine ⟨hr,L.chore T,?_,?_⟩
         · ext1 x; unfold Pawn.mold jet; simp_rw [(ht.iteratedFDeriv ℝ _).eq_of_nhds];rfl -- simp metav
         have he:T.w ∘ L.gradient=ᶠ[𝓝 0] (cradle p A X).w:=hv; ext1 x; unfold Pawn.mold jet; simp_rw [(he.iteratedFDeriv ℝ _).eq_of_nhds]
       · exact fun i=> (hx i).compLinear (prL p G).toLinearMap
       intro x; refine (Reads.selves (f (prL p G x))).cong ?_; let l(t:ℝ):=t•x; have he:Tendsto l (Tested.germ) (𝓝 0):=by simpa only [l,zero_smul] using! (show Continuous (fun t:ℝ=>t • x) from continuous_id.smul continuous_const).tendsto 0|>.mono_left (show Tested.germ ≤ 𝓝 0 from nhdsWithin_le_nhds)
       filter_upwards [he.eventually (F.outlookZ p), Tested.eventually_pos] with t h ht; change (f (prL p G (_ • L.gradient _))).atK _=_; rw [map_smul,show prL p G (L.gradient _) =_ from h.1, show prL p G (l t) = _ from map_smul .., inv_smul_smul₀ ht.ne'] -- precise
end Hark
end YM.OPE.Cascade.Pilot
