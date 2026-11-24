import YM.OPE.Compatible.Navy.Flag
/-!
# Homeomorphism for local germs of Φ. Triangular (multiplication by frame) with no Haar change. -/
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
local notation "XF" => Tile G I
local notation "YF" => Tile G J
local notation "LF" => Tile G U
def curveW (u:XF→YF)(h:Continuous u): (XF×YF)≃ₜ (XF×YF) where -- parentheses
    toFun x:=(x.1,x.2*u x.1)
    invFun x:=(x.1,x.2*(u x.1)⁻¹)
    left_inv x:=by simp
    right_inv x:=by simp
    continuous_toFun:= continuous_fst.prodMk (continuous_snd.mul (h.comp continuous_fst))
    continuous_invFun := continuous_fst.prodMk (continuous_snd.mul (h.comp continuous_fst).inv)
lemma curveH (u:XF→YF)(h:Continuous u): MeasurePreserving (curveW u h) ((Gem G I).prod (Gem G J)) ((Gem G I).prod (Gem G J)):=by
      let T:= curveW u h; let A:=Gem G I; let B:= Gem G J; have he(p:Tile G J): MeasurePreserving (fun i:Tile G J=>i*p) B B := measurePreserving_pi _ _ fun i:J=> measurePreserving_mul_right G.probHaar (p i)
      refine ⟨T.measurable,?_⟩; ext s hs; rw [Measure.map_apply T.measurable hs,Measure.prod_apply (T.measurable hs), Measure.prod_apply hs]
      apply lintegral_congr_ae (Eventually.of_forall fun i=> ?_); exact (he (u i)).measure_preimage (s:=(Prod.mk i) ⁻¹' s) ((hs.preimage (measurable_const.prodMk measurable_id)).nullMeasurableSet)
def timeL (x:LF):XF := (shoot p G.El x).1
def timeR (x:LF):YF := (shoot p G.El x).2
structure Hark (u: XF→ YF):Prop where
    moving : Continuous u
    prices (i:J) : ContDiffAt ℝ ω (fun x:Keys G I=>G.mat (u (put x) i)) 0
    zero : u 1=1
namespace Hark
variable {u: Tile G I→ Tile G J}
nonrec def run (Y: Hark u): LF ≃ₜ LF:= (shoot p G.El).trans ((curveW u Y.moving).trans (shoot p G.El).symm)
omit [Fintype J] [Fintype U] in lemma runleft (Y:Hark u) (i): timeL p (Y.run p i)=timeL p i := by unfold run timeL; simp [curveW]
omit [Fintype J] [Fintype U] in lemma runright (Y:Hark u)(i): timeR p (Y.run p i)=timeR p i*u (timeL p i):= by unfold run; simp [timeL,timeR,curveW]
omit [Fintype J] [Fintype U] in lemma run0 (Y:Hark u): Y.run p 1=1:= by apply (shoot p G.El).injective; apply Prod.ext (Y.runleft p 1); change timeR p _=_; rw [Y.runright,show timeL p (1:LF)=1 from rfl,Y.zero,mul_one];rfl
omit [Fintype I] [Fintype J] [Fintype U] in
@[simp] lemma runlift (x: Keys G U): timeR p (put x)=put (prR p G x):=rfl
omit [Fintype I] [Fintype J] [Fintype U] in
@[simp] lemma runfront (x: Keys G U): timeL p (put x)=put (prL p G x):=rfl
omit [Fintype J] in lemma scripted (Y:Hark u)(i:U):ContDiffAt ℝ ω (fun x: Keys G U=> G.mat (Y.run p (put x) i)) 0:=by
      obtain ⟨j,hj⟩|⟨j,hj⟩: (∃ j,lead p j=i) ∨∃ j,Pilot.secondC p j=i:=by
           cases h:p i with
           | inl j=> exact Or.inl ⟨j,(p.apply_eq_iff_eq_symm_apply.mp h).symm⟩
           | inr j=> exact Or.inr ⟨j,(p.apply_eq_iff_eq_symm_apply.mp h).symm⟩
      · simp_rw [← hj, show ∀ x: Keys G U,Y.run p (put x) (lead p j)=put x (lead p j) from fun x=> congr_fun (Y.runleft p _) j]; exact Stand.paintD ..
      simp_rw [←hj, show ∀ x: Keys G U, Y.run p (put x) (Pilot.secondC p j)= put x _ * u (put (prL p G x)) j from fun x=>congr_fun (Y.runright p _) j, G.mat_mul]; let L':= prL p G; exact (Stand.paintD ..).mul ((show ContDiffAt ℝ ω _ _ from L'.map_zero.symm ▸ Y.prices j).comp (g:=fun x=> G.mat (u (put x) j)) (f:=L') _ L'.contDiff.contDiffAt)
def suite (Y:Hark u): Dimes G U U where
    q:= Y.run p
    clan:=Y.run0 p
    acts:= by
         let A:= Gem G U; let B:= (Gem G I).prod (Gem G J); let X:=shoot p G.El; have he : MeasurePreserving X A B:=by
              have he: A= Measure.map X.symm B:= (brewing p G).map_eq.symm; refine ⟨X.measurable,?_⟩; rw [he,Measure.map_map X.measurable X.symm.measurable, show ⇑X ∘ X.symm=id from funext fun i=> X.apply_symm_apply i, Measure.map_id]
         exact ((brewing p G).comp (curveH u Y.moving)).comp he
    lifted := by apply contDiffAt_pi.mpr; intro i; exact ((show ContDiffAt ℝ ω G.plog (G.mat (Y.run p (put 0) i)) from (by rw [put_zero,Y.run0]; exact G.plog_diff)).comp (f:=fun x=> G.mat (Y.run p (put x) i)) _ (Y.scripted p i)).of_le le_top
end Hark
end YM.OPE.Cascade.Pilot
