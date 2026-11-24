import YM.OPE.Compatible.Loire.Aces
import YM.OPE.Compatible.Gully.Sail
/-!
# Θ obtains on capsule of the regulator. Ad covariance proof; not estimate on single constant mode.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume.Script Flock StageLight
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n:Side}{G:Gauge}{C:RG.KernelChoices}{P:ChartRatio G}
variable {i:ℕ}{l b:ℝ}{B:Sponsor G} {Q:Seasons B}{A:Alps B Q i l}{H:Even n.val}
local notation "TK"=> Keys G (Limb H)
local notation "W"=> Chart.tangent G (Limb H)
lemma grain (A:Alps B Q i l)(v:G.El)(X:TK): mural H A (glint _ v X)=mural H A X:=by
     apply (muralG H A _ _ (fun _=> v⁻¹) _).1
     rw [patchZ]; funext i; change v⁻¹*(v*_ *v⁻¹)*(v⁻¹)⁻¹ = _; group
lemma flareOwn (L:Alps B Q i l)(k:ℕ)(v:G.El)(p: TK) : jet (mural H L) k (glint _ v p)=jet (mural H L) k p:=by
     let E:TK ≃ₗ[ℝ] TK:= glint _ v; let T:=E.toContinuousLinearEquiv.toContinuousLinearMap; let f:=mural H L; have hp:f ∘ T=f:= funext fun x=>grain L v x
     unfold jet; nth_rw 2 [show mural H L=f∘T from hp.symm]; rw [jets_linear T ((muralD H L).of_le le_top)];rfl
lemma greet (v:G.El)(p:TK)(hm:A.gear=Train.top i)(h:4≤ i): (boost H (Train.top i) h B.K).P (glint _ v p) (glint _ v p)=(boost H (Train.top i) h B.K).P p p :=by
     rw [← hm]; have ho:= Lit.lip H A p h -- right 2 wave prefer mural_in
     have he:= mural_in H A p h; have ht:= mural_in H A (glint _ v p) h; rw [flareOwn A,qLinear] at ht; linarith only [ht,he]
-- priced vertex map. Norm matter. Use positive mural one not path antics.
abbrev dag :TK→ₗ[ℝ] Stray G n where
   toFun:=exclaim H
   map_add' x y:=by ext1 a; funext v; change cloak H (x+y) _= _;rw [map_add];rfl
   map_smul' a b:=by ext1 x; funext v;change cloak H (a • b) _= _; rw [map_smul];rfl
def signal (E F: Type*) [AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F](A:F→ₗ[ℝ]F→ₗ[ℝ] F→ₗ[ℝ]ℝ)(x:E→ₗ[ℝ] F): E→ₗ[ℝ] E→ₗ[ℝ]E→ₗ[ℝ]ℝ where
    toFun p:= { toFun y:= (A (x p) (x y))∘ₗ x, map_add':=fun y z=>LinearMap.ext fun i=>by change A _ (x (y+z)) _=_; rw [map_add, map_add, LinearMap.add_apply];rfl, map_smul':=fun a b=>LinearMap.ext fun i=>by change A _ (x (a • b)) _=_; rw [map_smul,map_smul,LinearMap.smul_apply]; rfl }
    map_add' p q:=LinearMap.ext fun i=> LinearMap.ext fun j=> by change A (x (p+q)) _ _= _; rw [map_add,map_add,LinearMap.add_apply,LinearMap.add_apply];rfl
    map_smul' p u:= LinearMap.ext fun i=> LinearMap.ext fun j=>by change A (x (p • u)) _ _=_; rw [map_smul,map_smul,LinearMap.smul_apply,LinearMap.smul_apply]; rfl
noncomputable def anthem (G:Gauge)(H:Even n.val):Temple (Keys G (Limb H)):= (G.colorScale^2*8)⁻¹ • signal _ _ (sal G n) dag
lemma drumA (hp:Track A n): Trill (anthem G H)=jet (mural H A) 3:=funext fun i=> (dataX i hp).symm
lemma anthemBond (hp:Track A n):Bond (Trill (anthem G H)):=by
    rw [drumA hp]; exact Bond.scale _ (Bond.multiline (ι:=Fin 3) (F:=TK) _ (fun _ :Fin 3=> id) (fun _ c=> Bond.glyph c))
-- derivative in invariant requires pp
lemma stroke (hp: Track A n)(x:TK)(k:G.El)(v:TK): poke (glint (Limb H) k x) (Trill (anthem G H)) (glint _ k v)=poke x (Trill (anthem G H)) v:=by
    let T:=glint (Limb H) k; let L:=T.toContinuousLinearEquiv.toContinuousLinearMap; let f:=Trill (anthem G H)
    have he:f ∘ L=f:=funext fun x=>by change f _=_; unfold f; rw [drumA hp]; exact flareOwn ..
    unfold poke; let P:=LinearMap.toContinuousLinearMap T.toLinearMap; change _=fderiv ℝ f v x; rw [show f=f ∘ L from he.symm]; -- occurrence uncertain
    rw [fderiv_comp v (show DifferentiableAt ℝ f _ from (anthemBond hp (H:=H)|>.smooth.differentiable (by simp) (L v))) L.differentiableAt,L.fderiv]; rfl
lemma tideD (hm:A.gear=Train.top i)(h:4≤ i)(hp:Track A n)(x:TK)(hs:G.Simple): (boost H (Train.top i) h B.K).average W (poke x (Trill (anthem G H)))=0:=by
   let L:Law TK:= boost H (Train.top i) h B.K; let f(x:TK):= L.average W (poke x (Trill (anthem G H))); let P:=Trill (anthem G H)
   have he(x: TK):Bond (poke x P):= (anthemBond hp).amount x
   let g:TK→ₗ[ℝ]ℝ:={ toFun:=f,map_add':=fun x y=>by unfold f;change L.average W _= _; rw [show poke (x+y) (Trill (anthem G H))=poke x P+poke y P from funext fun i=>map_add .., sun W L (he _) (he _)], map_smul':=fun c x=>by unfold f; rw [show poke (c • x) (Trill (anthem G H))=c • poke x P from funext fun w=>map_smul .., scooted]; rfl }
   refine YM.Stationary.slot_fixed hs (LinearMap.toContinuousLinearMap g) ?_ x
   intro v x; let E:=glint (Limb H) v; change f (E x)=f x; unfold f; rw [meanFit W W L L E.toLinearMap (dual_wick E L L (fun x=>(greet v x hm h).symm)) (poke (E x) (Trill _)) (he _)]; apply congrArg; funext i; exact stroke hp x v i
end YM.OPE.Shrew
