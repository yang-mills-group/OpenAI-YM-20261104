import YM.OPE.Compatible.Melon.Fret
/-!
# Equivariance purely for virtual Stands (preserves Haar prescription) -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {A:Alps B Q i l} {H: Even n.val}
local notation "TK" => Keys G (Limb H)
variable (T:Plot H) {I:Type}
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
def glint (I:Type)(v:G.El): Keys G I≃ₗ[ℝ] Keys G I where
   toFun x i:= G.adjoint v (x i)
   map_add' _ _:=by ext i; simp
   map_smul' _ _:=by ext i; simp
   invFun x i:= G.adjoint v⁻¹ (x i)
   left_inv i:=by ext; dsimp only; rw [← G.adjoint_mul];simp -- dsimp
   right_inv i:=by ext; dsimp only; rw [← G.adjoint_mul];simp
def plaque (v:G.El)(s:Tile G I)(j:I):G.El:= v*s j*v⁻¹
@[simp] lemma patchZ (v:G.El)(p: Keys G I): put (glint I v p)=plaque v (put p):=funext fun _=> YM.Stationary.adjoint_exp ..
lemma set_cover (g:G.El)(u: Tile G T.Stable)(v:Tile G T.Free): plaque g (T.cite u v)=T.cite (plaque g u) (plaque g v):=by funext i; unfold plaque Stand.cite; split <;>rfl
@[simp] lemma plaque_zero (g:G.El): plaque g (1:Tile G I)=1:=by ext; simp [plaque]
lemma dress_cover (g:G.El)(u:Tile G (Node H))(v:Tile G (Limb H)): plaque g ((Pond H).dress u v)=(Pond H).dress (plaque g u) (plaque g v):=by funext i; unfold plaque Score.dress; group
lemma plum (g:G.El)(v:Tile G (Limb H)): T.stepSet (plaque g v)= plaque g (T.stepSet v):=by
      have he(u:Tile G (Limb H)): T.sweep (plaque g u)=plaque g (T.sweep u):=by
           symm; refine T.sweep_spec _ _ (fun i h=>?_) (fun p=>?_)
           · unfold plaque; rw [T.swept u h]; group
           rw [← dress_cover]; unfold plaque; rw [T.bare_sweep];group
      let P:= T.splitSet v; let Q:=fun i:T.Free=> v i.val
      change (Pond H).dress (T.sweep (T.cite (plaque g P) 1))⁻¹ (T.cite 1 (plaque g Q))=plaque g ((Pond H).dress (T.sweep (T.cite P 1))⁻¹ (T.cite 1 Q))
      rw [dress_cover,set_cover T,plaque_zero, show T.cite (plaque g P) 1=plaque g (T.cite P 1) by rw [set_cover T,plaque_zero],he]; rw [show ∀ u:Tile G (Node H),plaque g u⁻¹=(plaque g u)⁻¹ from fun u=>by funext i; unfold plaque; simp [mul_assoc]] -- last
lemma glow (v:G.El): (layerZ T ∘ glint _ v)=ᶠ[𝓝 0] (glint _ v) ∘ layerZ T :=by
      let G₁:= T.skews G; let L:=glint (Limb H) v; let Z:= L.toContinuousLinearEquiv.toContinuousLinearMap; have hp:Tendsto Z (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! Z.continuous.tendsto 0
      have he : ∀ᶠ x:TK in 𝓝 0, put (layerZ T x)= T.stepSet (put x):=by
           have he:Tendsto (fun x:TK=>T.stepSet (put x)) (𝓝 0) (𝓝 1):=by simpa only [Function.comp_apply,put_zero,G₁.clan] using! (G₁.q.continuous.comp putC).tendsto 0
           unfold layerZ; filter_upwards [G₁.lead_grad,he.eventually Stand.sphere] with x hx hv; rw [hx]; exact hv
      have hy: Tendsto G₁.gradient (𝓝 0) (𝓝 0):=by simpa only [G₁.grad0] using! G₁.gradC.continuousAt.tendsto
      filter_upwards [he,hp.eventually he, (hp.comp hy).eventually local_zone,(hy.comp hp).eventually local_zone] with y ha hb hc ht; change unput (put (layerZ (G:=G) T (glint _ v y)))=layerZ T (glint _ v y) at ht; change unput (put (glint _ v (layerZ T y)))= glint _ v (layerZ T y) at hc; change layerZ T (glint _ v y)=glint _ v (layerZ T y); rw [← hc,patchZ,ha,← ht]; change put (layerZ T (glint _ v y))= T.stepSet (put (glint _ v y)) at hb; rw [hb,patchZ,plum T]
lemma glint_roll (v:G.El)(x:FD): glint _ v (T.rollX x)= T.rollX (glint _ v x):=by
     funext i; change G.adjoint v (T.cite 0 x _) = T.cite 0 _ _; unfold Stand.cite; split; exact map_zero _; rfl
lemma glint_palm (v:G.El)(x:DK): glint _ v (T.palmL G x)= T.palmL G (glint _ v x):=by
     funext i; change G.adjoint v (T.cite x 0 _) = T.cite _ 0 _; unfold Stand.cite; split; rfl; exact map_zero _
lemma gleam_dash (v:G.El)(x:TK): glint _ v (T.dtex G x)=T.dtex G (glint _ v x):=by
     let M:= (glint (Limb H) v).toContinuousLinearEquiv.toContinuousLinearMap; have hm: fderiv ℝ (layerZ T ∘ M) 0=fderiv ℝ (M ∘ layerZ T) 0:=(glow T v).fderiv_eq; let W:= T.skews G; have he:= W.gradC.differentiableAt (by simp); rw [fderiv_comp _ M.differentiableAt he, fderiv_comp, map_zero,M.fderiv,M.fderiv] at hm; exact DFunLike.congr_fun hm.symm x; · rw [map_zero]; exact he
     exact M.differentiableAt
lemma gleam_p (v:G.El)(x:DK): T.palmFrame G (glint _ v x)=glint _ v (T.palmFrame G x):= by unfold Stand.palmFrame; simp only [LinearMap.comp_apply]; rw [←glint_palm]; exact (gleam_dash T v _).symm
end YM.OPE.Cascade.Glass
