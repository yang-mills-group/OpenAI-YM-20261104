import YM.OPE.Compatible.Gully.Mist
/-!
# Antenna
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stubble
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Maxwell Cascade PertExtension Series Score Next.Foundations Matrix
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n:Side}{G:Gauge}
variable {X M:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup M][NormedSpace ℝ M]
def rawB (f:X→ M): X→L[ℝ] X→L[ℝ]M:= (continuousMultilinearCurryFin1 ℝ X M).toContinuousLinearEquiv.toContinuousLinearMap.comp (continuousMultilinearCurryLeftEquiv ℝ (fun _ :Fin 2=>X) M (iteratedFDeriv ℝ 2 f 0))
def cloudB (f:X→M): X→ₗ[ℝ]X→ₗ[ℝ] M where
    toFun x:= (rawB f x).toLinearMap
    map_add' x y:=by ext z; change rawB f (x+y) z=_; rw [map_add (rawB f)]; rfl
    map_smul' x y:= by ext z; change rawB f (x • y) z=_; rw [map_smul (rawB f)]; rfl

private def AlX (f:X→M): X→ₗ[ℝ]X→ₗ[ℝ]M:= (2:ℝ)⁻¹ • (cloudB f + (cloudB f).flip)
private lemma rot_X (f:X→M)(p q:X): AlX f p q= AlX f q p:=by unfold AlX; simp [add_comm]
private lemma alo_X (f:X→M)(p:X)(hp:ContDiff ℝ ω f): AlX f p p=iteratedDeriv 2 (fun x:ℝ=>f (x • p)) 0:=by
    rw [iteratedDeriv_on_line (hp.contDiffAt.of_le le_top)]; rw [show AlX f p p=rawB f p p from by unfold AlX; change (2:ℝ)⁻¹ • (rawB f p p+rawB f p p)= _; rw [← two_smul ℝ (rawB f p p), smul_smul, inv_mul_cancel₀ (by norm_num),one_smul]]; unfold rawB; erw [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, continuousMultilinearCurryFin1_apply,continuousMultilinearCurryLeftEquiv_apply]; congr 1; ext1 i; fin_cases i<;>rfl
def Al (G:Gauge):Tile G→ₗ[ℝ]Tile G→ₗ[ℝ]G.Mat:=AlX maceX
lemma al_rot (p q:Tile G): Al G p q=Al G q p:=rot_X ..
lemma alo (p:Tile G): Al G p p=iteratedDeriv 2 (fun x:ℝ=>maceX (x • p)) 0:=alo_X _ _ sheet
lemma asti (L:X→L[ℝ] X→L[ℝ]M){F H:ℝ→X}(hf:ContDiff ℝ ω F)(hh:ContDiff ℝ ω H) (hF:F 0=0)(hH:H 0=0)(hx:deriv F 0=0) :iteratedDeriv 2 (cat L F H) 0=0:=by rw [iteratedDeriv_succ (n:=1),iteratedDeriv_one,ast L hf hh];simp only [Pi.add_apply,cat,hF,hH,hx,map_zero, _root_.zero_apply,add_zero]
lemma satX (p:Tile G): ContDiff ℝ ω (fun x:ℝ=> maceX (x • p)):= sheet.comp (f:=fun x:ℝ=>x • p) (by fun_prop)
def root (x y:G.Color):Tile G:=![x,y,x,y]
lemma root_add (x y u v:G.Color): root (x+y) (u+v)=root x u+root y v:=by funext i; fin_cases i<;>rfl
lemma crux (x y:G.Color)(t:ℝ): root (t • x) (t • y)=t • root x y:= by funext i; fin_cases i <;> rfl
lemma ring_solo (x:G.Color) : Al G (root x 0) (root x 0)=0:=by
   rw [alo,show (fun t:ℝ=> maceX (t • root x 0))=(0:ℝ→G.Mat) from funext fun v=>by simp only [←crux]; simp [maceX,mace,root]]; simp
lemma ring_pair (x y:G.Color): Al G (root x y) (root x y)= -Al G (root y x) (root y x):=by
   rw [alo,alo]; let f(a b:G.Color)(t:ℝ):= maceX (t • root a b); let F:=f x y; let H:=f y x
   let m:= ContinuousLinearMap.mul ℝ G.Mat
   have he : F+H+cat m F H=0:=by
      funext i; let X:= G.mat (G.lieExp (i • x)*G.lieExp (i • y)*(G.lieExp (i • x))⁻¹*(G.lieExp (i • y))⁻¹)
      let Y:= G.mat (G.lieExp (i • y)*G.lieExp (i • x)*(G.lieExp (i • y))⁻¹*(G.lieExp (i • x))⁻¹)
      have h:F i=X-1:=by unfold F f; rw [← crux]; rfl
      have h':H i=Y-1:=by unfold H f; rw [← crux]; rfl
      have hx:X*Y=1:= by unfold X Y; rw [← G.mat_mul]; rw [show G.lieExp (i • x)*_*(G.lieExp (i • x))⁻¹*(G.lieExp (i • y))⁻¹*(G.lieExp (i • y)*_*(G.lieExp (i • y))⁻¹*(G.lieExp (i • x))⁻¹)= 1 from by group,G.mat_one]
      change F i+H i+F i*H i=0; rw [h,h',mul_sub,sub_mul,hx]; simp;abel
   have hv(a b:G.Color):f a b 0=0:=by unfold f; rw [zero_smul,seamW]
   have hx(a b:G.Color): deriv (f a b) 0=0:=by rw [show deriv _ _= _ from wick0 (root a b)]; rw [show Wj (root a b)=0 from (by change a+b-a-b=0;abel)]; exact map_zero _
   have hf:ContDiff ℝ ω F:=satX _; have hh:ContDiff ℝ ω H:=satX _
   have hu : iteratedDeriv 2 (F+H+cat m F H) 0=0:=by rw [he]; simp
   rw [iteratedDeriv_add (show ContDiffAt ℝ 2 (F+H) 0 from (hf.add hh).contDiffAt.of_le le_top) ((sat _ hf hh).contDiffAt.of_le le_top),iteratedDeriv_add (hf.contDiffAt.of_le le_top) (hh.contDiffAt.of_le le_top)] at hu; erw [asti m hf hh (hv x y) (hv y x) (hx x y),add_zero] at hu; exact eq_neg_of_add_eq_zero_left hu
lemma ring_second (x:G.Color): Al G (root 0 x) (root 0 x)=0:=by rw [ring_pair,ring_solo,neg_zero]
def axle (G:Gauge) (x y:G.Color):= Al G (root x 0) (root 0 y)
lemma axle_cash(x y u v:G.Color): Al G (root x y) (root u v)= axle G x v+axle G u y:=by
    have hX(x y:G.Color): Al G (root x 0) (root y 0)=0:=by
       have he:root (x+y) 0=root x (0:G.Color)+root y 0:=by rw [←root_add]; simp
       have hh:=ring_solo (x+y); rw [he,map_add (Al G),LinearMap.add_apply,map_add,map_add,al_rot (root y 0),ring_solo, ring_solo, zero_add,add_zero, ← two_smul ℝ] at hh; exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
    have hY(x y:G.Color): Al G (root 0 x) (root 0 y)=0:=by
       have he:root 0 (x+y)=root 0 x+root 0 y:=by rw [←root_add];simp
       have hh:=ring_second (x+y); rw [he,map_add (Al G),LinearMap.add_apply,map_add,map_add,al_rot (root 0 y),ring_second,ring_second,zero_add,add_zero,← two_smul ℝ] at hh; exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
    have h(a b:G.Color):root a b=root a 0+root 0 b:=by rw [← root_add]; simp
    rw [h x y,h u v,map_add (Al G),LinearMap.add_apply,map_add,map_add,hX,hY,al_rot (root 0 y),zero_add,add_zero];rfl
lemma axle_alt (x y:G.Color):axle G x y= -axle G y x:=by
    have ht:=ring_pair x y; rw [axle_cash,axle_cash] at ht; -- two inject
    apply eq_neg_of_add_eq_zero_left; apply (smul_eq_zero (r:=(2:ℝ))).mp _ |>.resolve_left (show (2:ℝ)≠0 by norm_num); rw [smul_add,two_smul,two_smul,ht]; abel
lemma priceJet (p:Tile G): iteratedDeriv 3 (fun x:ℝ=> G.price (mace (x • p))) 0= (G.colorScale^2*2)⁻¹ * (6*inner ℝ (Al G p p) (G.colorMat (Wj p))):=by
   let H(t:ℝ):=maceX (t • p); have h:H 0=0:=by unfold H; rw [zero_smul,seamW]
   let s:ℝ:=(G.colorScale^2*2)⁻¹; let L:=innerSL ℝ (E:=G.Mat)
   have he: (fun x:ℝ=> G.price (mace (x • p)))=s • cat L H H:=by
      funext x; change _= s*inner ℝ (H x) (H x); rw [real_inner_self_eq_norm_sq]; change _= s*‖G.mat _ -1‖^2; unfold s; rw [show forall a:G.El,G.price a= (‖G.mat a-1‖/G.colorScale)^2/2 from ?_]; rw [div_pow]; ring
      intro a; change _=(G.chord a)^2/_; rw [G.chord_price]; ring
   erw [he,iteratedDeriv_const_smul (show ContDiffAt ℝ 3 (cat L H H) 0 from (sat _ (satX _) (satX _)).contDiffAt.of_le le_top),blitz L (satX _) (satX _) h h,← alo,wick0]; change s • (3 • (⟪_,G.colorMat _⟫+⟪G.colorMat _,_⟫))=_; simp only[nsmul_eq_mul, Nat.cast_ofNat,smul_eq_mul]; rw [real_inner_comm _ (Al G p p)]; unfold s;ring
end YM.OPE.Stubble
