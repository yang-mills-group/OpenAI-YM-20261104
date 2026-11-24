import YM.OPE.Compatible.Gully.Lo
/-!
# Color launch through momentum shelves
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch Further.FreeCovariance.KP MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Nestle Balsam Weir
open GaussianScore Libra WithLp
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}
def grass (u:G.Color): Nestle.Tile→ₗ[ℝ] Stubble.Tile G where
   toFun x i:= x i • u
   map_add' a b:=by funext i; simp [add_smul]
   map_smul' t x:=by funext i;simp [smul_smul]
def hatB (x y z:Stubble.Tile G):=inner ℝ (Al G y z) (G.colorMat (Wj x))
def poltern (c:G.Color):G.Mat→ₗ[ℝ]ℝ where
   toFun x:=inner ℝ x (G.colorMat c)
   map_add' _ _:=inner_add_left ..
   map_smul' _ _:=real_inner_smul_left ..
def voteb {X Y Z F:Type}[AddCommGroup X][Module ℝ X][AddCommGroup Y][Module ℝ Y][AddCommGroup Z][Module ℝ Z][AddCommGroup F][Module ℝ F](A:X→ₗ[ℝ]X→ₗ[ℝ]Y)(L:Y→ₗ[ℝ]ℝ)(C:Z→ₗ[ℝ]X)(B:F→ₗ[ℝ] X):Z→ₗ[ℝ]F→ₗ[ℝ]ℝ where
    toFun z:=L.comp ((A (C z)).comp B)
    map_add' z f:=by ext g; change L (A (C (z+f)) (B g))= _; rw [map_add,map_add,LinearMap.add_apply,map_add];rfl
    map_smul' z f:=by ext g; change L (A (C (z • f)) (B g))=_; rw [map_smul,map_smul,LinearMap.smul_apply,map_smul];rfl
def harp (c w v:G.Color): Nestle.Zem:= voteb (Al G) (poltern c) (grass w) (grass v)
lemma versed (c w v:G.Color)(x y z:Nestle.Tile):hatB (grass c x) (grass w y) (grass v z)= voice x* harp c w v y z:=by
    rw [hatB,show Wj (grass c x)=voice x • c from (by unfold Wj voice; simp only [add_smul,sub_smul];rfl), map_smul,real_inner_smul_right]; rfl
lemma bol (c u v:G.Color): Vener (harp c u v) (inner ℝ (axle G u v) (G.colorMat c)):=by
    have he(x y:ℝ)(a:G.Color):grass a (basePair x y)=Stubble.root (x • a) (y • a):=by funext i; fin_cases i<;>rfl
    have hx(t s:ℝ)(x y:G.Color): axle G (t • x) (s • y)=(t*s) • axle G x y:=by unfold axle;rw [show Stubble.root (t • x) 0=t • Stubble.root x 0 from by rw [←crux];simp, show Stubble.root 0 (s • y)=s • Stubble.root 0 y from by rw [←crux];simp,map_smul,map_smul (Al G),LinearMap.smul_apply,smul_smul,mul_comm]; -- maybe smul zeros both match danger
    intro x y a b; change inner ℝ (Al G (grass u _) (grass v _)) _= _; rw [he,he,axle_cash,hx,hx,inner_add_left, real_inner_smul_left,real_inner_smul_left,axle_alt v u,inner_neg_left]; ring
abbrev layoutA {G: Type*}(p:Axis→Site n→G)(x:Face (Per n)):=localS p x.1 x.2.val.1 x.2.val.2
def scribeX (f g v:Axis→Site n→G.Color):ℝ:=∑ x:Face (Per n),hatB (layoutA f x) (layoutA g x) (layoutA v x)
def skid (f:Axis→Site n→ℝ)(u:G.Color): Axis→Site n→ G.Color:=fun i z=> f i z • u
abbrev exclaim (H:Even n.val)(p:Libra.Keys G (Limb H)) (a:Axis)(x:Site n):G.Color:=cloak H p (addressR (x,a))
abbrev expo (u:G.ColorIndex):G.Color:= toLp 2 (Pi.single u 1)
lemma ear_spec (x:G.ColorIndex)(y:Site n)(b:Pose)(v:Site n)(i:Axis)(h:4≤r)(H:Even n.val):exclaim H ((boost H (Train.top r) h C).inverse (poseT H y x b)) i v=
       (∑ k: Kv, torque b k *paper (reed b k) i (decks k y) v) • expo x:=by
          ext t; have ht:= wickPose (C:=C) H y v i b x t h; change Tags H t i v _ = _; rw [ht,PiLp.smul_apply]; unfold expo; simp [Pi.single_apply, eq_comm]
lemma largo {U:Gloam}(X Y Z:Candidate U)(a b c:G.Color)(j:ℕ):
   scribeX (n:=U.M j) (skid (fun i=>X i j) a) (skid (fun i=>Y i j) b) (skid (fun i=>Z i j) c)=Nestle.hash X Y Z (harp a b c) j:=by
   have he (X:Candidate U)(a:G.Color)(x y:Axis)(p:Site (U.M j)): localS (skid (fun i=>X i j) a) p x y=grass a (cup X p x y):=by funext i; fin_cases i<;>rfl
   unfold scribeX Face; rw [Fintype.sum_prod_type,Finset.sum_comm]; unfold Nestle.hash; simp_rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro p _; unfold layoutA mx;dsimp only; rw [he,he,he,versed]
end YM.OPE.StageLight
