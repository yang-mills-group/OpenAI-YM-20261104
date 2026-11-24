import YM.OPE.Compatible.Melon.Dream
/-!
# Cubic with 2 noises survives conditional averaging to a linear functional. No scalar direction means that mean dies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock
attribute [local instance] Gauge.frobInner
variable {H: Even n.val} (T: Plot H) {I:Type}
local notation "TK" => Keys G (Limb H)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
local notation "W" => Chart.tangent G T.Stable
section
-- helper polarization
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
def treeP (g:E→ₗ[ℝ](E →ₗ[ℝ] E →ₗ[ℝ] ℝ))(x:E):=g x x x
lemma movement (g:E→ₗ[ℝ](E →ₗ[ℝ] E →ₗ[ℝ] ℝ))(x y:E): treeP g (x+y)+treeP g (x-y)=2*treeP g x+2*(g x y y+g y x y+g y y x):=by unfold treeP; simp only [map_add,map_sub, LinearMap.add_apply,LinearMap.sub_apply];ring
nonrec def with3 (T:ContinuousMultilinearMap ℝ (fun _ :Fin 3=>E) ℝ): E→ₗ[ℝ](E→ₗ[ℝ] E→ₗ[ℝ] ℝ) where
   toFun p:= {
      toFun q:={
         toFun r:=T (![p,q,r])
         map_add' x y:=by
            have hb:= DFunLike.congr_fun (((T.curryLeft p).curryLeft q).curryLeft.map_add x y) (![]); exact hb
         map_smul' c x:=by have hb:= DFunLike.congr_fun (((T.curryLeft p).curryLeft q).curryLeft.map_smul c x) (![]); exact hb }
      map_add' x y:= by apply LinearMap.ext; intro z; have hp:= DFunLike.congr_fun ((T.curryLeft p).curryLeft.map_add x y) (![z]);exact hp
      map_smul' c x:=by apply LinearMap.ext; intro z;have hp:= DFunLike.congr_fun ((T.curryLeft p).curryLeft.map_smul c x) (![z]); exact hp }
   map_add' x y:= by apply LinearMap.ext; intro z; apply LinearMap.ext; intro k; exact DFunLike.congr_fun (map_add T.curryLeft x y) (![z,k])
   map_smul' c x:= by apply LinearMap.ext; intro z; apply LinearMap.ext; intro k; exact DFunLike.congr_fun (map_smul T.curryLeft c x) (![z,k])
end
-- Instead curry explicitly
nonrec def cubicP: TK→ₗ[ℝ](TK→ₗ[ℝ] TK→ₗ[ℝ] ℝ) := ((↑(Nat.factorial 3):ℝ)⁻¹) • with3 (iteratedFDeriv ℝ 3 (tall T) 0)
end YM.OPE.Cascade.Glass
