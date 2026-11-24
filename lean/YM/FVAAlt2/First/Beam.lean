import YM.FVAAlt2.First.Front
import YM.RG11Scheme.Bell.Winds
/-! Jet of the wave kernel evaluated on linear leading letter on cover, shifted from each
edge midpoint to its starting location. This common analytic phase unwrapping for the first
nonvanishing Taylor degree only. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native MS.Book MS.Plane MS.Theater MS.Landau MS.Landau.Detect MS.Lifting
open Pert Pert.Orb MS.Cylinder.Lab
open RG11Scheme (Mesh.row Stencil.gradient)
open RG11Scheme.Bell
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius
open Complex (I)
variable {G:Gauge}{n:Side}(p:Key G)
set_option maxRecDepth 8000
local notation "Ω"=> Lane4 G
set_option quotPrecheck false
local notation "D"=> Pert.Bare.wideLinear G p.1 1 (0:Cover)
def dots (G:Gauge)(j:ℕ): Feet G j →ₗ[ℝ] Lattice.Links ℤ G.Color where
 toFun Y l:= Tensor.diagonal (Y.val l.2) (RG11Scheme.Mesh.row l.1)
 map_add' _ _:=rfl
 map_smul' _ _:= rfl
lemma dots_small (j:ℕ) (hv:j≤p.1)(X:Feet G j): wh p (dots G j X)=0:=by
 have ht: RG11Scheme.Bell.Polar (dots G j X) p.1:=fun i=> hills hv (traces_grade (X.val i))
 rw [wh,LinearMap.comp_apply,blank_core _ ht, map_zero]
lemma dots_step {j:ℕ}(X:Labels.Taylor G j) : Pert.Bare.wideLinear G j 1 (0:Cover) (dots G (j+1) (step_in G j X))=X := by rw [show dots G (j+1) (step_in G j X)= RG11Scheme.Bell.brighten X from funext fun _=> rfl]; obtain he:= radar X 1; rw [_root_.one_zpow,one_smul] at he; with_reducible exact he
open RG11Scheme
lemma grade_lane {j:ℕ}(Z:Head G (j+2)) : Polar (-Stencil.gradient (traces (Z.val ())) - dots G (j+1) (Theater.gradS G (j+1) Z)) j := by
 let n:=j+1; let T:= Z.val (); intro i
 have he:= (own (P:=T) (Z.property ())).different i
 have hb (y:Cover) : -(Stencil.gradient (traces T) (y,i))= Mesh.go [i] (traces T) y:= neg_sub ..
 have ht: ∀ x:Cover,Bell.traces ( Bell.prime i T ) x= Bell.traces (( gradS G n Z ).val i) x:=by unfold traces Bell.prime; change ∀ x, Tensor.diagonal ((↑(n+1:ℕ):ℝ) • _ ) _ = Tensor.diagonal (( (n:ℝ)+1) • _ ) _; norm_cast; exact fun _=>rfl
 rw [show RG11Scheme.Bell.findout _ i= Mesh.go [i] (traces T) - traces ( Bell.prime i T ) from ?_]; exact he.subtract
 funext y; change -(Stencil.gradient (traces T) (y,i))-traces _ y=_; rw [hb y,← ht y];rfl
lemma sake(Z:Head G (p.1+2)): wh p (-Stencil.gradient (traces (Z.val ())) - dots G (p.1+1) (gradS G (p.1+1) Z))=0:=by rw [wh,LinearMap.comp_apply,blank_core _ (grade_lane Z),map_zero]
lemma shake(X:Cover→G.Color): wh p (Stencil.gradient X)=0:= by
 rw [wh,LinearMap.comp_apply,show Stencil.gradient X=Stencil.Spark.tremor X from rfl]
 rw [Stencil.Cell.shadow,map_zero]
lemma served {A:Type*}[AddCommGroup A][Module ℝ A] (w:A→ₗ[ℝ] ℝ) (u v:A)(hu:w (-u-v)=0)(hx:w u=0): w v=0:=by rw [map_sub,map_neg,hx,neg_zero,zero_sub,neg_eq_zero] at hu; exact hu
lemma pension(Z:Head G (p.1+2)): wh p (dots G (p.1+1) (gradS G (p.1+1) Z))=0:= by
 refine served (A:=Lattice.Links ℤ G.Color) (u:=Stencil.gradient (traces (Z.val ()))) (w:=wh p) _ ?_ ?_
 · apply sake
 exact shake p _
lemma dots_wide(X:Feet G (p.1+1)): wh p (dots G (p.1+1) X)=(Labels.axes G p.1).coord p.2 (Theater.yard G p.1 X) :=by
 have h : ∀ V:Labels.Taylor G p.1, wh p (dots G (p.1+1) (step_in G p.1 V))=(Labels.axes G p.1).coord p.2 V:=fun V=>by rw [wh,LinearMap.comp_apply,dots_step]
 rw [ ← h, taxiY,carveΩ,map_sub,map_smul, map_sub,map_smul,pension,smul_zero,sub_zero]
end YM.FVAAlt2.Pairing
