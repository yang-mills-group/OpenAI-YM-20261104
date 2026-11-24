import YM.X.Charting.Sell
import YM.Push.STRESS_FLUX.Color
/-!
## Antisymmetric cubic color stencil at one plaquette. No sum terms in `trinity` use repeated colors. Retained as triples with 2 edge scans & one curvature scan. Provides weight at least four in native jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Stems
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Jet Log MvPolynomial Next.Rank.Normal Finset
open Gauge LatticePT
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}
local notation "C₁"=> G.ColorIndex
local notation "P"=> Curly G
local notation "X₀"=> MvPolynomial.X -- syntax binder hides type letters
-- inner color

def tan (x:C₁):= EuclideanSpace.basisFun G.ColorIndex ℝ x
def iv (k i j:C₁):ℝ:= Inner.inner ℝ (tan k) (Log.shift (tan i) (tan j))
lemma skip_tan (k i j:C₁) (h:¬ (k ≠ i ∧ i≠ j ∧ j≠ k)): iv k i j=0:= by
   have ht (x y:C₁):Inner.inner ℝ (tan y) (Log.shift (tan x) (tan y))=0:= by
      have h:= ad_skew (tan x) (tan y) (tan y); rw [real_inner_comm (G.ad _ _)] at h; unfold Log.shift; rw [real_inner_smul_right]; have h':= real_inner_comm (tan y) (G.ad (tan x) (tan y)); linarith only [h,h']
   have he : k=i ∨ i=j ∨ j=k:= by tauto
   rcases he with rfl|rfl|rfl
   · unfold iv; rw [shift_skew (tan k),inner_neg_right, ht,neg_zero] -- direction? variables
   · unfold iv; have he : Log.shift (tan i) (tan i)=0:= by unfold Log.shift; rw [show G.ad (tan i) (tan i)=0 from G.colorMat_injective (by simp), smul_zero]
     rw [he]; simp
   exact ht _ _
lemma restore_tan (x:G.Color): x=∑ i:C₁,x i • tan i:= by exact Eq.symm ((EuclideanSpace.basisFun _ ℝ).sum_repr ..)
lemma kick (A B C:G.Color): Inner.inner ℝ A (Log.shift B C) =∑ k:C₁, ∑ i:C₁, ∑ j:C₁,iv k i j * A k * B i * C j:= by
   conv_lhs=> rw [restore_tan A,restore_tan B,restore_tan C]
   unfold iv Log.shift; simp only [_root_.map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,sum_inner,inner_sum,Finset.smul_sum,real_inner_smul_right,real_inner_smul_left]; conv_lhs=> rw [Finset.sum_comm]
   conv_rhs=> rw [Finset.sum_comm]
   apply Finset.sum_congr rfl; intro k _; rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

def faceText (p:PlaqAxes)(k:C₁):= blade (arc k 0 p.val.1 p.val.2)
def shiftProduct (p:PlaqAxes)(i j:C₁):P:= by
   let a: Pin:=(0,p.val.1); let b:Pin:=(step p.val.1,p.val.2); let c:Pin:=(step p.val.2,p.val.1); let d:Pin:=(0,p.val.2)
   exact (X₀ (a,i)*X₀ (b,j)- (X₀ (a,i)+X₀ (b,i))*X₀ (c,j)-(X₀ (a,i)+X₀ (b,i)-X₀ (c,i))*X₀ (d,j))
lemma fired_top (p:PlaqAxes)(x:Brush G): snap x (vertex p) = (↑(Inner.inner ℝ (curl x 0 p.val.1 p.val.2) (fire x 0 p.val.1 p.val.2)):ℂ):= by rw [vertex, mark_test,Log.flame_root (i:=3) _ _ (by omega),if_neg (by decide),if_pos rfl]
lemma trinity (p:PlaqAxes): vertex p=∑ k:C₁, ∑ i:C₁,∑ j:C₁, (iv k i j:ℂ) • (faceText p k * shiftProduct p i j) := by
   apply snap_ext; intro x; rw [fired_top]; simp_rw [_root_.map_sum,_root_.map_smul,map_mul,faceText,snaps_blade,arc_eq]
   unfold fire Log.sub; simp_rw [inner_add_right,kick,PiLp.neg_apply,←Finset.sum_add_distrib]; rw [Complex.ofReal_sum]; simp_rw [Complex.ofReal_sum]
   apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; unfold shiftProduct snap; simp only [map_mul,map_sub,map_add,aeval_X, text, smul_eq_mul,PiLp.add_apply,PiLp.sub_apply]; push_cast; simp only [zero_add]; ring
end YM.PositionX.Stems
