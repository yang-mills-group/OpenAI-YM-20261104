import YM.LocalTaylorR2.Reel.Lantern
import YM.LocalTaylorR2.Reel.Trust
import YM.LocalTaylorR2.Capstone.Routine
/-!
 # Lives for recalculating each step's inheritance error on its line
 Explicit scale/Submodule pay reaching output E.Rep (not just exists representatives).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Set Lattice Wilson RG Ovens UVNext.PricedKernels Progress.DirectedRecipe Extra.Iteration Push.AbsoluteSums
open Pressure ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Height
open Push.SectorMeasure
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup Averaging Geo Rack
open Capstone
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{b:Side}{O:Listing G b}{P:BudgetPoint}{k:Clip}(W:PathData G)(t:ℝ)
variable {x y z:Collection.Source G b}
lemma hess_scale {A:Support b}{f:Config G b→ℝ}(h:P.Regular A f)(u v:Directions G b): logHessian (t • f) u v=t*logHessian f u v:=by
   change (iteratedFDeriv ℝ 2 (t • (f ∘ increment 1)) 0) _=_; rw [iteratedFDeriv_const_smul_apply]; rfl; exact germ_diff h
lemma prj_scale {d:RegularAddress b}{f:Config G b→ℝ}(h:P.Regular d.support f)(i j:PlaqAxes) : projection d (t • f) i j=t*projection d f i j:=by unfold projection; split; exact hess_scale t h ..; exact (mul_zero _).symm
lemma bank {J q:ℝ} (hx:Collection.Local O P x J q) (hv:y.logRead=t • x.logRead): delta (O.read y)= t*delta (O.read x):=by
   unfold Averaging.delta Averaging.total; rw [← tsum_mul_left]; apply tsum_congr; intro i; unfold censusAt Listing.read; dsimp only []; rw [hv]; split; exact prj_scale t (hx.smooth i) ..; exact (mul_zero _).symm
lemma rebate_scale {A:RegularAddress b}{f:Config G b→ℝ}(h:P.Regular A.support f): Residual.rebate A (t • f)= t • Residual.rebate A f:= by
   have he: payout A (t • f)=t • payout A f:=by
      ext U; simp_rw [payout,counter, quad,prj_scale t h,mul_assoc]; simp only [← Finset.mul_sum,Pi.smul_apply,smul_eq_mul,counter,quad]; ring
   unfold Residual.rebate; rw [he]; ext; simp; ring
-- linear on the already-mapped E lanes. Choose arbitrary hard for Local incomes.
lemma proportional {J q:ℝ} (hx:Collection.Local O P x J q) (hv:y.logRead=t • x.logRead): (branch O W k P y 0).regular=t • (branch O W k P x 0).regular:= by
   have hb:= Reel.bank t hx hv
   have hf (i:EKey b): archive O W k y 0 (delta (O.read y)) i= t • (archive O W k x 0 (delta (O.read x)) i):=by -- beta annotate
      rcases i with i|⟨b,d⟩|⟨b,d⟩
      · unfold archive; rw [hv]; exact rebate_scale t (hx.smooth i)
      · unfold archive; dsimp only [Sum.elim]; rw [hb]; unfold Low.fresh; ext V; simp; ring
      unfold archive; dsimp only [Sum.elim]; rw [hb]; unfold High.fresh; ext V; simp; ring
   exact funext fun i=> hf (numbering _ i)
lemma intoSize (Z:Pipes G b) {u v:Tap G b}(he:u.regular=t • v.regular): Capstone.drawn Z u=t • (Capstone.drawn Z v):=by
   ext1 i
   unfold Capstone.drawn; rw [he,Pi.smul_apply]; by_cases h:i∈Set.range (upE Z)
   · obtain ⟨i,rfl⟩:=h; rw [stuffed,stuffed]; rfl
   rw [blank _ _ h,blank _ _ h,smul_zero]

def carver (O : Listing G b)(x:Collection.Source G b)(a':ℝ)(B:BudgetPoint)(K:Clip):Scroll G b:= Capstone.drawn (Collection.shelves O W B) (branch O W K B x a')
variable {Z u v e a:ℝ} {A B:Collection.Source G b} (h:Collection.Local O P A Z u)(hb:Collection.Local O P B v u)
include h hb
lemma carverAdd (hc: A.hardRead=B.hardRead)(hy:A.logRead=B.logRead+x.logRead)(he:A.hardRead=x.hardRead)(a:ℝ)(hG:G.Simple): carver W O A a P k-carver W O B a P k=carver W O x 0 P k:= by
  rw [sub_eq_iff_eq_add']; unfold carver; rw [Capstone.pouring_reg _ _ (Recoil.painted h hG a hb hy hc he).reg]; -- orientation
lemma carverSub (hc : x.hardRead=A.hardRead)(_hx : B.hardRead=A.hardRead)(hy: Collection.Local O P x e u)(ht: x.logRead=A.logRead - t • B.logRead)(hG:G.Simple):
    carver W O x a P k=carver W O A a P k - t • carver W O B 0 P k:= by
  let V:Collection.Source G b:={ A with logRead:=t • B.logRead}
  have he: A.logRead=x.logRead+V.logRead:=by rw [ht]; exact (sub_add_cancel ..).symm
  have hV : A.hardRead=V.hardRead:=rfl
  have hr : carver W O A a P k - carver W O x a P k=carver W O V 0 P k:= carverAdd W h hy hc.symm he hV a hG -- maybe t implicit
  have hg : carver W O V 0 P k=t • carver W O B 0 P k:= intoSize t _ (proportional W t hb rfl)
  rw [hg] at hr; rw [← hr]; abel
end YM.LocalTaylorR2.Reel
