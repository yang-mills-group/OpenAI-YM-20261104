import YM.Qlocal.Quipu.Pal
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Arbor
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c f:Side} {S:StepData c f}{d t a v u C:ℝ}{R:Census V}
open Album Lagger Binding Turbin Primitives.TwoWave Primitives.TwoWave.RealSlice AllOrder.Ker Lasso
variable (S) {s:Senses R} (A: Vase s G k)(t:Places s c) (p:V→Site S.ratio.count)(x: Site c) (W : Config G f)
local notation "Z"=> zstar S s p
set_option quotPrecheck false
local notation "K[" T "]"=> (A.stage.Hears (drew S T p))
local notation "V'"=> Ker.rule V c
variable (u: Ker.rule V c)
lemma promotion (P:Prop): (∑ t:Places s c,(if t (pivot s)=x then (if P∧Bay.Hears A.stage (drew S t p) then A.read (Z (t (pivot s))) n W *placard t u else 0) else (0:ℝ))) = if P then mass S A n p x W u else 0:= by
 by_cases h0:P; swap; · simp [h0]
 let r:Places s c→Site c:= fun t=>t (pivot s); let f(t:Places s c):ℝ := if K[t] then A.read (Z (r t)) n W*placard t u else 0; let Q(x:Site c)(t:Places s c):= if t (pivot s)=x then f t else 0
 simp_rw [h0, true_and,if_true]; symm; unfold mass; let Hp:=ticket S A.stage p x; split
 next hx =>
    symm; change (∑ t:Places s c,Q x t)= _; rw [Finset.sum_eq_single (family S A.stage p x)]; unfold Q f; rw [pup, if_pos rfl,if_pos (rein S A.stage p x hx),show r _ = _ from (show r (family S A.stage p x)=x from pup S _ p x)]
    · intro t ht h'; unfold Q f; split;
      next hi => apply if_neg; intro hK; exact h' (works S t A.stage p x ((points S t p).trans (congr_arg _ hi)) hK).2
      rfl
    simp
 next hx=> symm; change (∑ t:Places s c,Q x t)= _; refine Finset.sum_eq_zero fun t _=>?_ ; unfold Q f; split
           next hh=> exact if_neg (fun hK=> hx (works S t A.stage p x ((points S t p).trans (congr_arg _ hh)) hK).1)
           exact rfl
variable [Fintype V]{P : Album ι s G k}(b:ι→Prop) (hp : Health (a:=a) P C)(ha:0<a)
include hp ha
lemma sector : (∑' i:ι,village S p b P u n W x i) = ∑ t:Places s c, if t (pivot s)=x then picture b P (drew S t p) n W *placard t u else 0:= by
 let Q(t:Places s c)(i:ι):= if t (pivot s)=x then (P.readout (fun i=> b i∧Bay.Hears (P i).stage (drew S t p)) (Z (t (pivot s))) n i W)*placard t u else 0
 have hf(t:Places s c) : Summable (Q t):= by
    unfold Q; split; rename_i hz; · exact (Album.global_sum _ _ _ W n hp ha).mul_right _
    exact summable_zero
 have he(t:Places s c): (if t (pivot s)=x then picture b P (drew S t p) n W *placard t u else 0)= ∑' i,Q t i:= by
    unfold Q; split; rename_i hz; · unfold picture realize; rw [points,← tsum_mul_right]
    exact tsum_zero.symm
 simp_rw [he]; rw [← Summable.tsum_finsetSum (f:=Q) (fun t (_:t∈Finset.univ)=> hf t)]; apply tsum_congr; intro i
 refine Eq.trans (promotion S (P i) p x W u (b i)).symm ?_; apply Finset.sum_congr rfl; intro t ht; unfold Q; split; rename_i h; · unfold readout; split; rfl; simp
 rfl
end YM.Qlocal.Quipu.Sonnet.Arbor
