import YM.OPE.Compatible.Glim.Gum
/-!
# rank: kill equipment.Reading.Coupon

Use charge-filtered shifts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M:Type}{n:Side}
section
variable [Fintype I](p:I)(x y:G.ColorIndex)
local notation "E!"=> Libra.Keys G I
lemma Tara (X:E!): (Mount p ((Phone G) x) false y X).s=(if y=x then 1 else 0) :=by change jet (tou p (Phone G) false _ y) 0 X=_; rw [jet_zero]; unfold tou; rw [Pi.zero_apply,CastSign]; simp 
lemma PryTo (F:ScriptJ E!)(X:E!): (Topper p ((Phone G) x) false F X).s=bat (An p (Phone G) x) (fun X=>(F X).s) X:=by
     unfold Topper Variance.Flux; rw [Finset.sum_apply,show JetS.s (∑ i:G.ColorIndex,_)= ∑ i:G.ColorIndex,(Mount p ((Phone G) x) false i X).s* (Pry (An p (Phone G) i) F X).s from ?_,sum_eq_single x];rotate_left; · intro j _ hj; rw [Tara,if_neg hj,zero_mul]
     · simp
     · exact seqSum _ _ 0
     rw [Tara,if_pos rfl,one_mul];rfl
variable (U:Libra.Keys G I→ℝ)(h:ContDiffAt ℝ ω U 0)(V:Libra.Keys G I)
lemma mute (F:E!→ℝ): bat (An p (Phone G) x) (jet F 0) V=0:=by unfold bat;rw [show jet F 0=(fun _=>F 0) from funext fun x=> jet_zero .., fderiv_const_apply]; rfl -- norm omission check
lemma ridge0 (f g q: ScriptJ E!)(hp:f.B)(hq:g.B): (LoopM p ((Phone G) x) false f g q V).s= (bat (An p (Phone G) x) (fun v=>(f v).s) V +bat (An p (Phone G) x) (fun v=>(g v).s) V) * (q V).s - bat (An p (Phone G) x) (fun v=>(q v).s) V:=by
    unfold LoopM Stamp; rw [plyAdd _ _ _ _ _ hp hq]; change ((Topper p ((Phone G) x) false f V).s + (Topper p ((Phone G) x) false g V).s)*_ + -_ = _; rw [PryTo,PryTo,sub_eq_add_neg]; congr 2; exact PryTo .. -- replace
lemma Duke (F:E!→ℝ)(Y:E!→G.Color)(r:ℕ)(Z:E!→ℝ) : (Cake p false F Z Y r V).s= ∑ i:G.ColorIndex, let v:= An p (Phone G) i; let f:E!→ℝ:=(Phone G).coord i∘Y; bat v (jet F 2) V * jet f r V - bat v (jet f r) V:=by
     unfold Cake; rw [Finset.sum_apply]; let m(i:G.ColorIndex):= LoopM p ((Phone G) i) false (Pawn.mold F 2) (Pawn.mold Z 0) (Pawn.mold ((Phone G).coord i ∘ Y) r); change (∑ i,m i V).s=_; rw [show (∑ i,m i V).s=∑ i,(m i V).s from ?_]; swap; · exact seqSum _ _ 0
     apply sum_congr rfl; intro i _; unfold m; rw [ridge0 _ _ _ _ _ _ (tallJ _ _) (tallJ _ _), mute,add_zero]
end
end YM.OPE.Variance
