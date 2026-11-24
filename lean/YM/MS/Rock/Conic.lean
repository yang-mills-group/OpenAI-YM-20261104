import YM.MS.Rock.Synch
/-!
# Arbor and Counts operators in analytic grammar

Standard lines likely reverse but allow general `attaches p..`. Heat support on all family arguments. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Landau Arts Pilot Spin Arc Wire Path
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I A E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
   {b c:Bool}{m:ℕ}{z:UScale I}
variable {a d r:I→ℝ} {f h:I→Mob G}{u:I→ Rip G}
lemma for_tree (hf:fell z a f)(ht:fell z d h)(hu:∀ i j l,veg z (fun x=> (u x i) j l) r)(hz:∀ i,0≤ r i) : fell z (fun i=>r i*(a i*d i)) fun i=>arbor (u i) (f i) (h i):= by
    intro m E _ _ _ w; let X(i:I):=r i*(a i*d i); unfold fieldVal arbor; simp only [tree,sail_scatter,attaches,sail_net,sail_degree];
    refine gather_bound w (fun U V H=> ?_); let W:=net U; have hw : ((Arc.path z).full (E:=E)).NN (fun i p=> X i):=fun i p hp=> mul_nonneg (hz i) (mul_nonneg (znon hf i) (znon ht i))
    have h0 (j:Cfield G m)(k:ℂ): veg z (fun i x=> k * f i m ((j,-W x)::sail U x)) a:= ((hf m E ((j,-W)::U)).L (ContinuousLinearMap.mul ℝ ℂ k)) -- shorthand
    have hx (j:Cfield G m): veg z (fun i x=>h i m ((j,- -W x)::sail V x)) d:= by simp only [neg_neg]; exact ht m E ((j,W)::V)
    refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=> Costs.add ?_ ?_) hw) hw;
    · exact (Bound.linear (-W) (hu m i j)).mul ((h0 i _).mul (hx j))
    exact (Bound.linear (- -W) (hu m i j)).mul ((h0 j _).mul (hx i))
-- `Mot` line morph structure over cont + table costs for reuse
structure Priced (K: Shade G): Prop where
   solid n i j: veg 0 (fun _:Unit=> (K n).table i j) 1

lemma count_price (Q:Shade G)(hQ:Priced Q)(hf:fell z a f): fell z a (fun i=> portZ Q (f i)):= by
    intro m E _ _ _ w; let X:=(Q m); unfold portZ;  unfold fieldVal; simp_rw [visit_Z,visit_sail];
    refine visit_bound (znon hf) (fun l i k h=>?_); refine Costs.sum _ (fun c hc=>?_) (fun i _ _=> znon hf i); obtain H:= hf m E (l++(c,i.2)::k); convert! Costs.mul (Bound.linear i.2 (around (hQ.solid m i.1 c))) H using 1; funext i x; simp only [fieldVal, sail_join,sail_cons]; ext; simp
-- analytic pure tree geometry
end YM.MS.Rock
