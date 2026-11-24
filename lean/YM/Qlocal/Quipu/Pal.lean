import YM.Qlocal.Quipu.Arbor
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
abbrev domain {U:Type}(i: Finset U): ↥i→U:= fun x=>x.val
private lemma sees (x y : V→Site f)(P: Bay s) (h:∀ i∈essence s,x i=y i): P.Hears x ↔ P.Hears y:= by unfold Bay.Hears; apply forall_congr'; intro i; apply forall_congr'; intro hi; rw [h i hi,h _ (ownership s)]
abbrev riot (φ: Vase s G k) (p:V→Site S.ratio.count)(x:Site c): Places s c :=family S φ.stage p x
def mass (A:Vase s G k)(n:ℕ)(p:V→Site S.ratio.count)(x: Site c)(U: Config G f)(u: Ker.rule V c) := if ticket S A.stage p x then A.read (zstar S s p x) n U* placard (family S A.stage p x) u else 0
lemma unique3 (B:Bay s): ticket S B p x ↔ Bay.Hears B (drew S (family S B p x) p):= ⟨Arbor.rein S B p x,fun he=>(works S (family S B p x) B p x (by rw [points,pup]) he).1⟩
local notation "V'"=> Ker.rule V c
variable (u: Ker.rule V c)
local notation "h"=> mass S A n p
local notation "Y"=> family S A.stage p x
-- geometric per fixed-phase modal compare. Sum over any `Selected`. no need #clusters.
def street (x:Site c): Prop:= ticket S A.stage p x
lemma provision (P:Prop): (∑ t:Places s c,(if P∧Bay.Hears A.stage (drew S t p) then A.read (Z (t (pivot s))) n W *placard t u else 0)) = ∑ x:Site c, if P then mass S A n p x W u else 0:= by
 by_cases h0:P; swap; · simp [h0]
 let r:Places s c→Site c:= fun t=>t (pivot s); let f(t:Places s c):ℝ := if K[t] then A.read (Z (r t)) n W*placard t u else 0; let Q(x:Site c)(t:Places s c):= if t (pivot s)=x then f t else 0
 simp_rw [h0, true_and,if_true]; suffices hu : (∀ x:Site c,mass S A n p x W u=∑ t:Places s c,Q x t) from (by simp_rw [hu,Q]; rw [Finset.sum_comm]; simp; rfl)
 intro x; unfold mass; let Hp:=ticket S A.stage p x; split
 next hx =>
    symm; rw [Finset.sum_eq_single (family S A.stage p x)]; unfold Q f; rw [pup, if_pos rfl,if_pos (rein S A.stage p x hx),show r _ = _ from (show r (family S A.stage p x)=x from pup S _ p x)]
    · intro t ht h'; unfold Q f; split;
      next hi => apply if_neg; intro hK; exact h' (works S t A.stage p x ((points S t p).trans (congr_arg _ hi)) hK).2
      rfl
    simp
 next hx=> symm; refine Finset.sum_eq_zero fun t _=>?_ ; unfold Q f; split
           next hh=> exact if_neg (fun hK=> hx (works S t A.stage p x ((points S t p).trans (congr_arg _ hh)) hK).1)
           exact rfl
variable [Fintype V]
private lemma ask (u:V') (X: ℝ)(hx:‖u‖≤ X) : ‖placard t u‖ ≤ X^(essence s).card:= by
 unfold placard; rw [norm_prod]; have hm:=prod_le_prod (s:=univ) (fun i _=>norm_nonneg _) (g:=fun _=>X) (fun i _=> (norm_le_pi_norm u (t i,i.val)).trans hx); simpa using hm
variable {P : Album ι s G k} (b:ι→Prop) (hp : Health (a:=a) P C)(ha:0<a)
def village (W:Album ι s G k) (u: Ker.rule V c)(n:ℕ)(U: Config G f) (x:Site c) (i:ι):= if b i then mass S (W i) n p x U u else 0
local notation "M"=> village S p b
include hp ha
lemma market (w:V'): Summable (M P w n W x):= by
 let c:= (1+‖w‖)^ (essence s).card; let f(i):= P i; have hc:0≤c:=by unfold c; positivity
 apply Summable.of_norm_bounded ((hp.2.1.mul_left (Vase.ticketC G n k)).mul_right c); intro i
 unfold village mass; have he:= mul_nonneg (mul_nonneg (Vase.ticketC_pos G n k) (hp.1 i)) hc
 split_ifs <;> first| rw [norm_zero]; exact he | skip
 rw [norm_mul]; exact mul_le_mul (Vase.paid (P i) _ W ha n) (Arbor.ask (family S (P i).stage p x) w _ (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _) (mul_nonneg (Vase.ticketC_pos ..) (hp.1 i))
lemma culmination : (∑ z:Site c,∑' i:ι,M P u n W z i)= ∑ t:Places s c, picture b P (drew S t p) n W *placard t u:= by
 rw [← Summable.tsum_finsetSum (f:=fun i j=>M P u n W i j) (fun i _=>market S p i W b hp ha u)]; -- args order W etc
 have hf (t: Places s c) : Summable fun i=> (P.readout (fun i=> b i∧Bay.Hears (P i).stage (drew S t p)) (Z (t (pivot s))) n i W)*placard t u := (Album.global_sum _ _ _ W n hp ha).mul_right _
 unfold Album.picture realize; simp_rw [points, ← tsum_mul_right]; rw [← Summable.tsum_finsetSum (fun i (_:i∈Finset.univ)=> hf i)]; apply tsum_congr; intro i
 refine Eq.trans (provision S (P i) p W u (n:=n) (b i)).symm ?_
 apply Finset.sum_congr rfl; intro t _; unfold readout; split <;> first| rfl| simp
end YM.Qlocal.Quipu.Sonnet.Arbor
