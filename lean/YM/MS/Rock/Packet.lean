import YM.MS.Rock.Exchange
/-!
# Closed arithmetic of supports, beam linear

Knot and Form0 are supporting spaces (subspaces). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Path Landau Arts Pilot Spin Arc Wire
open Metric
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{F H:Mob G}{U V:Rip G}
namespace Form0
lemma add (h: Form0 b F)(hv:Form0 b H): Form0 b (F+H):= ⟨fall_add h.price hv.price,Sturdy_plus h.token hv.token⟩
lemma smul (h:Form0 b F)(x:ℂ): Form0 b (x • F):= ⟨by convert fall_scale (U:=fun _:Unit=>x) h.price (const_sc ..) using 1; ext; simp,Sturdy_scale h.token x⟩
lemma neg (h: Form0 b F): Form0 b (-F):= by simpa using h.smul (-1)
lemma sub (h:Form0 b F)(hv:Form0 b H): Form0 b (F-H):= by rw [sub_eq_add_neg]; exact h.add hv.neg
lemma zero : Form0 b (0: Mob G):= ⟨fall_zero (fun _=>zero_le_one),Sturdy0⟩
lemma portQ (Q:Shade G)(he:CountsD b Q)(h:Form0 b F)(hr: Priced Q): Form0 b (portZ Q F):= ⟨count_price Q hr h.price, zMotion h.token he⟩
lemma treed (h:Knot b U)(ht: closedF U c)(hv:reverseF U)(hF:Form0 b F)(hH:Form0 b H) : Form0 b (arbor U F H):= ⟨by
   convert! for_tree hF.price hH.price (u:=fun _:Unit=>U) (fun m p q=>railto (h.price m p q)) (fun _=>zero_le_one) using 1; simp, arboreal hF.token hH.token h.token hv ht⟩
lemma clearer (h: Form0 true F): Form0 false F:= ⟨h.price,⟨fun n K _=> h.token.turn n K (fun p=> Bool.noConfusion p),fun p=> h.token.grows p⟩⟩ -- prefix args ordering
end Form0
lemma Ruddy_pl (h:Ruddy b U)(he:Ruddy b V): Ruddy b (U+V):= by
   refine ⟨fun i K hK=> ?_,fun h' i j p=>?_⟩; · intro p a b; simp only [Pi.add_apply, (h.turn i K hK) p, (he.turn i K hK) p,add_mul, Finset.sum_add_distrib];
   simp only [Pi.add_apply,h.grows h',he.grows h']
lemma Ruddy_m {p:ℂ} (h:Ruddy b U): Ruddy b (p • U):= by
   refine ⟨fun i K hk=>?_,fun he i j z=>?_⟩; · intro q a b; simp only [Pi.smul_apply, (h.turn i K hk) q,smul_eq_mul,mul_assoc,Finset.mul_sum]
   simp only [Pi.smul_apply,h.grows he]
namespace Knot
lemma zero : Knot b (0:Rip G):= ⟨fun i a b j=>Costs.zero (fun x p hp=>show (0:ℝ)≤1 / (1+1*‖p‖)^j by positivity),⟨fun i K hk=>by intro q a b; simp, fun _ _ _ _=>rfl⟩⟩ -- `fun ..`
lemma add (h: Knot b U)(he:Knot b V): Knot b (U+V):= ⟨fun i a b j=> (h.price i a b j).add (he.price i a b j),Ruddy_pl h.token he.token⟩
lemma smul (h: Knot b U)(c:ℂ): Knot b (c • U):= ⟨fun i a b j=> (h.price i a b j).L (ContinuousLinearMap.mul ℝ ℂ c), Ruddy_m h.token⟩
lemma neg (h: Knot b U): Knot b (-U):= by simpa using h.smul (-1)
lemma sub (h:Knot b U)(hv:Knot b V): Knot b (U-V):= by rw [sub_eq_add_neg]; exact h.add hv.neg
lemma clearer (h:Knot true U): Knot false U:= ⟨h.price,⟨fun i K _=> h.token.turn i K (fun p=>Bool.noConfusion p),fun h' a b p=> h.token.grows h' a b p⟩ ⟩
end Knot
end YM.MS.Rock
