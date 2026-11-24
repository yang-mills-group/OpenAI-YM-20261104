import YM.XSpace.Cart
/-! # Strong point outputs include compactness and continuity -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cirrus
open Filter Set Function Metric Lattice
open scoped Topology BigOperators Classical
variable {n:ℕ}{F T ι:Type*}[PseudoMetricSpace T] {X:Sample n→ T}{f:Points n→T}{V K : Set (Points n)}
def Senses (V:Set (Points n))(X:Sample n→T)(f:Points n→T) := ∀ x∈V,Tendsto X (Gate x) (𝓝 (f x))
lemma Senses.mon (S:Senses V X f)(hx:K⊆V): Senses K X f:=fun x hx'=> S x (hx hx')
variable (h:Senses V X f)
include h in
lemma sensesU (x:Points n)(hx:x∈V) (e:ℝ)(he:0<e):∃ r:ℝ,0<r ∧ ∀ᶠ m in Front,∀ p:pack n, ∀ c∈m.Box,dist (m.rel p c) x<r → dist (X ⟨m,p,c⟩) (f x)<e:= gate_senses x ((Metric.tendsto_nhds.mp (h x hx)) e he)
include h in
lemma senses_price (x:Points n)(r:ℝ)(H:0<r)(ε:ℝ)(hp:∀ᶠ m in Front,∀ p:pack n,∀ c∈m.Box,dist (m.rel p c) x<r→ dist (X ⟨m,p,c⟩) (f x)<ε)(y:Points n)(hy:y∈V)(hv:dist y x<r): dist (f y) (f x) ≤ ε:=by
  apply le_of_tendsto ((h y hy).dist (tendsto_const_nhds (x:=f x))); filter_upwards [senseG y |>.eventually (isOpen_ball.mem_nhds hv), (liftG y).eventually hp,welcomeG y] with i hi hp hy; exact (hp i.layout i.center hy hi).le
include h in
lemma Senses.priced : ContinuousOn f V:=by
  rw [Metric.continuousOn_iff]; intro x hx e he; obtain ⟨r,hr,ht⟩:= sensesU h x hx (e/2) (by positivity); exact ⟨r,hr,fun _ hY hv=>(senses_price h x r hr (e/2) ht _ hY hv).trans_lt (half_lt_self he)⟩
def Accurate (K:Set (Points n)) (X:Sample n→ T) (f:Points n→ T):= ∀ (ε:ℝ),0<ε→∀ᶠ p in Front,∀ i:Sample n,grab i=p→welcome i→familiar i∈K→dist (X i) (f (familiar i))≤ε

lemma Senses.placed (h:Senses V X f) (H:IsCompact K)(hx:K⊆V): Accurate K X f:=by
  intro ε he; choose R hR H₀ using fun i:K=> sensesU h i.val (hx i.property) (ε/2) (by positivity)
  let B (i:K):= ball i.val (R i); obtain ⟨u,hu⟩:= H.elim_finite_subcover B (fun _=>isOpen_ball) (fun i hi=>mem_iUnion.mpr ⟨⟨i,hi⟩,mem_ball_self (hR _)⟩)
  filter_upwards [(eventually_all_finset u).mpr (fun i _=>H₀ i)] with p hp i hi hw hy; obtain ⟨j,hj⟩:= mem_iUnion.mp (hu hy); obtain ⟨ht,hb⟩:= mem_iUnion.mp hj; apply le_trans (dist_triangle _ (f j.val) _); rw [dist_comm (f j.val),← add_halves ε]; apply add_le_add _ (senses_price h j.val _ (hR j) _ (H₀ j) _ (hx hy) hb); subst p; exact (hp j ht _ _ hw hb).le
end YM.XSpace.Cirrus
