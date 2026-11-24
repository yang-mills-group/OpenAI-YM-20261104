import YM.Frontier6.Bouquet.Anise.Maison

/-! The linear Taylor reader at parent arity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q R:Place}[FiniteDimensional ℝ P][FiniteDimensional ℝ Q] (h:P≤Q)(f: Full Q)
variable (s:ℝ)(d:ℕ)
set_option quotPrecheck false
local notation "M"=> Loft Q P
def page : Full Q→ₗ[ℂ] Full Q:=∑ i:Fin (d+1),∑ a:Kin P i, (readCenter h (a.event s)) ∘ₗ (train Q a.phrase)
def escape : Full Q→ₗ[ℂ] Full Q:=LinearMap.id-page h s d
lemma paging : page h s d f=∑ i:Fin (d+1),∑ a:Kin P i, readCenter h (a.event s) (train Q a.phrase f):= by unfold page; simp_rw [LinearMap.sum_apply, LinearMap.comp_apply]
lemma train_ride_swap (p:Multiset Room)(u:Room) : train Q p (ride Q u f) = ride Q u (train Q p f):=by
    rw [← train_one u f, ← train_one u (train Q p f), ←trains_add,←trains_add,add_comm p]
lemma pages_mobile : Mobile (page h s d) M:=by intro x hx f; rw [paging,paging]; simp_rw [map_sum,train_ride_swap]; congr 1; apply funext; intro a; refine Finset.sum_congr rfl fun i _=> Mobile.center h (i.event s) x hx (train Q i.phrase f) -- congr type?
lemma pages_out : Mobile (escape h s d) M:= by intro x hx f; change ride Q x f -page h s d _=ride Q x (f-_); rw [pages_mobile h s d x hx,map_sub]
lemma mechanism (z:M): atLoft h z (page h s d f)= portion s d (atLoft h z f):= by
    rw [paging,portion_series]; simp_rw [map_sum]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun a _=>?_)); rw [specialization]; unfold series; congr 2; exact train_restricted h _ f _ a.phrase_in -- atLoft
lemma mechanism_out (z:M): atLoft h z (escape h s d f)= leftOut s d (atLoft h z f):= by change atLoft _ _ (f-page _ _ _ _)= _; rw [map_sub,mechanism];rfl
lemma sky_support (hs:0<s): tsupport (page h s d f)⊆ (floorOf P Q ⁻¹' Metric.closedBall (0:P) (2*s)) ∩ (centerless h ⁻¹' tsupport f):=by
   let S:=(floorOf P Q ⁻¹' Metric.closedBall (0:P) (2*s)) ∩ (centerless h ⁻¹' tsupport f)
   have he:IsClosed S:= (isClosed_closedBall.preimage (floorOf P Q).continuous).inter ((isClosed_tsupport _).preimage (centerless h).continuous) -- name
   refine closure_minimal (t:=S) ?_ he; intro x hx
   by_contra h'
   apply hx; suffices hX: ∀ (i: Fin (d+1))(a:Kin P i),readCenter h (a.event s) (train Q a.phrase f) x=0 by rw [paging]; simp [hX]
   intro i a; apply image_eq_zero_of_notMem_tsupport; exact fun hw=> ((h':x∉S) ⟨a.event_size hs ((center_support h _ _) hw).1,train_support a.phrase f ((center_support h _ _) hw).2⟩)
-- data economy later.
end YM.Frontier6.Bouquet
