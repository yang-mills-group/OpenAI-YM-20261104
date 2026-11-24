import YM.Frontier6.Bouquet.Anise.Carousel

/-! Commuting the disjoint derivatives for use on test-only operators -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q:Place}[FiniteDimensional ℝ P][FiniteDimensional ℝ Q] (h:P≤ Q)(u:P → ℂ)(hg:Smooth u)
set_option quotPrecheck false
local notation "M" => Loft Q P
section
variable {X Y:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
theorem Dproduces (v:X)(f g:X→ ℂ)(hf:Differentiable ℝ f)(hg:Differentiable ℝ g) : Analysis.D v (f*g)= f*Analysis.D v g + g*Analysis.D v f:= by ext1 x; unfold Analysis.D; rw [fderiv_mul (hf x) (hg x)];rfl
lemma D_at (v:X)(f:Y→ℂ)(hv:Differentiable ℝ f)(g:X→L[ℝ] Y): Analysis.D v (f ∘ g)=(Analysis.D (g v) f) ∘ g:=by ext1 x; unfold Analysis.D; rw [fderiv_comp _ (hv _) g.differentiableAt, (g.hasFDerivAt).fderiv];rfl
lemma Dzero (f:X→ℂ): Analysis.D 0 f=0:=funext fun i=>map_zero _
end
variable (A: Full Q →ₗ[ℂ] Full Q)
def Mobile (U:Place):Prop:=∀ x∈U,∀ f:Full Q,A (ride Q x f)=ride Q x (A f)
lemma ride_cast (f:Full Q)(v:M): (ride Q v.val f : Q→ℂ)=Analysis.D (insideCL loft_le v) f:=by
   unfold ride; rw [step_cast,show ontoSpace Q v.val=insideCL loft_le v from on_home (insideCL loft_le v)] -- underscore
include h
set_option maxHeartbeats 600000 in
lemma Mobile.pane : Mobile (paneM (Q:=Q) u hg) (Loft Q P):=by
   intro v hv f; let w : M:=⟨v,hv⟩; let V:Q:= insideCL loft_le w; ext1 i
   -- cast to w
   change (u ∘ floorOf P Q) i * ride Q w.val f i= ride Q w.val (paneM u hg f) i
   rw [ride_cast (P:=P),ride_cast (P:=P), show (paneM u hg f: Q→ℂ)= (u ∘ floorOf P Q)*f from rfl]
   rw [Dproduces _ _ _ (hg.differentiable (by simp)|>.comp (floorOf P Q).differentiable) (f.contDiff.differentiable (by simp)), D_at _ u (hg.differentiable (by simp)),(attendance h).of_right, Dzero u, show (0:P→ℂ) ∘ floorOf P Q=(0: Q→ℂ) from rfl,mul_zero,add_zero];rfl -- syntax
set_option maxHeartbeats 600000 in
lemma Mobile.center (g:Full P): Mobile (readCenter h g) M:=by
   intro v hv f; let w : M:=⟨v,hv⟩; let V:Q:= insideCL loft_le w; ext1 i
   change (g ∘ floorOf P Q) i * ride Q w.val f (centerless h i)= ride Q w.val (readCenter h g f) i
   have hu:= g.contDiff.differentiable (show (∞:WithTop ℕ∞)≠0 by simp); have hh:= f.contDiff.differentiable (show (∞:WithTop ℕ∞)≠0 by simp)
   rw [ride_cast (P:=P), ride_cast (P:=P), show (readCenter h g f:Q→ℂ)= (g ∘ floorOf P Q)*(f ∘ centerless h) from rfl]
   rw [Dproduces _ _ _ (hu.comp (floorOf P Q).differentiable) (hh.comp (centerless h).differentiable), D_at _ (g:P→ℂ) hu,(attendance h).of_right,Dzero g, show (0:P→ℂ)∘floorOf P Q=(0:Q→ℂ) from rfl,mul_zero,add_zero,D_at _ (f:Q→ℂ) hh,centerless_paths];rfl
omit h
lemma train_one (x:Room)(f:Full Q): train Q ({x}:Multiset Room) f=ride Q x f:=by rw [show ({x}:Multiset Room)=([x]:List Room) from rfl, train_list];rfl
lemma Mobile.train_paths (u:Multiset Room)(hg: Mobile A M)(he:∀ x∈ u,x∈M)(f:Full Q): train Q u (A f)= A (train Q u f):=by
   induction u using Multiset.induction_on generalizing f with
   | empty=> rw [trains_zero,trains_zero]
   | cons x u ih=>
       have ht:= ih (fun v hv=> he _ (Multiset.mem_cons_of_mem hv)) f
       have hk(g:Full Q): train Q (x ::ₘ u) g=ride Q x (train Q u g):=by rw [← Multiset.singleton_add]; exact (trains_add _ _ _).trans (train_one x _)
       exact (hk (A f)).trans ((congr_arg (ride Q x) ht).trans ((hg x (he _ (by simp)) _).symm.trans (congr_arg A (hk f).symm)))
lemma Mobile.pedals (u:List Room)(hg:Mobile A M)(he:∀ x∈u,x∈ M)(f:Full Q): pedal Q u (A f)= A (pedal Q u f):= by rw [← train_list,← train_list]; exact Mobile.train_paths A _ hg (fun i hi=> he i (by simpa using hi)) _
end YM.Frontier6.Bouquet
