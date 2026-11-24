import YM.MS.Garment.Wick
/-!
# Rotation testing actual vector/gauge/laplacian symbols

All axes dimension (tape formula), verifies full orthogonal d. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wick
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric City Color
open scoped Topology ContDiff
open Complex (I)
variable {G:Gauge}{A C:Type}[Fintype A][DecidableEq A] [Fintype C][DecidableEq C]
variable (X: Spin A)
lemma auth (p q:Leg A C): (∑ u: Leg A C, X.prop u p* X.prop u q)=(if p=q then 1 else 0):= by
    have h (i j:A): (∑ a:A, (X.profile a i:ℂ)* (X.profile a j:ℂ)) = if i=j then 1 else 0:= by simp_rw [X.dual,← Complex.ofReal_mul,← Complex.ofReal_sum, X.back.weights]; split <;> simp
    rcases p with ⟨⟨_|a,_|_⟩,c⟩ <;> rcases q with ⟨⟨_|b,_|_⟩,d⟩ <;> simp [Spin.prop, Fintype.sum_prod_type,Fintype.sum_option, rayS,shadow,ite_mul,mul_ite] <;> by_cases hx:c=d <;> simp only [hx,↓reduceIte,and_true,and_false] <;> first| rfl| (simp [h] <;> grind) -- try
abbrev TestPass (F: Flux (Atom A) (Momentum A) ℂ): Prop:= ∀ p i k, (∑ j,F i j p* X.rayS j k)= ∑ j, X.rayS i j * F j k (X.turn p)
lemma regular_copy {F: Flux (Atom A) (Momentum A) ℂ}(h: TestPass X F)(p: Momentum A)(i k:Leg A C): (∑ j, Landau.choir F id i j p* X.prop j k) = ∑ j, X.prop i j* Landau.choir F id j k ( X.turn p):= by
   simp only [Fintype.sum_prod_type,Landau.choir,Spin.prop,id_eq]; by_cases he:i.2=k.2; · simpa [he, ite_mul,mul_ite,Fintype.sum_prod_type,Fintype.sum_option] using h p i.1 k.1
   simp [he,ite_mul,mul_ite]
variable (C)
lemma card_tr {F: Flux (Atom A) ( Momentum A) ℂ} (H: TestPass X F): Transport (Spin.leggo C X) (Landau.choir F id) (Landau.choir F id):= by
    intro p i j; let U:= (Landau.choir (C:=C) F id); change U i j _=(∑ a,∑ b, U a b _ * X.prop a i* X.prop b j); simp_rw [show ∀ a b,U a b p * X.prop a i * X.prop b j=X.prop a i*(U a b p*X.prop b j) from fun a b=> by ring, ← Finset.mul_sum];
    simp_rw [show ∀ u,(∑ b, U u b p* X.prop b j)=∑ b,X.prop u b* U b j (X.turn p) from fun u=>regular_copy X H p u j, Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul,auth]; simp [ite_mul]; rfl
-- block angular rational lemmas
lemma carry (i j:A)(p:Momentum A) : ∑ a:A, precision i a p* X.profile a j=∑ a:A,X.profile i a*precision a j ( X.turn p):= by
   unfold precision delta; simp_rw [sub_mul,mul_sub,sum_sub_distrib]; simp [ite_mul,mul_ite, X.fare];
   have hx : ∑ a:A,X.profile i a* X.turn p a = p i:= by simp_rw [X.dual i,mul_comm _ (X.turn p _)]; rw [X.back.orth]; simp
   simp_rw [mul_assoc (p i), ← mul_assoc (X.profile i _)]; rw [← Finset.mul_sum, ← Finset.sum_mul]; rw [X.orth,hx]; ring -- may indices align
-- actual charge lemmas
lemma trial_q : TestPass X bare:= by
    intro p i j; have h a : (∑ i:A,(p i:ℂ)*X.profile i a) = X.turn p a :=by push_cast [← X.orth]; rfl -- parse
    have hy a : (∑ i:A,(X.profile a i:ℂ)*(X.turn p i:ℂ)) =p a:= by simp_rw [X.dual a, ← Complex.ofReal_mul,← Complex.ofReal_sum,mul_comm _ (X.turn p _)]; rw [X.back.orth]; simp
    rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;> simp [Fintype.sum_prod_type,Fintype.sum_option, rayS,shadow, Landau.bare] -- body
    · simp_rw [mul_assoc Complex.I,← Finset.mul_sum,h]
    · simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum,realK _ i p,realK j _ (X.turn p),carry]
    simp_rw [mul_left_comm _ Complex.I,← Finset.mul_sum,hy]
end YM.MS.Garment.Wick
