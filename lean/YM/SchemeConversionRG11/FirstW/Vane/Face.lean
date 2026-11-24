import YM.SchemeConversionRG11.FirstW.Mark.Root
/-! Orient all faces. Equivalent to positively-based Wilson price, also before perturbative expansion (if equally integrated bases). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {X : Type*} [AddCommGroup X] [One X]
-- order matters
abbrev Ticket := Axis×Bool
def fresh (q : Ticket) : Step := ⟨q.1,q.2⟩
def icon (u v : Step) : Walk := [u,v,u.rev,v.rev]
@[simp] lemma twiceRev (u : Step) : u.rev.rev=u := by rcases u with ⟨i,h|h⟩ <;> rfl
lemma icon_rev (u v : Step) : Lattice.reverse (icon u v)=icon v u := by simp [icon,Lattice.reverse]
lemma icon_stop (x : Four X) (u v : Step) : stop x (icon u v)=x := by simp [icon,stop,Step.vec_rev]; abel
lemma swipe_swap (U : Links X G.El) (x : Four X) (u v : Step) :
    G.price (travel U x (icon u v)) = G.price (travel U x (icon v u)) := by
  nth_rw 2 [← icon_stop x u v]; rw [←icon_rev u v,travel_reverse,G.price_inv]
lemma swipe_flip (U : Links X G.El) (x : Four X) (u v : Step) :
    G.price (travel U x (icon u v))= G.price (travel U (x+u.vec) (icon u.rev v)) := by
  rw [swipe_swap U _ u.rev]
  let Q:=travel U x (icon u v)
  let R:=u.read U x
  rw [show travel U (x+u.vec) (icon v u.rev)= R⁻¹ * Q * (R⁻¹)⁻¹ from ?_, G.price_conj]
  unfold Q R; simp only [icon,travel,twiceRev,mul_one]
  rw [u.vec_rev, v.vec_rev,show x+u.vec+v.vec +-(u.vec : Four X)+-(v.vec:Four X) = x by abel]; group
-- package summation over sites and walk pairs
variable {f : Site n → Walk → ℝ}
def wheels (f : Site n→ Walk → ℝ) := ∑ x,∑ s:Ticket,∑ t:Ticket, f x (icon (fresh s) (fresh t))
lemma wheel_rate (f : Site n→ Walk → ℝ) (hr : ∀ x i j, f x (icon i j)=f x (icon j i)) (hp : ∀ x i j, f x (icon i j)=f (x+i.vec) (icon i.rev j)) (hf : ∀ x i,f x (square i i)=0) :
    wheels f = (8:ℝ)*(∑ x,∑ i:Axis,∑ j:Axis, if i<j then f x (square i j) else 0) := by
  let P i j:=∑ x:Site n,f x (icon i j)
  have hP i j : P i j=P j i := Finset.sum_congr rfl fun x _ =>hr ..
  have he i j:P i j=P i.rev j := (Finset.sum_congr (s₂:=Finset.univ) (f:=fun x=>f x _) (g:=fun x=>f (x+i.vec) _) rfl fun x _=>hp ..).trans (Equiv.sum_comp (Equiv.addRight i.vec) (g:=fun x=> f x (icon i.rev j))) -- name
  have ha (s t:Ticket) : P (fresh s) (fresh t) = P (posDir s.1) (posDir t.1) := by
    have hz (s:Ticket) (j:Step) : P (fresh s) j=P (posDir s.1) j := by rcases s with ⟨i,h|h⟩; rfl; exact he (fresh (i,true)) j
    rw [hz,hP,hz,hP (posDir t.1)]
  have hu i j (x : Site n) : f x (square i j) = f x (square j i) := hr x (posDir i) (posDir j)
  unfold wheels; rw [Finset.sum_comm]; conv_lhs=> arg 2; intro a; rw [Finset.sum_comm]
  change (∑ s:Ticket,∑ t:Ticket,P (fresh s) (fresh t)) = _
  have hm : ∀ x : Site n,(∑ i: Axis,∑ j:Axis,f x (square i j))=2*(∑ i:Axis,∑ j:Axis, if i<j then f x (square i j) else 0) := by
    intro x; rw [two_mul]
    conv_rhs=> arg 1; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=>?_; split_ifs <;> grind
  simp_rw [ha, Fintype.sum_prod_type]; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]; push_cast; unfold P; simp only [show ∀ i j : Axis,icon (posDir i) (posDir j)=square i j from fun _ _=>rfl]
  conv_lhs=> arg 2; arg 2; arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm (f:=fun i x=>∑ j:Axis,f x (square i j))]; simp_rw [hm,← Finset.mul_sum]; ring
end YM.RG11.FirstW
