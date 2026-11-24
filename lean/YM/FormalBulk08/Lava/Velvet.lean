import YM.FormalBulk08.Lava.Meteor

/-! Rank functor across many alphabets incl output. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb MvPolynomial
open scoped BigOperators Classical
variable {V I J : Type*} (L : V→I→ℝ)
def pearl {r : ℕ} (T : Tile V r) : Tile I r:= fun v=> ∑' w,T w*∏ i,L (w i) (v i)
lemma pearl_agate {r : ℕ} {T : Tile V r} (h : Agate T) : Agate (pearl L T) := by
   intro v s;
   let e:=Equiv.arrowCongr s.symm (Equiv.refl V);unfold pearl; rw [← Equiv.tsum_eq e]
   exact tsum_congr fun i=>by change T (i ∘ s)* _= _; rw [h];congr 1; exact Fintype.prod_equiv s _ _ fun _=> rfl
lemma pearl_zero (r : ℕ) : pearl L (0 : Tile V r)=0:= by funext i; simp [pearl]
-- direct carve (Aft zeros avoids tsum versions)
def jetty (Z : I→V) {r : ℕ} (T : Tile V r) : Tile I r:= fun v=> T (Z ∘ v)
lemma jetty_agate (Z : I→V) {r : ℕ} {T : Tile V r} (h : Agate T) : Agate (jetty Z T) := fun v s=> h (Z ∘ v) s
lemma jetty_zero (Z : I→V) (r : ℕ) : jetty Z (0 : Tile V r)=0 := rfl

variable [Fintype V] [Fintype I]
lemma mix_facade {r : ℕ} (T : Tile V r) : mixRows L (facade _ T)=facade _ (pearl L T) := by
   simp_rw [facade_eq,map_sum,map_mul, cards, mixRows,aeval_C,map_prod,aeval_X]; simp_rw [Fintype.prod_sum,Finset.prod_mul_distrib, Finset.mul_sum]
   rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_
   simp only [pearl,tsum_fintype, _root_.map_sum, Finset.sum_mul,_root_.map_prod, map_mul]; apply Finset.sum_congr rfl; intro j _; rw [mul_assoc]; rfl
lemma shuffle_grade (p : TypeR V) (r : ℕ) : homogeneousComponent r (mixRows L p)=mixRows L (homogeneousComponent r p) := by
   rw [←sum_homogeneousComponent p]; simp_rw [map_sum]
   apply Finset.sum_congr rfl; intro i hi; nth_rw 1 [←marble_grade i p]; rw [mix_facade, homogeneousComponent_of_mem (facade_grade _ _), homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous _ p),←mix_facade,marble_grade]; split_ifs <;> simp
lemma target (r : ℕ) (p : TypeR V) : marble r (mixRows L p)=pearl L (marble r p) := by apply facade_unique (marble_agate _ _) (pearl_agate _ (marble_agate _ _)); rw [marble_grade,←mix_facade,marble_grade, shuffle_grade]
end YM.FormalBulk08.Lava
