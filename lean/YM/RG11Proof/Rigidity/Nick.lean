import YM.RG11Proof.Rigidity.Strip

/-!
# Interpolating marked contractions
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Strip
open Maxwell.Free Filter Function
open scoped BigOperators Topology

variable {I : Type*}

-- twice the price of one distinguished pair, weighted by `τ` of the remainder

def nick (E : I → I → ℝ) (τ : List I → ℝ) (u : List I) := pulls u (fun a l=> pulls l (fun b r=> E a b * τ r))

lemma nick_cons (E : I → I → ℝ) (τ : List I→ℝ) (u : List I) (hx : ∀ a b,E a b=E b a) (c : I) :
    nick E τ (c::u) = 2*pulls u (fun b r=>E c b * τ r) + nick E (fun l=>τ (c::l)) u := by
  unfold nick; rw [pulls_cons]; simp_rw [pulls_cons,pulls_add,hx _ c]; ring

def rate (E K : I → I → ℝ) (p L : List I) (t : ℝ) := grade (fun i j =>t*E i j) K p L
lemma rate_nil (E K : I → I → ℝ) (L : List I) (t) : rate E K [] L t = pairCost K L := grade_nil ..
lemma rate_cons (E K : I → I → ℝ) (a : I) (p L : List I) (t) :
    rate E K (a::p) L t = pulls p (fun b l=> t*E a b * rate E K l L t) + pulls L (fun b r=> K a b * rate E K p r t) := grade_cons ..

lemma hasPulls {t : ℝ} (l : List I) {f : I → List I → ℝ → ℝ} {k : I → List I → ℝ}
    (h : ∀ (i : Fin l.length), HasDerivAt (f (l.get i) (l.eraseIdx i.val)) (k (l.get i) (l.eraseIdx i.val)) t) :
    HasDerivAt (fun t=> pulls l (fun a r=> f a r t)) (pulls l k) t := by
  apply HasDerivAt.fun_sum; exact fun i _=> h i

lemma nick_rate {E K : I → I → ℝ} (hx : ∀ a b,E a b=E b a) (u L : List I) (t : ℝ) :
    HasDerivAt (rate E K u L) (1/2*nick E (fun r=> rate E K r L t) u) t := by
  induction h : u.length using Nat.strong_induction_on generalizing u L with
  | h n ih =>
    cases u with
    | nil => rw [show rate E K [] L = fun _=>pairCost K L from funext (rate_nil E K L),nick,pulls_nil,mul_zero]; exact hasDerivAt_const ..
    | cons a u =>
      rw [funext (rate_cons E K a u L),nick_cons E _ u hx a]
      let T r s := rate E K r s t
      let N r s := nick E (fun r=>T r s) r
      have he (r s : List I) (hr : r.length < n) : HasDerivAt (rate E K r s) (1/2*N r s) t := ih _ hr r s rfl
      have ht (i : Fin u.length) : HasDerivAt (fun y : ℝ=>y*E a (u.get i)*rate E K (u.eraseIdx i.val) L y)
          (E a (u.get i)*T (u.eraseIdx i.val) L+t*E a (u.get i)*(1/2*N (u.eraseIdx i.val) L)) t := by
        simpa [← mul_assoc,Pi.mul_def,T] using ((hasDerivAt_id' t).mul_const (E a (u.get i))).mul (he (u.eraseIdx i.val) L (by have := pulls_short i; simp only [List.length_cons] at h; omega))
      have hq (i : Fin L.length) := (he u (L.eraseIdx i.val) (by simp only [List.length_cons] at h; omega)).const_mul (K a (L.get i))
      refine (hasPulls (f:=fun b l t=> t*E a b * rate E K l L t) (k:=fun b r=> E a b * T r L + t*E a b*(1/2*N r L)) u ht).add
        (hasPulls (f:=fun b r t=> K a b*rate E K u r t) (k:=fun b r=> K a b*(1/2*N u r)) L hq) |>.congr_deriv ?_
      simp_rw [pulls_add]
      unfold nick N Strip.nick
      simp_rw [rate_cons,mul_add,pulls_add,← pulls_mul]
      simp_rw [mul_add,← pulls_mul]
      rw [← add_assoc]; congr 1; swap
      · rw [pulls_comm L u]
        refine pulls_congr u ?_; intro i
        rw [pulls_comm L]; refine pulls_congr _ ?_; intro j; refine pulls_congr L ?_; intro k; dsimp only [T]; ring
      congr 1; swap
      · rw [pulls_triple u (fun i j k r=>t*E a i*(1/2*(E j k*T r L)))]
        refine pulls_congr u ?_; intro i; refine pulls_congr _ ?_; intro j; refine pulls_congr _ ?_; intro k; dsimp only [T]; ring
      refine pulls_congr u ?_; intro i; dsimp only [T]; ring

end YM.RG11.Rigidity.Strip
