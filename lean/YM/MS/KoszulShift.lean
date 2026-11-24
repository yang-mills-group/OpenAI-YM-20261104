import YM.MS.KoszulProduct

/-! Row-finite linear substitutions and their derivations, including the free BV differential. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset
variable {R A : Type*} [CommRing R] {p : Sector A} {b : Bool}
structure Shift (R : Type*) [CommRing R] (p : Sector A) (b : Bool) where
    source : A → Finset A
    mat : A → A → R
    row a i : i ∈ source a → p i = b.xor (p a)
namespace Shift
variable (T : Shift R p b)
def hook (a : A) : Raw A R →ₗ[R] Raw A R := ∑ i∈T.source a, (T.mat a i) • D i
def evolve (f : Raw A R) : Raw A R
    | [] => 0
    | x::w => T.hook x f w + cross b (p x) * evolve (D x f) w
termination_by w=> w.length
def Q : Raw A R →ₗ[R] Raw A R where
    toFun := T.evolve
    map_add' f g := by
       ext l; induction l generalizing f g with
       | nil=> simp only [evolve,Pi.add_apply, add_zero] -- adjust
       | cons x l IH=>
         simp only [evolve,map_add,IH,Pi.add_apply,mul_add]; abel
    map_smul' c f:= by
       ext l; induction l generalizing f with
       | nil=> simp [evolve]
       | cons x l IH=> simp only [evolve,map_smul,IH,RingHom.id_apply,Pi.smul_apply,smul_eq_mul]; ring
@[simp] lemma nil (f : Raw A R) : T.Q f [] = 0 := evolve.eq_1 ..
lemma deriving' (a) (f : Raw A R) : D a (T.Q f) = T.hook a f + (cross b (p a):R) • T.Q (D a f) := by ext l; exact evolve.eq_2 ..

lemma hook_deriv (a) (f : Raw A R) (u) (h : Symm p f) :
    D u (T.hook a f)=(cross (b.xor (p a)) (p u):R) • T.hook a (D u f):= by
   simp only [hook,LinearMap.sum_apply, LinearMap.smul_apply, map_sum,map_smul,Finset.smul_sum]
   apply Finset.sum_congr rfl; intro i hi; rw [h.commute u i, T.row _ _ hi,smul_comm]
lemma hook_pure {f : Raw A R} {c} (h : Pure p c f) a : Pure p (c.xor (b.xor (p a))) (T.hook a f):= by
   simp only [hook,LinearMap.sum_apply, LinearMap.smul_apply]; exact Pure.sum _ fun i hi => T.row a i hi ▸ (h.drop i).smul _ -- motive?
lemma hook_sym {f : Raw A R} (h : Symm p f) a : Symm p (T.hook a f) := by
   simp only [hook,LinearMap.sum_apply, LinearMap.smul_apply]; exact Symm.sum _ fun i _ => (h.drop i).smul _
lemma pure {f : Raw A R} {c} (h : Pure p c f) : Pure p (c.xor b) (T.Q f):= by
   intro l he; induction l generalizing c f with
   | nil=> simp
   | cons x l IH=>
      rw [D_eval x (T.Q f), deriving', Pi.add_apply,Pi.smul_apply]; rw [hook_pure T h x l ?_, IH (h.drop _) ?_, smul_zero,zero_add]
      all_goals revert he; simp only [degree_cons]; cases hl:p x <;> cases hb:degree p l <;> cases hj:b <;> cases c <;> simp -- linter
lemma sym {f : Raw A R} (h : Symm p f) : Symm p (T.Q f) := by
   intro l i j r; induction l generalizing f with
   | nil=>
      have C a x : D a (T.hook x f) = (cross (p x) (p a):R) • (cross b (p a):R) • T.hook x (D a f) := by rw [T.hook_deriv x f a h,cross_left, mul_comm, smul_smul]
      -- distribute
      have hq : D j (D i (T.Q f))=(cross (p i) (p j):R) • D i (D j (T.Q f)):= by
         simp only [deriving',map_add,map_smul]
         rw [C j i,C i j,h.commute j i,map_smul,cross_comm (p j)]; simp only [smul_add]
         conv_lhs => rhs; rhs; rw [smul_comm (cross b (p j) : R) (cross (p i) (p j) : R),
            smul_comm (cross b (p i) : R) (cross (p i) (p j) : R), smul_comm (cross b (p i) : R) (cross b (p j) : R)]
         simp only [smul_smul,← mul_assoc,cross_cross,one_mul]; -- loses rewrites?
         abel
      exact congr_fun hq r
   | cons a l IH=>
      simp only [List.cons_append,D_eval a (T.Q f),deriving',Pi.smul_apply,Pi.add_apply,smul_eq_mul]
      rw [T.hook_sym h a l i j r,IH (h.drop a)]; ring
lemma hook_sign {f : Raw A R} (a) c : T.hook a (sign p c f) = (cross c (b.xor (p a)) : R) • sign p c (T.hook a f) := by
  simp only [hook,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi
  rw [sign_D, T.row _ _ hi,smul_comm]
lemma rotate (F: Raw A R) c : T.Q (sign p c F)= (cross b c:R) • sign p c (T.Q F) := by
   ext l; induction l generalizing F with
   | nil=> simp
   | cons a l IH=>
      simp only [D_eval a,deriving', map_smul,sign_D,T.hook_sign, map_add, Pi.smul_apply, Pi.add_apply,IH,cross_right,smul_eq_mul]
      rw [cross_comm c b]; ring
local infixl:70 " ⋄ " => product p
lemma hook_product (a) (F G : Raw A R) : T.hook a (F ⋄ G)=(T.hook a F) ⋄ G+(sign p (b.xor (p a)) F) ⋄ (T.hook a G) := by
    simp only [hook,LinearMap.sum_apply, LinearMap.smul_apply, map_sum,D_product, map_smul,smul_add,Finset.sum_add_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i hi; rw [T.row a i hi]
lemma product_rule (F G : Raw A R) : T.Q (F ⋄ G)= T.Q F ⋄ G + (sign p b F) ⋄ T.Q G := by
    ext l; induction l generalizing F G with
    | nil=> simp
    | cons a l IH=>
      let C : R := cross b (p a)
      have he : sign p (p a) (T.Q F) = C • T.Q (sign p (p a) F) := by rw [T.rotate,smul_smul]; simp [C,cross_cross]
      simp only [D_eval a, D_product, map_add,T.hook_product, deriving', Pi.add_apply, IH,sign_D,sign_twice,map_smul,LinearMap.add_apply,LinearMap.smul_apply,Pi.smul_apply] -- order of map_add vs Pi...
      rw [he]; simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,C,Bool.xor_comm]
      simp only [smul_add]; abel
end Shift
end YM.MS.Koszul
