import YM.MS.Koszul

set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset
variable {R : Type*} [CommRing R] {A B : Type*} {p : Sector A} {F H : Raw A R} {b c : Bool}

def product (p : Sector A) : Raw A R →ₗ[R] (Raw A R →ₗ[R] Raw A R) where
    toFun u:= { toFun:= times p u
                map_add' _ _:= times_add ..
                map_smul' _ _:= times_smul .. }
    map_add' _ _:= LinearMap.ext fun _ => add_times ..
    map_smul' _ _:= LinearMap.ext fun _=> smul_times ..
local infixl:70 " ⋄ " => product p
lemma D_product (x) (u v:Raw A R) : D x (u ⋄ v)= (D x u) ⋄ v + (sign p (p x) u) ⋄ (D x v):= times_rule ..
@[simp] lemma nil_product (u v:Raw A R) : (u ⋄ v) [] = u []*v []:= times_nil ..

lemma Symm.head_times (h : Symm p F) (t : Symm p H) (x y : A) :
    D y (D x (times p F H))=(cross (p x) (p y):R) • D x (D y (times p F H)):= by
   let M:R := cross (p x) (p y)
   simp only [times_rule,sign_D, map_add]
   rw [h.commute y x, t.commute y x, signs_commute p (p y) (p x), smul_times, smul_times, smul_times, times_smul, cross_comm (p y) (p x)];
   simp only [smul_add, smul_smul,(cross_cross ..),one_smul]; abel

lemma Symm.times (h : Symm p F) (t : Symm p H) : Symm p (times p F H) := by
   intro l a b r; induction l generalizing F H with
   | nil=> exact congr_fun (h.head_times t a b) r
   | cons x l ih=>
      simp only [List.cons_append,D_eval x (Koszul.times p F H),times_rule,Pi.add_apply]
      rw [mul_add]; exact congr_arg₂ (· + ·) (ih (h.drop _) t) (ih (h.signs _) (t.drop _))
lemma times_assoc (F H G:Raw A R): (F ⋄ H) ⋄ G= F ⋄ (H ⋄ G) := by
    ext l; induction l generalizing F H G with
    | nil => simp [mul_assoc]
    | cons a l IH=>
       simp only [D_eval a (product p _ _), D_product]
       rw [show sign p (p a) (F ⋄ H)=(sign p (p a) F) ⋄ (sign p (p a) H) from twisted_product ..]
       simp only [map_add, LinearMap.add_apply,Pi.add_apply]; rw [IH,IH,IH]; exact add_assoc ..
lemma Pure.prod (h : Pure p b F) (t : Pure p c H) : Pure p (b.xor c) (F ⋄ H) := by
    intro l hr; induction l generalizing F H b c with
    | nil=>
       simp only [nil_product]; cases b <;> cases c <;> simp_all [Pure,Bool.xor]
    | cons a l IH=>
       simp only [D_eval a (F ⋄ H),D_product,h.signs,map_smul,LinearMap.smul_apply,Pi.smul_apply,Pi.add_apply]
       rw [IH (h.drop a) t ?_,IH h (t.drop a) ?_, smul_zero, zero_add]
       all_goals cases hq:p a <;> cases hb: degree p l <;> cases b <;> cases c <;> simp_all [Bool.xor]
lemma Pure.times_comm (h : Pure p b F) (t : Pure p c H) : F ⋄ H =(cross b c:R) • (H ⋄ F) := by
    ext l; induction l generalizing F H b c with
    | nil=>
       cases b <;> cases c <;> first | solve | simp [mul_comm] | simp [h.from_nil rfl]
    | cons x l IH=>
       simp only [D_eval x, map_smul, D_product, h.signs, t.signs, LinearMap.smul_apply, Pi.smul_apply,Pi.add_apply,smul_eq_mul]
       rw [IH (h.drop x) t,IH h (t.drop x)]; cases hp:p x <;> cases b <;> cases c <;> simp [Bool.xor, add_comm]
-- easier for central even Id
lemma degree_cases (F : Raw A R) (p : Sector A) : ∃ K L, F= K+L ∧ Pure p false K∧Pure p true L:= by
    let K (x):= if degree p x then 0 else F x
    refine ⟨K,F-K,Eq.symm (add_sub_cancel ..),?_,?_⟩
    · intro x hx; simp_all [K]
    intro x hx; simp_all [K]
lemma Pure.central (h : Pure p false F) (v : Raw A R) : F ⋄ v=v ⋄ F:= by
    obtain ⟨K,L,rfl,hK,hL⟩:= degree_cases v p
    rw [map_add,map_add,LinearMap.add_apply, h.times_comm hK,h.times_comm hL]; simp

def coin (u : R) : Raw A R | [] => u | _::_ => 0
lemma coin_pure (c : R) : Pure p false (coin c) := by intro l h; cases l; contradiction; rfl
lemma coin_symm (c : R) : Symm p (coin c) := fun l _ _ _=> by cases l <;> simp [coin]
lemma coin_product (c : R) (F:Raw A R) : coin c ⋄ F=c • F:= by
    ext l; induction l generalizing F with
    | nil=> simp [coin]
    | cons x l IH=>
       simp only [D_eval x, map_smul, Pi.smul_apply,D_product,(coin_pure _).signs,cross_false',one_smul]
       rw [show D x (coin c)=0 from funext fun y=>rfl,map_zero]; simpa using IH (D x F)
end YM.MS.Koszul
