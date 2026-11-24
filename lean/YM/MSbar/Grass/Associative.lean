import YM.MSbar.Grass.Product

/-! Associative and super-commutative signs of tensor sewing. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset
open scoped BigOperators Classical
variable {T:Type*}{p:T→Bit} {f g h : Series T} {a b d e c i j : Bit}
lemma Homogeneous.join (hf:Homogeneous p d f)(hg:Homogeneous p e g): Homogeneous p (d+e) (join p f g):=by
   refine ⟨?_,joined hf.shape hg.shape⟩; intro l x y k
   induction l generalizing f g d e with
   | nil =>
      change field y (field x (Super.join p f g)) k=sign (p x) (p y)*field x (field y (Super.join p f g)) k
      rw [product_rule hf.shape g x,map_add,map_smul,product_rule hf.shape g y,map_add,map_smul,product_rule (hf.derives x).shape,product_rule hf.shape,product_rule (hf.derives y).shape,product_rule hf.shape, hf.comm x y,hg.comm x y, join_scale_left,join_scale_right]
      -- scalar arithmetic only
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sign_add_right]; rw [braid (p y) (p x)]; set s:= sign (p x) (p y) with he; have h0 : s=1∨s=-1:= (by rw [he]; unfold sign; split_ifs <;> simp)
      rcases h0 with hx|hx <;> rw [hx] <;> ring
   | cons z l ih =>
      change field z (Super.join p f g) (l++_)=_*field z (Super.join p f g) (l++_)
      rw [product_rule hf.shape]; simp_rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; rw [ih (hf.derives z) hg,ih hf (hg.derives z)]; ring
lemma atom_clean (hf : Homogeneous p d f) (hg:Homogeneous p e g) : join p f g=sign d e • join p g f := by
    funext v; induction v generalizing f g d e with
    | nil =>
       rcases eq_or_ne 0 d with rfl|h
       · simp [join,mul_comm]
       have ht:f []=0:=hf.shape [] h
       simp [join,ht]
    | cons a v ih =>
       change field a (join p f g) v=sign d e*field a (join p g f) v; rw [product_rule hf.shape,product_rule hg.shape]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; rw [ih (hf.derives a) hg,ih hf (hg.derives a)]
       simp only [Pi.smul_apply,smul_eq_mul,sign_add,sign_add_right]
       rw [braid d (p a)]; set s:=sign (p a) d with he; have hs:s=1∨s=-1:=by rw [he];unfold sign;split_ifs <;> simp
       rcases hs with h|h <;> rw [h] <;> ring
lemma join_assoc (hf:Homogeneous p d f)(hg: Homogeneous p e g)(hh:Homogeneous p c h) : join p (join p f g) h=join p f (join p g h):=by
    funext v; induction v generalizing f g h d e c with
    | nil => simp [join,mul_assoc]
    | cons a l ih =>
        change field a (join p (join p f g) h) l= field a (join p f (join p g h)) l
        rw [product_rule (hf.join hg).shape,product_rule hf.shape,product_rule hf.shape,product_rule hg.shape]
        rw [join_add_left,join_scale_left,join_add_right,join_scale_right]
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,ih (hf.derives a) hg hh,ih hf (hg.derives a) hh,ih hf hg (hh.derives a),sign_add_right]; ring

-- sign tactic
lemma sign_one (p:Bit) : sign 1 p=if p=0 then 1 else -1:=by rcases bit_cases p with rfl|rfl <;> simp [sign]
lemma bit_twice (c:Bit) : c+c=0:=by rcases bit_cases c with rfl|rfl <;> decide
end YM.MSbar.Super
