import YM.MSbar.Grass.Operators

/-! Pair operation is a graded biderivation. We prove on purely homogeneous super series so
later specialized identities require no simplifying symmetry of line orientations. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset
open scoped BigOperators Classical
variable {T:Type*}{p:T→Bit} {a b:T} {f g h : Series T} {d e r k j : Bit}
variable {P:Stock T} (hP : Grade p k P)

-- sign normalizers
lemma normalize_a : sign r d * sign (r+d) e=sign r (d+e) * sign d e:=by rw [sign_add_right,sign_add]; ring
lemma twice_one (A B:Bit) (z:ℂ):sign A B*(sign A B*z)=z:=by rw [←mul_assoc,sign_self,one_mul]
-- ext scalar tactic maybe.
namespace Grade
include hP
lemma swap (hf:Homogeneous p d f)(hg:Homogeneous p e g): pairs p d P f g=sign d e • pairs p e P g f:=by
   have he:=hP.product hf g; rw [atom_clean hf hg, map_smul,hP.product hg f] at he
   rw [atom_clean (hP.homogeneous hg) hf,atom_clean hg (hP.homogeneous hf)] at he
   ext v -- beware funext
   replace he := congr_fun he v
   simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sign_add_right,sign_add] at he ⊢
   rw [braid e d,braid e k] at he
   let s :=sign d e; let a:= sign k d; let b:=sign k e
   have h (i j:Bit) : sign i j=1∨sign i j=-1:=by unfold sign;split_ifs <;> norm_num
   rcases h d e with hs|hs <;> rcases h k e with h1|h1 <;>  (simp only [hs,h1] at he ⊢; linear_combination (norm:=ring_nf) - he)

/- Special-case pairing term rule of product on second slot; d used in sign is not changing in this. -/
private lemma seed_r (x : T)(y:T)(hf:Homogeneous p d f)(hg:Homogeneous p e g)(he:Homogeneous p r h)(hp:p x+p y=k):
    join p (field x f) (field y (join p g h))=join p (join p (field x f) (field y g)) h+ sign (k+d) e • join p g (join p (field x f) (field y h)):=by
   rw [product_rule hg.shape,join_add_right,join_scale_right,← join_assoc (hf.derives x) (hg.derives y) he,← join_assoc (hf.derives x) hg (he.derives y)]
   rw [atom_clean (hf.derives x) hg,join_scale_left, join_assoc hg (hf.derives x),←hp, smul_smul,show sign _ _* sign _ _=sign (p x+p y+d) e from ?_]
   rw [← sign_add,show p y +(p x+d)=_ from (show p y+(p x+d)=p x+p y+d by abel)]
   exact he.derives y
lemma derivation (hf:Homogeneous p d f)(hg:Homogeneous p e g)(he:Homogeneous p r h):
   pairs p d P f (join p g h)= join p (pairs p d P f g) h+ sign (k+d) e • join p g (pairs p d P f h):=by
   simp_rw [price_pair,join_sum_left,join_sum_right,join_scale_left,join_scale_right, Finset.smul_sum,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
   intro x hx; simp_rw [member_pair,seed_r hP _ _ hf hg he (hP x hx),seed_r hP _ _ hf hg he ((add_comm ..).trans (hP x hx)),join_add_left,join_add_right, join_scale_left,join_scale_right]; ext v; simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply]; ring
end Grade
end YM.MSbar.Super
