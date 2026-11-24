import YM.X.Sage.Tolling
/-!
# Xcall stamps algebra. both distinctive/class. no symmetry factors hidden.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V I:Type*} {q:ℕ+}{r R:ℝ}
local notation "U"=> G.ColorIndex
local notation "P"=> Curly G
local notation "T"=>Tet
local notation "o"=> side q k
local notation "Q"=> qu q G k
local notation "ℓ"=> Hair G→₀ℂ
variable (A B C:Curly G)
local notation "E"=> tri Q
local notation "δ"=> edge Q
abbrev XEdge (q:ℕ+)(k:ℕ)(x y:Hair G→₀ℂ)(A B C:Curly G):= tri (qu q G k) A (edge (qu q G k) x B) (edge (qu q G k) y C)
def XBridge (q:ℕ+)(k:ℕ)(x y:Hair G→₀ℂ)(A B C:P):= XEdge q k x y A B C+XEdge q k y x A B C
abbrev Corner (q:ℕ+)(k:ℕ)(x y: Hair G→₀ℂ)(A B C:P):= tri (qu q G k) A (edge (qu q G k) y (edge (qu q G k) x B)) C
lemma born (x y:ℓ) : E (glyph x*glyph y * A) B C=XBridge q k x y A B C+Corner q k x y A B C+ Corner q k x y A C B:= by rw [mul_assoc,tri_cross]; simp_rw [tri_cross,XBridge,XEdge,Corner]; rw [tri_C (q:=Q) (B:=δ y (δ x C))]; ring
-- linearity space
variable (x y z:Cover)(p:Tet)(i:G.ColorIndex)
abbrev Ticket (G:Gauge):= PlaqAxes × G.ColorIndex × G.ColorIndex
def suba (q:ℕ+)(k:ℕ)(x:Cover)(u:Ticket G): Hair G→₀ℂ:= psiA q k x u.1.val.1 u.2.1
def subb (q:ℕ+)(k:ℕ)(x:Cover)(u:Ticket G):ℓ:= psiA q k x u.1.val.2 u.2.2
def toll (r:ℝ)(p:Tet)(a:U)(u:Ticket G):ℂ:= ↑(dataF r p u.1 * ff a u.2.1 u.2.2)
lemma sleepy (t:Ticket G)(he:t.2.1=t.2.2): toll r p i t=0:= by unfold toll; rw [Sage.lack _ _ _ (by tauto)]; simp -- c name?
local notation "τ"=> toll r p i
def skirt (q:ℕ+)(k:ℕ)(s:ℝ)(x:Cover)(p:Tet)(a:U)(A B C:P):ℂ:= ∑ u:Ticket G,toll s p a u * XBridge q k (suba q k x u) (subb q k x u) A B C
def twiceC (q:ℕ+)(k:ℕ)(s:ℝ)(x:Cover)(p:Tet)(a:U)(A B C:P):ℂ:= ∑ u:Ticket G,toll s p a u * Corner q k (suba q k x u) (subb q k x u) A B C
lemma snap_a : veil x k (bcomp q r p i)=∑ u:Ticket G,τ u • (glyph (suba q k x u)*glyph (subb q k x u)) := by
    simp_rw [compb,map_sum,map_smul,foame,map_sum,map_smul, Finset.smul_sum,Fintype.sum_prod_type,smul_smul,map_mul,veil_pot]; apply Finset.sum_congr rfl; intro v _; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun l _=> ?_; unfold toll; rw [Complex.ofReal_mul];rfl
lemma birth : E (veil x k (bcomp q r p i)* A) B C=skirt q k r x p i A B C+twiceC q k r x p i A B C+twiceC q k r x p i A C B:= by rw [snap_a]; unfold skirt twiceC; simp_rw [Finset.sum_mul, smul_mul_assoc, tri_sum,tri_scale,born,smul_eq_mul,mul_add,Finset.sum_add_distrib]
lemma upperTher (x y:ℓ)(f:ℓ): school Q A B C (Tot.triple f x y)= XBridge q k x y (δ f A) B C+XBridge q k x y (δ f B) C A+ XBridge q k x y (δ f C) A B := by
    rw [just_school]; unfold XBridge XEdge send; rw [tri_spin Q (δ x A) (δ f B),tri_spin Q (δ y A) (δ f B),tri_rotate (A:=δ x A) (C':=δ f C), tri_rotate (A:=δ y A) (C':=δ f C)]; ring 
-- retrieve coefficient at birth.S
lemma skirt_S (V V':P): skirt q k r x p i (V+V') B C=skirt q k r x p i V B C + skirt q k r x p i V' B C:= by unfold skirt XBridge XEdge; simp_rw [tri_plus, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro t _; ring
lemma skirt_M (u:ℂ): skirt q k r x p i (u • A) B C= u • skirt q k r x p i A B C:= by unfold skirt XBridge XEdge; simp_rw [tri_scale,← smul_add]; simp only [smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
lemma skirt_sum (F:I→Curly G)(X:Finset I):skirt q k r x p i (∑ j∈X,F j) B C=∑ j∈X,skirt q k r x p i (F j) B C:= by
   induction X using Finset.induction_on with| empty=> simp only [Finset.sum_empty,skirt,XBridge,XEdge,tri_z,add_zero,mul_zero,Finset.sum_const_zero]| insert i X he ih=> rw [Finset.sum_insert he,Finset.sum_insert he,skirt_S,ih]
lemma skirt_swap : skirt q k r x p i A B C=skirt q k r x p i A C B:= by unfold skirt XBridge XEdge; apply Finset.sum_congr rfl; intro u _; apply congr_arg; rw [tri_C Q A (δ _ B) (δ _ C), tri_C Q A (δ _ B)]; ring
-- school linear ink
lemma school_plus (v w:P): school Q A B C (v+w)= school Q A B C v+school Q A B C w:= by unfold school majority; rw [space_add]; simp_rw [madd₀,tri_plus]; ring
lemma school_mul (V:P)(s:ℂ): school Q A B C (s • V)= s • school Q A B C V:= by unfold school majority; rw [space_scale]; simp_rw [mscale,tri_scale]; simp only [smul_sub]
lemma school_corn (X:Finset I)(F:I→P): school Q A B C (∑ i∈X,F i)=∑ i∈X,school Q A B C (F i) := by induction X using Finset.induction_on with| empty=> simp only [school, Finset.sum_empty, qu_zero,majority,mzero,tri_z,sub_zero]| insert i X h ih=> rw [Finset.sum_insert h,Finset.sum_insert h,school_plus,ih]
lemma upperFilm (f:ℓ):
   school Q A B C (glyph f*veil x k (bcomp q r p i)) = skirt q k r x p i (δ f A) B C+ skirt q k r x p i (δ f B) C A + skirt q k r x p i (δ f C) A B:= by
      rw [snap_a]; simp_rw [Finset.mul_sum,mul_smul_comm,school_corn,school_mul,skirt,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun u _=> ?_; rw [← mul_add, ← mul_add, show school _ _ _ _ _= _ from upperTher ..]; rfl
end YM.PositionX.Sage
