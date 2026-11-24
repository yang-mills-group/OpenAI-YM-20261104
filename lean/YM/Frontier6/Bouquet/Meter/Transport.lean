import YM.Frontier6.Bouquet.Meter.Pockets

/-!
# Local linearity of the finite-regulator ledger
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q:Ensemble} (i:P)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
    (x: Seats P) (H J:Patron S P Y) (f g:Full (fiber P))
def Appointed : Prop := ∀ (i:Down P)(p:Trip A i.val), Integrable (ink K A T i.property x H p f)
def Welcomes (H:Patron S P Y)(x:Seats P)(f:Full (fiber P)):Prop:=∃ B: Balcony P,Gentle H B∧Fair f B x
lemma Welcomes.appointed (he:Welcomes H x f): Appointed K A T x H f:=by rintro i p; obtain ⟨b,h,hE⟩:= he; exact further K A T _ _ _ h hE
lemma ink_zero (he:Q ≤ P)(p:Trip A Q): ink K A T he x H p 0=0:=by funext i; simp [ink]
lemma ink_noop (he:Q≤P)(p:Trip A Q): ink K A T he x (0:Patron S P Y) p f=0:=by funext i; simp [ink,convey_at]
lemma ink_add (he:Q≤P)(p:Trip A Q): ink K A T he x H p (f+g)= ink K A T he x H p f + ink K A T he x H p g:=by ext1 i; simp_rw [Pi.add_apply,ink,map_add,_root_.add_apply]; exact add_smul .. -- notation
lemma ink_scal (he:Q≤P)(p:Trip A Q)(c:ℂ): ink K A T he x H p (c • f)= c • ink K A T he x H p f:=by
    ext1 i; simp_rw [Pi.smul_apply,ink, map_smul,smul_apply]; rw [smul_eq_mul,mul_smul]
lemma ink_sameplus (he:Q≤P)(p:Trip A Q) : ink K A T he x (H+J) p f= ink K A T he x H p f+ ink K A T he x J p f:=by funext i; simp_rw [Pi.add_apply,ink,convey_at,MultilinearMap.add_apply]; exact smul_add ..
lemma ink_sameneg (he:Q≤P)(p:Trip A Q) : ink K A T he x (-H) p f= -ink K A T he x H p f:=by funext i; simp_rw [Pi.neg_apply,ink,convey_at,MultilinearMap.neg_apply]; exact smul_neg ..
lemma appointed_zero : Appointed K A T x H 0:=by intro i p; rw [ink_zero]; exact integrable_zero ..
lemma select_zero (s:Finset (Down P)) : select K A T s x H 0=0:=by unfold select branch essay; simp_rw [ink_zero]; simp
lemma select_scal (s:Finset (Down P)) (c:ℂ) :select K A T s x H (c • f)=c • select K A T s x H f:=by
    unfold select branch essay; simp_rw [ink_scal,Pi.smul_apply,integral_smul,Finset.smul_sum]
lemma select_plus (s:Finset (Down P))(hf: Appointed K A T x H f)(hg: Appointed K A T x H g): select K A T s x H (f+g)=select K A T s x H f + select K A T s x H g:=by
    unfold select branch essay; simp_rw [ink_add,Pi.add_apply]; -- annotation proof
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun p _=> integral_add (hf _ p) (hg _ p)
variable {f g x H J K A T}
lemma Appointed.scal (he:Appointed K A T x H f)(c:ℂ): Appointed K A T x H (c • f):=by intro i p; rw [ink_scal]; exact (he i p).smul c -- name
lemma Appointed.plus (he:Appointed K A T x H f)(hk:Appointed K A T x H g): Appointed K A T x H (f+g):=by intro i p; rw [ink_add]; exact (he i p).add (hk i p)
lemma Appointed.sameplus (he:Appointed K A T x H f)(hk:Appointed K A T x J f): Appointed K A T x (H+J) f:=by intro i p; rw [ink_sameplus]; exact (he i p).add (hk i p)
lemma Appointed.sameneg (he:Appointed K A T x H f): Appointed K A T x (-H) f:=by intro i p; rw [ink_sameneg]; exact (he i p).neg
lemma select_sameplus (s:Finset (Down P))(hf: Appointed K A T x H f)(hg: Appointed K A T x J f): select K A T s x (H+J) f=select K A T s x H f+ select K A T s x J f:=by
    unfold select branch essay; simp_rw [ink_sameplus,Pi.add_apply]; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun p _=> integral_add (hf _ p) (hg _ p)
lemma Appointed.trivial (K:Final C F S)(A:Teller S)(T:Veins)(x:Seats P)(f:Full (fiber P)): Appointed K A T x (0:Patron S P Y) f:=by intro i p; rw [ink_noop]; exact integrable_zero ..
end YM.Frontier6.Bouquet
