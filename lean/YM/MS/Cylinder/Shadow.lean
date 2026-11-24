import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Variable
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
/-! star on symbols before Fourier; real part only. No graded reflection signs here. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset Cylinder
variable {A I : Type*} {F H : Raw A ℂ}{p : Sector A}
def Still (F:Raw A ℂ) := ∀ w,star (F w)= F w
namespace Still
lemma D (i:A)(h:Still F): Still (D i F):= fun l=> h (i::l)
lemma sign (h:Still F)(b:Bool): Still (sign p b F):= by intro l; simp only [at_sign,cross]; split <;> simp [h l]
lemma add (h:Still F)(h':Still H): Still (F+H):=fun i=>by simp [h i,h' i]
lemma sub (h:Still F)(h':Still H): Still (F-H):=fun i=>by simp [h i,h' i]
lemma neg (h:Still F): Still (-F):=fun i=>by simp [h i]
lemma zero : Still (0:Raw A ℂ):= fun _=> star_zero _
lemma scalar (c:ℂ)(hc:star c=c)(h:Still F): Still (c • F):=fun i=>by simp [h i,hc]
lemma sum {P:I→Raw A ℂ}(s:Finset I)(h:∀ i∈s,Still (P i)): Still (∑ i∈s,P i):= by intro w; rw [Finset.sum_apply,star_sum]; exact Finset.sum_congr rfl fun i hi=> h i hi w
lemma product (h:Still F)(h':Still H): Still (product p F H):= by
   intro l; induction l generalizing F H with| nil=> simp [h [],h' []]
                                             | cons a l ih=> rw [D_eval a (Koszul.product p F H),D_product,Pi.add_apply]; simp [ih (h.D _) h',ih (h.sign _) (h'.D _)]
lemma letter (i:A): Still (atLetter i):= by intro l; cases l with| nil=> exact star_zero _| cons a l=> cases l with| nil=>simp [atLetter,apply_ite]| cons b l=> exact star_zero _
lemma sees {T:I→A→ℂ}(F:Cyl A ℂ)(h:Still F.val)(he:∀ i j,star (T i j)=T i j): Still (shade T F):= by
   intro l; induction l generalizing F with| nil=>exact h []| cons a l ih=> obtain ⟨s,hs⟩:=fromCyl F; rw [deriv_lum _ _ _ hs,star_sum]; exact Finset.sum_congr rfl (fun i _=> by simp [ih (enter i F) (h.D _),he])
lemma passes (r:A→I)(F:Cyl A ℂ)(h:Still F.val): Still (Ferry r F).val:= sees F h (fun i j=> by simp [way,apply_ite])

lemma charges (r:A→ℂ)(hr:∀ i,star (r i)=r i)(h:Still F): Still (rent r F):= by
    intro l; have he : star (l.map r).prod=(l.map r).prod:= by induction l with| nil=> simp| cons i l ih=> simp [ih,hr];
    simp only [rent, star_mul',h l,he]
end Still
end YM.MS.Koszul
