import YM.Frontier6.Bouquet.Core.Specs

/-! Lifting the coincidence/payroll identity through the matching *right*
 panel principle (both expansions use the same test/cutoff transits). -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R:Ensemble} (i:P)(d:Slot→ℕ)(s:ℝ)
lemma atOnly (p:Pod)(i:only p)(w:i.val.Horizon d): atBook i d s w=Normal.portion s (i.val.track d w):=by
   obtain rfl:i=(default:only p):= Subsingleton.elim ..; ext1 x
   let a:fiber (only p)≤fiber (only p):=le_rfl; let W:= (default:(only p)).val.track d w; have hy(g:Full (fiber (only p))): atLoft a 0 g=g:=by rw [atLoft,map_zero,restrict_zero]
   change page a s W x=_; nth_rw 1 [← hy (page a s W x)]; rw [mechanism,hy]
lemma moves_only {p:Pod}(he:Free (only p) Q)(i:only p)(w:i.val.Horizon d): Elevator (merged he).lft (atBook i d s w) (atBook (germL he i) d s w):=by
   obtain rfl:i=(default:only p):= Subsingleton.elim ..; rw [atOnly]; exact ⟨pages_mobile _ _ _,fun f z=> mechanism _ f _ _ _⟩ -- args?
lemma shares {p:Pod}(he:Free (only p) Q)(i:only p)(w:i.val.Horizon d)(f:Full (fiber (merge he))) (R:Down Q)(q:Trip A R.val)(y:Margin Q R.val): received A T he (atBook (germL he i) d s w f) q y= atBook i d s w (received A T he f q y):= transmission A T he f q _ _ (moves_only d s he i w) R.property _
variable (h:Free P Q)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
    (x:Seats (merge h))(H: Patron S (merge h) Y)(f:Full (fiber (merge h)))
lemma keys_commute (w:ℕ)(A:Program S Q): follow h (key K H (germL h i) x w) A= key K (follow h H A) i (preL h x) w := transactions_left h i H A _
section
variable {p:Pod} (h:Free (only p) Q) (i:only p) {x: Seats (merge h)} {H: Patron S (merge h) Y}{f: Full (fiber (merge h))}
variable (he: Payroll p K d s A T)(hh:Welcomes H x f)(hx:∀ w:i.val.Horizon d, Welcomes (key K H (germL h i) x w) x (atBook (germL h i) d s w f))
include he hh hx
lemma lifted : marble K A T (germL h i) x H f= -(∑ w:i.val.Horizon d,pollen K A T (germL h i) x (key K H (germL h i) x w) (atBook (germL h i) d s w f)):=by
    obtain ⟨B,hB,hA⟩:= hh; let W:= i.val.Horizon d; let y(w:W):=key K H (germL h i) x w; let F(w:W):= atBook (germL h i) d s w f; choose D hD hF using hx; let U:= proper (only p) i.val; let Z:= coin (only p) i.val
    let S(l:Down Q)(a:Trip A l.val):= regard K A T h H x f Z l a
    let P(w:W)(l:Down Q)(a:Trip A l.val):=regard K A T h (y w) x (F w) U l a
    have hv(w:W): select K A T (onLeft h U) x (y w) (F w)=∑ l:Down Q,∑ a:Trip A l.val,∫ z,P w l a z:= Curtains.program K A T h (hF w) (hD w) U
    have hm(w:W)(l:Down Q)(a:Trip A l.val):Integrable (P w l a):= Curtains.audience K A T h (hF w) (hD w) U l a
    have hr(l:Down Q)(a:Trip A l.val)(z):S l a z= -∑ w:W,P w l a z:=by
       unfold P S regard following y F; simp_rw [keys_commute K i h, shares A T d s h i]; exact he (preL h x) _ _ i
    change select K A T (coin (merge h) i.val) x H f = -(∑ w:W,select K A T (proper (merge h) i.val) x (y w) (F w)); rw [pocket_coin (P:=only p) i h,pocket_proper (P:=only p) i h]; change select K A T (onLeft h Z) _ _ _= -(∑ w:W,select K A T (onLeft h U) _ (y w) (F w)); rw [Curtains.program K A T h hA hB]; simp_rw [hv]; change (∑ l:Down Q,∑ a:Trip A l.val,∫ z,S l a z)=_; rw [sum_comm (s:= (Finset.univ:Finset W))]; rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun l _=>?_ ; rw [sum_comm (s:= (Finset.univ:Finset W)),← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun a _=>?_ ; simp_rw [hr]; rw [integral_neg,integral_finsetSum]; exact fun i _=>hm i l a
end
end YM.Frontier6.Bouquet
