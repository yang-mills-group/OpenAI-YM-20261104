import YM.Frontier6.Bouquet.Meter.Presence

/-!
# Explicit common-refinement identity in the finite joint cutoff version

Keep the smaller-aperture test `film` in this equality. It can be removed if
 all intergroup gaps are large compared with the regulator. Anchors moving only
 through independent macro frames as throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I V:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R:Ensemble} (h:P ≤ Q)(g:Q≤R)
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
    (p:Trip A P) {x:Seats R} {B:Balcony R}{H:Patron S R Y}{f:Full (fiber R)}(he:Gentle H B)(hf:Fair f B x)
set_option quotPrecheck false
local notation "M"=>bridges (plan_sub h) (plan_sub g)
def slit (z:Margin R Q) (f:Full (fiber R)) : Full (fiber Q):= restrictS (plan_sub g) (insideCL loft_le z) (T.film R Q f)
set_option maxHeartbeats 600000 in
lemma ink_fold (z:Margin R Q)(y:Margin Q P) : ink K A T (h.trans g) x H p f ((M).together (z,y))= ink K A T h (transit g x z) (convey g H) p (slit T g z f) y:=by
    unfold ink; rw [transits h y g x z,conveys h g]; unfold slit
    rw [← T.rectified h g z f, ← train_restricted (plan_sub g) _ _ (costsD A p) (fun i hi=> plan_sub h (courses_in A p i hi))]
    rw [restrict_at]
    let heq : insideCL (show Margin R P ≤fiber R from loft_le) ((M).together (z,y))= forward (plan_sub g) (insideCL loft_le z) (insideCL (show Margin Q P≤fiber Q from loft_le) y):=Subtype.ext rfl
    rw [heq]
include he hf
lemma essay_fold : essay K A T (h.trans g) x H p f=∫ z:Margin R Q, essay K A T h (transit g x z) (convey g H) p (slit T g z f):=by
    unfold essay; rw [(M).integral (further K A T (h.trans g) H p he hf)]; simp_rw [ink_fold K A T h g]
lemma essay_folding [CompleteSpace Y] : Integrable (fun z:Margin R Q=> essay K A T h (transit g x z) (convey g H) p (slit T g z f)):=by
    have hz:= (M).integrable (further K A T (h.trans g) H p he hf); have hv:=hz.integral_prod_left; convert hv using 1; ext1 z; unfold essay; simp_rw [← ink_fold]
lemma crust : branch K A T (h.trans g) x H f=∫ z:Margin R Q, branch K A T h (transit g x z) (convey g H) (slit T g z f):=by
    by_cases hu:CompleteSpace Y; swap; simp [branch,essay,integral,hu]
    unfold branch; simp_rw [essay_fold K A T h g _ he hf]; rw [integral_finset_sum]; exact fun i _=> essay_folding K A T h g _ he hf
lemma branch_folding : Integrable (fun z:Margin R Q=> branch K A T h (transit g x z) (convey g H) (slit T g z f)):=by
    by_cases hu:CompleteSpace Y; swap; simp [branch,essay,integral,hu]
    unfold branch; exact integrable_finsetSum _ (fun i _=> essay_folding K A T h g i he hf)
end YM.Frontier6.Bouquet
