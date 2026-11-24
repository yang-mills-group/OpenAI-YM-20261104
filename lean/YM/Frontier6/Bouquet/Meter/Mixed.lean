import YM.Frontier6.Bouquet.Meter.Inkling

/-! Writing the fixed-budget identity with disjoint groups (projection moment
 reuse for the other-parameter integration). -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R U:Ensemble} (h:Free P Q)
set_option quotPrecheck false
local notation "㏑"=> fiber (Ensemble.merge h)
variable (p:Trip A R)(q: Trip A U) {he: Free R U}(hR:R≤P)(hU:U ≤ Q)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y] [CompleteSpace Y]
    (x: Seats (merge h)) (f:Full (fiber (merge h))) (H:Patron S (merge h) Y)
abbrev following (v:Margin Q U):= follow h H (garland hU (togetherS K A q (transit hU (preR h x) v)))
def mixed (v:Margin Q U) := essay K A T hR (preL h x) (following K A h q hU x H v) p (received A T h f q v)
section
include he
-- ensure orientation of Fubini so y side macro first
local notation "Tq"=> adds_macro h (K:=he) hR hU
lemma patient (u:Margin P R)(v:Margin Q U): ink K A T (merge_le h (he:=he) hR hU) x H (palette A he (p,q)) f ((Tq).symm.together (v,u))=
    ink K A T hR (preL h x) (following K A h q hU x H v) p (received A T h f q v) u:=by
    unfold ink; rw [show (Tq).symm.together (v,u)=(Tq).together (u,v) from Subtype.ext (add_comm ..), impression A T h f p q hR hU u v]; exact congr_arg (_ • ·) (follow_with K A h p q hR hU H x u v) -- annotate
variable {x f H}{B:Balcony (merge h)}(hx:Fair f B x)(hY:Gentle H B)
include hx hY
lemma essays_merge : essay K A T (merge_le h (he:=he) hR hU) x H (palette A he (p,q)) f=∫ z: Margin Q U, mixed K A T h p q hR hU x f H z:=by
    unfold essay mixed; rw [(Tq).symm.integral (further K A T (merge_le h hR hU (he:=he)) H _ hY hx)]; simp_rw [patient K A T h p q hR hU]; rfl
-- integrability of cumulated vertical slice term (without continuity hypot outside geometry)
omit he
lemma mixes : Integrable (mixed K A T h p q hR hU x f H):=by
    let he:= h.refines hR hU; have hz:= (adds_macro h (K:=he) hR hU).symm.integrable (further K A T (merge_le h hR hU (he:=he)) H (palette A he (p,q)) hY hx); have hv:=hz.integral_prod_left;
    convert! hv using 1; ext1 z; unfold mixed essay; simp_rw [patient K A T h p q hR hU]; -- order
end
end YM.Frontier6.Bouquet
