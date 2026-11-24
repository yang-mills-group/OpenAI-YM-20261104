import YM.Frontier6.Bouquet.Meter.Mixed

/-!
# Curtain of local prescriptions

Isolate any series of partitions of the left group; any disjoint recursion
 supported on the right sees exactly that value. (At fixed positive UV suppressing
 lengths.) -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q :Ensemble} (h:Free P Q)
namespace Curtains
set_option quotPrecheck false
local notation "L"=> merge h
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
    {x: Seats (merge h)} {f:Full (fiber (merge h))} {H:Patron S (merge h) Y}
abbrev select (U:Finset (Down P)) (x:Seats P)(H:Patron S P Y) (f:Full (fiber P)) : Y:= ∑ i∈U, branch K A T i.property x H f
def onLeft (U:Finset (Down P)) : Finset (Down (merge h)):= (U.product Finset.univ).map (twineEquiv h).toEmbedding
def regard (H:Patron S (merge h) Y)(x:Seats (merge h))(f:Full (fiber (merge h)))(U: Finset (Down P))(l:Down Q)(p:Trip A l.val)(y:Margin Q l.val) := select K A T U (preL h x) (following K A h p l.property x H y) (received A T h f p y)
variable {B:Balcony (merge h)}(hf:Fair f B x)(hh:Gentle H B) (U:Finset (Down P))
include hf hh
lemma many_part (q:Down Q)(i:Down P) : branch K A T (twine h (i,q)).property x H f=
    ∑ p:Trip A q.val, ∫ z:Margin Q q.val, branch K A T i.property (preL h x) (following K A h p q.property x H z) (received A T h f p z):=by
    let u : Trip A i.val × Trip A q.val ≃ Trip A (twine h (i,q)).val:=palette A (h.refines i.property q.property); let a (r:Trip A (twine h (i,q)).val):= essay K A T (twine h (i,q)).property x H r f; change ∑ r,a r=_; rw [← Equiv.sum_comp u a,Fintype.sum_prod_type_right]; -- inspect order
    refine sum_congr rfl (fun p _=>?_); unfold branch; rw [integral_finsetSum]; rotate_left
    · exact fun j _=>mixes K A T h j p i.property q.property hf hh
    exact sum_congr rfl (fun j _=> essays_merge K A T h j p i.property q.property (he:=h.refines i.property q.property) hf hh)
lemma integrable_part (q:Down Q)(i:Down P)(p:Trip A q.val): Integrable (fun z:Margin Q q.val=> branch K A T i.property (preL h x) (following K A h p q.property x H z) (received A T h f p z)):= integrable_finsetSum _ (fun j _=>mixes K A T h j p i.property q.property hf hh)
lemma audience (p:Down Q)(q:Trip A p.val): Integrable (regard K A T h H x f U p q):= integrable_finsetSum U (fun i _=> integrable_part K A T h hf hh p i q)
lemma program : select K A T (onLeft h U) x H f=∑ l:Down Q,∑ p:Trip A l.val,∫ z, regard K A T h H x f U l p z:=by
    unfold select onLeft; rw [Finset.sum_map,]; let G(i):= branch K A T (twine h i).property x H f; change ∑ t∈ (U ×ˢ Finset.univ), G t=_; rw [Finset.sum_product_right]; -- test order
    refine sum_congr rfl fun i _=>?_ ;  dsimp only [G]; simp_rw [many_part K A T h hf hh]; rw [sum_comm]; refine sum_congr rfl (fun p _=> ?_); unfold regard select; exact (integral_finsetSum _ (fun j hj=> integrable_part K A T h hf hh i j p)).symm  -- fill
end Curtains
end YM.Frontier6.Bouquet
