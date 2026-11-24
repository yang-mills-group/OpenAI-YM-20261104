import YM.Frontier6.Bouquet.Truth.Schedule

/-! Teller dependency is inner-portions only; not tailoring to the pairing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(T:Veins){P Q:Ensemble}{A B:Teller S}
set_option quotPrecheck false
-- general reindex by pack: possible later need orientation distinct transforms, separate
section
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable {p:Pod}
def reaxis {A B:Issue S p}(h:A=B): A.Code ≃ B.Code:=by subst B; exact Equiv.refl _
lemma reaxis_payment {A B:Issue S p}(h:A=B)(x:A.Code): A.payment x=B.payment (reaxis h x):=by subst B;rfl
lemma reaxis_course {A B:Issue S p}(h:A=B)(x:A.Code): A.course x=B.course (reaxis h x):=by subst B;rfl
-- proof used as casts at dot
lemma turns (h:P≤Q) (he:∀ p∈ P.choose,A p=B p) (x:Seats Q)(H:Patron S Q Y)(f:Full (fiber Q)): branch K A T h x H f= branch K B T h x H f:=by
    let e:= Equiv.piCongrRight (fun p:P=> reaxis (he p p.property)); unfold branch; rw [← Equiv.sum_comp e]; refine Finset.sum_congr rfl fun i _=>?_
    have hi: costsD A i=costsD B (e i):= Finset.sum_congr rfl (fun p _=> reaxis_course (he p p.property) _)
    unfold essay ink; rw [hi,show togetherS K A i=togetherS K B (e i) from ?_]
    ext1 x; ext1 p; unfold togetherS; rw [reaxis_payment (he p p.property) (i p)]; rfl
lemma proper_deeper (p:Pod)(i:Down (only p))(hi:i∈ proper (only p) p){q:Pod}(hq:q∈ i.val.choose): q < p:=by
    have he : q≤p:= inside i.property (⟨q,hq⟩:i.val)|>.trans (only_mem.mp (assign i.property ⟨q,hq⟩).property).le; exact lt_of_le_of_ne he (fun h=> (Finset.mem_filter.mp hi).2 (h ▸ hq))
lemma select_only (p:Pod)(he:∀ q,q<p→ A q=B q)(x:Seats (only p))(H: Patron S (only p) Y)(f:Full (fiber (only p))): pollen K A T (me p) x H f= pollen K B T (me p) x H f:= by exact Finset.sum_congr rfl (fun i hi=> turns K T i.property (fun j hj=> he j (proper_deeper p i hi hj)) x H f)
lemma bills_only (p:Pod)(he:∀ q,q<p→ A q=B q)(d: Slot→ℕ)(s:ℝ) : partNumber K A T d p s= partNumber K B T d p s:=by
    have hh(w:ℕ): Expenses K A T p w= Expenses K B T p w:=funext fun _=>select_only K T p he _ _ _
    unfold partNumber; congr; ext1 v; rw [hh]
end
end YM.Frontier6.Bouquet
