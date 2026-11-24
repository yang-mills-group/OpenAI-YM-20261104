import YM.Frontier6.Bouquet.Meter.Dormer
import YM.Frontier6.Bouquet.Patron.Knot

/-!
# Equivalences commute the forest counters in disjoint frontier positions
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R U:Ensemble} (h:Free P Q)
def palette : Trip A P × Trip A Q ≃ Trip A (merge h):= by
   let a (i:merge h):=(A i.val).Code
   exact (Equiv.sumPiEquivProdPi (fun i=>a (parts h i))).symm.trans (Equiv.piCongrLeft a (parts h))
section
variable (p: Trip A P)(q:Trip A Q) (x:Seats (merge h))
lemma palette_left (i:P) : palette A h (p,q) (germL h i) = p i:= Equiv.piCongrLeft_sumInl (fun x:merge h=> (A x.val).Code) (parts h) p q i -- args?
lemma palette_right (i:Q) : palette A h (p,q) (germR h i) = q i:= Equiv.piCongrLeft_sumInr (fun x:merge h=> (A x.val).Code) (parts h) p q i
lemma palette_score : costsD A (palette A h (p,q))=costsD A p+costsD A q:=by
   unfold costsD; rw [← Equiv.sum_comp (parts h) (fun i:merge h=> (A i.val).course (palette A h (p,q) i)), Fintype.sum_sum_type]; congr 1
   · exact sum_congr rfl fun i _=>congr_arg ((A (germL h i).val).course) (palette_left A h p q i)
   exact sum_congr rfl fun i _=> congr_arg ((A (germR h i).val).course) (palette_right A h p q i)
lemma paletteL : togetherS K A (palette A h (p,q)) x ∘ germL h=togetherS K A p (x ∘ germL h):=by funext i; unfold Function.comp togetherS; rw [palette_left]; rfl
lemma paletteR : togetherS K A (palette A h (p,q)) x ∘ germR h=togetherS K A q (x ∘ germR h):=by funext i; unfold Function.comp togetherS; rw [palette_right]; rfl
end
variable (p:Trip A R)(q:Trip A U) {N:Free R U}(hP: R≤P)(hQ:U ≤ Q)
variable {Y:Type} [NormedAddCommGroup Y][NormedSpace ℂ Y]
    (H: Patron S (merge h) Y)(x: Seats (merge h))
lemma follow_with (u:Margin P R)(v:Margin Q U):
   let s:= (adds_macro h (K:=N) hP hQ).together (u,v)
   let M:= transit (merge_le h (he:=N) hP hQ) x s
   convey (merge_le h (he:=N) hP hQ) H (togetherS K A (palette A N (p,q)) M) = convey hP (follow h H (garland hQ (togetherS K A q (transit hQ (preR h x) v)))) (togetherS K A p (transit hP (preL h x) u)):=by
    intro s M; simp_rw [convey_at,follow_at]; apply congr_arg H; rw [← hear_mix h (garland _ _)]; -- may rewrite all, use explicit
    rw [converse_left h hP hQ N, converse_right h hP hQ N, paletteL,paletteR,show M ∘ germR N = _ from transit_right h hP hQ u v, show M ∘ germL N = _ from transit_left h hP hQ u v]
end YM.Frontier6.Bouquet
