import YM.Frontier6.Bouquet.Core.Seesaw
import YM.Frontier6.Bouquet.Patron.TrainShift
/-!
# Coincidence terms binding in one-slot seats
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q:Ensemble}
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
lemma final_zero_dim : dim (Margin P P)=0:=by have hh:=margin_rank (le_refl P); omega
lemma p_volume_zero {P:Place}[FiniteDimensional ℝ P](he:dim P=0): (volume:Measure P)=Measure.dirac 0:=by
    let u:= Fin (Module.finrank ℝ P); letI:IsEmpty (Fin (Module.finrank ℝ P)):= by change Module.finrank ℝ P=0 at he; rw [he];infer_instance
    let f:= (harp P).repr; rw [← f.symm.measurePreserving.map_eq, volume_euclideanSpace_eq_dirac, Measure.map_dirac' f.symm.measurePreserving.measurable, map_zero]
lemma pointIntegral {X:Place}[FiniteDimensional ℝ X] (he:dim X=0)(f:X→Y): (∫ x:X,f x)=f 0:=by rw [p_volume_zero he, integral_dirac]
-- evaluating coincidence with no split
lemma root_stamp (x:Seats P)(H:Patron S P Y)(f:Full (fiber P))(p:Trip A P): essay K A T (le_refl P) x H p f=train _ (costsD A p) f 0 • H (togetherS K A p x):=by
    unfold essay; rw [pointIntegral final_zero_dim,ink,map_zero, T.film_here,transit_self,convey_at,garland_alone]
variable (p:Pod)
abbrev me (p:Pod):only p:=default
lemma unique_full {P:Ensemble} (p:P)(he:∀ i:P,i=p) (H: Patron S P Y)(v:Program S P): H v=H.toLinearMap (fun _=>0) p (v p):=by
    apply congr_arg H; ext1 i; rw [he i, Function.update_self]
lemma unique_hears (H:Patron S (only p) Y): H= hearing p (H.toLinearMap (fun _=>0) (me p)):=by ext1 v; rw [hearing_at]; exact unique_full (me p) (fun i=> Subsingleton.elim ..) _ _
def isolation (p:Pod) : Trip A (only p) ≃ (A p).Code:= Equiv.piUnique (fun i:only p=> (A i.val).Code)
lemma finest (x: Seats (only p))(H: Patron S (only p) Y)(f:Full (fiber (only p))): marble K A T (me p) x H f=
    ∑ a:(A p).Code, train (fiber (only p)) ((A p).course a) f 0 • H.toLinearMap (fun _=>0) (me p) (let v:=(A p).payment a; Tale.suit K (x (me p)) v.fst v.snd):=by
    rw [marble_one]; unfold branch; rw [← Equiv.sum_comp (isolation A p)]; apply sum_congr rfl; intro i _; rw [root_stamp];
    have he: costsD A i=(A p).course (isolation A p i):=by unfold costsD; rw [Fintype.sum_unique];rfl -- defeq
    rw [he]; exact congr_arg (_ • ·) (unique_full (me p) (fun i=> Subsingleton.elim ..) H _)
end YM.Frontier6.Bouquet
