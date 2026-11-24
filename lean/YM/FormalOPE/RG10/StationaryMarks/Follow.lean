import YM.FormalOPE.RG10.StationaryMarks.Weather
import YM.FormalOPE.RG10.Restriction
/-!
 # coherent system through requested order, incl shoulder paid by radial test valuation
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I J:Type}[Fintype I][Fintype J]
namespace Survey
variable {P:ChartRatio G}{U V:Survey G I J} {O:Spending G I}{l n:ℕ}
-- `follows`
structure Continued (n:ℕ) (U V:Survey G I J) : Prop where
 convention : U.field=V.field
 weights i : Through n (U.w i) (V.w i)
namespace Continued
variable (h: Continued n U V)
include h
omit [Fintype I] in
lemma consistency : U.target=V.target:= by funext x; unfold target; simp_rw [h.convention]; exact Finset.sum_congr rfl (fun i _=> by unfold term; rw [h.weights i 0 (Nat.zero_le _)])
lemma possible (H:Ready U): Ready V where
 sincere := h.convention ▸ H.sincere
 localAll:= h.convention ▸ H.localAll
 lead_pos i:= by rw [show term (V.w i) 0= term (U.w i) 0 from (h.weights i 0 (Nat.zero_le _)).symm]; exact H.lead_pos i
 entire:= h.consistency ▸ H.entire
omit h in
private lemma prods {R:Type}[CommSemiring R] {I:Type*} {A B : I→ PowerSeries R}(s:Finset I)(h:∀ i∈s,Through n (A i) (B i)): Through n (∏ i∈s,A i) (∏ i∈s,B i):= by induction s using Finset.induction with
                                                                                                                                                                                                   | empty=> simp only [Finset.prod_empty]; exact Through.refl _
                                                                                                                                                                                                   | insert=> rw [Finset.prod_insert (by assumption), Finset.prod_insert (by assumption)]; rename_i i s he ih; exact (h i (by simp)).mul (ih (fun j hj=> h j (by simp [hj])))
lemma plate (C:Ready U)(F:Curtain O)(H:Waits l O)(L:LocalRatio P) {k}(e:Fin k→J) : Through (l+n) (U.print P O e) (V.print P O e) := by
 have hv: U.basePrint P O e=V.basePrint P O e:= by unfold basePrint readMarks; rw [h.consistency,h.convention]
 by_cases ho:k=0
 · subst k; rw [none_print, none_print,h.consistency]; exact Through.refl _
 unfold print; apply Through.mul (Through.refl _)
 rw [← hv]; intro j hj; rw [coeff_mul,coeff_mul]; refine Finset.sum_congr rfl fun a ha=>?_
 have ha:=Finset.mem_antidiagonal.mp ha
 by_cases hz: a.2< l+k
 · rw [C.floor l k L F H e _ hz |> (show term (U.basePrint P O e) a.2= _ → coeff a.2 (U.basePrint P O e)= _ from id),mul_zero,mul_zero] -- pipe syntax
 have he : a.1 < n:= by omega
 rw [(prods (A:=fun i=> Tracks.shadow (U.w (e i))) (B:=fun i=> Tracks.shadow (V.w (e i))) (Finset.univ) (fun i _ g hg=> show PowerSeries.coeff g _= _ from ?_)) a.1 (le_refl _)]
 unfold Tracks.shadow Tracks.deduct; simp_rw [map_neg, coeff_mk]; unfold term; rw [h.weights _ (1+g) (by omega)]
lemma keep (C:Ready U)(F:Curtain O)(H:Waits l O)(L:LocalRatio P) : Through (l+n) (U.imprint P O) (V.imprint P O):= by
 intro i hi; unfold imprint; simp_rw [coeff_mk, truncation, press, term,map_sum]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>?_ ; exact h.plate C F H L y i hi
end Continued
end Survey
end YM.FormalOPE.RG10.StationaryMarks
