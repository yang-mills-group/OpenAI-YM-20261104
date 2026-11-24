import YM.FormalOPE.RG10.StationaryMarks.Follow
/-!
 # canonical survey report
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
variable {P:ChartRatio G}{U V:Survey G I J}{O: Spending G I}{w:J→ℝ→ℝ}
-- use field notation `denom/power`
 def ratecard (U:Survey G I J)(P:ChartRatio G)(O:Spending G I): PowerSeries ℝ := U.imprint P O*(U.imprint P 1)⁻¹
namespace Ready
variable (L:LocalRatio P)(R:Ready U)(h:Curtain O)
include L R
lemma mark : constantCoeff (U.imprint P 1)≠0:= by rw [← coeff_zero_eq_constantCoeff_apply]; exact ne_of_eq_of_ne (U.precise 1 P) (upfront L R.entire).ne'
lemma use : U.imprint P 1 * (U.imprint P 1)⁻¹=1:= PowerSeries.mul_inv_cancel _ (R.mark L)
include h in
lemma unitized (hs:∀ i, Tracks (w i) (U.w i)):
 Tracks (U.advanced w O / U.advanced w 1) (U.ratecard P O):= by
 let v:= R.validated Inherit.unit hs L; have he:= (R.validated h hs L).quotient v (show term (U.imprint P 1) 0 ≠ 0 from by simpa [term] using R.mark L); simpa only [divide, Tracks.asSeries] using! he

include h in
lemma inertia {l:ℕ}(hv:Waits l O) {j:ℕ}(hj:j<l): term (U.ratecard P O) j=0:= by
 unfold term ratecard; rw [coeff_mul]; apply Finset.sum_eq_zero; intro i hi; have hi:= Finset.mem_antidiagonal.mp hi; rw [show coeff i.1 (U.imprint P O)=0 from R.delay l L h hv (by omega),zero_mul]
lemma feature (hv:O=1): U.ratecard P O=1:= by rw [hv]; exact R.use L -- no h needed
include h in
lemma belongs {n l:ℕ}(H: Continued n U V)(hv:Waits l O): Through (l+n) (U.ratecard P O) (V.ratecard P O):= by
 have hw:= H.keep R Inherit.unit (l:=0) (waits_no Inherit.unit) L -- show spends.O:
 have ht: Through n (U.imprint P 1) (V.imprint P 1):= by simpa using hw
 have hr:=ht.invAlready (R.use L) ((H.possible R).use L)
 intro i hi; unfold ratecard; simp_rw [coeff_mul]; apply Finset.sum_congr rfl; intro e hq; have hq:= Finset.mem_antidiagonal.mp hq; rw [← H.keep R h hv L _ (by omega)]
 by_cases he:e.2≤ n
 · rw [hr e.2 he]
 rw [show coeff e.1 (U.imprint P O) =0 from R.delay l L h hv (by omega)]; ring
include h in
lemma chopped {l:ℕ}(hs:∀ i, Tracks (w i) (U.w i))(hv:Waits l O):
 Tracks (fun t=> t⁻¹ ^ l * ((U.advanced w O / U.advanced w 1) t)) (Tracks.deduct (U.ratecard P O) l):= Tracks.clipped (R.unitized L h hs) _ fun _ hi=> R.inertia L h hv hi
include h in
lemma exactly {n l:ℕ}(H: Continued n U V)(hv:Waits l O):Through n (Tracks.deduct (U.ratecard P O) l) (Tracks.deduct (V.ratecard P O) l):= by intro i hi; unfold Tracks.deduct; rw [coeff_mk,coeff_mk]; exact R.belongs L h H hv _ (by omega)
end Ready
end Survey
end YM.FormalOPE.RG10.StationaryMarks
