import YM.FormalOPE.RG10.StationaryMarks.Creed
/-!
 # Realizing cost schedules by insertions (elementary combinatorics)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {I J:Type}[Fintype I][Fintype J]
variable (P:ChartRatio G)(U: Survey G I J) (w:J→ℝ→ℝ)(O:Spending G I)
namespace Survey
-- real loss
 def adjusted (t:ℝ)(u:Configuration G I): ℝ:= ∑ j,w j t * U.field j u
 def spike (t:ℝ)(x:Configuration G I):= (∑ i, Tracks.rate (w i) (U.w i) t * U.field i x) / t
 def burden {k:ℕ}(e:Fin k→J)(t:ℝ):= (k.factorial:ℝ)⁻¹*(∏ i, Tracks.rate (w (e i)) (U.w (e i)) t)*(t⁻¹)^k
 def individual {k:ℕ}(e:Fin k→J)(t:ℝ): ℝ:= U.burden w e t * journal U.target (U.readMarks O e) t
 def advanced (t:ℝ): ℝ:= journal (U.adjusted w t) O t
 def partialAt (k:ℕ): ℝ→ℝ:= ∑ i∈Finset.range (k+1), ∑ e:Fin i→J, U.individual w O e

omit [Fintype I] in
lemma spike_rate {t:ℝ}(ht: t≠0)(x): U.spike w t x=(U.target x - U.adjusted w t x)/t^2 := by
 unfold spike Tracks.rate target adjusted; rw [← Finset.sum_sub_distrib,Finset.sum_div,Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; field_simp

 def referenceCharge (k:ℕ)(z:ℝ) := ∑ i∈Finset.range (k+1), z^i/(i.factorial:ℝ) -- t unused
 def rubber (k:ℕ)(t:ℝ)(x) := referenceCharge k (U.spike w t x)

omit [Fintype I] in
lemma singleRubber (k:ℕ)(t:ℝ)(x) : O x * ((U.spike w t x)^k/(k.factorial:ℝ))= ∑ e:Fin k→J,U.burden w e t * (U.readMarks O e) x:= by
 rw [spike,div_pow,div_eq_mul_inv _ (t^k), Fintype.sum_pow,Finset.sum_mul,Finset.sum_div,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
 unfold readMarks burden; simp_rw [Finset.prod_mul_distrib,Pi.mul_apply,Finset.prod_apply]; rw [div_eq_mul_inv,inv_pow]; ring
omit [Fintype I] in
lemma rubber_stamp (k:ℕ)(t:ℝ)(x): dollar U.target O t x * U.rubber w k t x= ∑ i∈Finset.range (k+1), ∑ e:Fin i→J,U.burden w e t * dollar U.target (U.readMarks O e) t x:= by
 unfold rubber referenceCharge; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
 unfold dollar; conv_lhs => rw [mul_right_comm, singleRubber,Finset.sum_mul]
 apply Finset.sum_congr rfl; intro _ _; ring
variable {P U w O}
namespace Ready
variable (R: U.Ready) (h:Curtain O)
include R h in
lemma income (k:ℕ)(t:ℝ)(w): U.partialAt w O k t = scale G I t * ∫ u,dollar U.target O t u * U.rubber w k t u ∂physical G I:= by
 let f (i:ℕ)(v:Fin i→J)(x):= U.burden w v t * dollar U.target (U.readMarks O v) t x
 have hi i v: Integrable (f i v) (physical G I):=(endowment R.entire (R.readings _ h _) _).const_mul _
 simp_rw [rubber_stamp]; change _=scale G I t * ∫ u, (∑ i∈Finset.range (k+1),∑ v:Fin i→J,f i v u) ∂physical G I
 have h₁ (i:ℕ): Integrable (fun u=> ∑ v:Fin i→J,f i v u) (physical G I) := integrable_finsetSum _ (fun v _=> hi _ v)
 simp_rw [integral_finsetSum _ (fun i _=>h₁ i),integral_finsetSum _ (fun i _=> hi _ i),partialAt,Finset.sum_apply,Finset.mul_sum]; refine Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun v hv=>?_)); unfold individual journal f; rw [integral_const_mul]; ring
include R h in
lemma plate {k:ℕ}(e:Fin k→J)(hs:∀ j,Tracks (w j) (U.w j))(L:LocalRatio P): Tracks (U.individual w O e) (U.print P O e):= by
 have h₀: Tracks (journal U.target (U.readMarks O e)) (PowerSeries.mk (summing P U.target (U.readMarks O e))):= by rw [Tracks,Tracks.asTerm]; exact base L R.entire (R.readings k h e)
 have hv: Waits (0+2*k) (U.readMarks O e):= R.forecast 0 k (waits_no h) e
 convert Tracks.mul (Tracks.const ((k.factorial:ℝ)⁻¹)) (Tracks.mul (Tracks.prod Finset.univ _ _ (fun (i:Fin k) hi=> Tracks.start (hs (e i)))) (Tracks.clipped h₀ k (by
   intro i hi; rw [Tracks.asTerm]; exact lower L U.target (R.readings k h e) hv (by omega)))) using 1
 · funext i; simp [individual,burden, Finset.prod_apply]; ring
 rfl -- maybe
include R h in
lemma allPlates (k:ℕ)(hs:∀ j,Tracks (w j) (U.w j))(L:LocalRatio P): Tracks (U.partialAt w O k) (U.truncation P O k):= Tracks.sum _ _ _ (fun i _=> Tracks.sum (Finset.univ (α:=Fin i→J)) _ _ (fun v _=> R.plate h v hs L))
end Ready
end Survey
end YM.FormalOPE.RG10.StationaryMarks
