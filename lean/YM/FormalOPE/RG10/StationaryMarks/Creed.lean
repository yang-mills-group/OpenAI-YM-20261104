import YM.FormalOPE.RG10.StationaryMarks.Vary
/-!
 # variable cost scheduling with genuinely independent PowerSeries for each slot

 Exponent coefficients are reconstructed by pressing powers of schedule prices as
 EXTRA marked factors on G.El variables inside unnormalized integral. No clock
 ratio regularity beyond power series. No comparison estimate for physical resetting.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}{I J:Type}[Fintype I][Fintype J]
-- Schedule from any real positive λ slots.
structure Survey (G:Gauge)(I J:Type) where
 field : J→ Spending G I
 w : J→ PowerSeries ℝ

variable (U: Survey G I J)
namespace Survey
 def target (x:Configuration G I) := ∑ i, term (U.w i) 0 * U.field i x
structure Ready : Prop where
 sincere : ∀ i,Component (U.field i)
 localAll i : Curtain (U.field i)
 lead_pos i : 0 < term (U.w i) 0
 entire : Credential U.target

variable (P:ChartRatio G) (O:Spending G I) (l k : ℕ)
-- finite ordered tuple, not sets
 def readMarks {k} (e:Fin k→ J) : Spending G I:= O * ∏ i, U.field (e i)
-- series after dividing base observable integral by t^p
 def basePrint {k:ℕ} (e:Fin k→J) : PowerSeries ℝ:= Tracks.deduct (PowerSeries.mk (summing P U.target (U.readMarks O e))) k
 def print {k:ℕ} (e:Fin k→J): PowerSeries ℝ:= C ((k.factorial:ℝ)⁻¹) * ((∏ i, Tracks.shadow (U.w (e i))) * U.basePrint P O e) -- binding C and inverse parentheses?
 def press (k: ℕ) : PowerSeries ℝ:= ∑ i: Fin k→J,U.print P O i
 def truncation (n:ℕ) : PowerSeries ℝ:= ∑ i∈ Finset.range (n+1), U.press P O i
 def imprint : PowerSeries ℝ:= PowerSeries.mk (fun n=> term (U.truncation P O n) n)
-- conventional coefficients. delta-power threshold proven below.Attribute.
variable {U}
namespace Ready
variable (R: Ready U)
include R
lemma readings {O:Spending G I}(h:Curtain O)(e:Fin k→J): Curtain (U.readMarks O e):= h.mul (Curtain.gather Finset.univ (fun i=> U.field (e i)) (fun _ _=> R.localAll _))
lemma forecast {O:Spending G I}(hw: Waits l O)(e: Fin k→J): Waits (l+2*k) (U.readMarks O e):= waits_mul hw (waits_cargo (fun i=> U.field (e i)) (fun i=> waits_high (R.sincere (e i))))
variable {P O} (L:LocalRatio P) (h:Curtain O)
include h L
lemma floor (hw:Waits l O)(e:Fin k→J)(j:ℕ)(hj:j<l+k) : term (U.basePrint P O e) j=0:= by
 unfold basePrint Tracks.deduct; rw [Tracks.asTerm, Tracks.asTerm]; exact lower L U.target (R.readings k h e) (R.forecast l k hw e) (by omega)
omit R h L in
private lemma reserve {A B : PowerSeries ℝ}{k:ℕ}(h:∀ i<k,term B i=0)(j:ℕ)(hj:j<k) : term (A*B) j=0:= by unfold term; rw [coeff_mul]; apply Finset.sum_eq_zero; intro i hi; rw [show coeff i.2 B = 0 from h _ (by have ht:=Finset.mem_antidiagonal.mp hi; omega),mul_zero]
lemma allFloor (hw:Waits l O)(e:Fin k→J)(j:ℕ)(hj:j<l+k) : term (U.print P O e) j=0:= reserve (reserve (R.floor l k L h hw e)) j hj -- args
lemma subfloor (hw:Waits l O)(k:ℕ)(j:ℕ)(hj:j<l+k): term (U.press P O k) j=0:= by unfold press term; rw [map_sum]; exact Finset.sum_eq_zero fun i _=> R.allFloor l k L h hw _ j hj
-- available after normalizing within frames; coincident etc.
lemma pre_stall (j:ℕ)(n:ℕ)(hj:j ≤ n): term (U.imprint P O) j= term (U.truncation P O n) j:= by
 rw [imprint, Tracks.asTerm]; unfold truncation term; rw [map_sum,map_sum]; apply Finset.sum_subset (Finset.range_mono (by omega)); intro e hv hi; simp only [Finset.mem_range, not_lt] at hi; exact R.subfloor 0 L h (waits_no h) e j (by omega)
lemma delay (hw:Waits l O){j:ℕ}(hh:j<l):term (U.imprint P O) j=0:= by rw [R.pre_stall L h j j le_rfl,term,truncation,map_sum]; exact Finset.sum_eq_zero fun i _=> R.subfloor l L h hw _ j (by omega)
end Ready
lemma none_print (P:ChartRatio G)(U:Survey G I J) (e:Fin 0→J): U.print P O e = PowerSeries.mk (summing P U.target O):= by
 unfold print basePrint readMarks; simp [Tracks.deduct]
lemma precise (P:ChartRatio G)(U:Survey G I J): term (U.imprint P O) 0= summing P U.target O 0:= by
 rw [imprint, Tracks.asTerm,truncation]; simp [press,none_print,Tracks.asTerm] -- Empty Fintype
end Survey
end YM.FormalOPE.RG10.StationaryMarks
