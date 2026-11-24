import YM.Integration.WilsonConditionalTaylorThermalOddInsertion
import YM.Integration.WilsonConditionalTaylorThermalCentralDivision
import YM.Integration.WilsonConditionalTaylorThermalMixedQuotient

/-! The true thermal first differential through five excess orders. All
nonlinear Wilson and Haar terms enter through the same zero-offset books. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalFirstDifferential
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalDivision WilsonConditionalTaylorThermalOddInsertion
open WilsonConditionalTaylorThermalBook WilsonConditionalTaylorThermalLaplace
open scoped Classical BigOperators Topology
open PowerSeries
variable {G : Gauge} {n c : Side} {d : Descent n c}

def response (P : ChartRatio G) (d : Descent n c) (a : ℕ→ℝ) (f : Config G n→ℝ) (k : ℕ) :=
  let V := PowerSeries.mk (bareRank P d 0 (1 : Config G n→ℝ))
  let O := PowerSeries.mk (bareRank P d 0 f)*V⁻¹
  coeff k (WilsonConditionalTaylorThermalCentralDivision.direction O V
    (PowerSeries.mk (raw P d a f)) (PowerSeries.mk (raw P d a 1)))

theorem original (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (tag : d.Tags) (a : ℕ→ℝ)
    {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) (k : ℕ) (hk : k<w+6) :
    ranking P d a f k-ranking P d (-a) f k=response P d a f k+response P d a f k := by
  let D (u : ℕ→ℝ) (g : Config G n→ℝ) := PowerSeries.mk (bareRank P d u g)
  let S (g : Config G n→ℝ) := PowerSeries.mk (raw P d a g)
  let O (u : ℕ→ℝ) := D u f*(D u 1)⁻¹
  have piv (u : ℕ→ℝ) : coeff 0 (D u 1)≠0 := by simpa [D] using (pivot P R u room).ne'
  have norm (u : ℕ→ℝ) : O u*D u 1 = D u f := WilsonConditionalTaylorThermalInteractionDivision.normalized (piv u)
  have read (u : ℕ→ℝ) (i : ℕ) : coeff i (O u)=ranking P d u f i := rfl
  have asleep : zeroBefore (O 0) w := fun i hi => ranking_grade P R room 0 test old i hi
  have diff : zeroBefore (O a-O (-a)) (w+2) := by
    intro i hi;rw [map_sub,read,read,sub_eq_zero]
    exact WilsonConditionalTaylorThermalObserved.before P R room a (-a) test old i hi
  have temperature : zeroBefore (D a 1-D (-a) 1) 2 := by
    intro i hi
    simp only [map_sub,D,coeff_mk,sub_eq_zero]
    exact lower P R room a (-a) (unit_test d) unitGrade i hi
  have evenN : zeroBefore ((O a-O 0)+(O (-a)-O 0)) (w+4) := by
    intro i hi
    have law := (WilsonConditionalTaylorThermalMixedQuotient.original P R room tag (-a) a a test old).1 i hi
    simp only [WilsonConditionalTaylorThermalMixedQuotient.difference,WilsonConditionalTaylorThermalMixedDivision.square,neg_add_cancel,zero_add] at law
    simp only [map_sub,map_add,read];linarith
  have evenV : zeroBefore ((D a 1-D 0 1)+(D (-a) 1-D 0 1)) 4 := by
    intro i hi
    have law := WilsonConditionalTaylorThermalMixedBook.before P R room (-a) a a (unit_test d)
      (unitGrade (G:=G) (d:=d)) hi
    simp only [WilsonConditionalTaylorThermalMixedBook.change,neg_add_cancel,zero_add] at law
    simp only [map_sub,map_add,D,coeff_mk];linarith
  have paid {g : Config G n→ℝ} (good : d.Testable g) {v : ℕ} (grade : d.grade g v) :
      zeroBefore ((D a g-D (-a) g)+(S g+S g)) (v+6) := by
    intro i hi
    simp only [map_add,map_sub,D,S,coeff_mk,WilsonConditionalTaylorThermalOddInsertion.before P R room a good grade i hi,neg_add_cancel]
  have rawN : zeroBefore ((O a*D a 1-O (-a)*D (-a) 1)+(S f+S f)) (w+6) := by
    simp only [norm];exact paid test old
  have q := WilsonConditionalTaylorThermalCentralDivision.original (piv 0) asleep diff temperature evenN evenV
    rawN (paid (unit_test d) unitGrade) k hk
  rw [map_sub,sub_eq_zero,map_add,map_sub,read,read] at q
  exact q

end YM.Integration.WilsonConditionalTaylorThermalFirstDifferential
