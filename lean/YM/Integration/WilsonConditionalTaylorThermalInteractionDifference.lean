import YM.Integration.WilsonConditionalTaylorThermalInteractionBook

/-! Linearization of the actual temperature weight through relative order
three. The quadratic remainder of its exponential first enters at four. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalInteractionDifference
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalWeight WilsonConditionalTaylorThermalLaplace
open WilsonConditionalTaylorThermalBook WilsonConditionalTaylorThermalInteractionBook
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d

theorem linear (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    {A B : Fields G d → ℝ} (ha : d.SmoothAtFlat A) (hb : d.SmoothAtFlat B) (k : ℕ) :
    gaussianTerm P t (A-B) k = gaussianTerm P t A k-gaussianTerm P t B k := by
  have ja (i : ℕ) (x : E) : jet (nearFee P t (A-B)) i x =
      jet (nearFee P t A) i x-jet (nearFee P t B) i x := by
    have lin : nearFee P t (A-B) = nearFee P t A-nearFee P t B := by
      funext y; simp only [nearFee,Pi.sub_apply,mul_sub]
    dsimp only [jet]
    rw [lin,iteratedFDeriv_sub_apply (contDiffAt_infty.mp (near_smooth P R t _ (room_ok d room) ha) i)
      (contDiffAt_infty.mp (near_smooth P R t _ (room_ok d room) hb) i)]
    exact mul_sub .. 
  have term (x : E) : normTerm (nearFee P t (A-B)) (d.phase G t) k x =
      normTerm (nearFee P t A) (d.phase G t) k x - normTerm (nearFee P t B) (d.phase G t) k x := by
    simp only [normTerm,integrandSeries,Zone.mul,ja,sub_mul,Finset.sum_sub_distrib]
  unfold gaussianTerm Radial.moment
  simp_rw [term]
  exact integral_sub (integrates_term P R t A room ha k) (integrates_term P R t B room hb k)

theorem raw (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (u v : ℕ→ℝ)
    {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    bareRank P d u f (w+3) - bareRank P d v f (w+3) =
      -(∑t : d.Tags, gaussianTerm P t (score t (u-v) f) (w+3)) := by
  have each (t : d.Tags) : gaussianTerm P t (d.resetTerms u f t) (w+3)-gaussianTerm P t (d.resetTerms v f t) (w+3) =
      -gaussianTerm P t (score t (u-v) f) (w+3) := by
    let ok := room_ok d room
    have reset (a : ℕ→ℝ) : d.SmoothAtFlat (d.resetTerms a f t) :=
      ((smoothAccount ok t a).neg.exp).mul test.smooth
    have sc : d.SmoothAtFlat (score t (u-v) f) := (smoothAccount ok t (u-v)).mul test.smooth
    rw [←linear P R room t (reset u) (reset v),full,linear P R room t
      (smoothExtra ok t u v test) sc,
      gaussian_grade P R room (smoothExtra ok t u v test) (extraGrade ok t u v grade) t (by omega),zero_sub]
  simp only [bareRank,Finset.sum_apply,←Finset.sum_sub_distrib,each,Finset.sum_neg_distrib]

theorem signed (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (u v : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    bareRank P d u f (w+3)-bareRank P d v f (w+3) =
      -(scale P t*(ambient t room).average (Chart.tangent G d.Links) (inserted P t (u-v) f w)) := by
  rw [raw P R room u v test grade,charged P R room t (u-v) test grade]

end YM.Integration.WilsonConditionalTaylorThermalInteractionDifference
