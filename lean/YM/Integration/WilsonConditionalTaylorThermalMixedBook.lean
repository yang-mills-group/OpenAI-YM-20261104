import YM.Integration.WilsonConditionalTaylorThermalMixedWeight

/-! The complete mixed change of the two raw, independently tagged temperature
books, before the common vacuum denominator is divided out. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalMixedBook
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalBook WilsonConditionalTaylorThermalMixedWeight
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

def change (P : ChartRatio G) (d : Descent n c) (z a b : ℕ→ℝ) (f : Config G n→ℝ) (k : ℕ) :=
  (bareRank P d (z+a+b) f k-bareRank P d (z+a) f k) -
    (bareRank P d (z+b) f k-bareRank P d z f k)

theorem raw (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G)
    (z a b : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) (k : ℕ) :
    change P d z a b f k = ∑t : d.Tags, gaussianTerm P t (joint t z a b f) k := by
  have byTag (t : d.Tags) : (gaussianTerm P t (d.resetTerms (z+a+b) f t) k-
      gaussianTerm P t (d.resetTerms (z+a) f t) k) -
      (gaussianTerm P t (d.resetTerms (z+b) f t) k - gaussianTerm P t (d.resetTerms z f t) k) =
      gaussianTerm P t (joint t z a b f) k := by
    have neat (u : ℕ→ℝ) : d.SmoothAtFlat (d.resetTerms u f t) :=
      ((WilsonConditionalTaylorThermalWeight.smoothAccount (room_ok d room) t u).neg.exp).mul test.smooth
    have diff (u v : ℕ→ℝ) : d.SmoothAtFlat (d.resetTerms u f t-d.resetTerms v f t) := (neat u).sub (neat v)
    rw [←WilsonConditionalTaylorThermalInteractionDifference.linear P R room t (neat _) (neat _),
      ←WilsonConditionalTaylorThermalInteractionDifference.linear P R room t (neat _) (neat _),
      ←WilsonConditionalTaylorThermalInteractionDifference.linear P R room t
        (diff _ _) (diff _ _),together]
  simp only [change,bareRank,Finset.sum_apply,←Finset.sum_sub_distrib,byTag]

theorem before (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G)
    (z a b : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w)
    {k : ℕ} (low : k<w+4) : change P d z a b f k = 0 := by
  rw [raw P R room z a b test]
  exact Finset.sum_eq_zero (fun t _ => gaussian_grade P R room
    (regular (room_ok d room) t z a b test) (rank (room_ok d room) t z a b old) t low)

theorem source (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (z a b : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) :
    change P d z a b f (w+4) =
      scale P t*(ambient t room).average μ ((vertex t a*vertex t b)*field (d:=d) f w) := by
  rw [raw P R room z a b test]
  apply WilsonConditionalTaylorThermalInteractionBook.registered
  intro s
  funext x
  let ok := room_ok d room
  let J := fun x : E => Chart.jacobian P x*d.probability s (d.tablePath x)
  let F := joint s z a b f ∘ d.tablePath
  have sj : ContDiffAt ℝ ∞ J 0 := ((Chart.Ratio.jacobian_smooth R).of_le le_top).mul
    (contDiffAt_const.congr_of_eventuallyEq (prob_flat_tangent ok s))
  have sf := regular ok s z a b test
  have graded := rank ok s z a b old
  rw [gaussian_origin P R room sf graded s x]
  change jet (J*F) (w+4) x = _
  have p := head_product (A:=J) (f:=F) sj sf (k:=0) (fun y => (directions sj y).bounded) graded x
  simp only [Nat.zero_add,jet_zero] at p
  have j0 : J 0 = density d P := by
    dsimp only [J,density]
    rw [(prob_flat_tangent ok s).self_of_nhds]
  rw [p,j0,head ok s z a b test old,vertex_tag ok s t a,vertex_tag ok s t b]
  rfl

end YM.Integration.WilsonConditionalTaylorThermalMixedBook
