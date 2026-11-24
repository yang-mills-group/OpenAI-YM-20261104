import YM.Integration.WilsonConditionalTaylorThermalFourthCentering
import YM.Integration.WilsonConditionalTaylorThermalFourthBook
import YM.Integration.WilsonConditionalTaylorThermalParity

/-! The interacting normalized temperature derivative is an explicit
connected combination of whole original Gaussian measurements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalFourthGaussian
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalDivision WilsonConditionalTaylorThermalWeight WilsonConditionalTaylorThermalLaplace
open WilsonConditionalTaylorThermalBook WilsonConditionalTaylorThermalFirstDifferential WilsonConditionalTaylorThermalFourthBook
open scoped Classical BigOperators Topology
open PowerSeries
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "μ" => Chart.tangent G d.Links

private theorem first (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (a : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) :
    WilsonConditionalTaylorThermalOddInsertion.raw P d a f (w+2)=
      scale P t*(ambient t room).average μ (field (d:=d) f w * vertex t a) := by
  apply WilsonConditionalTaylorThermalInteractionBook.registered;intro s;funext x
  rw [scoreHead P R room s a test old x,vertex_tag (room_ok d room) s t a]
  rfl

def reading (P : ChartRatio G) (room : d.Room G) (t : d.Tags) (a : ℕ→ℝ) (f : Config G n→ℝ) (w : ℕ) :=
  let A := (ambient t room).average μ
  let F := field (d:=d) f w
  let Q := vertex t a
  WilsonConditionalTaylorThermalFourthCentering.centers (A F) (A (prior P t f w)) (A Q) (A (F*Q))
    (A (prior P t 1 0)) (A (submitted P t a f w)) (A (submitted P t a 1 0))

theorem original (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (a : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) :
    response P d a f (w+4)=reading P room t a f w := by
  let D (g : Config G n→ℝ) := PowerSeries.mk (bareRank P d 0 g)
  let V := D 1
  let S (g : Config G n→ℝ) := PowerSeries.mk (WilsonConditionalTaylorThermalOddInsertion.raw P d a g)
  let O := D f*V⁻¹
  let m := scale P t
  have dc (g) (i) : coeff i (D g)=bareRank P d 0 g i := coeff_mk _ _
  have sc (g) (i) : coeff i (S g)=WilsonConditionalTaylorThermalOddInsertion.raw P d a g i := coeff_mk _ _
  have v0 : coeff 0 V=m := (dc 1 0).trans (WilsonConditionalTaylorThermalBook.vacuum P R room t 0)
  have pos : coeff 0 V≠0 := (dc 1 0).trans_ne (pivot P R (0 : ℕ→ℝ) room).ne'
  have mpos : m≠0 := v0.symm.trans_ne pos
  have v1 : coeff 1 V=0 := (dc 1 1).trans (WilsonConditionalTaylorThermalParity.unnormalized P 0 1 (show Odd 1 by decide))
  have low : zeroBefore O w := fun i hi=>ranking_grade P R room 0 test old i hi
  have paid {g : Config G n→ℝ} {h : ℕ} (good : d.Testable g) (grade : d.grade g h) : zeroBefore (S g) (h+2) := by
    intro i hi
    simp only [S,coeff_mk,WilsonConditionalTaylorThermalOddInsertion.raw]
    apply Finset.sum_eq_zero;intro s _
    exact gaussian_grade P R room (Y:=score s a g) ((smoothAccount (room_ok d room) s a).mul good.smooth)
      (scoreGrade (room_ok d room) s a grade) s hi
  have un := unit_test (G:=G) d
  have ug := unitGrade (G:=G) (d:=d)
  have z3 : coeff 3 (S 1)=0 := by
    have p := WilsonConditionalTaylorThermalOddInsertion.before P R room a un ug 3 (by decide)
    simp only [WilsonConditionalTaylorThermalParity.unnormalized P _ _ (show Odd 3 by decide),sub_zero] at p
    rw [sc]
    linarith
  have z2 := first P R room t a un ug
  rw [unitField,one_mul] at z2
  exact WilsonConditionalTaylorThermalFourthCentering.original mpos v0 v1
    ((dc 1 2).trans (WilsonConditionalTaylorThermalFourthBook.vacuum P R room t un ug)) low
    (WilsonConditionalTaylorThermalInteractionDivision.normalized pos)
    ((dc f w).trans (source P R room t 0 test old)) ((dc f (w+2)).trans (WilsonConditionalTaylorThermalFourthBook.vacuum P R room t test old))
    (paid test old) ((sc f (w+2)).trans (first P R room t a test old)) ((sc f (w+4)).trans (scored P R room t a test old))
    (paid un ug) ((sc 1 2).trans z2) z3 ((sc 1 4).trans (scored P R room t a un ug))

end YM.Integration.WilsonConditionalTaylorThermalFourthGaussian
