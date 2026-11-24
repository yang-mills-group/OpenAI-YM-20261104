import YM.Integration.WilsonConditionalTaylorThermalWeight
import YM.RGComparison.Core16.Leading

/-! On the actual finite history the changing temperature first appears at the
leading source degree plus two. The Gaussian still contains every interior link. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalLaplace
open Lattice RG Tree Wilson Precision Push.BetaTransport RGComparison.Core16
open Function Filter MeasureTheory
open PertExtension PertExtension.Series Tested Radial GaussianScore
open scoped Topology ContDiff Classical BigOperators
open Descent
variable {G : Gauge} {n c : Side} {d : Descent n c} (P : ChartRatio G) (R : LocalRatio P)
    (room : d.Room G)
local notation "E" => Coordinates G d

private theorem jetSub {A B : E → ℝ} (ha : ContDiffAt ℝ ∞ A 0) (hb : ContDiffAt ℝ ∞ B 0)
    (k : ℕ) (x : E) : jet (A-B) k x = jet A k x - jet B k x := by
  unfold jet
  rw [iteratedFDeriv_sub_apply (contDiffAt_infty.mp ha k) (contDiffAt_infty.mp hb k)]
  exact mul_sub _ _ _

include R room in
private theorem gaussianSub (t : d.Tags) {A B : Fields G d → ℝ}
    (ha : d.SmoothAtFlat A) (hb : d.SmoothAtFlat B) (k : ℕ) :
    gaussianTerm P t (A-B) k = gaussianTerm P t A k - gaussianTerm P t B k := by
  let ok := room_ok d room
  have linear : nearFee P t (A-B) = nearFee P t A - nearFee P t B := by
    funext x; simp only [nearFee,Pi.sub_apply,mul_sub]
  have entry (x : E) :
      normTerm (nearFee P t (A-B)) (d.phase G t) k x =
        normTerm (nearFee P t A) (d.phase G t) k x - normTerm (nearFee P t B) (d.phase G t) k x := by
    simp only [normTerm,integrandSeries,Zone.mul,linear,
      jetSub (near_smooth P R t A ok ha) (near_smooth P R t B ok hb),sub_mul,Finset.sum_sub_distrib]
  unfold gaussianTerm Radial.moment
  simp_rw [entry]
  exact integral_sub (integrates_term P R t A room ha k) (integrates_term P R t B room hb k)

def field (f : Config G n → ℝ) (w : ℕ) := jet (f ∘ d.fine 1 ∘ d.tablePath) w
def vertex (t : d.Tags) (v : ℕ → ℝ) := jet (WilsonConditionalTaylorThermalWeight.account (G:=G) t v ∘ d.tablePath) 2
def density (d : Descent n c) (P : ChartRatio G) :=
  Chart.jacobian P (U:=d.Links) 0 * (Fintype.card d.Tags : ℝ)⁻¹
def mass (t : d.Tags) := ∫ x, Radial.kernel (d.phase G t) x ∂Chart.tangent G d.Links

theorem vertex_tag (ok : d.OK G) (t s : d.Tags) (v : ℕ → ℝ) :
    vertex (G:=G) t v = vertex s v := by
  have h := branch_independent (v := fun x : E => x) (Bg := fun _ => 0) ok contDiffAt_id rfl t s v
  simp only [link_one] at h
  funext x
  unfold vertex jet WilsonConditionalTaylorThermalWeight.account
  simp only [Function.comp_def]
  rw [(h.iteratedFDeriv ℝ 2).eq_of_nhds]

include R room

theorem scoreHead (t : d.Tags) (v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w) (x : E) :
    integrandSeries (d.phase G t) (nearFee P t (WilsonConditionalTaylorThermalWeight.score t v f)) (w+2) x =
      density d P * (field (d:=d) f w x * vertex t v x) := by
  let ok := room_ok d room
  let J (z : E) := Chart.jacobian P z * d.probability t (d.tablePath z)
  let A := WilsonConditionalTaylorThermalWeight.account (G:=G) t v ∘ d.tablePath
  let F := f ∘ d.fine 1 ∘ d.tablePath
  have hj : ContDiffAt ℝ ∞ J 0 := ((Chart.Ratio.jacobian_smooth R).of_le le_top).mul
      (contDiffAt_const.congr_of_eventuallyEq (prob_flat_tangent ok t))
  have hA : ContDiffAt ℝ ∞ A 0 := WilsonConditionalTaylorThermalWeight.smoothAccount ok t v
  have hf : d.SmoothAtFlat (WilsonConditionalTaylorThermalWeight.score t v f) := hA.mul test.smooth
  have hGrade := WilsonConditionalTaylorThermalWeight.scoreGrade ok t v grade
  rw [gaussian_origin P R room hf hGrade t x]
  change jet (J * (A * F)) (w+2) x = _
  have joint := head_product hj (hA.mul test.smooth) (k:=0)
    (fun z => (directions hj z).bounded) hGrade x
  rw [Nat.zero_add,jet_zero] at joint
  have mf := head_product hA test.smooth (WilsonConditionalTaylorThermalWeight.accountGrade ok t v) grade x
  rw [Nat.add_comm 2 w] at mf
  change jet (J * (A*F)) (w+2) x = J 0 * jet (A*F) (w+2) x at joint
  change jet (A*F) (w+2) x = jet A 2 x * jet F w x at mf
  rw [joint,mf]
  change (Chart.jacobian P 0 * d.probability t (d.tablePath 0)) * _ = _
  rw [(prob_flat_tangent ok t).self_of_nhds]
  unfold density field vertex A F
  ring

theorem raw (t : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w) (k : ℕ) (hk : k ≤ w+2) :
    gaussianTerm P t (d.resetTerms u f t) k - gaussianTerm P t (d.resetTerms v f t) k =
      -gaussianTerm P t (WilsonConditionalTaylorThermalWeight.score t (u-v) f) k := by
  let ok := room_ok d room
  have reset (z : ℕ → ℝ) : d.SmoothAtFlat (d.resetTerms z f t) :=
    ((WilsonConditionalTaylorThermalWeight.smoothAccount ok t z).neg.exp).mul test.smooth
  have score : d.SmoothAtFlat (WilsonConditionalTaylorThermalWeight.score t (u-v) f) :=
    (WilsonConditionalTaylorThermalWeight.smoothAccount ok t (u-v)).mul test.smooth
  rw [← gaussianSub P R room t (reset u) (reset v),WilsonConditionalTaylorThermalWeight.full,
    gaussianSub P R room t (WilsonConditionalTaylorThermalWeight.smoothExtra ok t u v test) score,
    gaussian_grade P R room (WilsonConditionalTaylorThermalWeight.smoothExtra ok t u v test) (WilsonConditionalTaylorThermalWeight.extraGrade ok t u v grade) t
      (show k < w+4 by omega),zero_sub]

theorem lower (t : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w) (k : ℕ) (hk : k < w+2) :
    gaussianTerm P t (d.resetTerms u f t) k = gaussianTerm P t (d.resetTerms v f t) k := by
  apply sub_eq_zero.mp
  rw [raw P R room t u v test grade k hk.le,gaussian_grade P R room (Y:=WilsonConditionalTaylorThermalWeight.score t (u-v) f)
    ((WilsonConditionalTaylorThermalWeight.smoothAccount (room_ok d room) t (u-v)).mul test.smooth)
    (WilsonConditionalTaylorThermalWeight.scoreGrade (room_ok d room) t (u-v) grade) t hk,neg_zero]

theorem leading (t : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    gaussianTerm P t (d.resetTerms u f t) (w+2) - gaussianTerm P t (d.resetTerms v f t) (w+2) =
      -(density d P * ((ambient t room).average (Chart.tangent G d.Links)
        (field (d:=d) f w * vertex t (u-v)) * mass (G:=G) t)) := by
  rw [raw P R room t u v test grade _ le_rfl, moment_diagram t P room]
  congr 1
  have e : integrandSeries (d.phase G t) (nearFee P t (WilsonConditionalTaylorThermalWeight.score t (u-v) f)) (w+2) =
      fun x => density d P * (field (d:=d) f w x * vertex t (u-v) x) :=
    funext (scoreHead P R room t (u-v) test grade)
  rw [e]
  unfold Law.average mass
  simp only [Pi.mul_apply, mul_assoc,integral_const_mul]
  ring

end YM.Integration.WilsonConditionalTaylorThermalLaplace
