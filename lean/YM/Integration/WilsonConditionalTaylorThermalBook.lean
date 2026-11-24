import YM.Integration.WilsonConditionalTaylorThermalLaplace

/-! The authentic flat tag probabilities and actual Gaussian masses in the two
unnormalized Wilson columns. These use the same tree, phase and Haar chart. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalBook
open Lattice RG Tree Wilson Precision Push.BetaTransport RGComparison.Core16
open Function Filter MeasureTheory
open PertExtension PertExtension.Series Tested Radial GaussianScore
open scoped Topology ContDiff Classical BigOperators
open Descent WilsonConditionalTaylorThermalLaplace
variable {G : Gauge} {n c : Side} {d : Descent n c} (P : ChartRatio G) (R : LocalRatio P)
    (room : d.Room G)
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

def scale (P : ChartRatio G) (t : d.Tags) :=
  Fintype.card d.Tags * density d P * mass (G:=G) t

include room in
theorem mass_tag (t s : d.Tags) : mass (G:=G) t = mass (G:=G) s := by
  unfold mass Radial.kernel
  rw [phase_jet (room_ok d room) t s]

theorem average_tag (t s : d.Tags) (F : E → ℝ) :
    (ambient t room).average μ F = (ambient s room).average μ F := by
  unfold Law.average Law.kern
  change (∫ x : E, F x * Real.exp _ ∂μ) / (∫ x : E, Real.exp _ ∂μ) =
    (∫ x : E, F x * Real.exp _ ∂μ) / (∫ x : E, Real.exp _ ∂μ)
  simp only [ambient,quadratic_independent t s room]

include R room in
theorem source (t : d.Tags) (u : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    bareRank P d u f w = scale P t * (ambient t room).average μ (field (d:=d) f w) := by
  have one (s : d.Tags) : gaussianTerm P s (d.resetTerms u f s) w =
      density d P * (ambient t room).average μ (field (d:=d) f w) * mass (G:=G) t := by
    rw [moment_diagram s P room,show Radial.integrandSeries (d.phase G s)
      (nearFee P s (d.resetTerms u f s)) w =
        fun x => density d P * (field (d:=d) f w) x from
          funext (ordinary_grade_jet s P R test grade u room)]
    change _ * mass (G:=G) s = _
    rw [mass_tag room s t,average_tag room s t]
    unfold Law.average
    simp only [Pi.mul_apply,mul_assoc,integral_const_mul]
    ring
  rw [bareRank, Finset.sum_apply]
  simp only [one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,scale]
  ring

include R room in
theorem lower (u v : ℕ → ℝ) {f : Config G n → ℝ} (test : d.Testable f)
    {w : ℕ} (grade : d.grade f w) (k : ℕ) (hk : k < w+2) :
    bareRank P d u f k = bareRank P d v f k := by
  simp only [bareRank,Finset.sum_apply]
  exact Finset.sum_congr rfl (fun t _ => WilsonConditionalTaylorThermalLaplace.lower P R room t u v test grade k hk)

include R room in
theorem sourceChange (t : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    bareRank P d u f (w+2) - bareRank P d v f (w+2) =
      -(scale P t * (ambient t room).average μ (field (d:=d) f w * vertex t (u-v))) := by
  simp only [bareRank,Finset.sum_apply,← Finset.sum_sub_distrib]
  have each (s : d.Tags) :
      gaussianTerm P s (d.resetTerms u f s) (w+2) - gaussianTerm P s (d.resetTerms v f s) (w+2) =
      -(density d P * ((ambient t room).average μ (field (d:=d) f w * vertex t (u-v)) * mass (G:=G) t)) := by
    rw [WilsonConditionalTaylorThermalLaplace.leading P R room s u v test grade,
      vertex_tag (room_ok d room) s t (u-v),mass_tag room s t,average_tag room s t]
  simp only [each,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,scale]
  ring

theorem unitGrade : d.grade (1 : Config G n → ℝ) 0 := fun _ => bill_const 1

theorem unitField : field (d:=d) (1 : Config G n → ℝ) 0 = 1 := by
  funext x
  rw [field,jet_zero]
  rfl

include R room in
theorem vacuum (t : d.Tags) (u : ℕ → ℝ) :
    bareRank P d u (1 : Config G n → ℝ) 0 = scale P t := by
  rw [source P R room t u (unit_test d) unitGrade,unitField]
  unfold Law.average
  rw [one_mul,div_self,mul_one]
  rw [← kern_is]
  exact (integral_exp_pos (kernel_integrable t room)).ne'

include R room in
theorem vacuumChange (t : d.Tags) (u v : ℕ → ℝ) :
    bareRank P d u (1 : Config G n → ℝ) 2 - bareRank P d v 1 2 =
      -(scale P t * (ambient t room).average μ (vertex t (u-v))) := by
  simpa only [Nat.zero_add,unitField,one_mul] using
    sourceChange P R room t u v (unit_test d) unitGrade

end YM.Integration.WilsonConditionalTaylorThermalBook
