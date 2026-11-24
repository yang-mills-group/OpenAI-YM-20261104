import YM.FVAAlt2.Boot.Revenue

/-! The normalized one-mark RG02 moment is the conditional expectation of
the original physical insertion under the full finite-volume Wilson density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeWilsonBlockObservable
open Function Filter Lattice Wilson RG Precision Tree Exterior Marker Multi
open PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Integral Comparison.RG02.Actual
open Comparison.RG02.Order
open scoped Classical Topology BigOperators

variable {G : Gauge} {c f : Side} {l : ℕ}
def numerator (S : StepData c f) (B : Boot.Scout (G := G) l) (x : fieldDir G c 1) (g : ℝ) : ℂ :=
  S.push (Integral.temperature g) (fun U : Config G f =>
    (↑(Wilson.bare (Integral.temperature g) U) : ℂ) * ((g^l)⁻¹ • (↑(B.Vt f U) : ℂ))) (Integral.sample g x)

variable (R : Run G) {I : Type} [DecidableEq I] [Fintype I] (H : Census I) (b : I)
  (m p : ℕ) (B : Boot.Scout (G := G) l)
  (F : Forest (R.family.path.levels.clock.op m p).ratio)
  (t : (R.family.path.levels.clock.op m p).Choices) (x : fieldDir G (R.family.side m p) 1)
local notation "K" => (RunFormalChain.fromRun R).step (m+1) m p (Nat.lt_succ_self m)
local notation "W" => Boot.ink H b R.family.path (m+1) p B
local notation "S" => R.family.path.levels.clock.op m p
local notation "f₁" => R.family.side (m+1) p

theorem integrated (g : ℝ) :
    (Bare.realMoment K F W t x g).part (H.fire b) = (Integral.office K F t g 0 x)⁻¹ • numerator S B x g := by
  unfold Bare.realMoment
  rw [Poly.part_smul, Actual.grades, Complex.real_smul, Complex.ofReal_inv]
  have he : Actual.atMark (H.fire b) (Bare.top W g) = fun U : Config G f₁ =>
      (↑(Wilson.bare (Integral.temperature g) U) : ℂ) * ((g^l)⁻¹ • (↑(B.Vt f₁ U) : ℂ)) :=
    funext fun U => Boot.Revenue.dot_o R p m H B b g U
  dsimp only
  rw [he]
  rfl

/-- Division by the same true empty-set Wilson density cancels the
Gaussian scale factor and retains the physical insertion and its power. -/
theorem normalized (g : ℝ) (hg : 0 < g) :
    (Order.unitScale (Bare.realMoment K F W t x g)).part (H.fire b) =
      ((S).push (Integral.temperature g) (Wilson.bare (Integral.temperature g)) (Integral.sample g x))⁻¹ •
      numerator S B x g := by
  unfold Order.unitScale
  rw [Poly.part_smul,Bare.vacancy,Bare.rho,integrated,Complex.real_smul,Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_inv]
  have hp : (↑(Integral.office K F t g 0 x):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Integral.office_pos K F t g 0 x hg).ne'
  field_simp

end YM.Integration.NativeWilsonBlockObservable
end
