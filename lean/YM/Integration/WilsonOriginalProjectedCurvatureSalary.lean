import YM.Integration.WilsonOriginalProjectedCurvatureBinder

/-! The actual Wilson Q-token commission is charged on its original independent
unit tests. Normalization moves precisely the invariant tensor tariff into paint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureSalary
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureRoster
open scoped Classical BigOperators

variable {G : Gauge} {r : ℕ}

def divided (a : Atom G r) (σ : ℝ) : Atom G r where
  leg := a.leg
  coeff j := (a.budget σ)⁻¹ * a.coeff j

theorem amount (a : Atom G r) (σ : ℝ) : 0 ≤ a.budget σ :=
  mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Real.exp_pos _).le

theorem poly (a : Atom G r) (σ : ℝ) (x : Fin r → G.Color) :
    (divided a σ).poly x = (a.budget σ)⁻¹ * a.poly x := by
  simp only [Atom.poly, divided, Finset.mul_sum, mul_assoc]

theorem invariant (a : Atom G r) (σ : ℝ) (h : a.Invariant) : (divided a σ).Invariant := by
  intro q x
  rw [poly, poly, h q x]

theorem graceful (a : Atom G r) (σ : ℝ) (h : 0 < a.budget σ) :
    (divided a σ).budget σ = 1 := by
  change (∑ j, |(a.budget σ)⁻¹ * a.coeff j|) * Real.exp (σ * a.length) = 1
  simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr h.le), ← Finset.mul_sum]
  change (a.budget σ)⁻¹ * a.magnitude * Real.exp (σ * a.length) = 1
  rw [mul_assoc]
  exact inv_mul_cancel₀ h.ne'

variable {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type}
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
  (N : ℕ) (s : Row (R:=R) u) (σ : ℝ)

abbrev tastes := IndependentTests (ActualRunQlocalNativeTuple.orbit D)
def paint (x : tastes D) : ℂ :=
  ((placed u s).budget σ : ℂ) * ActualRunKernelPackets.amplitude R
    (ActualRunQlocalNativeTuple.orbit D) (degree u) N p L (labels Q D u μ orders N) s
    (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)

def wallet := (ActualOriginalQPackets.token Q D u μ orders N s).coin *
  Real.exp (σ * ActualOriginalQCharges.rowFall u s)

theorem bound (x : tastes D) :
    ‖paint Q D u μ orders N s σ x‖ ≤ wallet Q D u μ orders N s σ := by
  let y := testInclusion (ActualRunQlocalNativeTuple.orbit D) x
  let a := ActualRunKernelPackets.amplitude R (ActualRunQlocalNativeTuple.orbit D)
    (degree u) N p L (labels Q D u μ orders N) s y
  have hc := ActualRunKernelPackets.term_bound R (ActualRunQlocalNativeTuple.orbit D)
    (degree u) N p L (fun t => ActualRunQlocalNativeTuple.root D t.1)
    (labels Q D u μ orders N) (coefficientBudget Q D u μ orders N) s y
    (coordinate_bound Q D u μ orders N s.1 s.2.1 x)
  change (∑ j, ‖NativeCurvatureTensor.coefficient
      (fun k => (word s.2.2.val k).2) j * a‖) ≤
      (ActualOriginalQPackets.token Q D u μ orders N s).coin at hc
  simp only [norm_mul, ← Finset.sum_mul] at hc
  change ‖(((placed u s).budget σ : ℝ) : ℂ) * a‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (amount _ _)]
  simp only [Atom.budget, (charges u s).1, (charges u s).2, wallet]
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

theorem work (x : tastes D) (U : Config G (R.family.side L p))
    (h : 0 < (placed u s).budget σ) :
    (((divided (placed u s) σ).unmasked U (ActualRunQlocalNativeTuple.root D s.1.1) : ℝ) : ℂ) *
        paint Q D u μ orders N s σ x =
      (ActualOriginalQPackets.token Q D u μ orders N s).read
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) U := by
  rw [actual Q D u μ orders s N]
  unfold Atom.unmasked
  rw [poly]
  simp only [paint, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [mul_mul_mul_comm, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr h.ne'), one_mul]
  rfl

end YM.Integration.WilsonOriginalProjectedCurvatureSalary
