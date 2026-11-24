import YM.Integration.WilsonIndependentCollarPrintWallet

/-! The moving factors in the literal per-date two-print tariff are polynomial
in canopy size and inverse strip at fixed order, support exponent and load. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMovingTariff
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.AbsoluteSums Comparison.Density Transport
open scoped BigOperators Classical

theorem empty {G : Gauge} (tube : LinkTube G) : groupPrice tube 0=1 := by
  simp [groupPrice,quote,Push.Uniform.composeCost]

theorem geometric {θ : ℝ} (positive : 0<θ) : (1-Real.exp (-θ))⁻¹ ≤ 1+θ⁻¹ := by
  have h := Real.add_one_le_exp θ
  have d : 0<Real.exp θ-1 := by linarith
  have e := Real.exp_pos θ
  have ee : Real.exp θ≠1 := by linarith
  have eq : (1-Real.exp (-θ))⁻¹=1+(Real.exp θ-1)⁻¹ := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [eq]
  linarith [(inv_le_inv₀ d positive).2 (show θ≤Real.exp θ-1 by linarith)]

def fixed (k : ℕ) (C a v : ℝ) := Real.exp (a*v) * C * (4+k).factorial * Real.exp 1

theorem payment (B k : ℕ) (θ C a v : ℝ) (pos : 0<θ) (small : θ≤1) (allow : 0≤C) :
    Footprint.payment 1 (B+2) k θ C 1 a v ≤
      fixed k C a v * ((B+B+5:ℕ):ℝ)^4*(1+θ⁻¹)^(5+k) := by
  let u := (1+θ⁻¹)
  have ui : θ⁻¹≤u := by dsimp [u]; linarith
  have u0 : 0≤u := (inv_nonneg.mpr pos.le).trans ui
  have free : 0≤(1-Real.exp (-θ))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
  have support : (↑(Footprint.spread 1 (B+2)):ℝ)=((B+B+5:ℕ):ℝ)^4 := by
    simp [Footprint.spread,Animals.ballCost]; ring
  unfold Footprint.payment Footprint.degreeIncome
  rw [support]
  calc
    _ ≤ Real.exp (a*v)*1*C*((B+B+5:ℕ):ℝ)^4*
        (u^(4+k)*(4+k).factorial*Real.exp 1)*u := by
      gcongr
      exact geometric pos
    _ = _ := by
      rw [show 5+k=4+k+1 by omega,pow_succ]; dsimp [fixed,u]; ring

end YM.Integration.WilsonIndependentCollarMovingTariff
