import YM.Integration.WilsonIndependentCollarMovingTariff
import YM.Integration.WilsonIndependentCollarPrintWallet

/-! After the rooted income has been restored, both literal physical unit
prices cost a polynomial in the logarithm of the clock. Its degree may depend
on the fixed working order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPhysicalRates
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.AbsoluteSums AllOrder AllOrder.Floe Laurent Comparison.Density
open Transport AnalyticBridge.SectorAffine.Offset
open WilsonIndependentCollarPrintWallet
open scoped BigOperators Classical Matrix.Norms.Frobenius

def jetConstant (G : Gauge) (J ℓ s pieces : ℕ) : ℝ :=
    (2:ℝ)^J * (‖ContinuousLinearMap.lsmul ℝ ℝ (E:=ℂ)‖*(Render.couple J)^ℓ) *
      WilsonEmittedCompactTariff.fixed G J s pieces

def wordConstant (G : Gauge) (s pieces : ℕ) : ℝ :=
    2^s * (WilsonEmittedRootSalary.fee G 0 s)⁻¹ * WilsonEmittedCompactTariff.fixed G 0 s pieces

theorem original (G : Gauge) (B:BudgetPoint) (tube : LinkTube G) (J ℓ p pieces depth : ℕ)
    {H σ : ℝ} (pos : 0<σ) (cap : B.supportExponent+2≤102)
    (reserve : Real.exp (σ⁻¹^2)≤H) (square : B.B=Nat.ceil ((Real.log H)^2)) :
    let s:=p+depth+1
    let θ:=WilsonEmittedCompactTariff.strip σ
    groupPrice tube 0*jetRate G B J ℓ p pieces depth θ ≤
      jetConstant G J ℓ s pieces*(1+Real.log H)^(13+J*s) ∧
    wordRate B p pieces depth θ ≤ wordConstant G s pieces*(1+Real.log H)^13 := by
  let s:=p+depth+1
  let θ:=WilsonEmittedCompactTariff.strip σ
  let C:=WilsonEmittedRootSalary.fee G 0 s
  have hp:=WilsonEmittedCompactTariff.original (G:=G) (B:=B) J s pieces zero_le_one pos cap reserve square
  have h0:=WilsonEmittedCompactTariff.original (G:=G) (B:=B) 0 s pieces zero_le_one pos cap reserve square
  have cc : 0<C := WilsonEmittedRootSalary.fee_pos G 0 s
  have eq : C*WilsonEmittedGroupWallet.stock B s pieces 0 1 θ =
      WilsonEmittedLocatedCensus.receipt G B 0 s pieces 0 1 (B.supportExponent+2) θ := by
    simp only [C,WilsonEmittedGroupWallet.stock,WilsonEmittedLocatedCensus.receipt,
      Footprint.payment,Footprint.degreeIncome,Nat.zero_mul]
    ring
  simp only [one_mul] at hp
  simp only [one_mul,zero_mul,Nat.add_zero] at h0
  change WilsonEmittedLocatedCensus.receipt G B 0 s pieces 0 1 (B.supportExponent+2) θ ≤ _ at h0
  rw [←eq] at h0
  constructor
  · rw [WilsonIndependentCollarMovingTariff.empty,one_mul]
    change (2:ℝ)^J*(‖ContinuousLinearMap.lsmul ℝ ℝ (E:=ℂ)‖*(Render.couple J)^ℓ*_ ) ≤ _
    have nn := Render.code_nn J
    calc
      _ ≤ (2:ℝ)^J*(‖ContinuousLinearMap.lsmul ℝ ℝ (E:=ℂ)‖*(Render.couple J)^ℓ*
        (WilsonEmittedCompactTariff.fixed G J s pieces*(1+Real.log H)^(13+J*s))) := by
          gcongr
      _ = _ := by dsimp [jetConstant,s]; ring
  · change (2:ℝ)^s * WilsonEmittedGroupWallet.stock B s pieces 0 1 θ ≤ _
    calc
      _ = (2:ℝ)^s*C⁻¹ * (C*WilsonEmittedGroupWallet.stock B s pieces 0 1 θ) := by
        field_simp [cc.ne']
      _ ≤ (2:ℝ)^s*C⁻¹ * (WilsonEmittedCompactTariff.fixed G 0 s pieces*(1+Real.log H)^13) :=
        mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = _ := by dsimp [C,s,wordConstant];ring

end YM.Integration.WilsonIndependentCollarPhysicalRates
