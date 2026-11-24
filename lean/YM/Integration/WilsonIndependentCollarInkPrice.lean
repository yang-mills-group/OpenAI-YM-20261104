import YM.Integration.WilsonIndependentCollarRootedInk
import YM.Integration.WilsonIndependentCollarOpticalSpan

/-! Price the absolute sum over positions and derivative measures by one
fixed polynomial, before the moving reporting date is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarInkPrice
open Function Finset Lattice Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos
open WilsonIndependentCollarPrintIncome
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [DecidableEq ι]

def load (j:ℕ):Credit:=(billingQ Unit j 0).usingC ⟨1,4,by norm_num⟩

theorem alternatives (S:Finset ι)(v:ι)(σ Z:ℝ)(positive:0<σ)(hZ:1≤Z)(shelf:σ⁻¹≤Z):
    sprigs S v (σ/2) ≤ (load (Fintype.card (S.erase v))).buy Z:=by
  unfold sprigs
  rw [show tiePay Unit 0 (σ/2/8)=1 from pow_zero _,mul_one]
  have escrow:(σ/2)⁻¹≤2*Z:=by rw [inv_div,div_eq_mul_inv];linarith only [shelf]
  have book:=snuff (α:=Unit) (r:=Fintype.card (S.erase v)) (half_pos positive) escrow
  have strong:=offer_expands (α:=Unit) (k:=Fintype.card (S.erase v)) (r:=0) (show 1≤2*(2*Z) by linarith only [hZ])
  apply book.trans
  apply strong.trans
  unfold load;rw [Credit.stock_up]
  change (billingQ Unit _ 0).buy (2*(2*Z)) ≤ (billingQ Unit _ 0).buy (4*Z^1)
  rw [pow_one,show 2*(2*Z)=4*Z by ring]

def cost (G:Gauge)(P:Credit)(k h n b:ℕ):Credit:=
  let constant:Credit:=⟨0,max 1 (glacier G k h*Real.exp 1),le_max_left ..⟩
  let identity:Credit:=⟨1,1,le_rfl⟩
  constant.prodC (identity.prodC ((P.powC n).prodC (load b)))

theorem original (P:Credit)(k h:ℕ)(S:Finset ι)(v:ι)(front:v∈S){σ Z fee A:ℝ}(positive:0<σ)(upper:σ≤1)
    (hZ:1≤Z)(shelf:σ⁻¹≤Z)(part:0≤fee)(paid:fee≤Z)(non:0≤A):
    glacier G k h*(Real.exp (3*σ/8)*(fee*(P.buy Z*A)^S.card))*sprigs S v (σ/2) ≤
      (cost G P k h S.card (Fintype.card (S.erase v))).buy Z*A^S.card:=by
  have reach:=alternatives S v σ Z positive hZ shelf
  have reachSum:=sprigsPay front (0:Cover) (half_pos positive)
  have spent:0 ≤ sprigs S v (σ/2):=(tsum_nonneg reachSum.1).trans reachSum.2.2
  have stage:0≤P.buy Z:=zero_le_one.trans (P.purchase hZ)
  have height:Real.exp (3*σ/8)≤Real.exp 1:=Real.exp_monotone (by linarith only [upper])
  unfold cost;rw [Credit.products,Credit.products,Credit.products,Credit.power]
  simp only [Credit.buy,pow_zero,mul_one,pow_one,one_mul,mul_pow]
  calc
    _ = (glacier G k h*Real.exp (3*σ/8))*(fee*((P.x*Z^P.d)^S.card*sprigs S v (σ/2)))*A^S.card:=by ring
    _ ≤ _:=by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg non _)
      apply mul_le_mul (le_trans (mul_le_mul_of_nonneg_left height (gentle ..)) (le_max_right ..)) _ _ (zero_le_one.trans (le_max_left ..))
      · rw [←mul_pow]
        exact mul_le_mul paid (mul_le_mul_of_nonneg_left reach (pow_nonneg stage _))
          (mul_nonneg (pow_nonneg stage _) spent) (zero_le_one.trans hZ)
      · exact mul_nonneg part (mul_nonneg (pow_nonneg stage _) spent)

end YM.Integration.WilsonIndependentCollarInkPrice
end
