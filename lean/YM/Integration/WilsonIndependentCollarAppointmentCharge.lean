import YM.Integration.WilsonIndependentCollarConnectedFilm

/-! Charge the same true connected rendering with the original roster's
salary, before its finite perturbative order is increased. -/
set_option autoImplicit false
set_option maxHeartbeats 230000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarAppointmentCharge
open Function Finset Filter Lattice Wilson RG Precision PhysicalNext.Repeat.Legato Exterior Work.F08 MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonIndependentCollarRootedWidth WilsonIndependentCollarPrintIncome
open FundedMarkedPathSelection WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e m:ℕ}

def coin (D k:ι→ℕ)(e:ℕ)(J:Finset ι)(c:ι):Credit:=
  WilsonIndependentCollarInkPrice.cost G (vigor G D k e Credit.leanC Credit.leanC) (mass k J) (e+1)
    J.card (Fintype.card (J.erase c))

theorem original (V:Realm G (e+1) Credit.leanC)(hm:V.anchor ≤ m)(J:Finset ι)(c:ι)(front:c∈J)
    (w:Widths G)(A:ℝ)(pos:0≤A):
    let U:=V.mint m hm
    let out:=issue w (e+1) (mass k J) U.gear
    let P:=FundedMarkedPathSelection.price V k D A J m
    U.σ≤1 → U.σ⁻¹≤V.y m → out.fee≤V.y m →
      glacier G (mass k J) (e+1)*(Real.exp (3*U.σ/8)*(out.fee*P))*sprigs J c (U.σ/2) ≤
      (coin (G:=G) D k e J c).buy (V.y m)*A^J.card:=by
  intro U out P cap shelf paid
  let VQ:=vigor G D k e Credit.leanC Credit.leanC
  have one:1≤VQ.buy (V.y m):=Credit.purchase _ (V.depth m hm)
  have count:0<J.card:=Finset.card_pos.mpr ⟨c,front⟩
  have pr:P ≤ (VQ.buy (V.y m)*A)^J.card:=by
    rw [mul_pow]
    change VQ.buy (V.y m)*A^J.card≤(VQ.buy (V.y m))^J.card*A^J.card
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg pos _)
    simpa only [pow_one] using pow_le_pow_right₀ one (show 1≤J.card by omega)
  have st:=sprigsPay front (0:Cover) (half_pos U.width)
  have sp:0 ≤ sprigs J c (U.σ/2):=(tsum_nonneg st.1).trans st.2.2
  have fee:0≤out.fee:=zero_le_one.trans out.funded
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left pr fee) (Real.exp_pos _).le) (gentle ..)) sp).trans
    (WilsonIndependentCollarInkPrice.original VQ (mass k J) (e+1) J c front U.width cap (V.depth m hm)
      shelf fee paid pos)

end YM.Integration.WilsonIndependentCollarAppointmentCharge
end
