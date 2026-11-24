import YM.Integration.WilsonAddressedOwnOffsetPrice
import YM.Integration.WilsonAddressedCollarWindow

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedCollarPrice
open Function Filter Real MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOffsetLedger
open WilsonAddressedReportedColumns WilsonInvariantActionPosition
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "h" => R.family.path.levels.clock.hatBeta
local notation "s" => R.family.S.scale
local notation "a" => R.family.S.a

private theorem prices (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit) (t : ℕ) :
    let k := (t:ℝ)+1
    let C := 5+G.slopeConstant*k
    ∀ᶠ m : ℕ in atTop,∀ j,m≤j → j≤berth R t m →
      Real.exp (k⁻¹*(s j-s m)) ≤ h m ∧
      2+Real.log (2+Real.log (h j)) ≤ C*h m ∧
      1+Real.sqrt (h j) ≤ C*h m := by
  intro k C
  have kp : 0<k := by dsimp [k]; positivity
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t zero_lt_one] with m step j _ fine
  have mh := (R.family.path.levels.fits.delayed m).le
  have jh := (R.family.path.levels.fits.delayed j).le
  have stable : s j-s m ≤ k*Real.log (h m) := by
    have budget := Real.log_le_log (div_pos (R.family.S.a_pos m) (R.family.S.a_pos _)) step.2.2
    rw [Real.rpow_one,Real.log_mul (pow_pos (zero_lt_one.trans_le mh) _).ne'
      (zero_lt_one.trans_le mh).ne',Real.log_pow] at budget
    have exactGap : s (berth R t m)-s m=Real.log (a m/a (berth R t m)) := by
      rw [Schedule.scale,Schedule.scale,Real.log_inv,Real.log_inv,Real.log_div
        (R.family.S.a_pos m).ne' (R.family.S.a_pos _).ne']
      ring
    refine (sub_le_sub_right ((OPE.scale_mono R.family.S).monotone fine) _).trans ?_
    rw [exactGap,show k*Real.log (h m) = (t:ℝ)*Real.log (h m)+Real.log (h m) by dsimp [k]; ring]
    exact budget
  have growth : Real.exp (k⁻¹*(s j-s m)) ≤ h m := by
    rw [← Real.exp_log (zero_lt_one.trans_le mh),Real.exp_le_exp]
    calc
      _ ≤ k⁻¹*(k*Real.log (h m)) := mul_le_mul_of_nonneg_left stable (inv_nonneg.mpr kp.le)
      _ = _ := by field_simp [kp.ne']
  have panel : h j ≤ (1+G.slopeConstant*k)*h m := by
    have log := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le mh)
    have bound := mul_le_mul_of_nonneg_left
      (stable.trans (mul_le_mul_of_nonneg_left (log.trans (sub_le_self _ zero_le_one)) kp.le))
      (Gauge.slopeConstant_pos simple).le
    change R.family.path.levels.clock.bar+G.slopeConstant*s j ≤ _
    change G.slopeConstant*(s j-s m) ≤ G.slopeConstant*(k*
      (R.family.path.levels.clock.bar+G.slopeConstant*s m)) at bound
    dsimp only [Calendar.hatBeta]
    linarith only [bound]
  have tmp : 2+Real.log (2+Real.log (h j)) ≤ 4+h j := by
    have hp : 0<2+Real.log (h j) := by linarith [Real.log_nonneg jh]
    linarith [Real.log_le_sub_one_of_pos hp, Real.log_le_sub_one_of_pos (zero_lt_one.trans_le jh)]
  have sq : 1+Real.sqrt (h j) ≤ 4+h j := by
    nlinarith [Real.sq_sqrt (zero_le_one.trans jh),sq_nonneg (Real.sqrt (h j)-1)]
  have cap : 4+h j ≤ C*h m := by dsimp [C]; linarith only [panel,mh]
  exact ⟨growth,tmp.trans cap,sq.trans cap⟩

/-- The polynomial exponent used by all transported basis rows is fixed by
    the physical alphabet even when the matching collar is made longer. -/
theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (shop : RG05Preconstruction.ReadoutPurchase R.b) (d t : ℕ) :
    let C := 5+G.slopeConstant*((t:ℝ)+1)
    ∀ᶠ m : ℕ in atTop,∀ N p (_live : m≤N) (z : Site (R.family.side N p)),
      ∃ (V : Sight R.family d p) (r : Emblems R.family d),
        Enrolled R.makes R.doors (cash R) m N p d (digits R N p z) V r ∧
        ∀ (y : Palette R.family d) j (away : m≤j) (_reached : j≤N), j≤berth R t m →
          let P := R.family.path.rep N p j
          let v := finer r away y
          ∃ x : Palette R.family d,
            Printed R.family d P 0 (kappa R.family.path j) (V j v) x v (cash R d j*size v) ∧
            size x ≤ C*(h m)^2*size y ∧
            size (weightsAt P.p.threshold x) ≤ C^(toll R.family d+1)*(h m)^(toll R.family d+2)*size y := by
  intro C
  have pos : 0 < ((t:ℝ)+1)⁻¹ := by positivity
  have base := WilsonAddressedOwnOffsetPrice.original R simple shop d _ pos
  filter_upwards [base,prices R simple slow t] with m course bound N p live z
  obtain ⟨V,r,legal,hearing⟩ := course N p live z
  refine ⟨V,r,legal,?_⟩
  intro y j away reached close P v
  obtain ⟨growth,income,shape⟩ := bound j away close
  obtain ⟨x,printed,w₀,w⟩ := hearing y j away reached
  have give : 0≤2+Real.log (2+Real.log (h j)) := by
    have hl := Real.log_nonneg (R.family.path.levels.fits.delayed j).le
    have hz : 1≤2+Real.log (h j) := by linarith
    linarith [Real.log_nonneg hz]
  have paid : (2+Real.log (2+Real.log (h j))) *
      (Real.exp (((t:ℝ)+1)⁻¹*(s j-s m))*size y) ≤ C*(h m)^2*size y := calc
    _ ≤ (C*h m)*(h m*size y) := mul_le_mul income
      (mul_le_mul_of_nonneg_right growth (size_ge _))
      (mul_nonneg (Real.exp_pos _).le (size_ge _)) (give.trans income)
    _ = _ := by ring
  refine ⟨x,printed,w₀.trans paid,w.trans ?_⟩
  calc
    _ ≤ (C*h m)^toll R.family d*(C*(h m)^2*size y) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) shape _) paid
        (mul_nonneg give (mul_nonneg (Real.exp_pos _).le (size_ge _)))
        (pow_nonneg (give.trans income) _)
    _ = _ := by rw [mul_pow,pow_succ,pow_add]; ring

end YM.Integration.WilsonAddressedCollarPrice
