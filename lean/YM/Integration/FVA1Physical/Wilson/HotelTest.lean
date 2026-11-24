import YM.Integration.FVA1Physical.Wilson.HotelPurchase

/-! Quantitative removal of all unsuccessful copied charts as a signed physical
reading. The normalization remains the measured, unrestricted vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology
variable {G : Gauge} {f c : Side} {S : StepData c f} {R : Rep G f}
theorem expect_on_chart (V : Config G c) {H : Set (Config G f)} (hH : MeasurableSet H)
    {σ C δ Λ w b y : ℝ} (adm : Admitted V R S σ C δ Λ w) (F : Config G f→ℝ) (mF : Measurable F)
    (hb : 0 ≤ b) (bound : ∀ U, |F U| ≤ b) (chanceH : chance S R V Hᶜ ≤ y) :
    |expect S R V F-expect S R V (H.indicator F)| ≤ b*y := by
  let A := H.indicator F
  let A' := Hᶜ.indicator F
  let I := Hᶜ.indicator (fun _=> (1:ℝ))
  have env : Envelope F := ⟨mF,b,bound⟩
  have aa : Envelope A := Envelope.piece hH env (Envelope.const 0)
  have ac : Envelope A' := ⟨mF.indicator hH.compl,b,fun U=>by
    by_cases h : U∈Hᶜ
    · simpa only [A',Set.indicator_of_mem h,Real.norm_eq_abs] using bound U
    simpa only [A',Set.indicator_of_notMem h,norm_zero] using hb⟩
  have ind : Envelope I := ⟨measurable_const.indicator hH.compl,1,fun U=>by
    by_cases h : U∈Hᶜ <;> simp [I,h]⟩
  have together : A+A'=F := by
    ext U
    by_cases h : U∈H <;> simp [A,A',h]
  have sum := e_sum V adm aa ac
  rw [together] at sum
  have hi : A' ≤ b • I := by
    intro U
    by_cases h : U∈H
    · simp [A',I,h]
    simpa [A',I,h] using ((le_abs_self (F U)).trans (bound U))
  have lo : (-b) • I ≤ A' := by
    intro U
    by_cases h : U∈H
    · simp [A',I,h]
    simpa [A',I,h] using (abs_le.mp (bound U)).1
  have right := nn V adm ((Envelope.const b).mul ind) ac hi
  have left := nn V adm ac ((Envelope.const (-b)).mul ind) lo
  change _ ≤ expect S R V (b • I) at right
  change expect S R V ((-b) • I) ≤ _ at left
  rw [e_mul] at right left
  change expect S R V I ≤ y at chanceH
  rw [show expect S R V F-expect S R V A=expect S R V A' by linarith only [sum]]
  exact (abs_le.mpr ⟨by linarith only [left],right⟩).trans (mul_le_mul_of_nonneg_left chanceH hb)

end YM.Integration.FVA1Physical.Wilson
