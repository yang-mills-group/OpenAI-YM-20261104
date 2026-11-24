import YM.Integration.WilsonThermometerWeakCanonicalAllowance
import YM.Integration.WilsonThermometerWeakOriginalRocket

/-! Real radius purchases for complete mixed regular and mandatory arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakInputNarrow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Next.Rank Perch Glimmer Tapes Atlas Station Vac.Numbers Edition
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics Tapes Paint
open Thirst Relation Corona Value Glyph Marker Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential Edition
open WilsonThermometerOwnOffsetRadii WilsonThermometerWeakCanonicalAllowance
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {n:Side} {ζ:I→Site n}
  {ι κ:Type} {p:BudgetPoint} {t e c:ℝ} {r w:I→ℝ}

theorem regular (A:ι→SourceAt G ζ) (income:Unpacks A p w e c) (pos:∀ i,0≤r i) (fee:∀ i,r i≤w i):Unpacks A p r e c:=by
  obtain ⟨cash,pay,stars⟩:=income
  refine ⟨cash,?_,stars⟩
  intro j
  obtain ⟨c0,pass⟩:=(transferD _ _ _ _).mp (pay j)
  refine (transferD _ _ _ _).mpr ⟨c0,?_⟩
  intro U clean
  exact (mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _=>pos i) (fun i _=>fee i)) (norm_nonneg _)).trans (pass U clean)

theorem forced (K:κ→Lifted G ζ p.threshold) (income:Unfold (p:=p) K w e c) (pos:∀ i,0≤r i) (fee:∀ i,r i≤w i):Unfold (p:=p) K r e c:=by
  obtain ⟨cash,pay,stars⟩:=income
  refine ⟨cash,?_,stars⟩
  intro j
  refine ⟨(pay j).1,?_⟩
  intro U
  exact (mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _=>pos i) (fun i _=>fee i)) (norm_nonneg _)).trans ((pay j).2 U)

theorem purchased (R:Run G) {D k:ℕ} {b:ℝ} (h:∀ j≤D,Accent.generator G j≤b)
    (one:1≤R.family.path.levels.clock.hatBeta k):
    let s:=clim R.family.path.levels k
    0≤Hat s^b ∧ Hat s^b≤radius R (maximum G D+1) k k:=by
  intro s
  have pos:0<Hat s:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le one))
  have hi:Hat s≤1:=by
    apply (inv_le_one₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le one))).mpr
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt one
  rw [WilsonThermometerWeakSourceRadius.native]
  exact ⟨Real.rpow_nonneg pos.le _,Real.rpow_le_rpow_of_exponent_ge pos hi (printed h)⟩

end YM.Integration.WilsonThermometerWeakInputNarrow
end
