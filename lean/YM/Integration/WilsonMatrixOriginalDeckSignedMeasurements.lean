import YM.Integration.WilsonMatrixOriginalDeckHorizon

/-! The signed comparison invoice is the regulator limit of the actual finite Wilson measurements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckSignedMeasurements
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalDeckCutoff WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckRelative
open private identity from YM.Integration.WilsonMatrixOriginalDeckCutoff
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {S:Table R.family.book} {f:Extraction.Order}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Sum of the measured residuals over every intermediate step and every pair of genuine field grades. -/
def invoice (g:Test 2) (r:ℕ→ℝ) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (n:ℕ) : ℝ :=
  ∑i∈range n,amount (mixed B J h g (r (i+1)) (r i)-WilsonMatrixOriginalDeckGram.bank B F J h g (r (i+1))*V i)

/-- The same signed comparison at one original physical cutoff and period. -/
def finite (g:Test 2) (r:ℕ→ℝ) (positive:∀i,0<r i) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (n:ℕ) (z:ℕ×ℕ) : ℝ :=
  ∑i∈range n,amount (raw R B J h g (positive (i+1)) (r i) z-raw R B J h g (positive (i+1)) (r (i+1)) z*V i)

private theorem continuous_cost {I:Type*} [Fintype I] : Continuous (@WilsonMatrixOriginalDeckRelative.amount I _) := by
  unfold WilsonMatrixOriginalDeckRelative.amount
  fun_prop

/-- All rows and all radii approach the same physical invoice on the same original cutoff filter. -/
theorem limit (g:Test 2) (r:ℕ→ℝ) (positive:∀i,0<r i) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ)
    (n:ℕ) (u:Filter (ℕ×ℕ)) [u.NeBot] (period:u≤f.fuse) :
    Tendsto (finite R B J h g r positive V n) u (𝓝 (invoice R B F J h g r V n)) := by
  apply tendsto_finsetSum
  intro i _
  have joint := WilsonMatrixOriginalDeckCutoff.limit R B F J h g (positive (i+1)) (r i) u period
  have diag := WilsonMatrixOriginalDeckCutoff.limit R B F J h g (positive (i+1)) (r (i+1)) u period
  rw [WilsonMatrixOriginalDeckMixed.observed B F J h g (positive (i+1)),identity R B J h,mul_one] at diag
  exact continuous_cost.continuousAt.tendsto.comp (joint.sub (diag.mul tendsto_const_nhds))

/-- Pass from actual signed row costs to the cost of one complete trial step before any grade projection. -/
theorem columns {I:Type*} [Fintype I] (U V W:Matrix I I ℂ) (C:ℝ)
    (rows:∀b, (∑i,‖U i b-V i b‖)≤C*(∑i,‖W i b‖)) :
    amount (V-U)≤C*amount W := by
  classical
  calc amount (V-U)=∑b,∑i,‖U i b-V i b‖ := by
         unfold WilsonMatrixOriginalDeckRelative.amount
         rw [sum_comm]
         apply sum_congr rfl
         intro b _
         exact sum_congr rfl fun i _=>norm_sub_rev _ _
       _ ≤ ∑b,C*(∑i,‖W i b‖) := sum_le_sum fun b _=>rows b
       _ = _ := by rw [←mul_sum];congr 1;exact sum_comm

end YM.Integration.WilsonMatrixOriginalDeckSignedMeasurements
