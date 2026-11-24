import YM.Integration.WilsonMatrixOriginalDeckDyadicWindow

/-! Finite original regulator receipts for the full signed cross/self Gram on each radius interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckEdgeIncome
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato WilsonMatrixOriginalDeckMixed
open WilsonMatrixOriginalDeckFiled WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckSignedMeasurements
open private identity from YM.Integration.WilsonMatrixOriginalDeckCutoff
open private continuous_cost from YM.Integration.WilsonMatrixOriginalDeckSignedMeasurements
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (L:Layout F) (J:ℝ→PhysMS.tower S) (h:ℕ)

open WilsonMatrixOriginalDeckFiledDebit

def cost (g:Test 2) (r:ℕ→ℝ) (pos:∀i,0<r i) (w:ℕ→Glyph B h→R.family.label h)
    (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (i:ℕ) (z:ℕ×ℕ) : ℝ :=
  amount (field R B F L h g (pos (i+1)) (r i) (w (i+1)) (w i) z-
    field R B F L h g (pos (i+1)) (r (i+1)) (w (i+1)) (w (i+1)) z*V i)

/-- Each true two-date measurement is allowed its own regulator threshold and signed comparison.
The finite common period and cutoff are purchased after all the radii are fixed. -/
theorem combined (g:Test 2) (r:ℕ→ℝ) (pos:∀i,0<r i) (w:ℕ→Glyph B h→R.family.label h)
    (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (u:Filter (ℕ×ℕ)) (n:ℕ) (δ:ℝ)
    (receipts:∀i<n,∀ᶠz in u,cost R B F L h g r pos w V i z≤δ) :
    ∀ᶠz in u,debit R B F L h g r pos w V n z≤n*δ := by
  have together:∀ᶠz in u,∀i:Fin n,cost R B F L h g r pos w V i z≤δ:=
    Filter.eventually_all.mpr (fun i=>receipts i i.isLt)
  filter_upwards [together] with z all
  calc debit R B F L h g r pos w V n z = ∑i∈range n,cost R B F L h g r pos w V i z:=rfl
       _ ≤ ∑_i∈range n,δ:=sum_le_sum (fun i hi=>all ⟨i,mem_range.mp hi⟩)
       _ = n*δ:=by simp

end YM.Integration.WilsonMatrixOriginalDeckEdgeIncome
