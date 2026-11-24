import YM.Integration.WilsonMeasuredOriginalCatalogueUnion
/-! Evaluate the native signed union at the one original child, after restoring an incoming coupling grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointFiledValue
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 FVA1Physical.TwoReset
open AnalyticBridge.SectorAffine.Offset WilsonMeasuredTransitionCatalogue
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {C V X:Type} [Fintype C] [Fintype V]
  {I:C→Type} {K:V→Type} {P:C→Passport n Unit} {S:V→Passport n Unit}
  {J:Census Unit} {D:ℕ}
variable (F:(z:C)→I z→Row (P z) J G X) (T:(v:V)→K v→Row (S v) J G X)

open WilsonMeasuredOriginalCatalogueUnion
variable (r:ℝ) (c:V→ℕ→ℝ)
variable (L:Layout G) (tape:Finset Age)

local notation "model" => WilsonMeasuredOriginalCatalogueUnion.rows F T
theorem original (ℓ:ℕ)(g:ℝ)(s:J.Mode)(t:X)(U:Config G n):
    (∑a:Names C V D,weight r c a • (g^(ℓ+lag a) • (Spill.Foundry.uncut (model a) g t U).part s))=
      g^ℓ • (r • (∑z,(Spill.Foundry.uncut (F z) g t U).part s) -
      ∑v,(∑ν:Fin (D+1),(c v ν)*g^ν.val) • (Spill.Foundry.uncut (T v) g t U).part s):=by
  classical
  rw [← WilsonMeasuredOriginalCatalogueUnion.field (D:=D) F T r c g s t U,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [pow_add,mul_smul,smul_comm (weight r c a) (g^ℓ)]
end YM.Integration.WilsonOlderFreshPointFiledValue
end
