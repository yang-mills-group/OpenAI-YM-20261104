import YM.Integration.QLocalInheritedGlyphPurchase

/-! Pre-length purchase of the original frozen expenses and actual collar
    charge of the physical large-cover bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedCoverPurchase
open Function Set Filter Lattice Wilson RG Pressure PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 AnalyticBridge VerifiedReset Precision Supply Input Org
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology BigOperators Classical

variable {G : Gauge}
def Paid (δ : ℝ) : Prediction G := fun {_} {D} {A} R =>
  (∀ j i, (R.expense j i).wanting = -(7/16 : ℝ)) ∧
  ∀ j x, A.delay.betaEntry j ≤ x → ∀ i, StepStages j i →
    Real.exp (Height.asset (R.expense j i)) ≤ betaF G x (D.L j) ^ δ

theorem prepaid (δ : ℝ) (hδ : 0 < δ) (s : Sheet G) (price : MapPrices) :
    Prepaid (Paid δ) s price := by
  intro Q E _ C z _ wanting
  refine ⟨fun _ => 0,fun _ _ D _ _ _ _ _ _ _ _ V _ => ?_⟩
  have stage j i (_ : StepStages j i) : ∀ᶠ x : ℝ in atTop,
      Real.exp (Height.asset (E j i)) ≤ betaF G x (D.L j) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp (Work.E09.betaF_growth G (D.L j))).eventually_ge_atTop _
  obtain ⟨β,_,hβ,h⟩ := collect_upper V.betaEntry _
    (fun j => eventually_transitions j _ _ (stage j))
  refine ⟨{V with betaEntry := β},⟨hβ,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW K I hp B A η q E' X J K' b hZ hY hm
  exact ⟨wanting,fun j x hx => h j x ((hW.beta j).trans hx)⟩

end YM.Integration.QLocalInheritedCoverPurchase
end
