import YM.Integration.QLocalSelectedVacuumGrades
import YM.Integration.QLocalGradeAddresses
import YM.Integration.WilsonLimitConstruction.FundedSignedPredictionRatio

/-! Charge the discarded physical vacuum layer bank at the actual measured coupling forecast. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalForecastOrderReadout

open Filter Lattice Wilson RG Marker PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalVacuumOrderRestriction WilsonLimitConstruction Comparison.RG02 PhysicalWilsonActionConvention Pert.Asymptotics
open scoped Classical Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {J : Request V}
    (R : Run G) {A : NumericSchedule R.family J} {caps : Handoff.OutputCapacities} {K : NumericPrices A}

def Receipt {z : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A z}
    (M : FundedPhysicalCatalogue.Purchase caps K F) (p : ℕ) (epsilon eta : ℝ) : Prop :=
  let b := A.outputNorm z.level
  let bank := extra (M.plan.layers z.level) p
  let g' := Currency.gain (M.plan.predict z.level)
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  let B := M.vacuum.packets
  0<M.plan.predict z.level ∧
  (∀ a∈bank, a.packet.Invoice b (ZeroAwareCappedRenderInvoice.credit B a)) ∧
  debit B p g'≤epsilon*g^((p:ℝ)+1-eta) ∧
  ∀ (E : Activities G (R.family.side z.level z.period)) (d k : ℝ), E.Valid b d k →
    let out := Render.adorn (Render.prefactor g') E bank
    out.Valid b (d+debit B p g') k ∧ out.forced=E.forced ∧ out.K=E.K

/-- The original measured quiet-bond transport can include the genuine finite/cover correction.
All subsequent cutoff, cells, independent inputs and full signed output records stay arbitrary. -/
theorem cover (hG : G.Simple) (hT : ActualRunNativeComponentRecipe.Attached R)
    (A : NumericSchedule R.family J) (K : NumericPrices A) (caps : Handoff.OutputCapacities)
    (p : ℕ) (epsilon eta : ℝ) (hε : 0<epsilon) (hη : 0<eta) :
    ∀ᶠ m : ℕ in atTop, ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A z) (M : FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) → Receipt R M p epsilon eta := by
  filter_upwards [QLocalSelectedVacuumGrades.bank (Γ:=Γ) R A hG K caps p eta epsilon hη hε,
    FundedCoverPredictionRatio.predicted_fine R hG hT (R:=Γ) caps A K] with m paid gains z hz Y F M contact
  obtain ⟨pos,l,u⟩ := gains z hz Y F M contact
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  have hg : 0<g := Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt z.below)
  have hl := (le_div_iff₀ hg).1 l
  obtain ⟨rows,bill⟩ := paid z hz _ M.vacuum M.output_layers_paid (Currency.gain (M.plan.predict z.level))
    (by linarith only [hl]) ((div_le_iff₀ hg).1 u)
  exact ⟨pos,rows,bill,fun E d k valid => QLocalGradeAddresses.admitted M.vacuum.packets M.output_layers_paid
    (A.output_width_pos z.level) p _ E valid⟩

theorem signed (hG : G.Simple) (hT : ActualRunNativeComponentRecipe.Attached R)
    (A : NumericSchedule R.family J) (K : NumericPrices A) (caps : Handoff.OutputCapacities)
    (p : ℕ) (epsilon eta : ℝ) (hε : 0<epsilon) (hη : 0<eta) :
    ∀ᶠ m : ℕ in atTop, ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A z) (M : SignedAnalyticOutput caps Y K F),
      Receipt R (FundedPhysicalCatalogue.ofSigned M) p epsilon eta := by
  filter_upwards [cover (Γ:=Γ) R hG hT A K caps p epsilon eta hε hη] with m paid z hz Y F M
  exact paid z hz Y F (FundedPhysicalCatalogue.ofSigned M) (FundedExactKineticContact.tested R M hG _)

end YM.Integration.QLocalForecastOrderReadout
end
