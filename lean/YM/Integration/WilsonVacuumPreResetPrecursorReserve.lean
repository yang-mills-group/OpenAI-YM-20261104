import YM.Integration.WilsonVacuumPreResetCurvatureReserve

/-! A prior election for the kinetic paths at the landing date itself. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrecursorReserve
open RG01Estimate
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Laplace Pressure ConnectedActivityE6 Coat Evoc Push Deck
open Censor Censor.Toft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open FullVolume WilsonLimitConstruction RG01Estimate.Chart
open Comparison.Density Comparison.Density.Render
variable {G:Gauge}


def Issued : FundedCompanySelection.Prediction G:=
  fun {_} {_} {A} _=>∀m:ℕ,let V:=A.B.a
    WilsonVacuumPreResetCurvatureReserve.income G (V.params m) (V.params m)≤Real.log (V.clock.hatBeta m)

theorem prepaid : FundedPredictionSupply.AllPrices (@Issued G):=by
  intro s fees target expense charted programs wages baton wanting
  refine ⟨fun _=>0,?_⟩
  intro l _ D w P Υ φ S θ p Px V hy
  let a i:=s.profile i
  have hx (j i:ℕ) (_:StepStages j i):∀ᶠ b:ℝ in atTop,WilsonVacuumPreResetCurvatureReserve.income G (a i) (a i)≤Real.log b:=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨X,-,hv,hf⟩:=collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (hx j))
  refine ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' hZ bar wait priced H _alloy η q E mesh aux rider booth hK hY hm
  change ∀m:ℕ,_
  intro m
  have h:=hf _ _ ((hZ.beta _).trans (H.valid.pays m)) _ (step_paid H.a m)
  have first:a (H.a.clock.J m)=H.a.params m:=(params_eq H.valid m).symm
  rwa [first] at h

end YM.Integration.WilsonVacuumPreResetPrecursorReserve
