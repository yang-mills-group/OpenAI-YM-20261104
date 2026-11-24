import YM.RG01Estimate.Reserves
import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply

/-! The authentic curvature, footprint and time reserve, on the same reporting
map and physical factor that receives all other before-run predictions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingTrebleMargin
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
open WilsonLimitConstruction.FundedCompanySelection
variable {G : Gauge}

/-- The geometric margin on the original stage width, chosen before the register dates. -/
def Wider {G : Gauge} (a : ℝ) : Prediction G := fun {M} {_} {A} _ =>
  ∀ j x, A.delay.betaEntry j ≤ x → ∀ i, StepStages j i →
    ((M.p.profile i).supportExponent+a) / radiusB x ≤ (M.p.profile i).width/2

theorem prepaid {G : Gauge} (a : ℝ) : FundedPredictionSupply.AllPrices (@Wider G a) := by
  intro s fees target expense charted programs wages baton wanting
  refine ⟨fun _ => 0,?_⟩
  intro l _ D w P Z φ S θ p cost V cap
  have h := @YM.Work.E01.radiusB_tendsto
  have hp (i:ℕ) : ∀ᶠ x in atTop, ((s.profile i).supportExponent+a) / radiusB x ≤ (s.profile i).width/2 :=
    (((tendsto_const_nhds (x:=(s.profile i).supportExponent+a)).div_atTop (tendsto_natCast_atTop_atTop.comp h)).eventually (gt_mem_nhds (half_pos (s.profile i).width_pos))).mono (fun _ H=>H.le)
  obtain ⟨X,-,hv,hf⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i _ => hp i))
  refine ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW bar wait price B A η reset exchange menu aux rider booth shelter works divides j x hx i hi
  exact hf j x ((hW.beta j).trans hx) i hi

end YM.Integration.WilsonMovingTrebleMargin
end
