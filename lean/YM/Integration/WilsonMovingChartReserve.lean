import YM.RG01Estimate.Reserves
import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply

/-! The authentic curvature, footprint and time reserve, on the same reporting
map and physical factor that receives all other before-run predictions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingChartReserve
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
variable {G : Gauge}

def Eligible (e:ℕ→ℕ→ℝ) : FundedCompanySelection.Prediction G :=
  fun {_} {_} {A} _=>Barrier A e

/-- Fund the genuine stage tariff before the register's later delay. The
reported time-base exponent can be prescribed separately at every transition. -/
theorem prepaid (e:ℕ→ℕ→ℝ) (positive:∀i j,StepStages j i→0<e j i) :
    FundedPredictionSupply.AllPrices (Eligible (G:=G) e) := by
    intro s fees target expense charted programs wages baton wanting
    refine ⟨fun _ => 0, ?_⟩
    intro l _ D w P Υ φ S θ p Px V hy
    let a i:= s.profile i
    have hx(j i:ℕ)(hk:StepStages j i) :∀ᶠ t:ℝ in atTop, Toft.stock G (Time.probe (a i)) * Real.exp (((a i).supportExponent+1)*81) ≤ t ∧ (radiusB t:ℝ)≤t∧Time.base G (a i)≤ t ^ (e j i):= by
        have hz:= (tendsto_rpow_atTop (positive i j hk)).eventually_ge_atTop (Time.base G (a i))
        filter_upwards [eventually_ge_atTop (Toft.stock G (Time.probe (a i)) * Real.exp (((a i).supportExponent+1)*81)),hz,(Work.E09.radiusB_small 1 zero_lt_one 1).bound zero_lt_one,eventually_gt_atTop 0] with t ht hz hh hT
        refine ⟨ht,?_,hz⟩; simpa only [pow_one,Real.rpow_one,Real.norm_of_nonneg (le_of_lt hT),Real.norm_of_nonneg (Nat.cast_nonneg _),one_mul] using hh
    obtain ⟨X,-,hv,hf⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (hx j))
    refine ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
    intro V' hZ bar wait priced H _alloy η q E mesh aux rider booth hK hY hm
    change Barrier _ _
    have ht m:=step_paid H.a m
    have hp m:= hf _ _ ((hZ.beta _).trans (H.valid.pays m)) _ (ht m)
    have hu m: a (H.a.clock.J m)=H.a.params m:= (params_eq H.valid m).symm
    refine ⟨fun m=> ?_,fun m=> (hp m).2.1,fun m=> ?_⟩
    · refine (RG01Estimate.Chart.relation (show Time.Same (H.a.params m) (H.a.budget m) from ⟨rfl,rfl,rfl⟩)).trans_le ?_
      rw [← hu]; exact (hp m).1
    intro a₀; change Time.base G (H.a.params m)≤_
    rw [← hu m]; exact (hp m).2.2

end YM.Integration.WilsonMovingChartReserve
end
