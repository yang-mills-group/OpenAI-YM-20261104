import YM.Integration.WilsonVacuumPreResetCurvaturePrice
import YM.Integration.WilsonVacuumPreResetRenderReserve

/-! The original two-date fee for the quadratic, cubic and quartic paths.
Its schedule is chosen before the common progression and all physical tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvatureReserve
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


def anchor (T:RG.Stage)(k:ℕ):ℝ:=(Fintype.card Signed:ℝ)*Real.exp ((T.supportExponent+9)*k)

def head (G:Gauge)(T D:RG.Stage):ℝ:=
  |factor| *turnFee (Time.probe T)* (lowFee G (Time.probe T) D.width*lowerSize D.clip D.paths)

def arm (G:Gauge)(T D:RG.Stage)(k:ℕ):ℝ:=
  |factor| *turnFee (Time.probe T)*(Geo.highFee G k (Time.probe T) D.width*D.paths)

def income (G:Gauge)(T D:RG.Stage):ℝ:=
  1+4*|T.supportExponent+9|/D.width+anchor T lowCount*|head G T D|+
    (anchor T (octave 3)*|arm G T D 3|+anchor T (octave 4)*|arm G T D 4|)

def Issued : FundedCompanySelection.Prediction G:=
  fun {_} {_} {A} _=>∀m:ℕ,let V:=A.B.a
    income G (V.params m) (V.params (m+1))≤Real.log (V.clock.hatBeta m)

theorem prepaid : FundedPredictionSupply.AllPrices (@Issued G):=by
  intro s fees target expense charted programs wages baton wanting
  refine ⟨fun _=>0,?_⟩
  intro l _ D w P Υ φ S θ p Px V hy
  let a i:=s.profile i
  have hx (j i:ℕ) (_:StepStages j i):∀ᶠ b:ℝ in atTop,income G (a i) (a j)≤Real.log b:=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨X,-,hv,hf⟩:=collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (hx j))
  refine ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' hZ bar wait priced H _alloy η q E mesh aux rider booth hK hY hm
  change ∀m:ℕ,_
  intro m
  have h:=hf _ _ ((hZ.beta _).trans (H.valid.pays m)) _ (step_paid H.a m)
  have first:a (H.a.clock.J m)=H.a.params m:=(params_eq H.valid m).symm
  have next:a (H.a.clock.J (m+1))=H.a.params (m+1):=(params_eq H.valid (m+1)).symm
  rwa [first,next] at h

end YM.Integration.WilsonVacuumPreResetCurvatureReserve
