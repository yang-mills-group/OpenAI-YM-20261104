import YM.Integration.WilsonRootedHeldAffineCenter
import YM.Integration.WilsonRootedPhysicalCommonCut

/-! A before-run purchase of the true physical window error at the normal center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineWallet
open Filter Function Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Next.Foundations UVNext.CouplingReset
open Pressure Pressure.Stores ConnectedActivityE6 Coat Control Window Census Blaze
open FullVolume WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology BigOperators Classical
variable {G:Gauge}{W:ℝ}

/-- The coordinate-to-color price, retaining the original block, radius and pressure. -/
def charge (G:Gauge)(L:Side){W:ℝ}(o:Target.Order G W)(x:ℝ):ℝ :=
  (Fintype.card G.ColorIndex:ℝ)*(2*(o.ample*distPay o.eta o.gap o.ample
    (tubularPrice G L) (radiusB x))*(o.cap*fiery G x L))

theorem rate (L:Side)(o:Target.Order G W)(d:ℝ):
    Rate G L d (charge G L o):=by
  have scraps:=o.f.physical G L d (tubularPrice G L)
  have both:=scraps.mul (Rate.flame (G:=G) (L:=L))
  have fees:=(both.mul_left ((Fintype.card G.ColorIndex:ℝ)*2*o.ample*
    payE o.eta o.gap o.ample (tubularPrice G L)*o.cap)).weaken (show d+(-(1/2:ℝ))≤d by linarith)
  refine fees.congr (Eventually.of_forall fun x=>?_ )
  unfold charge distPay
  ring

def Eligible {G:Gauge}:Prediction G:=fun {_} {D} {A} H=>
  ∀j i, StepStages j i → ∀x:ℝ,A.delay.betaEntry j≤x →
    charge G (D.L j) (H.shape.o j i) x ≤ betaF G x (D.L j)^(-(i:ℝ))

theorem prepaid {G:Gauge}:FundedPredictionSupply.AllPrices (@Eligible G):=by
  intro s cost target expense charted programs wages baton wanting
  refine ⟨fun _=>0,?_⟩
  intro L _ D w u Z scouts θ stages stages' quoted V quarter
  have stage (j i:ℕ)(_st:StepStages j i):∀ᶠ x:ℝ in atTop,
      charge G (D.L j) (Z.o j i) x≤ betaF G x (D.L j)^(-(i:ℝ)):=by
    exact (rate (D.L j) (Z.o j i) (-(i:ℝ)-1) (-(i:ℝ)) (by linarith)).mono
      (fun x h=>(le_abs_self _).trans h)
  obtain ⟨next,_,up,paid⟩:=collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (stage j))
  refine ⟨{V with betaEntry:=next},⟨up,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' grow bar wait funded price _alloy η settle exchange menu ax rider booth present good locked j i st x hx
  exact paid j x ((grow.beta j).trans hx) i st

end YM.Integration.WilsonRootedHeldAffineWallet
