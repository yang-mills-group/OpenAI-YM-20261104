import YM.Integration.WilsonMovingChartReserve
import YM.Integration.WilsonVacuumPreResetLiftedClock
import YM.Integration.FundedCloverWidthMoment

/-! Before-run purchase of the genuine curvature and corrected period derivative
constants through the requested ranks on each original reporting stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetRenderReserve
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

def base (G:Gauge)(T:RG.Stage)(k:ℕ):ℝ:=
  let B:=Time.probe T
  let A:=T.supportExponent+6
  (1+|Frame.cost B|)*(1+|factor|)*(1+|Comparison.Density.Render.bloom G B|)*Real.exp (81*A)*
    (1+|Wages.startup G k T.power T.order|)*Real.exp (A*(1+2*(k:ℝ)))*
    FundedCloverWidthMoment.coefficient (Wages.grade k T.power T.order)

def amount (G:Gauge)(T:RG.Stage)(k:ℕ)(x:ℝ):ℝ:=
  base G T k*(2*Real.log x)^(Wages.grade k T.power T.order+2)

private theorem log_tariff (c:ℝ)(d:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠ t:ℝ in atTop, c*(2*Real.log t)^d≤t^η:=by
  let K:ℝ:=(1+|c|)*2^d
  have hp:0<K:=by dsimp [K];positivity
  have small:=(isLittleO_log_rpow_rpow_atTop (d:ℝ) pos).def (inv_pos.mpr hp)
  filter_upwards [small,eventually_gt_atTop (1:ℝ)] with x h hx
  have x0:0<x:=by linarith
  have hl:0≤Real.log x:=(Real.log_pos hx).le
  have paid:(Real.log x)^d≤K⁻¹*x^η:=by
    simpa only [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hl d),
      abs_of_nonneg (Real.rpow_nonneg x0.le η)] using h
  calc
    c*(2*Real.log x)^d = (c*2^d)*(Real.log x)^d:=by rw [mul_pow];ring
    _ ≤ K*(Real.log x)^d:=by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hl _)
      apply mul_le_mul_of_nonneg_right _ (by positivity : 0≤(2:ℝ)^d)
      linarith [le_abs_self c]
    _ ≤ K*(K⁻¹*x^η):=mul_le_mul_of_nonneg_left paid hp.le
    _ = x^η:=by rw [←mul_assoc,mul_inv_cancel₀ hp.ne',one_mul]

def Eligible (cap:ℕ→ℕ→ℕ)(rate:ℕ→ℕ→ℝ):FundedCompanySelection.Prediction G:=
  fun {_} {_} {A} _=>∀m:ℕ, let a:=A.B.a
    ∀ k≤cap (a.clock.J (m+1)) (a.clock.J m),
      amount G (a.params m) k (a.clock.hatBeta m) ≤
        a.clock.hatBeta m^(rate (a.clock.J (m+1)) (a.clock.J m))

theorem prepaid (cap:ℕ→ℕ→ℕ)(rate:ℕ→ℕ→ℝ)(positive:∀i j,StepStages j i→0<rate j i):
    FundedPredictionSupply.AllPrices (Eligible (G:=G) cap rate):=by
  intro s fees target expense charted programs wages baton wanting
  refine ⟨fun _=>0,?_⟩
  intro l _ D w P Υ φ S θ p Px V hy
  let a i:=s.profile i
  have hx (j i:ℕ)(hk:StepStages j i):
      ∀ᶠ b:ℝ in atTop,∀k≤cap j i,amount G (a i) k b≤b^(rate j i):=by
    have all:∀ᶠ b:ℝ in atTop,∀k∈Finset.range (cap j i+1),amount G (a i) k b≤b^(rate j i):=
      (Finset.eventually_all _).2 fun k _=>log_tariff _ _ (positive i j hk)
    filter_upwards [all] with b hb
    exact fun k h=>hb k (Finset.mem_range.mpr (by omega))
  obtain ⟨X,-,hv,hf⟩:=collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (hx j))
  refine ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' hZ bar wait priced H _alloy η q E mesh aux rider booth hK hY hm
  change ∀m:ℕ, _
  intro m _a k hk
  have paid:=hf _ _ ((hZ.beta _).trans (H.valid.pays m)) _ (step_paid H.a m) k hk
  have hu:a (H.a.clock.J m)=H.a.params m:= (params_eq H.valid m).symm
  rwa [hu] at paid

end YM.Integration.WilsonVacuumPreResetRenderReserve
