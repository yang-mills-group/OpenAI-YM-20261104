import YM.Integration.WilsonRootedPhysicalCommonPrice

/-! A single original finite-stage purchase makes the explicit cover cut and the distinct length scale affordable. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalCommonCut

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

/-- A retained native decay rate on both genuine adjacent original stages. -/
def decay (i j:RG.Stage):ℝ:=min i.width j.width / 12

def Eligible:FundedCompanySelection.Prediction G:=fun {_} {D} {A} K=>∀m:ℕ,
  let H:=A.B.a
  let j:=H.clock.J (m+1)
  let i:=H.clock.J m
  let x:=H.clock.hatBeta m
  4≤x ∧ WilsonRootedPhysicalCommonPrice.price G (H.params m) (Pane.cloak D j)≤x ∧
    H.clock.hatBeta (m+1)≤2*x ∧
    (i:ℝ)+8+|(H.params m).supportExponent| ≤ decay (H.params m) (H.params (m+1))*Real.log x ∧
    (K.expense j i).wanting=-(7/16:ℝ)

theorem prepaid:FundedPredictionSupply.AllPrices (@Eligible G):=by
  intro s fees target expense charted programs wages baton wanting
  refine ⟨fun _=>0,?_⟩
  intro l _ D w P Υ φ S θ p Px V hy
  let a:=s.profile
  let b (j:ℕ):=(a j).drift + |G.slopeConstant*Real.log (D.L j).val| + 1
  have stage (j i:ℕ)(_:StepStages j i):∀ᶠx:ℝ in atTop,
      4≤x ∧ WilsonRootedPhysicalCommonPrice.price G (a i) (b j)≤x ∧
        G.slopeConstant*Real.log (D.L j).val≤x ∧ (i:ℝ)+8+|(a i).supportExponent| ≤ decay (a i) (a j)*Real.log x:=by
    have d:0<decay (a i) (a j):=div_pos (lt_min (a i).width_pos (a j).width_pos) (by norm_num)
    filter_upwards [eventually_ge_atTop (4:ℝ),eventually_ge_atTop (WilsonRootedPhysicalCommonPrice.price G (a i) (b j)),
      eventually_ge_atTop (G.slopeConstant*Real.log (D.L j).val),Real.tendsto_log_atTop.eventually_ge_atTop (((i:ℝ)+8+|(a i).supportExponent|)/decay (a i) (a j))] with x a₀ a₁ a₂ a₃
    exact ⟨a₀,a₁,a₂,by simpa only [mul_comm] using (div_le_iff₀ d).mp a₃⟩
  obtain ⟨X,_,hv,hf⟩:=collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (stage j))
  refine ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' hZ bar wait priced H _alloy η q E mesh aux rider booth hK hY hm
  change ∀m:ℕ,_
  intro m
  obtain ⟨x,coin,inc,room⟩:=hf _ _ ((hZ.beta _).trans (H.valid.pays m)) _ (step_paid H.a m)
  have first:a (H.a.clock.J m)=H.a.params m:=(params_eq H.valid m).symm
  have next:a (H.a.clock.J (m+1))=H.a.params (m+1):=(params_eq H.valid (m+1)).symm
  rw [first] at coin room
  rw [next] at room
  refine ⟨x,coin,?_,room,wanting _ _⟩
  rw [beta_eq H.valid m,Pressure.betaF]
  linarith only [inc]

/-- The cover radius is logarithmic in the actual original coarse temperature. -/
def cover (x:ℝ)(r:ℕ):ℕ:=⌈((r:ℝ)+6)*Real.log (2*x)⌉₊

/-- The length cost is in the separate original block-size unit. -/
def length (x:ℝ):ℕ:=⌈(Real.log x)^2⌉₊

variable (R:Run G)

theorem wallet (paid:Eligible R.kit)(m:ℕ):
    WilsonRootedPhysicalLocalPeriod.wallet R m≤7*(R.alloy.B.a.clock.hatBeta m)^2:=by
  obtain ⟨x,c,next,_,want⟩:=paid m
  exact WilsonRootedPhysicalCommonPrice.original R m x next (by rw [want]; norm_num) c

end YM.Integration.WilsonRootedPhysicalCommonCut
