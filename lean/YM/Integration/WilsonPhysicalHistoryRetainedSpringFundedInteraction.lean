import YM.Integration.WilsonPhysicalHistoryRetainedSpringPathTariff
import YM.Integration.WilsonPhysicalHistoryRetainedSpringInteraction

/-! Measured valuation of the actual cubic plus quartic part of the
previous path, with its own signed finite pitch and original root. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem interaction_zero {f : Side} (K : PathData G) (x : Site f) (z : Dir G f) (g : ℝ) :
    interactionTaylor K x z (fun b=>if b then 3 else 2) g=0 := by
  change siteTaylor K.cubic x z 2 g+siteTaylor K.quartic x z 3 g=0
  rw [flat_site_polynomial K.cubic x z (by decide : 2<3),flat_site_polynomial K.quartic x z (by decide : 3<4),zero_add]

private theorem scale_row {w D A g σ ε η : ℝ} (k : ℕ) (gp : 0<g)
    (paid : |w| *(D*(2*A/σ)^k)≤ε*g^(-η)) :
    |w| *(D*(2*A*|g|/σ)^k)≤ε*g^((k:ℝ)-η) := by
  calc _ = (|w| *(D*(2*A/σ)^k))*g^k:=by
          rw [abs_of_pos gp,show 2*A*g/σ=2*A/σ*g by ring,mul_pow]; ring
    _ ≤ (ε*g^(-η))*g^k:=mul_le_mul_of_nonneg_right paid (pow_nonneg gp.le k)
    _ = _:=by
      rw [mul_assoc,←Real.rpow_natCast,←Real.rpow_add gp]
      congr 2
      ring

theorem funded_interaction (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (r K l : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N per : ℕ,m+1<N →
      let j:=m+1
      let S:=V.clock.op m per
      let s:=V.clock.hatBeta m
      let g:=Pert.Asymptotics.regulatorRun R.family N per j
      let w:=g^2*pitchTail R N j r g+R.alloy.B.kin.alpha N j
      let path:=(R.family.path.rep N per j).path
      ∀ {W μ budget : ℝ} {P : Teller G} {Q : Target G P} {o : Target.Order G W}
        {T : Tube G S} {Y : Rep G (R.family.side j per)},
        (H : Cash W s μ S.patch.L Q o budget T Y) → 0≤Pressure.temp s →
        WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L o≤1+Real.log (betaF G s S.patch.L) →
        ∀ (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil (R.family.side m per) (R.family.side j per)))
          (i : Greenbelt.Reserve S) (tag : S.Choices) (y : (Greenbelt.allot i).Slice G) (x : Site (R.family.side j per)),
        let F:=Greenbelt.allot i
        let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 fan i tag
        let E:=fun z : Air (R.family.side j per) G=>(w:ℂ)*((interactionAt path x ((X.wrapY y).input
          ((X.wrapY y).liftA (Integral.temperature g) z)):ℂ)-
            interactionTaylor path x (angularSample F z) (fun b=>if b then K+3 else K+2) g)
        Integrable E X.dice ∧ Integrable (fun z=>‖E z‖^(l+1)) X.dice ∧
          (∫ z,‖E z‖^(l+1) ∂X.dice)≤(ε*g^(((K+3:ℕ):ℝ)-η))^(l+1) := by
  intro V
  have half : 0<ε/2:=by positivity
  filter_upwards [cofinal_path_tariff R simple slow v rows r ((K+3)*(l+1)-1) (K+3) half hp,
    cofinal_path_tariff R simple slow v rows r ((K+4)*(l+1)-1) (K+4) half hp,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)]
    with m three four small
  intro N per later j S s g w path W μ budget P Q o T Y H temp cost χ fan i tag y x F X E
  let D:=V.params j
  let q:=fun b : Bool=>if b then K+3 else K+2
  have selected : R.family.path.Conv N per j:=R.makes.wilson.represents N per j later.le
  have actual : path.Bounds D.clip D.width D.paths (V.clock.loopCap j):=by
    dsimp only [path,D,V]
    rw [←selected.clip]
    exact selected.good.paths
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per j later.le
  have atMost : g≤1:=(small N per later.le).le
  obtain ⟨measured,integrable,receipt⟩:=chamber_interaction H temp χ fan i tag y actual x q l g w gp
  have row3:=scale_row (K+3) gp (three N per later o cost)
  have row4:=scale_row (K+4) gp (four N per later o cost)
  have grades : g^(((K+4:ℕ):ℝ)-η)≤g^(((K+3:ℕ):ℝ)-η):=by
    apply Real.rpow_le_rpow_of_exponent_ge gp atMost
    push_cast
    linarith
  have cap:=add_le_add row3 (row4.trans (mul_le_mul_of_nonneg_left grades half.le))
  have sum : ε/2*g^(((K+3:ℕ):ℝ)-η)+ε/2*g^(((K+3:ℕ):ℝ)-η)=ε*g^(((K+3:ℕ):ℝ)-η):=by ring
  refine ⟨measured,integrable,receipt.trans (pow_le_pow_left₀ ?_ (cap.trans_eq sum) _)⟩
  have positive (b : Bool) : 0≤|w| *(D.paths*(2*speedPrice G S.patch.L o.eta o.gap o.ample
      ((q b+1)*(l+1)-1)*|g|/D.width)^(q b+1)):=by
    have M:=(speed_price_pos G S.patch.L o.eta o.gap o.ample ((q b+1)*(l+1)-1)).le
    positivity [D.paths_pos,D.width_pos]
  exact add_nonneg (positive false) (positive true)

end YM.Integration.OriginalMarkedRunAction
