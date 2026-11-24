import YM.Integration.WilsonOriginalTwoFlatIRFiled

/-! The same original infrared stop works for all regulators and all the
ordinary faces. Its height-zero return includes every scalar deposited by the
captured source in the intervening Wilson blocks. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRStopped
open Function Filter Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal
open Push.Local Push.AbsoluteSums Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open WilsonOriginalTwoFlatIRHalo (roof power)
open WilsonOriginalTwoFlatIRFiled (reserve)
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "T" => R.family.path.levels
local notation "Sec" => R.family.localSection 0
local notation "Y" => R.family.params

set_option linter.unusedVariables false in
theorem original (simple:G.Simple)(slow:∀m,((C).S.block m).val≤Real.log (Lambda (T) m))
    (ready:WilsonReportLampForecast.Ready (T))(D₀:XSpace.Run){stage u d:ℕ}
    (B:Band R D₀ stage)(v:Stop R D₀ B u d)(cu:(C).ref 0≤u)(P:ℕ):
    ∀ᶠ h:ℕ in atTop,let c:=B.reporter+h
    ∀N per:ℕ,∀hc:c<N,
    let rep:=(C).path.rep N per c
    let g:=regulatorRun C N per c
    let x:=3*g⁻¹
    ∀{V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    {o:V→Site ((C).side c per)}{p:BudgetPoint}(L:Lamps X ι G p o J)(same:rep.p=p)
    (s:J.Mode)(Z:Support ((C).side c per))(center:0∈Z)(reside:∀a∈s.val,o a∈Z)
    (rad:ℕ)(near:∀a∈s.val,separation (o a) 0≤rad)(inside:rad≤rep.p.B)
    (housed:Z⊆halo rep.p.B {0}){α:ℝ}(strip:rep.p.supportExponent≤α)
    (w:V→ℝ)(wp:∀v,0<w v)(D E:ℕ){K C₀ C₁ H:ℝ}(one:1≤K)(wh:0≤H)
    (wage:(Poly.toll w s)⁻¹≤H*x^E)(h₀:0≤C₀)(h₁:0≤C₁)
    (cost₀:C₀≤K*x^D)(cost₁:C₁≤K*x^D)
    (he:L.Paid w p.B (p.supportExponent+2) C₀)(hg:Gross L w p.B (p.supportExponent+2) C₁)
    (ou:Opened C 0 u per)(ov:Opened C 0 (v.date h) per)
    (reach:4*(P+(power s.val.card D+E+2))≤d),
    let e:=power s.val.card D+E+2
    let charge:=reserve (roof J s (Sec) (Y) α K) H*3^e
    ∀t:X,let M:=fun U=>(rep.eval U:ℂ)*(Poly.pass (bare L t U)).part s
    ∀uc:u≤c,‖reading R (N:=N) M u uc-reading R (N:=N) M (v.date h) (v.upper h)‖≤charge*g^P:=by
  obtain ⟨first,funded⟩:=eventually_atTop.mp (WilsonOriginalTwoFlatIRFiled.original R simple slow ready)
  filter_upwards [v.heard,eventually_ge_atTop first] with h move past c N per hc
  intro rep g x V X ι _ _ _ J o p L same s Z center reside rad near inside housed α strip w wp D E K C₀ C₁ H
    one wh wage h₀ h₁ cost₀ cost₁ he hg ou ov reach e charge t M uc
  have ⟨gp,small,gap,_⟩:=move.2 N per hc.le
  have atC:first≤c:=past.trans (Nat.le_add_left _ _)
  obtain ⟨posted,price⟩:=funded c atC N per hc L same s Z center reside rad near inside housed strip w wp
    D E one wh wage h₀ h₁ cost₀ cost₁ he hg
  have hearing:=WilsonThermometerUnitFilingStops.two_stops R simple cu move.1 (v.upper h) hc.le ou ov (posted t)
  have rate:(C).S.a c/((C).S.a (v.date h))≤(g^(4*(P+e)))^2:=
    gap.trans (pow_le_pow_left₀ (pow_nonneg gp.le _) (pow_le_pow_of_le_one gp.le small reach) _)
  have rp:0≤roof J s (Sec) (Y) α K:=by dsimp [roof,WilsonOriginalTwoFlatIRHalo.factor₀];positivity
  have lp:0≤charge:=by dsimp only [charge,WilsonOriginalTwoFlatIRFiled.reserve];positivity
  apply hearing.trans (WilsonOriginalTwoFlatIRClock.spend R gp lp rate ?_)
  simpa only [x,charge,e,mul_pow,mul_assoc] using price

end YM.Integration.WilsonOriginalTwoFlatIRStopped
