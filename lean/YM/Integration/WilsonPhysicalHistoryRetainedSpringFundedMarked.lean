import YM.Integration.WilsonRetainedJointVertexWeightedChamber
import YM.Integration.WilsonPhysicalHistoryRetainedSpringJointLoad
import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature

/-! The marked cofactor spends one moment at the same original Gaussian.
Its moment budget may include a genuinely unbounded filed polynomial. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert
open Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open scoped Topology BigOperators Classical
variable {G : Gauge}

def MarkedJointEstimate (R : Run G) (m N : ℕ) (Z : SeriesA G) (r n K : ℕ) (ε η : ℝ) : Prop :=
  let V:=R.family.path.levels
  ∀ per : ℕ,
    let S:=V.clock.op m per
    let s:=V.clock.hatBeta m
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    let p:=finitePitch R N (m+1) r g
    ∀ {W μ budget : ℝ} {P : Teller G} {Q : Target G P} {o : Target.Order G W}
      {T : Tube G S} {Y : Rep G (R.family.side (m+1) per)},
      (H : Cash W s μ S.patch.L Q o budget T Y) → 0≤Pressure.temp s →
      WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L o≤1+Real.log (betaF G s S.patch.L) →
      ∀ (χ : Chi) (v : Finset (LocalLTE.Fan.Veil (R.family.side m per) (R.family.side (m+1) per)))
        (i : Greenbelt.Reserve S) (tag : S.Choices) (y : (Greenbelt.allot i).Slice G)
        (a : Fin (n+1)→PrismA G), (∀ j,a j∈Z) → ∀ x : Fin (n+1)→Site (R.family.side (m+1) per),
      let F:=Greenbelt.allot i
      let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
      let β:=Integral.temperature g
      let w:=fun j=>β*p*(g/Real.sqrt p)^((a j).grade-(a j).rise)
      let physical:=fun j (z : Air (R.family.side (m+1) per) G)=>(w j:ℂ)*
        sitePacket (a j).cells (x j) ((X.wrapY y).input ((X.wrapY y).liftA β z))
      let polynomial:=fun j (z : Air (R.family.side (m+1) per) G)=>(w j:ℂ)*
        siteTaylor (a j).cells (x j) (angularSample F z) ((a j).rise+K+1) g
      ∀ (J : Air (R.family.side (m+1) per) G→ℂ) {B : ℝ}, 0≤B → AEStronglyMeasurable J X.dice →
      (Integrable (fun z=>‖J z‖^(n+2)) X.dice ∧ (∫ z,‖J z‖^(n+2) ∂X.dice)≤B^(n+2)) →
      let E:=fun z=>J z*((∏ j,polynomial j z)-∏ j,physical j z)
      Integrable E X.dice ∧ (‖∫ z,E z ∂X.dice‖≤B*(ε*g^(((K+∑ j,(a j).grade:ℕ):ℝ)-η)))

private theorem scale_marked (n s : ℕ) {g ε η C : ℝ} (gp : 0<g)
    (price : C≤ε/(2:ℝ)^(n+2)*g^(-η)) :
    (2:ℝ)^(n+2)*g^s*C≤ε*g^((s:ℝ)-η) := by
  calc _ ≤ (2:ℝ)^(n+2)*g^s*(ε/2^(n+2)*g^(-η)):=mul_le_mul_of_nonneg_left price (by positivity)
    _ = ε*(g^s*g^(-η)):=by
      have positive : (2:ℝ)^(n+2)≠0:=by positivity
      field_simp
    _ = _:=by rw [←Real.rpow_natCast,←Real.rpow_add gp,sub_eq_add_neg]

theorem funded_marked (R : Run G) (simple : G.Simple) (v : ℕ→Gear G→ℝ)
    (rows : FundedMarkedCoverRows.prices v R.kit) (credit : Credit) (d r n K : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ,m+1<N →
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀ σ : ℝ,0<σ → σ⁻¹≤zz V (m+1) →
      ∀ Z : SeriesA G,Draw Z σ D → (∀ a∈Z,a.grade≤d) → MarkedJointEstimate R m N Z r n K ε η := by
  intro V
  obtain ⟨_,pitch⟩:=cofinal_temperature R simple v rows r
  have ep' : 0<ε/(2:ℝ)^(n+2):=by positivity
  filter_upwards [cofinal_joint_load R simple credit d K n (n+1) ep' hp,
    (tendsto_add_atTop_nat 1).eventually pitch,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)]
    with m tariff tuning small
  intro N later D σ width dated Z filed incoming per S s g p W μ budget P Q o T Y H temp paid χ fan i tag y a occupied x F X β w physical
    polynomial J B B0 jm marked E
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per (m+1) later.le
  have limit : g≤1:=(small N per later.le).le
  have selected:=tuning N later per
  have hi:=chamber_marked H temp χ fan i tag y Z n K (fun _=>σ) (fun _=>D)
    (fun _=>width) (fun _=>filed) a occupied x g p gp limit selected.2.2.1 selected.2.2.2.1 J B0 jm marked
  have price:=tariff N per (Nat.lt_of_succ_lt later) (fun _=>σ) (fun _=>width) (fun _=>dated) o paid
    a (fun j=>incoming _ (occupied j)) filed.1
  exact ⟨hi.1,hi.2.trans (mul_le_mul_of_nonneg_left (scale_marked n _ gp price) B0)⟩

end YM.Integration.OriginalMarkedRunAction
