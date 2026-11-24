import YM.Integration.WilsonPhysicalHistoryRetainedSpringKinetic

/-! The true incoming scalar multiplies the entire Wilson quadratic at date
m+1. Its explicit two powers of the regulator give degree four at a site. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function MeasureTheory Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup Pert.Asymptotics
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}

def directUnit (G : Gauge) (h : ℕ) : ℝ:=(Fintype.card PlaqAxes:ℝ)*tracePrice G*‖(1:G.Mat)‖*(2:ℝ)^h
def pairUnit (G : Gauge) : ℝ:=(Fintype.card PlaqAxes:ℝ)*(Fintype.card G.ColorIndex / 2:ℝ)

theorem metric_direct (K : PathData G) {B : Clip} {σ D Λ : ℝ} (paid : K.Bounds B σ D Λ) : B.direct≤1:=by
  let a : PlaqAxes:=Classical.choice inferInstance
  have h:=paid.metric a a
  simp at h
  have nonneg : 0≤∑ i,K.symbol0 i a*K.symbol0 i a:=sum_nonneg fun _ _=>mul_self_nonneg _
  linarith

theorem kinetic_price (K : PathData G) {B : Clip} {σ D Λ M : ℝ} (paid : K.Bounds B σ D Λ)
    (h : ℕ) (pos : 0≤M) :
    kineticPrice G B D σ h M≤(directUnit G h+pairUnit G*(D^2*σ⁻¹^h))*(2*M)^h := by
  unfold kineticPrice
  have bounded : |B.direct|≤1:=(abs_of_pos B.quadratic_pos).trans_le (metric_direct K paid)
  apply (add_le_add (mul_le_mul_of_nonneg_right bounded
    (mul_nonneg (Nat.cast_nonneg _) (face_cost_nonneg G h pos))) (le_refl _)).trans_eq
  have eq : (4:ℝ)^h=2^h*2^h:=by rw [←mul_pow]; norm_num
  simp only [faceCost,Stationary.gramCost,directUnit,pairUnit,div_eq_mul_inv,mul_pow,eq]
  ring

theorem funded_kinetic (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (r K l : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N per : ℕ,m+1<N →
      let j:=m+1
      let S:=V.clock.op m per
      let s:=V.clock.hatBeta m
      let g:=regulatorRun R.family N per j
      let w:=g^2*pitchTail R N j r g
      let B:=(V.params j).clip
      let path:=(R.family.path.rep N per j).path
      ∀ {W μ budget : ℝ} {P : Teller G} {Q : Target G P} {o : Target.Order G W}
        {T : Tube G S} {Y : Rep G (R.family.side j per)},
        (H : Cash W s μ S.patch.L Q o budget T Y) → 0≤Pressure.temp s →
        WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L o≤1+Real.log (betaF G s S.patch.L) →
        ∀ (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil (R.family.side m per) (R.family.side j per)))
          (i : Greenbelt.Reserve S) (tag : S.Choices) (y : (Greenbelt.allot i).Slice G) (x : Site (R.family.side j per)),
        let F:=Greenbelt.allot i
        let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 fan i tag
        let e:=fun z : Air (R.family.side j per) G=>(w:ℂ)*((secondAt B path x ((X.wrapY y).input
          ((X.wrapY y).liftA (Integral.temperature g) z)):ℂ)-kineticTaylor B path x (angularSample F z) (K+1) g)
        Integrable e X.dice ∧ Integrable (fun z=>‖e z‖^(l+1)) X.dice ∧ (∫ z,‖e z‖^(l+1) ∂X.dice)≤
          (ε*g^(((K+4:ℕ):ℝ)-η))^(l+1) := by
  intro V
  let h:=K+2
  let u:=h*(l+1)-1
  have a0 : 0≤directUnit G h:=by unfold directUnit tracePrice; positivity
  have b0 : 0≤pairUnit G:=by unfold pairUnit; positivity
  filter_upwards [cofinal_kinetic_expense R simple slow v rows r u h a0 b0 ep hp] with m income
  intro N per later j S s g w B path W μ budget P Q o T Y H temp cost χ fan i tag y x F X e
  let D:=V.params j
  let M:=speedPrice G S.patch.L o.eta o.gap o.ample u
  have Mp : 0≤M:=(speed_price_pos ..).le
  have selected : R.family.path.Conv N per j:=R.makes.wilson.represents N per j later.le
  have actual : path.Bounds B D.width D.paths (V.clock.loopCap j):=by
    dsimp only [path,B,D,V]
    rw [←selected.clip]
    exact selected.good.paths
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per j later.le
  obtain ⟨measured,integrable,bill⟩:=chamber_kinetic H temp χ fan i tag y actual x (K+1) l g w gp
  have money : |pitchTail R N j r g| *kineticPrice G B D.paths D.width h M≤ε*g^(-η):=by
    apply le_trans _ (income N per later o cost)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (kinetic_price path actual h Mp) (abs_nonneg _)
  have raw : 0≤kineticPrice G B D.paths D.width h M:=by
    unfold kineticPrice Stationary.gramCost
    positivity [D.paths_pos,D.width_pos,face_cost_nonneg G h Mp]
  have checked : |w| *kineticPrice G B D.paths D.width h M*|g|^h≤ε*g^(((K+4:ℕ):ℝ)-η):=by
    calc
      _ = (|pitchTail R N j r g| *kineticPrice G B D.paths D.width h M)*g^(h+2):=by
        dsimp only [w]
        rw [abs_mul,abs_of_nonneg (pow_nonneg gp.le _),abs_of_pos gp,pow_add]
        ring
      _ ≤ (ε*g^(-η))*g^(h+2):=mul_le_mul_of_nonneg_right money (pow_nonneg gp.le _)
      _ = _:=by
        rw [mul_assoc,←Real.rpow_natCast g,←Real.rpow_add gp]
        congr 2
        dsimp only [h]
        push_cast
        ring
  exact ⟨measured,integrable,bill.trans (pow_le_pow_left₀ (by positivity) checked _)⟩

end YM.Integration.OriginalMarkedRunAction
