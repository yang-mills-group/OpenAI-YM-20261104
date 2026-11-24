import YM.Integration.WilsonPhysicalHistoryRetainedSpringPolynomialRun
import YM.Integration.WilsonRetainedOccupiedWick

/-! An actual occupied incoming Wilson spring, with its kinetic counterterm and
the full previously filed action, in the common conditional Wick comparison. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open IterationFour IterationFour.Vacuum Comparison.RG02
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open scoped BigOperators Classical
variable {G : Gauge}

private def incomingWick {c f : Side} {S : StepData c f} (T : Tube G S) (F : Forest S.ratio)
    (tag : S.Choices) (s : ℝ) (X : Coat T F) (J : Normal.poly (Eye X)) : ℂ :=
  Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
    (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 J

variable (R : Run G) {m N : ℕ} (per : ℕ)
local notation "S₀" => R.family.path.levels.clock.op m per
local notation "s₀" => R.family.path.levels.clock.hatBeta m
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per (m+1)
local notation "f₀" => R.family.side (m+1) per

theorem registered_spring_wick (later : m+1<N) (Z : SeriesA G) {τ C : ℝ}
    (ht : 0<τ) (filed : Draw Z τ C) (d : ℕ) (grade : ∀a∈Z,a.grade≤d)
    (r n K : ℕ) {ε η : ℝ} (purchase : SpringJointEstimate R m N Z r n K ε η)
    {W μ budget : ℝ} {P : Teller G} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}
    {T : Tube G S₀} {Y : Rep G f₀} (H : Cash W s₀ μ (S₀).patch.L Q o budget T Y)
    (temp : 0≤Pressure.temp s₀) (jump : WilsonCoherentMayerCovarianceCalendar.deviation G (S₀).patch.L o≤
      1+Real.log (betaF G s₀ (S₀).patch.L))
    (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil (R.family.side m per) f₀))
    (i : Greenbelt.Reserve S₀) (tag : (S₀).Choices) (y : (Greenbelt.allot i).Slice G)
    (x : Fin (n+1)→Site f₀) :
    let F:=Greenbelt.allot i
    let X:=chamber T s₀ o.K χ 1 fan i tag
    let a:=fun l z=>(springAt R N per (m+1) r Z g₀ (x l)
      ((X.wrapY y).input ((X.wrapY y).liftA (Integral.temperature g₀) z)):ℂ)
    let spr:=fun l=>registeredSpring R N per (m+1) r Z X (x l) K g₀
    ∀ B : Normal.poly (Eye X),
    let J:=B*∏ l,spr l
    let observed:=fun z : Air f₀ G=>Cloud.paint (fun u=>z (tube X u)) B*∏ l,a l z
    let mass:=Rise.coin B*∏ l,Rise.coin (spr l)
    let order:=B.totalDegree+(n+1)*(max (d+1) 3+K)
    let fee:=WilsonOriginalSignedSamplerMoment.fee T (S₀).patch.L P o order s₀
    let cap:=Rise.coin B*(1+Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G (S₀).patch.L))
      (2*((n+2)*B.totalDegree))))
    Integrable observed X.dice ∧
    ‖(∫ z,observed z ∂X.dice)-incomingWick T F tag s₀ X J‖≤
      mass*|fee|+cap*(ε*g₀^(((K+3*(n+1):ℕ):ℝ)-η)) := by
  intro F X a spr B J observed mass order fee cap
  let reading:=fun (p : Normal.poly (Eye X)) (z : Air (f₀) G)=>Cloud.paint (fun u=>z (tube X u)) p
  have manifest : X.manifest := by
    change (roster (LocalLTE.Fan.arm (S:=S₀) fan)).flags=RG.flags (Pressure.temp s₀) (1:Config G _)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s₀ χ o.K (1:Config G _) F).bowed temp
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  obtain ⟨bc,measurable,moment⟩:=mark_power X A B (n+1)
  have paid:=purchase per H temp jump χ fan i tag y x (reading B) bc measurable moment
  have typed : Integrable (reading J) X.dice := (WilsonCoherentMayerFuelSquare.sampled X A.fullC J).1
  have received (l : Fin (n+1)):=registered_spring R N per (m+1) r later.le Z ht filed d grade X (x l) K g₀
  let t:=fun l z=>springTaylorAt R N per (m+1) r Z (x l) (angularSample F z) K g₀
  have raw (z : Air (f₀) G) : reading J z=reading B z*∏ l,t l z := by
    dsimp only [reading,J]
    rw [map_mul,map_prod]
    congr 1
    exact Finset.prod_congr rfl fun l _=>(received l).2.2 z
  let diff:=fun z=>reading B z*((∏ l,t l z)-∏ l,a l z)
  have same : observed=fun z=>reading J z-diff z := by
    funext z
    rw [raw]
    dsimp only [observed,reading,diff]
    ring
  have bound : J.totalDegree≤order := by
    apply (MvPolynomial.totalDegree_mul ..).trans
    apply Nat.add_le_add_left
    apply (MvPolynomial.totalDegree_finsetProd ..).trans
    calc
      (∑ l : Fin (n+1),(spr l).totalDegree) ≤ ∑ _ : Fin (n+1),(max (d+1) 3+K) :=
        Finset.sum_le_sum fun l _=>(received l).1
      _ = _ := by simp
  have coin : Rise.coin J ≤ mass := by
    apply (Rise.funds 0 zero_le_one _ _).trans
    exact mul_le_mul_of_nonneg_left (Rise.purchased 0 zero_le_one _ _) (Rise.sign 0 _ zero_le_one)
  let expected:=Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s₀)
    (WilsonOriginalSignedSamplerMoment.symmetry T F tag s₀) 0 J
  have wick : ‖(∫ z,reading J z ∂X.dice)-expected‖ ≤ mass*|fee| :=
    (WilsonOriginalSignedSamplerMoment.original T H temp χ fan i tag J order bound).trans
      ((mul_le_mul_of_nonneg_left (le_abs_self fee) (Rise.sign 0 _ zero_le_one)).trans
        (mul_le_mul_of_nonneg_right coin (abs_nonneg fee)))
  have replacement : Integrable diff X.dice ∧ ‖∫z,diff z ∂X.dice‖≤cap*(ε*g₀^(((K+3*(n+1):ℕ):ℝ)-η)):=paid
  rw [same]
  refine ⟨typed.sub replacement.1,?_⟩
  rw [integral_sub typed replacement.1]
  change ‖((∫z,reading J z ∂X.dice)-(∫z,diff z ∂X.dice))-expected‖≤_
  rw [sub_right_comm]
  exact (norm_sub_le ..).trans (add_le_add wick replacement.2)

end YM.Integration.OriginalMarkedRunAction
