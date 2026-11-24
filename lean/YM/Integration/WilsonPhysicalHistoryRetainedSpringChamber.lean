import YM.Integration.WilsonPhysicalHistoryRetainedSpringRoot
import YM.Integration.WilsonPhysicalHistoryRetainedSpringOrder

/-! On the actually paid chamber, the all-visit moment buys the complete
previous vertex, with its kinetic and engineering factors still attached. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert
open scoped Topology BigOperators Classical
open Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}

theorem inverse_temperature_step {g : ℝ} (hg : 0<g) : gStep (Integral.temperature g)=g := by
  rw [gStep,Integral.temperature,Real.sqrt_inv,Real.sqrt_sq hg.le,inv_inv]

theorem registered_sample {F : Forest S.ratio} {X : Coat T F} {η r cap expense : ℝ}
    (A : Rotator P L η r cap expense X) {k : ℕ} (V : ℕ→Atom G k) {σ D B : ℝ}
    (hs : 0<σ) (enrolled : SumBudget (fun j=>(V j).budget σ) D) (x : Site f) (q : ℕ)
    (g w : ℝ) (raw : Air f G→ Config G f) (same : raw=fun z=>represent (g • angularSample F z))
    (J : Air f G→ℂ) (Jm : AEStronglyMeasurable J X.dice) (bound : ∀ z,‖J z‖≤B) :
    let d:=fun z=>(sitePacket V x (raw z):ℂ)-siteTaylor V x (angularSample F z) q g
    Integrable (fun z=>J z*(w:ℂ)*d z) X.dice ∧
    ‖∫ z,J z*(w:ℂ)*d z ∂X.dice‖ ≤ (B*|w|)*(D*(2*speedPrice G L η r cap q*|g|/σ)^(q+1)) := by
  subst raw
  exact site_with_tester A V hs enrolled x q g (fun z=>J z*(w:ℂ))
    (Jm.mul aestronglyMeasurable_const) (fun z=>by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (bound z) (abs_nonneg _))

theorem chamber_vertex (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) {σ D : ℝ} (hs : 0<σ) (filed : Draw Z σ D)
    (a : PrismA G) (member : a∈Z) (x : Site f) (q : ℕ) (g p : ℝ) (hg : 0<g)
    (J : Air f G→ℂ) {B : ℝ} (bound : ∀ z,‖J z‖≤B) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let F:=Greenbelt.allot i
    let β:=Integral.temperature g
    let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
    let d:=fun z : Air f G=>(sitePacket a.cells x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)-
      siteTaylor a.cells x (angularSample F z) q g
    AEStronglyMeasurable J X.dice →
      Integrable (fun z=>J z*(w:ℂ)*d z) X.dice ∧
      ‖∫ z,J z*(w:ℂ)*d z ∂X.dice‖ ≤ (B*|w|)*
        (D*(2*speedPrice G L o.eta o.gap o.ample q*|g|/σ)^(q+1)) := by
  let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
  let F:=Greenbelt.allot i
  let β:=Integral.temperature g
  let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
  have manifest : X.manifest:=by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have βpos : 0<β:=by dsimp only [β,Integral.temperature]; positivity
  have sample (z : Air f G) : (X.wrapY y).input ((X.wrapY y).liftA β z)=
      represent (g • angularSample F z) := by
    simpa only [β,inverse_temperature_step hg,mul_inv_cancel₀ hg.ne',one_smul] using
      chamber_path H.laws.data.funds.funds s o.K χ i v tag βpos y z g
  intro _ _ _ _ _ Jm
  exact registered_sample A a.cells hs (filed.2 a member).toll x q g w
    (fun z=>(X.wrapY y).input ((X.wrapY y).liftA β z)) (funext sample) J Jm bound

end YM.Integration.OriginalMarkedRunAction
