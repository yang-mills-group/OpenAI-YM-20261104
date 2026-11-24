import YM.Integration.WilsonPhysicalHistoryRetainedSpringChamber
import YM.Integration.WilsonPhysicalHistoryRetainedSpringInitial
import YM.Integration.WilsonPhysicalHistoryRetainedSpringPowers

/-! The positive coupling degree of every enrolled prior vertex on its measured
Gaussian, without a maximum over the random velocities or all torus sites. -/
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

theorem chamber_power (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) {σ D : ℝ} (hs : 0<σ) (filed : Draw Z σ D)
    (a : PrismA G) (member : a∈Z) (x : Site f) (r : ℕ) (g p : ℝ) (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2)
    (J : Air f G→ℂ) {B : ℝ} (bound : ∀ z,‖J z‖≤B) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let F:=Greenbelt.allot i
    let β:=Integral.temperature g
    let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
    let d:=fun z : Air f G=>(sitePacket a.cells x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)-
      siteTaylor a.cells x (angularSample F z) (r+1) g
    let M:=speedPrice G L o.eta o.gap o.ample (r+1)
    AEStronglyMeasurable J X.dice →
      Integrable (fun z=>J z*(w:ℂ)*d z) X.dice ∧
      ‖∫ z,J z*(w:ℂ)*d z ∂X.dice‖≤B*(2^(a.grade-a.rise+1)*D*(2*M/σ)^(r+2)*g^(a.grade-a.rise+r)) := by
  intro X F β w d M Jm
  obtain ⟨integ,bill⟩:=chamber_vertex H temp χ v i tag y Z hs filed a member x (r+1) g p hg J bound Jm
  refine ⟨integ,bill.trans ?_⟩
  have positive : 0≤B:=(norm_nonneg (J 0)).trans (bound 0)
  have hm : 0≤M:= (speed_price_pos G L o.eta o.gap o.ample (r+1)).le
  change B*|w| *(D*(2*M*|g| /σ)^(r+2))≤_
  rw [mul_assoc,abs_of_pos hg,show 2*M*g/σ=(2*M/σ)*g by ring]
  exact mul_le_mul_of_nonneg_left (weighted_power hg lo hi (by positivity) filed.1 (a.grade-a.rise) r) positive

theorem chamber_grade (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) {σ D : ℝ} (hs : 0<σ) (filed : Draw Z σ D)
    (a : PrismA G) (member : a∈Z) (x : Site f) (g p : ℝ) (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2)
    (J : Air f G→ℂ) {B : ℝ} (bound : ∀ z,‖J z‖≤B) :
    let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let β:=Integral.temperature g
    let w:=β*p*(g/Real.sqrt p)^(a.grade-a.rise)
    let M:=speedPrice G L o.eta o.gap o.ample (a.rise+1)
    let field:=fun z : Air f G=>(sitePacket a.cells x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)
    AEStronglyMeasurable J X.dice →
      Integrable (fun z=>J z*(w:ℂ)*field z) X.dice ∧
      ‖∫ z,J z*(w:ℂ)*field z ∂X.dice‖≤B*(2^(a.grade-a.rise+1)*D*(2*M/σ)^(a.rise+2)*g^a.grade) := by
  intro X β w M field Jm
  have zero (z : Dir G f) : siteTaylor a.cells x z (a.rise+1) g=0 :=
    flat_site_polynomial a.cells x _ (Nat.lt_succ_self _) g
  have quoted:=chamber_power H temp χ v i tag y Z hs filed a member x a.rise g p hg lo hi J bound Jm
  simpa only [zero,sub_zero,Nat.sub_add_cancel a.rankA] using quoted

end YM.Integration.OriginalMarkedRunAction
