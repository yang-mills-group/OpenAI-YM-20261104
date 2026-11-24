import YM.Integration.WilsonOriginalSignedShutterMoment

/-! The unmasked held-identity roster uses the same active quadratic
receipt as the original shrinking-path physical square at every branch. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonOriginalSignedShutterSquare
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Next.SectorChange ConnectedActivityE6.Control ConnectedActivityE6.Census
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine PhysicalNext.Repeat.Malachite
open Comparison.RG02.Cumulants Next.Rank WilsonCoherentMayerHearing
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
  {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
  {R : Rep G f}

theorem blank (χ : Chi) (s K : ℝ) (v : Finset (LocalLTE.Fan.Veil c f))
    (i : Greenbelt.Reserve S) (tag : S.Choices) :
    let X := chamber (G:=G) T s K χ 1 v i tag
    X.blank = X := by
  dsimp only [chamber]
  rw [LocalLTE.Fan.Field.rosterD]
  rfl

theorem original (H : Cash W s μ L Q o C T R) (temp : 0 ≤ Pressure.temp s) (χ : Chi)
    (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices) :
    let X := chamber T s o.K χ 1 v i tag
    X.plate.submatrix (tube X) (tube X) = profileGram T s 1 (bareStores S) (Greenbelt.allot i) tag 0 ∧
    WilsonHullGaussianMoment.active X = (profileGram T s 1 (bareStores S) (Greenbelt.allot i) tag 0)⁻¹ ∧
    ∀ (p : Normal.poly (Eye X)) (d : ℕ),p.totalDegree ≤ d →
      ‖(∫ z : Air f G, Cloud.paint (fun u => z (tube X u)) p ∂X.dice) -
        Cloud.wick (WilsonHullGaussianMoment.active X) (WilsonHullGaussianMoment.active_symm X) 0 p‖ ≤
        Rise.coin p * WilsonOriginalSignedShutterMoment.fee G L o d s := by
  let F := Greenbelt.allot i
  let X := chamber T s o.K χ 1 v i tag
  have e : X.blank = X := blank χ s o.K v i tag
  have fund : P.Funds S T := H.laws.data.funds.funds
  have gram := same_probe X fund
  rw [e] at gram
  refine ⟨gram, WilsonHullGaussianMoment.active_eq X fund, ?_⟩
  intro p d hd
  obtain ⟨A,-,-,-⟩ := H.laws.data.localP F X.blank rfl rfl (X.bowed temp)
  have h := WilsonHullGaussianMoment.active_paid X fund A.scale A.fullC p d hd
  have cov := WilsonHullGaussianMoment.zero_cov X
  change (gem X 0).relating = X.blank.relating at cov
  rw [e] at cov
  have measure : (gem X 0).dice = X.dice := congrArg Poll.sweep cov
  rw [measure] at h
  exact h

end YM.Integration.WilsonOriginalSignedShutterSquare

