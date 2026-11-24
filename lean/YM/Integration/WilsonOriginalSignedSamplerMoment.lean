import YM.Integration.WilsonOriginalSignedCutSquare

/-! On each retained original chamber, compare a complete signed finite
polynomial to the full-path normalized Wick sampler on the same free links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedSamplerMoment
open Function Filter Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Matrix
open Pressure Pressure.Tube Pressure.Stores FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open Next.SectorChange Next.SectorChange.Rows Next.Fluctuations Next.Fluctuations.Sector
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws AnalyticBridge.GaussianFieldAlignment
open ConnectedActivityE6 ConnectedActivityE6.Window ConnectedActivityE6.Control ConnectedActivityE6.Census
open PhysicalNext.Repeat PhysicalNext.Repeat.Malachite Comparison.RG02.Cumulants
open Next.Rank WilsonCoherentMayerHearing
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Next.SectorChange ConnectedActivityE6.Control ConnectedActivityE6.Census
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine PhysicalNext.Repeat.Malachite
open Comparison.RG02.Cumulants Next.Rank WilsonCoherentMayerHearing
open scoped Topology Classical BigOperators

variable {G : Gauge} {c f L : Side} {S : StepData c f} (T : Tube G S)
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ}
  {o : Target.Order G W} {R : Rep G f}

def cap := max 1 (headGap G S.patch S.kernel T.high)⁻¹

theorem bounded (fund : P.Funds S T) (geo : Bid.Larger (G:=G) S)
    (F : Forest S.ratio) (tag : S.Choices) (r : Admit) (i j : Key F G) :
    |(primary S F tag T.high T.up r 0)⁻¹ i j| ≤ cap T := by
  obtain ⟨Λ,_,hW,_⟩ := fund.feeds
  have hW₀ : T.up.Bounds T.high P.top.width P.top.paths Λ := by rw [fund.high]; exact hW
  have h := (knows (W:=T.up) F tag P.top.width_pos P.top.paths_pos.le (path_sheet T hW₀) geo T.high 0 r).gap
  have a := headGap_pos G S.patch S.kernel T.high
  exact (h.point a (Matrix.mul_nonsing_inv _ (h.unit_det a)) i j).trans (le_max_right _ _)

def ideal (F : Forest S.ratio) (tag : S.Choices) (x : ℝ) :=
  ((primary S F tag T.high T.up all 0)⁻¹).submatrix
    (Native.lineEquiv (G:=G) F x).symm (Native.lineEquiv (G:=G) F x).symm

theorem symmetry (F : Forest S.ratio) (tag : S.Choices) (x : ℝ) : (ideal T F tag x).IsSymm := by
  have h : (block S tag T.high T.up all 0).IsSymm := by
    unfold block
    apply Matrix.IsSymm.smul
    unfold Matrix.IsSymm channel squareQ
    simp [Matrix.transpose_sum]
  exact ((h.submatrix _).inv).submatrix _

def fee (L : Side) (P : Teller G) {W : ℝ} (o : Target.Order G W) (d : ℕ) (x : ℝ) :=
  WilsonOriginalSignedShutterMoment.fee G L o d x +
    (WilsonOriginalSignedPathCut.price G S.patch S.kernel T.high P.top.paths P.top.width *
      Real.exp (-(P.top.width/4)*till x)) * Common.priced (cap T) d

theorem rate (L : Side) (P : Teller G) {W : ℝ} (o : Target.Order G W) (d : ℕ) (b : ℝ) :
    Rate G L b (fee T L P o d) :=
  (WilsonOriginalSignedShutterMoment.rate G L o d b).add
    ((WilsonOriginalSignedPathCut.payable T L P b).mul_right (Common.priced (cap T) d))

theorem original (H : Cash W s μ L Q o C T R) (temp : 0 ≤ Pressure.temp s) (χ : Chi)
    (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices) :
    let F := Greenbelt.allot i
    let X := chamber T s o.K χ 1 v i tag
    ∀ (p : Normal.poly (Eye X)) (d : ℕ), p.totalDegree ≤ d →
      ‖(∫ z : Air f G, Cloud.paint (fun u => z (tube X u)) p ∂X.dice) -
        Cloud.wick (ideal T F tag s) (symmetry T F tag s) 0 p‖ ≤ Rise.coin p * fee T L P o d s := by
  intro F X p d hd
  have fund : P.Funds S T := H.laws.data.funds.funds
  have geo := H.laws.data.room.larger
  have stored := WilsonOriginalSignedShutterSquare.original H temp χ v i tag
  have cut : WilsonHullGaussianMoment.active X =
      ((primary S F tag T.high T.up (shorter (till s)) 0)⁻¹).submatrix
        (Native.lineEquiv (G:=G) F s).symm (Native.lineEquiv (G:=G) F s).symm :=
    stored.2.1.trans (WilsonOriginalSignedCutSquare.chart T fund F tag s)
  let δ := WilsonOriginalSignedPathCut.price G S.patch S.kernel T.high P.top.paths P.top.width *
    Real.exp (-(P.top.width/4)*till s)
  have hδ : 0≤δ := by unfold δ WilsonOriginalSignedPathCut.price; positivity
  have change := WilsonHullGaussianMoment.polynomial (WilsonHullGaussianMoment.active_symm X)
    (symmetry T F tag s) p d (show 1≤cap T from le_max_left _ _) hδ hd
    (fun a _ b _ => by rw [cut]; exact bounded T fund geo F tag _ _ _)
    (fun a _ b _ => bounded T fund geo F tag all _ _)
    (fun a _ b _ => by rw [cut]; exact WilsonOriginalSignedPathCut.entry T fund geo F tag (till s) _ _)
  have tri := dist_triangle (∫ z : Air f G, Cloud.paint (fun u => z (tube X u)) p ∂X.dice)
    (Cloud.wick (WilsonHullGaussianMoment.active X) (WilsonHullGaussianMoment.active_symm X) 0 p)
    (Cloud.wick (ideal T F tag s) (symmetry T F tag s) 0 p)
  simp only [dist_eq_norm] at tri
  exact tri.trans ((add_le_add (stored.2.2 p d hd) change).trans_eq (mul_add ..).symm)

end YM.Integration.WilsonOriginalSignedSamplerMoment
