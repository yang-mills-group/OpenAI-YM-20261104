import YM.Integration.WilsonHullGaussianMoment
import YM.Integration.WilsonCoherentMayerGaussian

/-! Replacing the physical window covariance on the retained, chain-free
Mayer support. The test is the entire signed polynomial on one actual rotor. -/
set_option autoImplicit false

noncomputable section
namespace YM.Integration.WilsonOriginalSignedShutterMoment
open Filter Function Finset MeasureTheory ProbabilityTheory Matrix Lattice RG Pressure Pressure.Stores
open Pressure.Tube Precision Exterior Tree Wilson Push Next.Fluctuations SectorMeasure
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Window
open ConnectedActivityE6.Control ConnectedActivityE6.Census ConnectedActivityE6.Blaze
open PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato RGLocalTaylor
open Next.SectorChange ConnectedActivityE6.Blaze.March Coat Matter Pond
open Comparison.RG02.Cumulants Next.Rank WilsonCoherentMayerHearing
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
  {R : Rep G f} {F : Forest S.ratio}

private theorem raw (A : Matrix (Tubular f G) (Tubular f G) ℝ) (h : A.PosSemidef)
    (p : Normal.poly (Tubular f G)) :
    (∫ z : Air f G, Cloud.paint (fun i => z i) p ∂Poll.sweep A) =
      Cloud.wick A (Matrix.isHermitian_iff_isSymm.mp h.isHermitian) 0 p := by
  let e := (MeasurableEquiv.toLp 2 (Gaussian.Vec (Tubular f G))).symm
  have he : MeasurePreserving e (Poll.sweep A) (Gaussian.cloud A) := ⟨e.measurable,rfl⟩
  have H := Cloud.paid A (Matrix.isHermitian_iff_isSymm.mp h.isHermitian) h 0 p
  simp only [Cloud.shift_zero,zero_add] at H
  rw [←H.2,←he.map_eq,integral_map he.measurable.aemeasurable]
  · rfl
  · simpa only [he.map_eq] using H.1.aestronglyMeasurable

def fee (G : Gauge) (L : Side) {W : ℝ} (o : Target.Order G W) (d : ℕ) (s : ℝ) :=
  let m := tubularPrice G L
  distPay o.eta o.gap o.ample m (radiusB s) * Common.priced (1 + payE o.eta o.gap o.ample m) d

theorem rate (G : Gauge) (L : Side) {W : ℝ} (o : Target.Order G W) (d : ℕ) (v : ℝ) :
    Rate G L v (fee G L o d) :=
  ((o.f.physical G L v (tubularPrice G L)).mul_left (payE o.eta o.gap o.ample (tubularPrice G L))).mul_right _

theorem covariance (Y : Coat T F) (H : Target.GrantBodies W s μ L Q o C T)
    (hx : Y.x = s) (hw : Y.width = o.K) (hy : Y.manifest)
    (p : Normal.poly (Tubular f G)) (d : ℕ) (hd : p.totalDegree ≤ d) :
    ‖(∫ z : Air f G,Cloud.paint (fun i => z i) p ∂Y.dice) -
      (∫ z : Air f G,Cloud.paint (fun i => z i) p ∂Poll.sweep Y.plate⁻¹)‖ ≤
      Rise.coin p * fee G L o d s := by
  obtain ⟨A,-,-,-⟩ := H.localP F Y hx hw hy
  have h₁ := A.fullC.posSemidef
  have h₂ := (Control.definite A.scale.symmetry A.scale.ground A.scale.down).inv.posSemidef
  unfold Coat.dice
  rw [raw Y.relating h₁ p, raw Y.plate⁻¹ h₂ p]
  dsimp only [fee]
  rw [←hx]
  have hB : 1 ≤ 1 + payE o.eta o.gap o.ample (tubularPrice G L) := by linarith [A.scale.disc]
  refine WilsonHullGaussianMoment.polynomial _ _ p d hB
    (mul_nonneg A.scale.disc (A.scale.heap _)) hd ?_ ?_ ?_
  · intro i hi j hj
    exact (only_price (A.scale.mate Y.shutter).1 A.scale.weather.1.le i j).trans (by linarith)
  · intro i hi j hj
    exact (only_price A.scale.flatup.1 A.scale.weather.1.le i j).trans (by linarith)
  · intro i hi j hj
    exact only_price (A.scale.drift Y.shutter).1 A.scale.weather.1.le i j

theorem original (H : Cash W s μ L Q o C T R) (temp : 0 ≤ Pressure.temp s) (χ : Chi)
    (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (p : Normal.poly (Tubular f G)) (d : ℕ) (hd : p.totalDegree ≤ d) :
    let X := chamber T s o.K χ 1 v i tag
    ‖(∫ z : Air f G,Cloud.paint (fun u => z u) p ∂X.dice) -
      (∫ z : Air f G,Cloud.paint (fun u => z u) p ∂Poll.sweep X.plate⁻¹)‖ ≤
      Rise.coin p * fee G L o d s := by
  let F := Greenbelt.allot i
  let X := chamber T s o.K χ 1 v i tag
  have hm : X.manifest := by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags = RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  exact covariance X H.laws.data rfl rfl hm p d hd

end YM.Integration.WilsonOriginalSignedShutterMoment
