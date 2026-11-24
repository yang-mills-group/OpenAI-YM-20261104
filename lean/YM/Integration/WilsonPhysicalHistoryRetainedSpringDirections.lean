import YM.Integration.WilsonPhysicalHistoryRetainedSpringGaussian

/-! Read the authentic Gaussian bond after rotating the original Wilson
word. Reversal contributes a sign before taking its speed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MeasureTheory WilsonMeasuredPathTaylor
open scoped BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {P : Teller G} {η r Q Y : ℝ} {X : Coat T F}

theorem noise_continuous (F : Forest S.ratio) (e : Edge (Site f)) :
    Continuous (fun z : Air f G=>WilsonCoherentMayerNoise.row F z e) := by
  by_cases he : e∈F.trunks
  · simpa only [WilsonCoherentMayerNoise.row,if_pos he] using
      (continuous_const : Continuous (fun _ : Air f G=>(0:G.Color)))
  · simp only [WilsonCoherentMayerNoise.row,if_neg he]
    change Continuous (fun z : Air f G=>colorReader G (fun b=>z (e,b)))
    exact (colorReader G).continuous.comp (continuous_pi fun b=>(EuclideanSpace.proj (𝕜:=ℝ) (e,b)).continuous)

theorem rotated_continuous (F : Forest S.ratio) (s : Signed) :
    Continuous (fun z : Air f G=>collect G (pulled (angularSample F z) s)) := by
  apply continuous_pi
  intro e
  have back (i : Axis) : axisEquiv.symm (coord i)=i:=axisEquiv.symm_apply_apply i
  simp only [collect,pulled,angularSample,back]
  split
  · exact (noise_continuous F _).neg
  · exact noise_continuous F _

theorem rotated_speed (F : Forest S.ratio) (s : Signed) (e : Edge (Site f)) (z : Air f G) :
    speed (collect G (pulled (angularSample F z) s)) e=
      speed (WilsonCoherentMayerNoise.row F z) (((posDir e.2).rotate s).used (affine s 0 e.1)) := by
  have back (i : Axis) : axisEquiv.symm (coord i)=i:=axisEquiv.symm_apply_apply i
  simp only [speed,collect,pulled,angularSample,back]
  split <;> simp only [map_neg,norm_neg]

theorem rotated_receipt (h : Rotator P L η r Q Y X) (s : Signed) (q : ℕ) (e : Edge (Site f)) :
    let v:=fun z : Air f G=>collect G (pulled (angularSample F z) s)
    AEStronglyMeasurable (fun z=>speed (v z) e) X.dice ∧
      Integrable (fun z=>speed (v z) e^(q+1)) X.dice ∧
      (∫ z,speed (v z) e^(q+1) ∂X.dice)≤(speedPrice G L η r Q q)^(q+1) := by
  dsimp only
  simp_rw [rotated_speed]
  exact field_speed h q _

end YM.Integration.OriginalMarkedRunAction
