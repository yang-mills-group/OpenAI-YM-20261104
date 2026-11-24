import YM.Integration.WilsonCoherentMayerFuelGate
import YM.Integration.WilsonOriginalSignedShutterMoment

/-! Dimension-independent second moment for the joint signed retained word on
the true cropped Gaussian. Its coefficient cost is counted before all periods. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerFuelSquare
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series



section Polynomial
variable {I:Type}
def reflected (p:Normal.poly I):Normal.poly I:=p.map (starRingEnd ℂ)

theorem reflection (p:Normal.poly I) (z:I→ℝ):
    Cloud.paint z (reflected p)=star (Cloud.paint z p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [reflected,Cloud.paint]
  | add p q hp hq =>
    change Cloud.paint z (MvPolynomial.map (starRingEnd ℂ) (p+q))=_
    rw [map_add,map_add];change Cloud.paint z (reflected p)+Cloud.paint z (reflected q)=_
    rw [hp,hq,map_add,star_add]
  | mul_X p i hp =>
    change Cloud.paint z (MvPolynomial.map (starRingEnd ℂ) (p*MvPolynomial.X i))=_
    rw [map_mul,map_mul];change Cloud.paint z (reflected p)*_=_
    rw [hp,map_mul];simp [Cloud.paint,mul_comm]

theorem reflection_coin (p:Normal.poly I):Rise.coin (reflected p)=Rise.coin p := by
  rw [Rise.metal,Rise.metal];unfold reflected
  rw [MvPolynomial.support_map_of_injective p (starRingEnd ℂ).injective]
  apply Finset.sum_congr rfl;intro m _
  rw [MvPolynomial.coeff_map];exact norm_star _

theorem reflection_degree (p:Normal.poly I):(reflected p).totalDegree=p.totalDegree := by
  simp only [MvPolynomial.totalDegree,reflected,MvPolynomial.support_map_of_injective p (starRingEnd ℂ).injective]

theorem reflection_read (p:Normal.poly I) (z:I→ℝ):
    (Cloud.paint z (p*reflected p)).re=‖Cloud.paint z p‖^2 := by
  rw [map_mul,reflection];simp [Complex.mul_conj,Complex.sq_norm]

end Polynomial
variable (X:Coat T F)
def submatrix := X.relating.submatrix (tube X) (tube X)

theorem sampled (h:X.relating.PosDef) (p:Normal.poly (Eye X)):
    Integrable (fun z:Air f G=>Cloud.paint (fun i=>z (tube X i)) p) X.dice ∧
    (∫z:Air f G,Cloud.paint (fun i=>z (tube X i)) p ∂X.dice)=
      Cloud.wick (submatrix X) (Matrix.isHermitian_iff_isSymm.mp (h.submatrix (tube X).injective).isHermitian) 0 p := by
  let e := (MeasurableEquiv.toLp 2 (Gaussian.Vec (Tubular f G))).symm
  have he:MeasurePreserving e X.dice (Gaussian.cloud X.relating):=⟨e.measurable,rfl⟩
  have U:MeasurePreserving (fun z:Air f G=>fun i=>z (tube X i)) X.dice (Gaussian.cloud (submatrix X)):=
    (AnalyticBridge.Sharp.Projection.cloud_projection h (tube X)).comp he
  have E:=Cloud.paid (submatrix X) (Matrix.isHermitian_iff_isSymm.mp (h.submatrix (tube X).injective).isHermitian)
    (h.posSemidef.submatrix (tube X)) 0 p
  simp only [zero_add,Cloud.shift_zero] at E
  refine ⟨(U.integrable_comp E.1.aestronglyMeasurable).2 E.1,?_⟩
  rw [←E.2,←U.map_eq,integral_map U.measurable.aemeasurable]
  simpa only [U.map_eq] using E.1.aestronglyMeasurable

theorem valuation {η r K Y:ℝ} (A:Rotator P L η r K Y X) (p:Normal.poly (Eye X)) (d:ℕ)
    (hd:p.totalDegree≤d) :
    ‖Cloud.wick (submatrix X) (Matrix.isHermitian_iff_isSymm.mp (A.fullC.submatrix (tube X).injective).isHermitian) 0 p‖ ≤
      Rise.coin p * Common.priced (1+payE η r K (tubularPrice G L)) d := by
  have hB:1≤1+payE η r K (tubularPrice G L):=by linarith [A.scale.disc]
  apply Tapes.bound_v _ _ hd hB
  · intro i _;simpa using (zero_le_one.trans hB)
  · intro i _ j _
    change ‖((X.relating (tube X i) (tube X j)):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (only_price (A.scale.mate X.shutter).1 A.scale.weather.1.le _ _).trans (by linarith)

theorem second {η r K Y:ℝ} (A:Rotator P L η r K Y X) (p:Normal.poly (Eye X)) (d:ℕ)
    (hd:p.totalDegree≤d):
    Integrable (fun z:Air f G=>‖Cloud.paint (fun i=>z (tube X i)) p‖^2) X.dice ∧
    (∫z:Air f G,‖Cloud.paint (fun i=>z (tube X i)) p‖^2 ∂X.dice) ≤
      (Rise.coin p)^2*Common.priced (1+payE η r K (tubularPrice G L)) (2*d) := by
  have E:=sampled X A.fullC (p*reflected p)
  have form (z:Air f G): (Cloud.paint (fun i=>z (tube X i)) (p*reflected p)).re=‖Cloud.paint (fun i=>z (tube X i)) p‖^2 := reflection_read p _
  have eq:(fun z:Air f G=>RCLike.re (Cloud.paint (fun i=>z (tube X i)) (p*reflected p)))=(fun z=>‖Cloud.paint (fun i=>z (tube X i)) p‖^2):=funext form
  rw [←eq];refine ⟨E.1.re,?_⟩
  rw [integral_re E.1,E.2]
  apply (Complex.re_le_norm _).trans
  have deg:(p*reflected p).totalDegree≤2*d:=
    (MvPolynomial.totalDegree_mul _ _).trans (by rw [reflection_degree];omega)
  have bounded:=valuation X A (p*reflected p) (2*d) deg
  apply bounded.trans
  have coin: Rise.coin (p*reflected p)≤(Rise.coin p)^2:=by
    rw [pow_two];have both:=Rise.funds 0 (zero_le_one (α:=ℝ)) p (reflected p)
    change Rise.coin (p*reflected p)≤Rise.coin p*Rise.coin (reflected p) at both
    simpa only [reflection_coin p] using both
  apply mul_le_mul_of_nonneg_right coin
  have hC:0≤1+payE η r K (tubularPrice G L):=by linarith [A.scale.disc]
  unfold Common.priced;positivity

end YM.Integration.WilsonCoherentMayerFuelSquare
