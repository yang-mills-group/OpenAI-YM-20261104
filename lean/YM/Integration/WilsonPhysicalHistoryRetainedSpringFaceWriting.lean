import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceChart

/-! Put the four actual plaquette contacts into the free coordinates of the
enrolled forest. Each original signed bond enters once per visit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoherentMayerHearing Dict06.Series
open PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open WilsonCoherentMayerRootPlaquette WilsonMeasuredPathTaylor
open scoped BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def faceWritten (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (j : ℕ) : Normal.poly (Eye X):=
  ∑ t : Fin j→FaceSlot G,MvPolynomial.C (Complex.ofReal (rye (faceTrace G) j t))*
    ∏ i,turn X s (faceBond x a (t i).1) (t i).2

theorem face_written_price (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (j : ℕ) :
    Rise.coin (faceWritten X s x a j)≤faceRankPrice G j := by
  unfold faceWritten faceRankPrice
  apply (Rise.collect 0 zero_le_one _ _).trans
  apply sum_le_sum
  intro t _
  apply (Rise.funds 0 zero_le_one _ _).trans
  rw [Rise.pay_C,Complex.norm_real]
  apply mul_le_of_le_one_right (abs_nonneg _)
  apply (Rise.purchased 0 zero_le_one _ _).trans
  exact prod_le_one (fun i _=>Rise.sign 0 _ zero_le_one) (fun i _=>(turn_pay X s _ _).1)

theorem face_written_degree (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (j : ℕ) :
    (faceWritten X s x a j).totalDegree≤j:=by
  unfold faceWritten
  apply MvPolynomial.totalDegree_finsetSum_le
  intro t _
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd ..).trans
  exact (sum_le_sum (fun i _=>(turn_pay X s (faceBond x a (t i).1) (t i).2).2)).trans_eq (by simp)

theorem face_written_read (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (j : ℕ)
    (z : Air f G) :
    let v:=collect G (pulled (angularSample F z) s)
    Cloud.paint (fun u=>z (tube X u)) (faceWritten X s x a j)=
      Complex.ofReal ((j.factorial:ℝ)⁻¹*normalizedTrace G (iteratedDeriv j (curve v x (square a.val.1 a.val.2)) 0)) := by
  intro v
  rw [←face_trace_coefficient,Blue.jet_apply]
  change _=Complex.ofReal (MvPolynomial.eval (faceFrame v x a) (∑ t : Fin j→FaceSlot G,
    (rye (faceTrace G) j t) • ∏ i,MvPolynomial.X (t i)))
  have reads (t : FaceSlot G) : Cloud.paint (fun u=>z (tube X u)) (turn X s (faceBond x a t.1) t.2)=
      Complex.ofReal (faceFrame v x a t):=by
    rw [turn_read]
    rfl
  simp only [faceWritten,map_sum,map_mul,map_prod,reads,Cloud.paint,MvPolynomial.aeval_C,
    MvPolynomial.smul_eq_C_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,Complex.ofReal_sum,
    Complex.ofReal_mul,Complex.ofReal_prod]
  rfl

end YM.Integration.OriginalMarkedRunAction
