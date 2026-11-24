import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceWriting
import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceAverage

/-! The measured normalized plaquette Taylor polynomial starts in degree two.
Its coefficient norm only sees the four original signed links and the fixed gauge. -/
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
open WilsonCoherentMayerRootPlaquette WilsonMeasuredPathTaylor WilsonWalkMatrixSecant
open scoped BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

theorem face_ray_tail (v : Directions G f) (x : Site f) (a : PlaqAxes) (K : ℕ) (g : ℝ) :
    let c:=fun j : ℕ=>(j.factorial:ℝ)⁻¹*normalizedTrace G (iteratedDeriv j (curve v x (square a.val.1 a.val.2)) 0)
    faceRay v x a (K+1) g= -(∑ j∈range K,g^(j+2)*c (j+2)) := by
  intro c
  have full (q : ℕ) : faceRay v x a q g=1-∑ j∈range (q+1),g^j*c j:=by
    simp only [faceRay,WilsonMeasuredPathTaylor.jet,map_sum,map_smul,smul_eq_mul,c]
    congr 1
    apply sum_congr rfl
    intro j _
    ring
  have flat:=face_ray_first v x a g
  rw [full] at flat
  rw [full,show K+1+1=2+K by omega,sum_range_add]
  simp only [Nat.add_comm 2] 
  linarith

def faceGerm (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (K : ℕ) (g : ℝ) : Normal.poly (Eye X):=
  -(∑ j∈range K,MvPolynomial.C ((g:ℂ)^(j+2))*faceWritten X s x a (j+2))

def faceGermPrice (G : Gauge) (K : ℕ) (g : ℝ) : ℝ:=
  ∑ j∈range K,|g|^(j+2)*faceRankPrice G (j+2)

theorem face_germ_read (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (K : ℕ) (g : ℝ) (z : Air f G) :
    Cloud.paint (fun u=>z (tube X u)) (faceGerm X s x a K g)=
      Complex.ofReal (faceRay (collect G (pulled (angularSample F z) s)) x a (K+1) g) := by
  rw [face_ray_tail]
  simp only [faceGerm,map_neg,map_sum,map_mul,face_written_read,Cloud.paint,MvPolynomial.aeval_C,
    Complex.ofReal_sum,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

theorem face_germ_price (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (K : ℕ) (g : ℝ) :
    Rise.coin (faceGerm X s x a K g)≤faceGermPrice G K g := by
  have neg (P : Normal.poly (Eye X)) : Rise.coin (-P)=Rise.coin P:=by simp [Rise.coin,Rise.cents]
  rw [faceGerm,neg]
  apply (Rise.collect 0 zero_le_one _ _).trans
  apply sum_le_sum
  intro j _
  apply (Rise.funds 0 zero_le_one _ _).trans
  rw [Rise.pay_C,norm_pow,Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (face_written_price ..) (pow_nonneg (abs_nonneg _) _)

theorem face_germ_degree (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes) (K : ℕ) (g : ℝ) :
    (faceGerm X s x a K g).totalDegree≤K+1 := by
  rw [faceGerm,MvPolynomial.totalDegree_neg]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  have low:=mem_range.mp hj
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  exact (face_written_degree ..).trans (by omega)

def facePortfolio (X : Coat T F) (x : Site f) (K : ℕ) (g : ℝ) : Normal.poly (Eye X):=
  MvPolynomial.C (((Fintype.card Signed:ℝ)⁻¹:ℝ):ℂ)*∑ u : Signed×PlaqAxes,faceGerm X u.1 x u.2 K g

theorem face_portfolio (X : Coat T F) (x : Site f) (K : ℕ) (g : ℝ) :
    (facePortfolio X x K g).totalDegree≤K+1 ∧ Rise.coin (facePortfolio X x K g)≤
      (Fintype.card PlaqAxes:ℝ)*faceGermPrice G K g ∧
    ∀ z : Air f G,Cloud.paint (fun u=>z (tube X u)) (facePortfolio X x K g)=
      Complex.ofReal (faceTaylorAt x (angularSample F z) (K+1) g) := by
  have size : 0<(Fintype.card Signed:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨?_,?_,?_⟩
  · unfold facePortfolio
    apply (MvPolynomial.totalDegree_mul ..).trans
    rw [MvPolynomial.totalDegree_C,zero_add]
    apply MvPolynomial.totalDegree_finsetSum_le
    exact fun _ _=>face_germ_degree ..
  · unfold facePortfolio
    apply (Rise.funds 0 zero_le_one _ _).trans
    rw [Rise.pay_C,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr size.le)]
    apply (mul_le_mul_of_nonneg_left ((Rise.collect 0 zero_le_one _ _).trans
      (sum_le_sum fun _ _=>face_germ_price ..)) (inv_nonneg.mpr size.le)).trans_eq
    simp only [sum_const,card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
    field_simp
  · intro z
    simp only [facePortfolio,faceTaylorAt,Patch.average,Fintype.sum_prod_type,map_sum,map_mul,
      face_germ_read,Cloud.paint,MvPolynomial.aeval_C,Complex.ofReal_sum,Complex.ofReal_mul]
    rfl

end YM.Integration.OriginalMarkedRunAction
