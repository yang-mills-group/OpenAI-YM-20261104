import YM.Integration.WilsonPhysicalHistoryRetainedSpringFacePolynomial
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSitePolynomial
import YM.Integration.WilsonPhysicalHistoryRetainedSpringAllSite

/-! The complete finite polynomial for one occupied old site uses one
ring of free-link variables for the local plaquette, both paths, and all corrections. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open WilsonCoherentMayerHearing Dict06.Series PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def springPolynomial (X : Coat T F) (B : Clip) (path : PathData G) (Z : SeriesA G)
    (γ w b c : ℝ) (x : Site f) (K : ℕ) (g : ℝ) : Normal.poly (Eye X):=
  MvPolynomial.C (γ:ℂ)*(MvPolynomial.C (B.direct:ℂ)*facePortfolio X x K g+
    sitePortfolio X (gramEntries path) x K g)+
  MvPolynomial.C (w:ℂ)*(sitePortfolio X path.cubic x K g+sitePortfolio X path.quartic x K g)+
  ∑ i : Fin Z.length,MvPolynomial.C (((b*c^((Z.get i).grade-(Z.get i).rise)):ℝ):ℂ)*
    sitePortfolio X (Z.get i).cells x K g

def springPolynomialPrice (G : Gauge) (B : Clip) (Z : SeriesA G) (σ D τ C γ w b c : ℝ) (K : ℕ) (g : ℝ) : ℝ:=
  |γ| *(|B.direct| *((Fintype.card PlaqAxes:ℝ)*faceGermPrice G K g)+
    sitePortfolioPrice G σ (Stationary.gramCost G D) 2 K g)+
  |w| *(sitePortfolioPrice G σ D 3 K g+sitePortfolioPrice G σ D 4 K g)+
  ∑ i : Fin Z.length,|b*c^((Z.get i).grade-(Z.get i).rise)| *sitePortfolioPrice G τ C ((Z.get i).rise+2) K g

theorem spring_polynomial_read (X : Coat T F) (B : Clip) (path : PathData G) (Z : SeriesA G)
    {σ D Λ τ C : ℝ} (previous : path.Bounds B σ D Λ) (ht : 0<τ) (filed : Draw Z τ C)
    (γ w b c : ℝ) (x : Site f) (K : ℕ) (g : ℝ) (z : Air f G) :
    Cloud.paint (fun u=>z (tube X u)) (springPolynomial X B path Z γ w b c x K g)=
      (γ:ℂ)*kineticTaylor B path x (angularSample F z) (K+1) g+
      rosterTaylor path Z w b c true x (angularSample F z) K g := by
  have faces:=(face_portfolio X x K g).2.2 z
  have gram:=(site_portfolio X (gramEntries path) (by decide) previous.width (gram_finance path previous) x K g).2.2 z
  have c3:=(site_portfolio X path.cubic (by decide) previous.width previous.three x K g).2.2 z
  have c4:=(site_portfolio X path.quartic (by decide) previous.width previous.four x K g).2.2 z
  have packet (i : Fin Z.length) := (site_portfolio X (Z.get i).cells (by omega) ht
    (filed.2 (Z.get i) (List.get_mem ..)).toll x K g).2.2 z
  have constant (r : ℝ) : Cloud.paint (fun u=>z (tube X u)) (MvPolynomial.C (r:ℂ))=(r:ℂ):=by simp [Cloud.paint]
  have q2 : 2-1+K=K+1 := by omega
  have q3 : 3-1+K=K+2 := by omega
  have q4 : 4-1+K=K+3 := by omega
  have qr (i : Fin Z.length) : (Z.get i).rise+2-1+K=(Z.get i).rise+K+1 := by omega
  simp only [springPolynomial,map_add,map_mul,map_sum,constant,faces,gram,c3,c4,packet,q2,q3,q4,qr]
  simp only [kineticTaylor,rosterTaylor,interactionTaylor,if_true,Bool.false_eq_true,if_false,Complex.ofReal_mul]
  rw [add_assoc]


private theorem coin_scalar {E : Type*} [DecidableEq E] (v : ℝ) (P : Normal.poly E) {A : ℝ} (paid : Rise.coin P≤A) :
    Rise.coin (MvPolynomial.C (v:ℂ)*P)≤|v| *A := by
  apply (Rise.funds 0 zero_le_one _ _).trans
  rw [Rise.pay_C,Complex.norm_real]
  exact mul_le_mul_of_nonneg_left paid (abs_nonneg _)

theorem spring_polynomial_price (X : Coat T F) (B : Clip) (path : PathData G) (Z : SeriesA G)
    {σ D Λ τ C : ℝ} (previous : path.Bounds B σ D Λ) (ht : 0<τ) (filed : Draw Z τ C)
    (γ w b c : ℝ) (x : Site f) (K : ℕ) (g : ℝ) :
    Rise.coin (springPolynomial X B path Z γ w b c x K g)≤ springPolynomialPrice G B Z σ D τ C γ w b c K g := by
  have faces:=(face_portfolio X x K g).2.1
  have gram:=(site_portfolio X (gramEntries path) (by decide) previous.width (gram_finance path previous) x K g).2.1
  have c3:=(site_portfolio X path.cubic (by decide) previous.width previous.three x K g).2.1
  have c4:=(site_portfolio X path.quartic (by decide) previous.width previous.four x K g).2.1
  unfold springPolynomial springPolynomialPrice
  apply (Rise.taller 0 zero_le_one _ _).trans
  apply add_le_add
  · apply (Rise.taller 0 zero_le_one _ _).trans
    apply add_le_add
    · exact coin_scalar _ _ ((Rise.taller 0 zero_le_one _ _).trans (add_le_add (coin_scalar _ _ faces) gram))
    · exact coin_scalar _ _ ((Rise.taller 0 zero_le_one _ _).trans (add_le_add c3 c4))
  · apply (Rise.collect 0 zero_le_one _ _).trans
    exact sum_le_sum fun i _=>coin_scalar _ _ (site_portfolio X (Z.get i).cells (by omega) ht
      (filed.2 (Z.get i) (List.get_mem ..)).toll x K g).2.1

end YM.Integration.OriginalMarkedRunAction
