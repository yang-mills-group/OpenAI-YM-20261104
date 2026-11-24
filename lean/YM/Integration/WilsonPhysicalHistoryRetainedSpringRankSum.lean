import YM.Integration.WilsonPhysicalHistoryRetainedSpringRankFields

/-! Reassemble the rooted coefficient expenses for a complete old site.
Both paths, the two nonlinear orders and the whole filed list remain present. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup Comparison.RG02
open WilsonCoherentMayerHearing Dict06.Series PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def springRankTotal (G : Gauge) (r K d M : ℕ) : ℝ:=
  (r:ℝ)*(facePaper G K+Stationary.gramCost G 1)+2*(r+1)+3*(M:ℝ)*2^(d+1)
theorem rank_total_nonneg (G : Gauge) (r K d M : ℕ) : 0≤ springRankTotal G r K d M:=by
  unfold springRankTotal Stationary.gramCost;positivity [face_paper_nonneg G K]

theorem spring_rank_sum (X : Coat T F) (B : Clip) (path : PathData G) (Z : SeriesA G)
    (x : Site f) (r K d M : ℕ) {g p γ w E : ℝ} (hg : 0<g) (g1 : g≤1) (large : 1≤E)
    (limit : Z.length≤M) (direct : |B.direct|≤1) (gamma : |γ|≤g^2*(r:ℝ)*E) (weight : |w|≤(r+1)*E)
    (lo : 1/2≤p) (hi : p≤3/2) (low : ∀a∈Z,3≤a.grade) (high : ∀a∈Z,a.grade≤d)
    (gram : Rise.coin (sitePortfolio X (gramEntries path) x K g)≤g^2*(Stationary.gramCost G 1*E))
    (tri : Rise.coin (sitePortfolio X path.cubic x K g)≤g^3*E)
    (four : Rise.coin (sitePortfolio X path.quartic x K g)≤g^4*E)
    (atoms : ∀a∈Z,Rise.coin (sitePortfolio X a.cells x K g)≤g^(a.rise+2)*(3*E^2)) :
    Rise.coin (springPolynomial X B path Z γ w (Integral.temperature g*p) (g/Real.sqrt p) x K g)≤
      springRankTotal G r K d M*g^3*E^2 := by
  have ep : 0≤E:=zero_le_one.trans large
  have f0:=face_paper_nonneg G K
  have gram0 : 0≤Stationary.gramCost G 1:=by unfold Stationary.gramCost;positivity
  have egg:=face_root_price X x K hg.le g1
  have f : Rise.coin (MvPolynomial.C (B.direct:ℂ)*facePortfolio X x K g)≤g^2*facePaper G K*E:=by
    apply (rooted_currency _ _ egg).trans
    calc _ ≤ 1*(g^2*facePaper G K):=mul_le_mul_of_nonneg_right direct (mul_nonneg (sq_nonneg _) f0)
         _ ≤ _:=by simpa only [one_mul,mul_one] using mul_le_mul_of_nonneg_left large (mul_nonneg (sq_nonneg g) f0)
  have kin:=(Rise.taller 0 zero_le_one _ _).trans (add_le_add f gram)
  have price:=rooted_currency γ _ kin
  have four_le : g^4≤g^3:=pow_le_pow_of_le_one hg.le g1 (by decide)
  have kcap : Rise.coin (MvPolynomial.C (γ:ℂ)*(MvPolynomial.C (B.direct:ℂ)*facePortfolio X x K g+
      sitePortfolio X (gramEntries path) x K g))≤(r:ℝ)*(facePaper G K+Stationary.gramCost G 1)*g^3*E^2:=by
    apply price.trans
    calc _ ≤ (g^2*r*E)*(g^2*facePaper G K*E+g^2*(Stationary.gramCost G 1*E)):=by
                exact mul_le_mul_of_nonneg_right gamma (by positivity)
         _ = (r:ℝ)*(facePaper G K+Stationary.gramCost G 1)*g^4*E^2:=by ring
         _ ≤ _:=by gcongr
  have acap : Rise.coin (MvPolynomial.C (w:ℂ)*(sitePortfolio X path.cubic x K g+sitePortfolio X path.quartic x K g))≤
      (2*(r+1):ℝ)*g^3*E^2:=by
    apply (rooted_currency _ _ ((Rise.taller 0 zero_le_one _ _).trans
      (add_le_add tri (four.trans (mul_le_mul_of_nonneg_right four_le ep))))).trans
    calc _≤((r+1)*E)*(g^3*E+g^3*E):=mul_le_mul_of_nonneg_right weight (by positivity)
         _=_:=by ring
  have cap : ∀i:Fin Z.length,Rise.coin (MvPolynomial.C
      (((Integral.temperature g*p*(g/Real.sqrt p)^((Z.get i).grade-(Z.get i).rise)):ℝ):ℂ)*
      sitePortfolio X (Z.get i).cells x K g)≤(2:ℝ)^(d+1)*g^3*(3*E^2):=fun i=>
    graded_packet X (Z.get i) d (low _ (List.get_mem ..)) (high _ (List.get_mem ..)) x K hg g1 lo hi
      (by positivity) (atoms _ (List.get_mem ..))
  unfold springPolynomial springRankTotal
  apply (Rise.taller 0 zero_le_one _ _).trans
  calc _ ≤ ((r:ℝ)*(facePaper G K+Stationary.gramCost G 1)*g^3*E^2+(2*(r+1):ℝ)*g^3*E^2)+
            ∑ _i:Fin Z.length, (2:ℝ)^(d+1)*g^3*(3*E^2):=add_le_add
              ((Rise.taller 0 zero_le_one _ _).trans (add_le_add kcap acap))
              ((Rise.collect 0 zero_le_one _ _).trans (sum_le_sum fun i _=>cap i))
       _ ≤ ((r:ℝ)*(facePaper G K+Stationary.gramCost G 1)*g^3*E^2+(2*(r+1):ℝ)*g^3*E^2)+
               (M:ℝ)*((2:ℝ)^(d+1)*g^3*(3*E^2)):=by
              simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (show (Z.length:ℝ)≤(M:ℝ) from Nat.cast_le.mpr limit) (show 0≤(2:ℝ)^(d+1)*g^3*(3*E^2) by positivity))
       _=_:=by ring

end YM.Integration.OriginalMarkedRunAction
