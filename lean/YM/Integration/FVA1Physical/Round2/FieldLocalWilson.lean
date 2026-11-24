import YM.Integration.FVA1Physical.Round2.FieldRecoil

/-! For an actual product of field stencils, the local reading in the
normalized analytic expansion is the independently computed local polynomial
bank, on the identical Schur mean, covariance, and exterior data. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Lattice RG YM.Wilson Tree Precision Exterior Pressure RGComparison.Core16 RGComparison.Core16.Spool
open MSbar MSbar.Cacao MSbar.Whisk MSbar.Duel MSbar.Lapaz MSbar.Bakery MSbar.Bakery.Film
open MSbar.Lis MSbar.Rolling MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open MSbar.Mosaic MSbar.Kelvin MSbar.Jade MSbar.Bakery.Portal Push.Uniform Next.SectorChange
open YM.Integration.FVA1Physical.Wilson
open scoped Classical
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G) (A : Mosaic.Issue G)

theorem field_local_wilson (V : Voice G) (χ : ChartRatio G) (X Y : Support A.f)
    (U : Config G A.f) (t : ℝ) (Z : Positions (Primary A.c G)) (p : ℕ)
    (clamp : ℝ → ℝ) (color : Site A.f → G.Color) (o : ι → Site A.f) (part : Bool)
    (pos : (mold A.pre A.F A.v).PosDef) (kind : Kind A.T) :
    Lapaz.localW A.F A.pre A.v V χ X Y U t Z A.T p clamp color (jointFieldBank J A o part) =
      taste p (Lapaz.owes (vene X A.F G) ((pinch (includeX A.F X) (mold A.pre A.F A.v))⁻¹)
        (barbed A.F A.v χ A.T) (jointFieldBank J A o part)
        (meetVar Z (berth A.F A.pre A.v V X Y U Z t 0)) p) t := by
  unfold Lapaz.localW
  have hc : ((pinch (includeX (G:=G) A.F X) (mold A.pre A.F A.v))⁻¹).PosDef :=
    (pos.submatrix (secureY A.F X G)).inv
  apply add_eq_left.mpr
  exact field_recoil_zero J A o part (vene X A.F G) hc _ (Rolling.well A.F A.v χ A.T kind) _ p _

theorem field_local_inner (V : Voice G) (χ : ChartRatio G) (y : ℝ) (b : Site A.f)
    (U : Config G A.f) (Z : Positions (Primary A.c G)) (p : ℕ)
    (clamp : ℝ → ℝ) (color : Site A.f → G.Color) (o : ι → Site A.f) (part : Bool)
    (pos : (mold A.pre A.F A.v).PosDef) (kind : Kind A.T) (hg : A.fClock ≠ 0) :
    Lapaz.localW A.F A.pre A.v V χ (boxX y b) (boxY y b) U A.fClock Z A.T p clamp color
      (jointFieldBank J A o part) =
      taste p (innerColumn A χ V y (A.fClock • Z) b U (jointFieldBank J A o part) p) A.fClock := by
  rw [field_local_wilson J A V χ _ _ U _ Z p clamp color o part pos kind]
  simp only [innerColumn,innerPoint,berth,Matrix.mulVec_zero,add_zero,inv_smul_smul₀ hg]
  rfl

end YM.Integration.FVA1Physical.Round2.Curvature
