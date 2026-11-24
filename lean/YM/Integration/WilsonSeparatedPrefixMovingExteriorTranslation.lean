import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentFittedExteriorProfile

/-! Moving the measuring cell moves the smooth exterior profile on its
original normalized source. Every visited lattice site agrees. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingExteriorTranslation
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}

def moved (F:Rarity D)(y:ℝ)(z o:CellR):Rarity D:=home F 1 one_pos (y • (z.val-o.val))

theorem wheel (F:Rarity D)(x y:ℝ)(site:Cover)(z o:CellR):
    wheelC x y site F.ψ z=wheelC x y site (moved F y z o).ψ o:=by
  apply congr_arg (page D)
  apply Subtype.ext
  funext v
  change F.ψ.val (Mer.address x y z site v)=
    (1:ℝ)⁻¹^4*F.ψ.val (Mer.address (1:ℝ)⁻¹ 0 zeroC 0
      (-(y • (z.val-o.val))+Mer.address x y o site v))
  rw [towards0]
  simp only [inv_one,one_pow,one_mul,one_smul]
  apply congr_arg F.ψ.val
  unfold Mer.address Mer.position
  module

theorem visits (F:Rarity D)(x y:ℝ)(hx:0<x)(z o:CellR):
    VisitsT F x y z=VisitsT (moved F y z o) x y o:=by
  ext site
  rw [visiting hx,visiting hx,wheel F x y site z o]

theorem site (P:TowerS G D)(F:Rarity D)(x y:ℝ)(b:Cover)(z o:CellR):
    locale z (shoe P F x y b)=locale o (shoe P (moved F y z o) x y b):=by
  apply Prod.ext
  · funext per j r w
    change P.1 per j r _ (wheelC x y b F.ψ z)=P.1 per j r _ _
    rw [wheel F x y b z o]
  · funext j r w
    change P.2 j r _ (wheelC x y b F.ψ z)=P.2 j r _ _
    rw [wheel F x y b z o]

theorem original (P:TowerS G D)(F:Rarity D)(x y:ℝ)(hx:0<x)(z o:CellR)(h:ℕ):
    word P F x y z h=word P (moved F y z o) x y o h:=by
  classical
  rw [word,word,pupil_eye _ _ _ _ _ _ hx,pupil_eye _ _ _ _ _ _ hx,visits F x y hx z o]
  exact Finset.sum_congr rfl fun b _=>congr_arg (drumB h x • ·) (site P F x y b z o)

theorem appointed (F:SealR G)(A:Levels G)(C:ChartRatio G)(ψ:Rarity F.D)(m i N:ℕ)(y:ℝ)(z o:CellR)(X:F.Rider):
    locale z (F.spins A C ψ m i N y X)=locale o (F.spins A C (moved ψ y z o) m i N y X):=by
  exact original _ ψ _ y (pace_pos ..) z o F.h

end YM.Integration.WilsonSeparatedPrefixMovingExteriorTranslation
