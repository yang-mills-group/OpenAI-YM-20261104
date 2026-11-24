import YM.Integration.WilsonPublicForkIndependentFields
import YM.Integration.WilsonPublicForkReadings
/-! The two original signed readings may first pass through the selected
physical regulator. The independent fitted coefficient then uses its own limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentReceipts
open Filter Function Set MeasureTheory FVA2 FVA2.O FVA2.O.Score FVA2.O.Enh
open FVA2.Register FVA2.Scale Maxwell XSpace XSpace.Normalize
open MS MS.Land MS.Fleet MS.Theater RG17 Trace.Pilot
open WilsonMSDictionaryFarRead WilsonMSDictionaryVector WilsonPublicForkIndependentPlacement
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{I:Type}[Fintype I]{h:ℕ}{f:Extraction.Order}

private theorem priced {e:ℝ→Free C h}{y:Free C h}(limit:Tendsto e atTop (𝓝 y))
    (gram:Dframe.Toon G h→I→ℂ){δ:ℝ}(pos:0<δ):
    ∀ᶠs:ℝ in atTop,∀j,
      ‖(∑k,(WilsonMSDictionaryVector.basis C h).repr y k*gram k j)-
        ∑k,(WilsonMSDictionaryVector.basis C h).repr (e s) k*gram k j‖≤δ:=by
  apply eventually_all.mpr;intro j
  have res:Tendsto (fun s=>∑k,(WilsonMSDictionaryVector.basis C h).repr (e s) k*gram k j) atTop
      (𝓝 (∑k,(WilsonMSDictionaryVector.basis C h).repr y k*gram k j)):=by
    apply tendsto_finsetSum;intro k _
    exact (((WilsonMSDictionaryVector.basis C h).coord k).toContinuousLinearMap.continuous.continuousAt.tendsto.comp limit).mul_const _
  filter_upwards [Metric.tendsto_nhds.mp res δ pos] with s small
  rw [norm_sub_rev];exact (by simpa only [dist_eq_norm] using small.le)

theorem original (e:ℝ→Free C h)(y:Free C h)(limit:Tendsto e atTop (𝓝 y))
    (actual:ℕ→ℕ→I→ℂ)(heads:ℕ→ℕ→Dframe.Toon G h→I→ℂ)
    (model:I→ℂ)(gram:Dframe.Toon G h→I→ℂ){a b c η:ℝ}(positive:0<η)
    (original:f.late fun N per=>(∀j,‖actual N per j-model j‖≤a*η) ∧ (∀k j,‖heads N per k j-gram k j‖≤b*η))
    (independent:∀j,‖model j-∑k,(WilsonMSDictionaryVector.basis C h).repr y k*gram k j‖≤c*η)
    (δ:ℝ)(dp:0<δ):
    ∃ᶠs:ℝ in atTop,f.late fun N per=>(∀j,‖actual N per j-model j‖≤a*η) ∧
        (∀k j,‖heads N per k j-gram k j‖≤b*η) ∧
        ∀j,‖model j-∑k,(WilsonMSDictionaryVector.basis C h).repr (e s) k*gram k j‖≤(c+δ)*η:=by
  apply Eventually.frequently
  filter_upwards [priced limit gram (mul_pos dp positive)] with s stable
  apply (f.fused (fun i=>(∀j,‖actual i.1 i.2 j-model j‖≤a*η) ∧
      (∀k j,‖heads i.1 i.2 k j-gram k j‖≤b*η) ∧
      ∀j,‖model j-∑k,(WilsonMSDictionaryVector.basis C h).repr (e s) k*gram k j‖≤(c+δ)*η)).mp
  have en:=(f.fused (fun i=>(∀j,‖actual i.1 i.2 j-model j‖≤a*η) ∧ (∀k j,‖heads i.1 i.2 k j-gram k j‖≤b*η))).mpr original
  filter_upwards [en] with i earned
  refine ⟨earned.1,earned.2,fun j=>?_⟩
  have step:=dist_triangle (model j) (∑k,(WilsonMSDictionaryVector.basis C h).repr y k*gram k j)
    (∑k,(WilsonMSDictionaryVector.basis C h).repr (e s) k*gram k j)
  simp only [dist_eq_norm] at step
  exact step.trans ((add_le_add (independent j) (stable j)).trans_eq (by ring))

end YM.Integration.WilsonPublicForkIndependentReceipts
