import YM.SchemeRG11.Steam.Acorn
/-! At fixed times always permute whole lines. Does not justify free permutation over a singular integral. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

def rotate : Time≃ᵐTime := (MeasurableEquiv.prodComm (α:=ℝ)).trans MeasurableEquiv.prodAssoc
private lemma right_pres : MeasurePreserving (⇑rotate) (volume.restrict tripod) (volume.restrict tripod) := by
  rw [tree_m]; exact (show MeasurePreserving (⇑(MeasurableEquiv.prodComm (α:=ℝ) (β:=ℝ×ℝ))) _ _ from Measure.measurePreserving_swap).trans (measurePreserving_prodAssoc Zen Zen Zen)

def rev : Time ≃ᵐTime := (MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm
private lemma rev_pres : MeasurePreserving (⇑rev) (volume.restrict tripod) (volume.restrict tripod) := by
  rw [tree_m]
  exact (MeasurePreserving.id Zen).prod (show MeasurePreserving Prod.swap (Zen.prod Zen) (Zen.prod Zen) from Measure.measurePreserving_swap)

lemma twists (U V W : Sl) (x y z : E4) :
    yolk U V W (castEye x y z)= yolk V W U (castEye y z x) := by
  unfold yolk
  rw [← right_pres.integral_comp rotate.measurableEmbedding (fun p=> orb V W U p (castEye y z x))]
  apply setIntegral_congr_fun tripod_meas
  intro p hp
  have ht : rotate p ∈ tripod:= ⟨hp.2.1,hp.2.2,hp.1⟩
  exact (grape U V W p hp _).trans ((integral_congr_ae (Eventually.of_forall (fun w : E4=> by
    change tint U p.1 (x-w)*tint V p.2.1 (y-w)*tint W p.2.2 (z-w)= tint V p.2.1 (y-w)*tint W p.2.2 (z-w)*tint U p.1 (x-w)
    ring))).trans (grape V W U (rotate p) ht _).symm)
lemma braces (U V W : Sl) (x y z : E4) :
    yolk U V W (castEye x y z)= yolk U W V (castEye x z y) := by
  unfold yolk
  rw [← rev_pres.integral_comp rev.measurableEmbedding (fun p=> orb U W V p (castEye x z y))]
  apply setIntegral_congr_fun tripod_meas
  intro p hp
  have ht : rev p∈tripod:=⟨hp.1,hp.2.2,hp.2.1⟩
  exact (grape U V W p hp _).trans ((integral_congr_ae (Eventually.of_forall (fun w : E4=> by
    change tint U p.1 (x-w)*tint V p.2.1 (y-w)*tint W p.2.2 (z-w)= tint U p.1 (x-w)*tint W p.2.2 (z-w)*tint V p.2.1 (y-w); ring))).trans (grape U W V (rev p) ht _).symm)
end YM.SchemeRG11.Steam
