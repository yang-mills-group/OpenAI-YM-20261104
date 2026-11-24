import YM.SchemeRG11.Steam.Paint
/-!
The collapse of a single same-helicity line (trace calculation) from open
tripod. No e≠0 contraction in this rule. Comes from a boundary of the heat
integration, not from dropping a distribution supported when w=apex.
-/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

def score (V : Sl) := series Green (V.map basis)

variable {x : Tri} (V W : Sl) (hx : x ∈ clearance 4)
include hx
lemma span : (∑ i:Axis,yolk [i,i] V W x) = - (score V (x 1-x 0)*score W (x 2-x 0)) := by
  let F := fun t : Time=> ∑ i:Axis, orb [i,i] V W t x
  have hi : IntegrableOn F tripod := integrable_finsetSum _ (fun i _=> oak [i,i] V W hx)
  have hv : Integrable F (Zen.prod (Zen.prod Zen)) := by rwa [←tree_m]
  have hh : x 1 ≠ x 0 ∧ x 2 ≠ x 0 := by
      constructor
      · intro h; have hp := hx 2; change 0 < ‖x 0-x 1‖^2/4 at hp; rw [h] at hp; simp at hp
      intro h; have hp := hx 1; change 0< ‖x 2-x 0‖^2/4 at hp; rw [h] at hp; simp at hp
  let ν:=Zen.prod Zen
  have hk : ∀ᵐ y : ℝ×ℝ ∂ν, (∫ t,F (t,y) ∂Zen) = -(tint V y.1 (x 1-x 0)*tint W y.2 (x 2-x 0)) := by
    have he : ∀ᵐ y : ℝ×ℝ ∂ν, 0<y.1 ∧ 0<y.2 := by rw [show ν=(volume:Measure (ℝ×ℝ)).restrict (openZen ×ˢ openZen) from Measure.prod_restrict ..]; exact ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) (fun y hy=>hy)
    filter_upwards [he,hv.prod_left_ae] with y hy ht
    have hb:= integral_Ioi_of_hasDerivAt_of_tendsto (m:=0) (a:=0) (f:=fun t=> orb [] V W (t,y) x) (f':=fun t=> F (t,y)) ?_ (fun t ha=> glory V W x hy.1 hy.2 ha) ht (thinning V W x hy.1 hy.2 hx)
    · apply hb.trans; rw [zero_sub,show (0,y)=( (0:ℝ),y.1,y.2) from rfl,arrive _ _ hy.1 hy.2 V W x]
    exact (oak_c [] V W (y:=(0:ℝ)) (u:=fun t : ℝ=>(t,y)) (v:=fun _=>x) (by fun_prop) continuousAt_const (by rw [knot]; dsimp; rw [zero_mul,zero_mul,zero_add,zero_add]; exact mul_pos hy.1 hy.2)).continuousWithinAt -- x arg invalid
  unfold yolk
  rw [← integral_finsetSum _ (fun i _=> oak [i,i] V W hx),tree_m]
  rw [integral_prod_symm F hv] -- defeq
  rw [integral_congr_ae hk, integral_neg, integral_prod_mul (fun t=>tint V t (x 1-x 0)) (fun t=>tint W t (x 2-x 0)),← show (volume:Measure ℝ).restrict openZen=Zen from rfl, sculpt V (x 1-x 0) (sub_ne_zero.mpr hh.1),sculpt W (x 2-x 0) (sub_ne_zero.mpr hh.2)]; rfl
end YM.SchemeRG11.Steam
