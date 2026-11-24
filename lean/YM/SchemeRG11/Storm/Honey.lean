import YM.SchemeRG11.Storm.Nectar
/-! Integrated curvature and potential readings for the tripod. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SchemeRG11.Storm
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace Classical
local notation "Tri" => Nodes 4
variable (i j m n : Eye)
/-- fan-F to fan-F at apex, signs from orientation. Uses entire star. -/
def central (hi : Bool) (i : Eye) (hj : Bool) (j : Eye) (V W : Sl) (X : Tri) :=
    -(∑ u,∑ v, rotatedProduct hi i hj j u v*yolk [u,v] V W X)

lemma commute (X : Tri) (V W : Sl) (u v : Axis) : yolk [u,v] V W X=yolk [v,u] V W X := by
  apply integral_congr_ae
  refine ae_restrict_of_forall_mem tripod_meas (fun p hp=> ?_)
  change orb _ _ _ _ _= orb _ _ _ _ _; rw [grape _ _ _ p hp,grape _ _ _ p hp]
  refine integral_congr_ae (Eventually.of_forall fun w=>?_)
  simp only [juice,second_line]; simp only [basis_eq,eq_comm (a:=u)]; ring
lemma replica {X : Tri} (hx : X∈ clearance 4) (hi : Bool) (V W : Sl):
    central hi i hi j V W X = if i=j then (2:ℝ)⁻¹*(Steam.score V (X 1-X 0)*Steam.score W (X 2-X 0)) else 0 := by
  have hh:= pays_trace (fun u v=>yolk [u,v] V W X) (fun v u=> commute X V W u v) hi i j
  simp_rw [show ∀ a b, yolk [a,b] V W X* rotatedProduct hi i hi j a b= rotatedProduct hi i hi j a b*yolk [a,b] V W X from fun a b=> mul_comm ..] at hh
  rw [Steam.span V W hx] at hh
  by_cases H:i=j <;> first | (rw [central]; split_ifs at *; linarith)

private lemma scores (a b:Axis)(x y w:E4) : twigs a b x y w= flow a (w-x)*flow b (w-y) := by
  have h i z : flow i z=Steam.score [i] (-z):= by
    have hh:=flow_odd z i; change _=-flow i z at hh
    change flow i z=grad i Maxwell.Green (-z)
    unfold flow at *; linarith
  rw [h,h]; simp only [twigs,neg_sub]

local notation "Piz" => Axis × Axis × Axis × Axis
def rune (p : Piz) := fan false j p.1 p.2.1*fan false m p.2.2.1 p.1*fan false n p.2.2.2 p.2.1
lemma forgery (x y w : E4): (∑ p:Piz, rune j m n p*twigs p.2.2.1 p.2.2.2 x y w)=integralInput j m n x y w := by
  simp only [Fintype.sum_prod_type,rune,integralInput,mLine, Finset.sum_mul,Finset.mul_sum,scores]
  congr 1; ext a; apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro d _; ring

variable {z x y : E4} (hx:z≠x)(hy:z≠y)(hh:x≠y)
include hx hy hh
theorem rebus : (∑ p : Piz, rune j m n p*central true i false j [p.2.2.1] [p.2.2.2] (castEye z x y))=against i j m n z x y := by
  simp_rw [show ∀ a b:Axis, central true i false j [a] [b] (castEye z x y)=savour i j a b z x y from fun a b=> (organ i j a b hx hy hh _ rfl).symm]
  let I := zone z x y
  have hi : MeasurableSet I:= isClosed_closedBall.measurableSet
  have H : innerZone i j m n z x y = I.indicator (fun w=>∑ p:Piz, rune j m n p*petal i j p.2.2.1 p.2.2.2 z x y w) := by
    ext w; by_cases h:w∈I
    · rw [indicator_of_mem h]; simp only [innerZone,if_pos (show w∈zone z x y from h),petal, ← forgery]
      simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_left_comm]
    rw [indicator_of_notMem h,innerZone,if_neg h]
  have Hb : outerZone i j m n z x y = Iᶜ.indicator (fun w=>∑ p:Piz, rune j m n p*pollen i j p.2.2.1 p.2.2.2 z x y w) := by
    ext w; by_cases h:w∈Iᶜ
    · rw [indicator_of_mem h]; simp only [outerZone,if_pos (show w∉zone z x y from h),pollen,← forgery]
      simp only [Finset.mul_sum,mul_left_comm]
    rw [indicator_of_notMem h,outerZone,if_neg (show ¬w∉zone z x y from h)]
  unfold savour against
  rw [H,Hb,integral_indicator hi,integral_indicator hi.compl,integral_finsetSum _ (fun p _=> (petals i j p.2.2.1 p.2.2.2 hx hy).const_mul _),integral_finsetSum _ (fun p _=> (pollens i j p.2.2.1 p.2.2.2 hx hy hh).const_mul _)]
  simp only [integral_const_mul,mul_add,Finset.sum_add_distrib]; rfl
end YM.SchemeRG11.Storm
