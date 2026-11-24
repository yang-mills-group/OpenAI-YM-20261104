import YM.SchemeRG11.Flare.Eye
/-!
The operative contact cancellations. Exact null of integrated theta checked
on full separated star; thus retains the same CR projection even across
unequal heat derivatives on the three marks.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.SchemeRG11.Flare
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4
variable {z x y : E4} (i m n : Eye)

-- standard completion-cor piece; sum ordered A-legs after orbit compression
local notation "Piz" => Axis × Axis × Axis × Axis
def pileup (i j k : Gem) (x y z:E4) := ∑ a:Axis,∑ b:Axis,coin i a b*edge j.1 j.2 a (x-z)*edge k.1 k.2 b (y-z)

lemma pylon (J K : Gem) (z x y:E4):
    (∑ p:Piz,yard J K i p*(Steam.score [p.2.2.1] (x-z)*Steam.score [p.2.2.2] (y-z)))=pileup (false,i) J K x y z:=by
  simp only [Fintype.sum_prod_type,pileup,yard,coin,edge,Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro w _; ring

lemma twin (I : Eye) (J K : Gem) (hx: z ≠ x)(hy:z≠y)(hh:x≠y) :
    pin (false,I) J K (castEye z x y) = - ((2:ℝ)⁻¹*pileup (false,I) J K x y z) := by
  rw [ridge]; simp only [replica _ _ (pantry hx hh hy)] -- he params
  simp_rw [mul_ite, mul_zero]; simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq,Finset.mem_univ,if_true, Finset.sum_const_zero]
  rw [← pylon]; congr 1
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _
  change yard _ _ _ _*((2:ℝ)⁻¹*(Steam.score [p.2.2.1] (x-z)*Steam.score [p.2.2.2] (y-z))) = _; ring

lemma pyramid (i m n : Eye) (z x y:E4):
    pileup (true,i) (false,m) (false,n) x y z= terminal x y z i m n:= by
  unfold pileup terminal coin; simp only [show x-z=-(z-x) by abel,show y-z=-(z-y) by abel,edge_minus,mul_assoc]

theorem spread (hx:z≠x)(hy:z≠y)(hh:x≠y) :
    let I : Gem := (true,i); let J : Gem:= (false,m); let K : Gem:= (false,n);
    street (Crew I J K (castEye z x y)) + pileup I J K x y z +pileup J K I y z x+pileup K I J z x y=impact x y z i m n := by
  dsimp only
  rw [inspect _ _ _ _ _ _ (pantry hx hh hy), twin _ _ _ hh hx.symm hy.symm,twin _ _ _ hy.symm hh.symm hx,ridge,pyramid]
  have hp t : (∑ p:Piz,yard (false,m) (false,n) t p*central true i false t [p.2.2.1] [p.2.2.2] (castEye z x y))=against i t m n z x y := rebus i t m n hx hy hh
  simp only [hp]; unfold impact; ring
end YM.SchemeRG11.Flare
