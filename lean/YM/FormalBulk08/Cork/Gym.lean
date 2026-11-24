import YM.FormalBulk08.Cork.Tent

/-! color simplicity. Choose sole index only by witness. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Cork
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Stationary
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {T : Slopes G} (h:Splendid T)
include h

lemma glassH (a b i j x) (g : G.El): hem T a b i j x= ∑ p:hue G,∑ q:hue G, hem T a b p q x * (suit g p i*suit g q j):= by
    let v:= ![(x,coord a,i),(0,coord b,j)]; obtain he := h.stain g v; change T v = _
    rw [he,← Equiv.sum_comp (finTwoArrowEquiv _).symm, Fintype.sum_prod_type];simp_rw [Fin.prod_univ_two]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl;intro w _;congr 1
    unfold hem; apply congr_arg T; ext1 k; fin_cases k <;> rfl
lemma glassMirror (a b i j)(g:G.El): mir T a a i j b b=∑ p:hue G,∑ q:hue G,mir T a a p q b b * (suit g p i*suit g q j) := by
   let f:=ch b*ch b; let U (p q:hue G) (v:Cover):=hem T a a p q v*f v *(suit g p i*suit g q j); unfold mir net; simp_rw [←tsum_mul_right]; change _= ∑ x,∑ y,∑' v,U x y v
   have hh p q : Summable (U p q):=(h.fares.sum a a p q ((Pad.ch b).mul (Pad.ch b))).mul_right _
   have he p : ∑ x,∑' v,U p x v=∑' v, ∑ x,U p x v:=(Summable.tsum_finsetSum (fun x _=> hh p x)).symm
   simp_rw [he]; rw [←Summable.tsum_finsetSum]; swap; · intro p _; exact summable_sum fun q _=> hh p q
   change (∑' v,hem T a a i j v*f v)= _;apply tsum_congr; intro v; rw [glassH h a a i j v g,Finset.sum_mul];apply Finset.sum_congr rfl;intro p _; rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro q _;unfold U; ring
-- into paints API
lemma mirror_lit (a b) : (fun v: Stationary.Ink G 2=>mir T a a (v 0) (v 1) b b) ∈paints G 2:= by
    intro g z
    have ha i (p:G.Color) : G.adjoint g p i= ∑ c:hue G,suit g i c * p c := (congr_fun (shy g p) i).symm
    simp_rw [Fin.prod_univ_two]; let R:=fun i j=>mir T a a i j b b
    -- matrix notation
    conv_lhs=> rw [←Equiv.sum_comp (finTwoArrowEquiv _).symm]
    conv_rhs=> rw [←Equiv.sum_comp (finTwoArrowEquiv _).symm]
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    change ∑ i:hue G,∑ j:hue G,R i j*(G.adjoint g (z 0) i * G.adjoint g (z 1) j)=∑ i:hue G,∑ j:hue G,R i j*(z 0 i*z 1 j)
    simp_rw [ha,Finset.sum_mul,Finset.mul_sum]
    let f(i j u v):= R i j * (suit g i u * z 0 u * (suit g j v*z 1 v))
    change ∑ i,∑ j,∑ u,∑ v,f i j u v = _
    conv_lhs =>
       arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext u; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun v _=>?_
    rw [show R u v= _ from glassMirror h a b u v g, Finset.sum_mul];simp_rw [Finset.sum_mul];apply Finset.sum_congr rfl; intro i _;apply Finset.sum_congr rfl; intro j _;unfold f R;ring
lemma detects {i:hue G}(hs:G.Simple)(a b)(hw : mir T a a i i b b=0) (u v : hue G): mir T a a u v b b=0:= by
   exact congr_fun (iris_detect _ hs (mirror_lit h a b) (fun i j=> invert_hem h ..) i hw) ![u,v]
end YM.FormalBulk08.Cork
