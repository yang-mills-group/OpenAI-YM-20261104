import YM.Pert.Kinetic.Viscosity
import YM.Pert.Kinetic.Rows
import YM.Pert.Kinetic.Tilt
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision -- no VerifiedReset because Dir fields
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {σ C m Λ : ℝ} {p : Clip} {R : PathData G} (hb : R.Bounds p σ C Λ) {v : Directions G n}

def costPath (p : Clip) (R : PathData G) (β : ℝ) (a : fieldDir G n 1) (x : Site n) := β/2* (∑ y:PlaqAxes,(p.direct*‖faceCurl (x,y) a‖^2 + ‖ellLine R (x,y) a‖^2)) + soloLoop R a x
include hb
lemma cost_error (β : ℝ) {a : fieldDir G n 1} (h : Slow a m) (x : Site n) :
    |costPath p R β a x - β/2 * ∑ y:PlaqAxes, ‖faceCurl (x,y) a‖^2| ≤ m^3*(|β|/2 * (Fintype.card PlaqAxes : ℝ)*(2*rowCost σ C)+Λ/σ) := by
    unfold costPath; rw [add_sub_right_comm, ←mul_sub]; refine (abs_add_le ..).trans ?_
    rw [abs_mul, abs_div, abs_of_pos (zero_lt_two (α:=ℝ))]; exact (add_le_add (mul_le_mul_of_nonneg_left (row_squares hb h x) (by positivity)) (solo_cost R hb h x)).trans_eq (by ring)

def actualPath (R : PathData G) (β : ℝ) (v : Directions G n) := Patch.average (fun s => ∑ x:Site n, costPath p R β (Bid.pulled (lift1 v) s) x)
lemma quad_tangent (v : Directions G n) (s : Signed) : Tendsto (fun t:ℝ=> quadratic p R (pull s 0 (AnalyticBridge.VerifiedReset.line v t))/t^2) (𝓝[≠] 0)
    (𝓝 (∑ x:Site n, ∑ y:PlaqAxes,(p.direct*‖faceCurl (x,y) (Bid.pulled (lift1 v) s)‖^2+‖ellLine R (x,y) (Bid.pulled (lift1 v) s)‖^2)/2)) := by
    let a := Bid.pulled (lift1 v) s
    have he t : pull s 0 (AnalyticBridge.VerifiedReset.line v t)=Precision.represent (t • a) := by rw [← represent_pulled];congr 1; unfold AnalyticBridge.VerifiedReset.line Precision.represent; congr 1; change t • v=t • collect G (lift1 v); rw [back_wave]
    simp_rw [quadratic,he, Fintype.sum_prod_type,Finset.sum_div]
    have hi(x y): Tendsto (fun t:ℝ => (p.direct*G.price (faceValue (Precision.represent (t • a)) (x,y)) + ‖R.ell (Precision.represent (t • a)) (x,y)‖^2/2)/t^2) (𝓝[≠] 0)
     (𝓝 ((p.direct*‖faceCurl (x,y) a‖^2+‖ellLine R (x,y) a‖^2)/2)) := by
        have he := ((ell_limit R hb (x,y) a).norm.pow 2).div_const 2
        have hp := (price_limit (G := G) (V := fun t : ℝ => faceValue (Precision.represent (t • a)) (x,y))
            (by rw [zero_smul]; exact _root_.YM.Push.stroll_zero ..) (face_deriv (x,y) a)).const_mul p.direct
        have hv := hp.add he
        rw [add_div, mul_div_assoc]
        refine hv.congr' (Filter.Eventually.of_forall fun t => ?_)
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]; ring
    apply tendsto_finsetSum _ fun x _=> tendsto_finsetSum _ fun y _=> hi x y
set_option maxHeartbeats 2000000 in
lemma multi_tangent (β : ℝ) (v : Directions G n) : Tendsto (fun t:ℝ=> (β * mainTerm p R (AnalyticBridge.VerifiedReset.line v t)+Precision.loop R (AnalyticBridge.VerifiedReset.line v t))/t^2) (𝓝[≠] 0) (𝓝 (actualPath (p:=p) R β v)) := by
    have HE(s : Signed) t : pull s 0 (AnalyticBridge.VerifiedReset.line v t)=Precision.represent (t • (Bid.pulled (lift1 v) s)) := by rw [← represent_pulled];congr 1; unfold AnalyticBridge.VerifiedReset.line Precision.represent; congr 1; change t • v=t • collect G (lift1 v); rw [back_wave]
    let a (s:Signed) := Bid.pulled (lift1 v) s
    simp only [mainTerm,Precision.loop, Patch.average,HE,actualPath,costPath,soloLoop,pair,slotAt,true_and, ↓reduceIte]; simp_rw [Finset.sum_add_distrib]
    have hc(s) := (((quad_tangent hb v s).add (uncut_limit (k:=0) (a s) R.cubic hb.width hb.three)).add (uncut_limit (k:=1) (a s) R.quartic hb.width hb.four)).const_mul β |>.add (atoms_limit (a s) R.loop hb.width hb.two)
    have H := (tendsto_finsetSum Finset.univ fun s _ => hc s).const_mul (Fintype.card Signed:ℝ)⁻¹
    convert H using 1
    · funext t; dsimp only [a]; simp only [Finset.sum_add_distrib,Finset.sum_div,← HE,add_div,←Finset.mul_sum,←Finset.sum_div]; ring
    simp only [a,add_zero]; simp only [Finset.sum_add_distrib, ←Finset.sum_mul,←Finset.mul_sum,←Finset.sum_div]; -- prove β/2 vs multiplied
    congr 2; ring
end YM.Pert.Kinetic
