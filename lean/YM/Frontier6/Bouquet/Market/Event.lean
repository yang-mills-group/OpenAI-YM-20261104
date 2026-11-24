import YM.Frontier6.Bouquet.Atlas.Receptor
/-!
# Remit payment from heir positions as long as the cut is in force
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier.Court
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L Y:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{K:Final C F S}{P:Ensemble}{i:P}(Z:Court i)
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (R: Air (S:=S) P I L Y)
set_option quotPrecheck false
local notation "Q"=> Z.split
variable {d:Slot→ℕ}{f:Full (fiber P)}{t A a b B ε D C':ℝ}{j n:ℕ}{M:Pod→ℝ}{x:I}
variable (v:(i:Slot)→ S.Field (d i))(ht: Length P M t)(hh:R.suitable x C' t)(hf:Fellow P (R.lengths x) (R.region x) B f j A)(hc : Z.Contains (R.lengths x i) f)
    (hx:R.Welkin M)(hQ:Endows K d v Z.split M (Z.newWorld R) n B C' ε D)
local notation "X"=> R.lengths x i
local notation "S↑"=> fun a=> Z.offspring R K d v t a x f
include ht hh hf hc hQ hx
lemma prize (z:Margin P Z.split) (ha:0 < a){A':ℝ}(he:Checks (fiber P) (paths P (R.lengths x)) ((common a).film P Z.split f) n A') : ‖offspring Z R K d v t a x f z‖ * X^dim (Margin P Z.split) ≤ D*A'*R.freight d x ε:=by
    by_cases hv:Z.Love R x z
    · let y: Z.Volunteers R:=⟨(x,z),hv⟩; let A:= Z.newWorld R; let p:= slit (common a) Z.legend.le z f
      have hz:= Z.recruits R hf.fair hf.local_ hc ((common a).film_support _ _ _) he z hv
      have hX:=hQ.unit ha (ht.lower Z.legend.le) (f:=p) (i:=y) (fun i=>hh (assign Z.legend.le i)) hz
      have hk:= R.length_pos x i; rw [passings Z x z hv ε,← mul_assoc]; exact mul_le_mul_of_nonneg_right hX (pow_nonneg hk.le _)
    rw [Z.uninhabited R v t a z (Z.loveless R hx hf hc _ z hv), norm_zero,zero_mul]; exact mul_nonneg (mul_nonneg hQ.pos (he.nonneg)) (R.freight_pos d hx x ε).le
lemma precision (z:Margin P Z.split)(ha:0<a)(hb:a ≤ b)(he:4*b<Z.clearance*X)(hJ:n≤j) : ‖offspring Z R K d v t a x f z-offspring Z R K d v t b x f z‖ * X^dim (Margin P Z.split) ≤ D*A*R.freight d x ε*R.delta x b:=by
    by_cases hv:Z.Love R x z
    · let y:Z.Volunteers R:=⟨(x,z),hv⟩; let W:= Z.newWorld R; let p:=restrictS (plan_sub Z.legend.le) (insideCL loft_le z) f; have hx':=R.length_pos x i
      have hz:= Z.recruits R hf.fair hf.local_ hc (g:=f) (Set.Subset.rfl) (hf.costs.low hJ) z hv
      have he₁(u:ℝ)(hu:0<u)(hu':u ≤ b): slit (common u) Z.legend.le z f=p:=by unfold slit; rw [Z.film_delayed hx' hu hc (by linarith only [hu',he])];
      have hL:= hQ.paired ha hb (ht.lower Z.legend.le) (f:=p) (i:=y) (fun i=> hh (assign Z.legend.le i)) hz; unfold offspring Glued; rw [he₁ a ha hb,he₁ b (lt_of_lt_of_le ha hb) le_rfl]; refine (mul_le_mul_of_nonneg_right hL (pow_nonneg hx'.le (dim (Margin P Z.split)))).trans_eq ?_; rw [passings Z x z hv ε, show R.delta x b=W.delta y b from rfl]; change _ = D*A*((W.freight d y ε)*_)* W.delta y _; ring! -- V clarity?
    have hi (u:ℝ): offspring Z R K d v t u x f z=0:= Z.uninhabited R v t u z (Z.loveless R hx hf hc _ z hv); rw [hi,hi,sub_self,norm_zero,zero_mul]; exact mul_nonneg (mul_nonneg (mul_nonneg hQ.pos hf.costs.nonneg) (R.freight_pos d hx .. |>.le)) (R.delta_pos x (lt_of_lt_of_le ha hb)|>.le) -- priority
end YM.Frontier6.Bouquet.Atelier.Court
