import YM.X.Haze.Visa
import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-!
# Forward powers on smooth tests. scaled Whitney convergence and sup bound. Directions scalar indexed; MVT.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Haze
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m v:ℕ} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{h:E4→V} -- upper e4 name
variable (l:List Axis)(a:ℝ)
def forwardL (l:List Axis)(e:ℝ)(f:E4→ V): E4→V:=match l with
   | []=>f
   | i::l=> fun x=> forwardL l e f (x+e • basis i)-forwardL l e f x
def thetaL (l:List Axis)(f:E4→V):E4→V:=match l with
   | []=>f
   | i::l=> thetaL l (Maxwell.grad i f)
lemma steps_match (z:Cover): forwardL l a h (spot a z)= Interval.grads l (fun z=>h (spot a z)) z:= by
   induction l generalizing z with
   | nil=> rw [forwardL]; rfl
   | cons i l IH=> rw [Interval.grads,differ,forwardL,← IH,← IH]; rw [show spot a (z+step i)=spot a z+a • basis i from by simp only [spots,mapZ_step,smul_add]]
lemma cForward (f:ContDiff ℝ ∞ h): ContDiff ℝ ∞ (forwardL l a h):= by
   induction l with
   | nil=> rw [forwardL]; exact f
   | cons i l IH=> rw [forwardL]; exact (IH.comp (contDiff_id.add contDiff_const)).sub IH
lemma cMore (f:ContDiff ℝ ∞ h)(i): ContDiff ℝ ∞ (Maxwell.grad i h):= contDiff_iff_contDiffAt.mpr (fun _=> Maxwell.grad_smooth i f.contDiffAt (by simp))
lemma cTheta (f:ContDiff ℝ ∞ h):ContDiff ℝ ∞ (thetaL l h):= by induction l generalizing h with| nil=>rw [thetaL]; exact f| cons i l IH=>rw [thetaL]; exact IH (cMore f _)
lemma thru (f:ContDiff ℝ ∞ h)(i:Axis) : Maxwell.grad i (forwardL l a h)= forwardL l a (Maxwell.grad i h):= by
   induction l with
   | nil=> rw [forwardL,forwardL]
   | cons j l IH=>
       let F:=forwardL l a h; let b:= a • basis j; have he:F= forwardL l a h:=rfl
       rw [forwardL,forwardL,← IH]; have Hp := (cForward l a f).differentiable (by simp)
       funext x; change fderiv ℝ (fun t=>F (t+b)-F t) x (basis i)= fderiv ℝ F _ _ - fderiv ℝ F _ _; rw [fderiv_fun_sub]; swap; -- apply
       · exact Hp.comp (differentiable_id.add_const _) x
       rw [show fderiv ℝ (fun t:E4=> F (t+b)) x= fderiv ℝ F (x+b) from ((Hp (x+b)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const b)).fderiv]; rfl
       exact Hp x -- name

omit V
lemma reach_exists {a:ℝ}{f:E4→ℝ}(hf:ContDiff ℝ ∞ f)(ha:0<a)(x:E4): ∃ y:E4,dist x y ≤ (l.length:ℝ)*a ∧ forwardL l a f x=a^l.length * thetaL l f y:= by
    induction l generalizing f x with
    | nil=> exact ⟨x,by simp [forwardL,thetaL]⟩
    | cons i l IH=>
       let L(u:ℝ):E4:= x+u • basis i; let g:= forwardL l a f; let Φ:= g ∘ L; have hg:= cForward l a hf; have hp : Differentiable ℝ Φ:= (hg.comp (show ContDiff ℝ ∞ L from contDiff_const.add (contDiff_id.smul contDiff_const))).differentiable (by simp)
       obtain ⟨v,⟨hV,hV'⟩,he⟩:= exists_deriv_eq_slope Φ ha hp.continuous.continuousOn hp.differentiableOn
       obtain ⟨y,hy,H⟩:= IH (cMore hf i) (L v); refine ⟨y,?_ ,?_⟩
       · have hxy := dist_triangle x (L v) y; rw [dist_eq_norm' x (L v),show L v - x=v • basis i from by unfold L; abel, norm_smul,basis_norm,Real.norm_of_nonneg hV.le] at hxy -- wrong rw dist first
         simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; linarith
       have ht: HasDerivAt L (basis i) v:= by simpa only [one_smul] using! (((hasDerivAt_id' v).smul_const (basis i)).const_add x)
       have heq : deriv Φ v=forwardL l a (Maxwell.grad i f) (L v):= ((hg.differentiable (by simp) (L v)).hasFDerivAt.comp_hasDerivAt v ht).deriv.trans (congr_fun (thru l a hf i) _)
       change forwardL (i::l) a f x=a^(l.length+1)*thetaL l (Maxwell.grad i f) y; rw [forwardL,pow_succ]; rw [heq,H,sub_zero,eq_div_iff ha.ne'] at he; unfold Φ L at he; simp only [comp_apply,zero_smul,add_zero, g] at he; linarith
variable {w:E4→ℝ}(hf:ContDiff ℝ ∞ w)
include hf
lemma visa_smooth (hr:R≥0)(hq:1<q.val): Visa q R (l.length:ℤ) 0 (fun i=> Interval.grads l (fun x=> w (spot (ε i) x)) ) := by
    let f:=thetaL l w; have hh : Continuous f:= (cTheta l hf).continuous
    let t:=R+l.length; obtain ⟨y,hy,h⟩:= IsCompact.exists_isMaxOn (isCompact_closedBall (0:E4) t) (nonempty_of_mem (mem_closedBall_self (by unfold t; positivity))) hh.norm.continuousOn
    choose X hx hX using fun (i:ℕ)(z:Cover)=> reach_exists l hf (epsilon_pos q i) (spot (ε i) z)
    refine ⟨⟨‖f y‖, norm_nonneg _,?_⟩,fun x hp hr z hz=>?_⟩
    · refine Eventually.of_forall (fun i z he=> ?_); rw [← steps_match,hX, norm_mul,Real.norm_of_nonneg (pow_nonneg (epsilon_pos q i).le _),price,zpow_zero,mul_one,zpow_natCast,mul_comm (ε i^_ : ℝ)]
      -- compact
      refine mul_le_mul_of_nonneg_right (h ?_) (pow_nonneg (epsilon_pos q i).le _)
      unfold t; rw [mem_closedBall,dist_comm,dist_zero_left]; have hi:= gate_range R hr z he; have hu := dist_triangle_right (X i z) (0:E4) (spot (ε i) z); -- simpler
      have hl:= hx i z; rw [dist_zero_right, dist_comm (X i z) _, dist_zero_left] at hu; have ht := (show ε i≤1 from inv_le_one_of_one_le₀ (Interval.cane q i)); nlinarith [Nat.cast_nonneg (α:=ℝ) l.length]
    let v(i):= X i (z i); have he:Tendsto v Fℕ (𝓝 x):= by
       refine (show plot q z x from hz).congr_dist (squeeze_zero (fun i=>dist_nonneg) (fun i=>hx i _) ?_); simpa only [mul_zero] using! (paths hq).cutoff.const_mul (l.length:ℝ)
    refine ⟨f x, (hh.continuousAt.tendsto.comp he).congr fun i=>?_⟩; rw [← steps_match,hX,smul_eq_mul,zero_sub,zpow_neg,zpow_natCast,inv_mul_cancel_left₀ ((pow_pos (epsilon_pos q i) _).ne')]; rfl
end YM.PositionX.Haze
