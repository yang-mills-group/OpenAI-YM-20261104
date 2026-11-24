import YM.FVA2.Gen.Cradle
/-!
 # Global real smooth parameter transport for entry into actual Gauge
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Wilson Precision MeasureTheory Labels Source
variable {G:Gauge}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}
local notation "Cℓ"=> G.Color
local notation "M"=> G.Mat
-- global smoothness from smooth ODE: using cofactor (star)
lemma MLtraj {p:ℝ→G.El}{F:ℝ→G.Color}(h:SolvesLink p F)(hp:ContDiff ℝ ∞ F): ContDiff ℝ ∞ (fun t=> G.mat (p t)):= by
 let f:= G.mat ∘ p; let K (t:ℝ):= G.colorMat (F t); have hk:ContDiff ℝ ∞ K:= G.colorMat.toContinuousLinearMap.contDiff.comp hp; have he(t:ℝ): HasDerivAt f (f t*K t) t:= h.2 t; have hm: Differentiable ℝ f:= fun x=> ( he x ).differentiableAt
 refine contDiff_infty.mpr ?_; intro n
 induction n with
 | zero=> exact contDiff_zero.mpr hm.continuous
 | succ n ih=>
    rw [ Nat.cast_add_one, contDiff_succ_iff_deriv ]; refine ⟨ hm, ?_,?_ ⟩; 
      --
    · simp
    change ContDiff ℝ ↑n ( deriv f ); rw [ show deriv f = f*K from funext fun t=> ( he t ).deriv ]; exact ih.mul ( hk.of_le ( WithTop.coe_le_coe.mpr le_top ) ) -- inspect
private lemma impF (g:G.El)(A B R:M): ((A*star (G.mat g)) * ( G.mat g * (B-R) * star ( G.mat g ) )) = A*B*star (G.mat g)+ A*(-R*star (G.mat g)):=by rw [ ← mul_assoc, ← mul_assoc (_*_) (G.mat g), mul_assoc A, G.mat_star_mul,mul_one, mul_sub,sub_mul,neg_mul,mul_neg,sub_eq_add_neg,mul_assoc A R _ ] -- star mat_inv normalization
variable {F:E×ℝ→G.Color}{p:E→ℝ→G.El}
lemma Meets.smooth (h:Meets F p)(hf:ContDiff ℝ ∞ F):ContDiff ℝ ∞ (fun u=> G.mat (p u 1)):=by
 apply contDiff_iff_contDiffAt.mpr; intro x; let l(s:ℝ):=p x s; let r:= G.mat ∘ l; let X:= enter G F
 let Z(t:E×ℝ) := r t.2 * ( X t-X (x,t.2) ) * star (r t.2)
 let Y(v:E)(t:ℝ):= G.mat (p v t) * star (r t); have hr: ContDiff ℝ ∞ r:= MLtraj (h x) (hf.comp (f:=fun s=>(x,s)) (contDiff_const.prodMk contDiff_id) ); have hu: Engage x Z Y:=by
    refine ⟨?_,fun t=>by simp [Z],fun v=>by unfold Y r l; rw [ comp_apply,(h x).1,(h v).1,G.mat_one, star_one,mul_one],?_⟩
    · have hX: ContDiff ℝ ∞ X:= G.colorMat.toContinuousLinearMap.contDiff.comp hf; have he:= hr.comp (f:=fun t:E×ℝ=> t.2) contDiff_snd; exact ((he.mul (hX.sub (hX.comp (f:=fun t:E×ℝ=>(x,t.2)) (contDiff_const.prodMk contDiff_snd) ) ) ).mul ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap.contDiff.comp he) )
    intro v t; refine ( (( h v ).2 t ).mul (( h x ).2 t ).star ).congr_deriv ?_; unfold Y Z; rw [star_mul,G.colorMat_skew]; exact ( impF .. ).symm -- check derivative formula
 have hy(y:E): G.mat (p y 1) = Y y 1 * r 1:= by unfold Y r l; rw [ mul_assoc,comp_apply,G.mat_star_mul,mul_one ]; --
 rw [funext hy]; exact hu.smooth.mul contDiffAt_const
end YM.FVA2.Gen
