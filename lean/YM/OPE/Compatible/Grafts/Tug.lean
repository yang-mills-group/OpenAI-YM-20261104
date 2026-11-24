import YM.OPE.Compatible.Straws.Oui
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Polynomial.Basic
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Essay
open Gael Stranded
open Polynomial
omit [MeasurableSpace E] [BorelSpace E] in
lemma thighs (x:ℝ→E)(hx:Gael x)(p:E→ℝ)(hp:Bond p) : trill (p ∘ x)= trill (p ∘ (trill x).atK):=by
     induction hp with
     | keep c=> exact rfl
     | glyph c=>
        let U:= toContinuousLinearMap c; rw [show trill (c ∘ x)= _ from Gael.chooses (k:= ⟨U (trill x).s,_,_⟩) (Reads.tours U (Gael.oath hx)), show trill (c ∘ (trill x).atK)= _ from Gael.chooses (k:= ⟨U (trill x).s,_,_⟩) (Reads.tours U (Reads.selves _))] -- coercions
     | @add p q hp hq hv hy=>
          have he(x':ℝ→E)(h:Gael x'):trill ((p+q)∘x')=trill (p∘x')+trill (q∘x'):= Gael.chooses ((Gael.oath (Gael.climb _ hp h)).sum (Gael.oath (Gael.climb _ hq h))); rw [he x hx, he _ (Exists.intro _ (Reads.selves _)),hv,hy] -- he self rhs rewrites?
     | @mul p q hp hq hv hy=>
          have he(x':ℝ→E)(h:Gael x'):trill ((p*q)∘x')=trill (p∘x')*trill (q∘x'):= Gael.chooses ((Gael.oath (Gael.climb _ hp h)).pile (Gael.oath (Gael.climb _ hq h))); rw [he x hx, he _ (Exists.intro _ (Reads.selves _)),hv,hy]
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma yolk (p:E→ℝ)(x:JetS E)(hp:Bond p):∃ f: ℝ[X],∀ t:ℝ,f.eval t=p (x.atK t):=by induction hp with
     | keep c=> exact ⟨C c, fun _=> eval_C⟩
     | glyph c=>exact ⟨C (c x.s)+Polynomial.X*C (c x.l)+Polynomial.X^2*C (c x.h),fun i=>by simp [atK];ring⟩
     | add _ _ ih he=> obtain ⟨p,hp⟩:=ih; obtain ⟨q,hq⟩:=he; exact ⟨p+q, fun i=>by rw [eval_add,hp,hq];rfl⟩
     | mul _ _ ih he=> obtain ⟨p,hp⟩:=ih; obtain ⟨q,hq⟩:=he; exact ⟨p*q, fun i=>by rw [eval_mul,hp,hq];rfl⟩
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma frontage (B:E→L[ℝ] F)(p:E→ℝ)(K:ℝ)(k:ℕ)(hK:0 ≤ K)(h:∀ v:E, ‖p v‖ ≤ K*(1+‖B v‖)^k) (x:JetS E)(f:ℝ[X])(hf:∀ i,f.eval i=p (x.atK i)): f.degree≤2*k:=by
    let a:= B x.s; let b:= B x.l; let c:= B x.h; let G:=1+‖a‖+‖b‖+‖c‖
    have hp(t:ℝ)(ht:1 ≤ t):‖p (x.atK t)‖≤K* G^k*t^(2*k):=by
          have hx:1+‖B (x.atK t)‖≤ G*t^2:=by
               rw [atK,map_add,map_add,map_smul,map_smul]; apply le_trans (add_le_add_right ((norm_add_le ..).trans (add_le_add_left (norm_add_le ..) _)) 1); -- add indexes
               change 1+(‖a‖+‖t • b‖+ ‖t^2 • c‖)≤ _; simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ t from by linarith), abs_of_nonneg (sq_nonneg t)]; unfold G; nlinarith only [ht, mul_nonneg (norm_nonneg a) (show 0≤ t^2-1 by nlinarith), mul_nonneg (norm_nonneg b) (show 0≤ t^2-t by nlinarith), show 1≤ t^2 by nlinarith]
          apply (h _).trans; rw [pow_mul, mul_assoc,← mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx k) hK
    let P:= (Polynomial.X:ℝ[X])^(2*k); have hx:P.degree=(↑(2*k):WithBot ℕ):=degree_X_pow _; by_contra h; push Not at h; have hy : Tendsto (fun y:ℝ=> |f.eval y/P.eval y|) atTop atTop:= f.abs_div_tendsto_atTop_atTop_of_degree_gt P (by rw [hx]; exact_mod_cast h) (pow_ne_zero _ X_ne_zero)
    obtain ⟨v,hv,hT⟩:= ((hy.eventually (eventually_gt_atTop (K*G^k))).and (eventually_ge_atTop 1)).exists; rw [hf,abs_div,show P.eval v=_ from (show P.eval v=v^(2*k) from by simp [P]),abs_of_nonneg (pow_nonneg (show 0 ≤ v by linarith only [hT]) _)] at hv; exact (not_lt_of_ge ((div_le_iff₀ (pow_pos (show 0<v from by linarith only [hT]) _)).mpr (hp v hT))) hv -- norm
end Essay
end YM.OPE.Libra
