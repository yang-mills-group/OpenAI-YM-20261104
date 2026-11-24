import YM.MS.Rock.Pipes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-!
# Temporary compact approximating functions at finite D operations

After analytic interpolation use sequence Cut-K_n. Strict probability across rank all
 but growth measured point + derivatives. Compact bumps on $sq$. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plum
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans
open Momentum Metric
open scoped Topology ContDiff
variable {I J E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F]{z: UScale I} {v w r: I→ℝ}{p:E→F}
-- prepare lemma
lemma booty (h:∀ i, 0<v i) (hx:∀ i,v i≤1)(hu: HasTemperateGrowth p)(hp:p 0=0) : veg z (fun i x=>p (v i • x)) v:= by
   let S:=Arc.path z; let V:Scale I:={S with length:= v,pos:=h}; let U (i:I)(x:E):=p (v i • x); have he : Bound V U (fun _=>1) := V.rescaled hu
   let f(i:I):= he.smooth i; have hb : ∀ n:ℕ, S.full.Part S U (fun i _=>v i) (n+1):= by
       intro n; obtain ⟨C,hC,b,hb⟩:= he.quoted (n+1); refine ⟨C,hC,b,fun i x hp=> le_trans (hb i x (mem_univ _)) ?_⟩
       simp only [S,cheap_length,one_pow,mul_one,one_mul]; have hm:=h i; have hk:=hx i; have hv : V.full.cheap i x ≤ S.full.cheap i x:= by dsimp only [V,Scale.weight,Scale.full]; gcongr; exact (S.basic_pos _).le; exact hx i
       have ht:= V.full.cheap_pos (i:=i) (p:=x) (mem_univ _); change C*_ * v i^_ ≤ C*S.full.cheap i x^b*v i; have ht:= S.full.cheap_pos (i:=i) (p:=x) (mem_univ _); gcongr; rw [pow_succ]; exact mul_le_of_le_one_left hm.le (pow_le_one₀ hm.le hk)
   refine ⟨f,fun j=>?_⟩; rcases j with _|j; swap; · exact hb j
   refine LogTime.lower_jet S f (Cost.of_le ?_) (hb 0); intro i p hh; simp [hp]; exact (h _).le
lemma rails_mul {u w: I→ E→ ℂ}(h:rails z v u)(hw: veg z w r): rails z (fun i=>v i*r i) (fun i p=> u i p*w i p):= by
   let S:=Arc.path z; let A:=ContinuousLinearMap.fst ℝ E ℝ; let J:=ContinuousLinearMap.inl ℝ E ℝ
   have hh:= (Line.rapid (F:=ℝ) h).mul (Bound.linear A hw); intro b; specialize hh b; have he:= Costs.linear (D:= S.strict fun _=> (Set.univ:Set E)) J hh (fun i x _=> mem_univ _) ⟨1,zero_lt_one,1,fun i p hp=>by simp [J,Scale.slow,Scale.strict,S,Scale.full]⟩
   exact he
end YM.MS.Plum
