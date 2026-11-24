import YM.OPE.Compatible.Navy.Dog
/-!
# Brush product recoil
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Pilot
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{I J U K:Type}[Fintype I][Fintype J][Fintype U]
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable (p: U ≃ I ⊕ J)
local notation "L" => prL p G
local notation "R" => prR p G
open ScriptJ JetS
lemma baseF (A:Lid G I){V:ChartRatio G}(h:LocalRatio V): (draw (A.hat V) (penon A) (Chart.tangent G I)).s=1:= (by simp only [draw, A.hat_full h]; exact (penon A).empty ..)
lemma simply (A:Lid G I)(B:Lid G J){V:ChartRatio G}(hv:LocalRatio V)(q:ScriptJ (Keys G I))(h:q.B): (cradle p A B).pay V (q ∘ prL p G)= A.pay V q:=by
      let X:= cradle p A B; let μ:=Chart.tangent G U; let ν:= Chart.tangent G I; let π:= Chart.tangent G J; rw [X.cutOut hv (penon X) _ (penon_shape _),A.cutOut hv (penon A) q (penon_shape _)]
      let r:= draw (B.hat V) (penon B) π; let w:=draw (q*A.hat V) (penon A) ν; let s:= draw (A.hat V) (penon A) ν
      rw [show draw ((q ∘ prL p G)*X.hat V) (penon X) μ= r*w from ?_, show draw (X.hat V) (penon X) μ=r*s from ?_]; exact JetS.transfer _ _ _ (by unfold r; rw [baseF B hv];norm_num) (by unfold s; rw [baseF A hv];norm_num)
      · rw [mul_comm]; unfold r s; rw [← flurry p A B (A.hat V) (B.hat V) (A.hat_toll hv) (B.hat_toll hv)]; exact congr_arg (fun f=> draw f (penon X) μ) (funext (rime p A B hv))
      rw [mul_comm r w]; unfold r w; rw [← flurry p A B (q*A.hat V) (B.hat V) (height h (A.hat_toll hv)) (B.hat_toll hv)]; apply congr_arg (fun f=> draw f (penon X) μ); funext i; change q (prL p G i)* X.hat V i = (_* _)*_; rw [show X.hat V i= _ from rime p A B hv i]; ring
-- shortcut quota identical on eventually
lemma quotas (A B:Lid G I)(h:A.f=ᶠ[𝓝 0] B.f)(he:A.w=ᶠ[𝓝 0] B.w)(V:ChartRatio G)(x:ScriptJ (Keys G I)): A.pay V x=B.pay V x:=by
     have ht {f g:Keys G I→ℝ}(h:f=ᶠ[𝓝 0] g) (n:ℕ) (x:Keys G I): jet f n x=jet g n x:=by unfold jet; rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]
     have hu: warmer V A.w =ᶠ[𝓝 0] warmer V B.w:= he.mul Filter.EventuallyEq.rfl
     unfold Lid.pay Lid.capstone Lid.purse Lid.heat; rw [show kernel A.f = kernel B.f from funext fun i=> congr_arg Real.exp (congr_arg Neg.neg (ht h 2 i)), show Pawn.mold (warmer V A.w) 0= Pawn.mold (warmer V B.w) 0 from funext fun i=> JetS.eta _ _ (ht hu 0 i) (ht hu 1 i) (ht hu 2 i), show Pawn.mold A.f 2=Pawn.mold B.f 2 from funext fun i=> JetS.eta _ _ (ht h 2 i) (ht h 3 i) (ht h 4 i)]
end YM.OPE.Cascade.Pilot
