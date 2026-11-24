import YM.RGComparison01.Ward.Cabri
import YM.Next.FOUNDATIONS.Regular

/-!
# Replacing the gauge-free coordinate stencil by the prescribed image

An extra adapter to Fruition: the numerator/Palm coefficient at a given
period lives upstairs in Cartesian positions. Cannot just compare to an
output economic proposition in those coordinates as if a well-defined local
gauge observable. Evaluate prescribed coefficients on rooted legs and
integrate. This output itself is not yet required to be a calibrated Fk
stencil for reuse over many steps.

Regularity and Brush integral technology, concrete chart costs come later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ward
open Function Filter MeasureTheory RG Pressure Pressure.Stores Pressure.Tube Gauge Wilson
open Lattice Next.Fluctuations Push Push.Uniform Push.AbsoluteSums Precision Exterior
open Work.E03 Work.F03 ConnectedActivityE6 SliceRows Blaze Brush
open scoped Matrix.Norms.Frobenius Topology ContDiff InnerProductSpace Classical BigOperators
variable {G:Gauge}{c:Side}{j k :ℕ}
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u d:ℝ}
lemma pour (F:E→ G.El → ℝ) (x:E)
    (h:∀ᶠ y in 𝓝 x,∀ z:G.El,Brush k u d (fun p=> F p z) y)(hm:∀ᶠ y in 𝓝 x,Measurable (F y)) : Brush k u d (fun y=> ∫ z,F y z ∂G.probHaar) x:=by
   let Q :ℝ:=u*(1+d)^k
   refine ((Meristem.points (j:=k) F G.probHaar ?_ hm).1.buds (fun _=>u) (integrable_const u) (h.self_of_nhds (1:G.El) |>.pos) (by simp) (ae_of_all _ h.self_of_nhds))
   use fun _=> Q
   exact ⟨integrable_const _, h.mono (fun _ h z=> (h z).trim)⟩
end
namespace Visage
variable (C:Visage G k)
variable (o:Site c) (P:Positions (Uniform.Primary c G)→ℝ)

def chant (V:Config G c):=∫ z,P (C.encode o V z) ∂G.probHaar
lemma chant_invar : GaugeInvariant (C.chant o P):= by
   intro a U; unfold chant; simp_rw [C.other]; exact integral_mul_right_eq_self (fun i=> P (C.encode o U i)) _

variable (he: ContDiff ℝ (↑k:WithTop ℕ∞) P)
include he
lemma listens : Measurable (C.chant o P):=by
   have h := he.continuous.comp (C.drape o)
   exact (h.measurable.stronglyMeasurable.integral_prod_right' (ν:=G.probHaar)).measurable -- check args
lemma builds (U:Config G c): ContDiffAt ℝ (↑k:WithTop ℕ∞) (C.chant o P ∘ increment U) 0:=by
   let Y:=increment U
   obtain ⟨d,h⟩:∃ d:ℝ,∀ᶠ x in 𝓝 (0:Directions G c), Mode Y x k d:=by
     obtain ⟨v,-,hv⟩:= Blaze.expCost G k 1
     refine ⟨(1+(k.factorial:ℝ)*v)* ((1+1)*1),?_⟩; filter_upwards [Metric.closedBall_mem_nhds (0:Directions G c) zero_lt_one] with x hx
     have hh : ‖x‖≤1:=by simpa using (Metric.mem_closedBall.mp hx)
     exact fromLogL (fun i:Directions G c=> i) (Brush.linearB (ContinuousLinearMap.id ℝ (Directions G c)) hh (by simpa using ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=Directions G c)) zero_le_one) 1 zero_lt_one hv (fun i=> (norm_le_pi_norm _ _).trans hh) U
   let T:ℝ:=(1+royalty G)*longitude d c.val (royalty G)
   let C':= C.prices
   letI : ProperSpace (Positions (Uniform.Primary c G)):= FiniteDimensional.proper ℝ _
   obtain ⟨b,-,hf⟩:= Brush.compact (isCompact_closedBall (0:Positions (Uniform.Primary c G)) C') (fun i _=>he.contDiffAt)
   have hhs : ∀ᶠ x in 𝓝 0, ∀ u:G.El,Brush k (k.factorial*b) ((1+C')*T) (fun i=> P (C.encode o (Y i) u)) x :=by
      filter_upwards [h] with x hx u
      have ha := (C.reckon o Y x u hx); exact ha.pine (hf _ (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact ha.bound)))
   exact (pour (k:=k) (fun i u=>P (C.encode o (Y i) u)) 0 hhs (Eventually.of_forall fun i=> (he.continuous.comp ((C.drape o).comp (continuous_const.prodMk continuous_id))).measurable)).smooth
lemma fitted (P':BudgetPoint)(hj:P'.order ≤ k) : P'.Regular Finset.univ (C.chant o P):=by
   have ht V : ContDiffAt ℝ (↑P'.order:WithTop ℕ∞) (C.chant o P ∘ increment V) 0 := (C.builds o P he V).of_le (by exact_mod_cast hj)
   refine ⟨fun V U hh=>?_, C.listens o P he,C.chant_invar o P,fun V _ => ht V, fun V _ A _ h=> Next.Foundations.left_has A h (ht V)⟩
   exact congr_arg (C.chant o P) (funext fun i=> hh i (Finset.mem_univ _) (Finset.mem_univ _))
end Visage
end YM.RGComparison01.Ward
