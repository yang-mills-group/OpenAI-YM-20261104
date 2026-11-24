import YM.WilsonCoeffUV.Stable.CalendarSupply
/-! # Actual ℓ1 moment currency for every presented Vote kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm Fountain PathCost Embroider.Canvas MeasureTheory
open scoped Topology BigOperators ContDiff ENNReal Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l j e k i m u:ℕ} {G:Gauge}{F:Labels.Frame G h} {P Q : ChamberTen G (Vote D) r} {A B:ℝ}
lemma certificate (p: Fruit 0 1 u P A): Keys_ P 0 u ((3+(r:ℝ))^u*A):=by
    choose f F hf he H using fun u=> issued (P u)
    refine ⟨f,fun i=>⟨F i,hf i⟩,H,?_⟩; simp_rw [he,zero_mul,Real.exp_zero,mul_one]; refine budget_minor (cap_scale p (show 0≤(3+(r:ℝ))^u by positivity)) (fun _=>mul_nonneg (by unfold ranging; positivity) (norm_nonneg _)) ?_; intro x; unfold hedge autumn; rw [one_mul, ← mul_assoc,←mul_pow]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by unfold ranging; positivity) (reachR x) _) (norm_nonneg _)
lemma redemption (p: Keys_ P 0 u A): Fruit 0 1 u P A:=by
    obtain ⟨f,h,H,hv⟩:=p; simp only [zero_mul,Real.exp_zero,mul_one] at hv
    refine budget_minor hv (fun _=>mul_nonneg (hedge_nn zero_le_one _) (norm_nonneg _)) ?_; intro x; haveI : IsFiniteMeasure (f x):= (h x).2
    have hp : ‖P x‖≤ (f x).real Set.univ:=by
        apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg; intro v; obtain ⟨q,rfl⟩:= submitted v; rw [H,mul_comm]; apply norm_integral_le_of_norm_le_const; refine Eventually.of_forall fun a=>?_;
        unfold balk; rw [norm_mul, pointV,one_mul]; exact creased q (Nat.le_of_lt_succ a.1.2.1.isLt) _ _
    unfold hedge autumn; rw [one_mul]; apply mul_le_mul _ hp (norm_nonneg _) (by unfold ranging; positivity); gcongr; change 1+ (port_d 0 x:ℝ) ≤3+ _
    have he i:(Bank.terrain.gap 0 (x i).1:ℝ)=size (x i).1:= congr_arg Nat.cast (show size ((x i).1-0)= size (x i).1 by rw [sub_zero]); simp_rw [he,←Nat.cast_sum]; exact add_le_add (by norm_num) (Nat.cast_le.mpr (vessels x))
end YM.WilsonCoeffUV.Shard
