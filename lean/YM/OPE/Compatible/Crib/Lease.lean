import YM.OPE.Compatible.Crib.Brush
/-! # Underwrite rank. C mass analytic or pol. global Author Minister. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n c f:Side} {b i k r m:ℕ}{t C s u z B v ε:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph
open Spells
variable (S:StepData c f)(H:Odd S.ratio.count.val)(o:Site f)
local notation "Fθ"=> forest S.ratio H
local notation "Yr"=>AxisChart G Fθ
local notation "Ix"=> crux S H o b
local notation "Yσ"=> Libra.Keys G (Ix:Type)
abbrev RentT (x r:ℝ):=10*r*x^3
private lemma coverJ {x r:ℝ}(hx:1 ≤x)(hr:0≤ r): Jfare x r≤ RentT x r ∧ Jfair x r*x≤ RentT x r:=by
       have he:r≤r*x:= le_mul_of_one_le_right hr hx; have hv:r*x ≤r*x^2:= mul_le_mul_of_nonneg_left (le_self_pow₀ hx (by omega)) hr; have ht:r*x^2 ≤r*x^3:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by omega)) hr; unfold Jfare Jfair RentT; constructor <;> linarith only [he,hv,ht,hr]
variable {p:Scoop G b→ℝ}
section
noncomputable abbrev Ufee (G:Gauge)(b k:ℕ)(s:ℝ):= 10*(s*(2*LargeK G b)^k)*LargeK G b^3
abbrev Xs(k:ℕ):=3*k+9
private lemma rent_Q {r:ℝ} {C:ℝ}(h:1≤C)(ht:0≤ t)(hr:0≤r)(k:ℕ):
            let x:=C*(1+t)^ (3:ℕ); RentT x (r*(1+x)^k)≤ (10*(r*(2*C)^k)*C^(3:ℕ))*(1+t)^Xs k:=by
                 intro x; let k':=C; let v:= 1+t; have he:1≤v:=by unfold v; linarith only [ht] --
                 have hx:1 ≤x:=one_le_mul_of_one_le_of_one_le h (one_le_pow₀ he); apply le_trans (b:=10*(r*(2*x)^k)*x^3) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith only[hx]) _) hr) (by norm_num)) (by positivity))
                 apply le_of_eq; change 10*(r* (2*(k'*v^(3:ℕ)))^k)*(k'*v^(3:ℕ))^3= 10*(r*(2*k')^k)*k'^(3:ℕ)*v^(3*k+9); rw [←mul_assoc 2, mul_pow _ (v^3),pow_add, pow_mul]; ring
lemma rent_X {r:ℝ} (G:Gauge)(ht:0≤ t)(hr:0≤r)(b k:ℕ):
            let x:=LargeK G b*(1+t)^ (3:ℕ); RentT x (r*(1+x)^k)≤ Ufee G b k r*(1+t)^Xs k:= rent_Q (bigK G b) ht hr k
end
-- Lipschitz on box t≥1 sufficient for later.
structure RubricT {X:Type}[NormedAddCommGroup X] (p:X→Token)(s:ℝ)(k:ℕ):Prop where
       pos : 0≤ s
       earn {t:ℝ}(ht:0≤t)(x:X)(hx:‖x‖≤ t) : scope (p x) (s*(1+t)^k)
       Ease {t:ℝ}(ht:1≤t)(x y:X)(hx:‖x‖ ≤ t)(hy:‖y‖ ≤ t): fuel (p x) (p y) (s*(1+t)^k * ‖x-y‖)
lemma RubricT.spikes {X:Type}[NormedAddCommGroup X]{p:X→Token}(h:RubricT p s k)(j:Phase) : Continuous (fun x=>(p x).seq j.val):=by
       apply continuous_iff_continuousAt.mpr; intro i; let t:=1+‖i‖; have ht:1≤t:= le_add_of_nonneg_right (norm_nonneg _); let f(x:X):=(p x).seq j.val; have he:0≤ s*(1+t)^k:=mul_nonneg h.pos (by positivity); let r:NNReal:= ⟨_,he⟩; have hp:LipschitzOnWith r f (closedBall 0 t):=by
             rw [lipschitzOnWith_iff_dist_le_mul]; intro x hx y hy; rw [dist_eq_norm,dist_eq_norm]; exact h.Ease ht _ _ (mem_closedBall_zero_iff.mp hx) (mem_closedBall_zero_iff.mp hy) j
       have hv:i∈ ball 0 t := by rw [mem_ball_zero_iff]; unfold t; linarith
       exact (hp.continuousOn i (ball_subset_closedBall hv)).continuousAt (mem_of_superset (isOpen_ball.mem_nhds hv) ball_subset_closedBall)
lemma Safe (hp:Velvet p s k): RubricT (fun x:Yσ=> Autum p (gam S H o b x)) (Ufee G b k s) (Xs k):=by
       have he:0 ≤ s:=hp.pos; have hx:=bigK G b
       refine ⟨(by unfold Ufee; positivity),fun {t} ht x hz i =>?_,fun {t} ht x y hX hY i=>?_⟩
       · have h:= (VFμ G b ht).1; exact (Approve S H o hp x hz h i).trans (le_trans (b:=RentT _ _) (coverJ (one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ (le_add_of_nonneg_right ht))) (mul_nonneg he (by positivity))).1 (rent_X G ht he b k))
       obtain ⟨hC,hS⟩:= VFμ G b (zero_le_one.trans ht); apply (Appeal S H o hp x y hX hY ht hC hS i).trans; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact (coverJ (one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ (le_add_of_nonneg_right (zero_le_one.trans ht)))) (mul_nonneg he (by positivity))).2.trans (rent_X G (zero_le_one.trans ht) he b k)
end YM.OPE.Crown
