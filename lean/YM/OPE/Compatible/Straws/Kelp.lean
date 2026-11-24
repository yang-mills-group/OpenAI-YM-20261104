import YM.OPE.Compatible.Gables.Brac
/-!
# Jet calculus along small paths of coarse parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
open Radial ScriptJ JetS
private lemma expK (x : ℝ)(j : ℕ) : ‖Real.exp x - ∑ i∈Finset.range (j+1),(i.factorial:ℝ)⁻¹*x^i‖ ≤ ‖x‖^(j+1) * Real.exp ‖x‖ := by
  let g : ℝ → ℝ := fun t=> Real.exp (x*t)
  have hsm : ContDiff ℝ ∞ g := (Real.contDiff_exp).comp (contDiff_const.mul contDiff_id)
  have hy (i : ℕ)(t)(ht : t∈Icc (0:ℝ) 1) : iteratedDerivWithin i g (Icc 0 1) t=x^i*Real.exp (x*t):=by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) ((hsm.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt) ht]; unfold g; rw [iteratedDeriv_exp_const_mul]
  have hh : ContDiffOn ℝ ((j:WithTop ℕ∞)+1) g (Icc 0 1):=by rw [← Nat.cast_one (R:=WithTop ℕ∞),←Nat.cast_add];exact hsm.of_le (by exact WithTop.coe_le_coe.mpr le_top)|>.contDiffOn
  have h := taylor_mean_remainder_bound (n:=j) (x:=1) (C:=‖x‖^(j+1) * Real.exp ‖x‖) (a:=0) (b:=1) zero_le_one hh (right_mem_Icc.mpr zero_le_one) ?_; swap
  · intro y hy'; obtain ⟨hd,hu⟩:=hy'
    rw [hy _ _ ⟨hd,hu⟩,norm_mul,norm_pow,Real.norm_eq_abs (Real.exp ..), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show x*y≤‖x‖ by rw [Real.norm_eq_abs];rcases abs_cases x with ⟨eq,_⟩|⟨eq,_⟩ <;> rw [eq] <;> nlinarith)) (by positivity)
  have e : taylorWithinEval g j (Icc 0 1) 0 1 = ∑ i∈Finset.range (j+1),(i.factorial:ℝ)⁻¹*x^i := by
    rw [taylor_within_apply]; apply Finset.sum_congr rfl fun i _ => ?_
    rw [hy _ _ (left_mem_Icc.mpr zero_le_one)];simp
  rw [e] at h; dsimp [g] at h; rw [mul_one,sub_zero,one_pow,mul_one] at h
  exact h.trans <| div_le_self (by positivity) (by exact_mod_cast j.factorial_pos)

namespace Reads
variable {f h:ℝ→E}{s k:JetS E}
lemma tours (K:E→L[ℝ] F)(H:Reads f k):Reads (K∘f) ⟨K k.s,K k.l,K k.h⟩:=by
    unfold Reads; rw [show K∘ f- JetS.atK _ = K∘(f-k.atK) from funext fun i=>by simp [atK]]; exact (K.isBigO_comp ..).trans H
lemma sumO {k':JetS ℝ} (c:ℝ→ℝ)(x:ℝ)(hc:Reads c k')(y: E)(hx:k'.s=x):Reads (fun t=> c t • y) ⟨x • y,k'.l • y,k'.h • y⟩:=hx ▸ tours ((ContinuousLinearMap.id ℝ ℝ).smulRight y) hc
variable {u w:ℝ→ℝ}{p:JetS ℝ}
protected lemma clash (h: Reads u p)(hv:(u-w) =O[Lf](gradeP 3)): Reads w p:= by
    unfold Reads; rw [show w-p.atK=(u-p.atK)-(u-w) by ring]; exact h.sub hv -- resolves name
lemma nopay (h:Reads u p)(hp:p.s=0) : u=O[Lf](gradeP 1):=by
    have hv:= h.origin 0 (by decide); unfold Tested.peval Zone.eval at hv; simp only [zero_add,Finset.sum_range_one, JetS.seq,pow_zero,one_smul,hp] at hv; simpa using (show (u-0) =O[Lf](gradeP 1) from isTariff.mpr hv)
abbrev pluck (p:JetS ℝ):JetS ℝ:=⟨1,p.l,p.h+p.l^2/2⟩
def sprout (p:JetS ℝ):JetS ℝ:= plainJ (Real.exp p.s)*pluck p
lemma expHop (h:Reads u p)(hp:p.s=0): Reads (Real.exp ∘ u) (pluck p):=by
     let e:= Real.exp ∘ u; let f:= (1+u)+(fun t=> (2:ℝ)⁻¹)* (u*u)
     have hv: Reads f (1+p+(plainJ _)*(p*p)):= ((Reads.constants (1:ℝ)).sum h).sum ((Reads.constants (2:ℝ)⁻¹).pile (h.pile h)); rw [show 1+p+ _= pluck p from (show 1+p+(plainJ (2:ℝ)⁻¹)*(p*p)= pluck p from by apply JetS.eta <;>simp [hp]; ring )] at hv
     apply hv.clash
     rw [←neg_sub]; apply IsBigO.neg_left; let a(t):= ‖u t‖; let P(t:ℝ):= Real.exp (a t)
     have hA: a=O[Lf](gradeP 1):= (h.nopay hp).norm_left
     have hx:Tendsto P Lf (𝓝 (Real.exp ‖p.s‖)):= Real.continuous_exp.continuousAt.tendsto.comp ((limit h).norm)
     have hb: (fun t=> a t^3*P t)=O[Lf](gradeP 3):=by convert! (hA.pow 3).mul (hx.isBigO_one ℝ) using 2; simp
     apply IsBigO.trans (isBigO_of_le _ fun x=> ?_) hb; let t:=u x; rw [Real.norm_eq_abs (a x^3*P x), abs_of_nonneg (by unfold a P; positivity)]; -- should nonneg
     convert! expK (u x) 2 using 1; dsimp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]; norm_num [Finset.sum_range_succ,f]; ring_nf
lemma roofer (h:Reads u p): Reads (Real.exp ∘ u) (sprout p):=by
     let a:= plainJ p.s; let v:ℝ→ℝ:= fun _=>p.s; have ht : Reads (u-v) (p-a):= h.minus (Reads.constants _); have hs:= ht.expHop (by simp [sub_eq_add_neg,show (-a).s= -p.s from rfl]); rw [show pluck (p-a)= pluck p from by unfold pluck;simp [sub_eq_add_neg,show (-a).l=0 from by change -(0:ℝ)=0;simp,show (-a).h=0 from by change -(0:ℝ)=0;simp]] at hs; apply ((Reads.constants (Real.exp p.s)).pile hs).cong; filter_upwards with i; change Real.exp (u i)=Real.exp p.s* Real.exp (u i-p.s); rw [← Real.exp_add]; ring_nf
end Reads
end YM.OPE.Libra
