import YM.RG06.Weak.Shift
import Mathlib.Analysis.Calculus.Taylor
/-!
# Actual interpretation of `DeSlot`

Two-sided through a punctured real neighborhood of zero, with every
other argument held fixed. No uniformity even over bounded fields
claimed here. Use the little-o real Taylor theorem on a small open
interval where `ContDiffAt` supplies `ContDiffOn` *at the requested
finite order*. We don't need analyticity or a common C∞ neighborhood.
Upgrade to the `=O(t^(r+1))` statement by actually taking one
additional term (and paying its fixed coefficient). These estimates
are for bare-stencil kinematics, NOT full qlocal or correlation/report
estimates (those have other derivative, mask, integration,
normalization and Gram costs).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Weak
open scoped Topology ContDiff Classical BigOperators
open Finset Function Filter Set Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of the real line series up to and including r. -/
def report (p : ℕ→E) (r : ℕ) (t : ℝ) := ∑ i∈Finset.range (r+1), t^i • p i

theorem Writes.asReport {f : ℝ→ E} {F : ℕ→E} (h : Writes f F)(r : ℕ) : (f - report F r)=o[𝓝 0] fun t=> t^r := by
  have hc := (h.nice r).eventually (by simp)
  obtain ⟨b,hb,ht⟩:=Metric.eventually_nhds_iff.mp hc
  let U := Metric.ball (0:ℝ) b
  have hi : (0:ℝ)∈U:=Metric.mem_ball_self hb
  have hf : ContDiffOn ℝ (r:ℕ) f U:= fun x hx=>(ht hx).contDiffWithinAt
  have hy := taylor_isLittleO (x₀:=(0:ℝ)) (n:=r) (convex_ball ..) hi hf
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ hb)] at hy
  have he (i) : iteratedDerivWithin i f U 0=iteratedDeriv i f 0:= by
    simp_rw [← iteratedDerivWithin_univ,iteratedDerivWithin_eq_iteratedFDerivWithin]
    rw [← univ_inter U,iteratedFDerivWithin_inter_open Metric.isOpen_ball hi]
  have hR (x):taylorWithinEval f r U 0 x= report F r x:=by
    rw [taylor_within_apply,report]; simp_rw [sub_zero,he,mul_comm _ (x^_),mul_smul,h.coeff]
  unfold U at hR
  change (fun x=> f x-report F r x)=o[_] _; simpa only [sub_zero,hR] using hy

/- Keep one extra order for a concrete bound at order r. The constant
and onset here may depend on EVERYTHING, including field direction. -/
theorem Writes.bound {f : ℝ→E}{F : ℕ→E}(h : Writes f F)(r : ℕ): (f-report F r)=O[𝓝 0] fun t=>t^(r+1):=by
  have he:= (h.asReport (r+1)).def (c:=1) one_pos
  apply IsBigO.of_bound (1+‖F (r+1)‖)
  filter_upwards [he] with t ht
  have hX : f t - report F r t= (f-report F (r+1)) t+t^(r+1)• F (r+1):=by unfold report; rw [Pi.sub_apply,Finset.sum_range_succ _ (r+1)]; abel
  rw [Pi.sub_apply,hX]; refine (norm_add_le ..).trans ((add_le_add_left ht _).trans_eq ?_); rw [norm_smul]; ring

/-- Bare divided operator equality as punctured weak-asymptotic
coefficient claim in addition to the ordinary coefficient statement.
Positive or negative t, NO analytic/log branch choice. -/
theorem DeSlot.punctured {l : ℕ}{v : ℝ→ℂ}{p : PowerSeries ℂ} (h : DeSlot l v p) (r : ℕ):
    ((fun t:ℝ=> (t⁻¹)^l • v t)-report (fun i=>PowerSeries.coeff i p) r)
      =O[𝓝[≠] (0:ℝ)] fun t=> t^(r+1):=by
  have he:= Writes.bound h (l+r)
  obtain ⟨C,hC⟩:= he.isBigOWith
  apply IsBigO.of_bound C
  let B:= fun i=> PowerSeries.coeff i (p * PowerSeries.X^l)
  let F:= fun i=> PowerSeries.coeff i p
  have hx: ∀ᶠ t in 𝓝[≠] (0:ℝ), ‖(v-report B (l+r)) t‖ ≤ C * ‖t^(l+r+1)‖:= hC.bound.filter_mono nhdsWithin_le_nhds
  have ht: ∀ᶠ t in 𝓝[≠] (0:ℝ),t≠0:=self_mem_nhdsWithin
  filter_upwards [hx,ht] with t hx ht
  have hr : report B (l+r) t=t^l • report F r t:=by
    unfold report
    rw [Nat.add_assoc,Finset.sum_range_add, Finset.sum_eq_zero (s:=Finset.range l) (by
      intro i hi; have he: ¬ (l ≤ i) :=Nat.not_le.mpr (Finset.mem_range.mp hi);simp [B,PowerSeries.coeff_mul_X_pow',he]),zero_add,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i hi=>by simp [B,F,PowerSeries.coeff_mul_X_pow',pow_add,mul_assoc]
  change ‖(t⁻¹)^l • v t-report F r t‖ ≤ _
  rw [show (t⁻¹)^l • v t-report F r t=(t⁻¹)^l • (v-report B (l+r)) t by rw [Pi.sub_apply,hr,smul_sub, smul_smul, ←mul_pow,inv_mul_cancel₀ ht,one_pow,one_smul],norm_smul]
  grw [hx]; rw [Nat.add_assoc,pow_add,norm_mul,norm_pow,norm_pow,norm_inv];have hxN : ‖t‖≠0:= (norm_pos_iff.mpr ht).ne'; rw [inv_pow]; field_simp; rfl

end YM.RG06.Weak
