import YM.GradedFar.Funds
import YM.OPE.Log.Uniform
/-!
# QScale, polynomial prices from iteration of fixed-neighbor prices. No shortcut to polynomial Z via a raw discrepancy.

We give additional retailer proofs from *compact* (G.1) prices. This file prepares log-length budget for
(G.2) use. Use dyadic steps at the true H frame, both resources eventually small. Not claiming
in this step to discharge the compact physical prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
namespace Dyadic
open Filter Finset Function Set Spec Table Extraction
open Trace.Pilot PhysMS OPE OPE.Orbits OPE.Log
open FVA2 XSpace XSpace.Normalize
open scoped Topology BigOperators Classical
variable {G:Gauge} (hG:G.Simple)
local notation "g" => strength G
include hG
lemma buys_log (C:ℝ)(hC:0≤C):∃ p:ℕ,∀ᶠ r:ℝ in trail, 1+C*g r^2 ≤ (badge (r/2)/badge r)^p := by
  obtain ⟨p,hp⟩:= exists_nat_gt (2*C*G.slopeConstant⁻¹/(Real.log 2))
  refine ⟨p,?_⟩
  have ht:0<Real.log 2:=Real.log_pos (by norm_num)
  filter_upwards [strength_scale hG,to_log_zoom.eventually_ge_atTop 1,self_mem_nhdsWithin] with r hv hz (hr:0<r)
  have h0 : badge r=1+LogV r:= by unfold badge run LogV; rw [Real.log_inv]
  have h1 : 0 < badge r:= by linarith
  have h2 : badge (r/2) = badge r+Real.log 2:=by unfold badge run; rw [Real.log_div hr.ne' (by norm_num)]; ring
  rw [h2,add_div,div_self h1.ne']
  have hb : C*g r^2 ≤ (p:ℝ)*(Real.log 2/badge r):= by
    rw [← mul_div_assoc]; apply (le_div_iff₀ h1).mpr; apply le_trans _ ((div_le_iff₀ ht).mp hp.le)
    calc _≤ C*g r^2*(2*LogV r):= mul_le_mul_of_nonneg_left (by linarith) (by positivity)
         _ = _:=by rw [← hv]; ring
  exact (add_le_add (le_refl 1) hb).trans (one_add_mul_le_pow (by linarith only [div_pos ht h1]) p)

/-- If each admissible power budget for positive late r buys one at every `r/2 ≤ s ≤ r` with price
scaled by `1+C*g(r)^2`, then the actual account costs at most a polynomial in the log length.
This lemma is independent of including an "$O(1)" goal on the physical states. -/
lemma iterate (R:ℝ→ℝ→Prop) (grows:∀ {r s b}, R r s→ s ≤ b→R r b)(existsC:∀ r>0,∃ b:ℝ,0≤b ∧ R r b)
    {C:ℝ}(hC:0≤C) (h:∀ᶠ r:ℝ in trail,∀ s:ℝ,r/2 ≤ s → s ≤  r → ∀ b:ℝ,0≤b→ R r b→ R s ((1+C*g r^2)*b)) :
    ∃ A:ℝ,0≤A ∧ ∃ p:ℕ, ∀ᶠ r:ℝ in trail, R r (A*badge r^p) := by
  obtain ⟨p,hp⟩:=buys_log hG C hC
  have he: Tendsto (fun r=>C*g r^2) trail (𝓝 0):=by
    simpa using
      ((Coupling.conforms hG (strength_coupling hG)).pow 2).const_mul C
  obtain ⟨a,ha,H⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp (h.and (hp.and ((he.eventually_le_const zero_lt_one).and
    ((ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds))))
  obtain ⟨b,hb,B⟩:=existsC a ha
  let T (n:ℕ):=a*(1/2:ℝ)^n
  have hs(n): T n∈Set.Ioc (0:ℝ) a:= ⟨mul_pos ha (pow_pos (by norm_num) _),
    mul_le_of_le_one_right (le_of_lt ha) (pow_le_one₀ (by norm_num) (by norm_num) (n:=n))⟩
  have ht(n:ℕ):T (n+1) = T n/2:=by unfold T; rw [pow_succ]; ring
  have hB x (hx:x∈Set.Ioc (0:ℝ) a):1≤badge x:= le_add_of_nonneg_right
    (neg_nonneg.mpr (Real.log_nonpos hx.1.le (H hx).2.2.2))
  have Ht (n):R (T n) (b*badge (T n)^p):= by
    induction n with
    | zero => rw [show T 0=a by simp [T]]; apply grows B; exact le_mul_of_one_le_right hb (one_le_pow₀ (hB a ⟨ha,le_rfl⟩))
    | succ n ih=>
      have hn := H (hs n); have hk:= zero_lt_one.trans_le (hB _ (hs n)); apply grows (hn.1 (T (n+1)) (ht n).ge (by rw [ht]; exact half_le_self (hs n).1.le) _ (by positivity) ih); calc
        _≤ (badge (T n/2)/badge (T n))^p*(b*badge (T n)^p):= mul_le_mul_of_nonneg_right hn.2.1 (by positivity)
        _ = _:= by rw [ht n,div_pow]; field_simp
  refine ⟨2*b,by positivity,p, mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨a,ha,?_⟩⟩
  intro x (hz:x∈Set.Ioc (0:ℝ) a)
  obtain ⟨n,hn,hx⟩:= exists_nat_pow_near_of_lt_one (div_pos hz.1 ha) ((div_le_one ha).mpr hz.2)
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  have hv:T n/2≤x := by rw [← ht n]; unfold T; rw [mul_comm]; exact ((lt_div_iff₀ ha).1 hn).le
  have hq:x≤T n:= le_trans ((div_le_iff₀ ha).1 hx) (mul_comm ..).le
  have H:= H (hs n); have hp0:=zero_lt_one.trans_le (hB _ (hs n)); apply grows (H.1 x hv hq _ (by positivity) (Ht n))
  have hb': badge (T n) ≤ badge x:= add_le_add (le_refl 1) (neg_le_neg (Real.log_le_log hz.1 hq))
  calc _ ≤ (1+1)*(b*badge x^p):= by gcongr; exact H.2.2.1
       _ = _:=by ring
end Dyadic
end YM.Integration.GradedFar
