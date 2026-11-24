import YM.Integration.WilsonThermometerWeakSignedJets

/-! Each smooth coefficient of the independently prescribed finite common-frame
expansion is paid on a fixed compact collar before the coupling tends to zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCoefficientTail
open Spec Set Filter WilsonThermometerWeakValueRecovery
open scoped Classical Topology ContDiff BigOperators
variable {n:ℕ}{A:Type*}{l:Filter A}{U:Set (Points n)}

def part (coeff:ℕ→Points n→ℂ)(S:Finset ℕ)(t:ℝ):Points n→ℂ:=
  fun x=>∑a∈S,t^a • coeff a x

theorem smooth (c:ℕ→Points n→ℂ)(S:Finset ℕ)(t:ℝ)(legal:∀a∈S,ContDiffOn ℝ ∞ (c a) U):
    ContDiffOn ℝ ∞ (part c S t) U:=
  ContDiffOn.sum fun a ha=>(show ContDiffOn ℝ ∞ (fun _:Points n=>t^a) U from contDiffOn_const).smul (legal a ha)

theorem original (openU:IsOpen U)(c:ℕ→Points n→ℂ)(S:Finset ℕ)(g:A→ℝ)(j p:ℕ)
    (legal:∀a∈S,ContDiffOn ℝ ∞ (c a) U)(starts:∀a∈S,p≤a)
    (tiny:Tendsto g l (𝓝 0))(positive:∀ᶠr in l,0≤g r):
    Price l U (fun r=>part c S (g r)) g p j:=by
  intro K compact safe
  have face (i:ℕ)(hi:i∈S) : ∃B,0≤B ∧ ∀x∈K,‖iteratedFDeriv ℝ j (c i) x‖≤B:=by
    obtain ⟨B,paid⟩:=compact.exists_bound_of_continuousOn (f:=iteratedFDeriv ℝ j (c i))
      (fun x hx=>(((legal i hi x (safe hx)).contDiffAt (openU.mem_nhds (safe hx))).continuousAt_iteratedFDeriv
        (k:=j) (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)
    exact ⟨max 0 B,le_max_left ..,fun x hx=>(paid x hx).trans (le_max_right ..)⟩
  choose B pos fees using face
  let wage:=fun (a:ℕ)=>if ha:a∈S then B a ha else 0
  have wage0 (a:ℕ)(ha:a∈S):0≤wage a:=by simpa only [wage,dif_pos ha] using pos a ha
  refine ⟨∑a∈S,wage a,Finset.sum_nonneg wage0,?_⟩
  filter_upwards [positive,tiny.eventually_lt_const zero_lt_one] with r gp gu x hx
  have placed (a:ℕ)(ha:a∈S):ContDiffAt ℝ j (c a) x:=
    (((legal a ha) x (safe hx)).contDiffAt (openU.mem_nhds (safe hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  unfold part
  rw [iteratedFDeriv_fun_sum_apply (f:=fun (a:ℕ)(v:Points n)=>g r^a • c a v) (fun a ha=>(show ContDiffAt ℝ j (fun _:Points n=>g r^a) x from contDiffAt_const).smul (placed a ha)),Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [iteratedFDeriv_const_smul_apply' (placed a ha),norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg gp _),mul_comm]
  exact mul_le_mul (by simpa only [wage,dif_pos ha] using fees a ha x hx)
    (pow_le_pow_of_le_one gp gu.le (starts a ha)) (pow_nonneg gp _) (wage0 a ha)

end YM.Integration.WilsonThermometerWeakCoefficientTail
end
