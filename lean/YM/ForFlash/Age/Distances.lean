import YM.SignedWilsonExpansion.Fire.Timer
/-! Choose a pair of growing report sizes. -/ 
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Fire
open Function Filter Asymptotics Gauge Wilson RG Real
open Trace.Pilot Purchases UVClock Schedules WilsonCoeffUV.Bank PathCost
open Commission Purchases.HalfRoof.Minty
open scoped Classical BigOperators Topology
variable {G:Gauge} {ι : Type} (K:Levels G) (h:G.Simple)
namespace RoadForFlash
variable {L:Filter ι}{r:ι→ℝ}{w:ℝ}
local notation "Bk" => (cck G∘r)
/-- minimum length, to obtain enough rounding precision directly -/
abbrev spare (G:Gauge)(w:ℝ)(r:ι→ℝ): ι→ℝ:= r*payD (cck G∘r) (-w)
local notation "r₀" => spare G w r
include h
lemma tends (hr:Tendsto r L trail)(hw:0<w): Tendsto (spare G w r) L trail:= tendsto_nhdsWithin_iff.mpr (by
  refine ⟨?_, (hr.eventually self_mem_nhdsWithin).mono fun i hi=> mul_pos (show 0<r i from hi) (pay_pos ..) ⟩
  change Tendsto (fun i=> r i * payD (βClock G r) (-w) i) L _; simpa only [mul_zero] using (hr.mono_right nhdsWithin_le_nhds).mul (payD_cuts (radius_clock h hr) (neg_lt_zero.mpr hw)))
lemma shrink₁ (hr:Tendsto r L trail)(hw:0<w){d:ℝ}(hd:0<d) : spare G w r ≤ᶠ[L] fun i=> d*r i:=by
    filter_upwards [ (payD_cuts (B:=Bk) (radius_clock h hr) (neg_lt_zero.mpr hw)).eventually_le_const hd,hr.eventually self_mem_nhdsWithin] with i hi hp
    change r i * payD Bk (-w) i ≤ d*r i
    rw [mul_comm d]
    exact mul_le_mul_of_nonneg_left hi (show 0<r i from hp).le
lemma shrink (hr:Tendsto r L trail)(hw:0<w): spare G w r ≤ᶠ[L] r:= by
    apply (shrink₁ h hr hw zero_lt_one).trans
    simp only [one_mul,EventuallyLE.rfl]
lemma audience {Z:ℝ→ℝ}{a:ℝ}{n:ℕ}(hr:Tendsto r L trail)(hw:0<w)(hc:Coupling G Z)(hi:4*(a+w) ≤ n): (r*payD (cck G ∘ r) a) ≤ᶠ[L] fun i=> spare G w r i*(Z (spare G w r i))⁻¹^n:=by
    let x:=spare G w r
    have ht:= tends h hr hw
    let A:ι→ℝ:= payD Bk
      (1/4)
    have eq: payD Bk (-1/2)=(payD Bk (-(1/4)))^2:= by rw [←payD_pow]; congr 1; norm_num
    filter_upwards [shrink h hr hw, owns_clock h ht hc, ht.eventually hc.positive, hr.eventually self_mem_nhdsWithin,
       ( radius_clock h hr ).eventually_gt_atTop 0, payD_fee (B:=Bk) (radius_clock h hr) (show a ≤ -w + (n:ℝ)*(1/4) by linarith)] with i hi hZ hp hr hY hl
    have hX:0<x i:= mul_pos (show 0<r i from hr) (pay_pos ..)
    have he:0<Z (x i):= hp
    have hv: Bk i ≤ cck G (x i):=by
       exact mul_le_mul_of_nonneg_left (Real.log_le_log (inv_pos.mpr (show 0<r i from hr)) (inv_anti₀ hX hi)) (Gauge.slopeConstant_pos h).le
    have hu: payD (cck G∘x) (-1/2) i ≤ payD Bk (-1/2) i:= by exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.log_le_log hY hv) (by norm_num:(-1:ℝ)/2≤0))
    have hz: Z (x i) ≤ payD Bk (-(1/4)) i := le_of_pow_le_pow_left₀ (by norm_num:2 ≠ 0) (pay_pos ..|>.le) (by
         have hm:Z (x i)^2≤payD Bk (-1/2) i:=le_trans hZ hu
         rw[eq] at hm; exact hm)
    have hx:A i≤ (Z (x i))⁻¹:=by
         rw[payD_inv] at hz
         exact (inv_inv (A i)) ▸ inv_anti₀ he hz
    change r i * payD Bk a i≤ (r i * payD Bk (-w) i)* (Z (x i))⁻¹^n
    rw[mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (show 0<r i from hr).le
    apply le_trans hl
    change payD Bk (-w+n*(1/4)) i ≤ _
    rw [payD_add,payD_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pay_pos (B:=Bk) ..|>.le) hx _) (pay_pos ..|>.le)
end RoadForFlash
end YM.SignedWilsonExpansion.Fire
end
