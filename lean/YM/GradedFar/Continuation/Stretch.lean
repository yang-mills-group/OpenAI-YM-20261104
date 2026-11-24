import YM.GradedFar.Continuation.Windows
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strict exponent gaps pay all the deformation costs

Use the argument at (M.3). Price manipulation independent of data (including actual
onset from the stationary moments); B chosen *after* P,η,h, etc., then p can be
chosen sufficiently large depending on B. Does not assume a single frozen T-r
subsequence in the given lease. Real B; all constants C even allowing constant multiples
in both bounds `T ≍ g^(-B)`.
-/
namespace YM.FVA2.GradedFar.Continuation
namespace Stretch
noncomputable section
open Filter Set Topology Real Function
open scoped Topology
open Window (windows)
variable {G : Gauge} (simple : G.Simple)
local notation "τ" => (𝓝[>] (0:ℝ))
local notation "g" => gYM G

lemma small_log (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) : ∀ᶠ s in (atTop : Filter ℝ),
    (1+s)^k ≤ (exp s)^ρ := by
  filter_upwards [(tendsto_exp_mul_div_rpow_atTop k ρ hρ).eventually_ge_atTop (2^k), eventually_ge_atTop (1:ℝ)] with s hs hp
  rw [rpow_natCast] at hs
  have h : 0<s := zero_lt_one.trans_le hp
  calc
    (1+s)^k ≤ (2*s)^k := by gcongr; linarith
    _ = 2^k*s^k := mul_pow ..
    _ ≤ exp (ρ*s) := (le_div_iff₀ (by positivity)).mp hs
    _ = _ := by rw [mul_comm, exp_mul]

include simple
/-- r below any power of g. -/
lemma small_root (p : ℝ) : ∀ᶠ r in τ, r ≤ g r ^ p := by
  let D := G.slopeConstant
  have hd : 0<D := Gauge.slopeConstant_pos simple
  let M := D^(p/2)
  have ht : Tendsto (fun r : ℝ => Real.log r⁻¹) τ atTop := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  filter_upwards [ht.eventually ((tendsto_exp_div_rpow_atTop (p/2)).eventually_ge_atTop M), ht.eventually_gt_atTop 0,
    self_mem_nhdsWithin] with r hr hp (hr0 : r ∈ Ioi 0)
  have hx : 0 < r := hr0
  let L := Real.log r⁻¹
  have hp : 0 < L := hp
  have hz : M*L^(p/2) ≤ r⁻¹ := (le_div_iff₀ (by positivity)).mp (by
    rwa [Real.exp_log (inv_pos.mpr hx)] at hr)
  have he : g r ^ p = (M*L^(p/2))⁻¹ := by
    change (√(D*L))⁻¹^p=(D^(p/2)*_)⁻¹
    rw [inv_rpow,Real.sqrt_eq_rpow,← rpow_mul, show 1/2 * p = p/2 by ring,mul_rpow hd.le hp.le] <;> positivity
  rw [he]; exact (inv_inv r).symm.le.trans (inv_anti₀ (by unfold M; positivity) hz)

lemma power_tends (p : ℝ) (hp : 0 < p) : Tendsto (fun r => g r ^ p) τ (𝓝 0) := by
  have h := (shrink simple).rpow_const (Or.inr hp.le)
  rwa [Real.zero_rpow hp.ne'] at h
variable {c C B : ℝ}

-- T bounds give both signs of the power expense.
lemma cap (hc : 0<c) (hC : 0<C) (p : ℝ) :
    let M := max (c^p) (C^p)
    ∀ᶠ w in windows (band G c C B), (exp w.2)^p ≤ M * (g w.1)^(-B*p) := by
  intro M
  filter_upwards [Window.windows_span (band G c C B),(Window.windows_short _).eventually (positive_g simple)] with w ⟨up,lo⟩ hg
  have hg' (v : ℝ) : 0<(g w.1)^v := Real.rpow_pos_of_pos hg _
  rw [Real.rpow_mul (show 0 ≤ g w.1 from hg.le)]
  rcases le_total 0 p with hp|hp
  · refine le_trans (Real.rpow_le_rpow (exp_pos _|>.le) (show (exp w.2) ≤ C*g w.1^(-B) from up) hp) ?_
    rw [mul_rpow hC.le (hg' _).le]
    exact mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
  refine le_trans (Real.rpow_le_rpow_of_nonpos (mul_pos hc (hg' _)) (show c*g w.1^(-B) ≤ (exp w.2) from lo) hp) ?_
  rw [mul_rpow hc.le (hg' _).le]
  exact mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)

/-- With strict exponent gaps every fixed multiplier (and power of log T) can even be bought. -/
lemma trade (hc : 0<c) (hC : 0<C) (hB : 0<B) {a b p q : ℝ} (hi : b-B*q < a-B*p)
    (k : ℕ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ w in windows (band G c C B), D*((1+w.2)^k)*g w.1^a*(exp w.2)^p ≤ g w.1^b*(exp w.2)^q := by
  let d := a-B*p - (b-B*q)
  let ρ : ℝ := d/(2*B)
  have hd : 0 < d := sub_pos.mpr hi
  have hr : 0 < ρ := div_pos hd (by positivity)
  let u := p+ρ-q
  let xp := a + -B*u-b
  have hz : xp=d/2 := by unfold xp u ρ d; field_simp; ring
  have hx : 0 < xp := hz ▸ half_pos hd
  let M := max (c^u) (C^u)
  have hm : 0 < M := lt_max_of_lt_left (Real.rpow_pos_of_pos hc _)
  have he : ∀ᶠ r in τ, D*M*g r^xp ≤ 1 := by
    have hv := (power_tends simple xp hx).const_mul (D*M); rw [mul_zero] at hv
    exact (hv.eventually_lt_const zero_lt_one).mono fun i hi => hi.le
  filter_upwards [(Window.windows_short _).eventually he, (Window.windows_short _).eventually (positive_g simple),
    cap simple (B:=B) hc hC u, (Window.windows_separation _).eventually (small_log k ρ hr)] with w hw hg hu hp
  let T := (exp w.2); have ht : 0<T := exp_pos _; let t := g w.1; have ht' : 0<t := hg
  calc
    _ ≤ D*T^ρ*t^a*T^p := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hp hD.le
    _ = D*t^a*T^u*T^q := by
        rw [mul_assoc (D*t^a) (T^u), ← Real.rpow_add ht, show u + q = ρ + p by unfold u; ring, Real.rpow_add ht]; ring
    _ ≤ D*t^a*(M*t^(-B*u))*T^q := by gcongr
    _ = D*M*t^xp*(t^b*T^q) := by
        rw [show a = xp+b-(-B*u) by unfold xp; ring, Real.rpow_sub ht',Real.rpow_add ht']; field_simp
    _ ≤ 1*(t^b*T^q) := by gcongr; exact hw
    _ = _ := one_mul _
end
end Stretch
end YM.FVA2.GradedFar.Continuation
