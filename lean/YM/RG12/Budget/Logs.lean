import YM.Pert.Asymptotics.RawAxis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Readout precision clocks on the shared Family

The price in `MatrixTicket` uses powers of hat-beta i.e. logs of distance, approximately inverse
square coupling. When applied to an error term, increase internal order accordingly! Reuse
actual trajectory rate from the baseline. This justifies such payments at fixed or varying
cutoff/period on tails; says nothing about scheme conversion or matching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Budget
open Function Filter Pert.Asymptotics Topology Lattice RG
variable {G : Gauge}

/-- On a tail, every cutoff. -/
theorem energy {C : Family G} (hC : C.Makes) (hG : G.Simple) :
    ∀ᶠ m in atTop, ∀ N p, m ≤ N →
      C.path.levels.clock.hatBeta m ≤ 3*C.path.β N p m ∧
      C.path.β N p m > G.slopeConstant / 2 * C.S.scale m := by
  let x := G.slopeConstant
  have hx : 0 < x := Gauge.slopeConstant_pos hG; let c:= C.path.levels.clock.bar
  have hc := C.S.divergent.eventually_gt_atTop (max 0 (2*c/x))
  filter_upwards [hc, zeroUp_bound C hC (ε:= x/2) (half_pos hx)] with m hm hA N p hN
  let E := C.path.β N p m; let t:= C.S.scale m
  have ht: 0<t:= (le_max_left ..).trans_lt hm
  have hu:= hA N p hN; rw [b0_normalizes, abs_lt] at hu
  have he : x/2*t < E:=(lt_div_iff₀ ht).mp (by linarith only [hu])
  refine ⟨le_of_lt ?_,he⟩
  change c+x*t < _; have hi:2*c < t*x:= (div_lt_iff₀ hx).mp ((le_max_right ..).trans_lt hm)
  linarith only [hi,he]

theorem energy_grows {C : Family G} (hC : C.Makes) (hG : G.Simple) {I : Type} {l : Filter I}
    {m p N : I → ℕ} (hm : Tendsto m l atTop) (h : ∀ᶠ i in l, m i ≤ N i) :
    Tendsto (fun i=> C.path.β (N i) (p i) (m i)) l atTop := by
  let x:= G.slopeConstant/2
  have hx:0<x:=half_pos (Gauge.slopeConstant_pos hG)
  apply tendsto_atTop_mono' (f₁:=fun i=> x*C.S.scale (m i)) l _ ((C.S.divergent.comp hm).const_mul_atTop hx)
  filter_upwards [h,hm.eventually (energy hC hG)] with i hi hp using (hp _ (p i) hi).2.le

theorem coupling_small {C : Family G} (hC : C.Makes) (hG : G.Simple) {I : Type} {l : Filter I}
    {m p N : I → ℕ} (hm : Tendsto m l atTop) (h : ∀ᶠ i in l, m i ≤ N i) :
    Tendsto (fun i=> regulatorRun C (N i) (p i) (m i)) l (𝓝[>] 0) := by
  have he:=energy_grows hC hG (p:=p) hm h
  apply tendsto_nhdsWithin_iff.mpr; refine ⟨?_,?_⟩
  · exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp he)
  exact (he.eventually_gt_atTop 0).mono fun i hi=> inv_pos.mpr (Real.sqrt_pos.mpr hi)

lemma hat_charged {C : Family G} (hC : C.Makes) (hG : G.Simple) :
    ∀ᶠ m in atTop, ∀ N p, m ≤ N → C.path.levels.clock.hatBeta m * regulatorRun C N p m ^ 2 ≤ 3 := by
    filter_upwards [energy hC hG,C.S.divergent.eventually_gt_atTop 0] with m hm hx N p hN
    obtain ⟨ht,he⟩:=hm N p hN
    have hi:=Gauge.slopeConstant_pos hG; have hs : 0<C.path.β N p m:= (mul_pos (half_pos hi) hx).trans he
    rw [regulatorRun,inv_pow,Real.sq_sqrt hs.le, ← div_eq_mul_inv]
    exact (div_le_iff₀ hs).mpr ht

/-- `1+abs(log)`; this should be stipulated or quantitatively compared to the actual log cost
in a report, NOT assumed as the scale of the earned MatrixTicket. -/
def logPrice (g : ℝ) := 1 + |Real.log g|
lemma log_ge (g : ℝ) : 1 ≤ logPrice g := by unfold logPrice; linarith [abs_nonneg (Real.log g)]

lemma log_fades (p : ℕ) : Tendsto (fun x:ℝ => x * logPrice x ^ p) (𝓝[>]0) (𝓝 0) := by
  let a:ℝ:= ((p:ℝ)+1)⁻¹; have ha:0<a:= inv_pos.mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) p])
  have hp := (tendsto_log_mul_rpow_nhdsGT_zero ha).abs
  have he : Tendsto (fun x:ℝ=> x^a * logPrice x) (𝓝[>] 0) (𝓝 0):=by
    have ht : Tendsto (fun x:ℝ=>x^a) (𝓝[>]0) (𝓝 0):=(show Tendsto (fun x:ℝ=> x^a) (𝓝 0) (𝓝 0) by simpa [ContinuousAt, ha.ne'] using (continuousAt_id.rpow_const (x:=(0:ℝ)) (Or.inr ha.le) : ContinuousAt (fun x:ℝ=> x^a) 0)).mono_left nhdsWithin_le_nhds
    have hh:=hp.add ht; rw [abs_zero,zero_add] at hh; apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx; unfold logPrice; rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp hx).le _)]; ring
  have he' := (he.pow (p+1)); rw [zero_pow (Nat.succ_ne_zero p)] at he'
  have hz : Tendsto (fun x:ℝ=>x * logPrice x ^ (p+1)) (𝓝[>]0) (𝓝 0):=by
    apply he'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hs : 0<x:= Set.mem_Ioi.mp hx
    rw [mul_pow, show a=(↑(p+1:ℕ):ℝ)⁻¹ from by simp [a], Real.rpow_inv_natCast_pow hs.le (Nat.succ_ne_zero p)]
  apply squeeze_zero' _ _ hz
  · filter_upwards [self_mem_nhdsWithin (a:= (0:ℝ)) (s:=Set.Ioi 0)] with x hx using mul_nonneg (Set.mem_Ioi.mp hx).le (pow_nonneg (zero_le_one.trans (log_ge _)) _)
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Set.Ioi 0)] with x hx using mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (log_ge _) (Nat.le_succ p)) (Set.mem_Ioi.mp hx).le
end YM.RG12.Budget
