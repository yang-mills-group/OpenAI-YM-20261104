import YM.Integration.WilsonOrdinaryNormalizedStep
import YM.RG12.Canonical.Stops

/-! Numerical rate on the true logarithmic clock used by the original Gram march. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryDyadicAge
open Filter Set Spec Climb Trace.Pilot RG12 WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep
open scoped Topology Classical

theorem approaching : Tendsto Sample.length atTop trail := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun i => (Sample.samples_spacing i).1)⟩
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

/-- On the original discrete physical radii the *numerical* coupling has a
square bounded by the precise inverse age required in `Desk.Elementary.across`. -/
theorem square {G : Gauge} {g : ℝ → ℝ} (paid : Coupling G g) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i : ℕ in atTop, (g (Sample.length i))^2 ≤ C / Sample.age i := by
  let B := |G.slopeConstant⁻¹|+1
  have pos : 0 < B := by dsimp [B]; positivity
  have large : G.slopeConstant⁻¹ < B := lt_of_le_of_lt (le_abs_self _) (lt_add_one _)
  have hi := approaching.eventually (paid.running.eventually (gt_mem_nhds large))
  refine ⟨2*B, by positivity, ?_⟩
  filter_upwards [hi,eventually_ge_atTop (2:ℕ)] with i bound old
  have base : LogV (Sample.length i) = (i:ℝ) := by
    rw [LogV, Sample.length,Real.log_inv,Real.log_exp,neg_neg]
  change LogV (Sample.length i) * g (Sample.length i)^2 < B at bound
  rw [base] at bound
  have aged : Sample.age i ≤ 2*(i:ℝ) := by unfold Sample.age; exact_mod_cast (by omega : i+2 ≤ 2*i)
  have hpos : 0 < Sample.age i := by unfold Sample.age; positivity
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ (g (Sample.length i))^2 * (2*(i:ℝ)) := mul_le_mul_of_nonneg_left aged (sq_nonneg _)
    _ = 2*((i:ℝ)*(g (Sample.length i))^2) := by ring
    _ ≤ 2*B := by linarith

/-- The genuine order-two post-reset Taylor tariff, with loss at most one,
still has a square of coupling to spend. A first-order extraction with positive
loss does not give this estimate. -/
theorem post_reset {G : Gauge} {g : ℝ → ℝ} (simple : G.Simple) (paid : Coupling G g)
    {η : ℝ} (loss : η ≤ 1) : ∀ᶠ r in trail, 18 * (2 * g r)^((3:ℝ)-η) ≤ 72*(g r)^2 := by
  have small := (Coupling.conforms simple paid).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [paid.positive,small] with r pos capped
  have pt : 0 < 2*g r := by positivity
  have unit : 2*g r ≤ 1 := by linarith
  have s := Real.rpow_le_rpow_of_exponent_ge pt unit (by linarith : (2:ℝ)≤3-η)
  calc
    _ ≤ 18 * (2*g r)^(2:ℕ) := mul_le_mul_of_nonneg_left (by exact s.trans_eq (Real.rpow_natCast ..)) (by norm_num)
    _ = _ := by ring

variable {ι : Type} [Fintype ι] {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d

/-- After first-order cancellation on the specified physical row and column, the
actual `PhysMS` coboundary has the right logarithmic age at the original samples.
Only a finite test table of numerical errors is required. -/
theorem crossed {t : ℝ} (ht : 0<t) (P : Pier.Lair.Present F J) (b : Module.Basis ι ℝ D)
    (g : ℝ → ℝ) (paid : Coupling G g) (A B : D →ₗ[ℂ] D) (c : ℝ) (hc : 0≤c)
    (table : ∀ᶠ r in trail, ∀ i j : ι,
      |mixed F J d r (t*r) (b i) (b j) - trialStep F J d r t (second d (g r) A B) (b i) (b j)| ≤ c*(g r)^2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ (L : D →L[ℂ] ℂ) (v : D), L (A v)=0 →
      ‖L (PhysMS.Frame.cocycle d J (Sample.length n) t ht v) - L v‖ ≤
        ‖L‖ * (K / Sample.age n) * ‖v‖ := by
  obtain ⟨U,hU,actual⟩ := WilsonOrdinaryNormalizedStep.crossed F J d ht P b g A B c hc table
  obtain ⟨V,hV,coupled⟩ := square paid
  refine ⟨U*V,by positivity,?_⟩
  filter_upwards [approaching.eventually actual,coupled] with n hn hm L v silent
  refine (hn L v silent).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  calc
    _ ≤ ‖L‖ * U * (V / Sample.age n) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end YM.Integration.WilsonOrdinaryDyadicAge
