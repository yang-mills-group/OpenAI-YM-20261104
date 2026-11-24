import YM.PhysMS.Foundation.Estimates
import YM.GradedFar.Formal
/-!
# Charging T-log costs in the bridge to a prescribed clock

Actually use on `WilsonPositionHomogeneousFrame.reading`, see `Measured` & `Clock`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries
open Climb Trace.Pilot PhysMS
open XSpace XSpace.Normalize FVA2 FVA2.Register
open scoped Topology BigOperators Classical

variable {G : Gauge} (hG : G.Simple)

/-- g(r) of (M.1) and line 24 (length r>0; totalized by Lean conventions)
using the inverse square root branch. -/
def strength (G : Gauge) (r : ℝ) := (Real.sqrt (G.slopeConstant * Real.log r⁻¹))⁻¹
local notation "g" => strength G
include hG
lemma strength_positive : ∀ᶠ r in trail, 0 < g r := by
  refine (PhysMS.to_log_zoom.eventually_gt_atTop 0).mono (fun r hr => ?_)
  exact inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (Gauge.slopeConstant_pos hG) hr))
lemma strength_scale : ∀ᶠ r in trail, LogV r * (g r)^2 = G.slopeConstant⁻¹ := by
  refine (PhysMS.to_log_zoom.eventually_gt_atTop 0).mono (fun r hr => ?_)
  have hh := Gauge.slopeConstant_pos hG
  change LogV r * (Real.sqrt (G.slopeConstant * LogV r))⁻¹^2 = _
  rw [inv_pow, Real.sq_sqrt (mul_pos hh hr).le]
  field_simp
lemma strength_coupling : Coupling G g :=
  ⟨strength_positive hG, tendsto_const_nhds.congr' ((strength_scale hG).mono (fun _ h=> h.symm))⟩

-- following the normalization argument also in WilsonMaxwellThermometerKineticLog.running
lemma ratio_clock {t : ℝ → ℝ} (h : Coupling G t) : Tendsto (fun r => t r / g r) trail (𝓝 1) := by
  have hp := (strength_coupling hG).running
  have hn := Gauge.slopeConstant_pos hG
  have hf := h.running.div hp (inv_pos.mpr hn).ne'
  rw [div_self (inv_pos.mpr hn).ne'] at hf
  have hr := hf.sqrt
  rw [Real.sqrt_one] at hr
  refine hr.congr' ?_
  filter_upwards [strength_positive hG, h.positive, PhysMS.to_log_zoom.eventually_gt_atTop 0] with r hs ht hz
  simp only [Pi.div_apply]; rw [mul_div_mul_left _ _ (ne_of_gt hz), ← div_pow, Real.sqrt_sq (div_pos ht hs).le]

theorem clock_budget {t : ℝ → ℝ} (ht : Coupling G t) :
    ∀ᶠ r in trail, 0 < g r ∧ |t r| ≤ 1 ∧ |t r| ≤ 2 * g r := by
  -- supplier for calendar g, sign, and price order. Use only this bridge before detector inversion.
  filter_upwards [strength_positive hG, ht.positive, (ratio_clock hG ht).eventually_lt_const (show (1:ℝ) < 2 by norm_num),
    (Coupling.conforms hG ht).eventually_lt_const zero_lt_one] with r hr hQ hr' hr''
  rw [abs_of_pos hQ]; exact ⟨ hr, le_of_lt hr'', le_of_lt ((div_lt_iff₀ hr).mp hr') ⟩
lemma strength_falls : Tendsto g trail trail := tendsto_nhdsWithin_iff.mpr
  ⟨Coupling.conforms hG (strength_coupling hG), (strength_coupling hG).positive⟩
lemma radius_falls (p : ℕ) : ∀ᶠ r in trail, r ≤ g r^p := by
  simpa only [one_mul, Real.rpow_one] using
    (PhysMS.subpower_payment (strength_coupling hG) hG 1 1 zero_lt_one 1 zero_lt_one p)
omit hG
variable {hG}
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open FVA2.Scale Dframe O O.Score Enh FVA2.GradedFar
variable {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (N : WilsonPrescription G)
    (Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    (H : Main.Match N hG Z σ true) (ν : ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "F" => GroupS.gaugeN N.scheme N.criterion Z ν

include H hG
theorem clocked {t : ℝ → ℝ} (ht : Coupling G t) (hd : Through l d) (he : Through l e) (hh : h ≤ l)
    (K : Set (Points n)) (S' : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S') (hy : S' ⊆ Outside m)
    (p : ℕ) (L : ℝ) (hL : 0 ≤ L) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ᶠ r in trail, ∀ T : ℝ, T₀ ≤ T → ∀ x ∈ K, ∀ y ∈ S',
      forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) ∧
      ∀ (u : Inputs G d) (v : Inputs G e), Box u L → Box v L →
        ‖crop p (t r) (fullSeries A F (-Real.log T) hd he x y u v) -
            croppedResponse A F (-Real.log T) hh he y v p (t r) (croppedVector A h p u x (t r))‖ ≤
          C * ((T^(h+1))⁻¹ + (g r)^(p+1)) * (1+Real.log T)^k := by
  obtain ⟨C,hC,k,T₀,hT₀,hF⟩ := formal N Z H ν hd he hh K S' hK hx hS hy p L hL
  refine ⟨C * 2^(p+1), by positivity, k, T₀, hT₀, ?_⟩
  filter_upwards [clock_budget hG ht] with r ⟨hr,h1,h2⟩ T hT x hX y hY
  obtain ⟨hx,hy,hf⟩ := hF T hT x hX y hY
  refine ⟨hx,hy,?_⟩
  intro u v hu hv; refine (hf u v hu hv _ h1).trans ?_
  have hT1 : 1 ≤ T := by linarith
  have hP : 0 ≤ (T^(h+1))⁻¹ := by positivity
  have hz := Real.log_nonneg hT1
  have hm : (T^(h+1))⁻¹ ≤ (2:ℝ)^(p+1)*(T^(h+1))⁻¹ := le_mul_of_one_le_left hP (one_le_pow₀ (by norm_num))
  calc
    _ ≤ C * (2^(p+1)*(T^(h+1))⁻¹ + (2*g r)^(p+1)) * (1+Real.log T)^k := by gcongr
    _ = _ := by rw [mul_pow]; ring

end YM.Integration.GradedFar
