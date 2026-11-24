import YM.Integration.WilsonGraphCenteredFarClockTransport

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredTransport

open Filter Real PowerSeries Growth Continuation
open Register MS MS.Book MS.Land Scale
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Dframe Jury
open MS.Native MS.Menus MS.Tide MS.Book.Program
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)

private abbrev postedHeater := ElectedMeasurement.clock
  (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict))
  (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)

/-- A fixed heat order on the published window admits a polynomial in the log distance.
The group currency is evaluated at the near radius and the physical heater at the far radius. -/
theorem farHeaterRate (p : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ a : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C * (gYM g.core r)^(-B) →
      |postedHeater.{u} g hg periods strict (r * exp s)| ≤ D * gYM g.core r * (1+s)^a ∧
      |postedHeater.{u} g hg periods strict (r * exp s)| ≤ 1 := by
  let N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let Q := WilsonGraphPaperPublication.perspective.{u} g hg
  let law := (Q.matching.dilation (Teller.logNu 1)).check
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  obtain ⟨k, paired⟩ := (AppointedCenteredWindow.paid.{u} g hg periods strict 0 (p+1) hC hB).exists
  obtain ⟨L,hL,a,price⟩ := Appointed220.Zones.clock_log law k
  obtain ⟨K,hK⟩ := exists_nat_gt B
  have running : Tendsto (gYM g.core) (𝓝[>] (0:ℝ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨shrink simple, positive_g simple⟩
  have edges := running.eventually (G1.Wire.move C B hK hC)
  have heat := paid_reading simple (postedHeater.{u} g hg periods strict)
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg periods strict)
  have locations := running.eventually (Appointed220.Zones.Budget.location law K k
    (δ:=1/2) (by norm_num))
  refine ⟨1+2*L, by positivity, a, ?_⟩
  filter_upwards [paired, heat, edges, locations,
    running.eventually (Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4))] with
    r pairedAt heatAt edgeAt locate small s hs upper
  let x := gYM g.core r
  let t := postedHeater.{u} g hg periods strict r
  let v := postedHeater.{u} g hg periods strict (r * exp s)
  let ψ := GroupS.ψ N.criterion Q.MS (Teller.logNu 1) (-s)
  let w := bend N Q.MS s k (t:ℂ)
  have hx : 0 < x := small.1
  have quarter : x ≤ 1/4 := small.2
  have cap : x ≤ 1 := by linarith
  have near : ‖(t:ℂ)‖ ≤ 2*x := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using heatAt.2.2.2
  have edge := edgeAt (exp s) (Real.one_le_exp_iff.mpr hs) upper
  have located := locate (exp s) edge (t:ℂ) near
  rw [Appointed220.Zones.Budget.eta,Real.log_exp] at located
  have half : ‖w‖ ≤ 1/2 := located
  have err : ‖(v:ℂ)-w‖ ≤ x := by
    have h := (le_add_of_nonneg_right (norm_nonneg _)).trans (pairedAt s hs upper).1
    exact h.trans (by simpa only [pow_one] using
      (pow_le_pow_of_le_one hx.le cap (show 1 ≤ p+2 by omega)))
  have triangle : |v| ≤ ‖(v:ℂ)-w‖+‖w‖ := by
    calc |v| = ‖(v:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]
         _ = ‖((v:ℂ)-w)+w‖ := by rw [sub_add_cancel]
         _ ≤ _ := norm_add_le _ _
  have mass : Appointed220.Eval.mass k ψ ≤ L*(1+s)^a := by
    simpa only [abs_neg,abs_of_nonneg hs] using price (-s)
  have rooted : ‖w‖ ≤ Appointed220.Eval.mass k ψ * ‖(t:ℂ)‖ :=
    Appointed220.Eval.reserve_rooted ψ k (t:ℂ) (law.led (-s)).start (by linarith)
  have hb := rooted.trans (mul_le_mul mass near (norm_nonneg _) (by positivity))
  have one : 1 ≤ (1+s)^a := one_le_pow₀ (le_add_of_nonneg_right hs)
  have included : x ≤ x*(1+s)^a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left one hx.le
  constructor
  · calc |v| ≤ x + L*(1+s)^a*(2*x) := triangle.trans (add_le_add err hb)
         _ ≤ x*(1+s)^a + L*(1+s)^a*(2*x) := add_le_add included le_rfl
         _ = (1+2*L)*x*(1+s)^a := by ring
  · change |v| ≤ 1
    linarith only [triangle,err,half,quarter]

/-- Raising the actual far heater to the first omitted order preserves the near-currency
power. Only the fixed exponent of the log-distance polynomial changes. -/
theorem farHeaterPower (p : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ b : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C * (gYM g.core r)^(-B) →
      |postedHeater.{u} g hg periods strict (r * exp s)|^(p+1) ≤
        E * (gYM g.core r)^(p+1) * (1+s)^b ∧
      |postedHeater.{u} g hg periods strict (r * exp s)| ≤ 1 := by
  obtain ⟨D,hD,a,fee⟩ := farHeaterRate.{u} g hg periods strict p hC hB
  refine ⟨D^(p+1),pow_nonneg hD _,a*(p+1),?_⟩
  filter_upwards [fee] with r bill s hs upper
  obtain ⟨rate,unit⟩ := bill s hs upper
  refine ⟨?_,unit⟩
  simpa only [mul_pow,pow_mul] using pow_le_pow_left₀ (abs_nonneg _) rate (p+1)

end YM.FVA2.GradedFar.AppointedCenteredTransport

