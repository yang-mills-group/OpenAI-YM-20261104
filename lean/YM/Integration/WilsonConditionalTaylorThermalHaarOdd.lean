import YM.Integration.WilsonConditionalTaylorThermalHaarReversal

/-! Odd Haar derivatives vanish on every bond and on the complete finite
descent. The odd activity in the normalized fourth thermal response thus
comes entirely from the original cubic phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalHaarOdd
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalInteraction
open WilsonConditionalTaylorThermalFourthActivity WilsonConditionalTaylorThermalLogHaar
open scoped Classical BigOperators Topology ContDiff

theorem diagonal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E→ℝ}
    (smooth : ContDiffAt ℝ ∞ f 0) (even : ∀ᶠy in 𝓝 0,f (-y)=f y) {k : ℕ}
    (odd : Odd k) (x : E) : jet f k x=0 := by
  have c : Continuous (fun t : ℝ=>t • x) := continuous_id.smul continuous_const
  have tends : Tendsto (fun t : ℝ=>t • x) Tested.germ (𝓝 0) := by
    simpa using (c.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have ne := tends.eventually even
  have right : Aspiration (fun t : ℝ=>f (t • x)) (fun j=>jet f j (-x)) := by
    intro j
    obtain ⟨C,hC,bound⟩:=directions smooth (-x) j
    refine ⟨C,hC,?_⟩
    filter_upwards [bound,ne] with t ht eq
    simpa only [Pi.sub_apply,smul_neg,eq] using ht
  have row := congrFun (right.unique (directions smooth x)) k
  change jet f k (-x)=jet f k x at row
  rw [←neg_one_smul ℝ x,jet_smul,odd.neg_one_pow,neg_one_mul] at row
  linarith

variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
theorem mirror (P : ChartRatio G) (R : LocalRatio P) : ∀ᶠx in 𝓝 0,Chart.fee P (-x)=Chart.fee P x := by
  filter_upwards [Metric.ball_mem_nhds (0:G.Color) R.patch] with x hx
  simp only [Chart.fee,WilsonConditionalTaylorThermalHaarReversal.original P R hx]

theorem mirrorAt (P : ChartRatio G) (R : LocalRatio P) (i : d.Links) :
    ∀ᶠy:E in 𝓝 0,Chart.fee P (-(y i))=Chart.fee P (y i) := by
  have atZero : ContinuousAt (fun y : E=>y i) 0 := (continuous_apply i).continuousAt
  exact atZero.tendsto.eventually (mirror P R)

theorem bonds (P : ChartRatio G) (R : LocalRatio P) (i : d.Links) {k : ℕ} (h : Odd k) (x : E) :
    jet (leaf P i) k x=0 := by
  have s : ContDiffAt ℝ ∞ (Chart.fee P) ((0:E) i) := (Chart.Ratio.fee_smooth R).of_le (by simp)
  refine diagonal (s.comp (f:=fun z:E=>z i) 0 (contDiffAt_apply ℝ G.Color _ _)) ?_ h x
  exact mirrorAt P R i

theorem entire (P : ChartRatio G) (R : LocalRatio P) {k : ℕ} (h : Odd k) (x : E) :
    jet (haar P d) k x=0 := by
  have s : ContDiffAt ℝ ∞ (haar P d) 0 := ((Chart.Ratio.jacobian_smooth R).of_le le_top).mul contDiffAt_const
  apply diagonal s _ h x
  have local_ : ∀ᶠy:E in 𝓝 0,∀i:d.Links,Chart.fee P (-(y i))=Chart.fee P (y i) :=
    eventually_all.mpr (mirrorAt P R)
  filter_upwards [local_] with y hy
  simp only [haar,Chart.jacobian,Pi.neg_apply,hy]

theorem cubic (P : ChartRatio G) (R : LocalRatio P) (t : d.Tags) (x : E) :
    interaction P t x = -jet (d.phase G t) 3 x := by
  rw [interaction,entire P R (by decide : Odd 1) x,zero_div,zero_sub]

theorem onsite (P : ChartRatio G) (R : LocalRatio P) (x : E) :
    (∑ i:d.Links,logarithmic (leaf P i) x) = ∑ i:d.Links, jet (leaf P i) 2 x / leaf P i 0 := by
  simp only [logarithmic,bonds P R _ (by decide : Odd 1) x,zero_div,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,zero_pow,sub_zero]

end YM.Integration.WilsonConditionalTaylorThermalHaarOdd
