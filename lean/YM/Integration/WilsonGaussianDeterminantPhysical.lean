import YM.Integration.WilsonGaussianDeterminantGerm

/-! Full trace roots on the retained calculus, with signed seed and the original running coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantPhysical

open LocalTaylorR2 LocalTaylorR2.Pavilion Analysis
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G}

open PhysicalAffineScalarLogarithm
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
  {F : Forest S.ratio} {R : Rep G f} {W s μ C : ℝ} {P : Teller G}
  {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

open WilsonGaussianDeterminantFull WilsonGaussianDeterminantVertex
open RGLocalTaylor LocalLTE.Fan
open WilsonGaussianDeterminantRoster (model)

private theorem sqrtRate (G : Gauge) (L : Side) :
    Rate G L (1/2) (fun t => Real.sqrt (2 * betaF G t L)) := by
  have h := (Rate.power (G:=G) (L:=L) (a := (1/2 : ℝ))).mul_left (Real.sqrt 2)
  apply h.congr
  filter_upwards with x
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ)), Real.sqrt_eq_rpow (betaF G x L)]

private theorem redeem {p : ℕ} {t : ℝ → ℝ} (h : Rate G L (-((p : ℝ)+1)/2) t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ (β : ℝ), 0 < β → β ≤ 2 * betaF G s L →
      |t s| ≤ ε * (gStep β)^p := by
  have small := (h.mul ((sqrtRate G L).pow p)).below (by linarith) ε hε
  filter_upwards [small] with s hs
  intro β hβ hcap
  have hmul : |t s| * (Real.sqrt β)^p ≤ ε := calc
    |t s| * (Real.sqrt β)^p ≤ |t s| * (Real.sqrt (2 * betaF G s L))^p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hcap) p) (abs_nonneg _)
    _ = |t s * (Real.sqrt (2 * betaF G s L))^p| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) p)]
    _ ≤ ε := hs
  rw [gStep,inv_pow,← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr hβ) p)).mpr hmul


theorem refund (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (L : Side) (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (p j : ℕ)
    (v d : ℝ → ℝ) (hv : Rate G L (-(1/2)) v) (hu : ∀ᶠ s : ℝ in atTop, 0 ≤ v s)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R) (i : Bond f), S.patch = D →
      Sees H j (v s) (d s) χ (fun _ X _ => X.undercurrent i + seed X i - fullPair X i)
        (ε*(gStep R.beta)^p) 1 := by
  obtain ⟨fee,price,paid⟩ := WilsonGaussianDeterminantMarked.available P Q o L D hD χ j v d hv (-((p:ℝ)+1)/2)
  have charts := Glass.portal P D L hD j χ hv hu o.K o.γ W o.indexPay o.f
  filter_upwards [paid,redeem price hε,charts] with s deposit hs charts
  intro c f S T R μ C H i hS E _ _ _ F X V u z x w hx hk hm hχ hV hC
  have small := (hs R.beta H.laws.intake.positive) (H.laws.data.funds.length_eq ▸ H.laws.intake.window.2)
  have cost := (deposit c f S T R μ C H i hS E F X V u z x w hx hk hm hχ hV hC).climb small le_rfl
  apply cost.shimmy
  have port := H.laws.data.localP F X hx hk hm
  have glass := charts c f S T hS H.laws.data.funds H.laws.data.access F X hk hχ hx
    port E V x hC.atV hV
  exact WilsonGaussianDeterminantGerm.rooted X glass port i

theorem original (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (L : Side) (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (p j : ℕ)
    (v d : ℝ → ℝ) (hv : Rate G L (-(1/2)) v) (hu : ∀ᶠ s : ℝ in atTop, 0 ≤ v s)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R) (i : Bond f), S.patch = D →
      Sees H j (v s) (d s) χ (fun _ X _ => fullPair X i - seed X i - model p R X i)
        (ε*(gStep R.beta)^p) 1 := by
  obtain ⟨t,price,localBound⟩ := WilsonGaussianDeterminantVertex.charged P Q o v d L hv hu D hD χ p j
  have err := refund P Q o L D hD χ p j v d hv hu (ε/2) (half_pos hε)
  have observations := WilsonGaussianDeterminantResolvent.paid P Q o v L hv hu D hD p
  filter_upwards [localBound,redeem price (half_pos hε),err,observations] with s hc hs he observed
  intro c f S T R μ C H i hS E _ _ _ F X V u z x w hx hk hm hχ hV hU
  have small := (hs R.beta H.laws.intake.positive) (H.laws.data.funds.length_eq ▸ H.laws.intake.window.2)
  have left := (hc c f S T R μ C H i hS E F X V u z x w hx hk hm hχ hV hU).climb small le_rfl
  have right := he c f S T R μ C H i hS E F X V u z x w hx hk hm hχ hV hU
  have corr := left.separating right
  have hw : ε/2*(gStep R.beta)^p + ε/2*(gStep R.beta)^p ≤ ε*(gStep R.beta)^p := by ring_nf; rfl
  apply (corr.climb hw le_rfl).shimmy
  filter_upwards with y
  let Y := vary X (V y)
  have same : model p R Y i = ∑ n ∈ Finset.range (p+1),
      (gStep R.beta)^n * WilsonGaussianDeterminantVertex.coefficient n Y i
        ((gStep R.beta)⁻¹ • Pavilion.pitch (Canvas.primary G) Y (atEdge S i)) := by
    unfold model
    apply Finset.sum_congr rfl
    intro n hn
    rw [observed c f S T R μ C H F Y i hS hx hk n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]
  change fullPair Y i - seed Y i - model p R Y i =
    (Y.undercurrent i - _) - (Y.undercurrent i + seed Y i - fullPair Y i)
  rw [← same]
  ring

end YM.Integration.WilsonGaussianDeterminantPhysical
end
