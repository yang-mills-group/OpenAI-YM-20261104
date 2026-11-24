import YM.WiderProfiles.Compare
/-!
# Spending WiderProfiles on the grown window

Abstract Filter-indexed version so no dependence on a *choice* of physical or
auxiliary schedule. In §F `RecropCash`, think of the ExtendedEpoch hypotheses
εᵏ nside → ∞, θ scale given by `X+O(ℒ)`, `X=g^(-γ)`, as supplying `front`,
`window`. This makes explicit exactly what scale comparisons the WiderProfiles
step consumes, not assuming C1.w itself nor formalizing the construction of epochs.
This application is still to the **independent formal coefficient** (both before
and after adjustment), not to measurements on the physical hierarchy. `g` does
not change the selected calibration or clocks; it indexes the test geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Real
open Register MS MS.Land MS.Menus MS.Tide MS.Fleet
open XSpace XSpace.Cirrus Maxwell Maxwell.Free XSpace.Structure1 Arrival
open O.Enh
open O.Score (squeeze)
open scoped Topology ContDiff BigOperators Classical
variable {I : Type*} {f : Filter I} {p : I → XSpace.Mesh} {g : I → ℝ} {b : ℝ}

lemma pow_budget (u : ℝ) (γ B : ℝ) (a : ℕ) (ha : B/γ ≤ (a:ℝ))
    {x : ℝ} (hγ : 0 < γ) (hu : 0 < u) (h : u ≤ 1) (ht : u^(-γ) ≤ 2*x) :
    u^(-B) ≤ (2:ℝ)^a * (1+x)^a := by
  have h1 : -γ * (a:ℝ) ≤ -B := by linarith [ (div_le_iff₀ hγ).mp ha ]
  calc
    _ ≤ u^(-γ * (a:ℝ)) := Real.rpow_le_rpow_of_exponent_ge hu h h1
    _ ≤ _ := by rw [Real.rpow_mul_natCast hu.le, ← mul_pow]
                exact pow_le_pow_left₀ (Real.rpow_nonneg hu.le _) (ht.trans (by linarith)) a

lemma spacing_pay (front : Tendsto p f Front) (hg : Tendsto g f (𝓝[>] 0))
    {γ : ℝ} (hγ : 0 < γ) (window : ∀ᶠ i in f, g i ^ (-γ) ≤ 2 * Schedule.theta (p i))
    (B : ℝ) : ∀ᶠ i in f, cost (p i) ≤ g i ^ B := by
  let θ i := Schedule.theta (p i)
  let e i := (p i).spacing
  have hp : ∀ᶠ i in f, e i ≤ 1 := front.eventually frontier.smaller
  have he : Tendsto (fun i => log (e i)) f atBot := Real.tendsto_log_nhdsGT_zero.comp
    (tendsto_nhdsWithin_iff.mpr ⟨frontier.endpt.comp front, Eventually.of_forall fun i=> (p i).positive⟩)
  have ht : Tendsto θ f atTop := (tendsto_neg_atBot_atTop.comp he).congr'
    (hp.mono fun i hi => (Schedule.theta_value hi).symm)
  obtain ⟨a,ha⟩ := exists_nat_gt (B/γ)
  let r := mildG/2
  have h1 : Tendsto (fun i => (1+θ i)^a * exp (-r*θ i)) f (𝓝 0) :=
    (exp_keep _ (half_pos mild_p) a _).comp ht
  have hw := h1.eventually (ge_mem_nhds (by positivity : (0:ℝ) < ((2:ℝ)^a)⁻¹))
  filter_upwards [ (tendsto_nhdsWithin_iff.mp hg).2,
    (tendsto_nhdsWithin_iff.mp hg).1.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),
    hp, window, hw] with i hi hi' hpi hz hq
  have hx : cost (p i) = exp (-r*θ i) := by
    unfold cost r θ; rw [Schedule.theta_value hpi, Real.rpow_def_of_pos (p i).positive]; ring_nf
  rw [hx]
  have hI : 0 < g i := hi
  apply (le_of_mul_le_mul_right _ (Real.rpow_pos_of_pos hI (-B)))
  have hh : (2:ℝ)^a * ((1+θ i)^a * exp (-r*θ i)) ≤ 1 := by
    apply (le_div_iff₀' (by positivity : 0 < (2:ℝ)^a)).mp
    rw [one_div]
    exact hq
  calc
    _ ≤ exp (-r*θ i) * ((2:ℝ)^a * (1+θ i)^a) := mul_le_mul_of_nonneg_left
      (pow_budget _ γ B a ha.le hγ hI hi' hz) (exp_pos _).le
    _ ≤ 1 := le_trans (le_of_eq (by ring)) hh
    _ = _ := by rw [← Real.rpow_add hI]; simp

/-- §F use at ExtendedEpoch price scales (including all those two-zone layout
samples and choices of fixed labels); precision any power of the small parameter.
No compact restriction on the combined layout. `b` as large as desired; γ positive
as small as desired, but held fixed when using this error estimate. -/
theorem powered_forest {G : Gauge} (N : WilsonPrescription G) (h : G.Simple)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (A : Prescription (Press.portDeck G)) (H : Main.Match N h T A true)
    {n m d : ℕ} (K : Set (Points n)) (S : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    (E : ℝ) (hE : 0 < E) (k : ℕ) (v : Tags G d (n+m))
    (front : Tendsto p f Front) (hg : Tendsto g f (𝓝[>] 0))
    {γ : ℝ} (hγ : 0 < γ) (window : ∀ᶠ i in f, g i ^ (-γ) ≤ 2 * Schedule.theta (p i))
    (b B : ℝ) : ∃ t0 C : ℝ, 0 < C ∧ ∀ᶠ i in f, ∀ t ≥ t0,
        exp t ≤ E * g i ^ (-b) → ∀ x ∈ K, ∀ y ∈ S,
      ∀ s : Sample (n+m), grab s=p i → Schedule.Sized s → familiar s=forest x (squeeze (-t) y) →
      ∃ hc : familiar s ∈ conf (n+m),
       ‖Rose.measureₓ N.scheme N.criterion d s k v -
          Scale.Measure.start N.scheme N.criterion d (n+m) ⟨familiar s, hc⟩ k v‖ ≤ C * g i ^ B ∧
       ‖Speed.forms_t N.scheme N.criterion s d k v -
          Scale.Measure.outlook N.scheme N.criterion d (n+m) ⟨familiar s,hc⟩ k v‖ ≤ C * g i ^ B := by
  obtain ⟨a,ha⟩ := exists_nat_gt (b/γ)
  obtain ⟨t0,C,hC,hq⟩ := compare_forest N h T A H K S hK hx hS hy (E*2^(a+1))
    (by positivity) (a+1) k v
  refine ⟨t0,C,hC,?_⟩
  filter_upwards [front.eventually hq, spacing_pay front hg hγ window B,
    (tendsto_nhdsWithin_iff.mp hg).2,
    (tendsto_nhdsWithin_iff.mp hg).1.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),
    window] with i hi hpi h1 h2 hi' t ht ht' x hx y hy s hS hx' hL
  have h3 := pow_budget (g i) γ b (a+1) (by push_cast; linarith)
    (x:= Schedule.theta (p i)) hγ h1 h2 hi'
  obtain ⟨hc,hP,hX⟩ := hi t ht (by rw [mul_assoc]; exact ht'.trans (mul_le_mul_of_nonneg_left h3 hE.le)) x hx y hy s hS hx' hL
  exact ⟨hc, hP.trans (mul_le_mul_of_nonneg_left hpi hC.le),
    hX.trans (mul_le_mul_of_nonneg_left hpi hC.le)⟩
end YM.FVA2.WiderProfiles
