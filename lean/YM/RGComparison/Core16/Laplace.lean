import YM.RGComparison.Core16.Positive

/-!
# History expansion: actual normalized-block path potentials to Gaussian moments at fixed torus

All-power exceptional-tail and integrated Taylor remainder, **fixed history only**. Not a norm of
represented activities but estimate of some actual `output` observables. Leaves constants in the
quantification ∀geometry,...∃C (recording dimension explicitly as well). Does not yet estimate
outputs for all `admitted geometry` uniformly. A panel evaluates at the same tree and on the same
tag kernel. Probability zero on unusable tags retained.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial
variable {G : Gauge} {n c : Side} {d : Descent n c} (P : ChartRatio G) (R : LocalRatio P)

private lemma chord_pos {x : G.El} (h : x ≠ 1) : 0 < G.chord x := by
  unfold Gauge.chord
  exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr fun e => h (G.mat_injective e)))
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr G.dimPos))

/-- No period threshold in choosing the positive lower bound to chord for a fixed group and
single-link germ radius. Handles disconnected group (not assuming chart global). -/
def exteriorLinks (r : ℝ) := (G.lieExp '' (ball 0 r))ᶜ

lemma wall_bound {r : ℝ} (hr : 0 < r) (he : r ≤ Chart.small G P) : ∃ b : ℝ, 0 < b ∧
    ∀ x ∈ exteriorLinks (G := G) r, b ≤ G.chord x := by
  let W : Set G.El := exteriorLinks r
  have hx : (1 : G.El) ∉ W := fun i => i ⟨0, mem_ball_self hr, G.mat_lieExp_zero⟩
  have ho : IsCompact W := (((LocalH.geom_patch G).choose_spec.2 r (he.trans (min_le_right ..))).1.isClosed_compl).isCompact
  by_cases h : W.Nonempty
  · obtain ⟨x,hx',H⟩ := ho.exists_isMinOn h G.continuous_chord.continuousOn
    exact ⟨G.chord x, chord_pos (fun e => hx (e ▸ hx')), fun x hx => H hx⟩
  exact ⟨1, one_pos, fun x hx => False.elim (h ⟨x,hx⟩)⟩

open Chart (chamber)
lemma cost_exterior (h : d.Room G) (t : d.Tags) {b r : ℝ} (hb : 0 < b)
    (H : ∀ x ∈ exteriorLinks (G := G) r, b ≤ G.chord x)
    {x : Fields G d} (hx : x ∉ chamber G d.Links r) (hp : 0 < d.probability t x) :
    (b / (1+d.edgeBill G))^2 ≤ d.action t 1 x := by
  obtain ⟨i,hi⟩ : ∃ i, x i ∈ exteriorLinks (G := G) r := by
    by_contra! hn
    exact hx fun i _ => not_not.mp (hn i)
  let B := 1+d.edgeBill G
  have hv : 0 ≤ d.edgeBill G := edgeBill_nonneg G d
  have hb' : 0 < B := by unfold B; linarith
  let f := d.action t (1:Config G c) x
  have hh : b / B ≤ Real.sqrt f := (div_le_iff₀ hb').mpr ((H _ hi).trans
    ((from_flat h hp i).trans (by rw [mul_comm _ (Real.sqrt (d.action ..))]; gcongr; unfold B; linarith)))
  exact (pow_le_pow_left₀ (show 0≤b/B by positivity) hh 2).trans_eq (Real.sq_sqrt (action_nonneg ..))

variable (t : d.Tags) (Y : Fields G d → ℝ)
local notation "muₜ" => d.measure G
local notation "D" => Module.finrank ℝ (Coordinates G d)

def power (a : ℝ) (x : Fields G d) := d.probability t x * Y x * Real.exp (-d.action t 1 x / a^2)

def region (S : Set (Fields G d)) (a : ℝ) := (a^D)⁻¹ * ∫ x in S, power t Y a x ∂muₜ

def nearFee (x : Coordinates G d) := Chart.jacobian P x * d.probability t (d.tablePath x) * Y (d.tablePath x)

include R in
lemma inside (hm : d.OK G) (hY : Measurable Y) {r : ℝ} (hr : 0 < r) (he : r < Chart.small G P)
    {a : ℝ} (ha : 0 < a) : region t Y (chamber G d.Links r) a =
      Radial.partialSum (Chart.tangent G d.Links) (nearFee P t Y) (d.phase G t) r a := by
  let E := Coordinates G d
  let W := Chart.tangent G d.Links
  let φ := d.phase G t
  unfold region
  have hs : Measurable (fun x : Fields G d => d.action t 1 x) :=
    (account_envelope hm 1 t).meas.comp (measurable_const.prodMk measurable_id)
  have hp : Measurable (power t Y a) := ((prob_measurable hm t).mul hY).mul
    (Real.continuous_exp.measurable.comp (hs.neg.div_const (a^2)))
  have hy := Chart.Ratio.chamber_integral (U := d.Links) R _ hp he hr
  have hx : (∫ x in chamber G d.Links r, power t Y a x ∂muₜ) = _ := hy
  rw [hx]; unfold Radial.partialSum
  let g (v : E) := Chart.jacobian P v * power t Y a (d.tablePath v)
  have hh (v : E) : Radial.projection (nearFee P t Y) φ a v = g (a • v) := by
    rw [Radial.projection_eq]; change (_ * _ * _) * _ = _* (_*_* _)
    change _ = _* (_*_* Real.exp (-φ (a • v)/a^2)); ring
  let S : Set E := Radial.disc a r
  let B : Set E := ball 0 r
  have H (x : E) : B.indicator g (a • x) = S.indicator (fun u => g (a • u)) x := by
    by_cases h : a • x ∈ B
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ S from h)]
    rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ S from h)]
  have hi := Measure.integral_comp_smul_of_nonneg W (B.indicator g) a (hR := ha.le)
  simp_rw [H] at hi
  rw [integral_indicator (s:=B) (isOpen_ball.measurableSet), integral_indicator (s:=S)
    (Radial.disc_meas ..)] at hi
  simp_rw [show Radial.projection (nearFee P t Y) (d.phase G t) a = fun v : E => g (a • v) from funext hh]
  exact hi.symm

lemma pow_env (H : d.OK G) (hY : Envelope Y) (a : ℝ) : Envelope (power t Y a) := by
  have h : Envelope (d.action t (1:Config G c)) := ⟨(account_envelope H 1 t).meas.comp
    (measurable_const.prodMk measurable_id), (account_envelope H 1 t).cost.choose,
      fun x => (account_envelope H 1 t).cost.choose_spec (1,x)⟩
  unfold power; simp_rw [div_eq_mul_inv]; exact ((prob_envelope H t).mul hY).mul (h.neg.mul (Envelope.const _)).exp

include R in
/-- Exceptional portion is flat at all finite orders, also for every actual coupling (positive).
Constants after fixing the history. -/
theorem outside_flat (h : d.Room G) (hY : Envelope Y) {r : ℝ} (hr : 0 < r) (he : r < Chart.small G P)
    (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0, ‖region t Y (chamber G d.Links r)ᶜ a‖ ≤ C*a^k := by
  obtain ⟨b,hb,hX⟩ := wall_bound P hr he.le
  let S := (chamber G d.Links r)ᶜ; let d' := D
  let K := (b / (1+d.edgeBill G))^2
  have hK : 0 < K := by have hv := edgeBill_nonneg G d; unfold K; positivity
  have hS := (Chart.Ratio.chamber_open R he.le (U:=d.Links)).isClosed_compl.measurableSet
  obtain ⟨C,hc⟩ := ((prob_envelope (room_ok d h) t).mul hY).cost
  obtain ⟨B,hB,hg⟩ := bounded_exp hK (k+d')
  refine ⟨|C| *B, by positivity, fun a ha => ?_⟩
  have hb' : ∀ x ∈ S, ‖power t Y a x‖ ≤ |C| *Real.exp (-K/a^2) := by
    intro x hx; by_cases ht : 0 < d.probability t x
    · have hz := cost_exterior h t hb hX hx ht
      unfold power; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
      exact (hc x).trans (le_abs_self _)
    · rw [power, show d.probability t x = 0 from le_antisymm (not_lt.mp ht) (probability_nonneg d ..), zero_mul,zero_mul,norm_zero]; positivity
  have hi : ‖∫ x in S, power t Y a x ∂muₜ‖ ≤ |C| *Real.exp (-K/a^2) := le_trans
    (norm_integral_le_of_norm_le (integrable_const _) (by
      filter_upwards [ae_restrict_mem hS] with x hx using hb' x hx))
    ((setIntegral_le_integral (μ:=muₜ) (f:=fun _=>|C| *Real.exp (-K/a^2)) (integrable_const _) (Eventually.of_forall (fun _ => by positivity))).trans_eq (by simp))
  have hv : (a^d')⁻¹ * Real.exp (-K/a^2) ≤ B*a^k := by
    apply le_of_mul_le_mul_left (a := (a⁻¹)^k) _ (by positivity)
    have hh := hg a⁻¹ (by positivity)
    calc
      _ = (a⁻¹)^(k+d') * Real.exp (-K*(a⁻¹)^2) := by rw [inv_pow, inv_pow, inv_pow, pow_add, mul_inv, ← mul_assoc, div_eq_mul_inv]
      _ ≤ B := le_trans (by gcongr; linarith) hh
      _ = _ := by rw [inv_pow, mul_left_comm, inv_mul_cancel₀ (pow_pos ha _).ne', mul_one]
  change ‖(a^d')⁻¹ * _‖ ≤ _; rw [norm_mul, Real.norm_of_nonneg (by positivity : 0≤(a^d')⁻¹)]
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans ((le_of_eq (mul_left_comm ..)).trans
    ((mul_le_mul_of_nonneg_left hv (abs_nonneg C)).trans_eq (mul_assoc ..).symm))

-- strengthened integrator input Y needn't be given by globally smooth function
abbrev SmoothAtFlat (d : Descent n c) (Y : Fields G d → ℝ) := ContDiffAt ℝ ∞ (Y ∘ d.tablePath) 0

def gaussianTerm (k : ℕ) := Radial.moment (Chart.tangent G d.Links) (nearFee P t Y) (d.phase G t) k

private lemma gap (h : d.Room G) : ∃ c > 0, ∀ u, c*‖u‖^2 ≤ jet (d.phase G t) 2 u :=
  ⟨(1+d.edgeBill G)⁻¹^2, pow_pos (inv_pos.mpr (add_pos_of_pos_of_nonneg one_pos (edgeBill_nonneg ..))) 2, coercive_charge t h⟩

include R
lemma near_smooth (hm : d.OK G) (h : d.SmoothAtFlat Y) : ContDiffAt ℝ ∞ (nearFee P t Y) 0 :=
  ((Chart.Ratio.jacobian_smooth R).of_le le_top |>.mul (contDiffAt_const.congr_of_eventuallyEq
    (prob_flat_tangent hm t))).mul h

/-- Local integrability and expansion. `∃C` through `Aspiration` for every fixed finite order,
not a Taylor series of the actual histories in coupling. -/
theorem expands (h : d.Room G) (hY : Envelope Y) (hf : d.SmoothAtFlat Y) :
    Aspiration (region t Y univ) (gaussianTerm P t Y) := by
  intro k; let m := Chart.tangent G d.Links
  let φ := d.phase G t; let B := nearFee P t Y
  have hF := room_ok d h
  have hs : Measurable B := ((Chart.Ratio.jacobian_meas R).mul ((prob_measurable hF t).comp Chart.expLinks_meas)).mul (hY.meas.comp Chart.expLinks_meas)
  have he : Measurable φ := (account_envelope hF 1 t).meas.comp (measurable_const.prodMk Chart.expLinks_meas)
  obtain ⟨δ,hδ,H⟩ := (stationary hF t).rescale_estimate m (near_smooth P R t Y hF hf) hs he (gap t h) k
  let s := Chart.small G P; let r := min s δ/2; let S := chamber G d.Links r
  have hb : 0<s := Chart.Ratio.small_pos R
  have h₁ : 0<r := half_pos (lt_min hb hδ)
  have h₂ : r<s := (half_lt_self (lt_min hb hδ)).trans_le (min_le_left ..)
  obtain ⟨C,H⟩ := H r ⟨h₁,by unfold r; linarith [min_le_right s δ]⟩
  obtain ⟨y,hy,K⟩ := outside_flat P R t Y h hY h₁ h₂ (k+1)
  refine ⟨|C| + y,by positivity,?_⟩
  filter_upwards [Tested.eventually_pos,H] with a ha H
  change ‖region t Y _ a - peval (gaussianTerm P t Y) k a‖ ≤ _
  have heq : region t Y univ a = region t Y S a + region t Y Sᶜ a := by
    unfold region; rw [setIntegral_univ, ← mul_add, integral_add_compl (Chart.Ratio.chamber_open R h₂.le|>.measurableSet)
      ((pow_env t Y hF hY a).integrable _)]
  rw [heq,add_sub_right_comm]
  refine (norm_add_le ..).trans ((add_le_add (b:= |C| * a^(k+1)) ?_ (K a ha)).trans_eq (add_mul ..).symm)
  unfold S; rw [inside P R t Y hF hY.meas h₁ h₂ ha]
  exact H.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))

lemma integrates_term (h : d.Room G) (hf : d.SmoothAtFlat Y) (k : ℕ) :
    Integrable (Radial.normTerm (nearFee P t Y) (d.phase G t) k) (Chart.tangent G d.Links) :=
  (stationary (room_ok d h) t).integrableTerm _ (near_smooth P R t Y (room_ok d h) hf) (gap t h)

omit R in
lemma kernel_integrable (h : d.Room G) : Integrable (Radial.kernel (d.phase G t)) (Chart.tangent G d.Links) := by
  obtain ⟨c,hc,h⟩:=gap t h
  apply (bill_integrable (Chart.tangent G d.Links) 0 hc).mono'
  · unfold Radial.kernel; exact (Real.continuous_exp.comp (continuous_neg.comp (Radial.Smooth.continuousJet ..))).aestronglyMeasurable
  apply Eventually.of_forall; intro x
  rw [bill,pow_zero,one_mul,Real.norm_of_nonneg (kernel_pos.le : 0 ≤ Radial.kernel ..), Radial.kernel]
  refine Real.exp_le_exp.mpr ?_; linarith [h x]

omit R
private lemma first_term (x) : normTerm (nearFee P t Y) (d.phase G t) 0 x = nearFee P t Y 0 * Radial.kernel (d.phase G t) x := by
  have h:(Finset.antidiagonal 0 : Finset (ℕ×ℕ))={((0,0):ℕ×ℕ)}:= by ext ⟨x,y⟩; simp only [Finset.mem_antidiagonal,Finset.mem_singleton,Prod.mk.injEq];omega
  simp [normTerm,integrandSeries,Zone.mul,h,expsum,Zone.TaylorPow]

lemma first_gaussian (h : d.OK G) : gaussianTerm P t Y 0 =
    (Chart.jacobian P (U:=d.Links) 0 * (Fintype.card d.Tags : ℝ)⁻¹ * Y 1) *
      ∫ x, Radial.kernel (d.phase G t) x ∂Chart.tangent G d.Links := by
  unfold gaussianTerm Radial.moment; simp_rw [first_term,integral_const_mul]
  have hv := (prob_flat_tangent h t).self_of_nhds; unfold nearFee; rw [hv,tablePath_zero]

include R in
lemma normalization_pos (h : d.Room G) (hx : 0 < Y 1) : 0 < gaussianTerm P t Y 0 := by
  rw [first_gaussian P t Y (room_ok d h)]
  refine mul_pos (mul_pos (mul_pos ?_ ?_) hx) (integral_exp_pos (kernel_integrable t h))
  · exact Finset.prod_pos fun i _ => (show 0 < Chart.fee P 0 from lt_max_of_lt_left (by rw [R.anchored,mul_one]; exact R.scale))
  exact inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance))
end YM.RGComparison.Core16.Descent
