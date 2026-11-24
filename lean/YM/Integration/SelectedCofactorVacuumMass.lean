import YM.Integration.SelectedCofactorCommonVacuum
import YM.TraceExtension.Shepherd.Abyss

/-! The same selected scalar cancels between the original partition and
the full dirty-field numerator. The regular rows require the stated E budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorVacuumMass
open RG Wilson Lattice Set MeasureTheory Filter Function Finset Marker
open LocalComparison LocalComparison.Global PathData AnalyticBridge.VerifiedReset
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ENNReal

variable {G : Gauge} {n : Side} {R : Rep G n} {p : BudgetPoint} {σ A Λ : ℝ}
local notation "Y" => R.path
local notation "Z" => R.p
local notation "K" => R.clip
local notation "a" => R.beta

/-- Volume estimate at the actual mask, under its retained E budget. -/
theorem regular_volume (h : WellFormed p R) (U : Config G n) :
    |R.activities.additive R.p U| ≤ Fintype.card (Site n) * h.regularCost := by
  let E := fun i => R.activities.regularOccurrence R.p i U
  have he : Summable (fun i => ‖E i‖) := by
    simpa only [Real.norm_eq_abs] using (h.regular_sum U).abs
  obtain ⟨b,hb,hB⟩ := h.regular_bound
  let W (z : Site n) i := if (R.activities.reg i).site = z then p.mass (R.activities.reg i).support (b i) else 0
  have hs z : Summable (W z) := (hB z).2.1
  calc
    _ ≤ ∑' i, ‖E i‖ := norm_tsum_le_tsum_norm he
    _ ≤ ∑' i, ∑ z, W z i := by
      apply he.tsum_le_tsum _ (summable_sum fun i _ => hs i)
      intro i
      simp only [W,sum_ite_eq,Finset.mem_univ,if_true]
      apply le_trans _ (p.loMass _ _ (hb i).1)
      dsimp only [E, Activities.regularOccurrence]
      rw [← h.threshold]
      by_cases hx : Healthy p.threshold (R.activities.reg i).support U
      · rw [masked_eq _ _ _ _ hx]
        exact (hb i).2 U hx [] (Nat.zero_le _) (by simp)
      rw [masked_ne _ _ _ _ hx,norm_zero]
      exact (hb i).1
    _ = _ := Summable.tsum_finsetSum (fun i _ => hs i)
    _ ≤ ∑ _ : Site n, h.regularCost := sum_le_sum fun z _ => (hB z).2.2
    _ = _ := by simp

/-- The physical path has the original flag penalty on a weakly regular output. -/
theorem flag_exponent (h : WellFormed p R) (hPath : R.path.Bounds R.clip σ A Λ)
    (U : Config G n) (t : ℝ) (ht : 0 < t) (hv : 2*t ≤ R.p.threshold) (hs : 0 ≤ R.beta) :
    R.exponent U ≤ R.scalar + Fintype.card (Site n)*R.exCost A Λ h.regularCost -
      R.beta*(R.clip.linear/5*t^2*(flags t U).card) := by
   let x:=Fintype.card (Site n); let f(V:Config G n):=R.path.principal K Z R.beta V
   let L:=PathData.loopsPrice Z a A Λ; let b:= R.beta*(R.clip.linear/5*t^2*(flags t U).card)-x*L
   have he(s: Signed): b≤R.path.principal K Z a (pull s 0 U):=by
      let V:=pull s 0 U; have hp : (flags t V).card=(flags t U).card:=by rw [← Work.H03.flags_send s (0:Site n) t U]; exact (Finset.card_image_of_injective _ (Push.Local.turnSites s 0|>.injective)).symm
      have hi:= Trace.Shepherd.valour R V t ht hv; rw [hp] at hi; let q:=Y; have hx:= (abs_le.mp (q.volume_price K Z a hs V hPath)).1
      unfold b; linarith only [hx,mul_le_mul_of_nonneg_left hi hs]
   have hh : b≤ R.path.inChannels K Z a U:= by
      have hm:= sum_le_sum (f:=fun _ : Signed=> b) (fun i (_:i∈Finset.univ)=> he i); exact (le_trans (le_of_eq (b:=factor * ∑ i:Signed,b) (by simp only[sum_const, card_univ,nsmul_eq_mul,← mul_assoc,factor_card,one_mul])) (mul_le_mul_of_nonneg_left hm factor_pos.le))
   have hy := (abs_le.mp (regular_volume h U)).1
   unfold Rep.exponent Rep.scalar Rep.exCost; unfold b at hh; linarith only [hh,hy]

private theorem calm_exponent (h : WellFormed p R) (hPath : R.path.Bounds R.clip σ A Λ)
    (hs : 0 ≤ R.beta) {s : ℝ} (hp : 0 < s) (he : s ≤ R.p.threshold)
    {U : Config G n} (hh : U ∈ calm G n s) :
    R.scalar - (Fintype.card (Site n):ℝ)*(R.exCost A Λ h.regularCost + R.beta*baseBudget R.clip A s) ≤ R.exponent U := by
  have H := PathData.under hPath s hp he hs hh
  have hw := (abs_le.mp (regular_volume h U)).2
  unfold Rep.scalar Rep.exponent Rep.exCost
  linarith

/-- Lower bound for the original integral. Positivity and integrability concern
the actual density; its vacuum representation need only be weakly regular. -/
theorem denominator (h : WellFormed p R) (hPath : R.path.Bounds R.clip σ A Λ)
    (hs : 0 ≤ R.beta) (s : ℝ) (hp : 0 < s) (he : s ≤ R.p.threshold)
    (hpos : ∀ U, 0 ≤ R.eval U) (hI : Integrable R.eval (prior G n)) :
    Real.exp (R.scalar - (Fintype.card (Site n):ℝ)*(R.exCost A Λ h.regularCost+R.beta*baseBudget R.clip A s)-
       (Fintype.card (Edge (Site n)):ℝ)*Module.finrank ℝ G.Mat* Real.log (16/s)) ≤ ∫ U, R.eval U ∂prior G n := by
  let D := calm G n s
  let X := R.scalar - (Fintype.card (Site n):ℝ)*(R.exCost A Λ h.regularCost+R.beta*baseBudget R.clip A s)
  have hf (U : Config G n) (hU : U∈D) : Real.exp X ≤ R.eval U := by
    unfold Rep.eval; rw [Activities.gas_one _ _ (voids hU he),mul_one]
    exact Real.exp_monotone (calm_exponent h hPath hs hp he hU)
  have hD : (prior G n).real D * Real.exp X ≤ ∫ U : Config G n,R.eval U ∂prior G n := calc
    _ = ∫ U : Config G n,D.indicator (fun _ => Real.exp X) U∂prior G n := by
      rw [integral_indicator (show MeasurableSet D from calm_meas _),setIntegral_const]; simp only [smul_eq_mul]
    _ ≤ _ := integral_mono (integrable_const _ |>.indicator (show MeasurableSet D from calm_meas _)) hI fun i => by
      by_cases he : i ∈ D
      · rw [indicator_of_mem he]; exact hf i he
      rw [indicator_of_notMem he]; exact hpos _
  let d := Module.finrank ℝ G.Mat
  let edges := Fintype.card (Edge (Site n))
  apply le_trans ?_ hD
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (space G n s hp (he.trans R.p.threshold_le)) (Real.exp_pos X).le)
  change Real.exp (X - (edges:ℝ)*d*Real.log (16/s)) ≤ ((s/16)^d)^edges*Real.exp X
  refine le_of_eq ?_
  have hy : Real.log (16/s) = -Real.log (s/16) := by rw [← Real.log_inv]; congr 1; field_simp
  rw [mul_comm _ (Real.exp X), hy, mul_neg, sub_neg_eq_add,Real.exp_add, mul_assoc (edges:ℝ), Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log (by positivity)]

/-- A one-vacuum signed observable keeps the volume cost and physical dirty gain explicit. -/
theorem signed_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (h : WellFormed p R) (hPath : R.path.Bounds R.clip σ A Λ) (hβ : 0 ≤ R.beta)
    (s t : ℝ) (hs : 0 < s) (hSmall : s ≤ R.p.threshold) (ht : 0 < t) (hT : 2*t ≤ R.p.threshold)
    (hpos : ∀ U, 0 ≤ R.eval U) (hI : Integrable R.eval (prior G n))
    (F : Config G n → E) (hF : Measurable F) (b : ℝ) (hB : ∀ U, ‖F U‖ ≤ b)
    (q : ℕ) (hFlags : ∀ U, F U ≠ 0 → q ≤ (flags t U).card) :
    let f := fun U => Real.exp (R.exponent U) • F U
    let Z₀ := ∫ U, R.eval U ∂prior G n
    Integrable f (prior G n) ∧ ‖Z₀⁻¹ • ∫ U, f U ∂prior G n‖ ≤ b * Real.exp
      ((Fintype.card (Site n):ℝ)*(2*R.exCost A Λ h.regularCost + R.beta*baseBudget R.clip A s) +
        (Fintype.card (Edge (Site n)):ℝ)*Module.finrank ℝ G.Mat*Real.log (16/s) -
        R.beta*(R.clip.linear/5*t^2*q)) := by
  dsimp only
  let upper := R.scalar + Fintype.card (Site n)*R.exCost A Λ h.regularCost - R.beta*(R.clip.linear/5*t^2*q)
  let lower := R.scalar - Fintype.card (Site n)*(R.exCost A Λ h.regularCost+R.beta*baseBudget R.clip A s) -
    Fintype.card (Edge (Site n))*Module.finrank ℝ G.Mat*Real.log (16/s)
  have hz := denominator h hPath hβ s hs hSmall hpos hI
  have hZ : 0 < ∫ U, R.eval U ∂prior G n := (Real.exp_pos lower).trans_le hz
  have hb : 0 ≤ b := (norm_nonneg _).trans (hB 1)
  have hu (U) : ‖Real.exp (R.exponent U) • F U‖ ≤ Real.exp upper * b := by
    by_cases he : F U = 0
    · rw [he,smul_zero,norm_zero]
      exact mul_nonneg (Real.exp_pos _).le hb
    rw [norm_smul_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul _ (hB U) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_monotone ((flag_exponent h hPath U t ht hT hβ).trans _)
    dsimp only [upper]
    have hγ : 0 ≤ R.clip.linear/5*t^2 := mul_nonneg (div_nonneg R.clip.tail_pos.le (by norm_num)) (sq_nonneg t)
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hFlags U he)) hγ) hβ) _
  refine ⟨Integrable.of_bound (((ActualSelectedModelEnvelope.exponent_envelope h hPath).exp.meas.smul hF).aestronglyMeasurable)
    _ (ae_of_all _ hu),?_⟩
  rw [norm_smul_of_nonneg (inv_nonneg.mpr hZ.le)]
  have hn : ‖∫ U, Real.exp (R.exponent U) • F U ∂prior G n‖ ≤ Real.exp upper * b := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := prior G n) (ae_of_all _ hu)
  calc
    _ ≤ (Real.exp lower)⁻¹*(Real.exp upper*b) := mul_le_mul (inv_anti₀ (Real.exp_pos lower) hz) hn
      (norm_nonneg _) (inv_nonneg.mpr (Real.exp_pos _).le)
    _ = b * Real.exp _ := by
      rw [←Real.exp_neg,←mul_assoc,←Real.exp_add,mul_comm _ b]
      congr 2
      dsimp only [lower,upper]
      ring

end YM.Integration.SelectedCofactorVacuumMass
end
