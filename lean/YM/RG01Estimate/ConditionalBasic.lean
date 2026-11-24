import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Card
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hallmark
import YM.Next.MULTISOURCE.Determined
import YM.UVExt.NeedleShift
/-!
# Actual fine conditional normalization (positive real step)

Kernel fine density and held-tag real derivative prices, full priors. Base positivity (theorem
for the SAME history offsets, saved vacuum scalar used, no denominator assumption from
normalizing the coarse-transition variable). Auxiliary rough bills for derivatives. These can
grow with the volume; intended for consumption in the short-shape argument on SMALL
auxiliary tori, or when any fixed volume cost is allowed. But never by an inverse power of
the VALUE of the normalization, not even for signed inserted moments dominated by the base
in L^∞ relative mass. This lemma at a point does not assume that the flags at the point or
in a neighborhood are fixed or empty. The fine function appearing in this consumption is a
given function for the budget check, no Lipschitz dependence on other parameters implied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Conditioning
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)
variable {n : ℕ} {r C Z a : ℝ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun x:Xs=> represent (tint G _ x))

lemma noise_invoice (U : Config G f) (W : Config G c) (k : S.Choices) :
    S.noise β (S.prediction U k) W = prefactor S G β * Real.exp (-β * noiseTaylor S W U k) := by
  unfold StepData.noise StepData.penaltyWeight Sector.prefactor noiseTaylor
  simp_rw [Finset.prod_mul_distrib, prod_const, card_univ,mul_sum,Real.exp_sum]
  congr 1; apply prod_congr rfl; intro i _; congr 1; ring

local notation "K" => Token.prime G S.kernel n Z C β r
variable (hp : PaintSupply G n Z) (h : (Fintype.card (Bond c):ℝ) ≤ r)
    (he : Brush n C 1 Real.exp 0) (x : Positions (Uniform.Primary c G))

include hp h he in
lemma thermal_slice (U : Config G f) (k : S.Choices) (hx : ‖x‖ ≤ 1) : Brush n
    (K * taggedKernel S β k U (V x)) 1 (fun y=> taggedKernel S β k U (V y)) x := by
  let T:= prefactor S G β * S.likelihood U k
  have hpf : 0 < prefactor S G β := pow_pos (inv_pos.mpr (S.penaltyZ_pos _)) _
  have hT : 0 ≤ T := mul_nonneg hpf.le (S.likelihood_pos ..)
  let p (i:Xs):= -β*noiseTaylor S (V i) U k
  have hQ (y:Xs) : taggedKernel S β k U (V y)=T*Real.exp (p y) := by
     unfold taggedKernel T p; rw [noise_invoice]; ring
  have ha := (Token.dates (U:=U) k hp h x hx).smul (-β); rw [norm_neg] at ha
  simp_rw [hQ]; exact Token.seasons p hT x ha he

include hp h he in
lemma full_slice (U : Config G f) (hx : ‖x‖ ≤ 1) :
    Brush n (K * S.density β U (V x)) 1 (fun y => S.density β U (V y)) x := by
  unfold StepData.density; rw [Finset.mul_sum]
  exact Brush.spree Finset.univ _ _ zero_le_one (fun i _=> thermal_slice S β hp h he x U i hx)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {W : Config G f → ℝ} (hm : S.patch.Branches S.kernel G) (hW : Integrable W (prior G _))
    (hplus : 0 ≤ Token.prime G S.kernel n Z C β r)

abbrev den (W : Config G f → ℝ) (x : Xs) := S.push β W (V x)
abbrev roll (U : Config G f → F) (x : Xs) := S.push β U (V x)
include hp he h hm hW hplus
lemma marked {U : Config G f → F} (hf : StronglyMeasurable U) {a : ℝ}
    (hv : ∀ u, ‖U u‖ ≤ a* W u) (hx : ‖x‖< 1) :
    Brush n (K * (a*den S β W x)) 1 (roll S β U) x := by
  let g y u := S.density β u (V y) • U u
  let σ := S.isKernel hm β; let μ := prior G f
  have hE u (y:Xs) : 0 ≤ S.density β u (V y):= S.density_positive ..
  have ht u y (hy : ‖y‖ ≤ 1): Brush n (K * (a * (S.density β u (V y) * W u))) 1
        (fun y=> g y u) y:= by
     let L : ℝ →L[ℝ] F:= ContinuousLinearMap.toSpanSingleton ℝ (U u)
     have hp:= full_slice S β hp h he y u hy
     have hL : ‖L‖ ≤ ‖U u‖:= by
        apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun i=> ?_)
        change ‖i • U u‖ ≤ _; rw [norm_smul,mul_comm]
     refine ⟨L.contDiff.contDiffAt.comp y hp.smooth,zero_le_one,fun i hi=>?_⟩
     change ‖iteratedFDeriv ℝ i (L ∘ fun v : Xs=> S.density β u (V v)) y‖ ≤ _
     rw [L.iteratedFDeriv_comp_left hp.smooth (by exact_mod_cast hi)]
     apply ((L.norm_compContinuousMultilinearMap_le _)).trans
     exact (mul_le_mul (hL.trans (hv u)) (hp.order _ hi) (norm_nonneg _) ((norm_nonneg _).trans (hv _))).trans_eq (by ring)
  have hT y : StronglyMeasurable (g y) := by
     apply StronglyMeasurable.smul _ hf
     exact ((S.density_meas hm β).comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
  obtain ⟨D,hD⟩:= σ.bound
  have hX := UVExt.EnergyRay.Thermal.Core.meristem_complex (f:=g) (μ:=μ) (Eventually.of_forall hT)
    ⟨fun u=> K * (D*(a*W u)), ((hW.const_mul _).const_mul _).const_mul _,
      (continuous_norm.continuousAt.eventually (gt_mem_nhds hx)).mono fun y hy u =>
        (ht u y hy.le).climb (mul_le_mul_of_nonneg_left (le_trans (by rw [mul_left_comm a])
          (mul_le_mul_of_nonneg_right (hD u (V y)) ((norm_nonneg _).trans (hv _)))) (by assumption)) le_rfl⟩
  apply hX.1.buds (fun u=> K * (a*(S.density β u (V x) * W u)))
      (((StepData.push_slice σ _ _ hW).const_mul a).const_mul _) zero_le_one _ (ae_of_all _ fun u=> ht u x hx.le)
  rw [integral_const_mul, integral_const_mul]; rfl

lemma central (hs : Measurable W) (hw : 0 ≤ W) (hx : ‖x‖<1) :
    Brush n (K * den S β W x) 1 (den S β W) x := by
  rw [← one_mul (den ..)]; apply marked S β hp h he x hm hW (by assumption) hs.stronglyMeasurable _ hx
  intro u; rw [Real.norm_of_nonneg (hw u),one_mul]

/-- Relative estimates at the point x. Avoid paying reciprocal volume costs. -/
lemma log_budget (hs : Measurable W) (hw : 0 ≤ W) (hx : ‖x‖<1) {p : ℝ}
    (hφ : Brush n p 1 Real.log 1) (h0 : 0 < den S β W x) :
    Brush n (clump n K p) 1 (fun y=> Real.log (den S β W y) - Real.log (den S β W x)) x := by
  let s:= den S β W x; let f y:= s⁻¹*den S β W y
  have hp:= central S β hp h he x hm hW (by assumption) hs hw hx
  have h₀ : f x=1:= inv_mul_cancel₀ h0.ne'
  have hZ:0<s⁻¹ := inv_pos.mpr h0; have hr := hp.smul s⁻¹
  rw [Real.norm_of_nonneg hZ.le, mul_left_comm, inv_mul_cancel₀ h0.ne',mul_one] at hr
  refine (composite hr (show Brush n p 1 Real.log (f x) from h₀ ▸ hφ)).shimmy ?_
  filter_upwards [hp.smooth.continuousAt.eventually (lt_mem_nhds h0)] with y hy
  change _ = Real.log (f y); unfold f; rw [Real.log_mul hZ.ne' hy.ne',Real.log_inv]; unfold s; ring


lemma moment_derivatives (hs : Measurable W) (hw : 0 ≤ W) (hx : ‖x‖<1) {p a : ℝ}
    (hφ : Brush n p 1 (fun t:ℝ=> t⁻¹) 1) (h0 : 0 < den S β W x) {U : Config G f → F}
    (hf : StronglyMeasurable U) (hv : ∀ u, ‖U u‖ ≤ a*W u) :
    let K':= Token.prime G S.kernel n Z C β r
    Brush n (clump n K' p * (K' * a)) (1+1) (fun y=> (den S β W y)⁻¹ • roll S β U y) x := by
  intro K'
  let s:= den S β W x; let f y:= s⁻¹*den S β W y
  have hZ:0<s⁻¹ := inv_pos.mpr h0
  have h₁:f x=1:= inv_mul_cancel₀ h0.ne'
  have hd := (central S β hp h he x hm hW hplus hs hw hx).smul s⁻¹
  rw [Real.norm_of_nonneg hZ.le, mul_left_comm,inv_mul_cancel₀ h0.ne',mul_one] at hd
  have hh:= composite hd (show Brush n p 1 (fun t:ℝ=> t⁻¹) (f x) from by rwa [h₁])
  have hM := (marked S β hp h he x hm hW hplus hf hv hx).smul s⁻¹
  rw [Real.norm_of_nonneg hZ.le,mul_left_comm,mul_left_comm s⁻¹,inv_mul_cancel₀ h0.ne',mul_one] at hM
  refine ((hh.twins hM (ContinuousLinearMap.lsmul ℝ ℝ)).climb
    (mul_le_of_le_one_left (mul_nonneg hh.nonneg hM.nonneg) (ContinuousLinearMap.opNorm_lsmul_le ..)) le_rfl).shimmy ?_
  filter_upwards with y; change _=(f y)⁻¹ • s⁻¹ • roll S β U y
  unfold f; rw [_root_.mul_inv_rev, inv_inv,smul_smul,mul_assoc, mul_inv_cancel₀ h0.ne',mul_one]
section realCase
omit hp he h hm hW hplus
-- This step kernel is THE actual one (via History). No gauge law or sector change used at all here.
lemma baseline (H : History G) (h : H.Selected) {m N p : ℕ} (hm : m<N) :
    let β' := H.β N p (m+1); let S':= H.levels.clock.op m p; let U := (H.rep N p (m+1)).eval
    (forall Z, 0 < S'.push β' U Z) ∧
    ∀ (x : Positions (Uniform.Primary (H.S.side m p) G)), ‖x‖<1 →
    ∀ (n : ℕ), ∃ a:ℝ, 0 < a ∧ Brush n a 1 (fun y=> Real.log (den S' β' U y)-Real.log (den S' β' U x)) x := by
  intro β' S' U
  have hr(W) : 0 < S'.push β' U W:= by rw [show S'.push β' U = _ from (h.steps N p m hm).1.symm]; exact Multi.AxisShift.chosen_positive h hm.le W
  refine ⟨hr,fun x hx n=>?_⟩
  let s:= S'.push β' U (represent (tint G _ x))
  have hw : 0 ≤ U := fun u=> (Multi.AxisShift.chosen_positive h hm u).le
  have henv := Rep.envelope _ (h.represents N p _ hm).good
  obtain ⟨Z,hz⟩:= paint_supply G n
  obtain ⟨C,hC,hΨ⟩:= Brush.compact (f:=Real.exp) (k:=n) (s:=({0}:Set ℝ)) (isCompact_singleton) (fun i _=> Real.contDiff_exp.contDiffAt)
  obtain ⟨a,ha,hA⟩:= Brush.compact (f:=Real.log) (k:=n) (s:=({1}:Set ℝ)) (isCompact_singleton) (fun i hi=> Real.contDiffAt_log.mpr ((mem_singleton_iff.mp hi) ▸ one_ne_zero))
  -- direct prime≥0
  let r:ℝ := Fintype.card (Bond (H.S.side m p))
  let K':= Token.prime G S'.kernel n Z C β' r
  have hk : 0 ≤ K':= by
    unfold K' Token.prime; let t:= Token.sizeN G S'.kernel n r Z
    have ht : 0 ≤ t:= by
      unfold t Token.sizeN priceCost Uniform.outerCost composeCost; have hr:0 ≤ r := Nat.cast_nonneg _
      have he:= S'.kernel.penalty_pos; have h:=Uniform.shade_pos G; have hh:=G.colorScale_pos
      have hp : 0< Z:=hz.1
      positivity
    change 0≤ clump n _ _; unfold clump; unfold t at ht
    positivity
  have hd := log_budget S' β' hz (le_refl r) (hΨ _ (mem_singleton 0)) x (H.levels.blocks m p).branches
    (henv.integrable _) hk henv.meas hw hx (hA _ (mem_singleton 1)) (hr (represent (tint G _ x)))
  exact ⟨clump n K' a +1, add_pos_of_nonneg_of_pos hd.nonneg zero_lt_one,hd.climb (le_add_of_nonneg_right zero_le_one) le_rfl⟩
end realCase
end YM.RG01Estimate.Conditioning
