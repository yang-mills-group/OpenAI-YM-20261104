import YM.RG01Estimate.Parchment
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Views
/-!
# Move normalized gauges back to Left-derivative prices. Consume at all reserved apertures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Receipt
open Function Filter Set Metric Finset Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat Blaze.March
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}{L:Side}
section C
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] {c: Side}
  {x:Positions (Uniform.Primary c G)} {F: Config G c→ E} {v b C w G' : ℝ} {j:ℕ}
local notation "X" => Positions (Uniform.Primary c G)

-- g inverse
omit [CompleteSpace E] in
lemma rotor (hb:0<b)(hg:1≤C)(h : Brush j v 1 (fun y:X=> F (actual (b • y))) (b⁻¹ • x)) :
   Brush j (v*C^j) (b*C)⁻¹ (F ∘ actual) x:= by
    let D:= b⁻¹ • ContinuousLinearMap.id ℝ X
    have ht : ‖D‖≤ b⁻¹:= by unfold D; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hb).le]; exact mul_le_of_le_one_right (inv_pos.mpr hb).le ContinuousLinearMap.norm_id_le
    have he:= Brush.reading D (x:=x) (show Brush j v 1 _ (D x) from h) ht; rw [one_mul] at he
    let k:= F ∘ actual
    have hv:Brush j v b⁻¹ k x:= he.shimmy (Eventually.of_forall (fun i=> congr_arg F (congr_arg actual (smul_inv_smul₀ hb.ne' i).symm)))
    have hP:0<(b*C):=mul_pos hb (zero_lt_one.trans_le hg)
    refine ⟨hv.smooth,(inv_pos.mpr hP).le,fun i hi=> (hv.order i hi).trans ?_⟩
    nth_rw 1 [show b⁻¹=C*(b*C)⁻¹ by rw [_root_.mul_inv_rev,← mul_assoc,mul_inv_cancel₀ (zero_lt_one.trans_le hg).ne',one_mul]]; rw [mul_pow,← mul_assoc]; gcongr; exact h.nonneg

omit [CompleteSpace E] in
lemma polar_price (J: Suitable G j v b 1) (hq:∀ a:G.Color, ‖a‖≤ Uniform.shade G*C→ G.plog (G.mat (G.lieExp a))=a ∧ ‖G.mat (G.lieExp a)-1‖≤b) (hp:0<C)(hx:‖x‖≤C)
    {t y:ℝ} (h:Brush j t C⁻¹ (F ∘ actual) x)(hc:j.factorial*v*((1+royalty G)*w) ≤ C)(hC :(1+royalty G)*w≤ 1) {P:BudgetPoint}(M:Sailor G P.threshold y j) (hB:0< y)(he:0< w)(hm:j*y≤ w) (hf:Push.Local.Chart j F (actual x)) :
    ∀ l: List (Directions G c), l.length ≤ j → (∀ i∈l,‖i‖≤ P.threshold) → ‖leftDerivs F l (actual x)‖ ≤ Boulevard.ticket j t:= by
  have ht:= h.nonneg; intro l hl hL
  by_cases hd:leftDerivs F l (actual x)=0
  · rw [hd,norm_zero]; unfold Boulevard.ticket; positivity
  let f:= leftDerivs F l (actual x)
  obtain ⟨K,hK,hx'⟩:= exists_dual_vector ℝ f (by exact norm_ne_zero_iff.mpr hd)
  have hr:Brush j t C⁻¹ ((K ∘ F) ∘ Boulevard.actual) x:= by
      have ht:= RealTaylor.linear_compression K h hK.le; rw [one_mul] at ht; exact ht
  have h:= (Boulevard.hires J hq hp hx hr hc hC M hB he hm).2 _ hl hL; rw [Push.Local.left_linear K _ hf hl] at h
  rw [show K (leftDerivs F l (actual x))= ‖f‖ from hx',Real.norm_of_nonneg (norm_nonneg f)] at h; exact h
end C

lemma reverse_g (s:ℝ)(β:ℝ)(hp:0<betaF G s L)(h:0<β)(he:β ≤ 2*betaF G s L): gStep (betaF G s L) ≤ 2*gStep β:= by
  let x:=betaF G s L
  have hh:= Fare.gS β h; have hh':= Fare.gS x hp; let u:=gStep β
  change gStep x ≤ 2*u
  apply (sq_le_sq₀ hh'.1.le (mul_nonneg (show 0 ≤ (2:ℝ) by norm_num) hh.1.le)).1
  apply le_of_mul_le_mul_right _ hp; rw [hh'.2,mul_pow]; unfold x at hh'
  nlinarith only [hh.2,mul_le_mul_of_nonneg_left he (sq_nonneg (gStep β))]

lemma travel (G: Gauge)(L: Side)(Y:ℝ→ℝ)(j:ℕ)(hp: Cookie G L Y): ∃ W:ℝ→ℝ, Cookie G L W ∧ ∀ᶠ t in atTop, ∀ (c:Side)(P:BudgetPoint)(x:Positions (Uniform.Primary c G))(β v:ℝ)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
    (F:Config G c → E), let b:= gStep β; betaF G t L /2 ≤ β → β≤2*betaF G t L → 1≤Y t → ‖x‖≤ b*Y t → P.threshold≤ 2* Pressure.fiery G t L →
    Push.Local.Chart j F (Boulevard.actual x) → Brush j v 1 (fun y=> F (Boulevard.actual (b • y))) (b⁻¹ • x) →
    ∀ l:List (Directions G c),l.length≤ j → (∀ i∈l, ‖i‖≤ P.threshold)→ ‖leftDerivs F l (actual x)‖ ≤ v*W t:= by
  obtain ⟨C,hC,H⟩:= oar G j; obtain ⟨d,f,hf⟩:=cleanly G j 1 zero_lt_one
  obtain ⟨M,hM,hm⟩:= Boulevard.seek (G:=G) hf.pos; let r:= royalty G
  let A t:=2* Pressure.fiery G t L; let Hx t:= 4* Delay.fineMonitor G L t
  let W t:=(1+(j:ℝ))*(C*Hx t); let Y' t:= Y t+j.factorial*d*((1+r)*W t)
  have hc : Cookie G L W:= (Cookie.const _).pays ((Cookie.const _).pays ((Cookie.const (4:ℝ)).pays Cookie.mast))
  have hr:= hp.joins ((Cookie.const (↑j.factorial*d:ℝ)).pays ((Cookie.const (1+r)).pays hc)); let Q t:=ticket j (Y' t^j)
  have hp:Cookie G L Y':=hr; have hQ:Cookie G L Q:= ((Cookie.const (j.factorial:ℝ)).pays (hp.pow j)).pays (Cookie.const _)
  have hl:= (glim G L).mul hp.uses|>.mul_left (Uniform.shade G); have hP:= (glim G L).mul hc.uses|>.mul_left (1+r)
  refine ⟨Q,hQ,?_⟩; filter_upwards [Delay.shift_pos G L,hl.below (by norm_num) M hM,hP.below (by norm_num) 1 zero_lt_one] with t ht hh hx c P x β v E _ _ _ F b hp hb hm' hz he hF hΦ l hL h
  have hp':0<β := (half_pos ht).trans_le hp
  obtain ⟨hv,hV⟩:= lamp G L ht β hp; have he':= (reverse_g t β ht hp' hb)
  have hd:=hf.value; have hr:0<r:=zero_lt_one.trans_le (royalty_ge _); have hu : 0 < Hx t:= mul_pos (by norm_num) (Delay.monitor_pos G L t)
  have hf' : 0 < W t := by unfold W; positivity; -- semicolon
  have hA: A t ≤ b*Hx t:= by
     change 2*(gStep (betaF G t L)* Delay.fineMonitor G L t) ≤ b * Hx t
     refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he' (Delay.monitor_pos G L t).le) (show (0:ℝ)≤2 by norm_num)).trans_eq ?_; unfold Hx b; ring
  let Z:=b*W t; have hZ:0<Z:=mul_pos hv hf'; let p:= b*Y' t
  have ht : Y t ≤ Y' t:= le_add_of_nonneg_right (by positivity)
  have hc:1≤ Y' t:= hm'.trans ht; have ht' :=zero_lt_one.trans_le hc
  have hpp : 0 < p:= mul_pos hv ht'; have hx': ‖x‖≤ p:= hz.trans (mul_le_mul_of_nonneg_left ht hv.le)
  have hq (a:G.Color)(hz':‖a‖≤ Uniform.shade G*p):= hm a (hz'.trans (le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV ht'.le) (Uniform.shade_pos G).le) ((le_abs_self _).trans hh)))
  let u:= C*(b*Hx t); have h1:Sailor G P.threshold u j:= ⟨fun c i hh=> H c (b*Hx t) (mul_nonneg hv.le hu.le) i (hh.trans (he.trans hA))⟩
  have hW:(j:ℝ)* u≤Z:= by unfold u Z W; nlinarith only [mul_pos hC (mul_pos hv hu)] -- defeq b?
  have hs : 0<Y t:= zero_lt_one.trans_le hm'
  have hQ : j.factorial*d*((1+r)*Z) ≤ p:= by unfold Z p Y'; nlinarith only [mul_pos hv hs]
  have hs:(1+r)*Z ≤ 1:= le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV hf'.le) (show 0≤ 1+r by positivity)) ((le_abs_self _).trans hx)
  refine (polar_price hf hq hpp hx' (rotor hv hc hΦ) hQ hs h1 (mul_pos hC (mul_pos hv hu)) hZ hW hF l hL h).trans_eq ?_
  unfold Q Boulevard.ticket; ring

lemma rim (G:Gauge)(L:Side)(Y:ℝ→ℝ)(hk:Cookie G L Y) : ∀ᶠ t in atTop,
     ∀ (c:Side)(x:Positions (Uniform.Primary c G))(β v:ℝ)(P: BudgetPoint)
        (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]
        (f:Config G c→ E), betaF G t L/2≤ β → ‖x‖≤gStep β*Y t → P.threshold=Pressure.temp t → flags P.threshold (actual x)=∅ → Push.Local.Chart P.order f (actual x) →
        (∀ y:Positions (Uniform.Primary c G), ‖y‖≤ ‖x‖ → actual y∈ Boulevard.sunny P → ∀ l:List (Directions G c),l.length ≤ P.order → (∀ i∈l, ‖i‖ ≤ P.threshold) → ‖leftDerivs f l (actual y)‖ ≤ v) →
        ∀ l:List (Directions G c),l.length ≤ P.order→(∀ i∈l, ‖i‖ ≤ P.threshold) → ‖leftDerivs f l (actual x)‖ ≤ v := by
   obtain ⟨C,hC,H⟩:= expCost G 2 1
   let d t:= Uniform.shade G*(2*gStep (betaF G t L)*Y t)
   let p:= Blaze.royalty G; let P t:= 4*(Boulevard.sunLength C (d t)*p); have hp:0<p:=zero_lt_one.trans_le (royalty_ge G)
   have hd: Rate G L (-(1/2)) d:= (((glim G L).mul hk.uses).mul_left (Uniform.shade G)).weaken (by norm_num)
   have hx := ((((hd.mul_left (1+1)).mul_left (1+Nat.factorial 2*C)).mul_right p).mul_left 4)
   filter_upwards [Delay.shift_pos G L, hd.below (by norm_num) 1 zero_lt_one, Sienna.contraction G L (a:=p) (b:=p) hp (f:=fun t => P t^2) (hx.pow 2) (show -(1/2)*(2:ℕ) < (-(1/2:ℝ)) by norm_num), softly G L] with t ht hd he h' c x β v B E _ _ f hV hX hK hB hF h l hl hL
   have hplus : 0≤ Y t := nonneg_of_mul_nonneg_right ((norm_nonneg _).trans hX) (lamp G L ht β hV).1
   have hm:= Boulevard.sunnySoon C (d t) H x (mul_le_mul_of_nonneg_left (hX.trans (mul_le_mul_of_nonneg_right (lamp G L ht β hV).2 hplus)) (Uniform.shade_pos G).le) ((le_abs_self _).trans hd) hB (show p* (P t)^2<B.threshold*p by
       apply he.trans_le; rw [hK,mul_comm p,Real.rpow_neg ht.le]; exact mul_le_mul_of_nonneg_right h'.2 hp.le)
   let V:= fun i:ℝ=>actual (i • x); rw [← one_smul ℝ x] at hF; have hz : actual x= V 1:=by simp [V]
   have hQ : Push.Local.Chart 0 (leftDerivs f l) (V 1):= Next.Foundations.leftDerivs_chart l 0 (show ContDiffAt _ _ _ _ from hF.of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl))
   have hY:= (Push.Local.chart_comp hQ (fun i=> radiator 1 x i)).continuousAt.norm.tendsto.mono_left (show (𝓝[<] (1:ℝ))≤𝓝 1 from nhdsWithin_le_nhds); rw [hz]
   apply le_of_tendsto hY; filter_upwards [hm,self_mem_nhdsWithin (s:=Set.Iio 1),(eventually_ge_nhds (show (0:ℝ)<1 by norm_num)).filter_mono (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)] with i hi hk hv
   exact h _ (by rw [norm_smul,Real.norm_of_nonneg hv]; exact mul_le_of_le_one_left (norm_nonneg _) (show i≤1 from (show i<1 from hk).le)) hi l hl hL
end YM.RG01Estimate.Receipt
