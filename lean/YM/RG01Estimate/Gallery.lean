import YM.RG01Estimate.ValueRead
/-!
# Real analytic (Taylor) readiness for the local cut-torus numerator

ALL derivative orders through n, with any larger contour order k, actual β and step.
All scalar multiplications inside earned logs together. Comparing with coefficients in
ordinary normalized b requires a separate coefficient identification. Don't recombine at
other gauges or periods without locality receipts; use with producer's stencil budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G:Gauge)(L:Side)(K:KernelChoices)
lemma read_shape (n k i j:ℕ)(h₁:n+1 ≤ k)(hn:n+j ≤ k) (m δ d c :ℝ) (hδ:0<δ) (hd:0<d) (hc:0<c)
    (w Y p v C' F V : ℝ→ℝ)(hw: Rate G L m w)(hY: Cookie G L Y)(hC:Cookie G L p)(hF:Bolt G L F)
    (hv:Rate G L 0 v)(hV:Cookie G L V)(hk:Cookie G L C') :
   ∃ J:ℝ→ℝ, Cookie G L J ∧ ∀ᶠ t in atTop,
      let β₀:= breath G L t; let e:=Real.exp (-(δ*(wick G L d t)^2/4)/2)
      let u:=eaves G L t; let D:= wick G L d t
      ∀ (c₀ f:Side)(S:StepData c₀ f)(A:Forest S.ratio)(T:Tube G S)(B:BudgetPoint)(P:Teller G)(β:ℝ)(O:ChartRatio G)(l:S.Choices)(ρ:Bid.Dir G c₀→AxisChart G A),
       let Z':= ball (0: Positions (Uniform.Primary c₀ G)) (Y t)
       let M:= (Lapis.gram A T.up T.high ρ l 0)⁻¹
       S.patch.L=L→ S.kernel=K→ (Fintype.card (Bond c₀):ℝ) ≤ v t →
       (Fintype.card (Precision.Key A G):ℝ) ≤ F t → 1 ≤ F t → 1 ≤ Y t → 0 ≤ w t →
       Intake P T t (Pane.virgin T B β) → M.PosDef → (∀ z, dotProduct z (M *ᵥ z) ≤ c* dotProduct z z)→
       ∀ y∈ Z', let g:= gStep β; let U:= closedBall (g • y) (furl G L t)
                (∀ x∈ U,g⁻¹ • x ∈ Z' ∧ Interior A T O l ρ B β D x u (p t) e k) →
       ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](f₁:Config G f → E)
         (H : Poll.Body (Precision.Key A G) → ℝ × Positions (Uniform.Primary c₀ G) → E),
        StronglyMeasurable f₁ → GaugeInvariant f₁ → (∀ x, ‖f₁ x‖≤ w t * (Pane.virgin T B β).eval x) →
        (∀ x∈U, ∀ z:Poll.Body (Precision.Key A G), ‖z‖≤ D→
             f₁ (field A ρ β x z)= (Pane.virgin T B β).eval (field A ρ β x z) • H z (g, g⁻¹ • x)) →
        Roll H (closedBall 0 D) Z' β₀ (C' t) k → Atlas H Z' i k (V t) → 0 ≤ V t →
        Brush n (g^j*J t) 1 ((organic A T ρ l O β f₁) - (purses A T ρ l O H β j)) y ∧
           (∀ L< j, Brush (k-L) (J t) 1 (Laplace.step (fill A T ρ l O H) Set.univ (Poll.sweep M) L) y) := by
  obtain ⟨Ψ,hΨ,H'⟩:= Brush.compact (f:=Real.exp) (k:=k) (s:=Set.Icc (-1:ℝ) 1) isCompact_Icc (fun x _=> Real.contDiff_exp.contDiffAt)
  let Φ (v W U:ℝ):= clump k (clump k (Courtyard.expense k v) (fee k W U)) Ψ
  let B t:= betaF G t L
  let C t:= Φ (Y t) (p t) (Sienna.wick G L d t)*C' t*3^k
  let U t:= Φ (Y t) (p t) 1 * V t *3^k; let l:= priceExponent k+i
  let s t:= U t* PolyGauss.costs l (F t) c
  let X t:= C t+U t*(j+1)+1; let J t:= X t+s t
  have hp (g:ℝ→ℝ)(h:Cookie G L g) : Cookie G L (fun t=> Φ (Y t) (p t) (g t)) := ((hY.expense k).lump (hC.charged h _) _).lump (Cookie.const _) _
  have hT : Cookie G L C:= ((hp _ ((Cookie.const _).pays Cookie.mast)).pays hk).pays (Cookie.const _)
  have hU : Cookie G L U:= ((hp _ (Cookie.const _)).pays hV).pays (Cookie.const _)
  have hX : Cookie G L X:= (hT.joins (hU.pays (Cookie.const _))).joins (Cookie.const 1)
  -- charge n+1 invoice as inverse g derivatives. enough exponent Q
  let ε := -(j:ℝ)
  let P:= 0+1*((n+1:ℕ):ℝ)
  have hs := (hT.uses.mul (((Rate.const (G:=G) (L:=L) 1|>.weaken (show (0:ℝ)≤1 by norm_num)).add (Rate.hat (G:=G) (L:=L))|>.pow (n+1)))) (P+1) (by unfold P; linarith)
  refine ⟨J,hX.joins (hU.pays (Cookie.bolt (PolyGauss.costs_poly l F hF c))),?_⟩
  have hw':= Lantern.walls G L hF hc hd (-(1:ℝ))
  have hW:= PolyGauss.walls l c d ε hc hd hF
  have ht:= Courtyard.preparation G K L d δ hd hδ n k ε (P+1) m hC.uses hv hw h₁
  filter_upwards [hs,hw',hW,ht,funding k d hC.uses hY.uses,(Work.E09.betaF_growth G L).eventually_ge_atTop 4] with t hs hw₀ hh ht hB h₀ β₀ e u D c₀ f S A T B₀ P' β O l' ρ Z M hL hK htB htM hF hY hW pH hM hc y hy g U' hY' E' _ _ _ f₁ H h₁' hGI hRate hZ hR hA hV
  let z:= betaF G t L
  have hB' : 4≤ z := h₀; have hx : 0< z:= by linarith
  have hP : 0<β:=pH.positive; have hg:0<g:= (gS β hP).1; obtain ⟨hrB,hgY,hF₁,hK₁,hm⟩:= hB
  have hZ₁ : z/2 ≤ β:= by unfold z; exact hL ▸ pH.window.1
  have hZ₂ : β≤2*z:=by unfold z; exact hL ▸ pH.window.2
  have he : g < β₀:=hm β hZ₁; let σ := closedBall (0:Poll.Body (Precision.Key A G)) D
  have h' : 0 ≤ D:= mul_nonneg hd.le (Delay.monitor_pos G L t).le
  have hKx : g • y ∈ U':= mem_closedBall_self (Real.rpow_nonneg hx.le _)
  have h : Interior A T O l' ρ B₀ β D (g • y) u (p t) e k:= (hY' _ hKx).2
  have hz:(g,y)∈corridor β₀ Z:= ⟨mem_ball_zero_iff.mpr (by rw [Real.norm_of_nonneg hg.le]; exact he),hy⟩
  have hO : Roll (fill A T ρ l' O H) σ Z β₀ (C t) k:= hR.active (near_formula h.calcJ hY hrB hgY (by omega) hK₁ H')
  have hA' : Atlas (fill A T ρ l' O H) Z l k (U t) := hA.active (atlas_formula h.calcJ (mul_pos hd (Delay.monitor_pos _ _ _)) (by omega) hY hΨ.le H')
  have hUC: 0≤ C t:= (hO.occupied 0 (mem_closedBall_self h') _ hz).nonneg
  have hV : 0 ≤ U t:= by
      have hp : 0 ≤ p t := (h.calcJ.curve _ h.center).nonneg
      have he : 0 ≤ Y t := zero_le_one.trans hY
      unfold U Φ expense Lantern.fee acrossE spanE clump; positivity
  have hΦ: (1/2:ℝ) ≤ (Poll.sweep M).real σ:= by
      have h:= hw₀ _ _ htM hM hc; change 1-_ ≤ z ^ (-(1:ℝ)) at h
      rw [Real.rpow_neg hx.le, Real.rpow_one] at h
      have he' : z⁻¹ ≤ (4:ℝ)⁻¹ := inv_anti₀ (by norm_num) hB'
      unfold σ; change _ ≤ (Poll.sweep M).real _; unfold D wick; linarith only [h, he']
  have hη := roots t β h₀ hP hZ₂
  have hc' : Brush n (z^ε) 1 (invoice A T O l' ρ β f₁ - weight A T O l' ρ D (pullF A H β) β) (g • y) := by
      refine ht _ _ S A T B₀ P' β O l' ρ _ htB hL hK pH (fun _ hu=> (hY' _ hu).2) hΦ E' f₁ (pullF A H β) h₁' hGI hW hRate ?_
      intro x hx'; obtain ⟨he',hx⟩:= hY' x hx'
      have h': (g,g⁻¹ • x) ∈ corridor β₀ Z:= ⟨(show g∈ ball (0:ℝ) β₀ from hz.1),he'⟩
      refine ⟨?_,hZ _ hx', (Laplace.charged A T ρ l' O H β D x hP (hO.of_le le_rfl le_rfl h₁) hUC h').climb ?_ le_rfl⟩
      · rw [Laplace.token A T ρ l' O H β D hP]; exact internal _ _ Z _ hO hUC _ h'
      exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one (inv_pos.mpr hg).le) (add_le_add_right hη.2 1) (n+1)) hUC) ((le_abs_self _).trans hs)
  let u':= PolyGauss.costs l (F t) c; have hu:0 ≤ u':= by unfold u' PolyGauss.costs; positivity
  have hl: z^ε ≤ g^j:= by
       apply le_trans _ (pow_le_pow_left₀ (Real.rpow_pos_of_pos hx (-(1:ℝ))).le hη.1 j)
       rw [← Real.rpow_mul_natCast hx.le] -- edit
       unfold ε; rw [neg_one_mul]
  refine ⟨(collects A T ρ l' O H β D y hn hP (he.le.trans hF₁) hM hc htM hF hO hA' hV hUC hz (hh _ _ htM hF hM hc) hc').climb ?_ le_rfl,fun i hi=>?_⟩
  · rw [abs_of_nonneg hg.le]; unfold J X; refine le_trans (add_le_add hl (add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hV) (Nat.cast_nonneg _)))) ?_
    change g^j+(_*_+j * (U t * g^j))≤ g^j*((_+U t*((j:ℝ)+1)+1)+U t*u'); nlinarith only [mul_nonneg hV (pow_nonneg hg.le j), mul_nonneg (pow_nonneg hg.le j) (mul_nonneg hV hu)]
  have hT:= PolyGauss.total hc hM l _ hF htM
  have h:= (receives Z _ Set.univ M hA' isOpen_ball hV y hy i (show i≤k by omega) hT.1.integrableOn).2
  apply h.climb _ le_rfl; rw [setIntegral_univ]; unfold J; have he:0≤X t:= by unfold X; positivity
  exact (mul_le_mul_of_nonneg_left hT.2 hV).trans (le_add_of_nonneg_left he)
end YM.RG01Estimate.Laplace
