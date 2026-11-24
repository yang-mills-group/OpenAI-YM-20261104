import YM.RG01Estimate.InteriorFar
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Courtyard
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable (G:Gauge) (J:KernelChoices) (L:Side)
variable {K d : ℝ} {f D v a C : ℝ→ℝ}
section estimates
variable {c f:Side} {S:StepData c f}

def weight {G : Gauge} (F:Forest S.ratio)(T:Tube G S)(O:ChartRatio G)(l:S.Choices) (ρ:Bid.Dir G c→ AxisChart G F)
    {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (w:ℝ)
    (H:Positions (Uniform.Primary c G)→ Poll.Body (Precision.Key F G)→E)(β:ℝ) (x:Positions (Uniform.Primary c G)):=
      ∫ i,restricted F T O l ρ w (H x) (gStep β,x) i ∂ Poll.sweep (Lapis.gram F T.up T.high ρ l 0)⁻¹
end estimates
-- k = n activation -- BEFORE A
lemma preparation (d K : ℝ) (hd:0<d) (hK:0<K) (j k : ℕ) (m R C : ℝ) {φ a p : ℝ→ℝ}
    (hp : Rate G L 0 p) (hφ : Rate G L 0 φ) (hb : Rate G L C a) (hj:j+1≤k) :
    ∀ᶠ t in atTop,
      let z:= betaF G t L; let D:= wick G L d t; let U:= eaves G L t; let ε:= Real.exp (-(K*D^2/4)/2)
      ∀ (c f:Side)(S:StepData c f)(F:Forest S.ratio)(T:Tube G S)(B:BudgetPoint) (P:Teller G)(β : ℝ) (O:ChartRatio G)(l:S.Choices) (ρ:Bid.Dir G c→ AxisChart G F) (x : Positions (Uniform.Primary c G)),
        (Fintype.card (Bond c):ℝ)≤ φ t → S.patch.L=L → S.kernel=J →
        Intake P T t (Pane.virgin T B β) →
        (∀ y∈ closedBall x (furl G L t), Interior F T O l ρ B β D y U (p t) ε k) →
        1/2 ≤ (Poll.sweep (Lapis.gram F T.up T.high ρ l 0)⁻¹).real (closedBall 0 D) →
        ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
          (g:Config G f→E)(H:Positions (Uniform.Primary c G)→Poll.Body (Precision.Key F G)→E),
        StronglyMeasurable g → GaugeInvariant g → 0≤ a t → (∀ V, ‖g V‖≤ a t * (Pane.virgin T B β).eval V) →
        (∀ y∈ closedBall x (furl G L t),
               Integrable (restricted F T O l ρ D (H y) (gStep β,y)) (Poll.sweep (Lapis.gram F T.up T.high ρ l 0)⁻¹) ∧
               (∀ i, ‖i‖≤ D → g (field F ρ β y i)= (Pane.virgin T B β).eval (field F ρ β y i) • H y i) ∧
               Brush (j+1) (z^R) 1 (weight F T O l ρ D H β) y) →
        Brush j (z^m) 1 ((invoice F T O l ρ β g)-(weight F T O l ρ D H β)) x := by
  let k' := j+1; have hs:1 ≤ k:=by omega
  obtain ⟨Z,hz⟩:=paint_supply G k'
  obtain ⟨c,hc,hU⟩ := Brush.compact (f:=Real.exp) (s:= Set.Icc (-1:ℝ) 1) (k:=k) isCompact_Icc (fun _ _=> Real.contDiff_exp.contDiffAt)
  let z t:= betaF G t L
  let ε t:= Real.exp (-(K*(wick G L d t)^2/4)/2)
  have hr (m:ℝ) : Rate G L m ε:= by
    have he:=Rate.monitor_cutoff (G:=G) (L:=L) (a:=m) (show 0 < K*d^2/8 by positivity) (show 0<(2:ℝ) by norm_num)
    refine he.congr (Eventually.of_forall (fun t=>?_))
    unfold ε; apply congr_arg Real.exp; unfold wick; rw [Real.rpow_two]; ring
  let W t:= clump k' (oat k' (p t) (2*z t)+oat k' (p t) (2*z t)) c* (Token.prime G J k' Z c (2*z t) (φ t)*(a t*(Real.exp 1+ε t)))*3^k'
  have hW : Rate G L ((1*k':ℝ)+(1*k'+(C+0))) W:= ((Token.climbF (Token.oatr k' hp) zero_le_one k' c |>.mul ((Token.primeR φ J hφ).mul (hb.mul ((Rate.const _).add (hr 0))))).mul_right _)
  let X := (1*k':ℝ)+(1*k'+(C+0)); let A:=max X R
  have hA := (hW.weaken (le_max_left X R)).add ((Rate.power (G:=G) (L:=L)).weaken (le_max_right X R))
  obtain ⟨η,hη⟩:= Lantern.iteration G L j (a:=1) (m:=m) (d:=A+1) zero_lt_one
  filter_upwards [Delay.shift_pos G L, ((Lantern.fareRate k hp (gen G L d)).mul (edge G L)).below (by simp [vow_ok]) 1 zero_lt_one,
    (hb.mul (hr (η-C-1))) η (by linarith), hA (A+1) (lt_add_one _), hη]
    with t hv hh hk ht ht' b D U ε' c' f S F T B P β O l ρ x hK' hL hJ pH hy hB E _ _ _ g H hG hΨ hα hkV hM
  have hβ : 0<β:= pH.positive; have hP:β≤2*b:= by unfold b; exact hL ▸ (show β ≤ 2*betaF G t S.patch.L from pH.window.2)
  subst J
  let s:= closedBall x (furl G L t)
  let f' y:= invoice F T O l ρ β g y - weight F T O l ρ D H β y
  apply ht'
  · change ∀ y∈s,Brush k' (b^(A+1)) 1 f' y; intro y hi
    have he:= hy y hi
    let Y:=Lapis.orbit F ρ; let q:= Lapis.gram F T.up T.high ρ l
    let C:= ratify (Lapis.table F l T.up T.high) (mist F O T.up) Y q D (gStep β,y)
    have hh : fee k (p t) D* max U U≤ 1:= by rw [max_self]; exact (le_abs_self _).trans hh
    have hv : ‖gStep β‖ < U:= by rw [Real.norm_of_nonneg (gS β hβ).1.le]; exact he.room.2
    have hC:C≤Real.exp 1:=
       (temperature D he.calcJ he.center hv hs hh (burs D he.calcJ he.center hv hs hh hU hc.le).2 hB).2
    obtain ⟨h₀,hB⟩:= primeN (G:=G) S.kernel (n:=k') hβ hP hc.le hz.1.le ((Nat.cast_nonneg _).trans hK')
    have hm:=gross F T O l ρ B β D pH he hG hkV hα hC ((hU 0 (by norm_num)).smaller hj) hz hK' h₀ hj
    refine (hm.climb ?_ le_rfl|>.separating (hM y hi).2.2).climb ((le_abs_self _).trans ht) le_rfl
    unfold W
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hp: 0 ≤ p t := (he.calcJ.curve y he.center).nonneg
    have ho:= Token.rung (j:=k') hβ.le hp hP
    have hv : 0 ≤ Token.oat k' (p t) β+Token.oat k' (p t) β:= (Token.octane F T O ρ β l hj he.center he.calcJ hβ).nonneg
    have hf:= Token.rising k' hv (add_le_add ho ho) hc.le
    have hK:0≤ε' := (Real.exp_pos _).le
    exact mul_le_mul hf (mul_le_mul_of_nonneg_right hB (by change 0≤ a t *(Real.exp 1+ε'); positivity)) (by positivity) (le_trans (by unfold clump; positivity) hf)
  change ∀ y∈s, ‖f' y‖ ≤ b^η; intro y hi; obtain ⟨ht,hv,-⟩:= hM y hi
  apply (reduced_pricing F T O l ρ B β D pH (hy y hi) hG hkV hα hΨ (H y) hv ht).trans
  exact (le_abs_self _).trans hk
end YM.RG01Estimate.Courtyard
