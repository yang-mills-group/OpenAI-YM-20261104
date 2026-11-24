import YM.RGComparison01.AuxMiles

/-!
# True auxiliary step with the supplied extra model exponent and inserted mark test

Still before recovering marked factorials; exact full output integral of THESE regular
model parts. No set-integral error assumed. Mask: fine-germ only on the flags-empty
side; full-real sup only there. Truncated comparison no continuation of indicator.
Uncertainty past successful germ choice in terms of parameters/correspondence is not
asserted here. Intended to apply when those germs render actual model data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxPackage
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} (A:ChartRatio G) {P : Teller G} {C a u v d s σ : ℝ} {k j n q q' : ℕ} {L: Side}
section pack
variable {c f:Side} {S:StepData c f} (T : Tube G S) (F:Forest S.ratio) (ρ:Bid.Dir G c→AxisChart G F)
 (B:BudgetPoint) (β:ℝ) (i:S.Choices) (e J : Config G f→ℝ)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "M₀" => Lapis.gram F T.up T.high ρ i
local notation "W" => shot A F T ρ i
local notation "b" => gStep β
variable (E U : Poll.Body (Precision.Key F G)→ℝ×Positions (Uniform.Primary c G)→ℝ)

def gross := (Real.exp ∘ e) * J
structure Render (J:Config G f → ℝ) (U : Y→ℝ×Xs→ℝ) (q : ℕ) (a D v : ℝ) : Prop where
  invariant : GaugeInvariant J
  safe : RG.Envelope J
  positive : 0 ≤ v
  allReal (k:Config G f) : flags B.threshold k=∅ → |J k| ≤ v
  healthy (x:Xs) (h:‖x‖ < a) (z:Y) (he: ‖z‖≤D) : flags B.threshold (tests F ρ β x z)=∅→ J (tests F ρ β x z)= b⁻¹^q * U z (b,x)

def bill (q q' n:ℕ) : AuxStage.Co Xs:= AuxFabric.intent (M₀ 0)⁻¹ W E U q q' n
lemma read_render (h : Render F ρ B β e E q a d C)
    (hp : Render F ρ B β J U q' a d v) : Plays A F T ρ B β i (numeric b W U E q q' Real.exp) (gross e J) a d (Real.exp C * v):= by
  have ht:=pays h; have hz : 0 ≤ v:= hp.positive
  refine ⟨fun g U=>by change Real.exp (e (gauge g U))*J _=Real.exp (e U)*J U; rw [h.invariant g U,hp.invariant g U],ht.mul hp.safe, by positivity,fun y hy=>?_,fun y hy z hK hR=>?_⟩
  · unfold gross; simp only [Pi.mul_apply,Function.comp_apply,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_monotone ((le_abs_self _).trans (h.allReal _ hy))) (hp.allReal _ hy) (abs_nonneg _) (Real.exp_pos _).le
  unfold gross numeric; simp only [Pi.mul_apply,Function.comp_apply, Pi.smul_apply, smul_eq_mul,h.healthy y hy z (mem_closedBall_zero_iff.mp hK) hR,hp.healthy y hy z (mem_closedBall_zero_iff.mp hK) hR]; ring
where
  pays (_p' : Render F ρ B β e E q a d C) : Envelope (Real.exp ∘ e):= by
    obtain ⟨p,H⟩:= _p'.safe.cost
    exact ⟨Real.measurable_exp.comp _p'.safe.meas, ⟨Real.exp p, fun u=>by change |Real.exp _|≤_; rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_monotone ((le_abs_self _).trans (H u))⟩⟩
lemma blank_render : Render F ρ B β 0 0 q a d 0:= by
  refine ⟨fun _ _=>rfl,?_,le_rfl,fun _ _=>by simp,fun y hy z h H=>by simp⟩
  exact ⟨measurable_const,0,fun _=> by simp⟩
lemma one_render : Render F ρ B β 1 1 0 a d 1:= by
  refine ⟨fun _ _=>rfl,?_,zero_le_one,fun _ _=>by simp,fun y hy z h H=>by simp⟩
  exact ⟨measurable_const,1,fun _=> by simp⟩
end pack

variable {f X u v w g : ℝ→ℝ} {w' : ℕ} (K: KernelChoices)
local notation "s" => (fun t=> betaF G t L)
variable (n k j q q' : ℕ)

set_option maxHeartbeats 400000 in
lemma plenty (V:ChartPrices) (hv:0 < V.gap) (h: Geo G L f) (hp : Bolt G L X)
    (hr : Geo G L u) (hh : Geo G L v) (hz : Geo G L w) (ht : Geo G L g) (hD : 0 < d) (hA : LocalRatio A)
    (j₁ j₂:ℕ) (hs : n+(q'+q*n)<k) (hn:1≤n) (hk : j<k) (m:ℝ) : ∃ T₀:ℝ→ℝ,Geo G L T₀∧∀ᶠ t in atTop, ∀ (c l:Side) (S:StepData c l) (T:Tube G S) (p:Before G σ C S.patch.J S.kernel (k+3)) (F:Forest S.ratio) (B:BudgetPoint) (i:S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (x:Positions (Uniform.Primary c G)) (V':Teller G) (β : ℝ),
    S.patch.L = L→ S.kernel=K → Quilt T F (X t) → p.tables T.high S.patch=V → Intake V' T t (Pane.virgin T B β) → 1 < w t →
    p.Service F T.high T.up ρ → ∀ Λ, T.up.Bounds T.high σ C Λ → AuxDesk.receipt T p B F ρ i L A d (f t) t β x →
    let D:= wick G L d t; let r:=w t*gStep β
    ‖x‖+furl G L t < r →
    ∀ E U e J, Probe E k j₁ (q+1) r D (u t) (u t) → Probe U k j₂ q' r D (v t) (v t) → Render F ρ B β e E q r D m → Render F ρ B β J U q' r D (g t) →
      AuxStage.Points (T₀ t) r⁻¹ (gStep β) n j (rescale F T A ρ B i β (gross e J)) x (bill A T F ρ i E U q q' n):= by
  let y:= (V.gap/2)⁻¹; have hy : 0<y:= inv_pos.mpr (half_pos hv)
  obtain ⟨Q,hQ,he⟩:= within_core n k j₁ j₂ q q' h hp hr hh hz hD hy hs hn
  obtain ⟨α,hα⟩:=mean_gross (k:=n) hQ hk
  have h':Rate G L 0 (fun t=> Real.exp m * g t) := ht.rate.mul_left _
  let γ:ℝ := -(((n+1:ℕ):ℝ)/2 + 1)
  have hB := resume (σ:=σ) (c':=C) A V hv h' hz.rate hD h.rate hp hA γ α K k j hk
  refine ⟨fun t=>1+Q t,(Geo.fixed 1).joins hQ,?_⟩
  filter_upwards [he,hα,hB,Geo.advance (G:=G) (L:=L) (n+1), upper_guard hz.rate] with t ht hQ hK hγ hW c l S T p F B i ρ x V' β hL ha H Hv hI hw hρ Λ hp R D r hZ E U e J he hg H₀ H₁
  let M:= Lapis.gram F T.up T.high ρ i; let W:= shot A F T ρ i
  let b:=gStep β; have hb := hI.positive; have hh: 0 < b:= (Fare.gS β hb).1
  have hr: s t/2 ≤ β ∧ β ≤ 2*s t:= hL ▸ (show betaF G t S.patch.L / 2 ≤ β ∧ β ≤ 2*betaF G t S.patch.L from hI.window)
  obtain ⟨hF,hβ,hx,hV⟩:=R.1; have hm (z): dotProduct z ((M 0)⁻¹*ᵥ z)≤y*dotProduct z z:= by
    have h := (Lapis.wakes F i T.up T.high ρ σ C Λ p H.large hp hρ 0 (by rw [norm_zero]; exact hF.pos.trans_le hx)).2.2.1 z; rw [Hv] at h; exact h
  let Z:= numeric b W U E q q' Real.exp; let W' := play F T ρ β i Z D
  have hζ := ht β hr.1 hr.2 hw (Positions (Uniform.Primary c G)) _ (Lapis.table F i T.up T.high) (Lapis.mist F A T.up) (Lapis.orbit F ρ) M E U (Lapis.countsK F _ H.overall) hF hm he hg
  have hu i (hy: ‖i‖ < r) : Brush (j+1) ((betaF G t L)^α) 1 W' i:= hQ β hb hr.2 (hβ.le.trans hF.small) (w t) hw _ _ _ _ (hζ i hy)
  have heR:= read_render A T F ρ B β i e J E U H₀ H₁
  have H':= hK _ _ S T F p B ρ β V' i hL ha H Hv hI hw x hZ R Z (gross e J) heR hu
  have hz0 :0 ≤ furl G L t:=Real.rpow_nonneg (hL ▸ (zero_le_one.trans hI.height.le)) _
  have hq:= hζ x (lt_of_le_of_lt (le_add_of_nonneg_right hz0) hZ)
  exact (hq.smaller hk.le).quote (1:ℝ) (H'.climb (by rw [one_mul]; exact hγ β hb hr.2) ((one_le_inv₀ (mul_pos (zero_lt_one.trans hw) hh)).2 ((hW β hr.1 hw).trans hF.small))) zero_le_one hh.le
end YM.RGComparison01.AuxPackage
