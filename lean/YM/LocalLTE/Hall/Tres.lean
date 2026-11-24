import YM.LocalLTE.Hall.Scale
/-! # Re-box in curved coordinates, maintaining ambient jets -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (R : ChartRatio G)
    (ρ:Bid.Dir G c→AxisChart G F) (o:S.Choices)(p :ℕ)
open Frame
variable (t D' β α x:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "U"=> Sienna.eaves G L t
local notation "D"=> wick G L D' t
local notation "φ"=> joint F T R ρ D o
local notation "h₁"=> cedar F T ρ o
local notation "h₂"=> shed F T R ρ α o
variable {a b n₀ n₁ n₂ C M V Q c' v : ℝ} {A:ChartRatio G}
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E](f': E→ Positions (Uniform.Primary c G))
variable {κ V₀ : ℝ}{j n : ℕ}
lemma crosses {H H' E: Type} [NormedAddCommGroup H][NormedSpace ℝ H] [NormedAddCommGroup H'][NormedSpace ℝ H'][NormedAddCommGroup E][NormedSpace ℝ E] {x:E}
   (G':E→H)(h:Brush j Q 1 G' x) (e:H') (ht:‖e‖≤Q) : Brush j (2*Q) 1 (fun i=>(e,G' i)) x:= by
   let P : H →L[ℝ] H' × H:= ContinuousLinearMap.inr ..
   have he:‖P‖≤1:= ContinuousLinearMap.opNorm_le_bound P zero_le_one (fun x=>by rw [one_mul]; change ‖((0:H'),x)‖≤_; simp)
   let W: E→H'×H:=fun _=>(e,0); have hx: Brush j Q 1 W x:= (Brush.certified zero_le_one (e,(0:H))).climb ((show ‖(e,(0:H))‖=‖e‖ from (by simp)).trans_le ht) le_rfl
   rw [two_mul]; have hh:= h.report P he; rw [one_mul] at hh
   apply (hx.gathering hh).shimmy; filter_upwards with t; change (e,G' t) = (e,0)+(0,G' t); simp -- edit
-- only infer implicit radius from t
set_option quotPrecheck false
def feeS (j n:ℕ)(M K:ℝ):= (n:ℝ)*(2*M*K^n)*(1+(n:ℝ))^j
variable {v₁ v₂ s q g:ℝ}{J: ℕ}
def bundleS (j p:ℕ)(M H₀ T Λ β:ℝ) := feeS j (p+1) M (2*Λ) + β*feeS j (p+3) H₀ Λ + feeS j (p+1) T Λ
lemma listens (x':E) (j:ℕ)(M' K c₀ C:ℝ)(hz: ‖g‖ ≤ 1) (hq: 1 ≤ M')(hp: Brush j M' 1 f' x')(hc:0 ≤ K)(hf:0 ≤ c₀)(ha:0 ≤ C) (h:∀ (i:ℕ), i ≤ p→ i>0→ normJ i (joint F T R ρ (wick G L D' t) o) 0≤ K) (h₂' :∀ (i:ℕ), i ≤ p→i>0→normJ i (shed F T R ρ α o) 0 ≤ C)(h₃' :∀ (i:ℕ), i ≤ p+2→i>0→ normJ i (cedar F T ρ o) 0 ≤ c₀) : Brush j (bundleS j p K c₀ C M' (g⁻¹^2)) 1 (fun u=> Shellac.off (song F T R ρ (wick G L D' t) α o p g) (f' u)) x':=by
    have hz:=hz.trans hq; have hx: M' ≤ 2*M':=by linarith
    have hk i (hi: i < p+1) (hp : i>0): normJ i (joint F T R ρ (wick G L D' t) o) 0 ≤ K := h _ (by omega) hp
    have hy: ‖((g,(0:Xs)))‖ ≤ 2*M':= by rw [Prod.norm_mk]; exact max_le (hz.trans hx) (norm_zero.trans_le (by linarith only [hq]))
    have hA:= crosses f' hp g hz
    have he:=rotunda hk (g,0) (hq.trans hx) hy hc hA
    have hh:=rotunda (f:= shed F T R ρ α o) (b:=C) (n:=p+1) (s:=M') (fun i hi hp=> h₂' i (by omega) hp) 0 hq (by simp; positivity) ha hp
    have hv:=(rotunda (f:= cedar F T ρ o) (b:=c₀) (n:=p+3) (s:=M') (fun i hi hp=> h₃' i (by omega) hp) 0 hq (by simp; positivity) hf hp).smul (g⁻¹^2); rw [Real.norm_of_nonneg (sq_nonneg _)] at hv
    apply ((he.gathering hv).gathering hh).shimmy; filter_upwards with t; unfold off song; simp only [Pi.sub_apply,smul_eq_mul]; ring

lemma channeled (x':Xs) (j:ℕ) (M' K c₁ C:ℝ) (hs: Reliable G κ V₀) (hh: ‖x'‖ < v) (hY: ∀ (x:Xs), ‖x‖ < v →∀ i:G.El, Brush j M' 1 (Frame.convertLinks Chi.canonical κ i ∘ Boulevard.actual) x)(hz: ‖g‖ ≤ 1) (hq: 1 ≤ M')(hc:0 ≤ K)(hf:0 ≤ c₁)(ha:0 ≤ C) (h:∀ (i:ℕ), i ≤ p→ i>0→ normJ i (joint F T R ρ (wick G L D' t) o) 0≤ K) (h₂' :∀ (i:ℕ), i ≤ p→i>0→normJ i (shed F T R ρ α o) 0 ≤ C)(h₃' :∀ (i:ℕ), i ≤ p+2→i>0→ normJ i (cedar F T ρ o) 0 ≤ c₁) :
    Brush j (bundleS j p K c₁ C M' (g⁻¹^2)) 1 ((Boulevard.stillA (Frame.placed Chi.canonical κ (song F T R ρ (wick G L D' t) α o p g))) ∘ Boulevard.actual) x':=by
      let f:=song F T R ρ (wick G L D' t) α o p g; let X' (x:Xs) (u:G.El):= Frame.convertLinks Chi.canonical κ u (Boulevard.actual x)
      let K' (x:Xs)(u:G.El) := Shellac.off f (X' x u)
      let z:=bundleS j p K c₁ C M' (g⁻¹^2)
      have hc' := (smoothSong F T R ρ (wick G L D' t) α o p g j).continuous
      have hh' (x:Xs):Continuous (X' x):= by
         let u₁:=Frame.convertLinks (G:=G) Chi.canonical κ 1 (Boulevard.actual x); have he (i:G.El) : X' x i=Frame.adj i u₁:= by unfold X' u₁; simpa only [mul_one] using (Frame.motion (x:=i) hs (1:G.El) (Boulevard.actual x) (χ:=Chi.canonical))
         rw [funext he]; exact Frame.adj_el u₁
      have h' x : Continuous (K' x):= (hc'.sub continuous_const).comp (hh' x)
      have hP : ∀ᶠ y:Xs in 𝓝 x',∀ i:G.El, Brush j z 1 (fun u=>K' u i) y:=by
         filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hh)] with y hy i
         exact listens F T R ρ o p _ _ _ (fun y=>X' y i) y j M' K c₁ C hz hq (hY _ hy i) hc hf ha h h₂' h₃'
      obtain ⟨hT,-⟩:= Meristem.points K' G.probHaar ⟨fun _=>_,integrable_const _,hP⟩ (Eventually.of_forall fun x=> (h' x).measurable)
      apply (hT.buds _ (integrable_const _) zero_le_one (show (∫ _:G.El,z ∂G.probHaar)≤z from (by simp)) (ae_of_all _ hP.self_of_nhds)).shimmy
      filter_upwards with i; unfold Boulevard.stillA; rw [Function.comp_apply,Frame.meansRead hs,Frame.meansRead hs]; simp_rw [boundFlat hs]; unfold K' Shellac.off; simp_rw [Pi.sub_apply]; exact (integral_sub (μ:=G.probHaar) ((hc'.comp (hh' i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const (f 0))).symm
end YM.LocalLTE.FrameBox.Hall
