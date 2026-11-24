import YM.GapsR2RG.Anchor
/-!
# Re-expression of affine-null plus flag variation by one genuine integrated
field direction at an intermediate stop. No comparison of separately-shot
trajectories. Motivated by Extra.Histories.Relay's exact match-up on finitely
many fixed scales. All flagged terms paid on same D before dilution. Prices as
in `Tab` (at rate and its κ over the actual forced cap). Quiet before exponent:
define the one-linear derivative value as full represented insertion (on log
AND actual gas). Not formula for changing β/clipping through the trajectory.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.GapsR2RG.Anchor
open Lattice Wilson RG RG.Activities PhysicalNext PhysicalNext.JointLoad.Heir
open Labels Source Function Filter Set MeasureTheory Finset Extra.Histories
open scoped Classical Topology Matrix.Norms.Frobenius ContDiff BigOperators
set_option quotPrecheck false
variable {G:Gauge}{n:Side}(D:Rep G n)
noncomputable section
protected structure Stratum (G:Gauge) (n:Side) where
   stencil : ℕ → Support n
   logit : ℕ → Config G n → ℝ
   flag : ℕ → Config G n → ℝ
structure Affidavit (T:Anchor.Stratum G n)(t ρ:ℝ) : Prop where
   regular (i): Seed D.p 0 (T.stencil i) (T.logit i)
   eligible(i:ℕ)(U:Config G n) : T.flag i U≠0  →  (D.activities.forced i).eligible D.p.threshold U
   carried(i:ℕ) : T.flag i ≠0  →  0∈ (D.activities.forced i).support
   invariant : ∀ i,GaugeInvariant (T.flag i)
   reads : ∀ i,UsesFinal D.p.threshold (D.activities.forced i).support (T.flag i)
   measurable : ∀ i,Measurable (T.flag i)
   budget : ∃ b c:ℝ,0≤b ∧ 0≤c ∧ b + c ≤ ρ ∧ 0<t∧ (∃ f:ℕ → ℝ,SumBudget (fun i=> D.p.mass (T.stencil i) (f i)) b ∧ ∀ i,D.p.supBounds 0 (T.stencil i) (T.logit i) (f i)) ∧
      ∃ f:ℕ → ℝ, SumBudget (fun i=> D.p.mass (D.activities.forced i).support (f i)) (t*c) ∧ ∀ i,0≤f i ∧ ∀ U,‖T.flag i U‖≤ f i

noncomputable def responseAt (Q:Anchor.Stratum G n)(U:Config G n):ℂ :=
   D.eval U * (∑' i:ℕ,Complex.ofReal (masked D.p.threshold (Q.stencil i) (Q.logit i) U)) + (Real.exp (D.exponent U):ℂ)* ∑' (s:Finset ℕ),
       if D.activities.admissible D.p U s then ∑ i ∈ s, Complex.ofReal (Q.flag i U) * ∏ j ∈ s.erase i,(D.activities.K j U:ℂ) else 0

noncomputable def sheath {d}(F:Labels.Frame G d) (Q:Anchor.Stratum G n): Coefficient F n := ⟨0,Q.stencil,fun i=>Complex.ofReal ∘ Q.logit i, fun i=>Complex.ofReal ∘ Q.flag i⟩

variable {D}{t ρ:ℝ} (F:Labels.Frame G 4) (H:Hol G) (Q:Anchor.Stratum G n)
include Q
lemma recognized (J: SectionData F) : (Anchor.sheath F Q).density 0 J D = responseAt D Q :=by
  let T:=sheath F Q; change T.density 0 J D = _; unfold Coefficient.density Coefficient.exponentialEntry responseAt; have hx:T.x=0:=rfl
  simp only [hx,map_zero,show J.places 0 (0:Site n)=fun _=>0 from funext fun U=> by simp [SectionData.places,SectionData.evaluate], Pi.zero_apply]
  funext U
  congr 2
  · have hy:masked D.p.threshold (J.footprint 0) (fun _=> (0:ℂ)) U=0:=by by_cases hu : Healthy D.p.threshold (J.footprint 0) U <;> simp [hu]
    simp only [hy,zero_add]
    apply tsum_congr; intro i; by_cases hS:Healthy D.p.threshold (Q.stencil i) U
    · simp [Coefficient.maskedTerm,T,sheath,hS]
    simp [Coefficient.maskedTerm,T,sheath,hS]

variable (h:Affidavit D Q t ρ) (hc:G.Simple) (hn:4≤n.val)
include h hc hn H F
lemma contractS : let T:=sheath F Q; T.Format 0 H D ∧ T.remBound 0 D t ρ :=by
  intro T
  refine ⟨⟨fun i=> PhysicalNext.Repeat.Blush.ornate (h.regular i).good,fun i=> (h.regular i).site, fun i=> by change Complex.ofReal _=_; rw [(h.regular i).value]; rfl, fun i hx=> survey H _ hc (h.regular i) hx hn, fun i U hf=>h.eligible i U (fun he=> hf (congr_arg Complex.ofReal he)), fun i hi=>h.carried i (fun he => ?_), fun i j U=>congr_arg Complex.ofReal (h.invariant i j U),fun i U V ha hb=> congr_arg Complex.ofReal (h.reads i U V ha hb), fun i=> Complex.continuous_ofReal.measurable.comp (h.measurable i)⟩,?_⟩
  · exact hi (funext fun z=> (show Complex.ofReal (Q.flag i z) = _ from congr_arg Complex.ofReal (congr_fun he z)))
  obtain ⟨b,c,hb,hv,hr,ht,⟨f,hf,hB⟩,g,hg,hG⟩:=h.budget
  refine ⟨b,c,hb,hv,hr,ht,⟨f,hf,fun i=>⟨(hB i).1,fun U hx l hl hy=>?_⟩⟩,g,hg,fun i=>⟨(hG i).1,fun U=> (Complex.norm_real _).trans_le ((hG i).2 U)⟩⟩
  change ‖leftDerivs (Complex.ofRealCLM ∘ Q.logit i) l U‖ ≤ _
  rw [Push.Local.left_linear Complex.ofRealCLM _ ((h.regular i).good.smooth U hx) hl]; change ‖Complex.ofReal (leftDerivs (Q.logit i) l U)‖ ≤ _; rw [Complex.norm_real]; exact (hB i).2 U hx l hl hy

lemma fees : let T:=sheath F Q; F.coeffSize T.x + ρ ≤ ρ:=by intro T; change F.coeffSize 0 + _ ≤_; simp [Frame.coeffSize]
end
end YM.GapsR2RG.Anchor
