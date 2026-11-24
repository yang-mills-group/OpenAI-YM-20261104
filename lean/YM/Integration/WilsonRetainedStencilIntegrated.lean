import YM.Integration.WilsonRetainedStencilPhysical
import YM.Integration.WilsonRetainedStencilMoment

/-! The signed error against the original joint Haar and Gaussian law, with
one constant fixed before the regulator and the individual marked partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedStencilIntegrated
open Function Filter Lattice RG Pressure Tree Wilson Source ConnectedActivityE6
open Coat Census Control Window RGLocalTaylor RGLocalTaylor.Insert PhysicalNext.Repeat.Legato
open Finset MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)
variable {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {P:Teller G}
open WilsonCoherentMayerProjection WilsonRetainedStencilMoment

private theorem finite (o:I→Site f) (X:Coat T F) (p:ℕ):
    Integrable (fun z:Air f G=>‖restrict R d F o z‖^(p+1)) X.dice:=by
  let L':=restrict R d F o
  haveI:IsGaussian X.dice:=inferInstanceAs (IsGaussian (multivariateGaussian 0 X.relating))
  have hn:Integrable (fun u:Panels R d=>‖u‖^(p+1)) (X.dice.map L'):=
    MemLp.integrable_norm_pow' (p:=p+1) (f:=id) (IsGaussian.memLp_id (X.dice.map L') _ (by simp))
  exact (integrable_map_measure (by fun_prop) L'.continuous.aemeasurable).mp hn

/-- Price after the paid matrix has been chosen. The multiplier can depend
on both the Haar and the Gaussian coordinates, with arbitrary correlations. -/
theorem under (o:I→Site f) (X:Coat T F) (p:ℕ) {K weight fee:ℝ} (hw:0≤weight) (hf:0≤fee)
    (cap:(∫ z:Air f G,‖restrict R d F o z‖^(p+1) ∂X.dice)≤K)
    (W D:momentSpace X→ℝ) (whole:Measurable W) (err:Measurable D)
    (wm:∀z,|W z|≤weight) (dm:∀z,|D z|≤fee*‖restrict R d F o z.2‖^(p+1)) :
    Integrable (fun z:momentSpace X=>W z*D z) (moment X) ∧
      (∫ z:momentSpace X,|W z*D z| ∂moment X)≤weight*(fee*K) :=by
  let coeff:=weight*fee
  let momentCost (w:Air f G):=‖restrict R d F o w‖^(p+1)
  have bounded (z:momentSpace X):|W z*D z|≤coeff*momentCost z.2:=by
    rw [abs_mul,mul_assoc]
    exact mul_le_mul (wm z) (dm z) (abs_nonneg _) hw
  have hg:Integrable (fun z:momentSpace X=>coeff*momentCost z.2) (moment X):=
    ((finite R d o X p).comp_snd (F.order G)).const_mul coeff
  have hi:Integrable (fun z:momentSpace X=>W z*D z) (moment X):=
    hg.mono' (whole.mul err).aestronglyMeasurable (Eventually.of_forall bounded)
  refine ⟨hi,(integral_mono hi.norm hg bounded).trans ?_⟩
  change (∫ z:momentSpace X,coeff*momentCost z.2 ∂(F.order G).prod X.dice)≤_
  rw [integral_const_mul,integral_fun_snd]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  exact (mul_le_mul_of_nonneg_left cap (mul_nonneg hw hf)).trans_eq (mul_assoc ..)

/-- Uniform funding of the signed conditional estimate for every physical
coat admitted by the original construction. -/
theorem purchased (P:Teller G) (L:Side) (D:Patch) (hd:D.Branches P.bind G) (p:ℕ) :
    ∃ K:ℝ,0≤K ∧ ∀ᶠ s:ℝ in atTop, ∀ (c f:Side) (S:StepData c f) (T:Tube G S)
    (F:Forest S.ratio) (X:Coat T F), X.x=s → S.patch=D → S.patch.L=L →
      Room P S T s → X.manifest → ∀ o:I→Site f, ∀ {weight fee:ℝ},0≤weight→0≤fee→
        ∀ W D':momentSpace X→ℝ,Measurable W→Measurable D'→(∀z,|W z|≤weight)→
          (∀z,|D' z|≤fee*‖restrict R d F o z.2‖^(p+1))→
          Integrable (fun z:momentSpace X=>W z*D' z) (moment X) ∧
          (∫ z:momentSpace X,|W z*D' z| ∂moment X)≤weight*(fee*K) :=by
  obtain ⟨η,r,Q,Y,_,good⟩:=shoots P L D hd
  let K:=‖restore R d‖^(p+1)*((Fintype.card (Keys R d):ℝ)*
    ((Real.sqrt (payE η r Q (tubularPrice G L)))^(p+1)*unitMoment (p+1)))
  have non:0≤unitMoment (p+1):=integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) _)
  refine ⟨K,by unfold K; positivity,?_⟩
  filter_upwards [good] with s forts c f S T F X hx hd hl room hm o weight fee hw hf
  exact under R d o X p hw hf (WilsonRetainedStencilMoment.purchased R d F o (forts c f S T F X hx hd hl room hm) p)

end YM.Integration.WilsonRetainedStencilIntegrated
