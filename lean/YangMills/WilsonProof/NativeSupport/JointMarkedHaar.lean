import YangMills.WilsonProof.NativeSupport.JointPhysicalPush

/-! A finite product of bounded tests of actual tagged blocking energies
preserves the held-field gauge symmetry through every original unsliced
step. The finite-volume norm here serves only to justify Haar integration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointPhysical
open Function Filter Lattice RG Pressure Tree Wilson Finset MeasureTheory
open Push Push.BetaTransport Push.AbsoluteSums Push.SectorMeasure
open scoped Topology BigOperators Classical
variable {G:Gauge} {c f:Side} (S:StepData c f)
variable (J:Finset (Bond c)) (h:Bond c → ℝ → ℝ) (β:ℝ) {g:Config G f → ℝ}
variable (ok:S.patch.Branches S.kernel G) (hg:Envelope g)
variable (hm:∀ b∈J,Measurable (h b)) (hu:∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖ ≤ 1)

include ok hg hm hu in
theorem marked_joint_envelope (k:S.Choices) :
    Envelope fun z:Config G f × Config G c=>integrand S k J h β g z.2 z.1 := by
  have inner:Envelope (fun z:Config G f × Config G c=>g z.1) :=
    ⟨hg.meas.comp measurable_fst,hg.cost.choose,fun z=>hg.cost.choose_spec z.1⟩
  exact ((env_tagged β k ok measurable_fst measurable_snd).mul inner).mul
    (sample_env S k J h ok measurable_fst measurable_snd hm hu)

include ok hg hm hu in
theorem push_envelope : Envelope (push S J h β g) := by
  let E:=marked_joint_envelope S J h β ok hg hm hu
  let C k:=(E k).cost.choose
  refine ⟨Finset.measurable_fun_sum _ (fun k _=>(E k).meas.stronglyMeasurable.integral_prod_left'.measurable),
    ∑ k,C k,fun V=>?_⟩
  apply (norm_sum_le _ _).trans (sum_le_sum fun k _=>?_ )
  have bound := norm_integral_le_of_norm_le (μ:=prior G f) (f:=integrand S k J h β g V)
    (integrable_const (C k)) (Eventually.of_forall fun U=>(E k).cost.choose_spec (U,V))
  simpa only [integral_const,probReal_univ,one_smul] using bound

include ok hg hm hu in
theorem push_gauge (sym:GaugeInvariant g) : GaugeInvariant (push S J h β g) := by
  intro k V
  let z:=k ∘ S.ratio.parent
  have lifted:z ∘ S.ratio.embed=k := funext fun i=>congrArg k (S.ratio.embed_parent i)
  apply sum_congr rfl
  intro t _
  let F:=integrand S t J h β g (Lattice.gauge k V)
  have me:StronglyMeasurable F :=
    ((marked_joint_envelope S J h β ok hg hm hu t).meas.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
  have stable:=Wilson.prior_gauge (G:=G) z
  have changeVar := integral_map_of_stronglyMeasurable (μ:=prior G f) stable.measurable me
  rw [stable.map_eq] at changeVar
  apply changeVar.trans
  apply integral_congr_ae
  filter_upwards with U
  change integrand S t J h β g (Lattice.gauge k V) (Lattice.gauge z U)=integrand S t J h β g V U
  unfold integrand
  rw [←lifted,tagged_gauge S t β ok,gauge S t J h ok,sym]

end YM.Integration.InletSusceptibility.JointPhysical
