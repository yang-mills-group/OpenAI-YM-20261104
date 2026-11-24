import YM.Integration.FVA1Physical.Wilson.FirstAligned
import YM.Comparison.RG02.Adjacent.Rank

/-! At the first order beyond an insertion's engineering degree, the exact
correction from the nonlinear fine gauge chart depends only on the incoming
leading homogeneous jet. Thus the correction cancels for matched leading jets
even when the next physical source coefficients disagree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision Marker Multi
open Comparison.RG02 Comparison.RG02.Assembly Progress.ClassicalKin
open scoped Topology Classical ContDiff BigOperators

variable {G:Gauge} {c f:Side} {S:StepData c f} (F:Forest S.ratio)
local notation "E" => Bulk.Joint S F (G:=G)
local notation "X" => ℝ × fieldDir G f 1

private theorem next_grade {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a:Y→ℂ} {k:ℕ} (h:GradeAt k a) : GradeAt (k+1) (a-jet a k) := by
  have sp:= (Adjacent.levelJet h.smooth k).smooth.contDiffAt (x:=0)
  refine ⟨h.smooth.sub sp,fun j hj=>?_⟩
  rw [iteratedFDeriv_sub_apply (h.smooth.of_le le_top) (sp.of_le le_top),Adjacent.Ranking.crop h.smooth]
  by_cases eq:j=k
  · rw [if_pos eq,sub_self]
  rw [if_neg eq,h.vanish j (by omega),sub_zero]

private theorem sub_jet {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a b:Y→ℂ} (ha:ContDiffAt ℝ ω a 0) (hb:ContDiffAt ℝ ω b 0) (n:ℕ) (y:Y):
    jet (a-b) n y=jet a n y-jet b n y:=by
  unfold Assembly.jet
  rw [iteratedFDeriv_sub_apply (ha.of_le le_top) (hb.of_le le_top),_root_.sub_apply,smul_sub]

theorem next_source_chart (V:ℝ → Config G f → ℂ) {k:ℕ} (h:GradeAt k (Bulk.projected V)) (y:E):
    jet (Bulk.posed S F V) (k+1) y=jet (Bulk.projected V) (k+1) (fineVelocity F y)+
      jet ((jet (Bulk.projected V) k) ∘ fineLogChart F) (k+1) y := by
  let a:=Bulk.projected V
  let h₀:=jet a k
  let L:=fineLogChart F (G:=G)
  have zero:L 0=0 :=congrArg (fun q:Work.F03.Logs G c f=>((0:ℝ),q.2)) (Work.F03.inclusion_zero F)
  have smooth:ContDiffAt ℝ ω L 0:=contDiffAt_fst.prodMk
    ((Work.F03.inclusion_smooth F).snd.comp (f:=Prod.snd) (0:E) contDiffAt_snd)
  have sm:ContDiffAt ℝ ω h₀ 0:=(Adjacent.levelJet h.smooth k).smooth.contDiffAt
  have eq:Bulk.posed S F V=ᶠ[𝓝 0] a ∘ L:=by
    filter_upwards [(continuous_snd.tendsto (0:E)).eventually (Work.F03.inclusion_works F)] with u hu
    exact congrArg (V u.1) hu.symm
  have actual:jet (Bulk.posed S F V) (k+1) y=jet (a ∘ L) (k+1) y:=by
    unfold Assembly.jet; rw [(eq.iteratedFDeriv ℝ (k+1)).eq_of_nhds]
  have high:=next_grade h
  have hh:jet ((a-h₀) ∘ L) (k+1) y=jet (a-h₀) (k+1) (fineVelocity F y):=by
    unfold Assembly.jet
    rw [wakes (a-h₀) L (high.smooth.of_le le_top) (smooth.of_le le_top) zero high.vanish]
    rfl
  have lhs:ContDiffAt ℝ ω (a ∘ L) 0:=(zero.symm ▸ h.smooth).comp _ smooth
  have rhs:ContDiffAt ℝ ω (h₀ ∘ L) 0:=(zero.symm ▸ sm).comp _ smooth
  change jet ((a ∘ L) - (h₀ ∘ L)) (k+1) y=_ at hh
  rw [sub_jet lhs rhs,sub_jet h.smooth sm] at hh
  have van:jet h₀ (k+1) (fineVelocity F y)=0:=by
    change jet (jet (Bulk.projected V) k) (k+1) (fineVelocity F y)=0
    rw [Adjacent.Ranking.clip h.smooth,if_neg (by omega : k+1≠k)];rfl
  rw [van,sub_zero] at hh
  exact actual.trans (sub_eq_iff_eq_add.mp hh)

theorem matched_next_letter (U V:ℝ → Config G f → ℂ) {k:ℕ}
    (hu:GradeAt k (Bulk.projected U)) (hv:GradeAt k (Bulk.projected V))
    (head:jet (Bulk.projected U) k=jet (Bulk.projected V) k) (y:E):
    jet (Bulk.posed S F U) (k+1) y-jet (Bulk.posed S F V) (k+1) y=
      jet (Bulk.projected U) (k+1) (fineVelocity F y)-jet (Bulk.projected V) (k+1) (fineVelocity F y) := by
  rw [next_source_chart F U hu,next_source_chart F V hv,head,add_sub_add_right_eq_sub]

end YM.Integration.FVA1Physical.Wilson
