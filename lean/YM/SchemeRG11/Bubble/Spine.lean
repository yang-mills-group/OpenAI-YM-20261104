import YM.SchemeRG11.Bubble.Taylor
import Mathlib.Analysis.Meromorphic.Basic

/-! Simple-pole local subtraction BEFORE correlated projection. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Function Set MeasureTheory Filter Metric Asymptotics Hot MSbar
open scoped ContDiff Topology
variable {μ A B : ℝ} {w : ℝ→ℂ} (hw : Continuous w) {P : ℂ→ℝ→ℂ} {D : ℂ→ℂ} (h : Glaze P D) (j : Bool) (hA : 1≤A+B)

def cave := {z : ℂ| -1<z.re}
lemma cave_open : IsOpen cave := isOpen_Ioi.preimage Complex.continuous_re

section
include hw h hA
theorem restored : AnalyticOnNhd ℂ (restore A B w P D j) cave := by
  rw [Complex.analyticOnNhd_iff_differentiableOn cave_open]
  intro e he
  obtain ⟨α,hα,h'⟩ := exists_between (show -1<e.re from he)
  obtain ⟨K,hK,hz,hp⟩ := exists_compact_subset (isOpen_Ioi.preimage Complex.continuous_re) h'
  obtain ⟨b,hb,he⟩:= till hw j h _ hα hK (fun u hu=> le_of_lt (hp hu))
  obtain ⟨c,hc,hq⟩:= trawl hw j h A B hA hK
  refine (DifferentiableAt.add (diffuse (F:= purse w P D j) (mem_interior_iff_mem_nhds.mp hz) ?_ ?_ hb) (diffuse (F:= pouch w P j) (mem_interior_iff_mem_nhds.mp hz) ?_ ?_ hc)).differentiableWithinAt
  · exact Eventually.of_forall (fun z=> (purse_on j h hw z).aestronglyMeasurable stem_meas)
  · exact ae_restrict_of_forall_mem stem_meas (fun p hs y hy=> ⟨purse_open j h p hs y, he y hy p hs⟩)
  · exact Eventually.of_forall (fun z=> (pouch_on j h hw z A B).aestronglyMeasurable (foil_meas ..))
  exact ae_restrict_of_forall_mem (foil_meas A B) (fun p hs y hy=> ⟨pouch_open j h p hs y, hq y hy p hs⟩)

theorem grope (hμ : 0<μ) : MeromorphicOn (extend μ A B w P D j) cave := by
  intro e he
  have hp:= (Pole.factor_entire μ hμ).analyticAt e
  have hq:= (h.fire 0 le_rfl).analyticAt e
  apply MeromorphicAt.mul hp.meromorphicAt
  refine MeromorphicAt.add ((restored hw h j hA).meromorphicOn e he) ?_
  cases j
  · exact ((analyticAt_id.meromorphicAt.inv.mul analyticAt_const.meromorphicAt).mul hq.meromorphicAt)
  exact ((((analyticAt_id.sub analyticAt_const).meromorphicAt.inv).mul analyticAt_const.meromorphicAt).mul hq.meromorphicAt |>.add ((analyticAt_id.meromorphicAt.inv.mul analyticAt_const.meromorphicAt).mul (h.crack.analyticAt e).meromorphicAt))
end

def glide (μ A B : ℝ) (w : ℝ→ℂ) (P : ℂ→ℝ→ℂ) (D : ℂ→ℂ) (j : Bool) (e : ℂ) :=
    Pole.factor μ e*(restore A B w P D j e+ if j then (e-1)⁻¹*route w*P e 0 else 0) +
      dslope (Pole.factor μ) 0 e*(if j then scale w * D e else route w * P e 0)

def blade (μ : ℝ) (w : ℝ→ℂ) (P : ℂ→ℝ→ℂ) (D : ℂ→ℂ) (j : Bool) (e : ℂ) :=
    Pole.factor μ 0*(if j then scale w*D e else route w * P e 0)

include h hw hA in
lemma glides (hμ : 0<μ) : AnalyticAt ℂ (glide μ A B w P D j) 0 := by
  have hp := Pole.factor_entire μ hμ
  have hs : Differentiable ℂ (dslope (Pole.factor μ) 0) := differentiableOn_univ.mp ((Complex.differentiableOn_dslope (univ_mem (f:=𝓝 0))).mpr hp.differentiableOn)
  have he := restored hw h j hA 0 (show (0:ℂ)∈cave from by simp [cave])
  have hz: AnalyticAt ℂ (fun e=>P e 0) (0:ℂ) := (h.fire 0 le_rfl).analyticAt _
  unfold glide
  refine AnalyticAt.add ((hp.analyticAt _).mul (he.add ?_)) ((hs.analyticAt _).mul ?_)
  · split
    · exact ((((analyticAt_id.sub (analyticAt_const (v:=(1:ℂ)))).inv (by simp)).mul analyticAt_const).mul hz)
    exact analyticAt_const
  split
  · exact analyticAt_const.mul (h.crack.analyticAt _)
  exact analyticAt_const.mul hz

lemma delivers {e : ℂ} (he : e≠0) : extend μ A B w P D j e-e⁻¹*blade μ w P D j e=glide μ A B w P D j e := by
  unfold extend blade glide dslope; rw [update_of_ne he,slope_def_module, sub_zero, smul_eq_mul]
  cases j <;> simp <;> ring

include hw h hA in
/-- If the blade is on the density -- independent of e -- `extend` has *exactly*
this pole part. Thus MSbar over all open-index readings at these parameters
subtracts precisely this one counterterm. If the same blade is ALREADY
contracted with other lines, those lines may themselves depend on e; do NOT
use this latter formula to do a new MS subtraction on the product. Instead
use `delivers` with their e dependence. -/
lemma poles (hμ : 0<μ) (c : ℂ) (hb : ∀ e, blade μ w P D j e=c) :
   AnalyticAt ℂ (glide μ A B w P D j) 0 ∧ ∀ e : ℂ, e≠0 →
      extend μ A B w P D j e=c/e+glide μ A B w P D j e := by
  refine ⟨glides hw h j hA hμ,fun e he=>?_⟩
  rw [← delivers j he,hb]; ring
end YM.SchemeRG11.Bubble
